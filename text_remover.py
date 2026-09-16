"""
text_remover.py — local, free, self-hosted burned-in subtitle/text removal for videos.

This is a Cog-free port of the open-source model hjunior29/video-text-remover
(https://github.com/hjunior29/video-text-remover, MIT license): a YOLO11 ONNX text
detector + OpenCV inpainting. Runs entirely on CPU, no external API, no per-run cost —
the only "cost" is the compute time on whatever host runs the bot.

SETUP REQUIRED before this works:
  1. pip install onnxruntime opencv-python-headless numpy pillow
  2. Get the ~37MB detector weights and place them at the path below:
       git clone https://github.com/hjunior29/video-text-remover.git
       cp video-text-remover/models/text_detector/converted_best.onnx  <this project>/models/text_detector/converted_best.onnx
  3. ffmpeg must be installed on the host (Render's standard images already have it,
     since main_15.py already shells out to ffmpeg elsewhere).

PERFORMANCE NOTE: this is CPU inpainting, not a GPU service — expect roughly 2-5 FPS
on a typical small Render instance (a 30s/30fps clip is ~900 frames, so budget several
minutes, not seconds). Keep `resolution` at 480p/360p and cap video length in the
calling code to keep this usable on a cheap/free host — see MAX_REMOVESUBS_SECONDS in
main_15.py.
"""
import os
import shutil
import subprocess
import tempfile
import concurrent.futures
from typing import List

import cv2
import numpy as np
import onnxruntime as ort

MODEL_PATH = os.environ.get(
    "TEXT_REMOVER_MODEL_PATH",
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "models", "text_detector", "converted_best.onnx"),
)

_session = None
_input_name = None
_output_names = None


def model_available() -> bool:
    """Whether the ONNX weights are actually present — lets callers give a clean error
    instead of crashing the first time someone runs the command before setup is done."""
    return os.path.exists(MODEL_PATH)


def _load_model():
    """Loads the ONNX session once and caches it at module level (mirrors the original
    Cog predictor's one-time `setup()`)."""
    global _session, _input_name, _output_names
    if _session is not None:
        return
    if not model_available():
        raise FileNotFoundError(
            f"Text-detector model not found at {MODEL_PATH}. See the setup instructions "
            f"at the top of text_remover.py."
        )
    sess_options = ort.SessionOptions()
    sess_options.graph_optimization_level = ort.GraphOptimizationLevel.ORT_ENABLE_BASIC
    sess_options.intra_op_num_threads = max(1, os.cpu_count() or 2)
    sess_options.log_severity_level = 3
    available_providers = ort.get_available_providers()
    if "CUDAExecutionProvider" in available_providers:
        providers = ["CUDAExecutionProvider", "CPUExecutionProvider"]
    elif "TensorrtExecutionProvider" in available_providers:
        providers = ["TensorrtExecutionProvider", "CUDAExecutionProvider", "CPUExecutionProvider"]
    else:
        providers = ["CPUExecutionProvider"]
    _session = ort.InferenceSession(MODEL_PATH, providers=providers, sess_options=sess_options)
    inputs = _session.get_inputs()
    outputs = _session.get_outputs()
    _input_name = inputs[0].name if inputs else None
    _output_names = [o.name for o in outputs] if outputs else []


# ---------------------------------------------------------------------------
# Detection (YOLO11 ONNX)
# ---------------------------------------------------------------------------

def _preprocess_frame(frame: np.ndarray, input_size: int = 640):
    frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
    orig_height, orig_width = frame.shape[:2]
    scale = min(input_size / orig_width, input_size / orig_height)
    new_width = int(orig_width * scale)
    new_height = int(orig_height * scale)
    resized = cv2.resize(frame_rgb, (new_width, new_height))
    padded = np.full((input_size, input_size, 3), 114, dtype=np.uint8)
    pad_x = (input_size - new_width) // 2
    pad_y = (input_size - new_height) // 2
    padded[pad_y:pad_y + new_height, pad_x:pad_x + new_width] = resized
    input_tensor = padded.astype(np.float32) / 255.0
    input_tensor = input_tensor.transpose(2, 0, 1)
    return input_tensor, (orig_width, orig_height, scale, pad_x, pad_y)


def _apply_nms(boxes: List[List[int]], iou_threshold: float) -> List[List[int]]:
    if not boxes:
        return []
    boxes_array = np.array(boxes)
    x1, y1, x2, y2 = boxes_array[:, 0], boxes_array[:, 1], boxes_array[:, 2], boxes_array[:, 3]
    areas = (x2 - x1) * (y2 - y1)
    order = areas.argsort()[::-1]
    keep = []
    while order.size > 0:
        i = order[0]
        keep.append(i)
        xx1 = np.maximum(x1[i], x1[order[1:]])
        yy1 = np.maximum(y1[i], y1[order[1:]])
        xx2 = np.minimum(x2[i], x2[order[1:]])
        yy2 = np.minimum(y2[i], y2[order[1:]])
        w = np.maximum(0, xx2 - xx1)
        h = np.maximum(0, yy2 - yy1)
        inter = w * h
        iou = inter / (areas[i] + areas[order[1:]] - inter)
        order = order[np.where(iou <= iou_threshold)[0] + 1]
    return [boxes[i] for i in keep]


def _postprocess_detections(predictions, orig_info, conf_threshold: float, iou_threshold: float):
    boxes = []
    orig_width, orig_height, scale, pad_x, pad_y = orig_info
    if predictions is None:
        return boxes
    if hasattr(predictions, "shape") and len(predictions.shape) == 3:
        predictions = predictions[0]
    if predictions.shape[0] < predictions.shape[1]:
        predictions = predictions.transpose()
    for pred in predictions:
        if pred is not None and len(pred) >= 5 and pred[4] >= conf_threshold:
            x_center, y_center, width, height = pred[:4]
            x1 = (x_center - width / 2 - pad_x) / scale
            y1 = (y_center - height / 2 - pad_y) / scale
            x2 = (x_center + width / 2 - pad_x) / scale
            y2 = (y_center + height / 2 - pad_y) / scale
            x1, x2 = max(0, min(x1, orig_width)), max(0, min(x2, orig_width))
            y1, y2 = max(0, min(y1, orig_height)), max(0, min(y2, orig_height))
            boxes.append([int(x1), int(y1), int(x2), int(y2)])
    if len(boxes) > 1:
        boxes = _apply_nms(boxes, iou_threshold)
    return boxes


def _detect_onnx(frame: np.ndarray, conf_threshold: float, iou_threshold: float) -> List[List[int]]:
    try:
        input_tensor, orig_info = _preprocess_frame(frame)
        input_tensor = np.expand_dims(input_tensor, axis=0)
        outputs = _session.run(_output_names, {_input_name: input_tensor})
        if not outputs:
            return []
        return _postprocess_detections(outputs[0], orig_info, conf_threshold, iou_threshold)
    except Exception as e:
        print(f"⚠️ text_remover: detection error: {e}")
        return []


# ---------------------------------------------------------------------------
# Removal methods (all plain OpenCV — no ML here)
# ---------------------------------------------------------------------------

def _expand_box(frame, box, margin):
    x1, y1, x2, y2 = box
    height, width = frame.shape[:2]
    return [max(0, x1 - margin), max(0, y1 - margin), min(width, x2 + margin), min(height, y2 + margin)]


def _apply_inpaint_telea(frame, box):
    x1, y1, x2, y2 = box
    mask = np.zeros(frame.shape[:2], dtype=np.uint8)
    mask[y1:y2, x1:x2] = 255
    return cv2.inpaint(frame, mask, inpaintRadius=3, flags=cv2.INPAINT_TELEA)


def _apply_inpaint_ns(frame, box):
    x1, y1, x2, y2 = box
    mask = np.zeros(frame.shape[:2], dtype=np.uint8)
    mask[y1:y2, x1:x2] = 255
    return cv2.inpaint(frame, mask, inpaintRadius=3, flags=cv2.INPAINT_NS)


def _apply_blur(frame, box):
    x1, y1, x2, y2 = box
    roi = frame[y1:y2, x1:x2]
    if roi.size > 0:
        frame[y1:y2, x1:x2] = cv2.GaussianBlur(roi, (51, 51), 30)
    return frame


def _apply_hybrid(frame, box):
    x1, y1, x2, y2 = box
    height, width = frame.shape[:2]
    context_margin = 20
    cx1, cy1 = max(0, x1 - context_margin), max(0, y1 - context_margin)
    cx2, cy2 = min(width, x2 + context_margin), min(height, y2 + context_margin)
    roi_expanded = frame[cy1:cy2, cx1:cx2].copy()
    mask_local = np.zeros(roi_expanded.shape[:2], dtype=np.uint8)
    mx1, my1, mx2, my2 = x1 - cx1, y1 - cy1, x2 - cx1, y2 - cy1
    mask_local[my1:my2, mx1:mx2] = 255
    roi_inpainted = cv2.inpaint(roi_expanded, mask_local, 3, cv2.INPAINT_TELEA)
    frame[y1:y2, x1:x2] = roi_inpainted[my1:my2, mx1:mx2]
    return frame


def _apply_background(frame, box):
    x1, y1, x2, y2 = box
    height, width = frame.shape[:2]
    m = 10
    sx1, sy1 = max(0, x1 - m), max(0, y1 - m)
    sx2, sy2 = min(width, x2 + m), min(height, y2 + m)
    mask = np.ones((sy2 - sy1, sx2 - sx1), dtype=np.uint8) * 255
    if sx1 < x1 < sx2 and sy1 < y1 < sy2:
        mask[y1 - sy1:y2 - sy1, x1 - sx1:x2 - sx1] = 0
    sample_region = frame[sy1:sy2, sx1:sx2]
    if mask.any():
        frame[y1:y2, x1:x2] = cv2.mean(sample_region, mask=mask)[:3]
    else:
        frame[y1:y2, x1:x2] = (0, 0, 0)
    return frame


def _remove_text(frame, box, method, margin):
    x1, y1, x2, y2 = _expand_box(frame, box, margin)
    box = [x1, y1, x2, y2]
    if method == "hybrid":
        return _apply_hybrid(frame, box)
    if method == "inpaint":
        return _apply_inpaint_telea(frame, box)
    if method == "inpaint_ns":
        return _apply_inpaint_ns(frame, box)
    if method == "blur":
        return _apply_blur(frame, box)
    if method == "black":
        frame[y1:y2, x1:x2] = (0, 0, 0)
        return frame
    if method == "background":
        return _apply_background(frame, box)
    return _apply_inpaint_telea(frame, box)


def _process_single_frame(frame, boxes, method, margin):
    for box in boxes:
        frame = _remove_text(frame, box, method, margin)
    return frame


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------

_RESOLUTION_MAP = {"1080p": 1080, "720p": 720, "480p": 480, "360p": 360, "original": None}


def remove_text_from_video(
    video_path: str,
    method: str = "hybrid",
    conf_threshold: float = 0.25,
    iou_threshold: float = 0.45,
    margin: int = 5,
    resolution: str = "480p",
    detection_interval: int = 6,
    progress_cb=None,
) -> str:
    """Removes burned-in text from a local video file and returns the path to a new,
    cleaned (VIDEO-ONLY — audio is not preserved by this model) mp4. Raises on failure
    instead of returning None, so callers should wrap this in a try/except.

    BLOCKING / CPU-heavy — always call this from a thread executor, never directly on
    the bot's event loop. `progress_cb(current_frame, total_frames)`, if given, is
    called periodically so a caller can update a Discord message."""
    _load_model()

    cap = cv2.VideoCapture(video_path)
    if not cap.isOpened():
        raise ValueError(f"Could not open video file: {video_path}")

    fps = cap.get(cv2.CAP_PROP_FPS)
    orig_width = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
    orig_height = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
    total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
    if fps <= 0 or orig_width <= 0 or orig_height <= 0 or total_frames <= 0:
        cap.release()
        raise ValueError(f"Invalid video properties (fps={fps}, {orig_width}x{orig_height}, frames={total_frames})")

    target_height = _RESOLUTION_MAP.get(resolution)
    processing_width, processing_height = orig_width, orig_height
    if target_height is not None and orig_height > target_height:
        scale = target_height / orig_height
        processing_width = int(orig_width * scale)
        processing_height = target_height

    frames_dir = tempfile.mkdtemp(prefix="textrm_frames_")
    output_path = os.path.join(tempfile.mkdtemp(prefix="textrm_out_"), "output.mp4")

    # Small, host-friendly worker/batch sizes — the upstream defaults (up to 128
    # threads) assume beefy dedicated infra, which a cheap Render instance is not.
    cpu_count = os.cpu_count() or 2
    num_workers = max(1, min(4, cpu_count))
    BATCH_SIZE = 16

    MAX_DETECTION_DIMENSION = 1080
    det_scale_factor = 1.0
    if max(processing_width, processing_height) > MAX_DETECTION_DIMENSION:
        det_scale_factor = MAX_DETECTION_DIMENSION / max(processing_width, processing_height)

    frames_since_detection = detection_interval
    previous_boxes: List[List[int]] = []
    frame_num = 0

    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=num_workers) as executor:
            while cap.isOpened():
                batch_frames = []
                for _ in range(BATCH_SIZE):
                    ret, frame = cap.read()
                    if not ret:
                        break
                    if processing_height != orig_height:
                        frame = cv2.resize(frame, (processing_width, processing_height))
                    batch_frames.append(frame)
                if not batch_frames:
                    break

                batch_boxes = []
                for frame in batch_frames:
                    frame_num += 1
                    if frames_since_detection >= detection_interval:
                        if det_scale_factor < 1.0:
                            det_w = int(processing_width * det_scale_factor)
                            det_h = int(processing_height * det_scale_factor)
                            frame_small = cv2.resize(frame, (det_w, det_h))
                            boxes = _detect_onnx(frame_small, conf_threshold, iou_threshold)
                            boxes = [[int(v / det_scale_factor) for v in b] for b in boxes]
                        else:
                            boxes = _detect_onnx(frame, conf_threshold, iou_threshold)
                        previous_boxes = boxes
                        frames_since_detection = 0
                    else:
                        boxes = previous_boxes
                        frames_since_detection += 1
                    batch_boxes.append(boxes)

                futures = [
                    executor.submit(_process_single_frame, frame, boxes, method, margin) if boxes
                    else executor.submit(lambda f: f, frame)
                    for frame, boxes in zip(batch_frames, batch_boxes)
                ]
                for i, future in enumerate(futures):
                    processed_frame = future.result()
                    current_frame_num = (frame_num - len(batch_frames)) + i + 1
                    cv2.imwrite(os.path.join(frames_dir, f"frame_{current_frame_num:06d}.png"), processed_frame)
                    if progress_cb and (current_frame_num % 30 == 0 or current_frame_num == total_frames):
                        try:
                            progress_cb(current_frame_num, total_frames)
                        except Exception:
                            pass
    except Exception:
        cap.release()
        shutil.rmtree(frames_dir, ignore_errors=True)
        raise
    finally:
        cap.release()

    ffmpeg_cmd = [
        "ffmpeg", "-y", "-framerate", str(fps), "-i", os.path.join(frames_dir, "frame_%06d.png"),
        "-c:v", "libx264", "-preset", "medium", "-crf", "23", "-pix_fmt", "yuv420p", "-movflags", "+faststart",
    ]
    if processing_height != orig_height:
        ffmpeg_cmd.extend(["-vf", f"scale={orig_width}:{orig_height}"])
    ffmpeg_cmd.append(output_path)

    try:
        subprocess.run(ffmpeg_cmd, capture_output=True, text=True, check=True, timeout=600)
    except subprocess.CalledProcessError as e:
        shutil.rmtree(frames_dir, ignore_errors=True)
        raise RuntimeError(f"FFmpeg encoding failed: {e.stderr}")
    finally:
        shutil.rmtree(frames_dir, ignore_errors=True)

    if not os.path.exists(output_path) or os.path.getsize(output_path) == 0:
        raise RuntimeError("Output video file was not created or is empty")
    return output_path
