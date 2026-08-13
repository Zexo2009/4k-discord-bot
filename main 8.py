import os
import threading
import asyncio
import subprocess

from flask import Flask
import discord
from discord import app_commands
from discord.ext import commands

# --- Keep-alive webserver (Render needs an open port for a "Web Service") ---
app = Flask(__name__)

@app.route('/')
def home():
    return "Bot is running!"

def run_web():
    port = int(os.environ.get("PORT", 10000))
    app.run(host='0.0.0.0', port=port)

threading.Thread(target=run_web, daemon=True).start()

# --- Discord bot setup ---
intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix="!", intents=intents, help_command=None)

DOWNLOAD_DIR = "downloads"
os.makedirs(DOWNLOAD_DIR, exist_ok=True)

COOKIES_PATH = "/etc/secrets/cookies.txt"
MAX_SECONDS = 60          # trim length, keeps RAM usage sane on the free tier
MAX_UPLOAD_MB = 8         # safe margin under Discord's ~10MB non-boosted limit


def cleanup(user_id: int):
    for f in os.listdir(DOWNLOAD_DIR):
        if f.startswith(str(user_id)):
            try:
                os.remove(os.path.join(DOWNLOAD_DIR, f))
            except OSError:
                pass


async def run_with_timeout(cmd, timeout=180):
    """Run a subprocess, return (returncode, stderr_text) or (None, 'timeout')."""
    proc = await asyncio.create_subprocess_exec(
        *cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    try:
        _, stderr = await asyncio.wait_for(proc.communicate(), timeout=timeout)
    except asyncio.TimeoutError:
        proc.kill()
        return None, "timeout"
    return proc.returncode, stderr.decode()[-500:]


async def download_source(url: str, user_id: int):
    """Downloads a video from a URL (YouTube/TikTok/direct link/etc) via yt-dlp.
    Returns (path_to_file, error_message)."""
    input_template = os.path.join(DOWNLOAD_DIR, f"{user_id}_input.%(ext)s")

    dl_cmd = [
        "yt-dlp",
        "-f", "bestvideo[height<=1080]+bestaudio/best[height<=1080]/best",
        "--merge-output-format", "mp4",
        "-o", input_template,
    ]
    if os.path.exists(COOKIES_PATH):
        dl_cmd += ["--cookies", COOKIES_PATH]
    dl_cmd.append(url)

    code, err = await run_with_timeout(dl_cmd)
    if code == "timeout" or err == "timeout":
        return None, "❌ Download timed out. Try a shorter/smaller video."
    if code != 0:
        return None, f"❌ Download failed:\n```{err}```"

    for f in os.listdir(DOWNLOAD_DIR):
        if f.startswith(f"{user_id}_input"):
            return os.path.join(DOWNLOAD_DIR, f), None
    return None, "❌ Downloaded file not found."


async def encode_video(input_path: str, user_id: int):
    """Re-encodes to 1080p, trimmed. Returns (path, error_message)."""
    output_path = os.path.join(DOWNLOAD_DIR, f"{user_id}_output.mp4")
    ff_cmd = [
        "ffmpeg", "-y",
        "-i", input_path,
        "-t", str(MAX_SECONDS),
        "-vf", "scale=-2:1080",
        "-c:v", "libx264",
        "-preset", "ultrafast",
        "-crf", "23",
        "-threads", "1",
        "-c:a", "aac",
        output_path,
    ]
    code, err = await run_with_timeout(ff_cmd)
    if code == "timeout" or err == "timeout":
        return None, "❌ Encoding timed out. Try a shorter video."
    if code != 0:
        return None, f"❌ Encoding failed:\n```{err}```"
    return output_path, None


async def extract_audio(input_path: str, user_id: int):
    """Extracts audio track as mp3. Returns (path, error_message)."""
    output_path = os.path.join(DOWNLOAD_DIR, f"{user_id}_audio.mp3")
    ff_cmd = [
        "ffmpeg", "-y",
        "-i", input_path,
        "-t", str(MAX_SECONDS),
        "-vn",
        "-acodec", "libmp3lame",
        "-q:a", "2",
        output_path,
    ]
    code, err = await run_with_timeout(ff_cmd)
    if code == "timeout" or err == "timeout":
        return None, "❌ Audio extraction timed out."
    if code != 0:
        return None, f"❌ Audio extraction failed:\n```{err}```"
    return output_path, None


async def send_result(channel, status_msg, path: str, label: str):
    size_mb = os.path.getsize(path) / (1024 * 1024)
    if size_mb > MAX_UPLOAD_MB:
        await status_msg.edit(
            content=(
                f"⚠️ Done, but the {label} is {size_mb:.1f} MB — "
                f"likely too large to upload on this server (default Discord limit is ~10 MB "
                f"unless the server is boosted). Try a shorter clip or a file host instead."
            )
        )
        return
    await status_msg.edit(content=f"✅ Done! Uploading {label}...")
    try:
        await channel.send(file=discord.File(path))
    except discord.HTTPException:
        await status_msg.edit(
            content=(
                f"⚠️ Upload rejected by Discord ({size_mb:.1f} MB — too large for this server)."
            )
        )


async def handle_video_job(channel, status_msg, url: str, user_id: int, want_audio: bool):
    input_path, err = await download_source(url, user_id)
    if err:
        await status_msg.edit(content=err)
        cleanup(user_id)
        return

    if want_audio:
        await status_msg.edit(content="⏳ Extracting audio...")
        out_path, err = await extract_audio(input_path, user_id)
        label = "audio file"
    else:
        await status_msg.edit(
            content=(
                "⏳ Encoding to 1080p... "
                "(trimmed to max 60s to stay within the free server's memory limit)"
            )
        )
        out_path, err = await encode_video(input_path, user_id)
        label = "video"

    if err:
        await status_msg.edit(content=err)
        cleanup(user_id)
        return

    await send_result(channel, status_msg, out_path, label)
    cleanup(user_id)


@bot.event
async def on_ready():
    print(f"✅ Bot is online as {bot.user}")
    try:
        synced = await bot.tree.sync()
        print(f"Synced {len(synced)} slash command(s)")
    except Exception as e:
        print(f"Slash command sync failed: {e}")


# --- Reply-based triggers: reply to a message with a video attachment with .dl or .extract ---
@bot.event
async def on_message(message: discord.Message):
    if message.author.bot:
        return

    content = message.content.strip().lower()
    if content in (".dl", ".extract") and message.reference:
        try:
            ref_msg = await message.channel.fetch_message(message.reference.message_id)
        except discord.NotFound:
            await message.channel.send("❌ Couldn't find the message you replied to.")
            return

        video_url = None
        for att in ref_msg.attachments:
            if att.content_type and att.content_type.startswith("video"):
                video_url = att.url
                break

        if not video_url:
            await message.channel.send("❌ The message you replied to has no video attachment.")
            return

        status_msg = await message.channel.send("⏳ Downloading video...")
        want_audio = content == ".extract"
        await handle_video_job(message.channel, status_msg, video_url, message.author.id, want_audio)
        return

    await bot.process_commands(message)


# --- Prefix commands (still work with !) ---
@bot.command()
async def ping(ctx):
    await ctx.send("Pong! 🚀")


@bot.command()
async def help(ctx):
    await ctx.send(embed=build_help_embed())


@bot.command()
async def vhq(ctx, url: str = None):
    if url is None:
        await ctx.send("Please provide a video URL, e.g. `!vhq https://...`")
        return
    status_msg = await ctx.send("⏳ Downloading video...")
    await handle_video_job(ctx.channel, status_msg, url, ctx.author.id, want_audio=False)


@bot.command(name="extractaudio")
async def extractaudio_cmd(ctx, url: str = None):
    if url is None:
        await ctx.send("Please provide a video URL, e.g. `!extractaudio https://...`")
        return
    status_msg = await ctx.send("⏳ Downloading video...")
    await handle_video_job(ctx.channel, status_msg, url, ctx.author.id, want_audio=True)


def build_help_embed():
    embed = discord.Embed(
        title="Bot Commands",
        description="Here's what I can do:",
        color=discord.Color.blurple(),
    )
    embed.add_field(name="/vhq or !vhq <url>", value="Downloads a video and re-encodes it in 1080p (max 60s).", inline=False)
    embed.add_field(name="/extractaudio or !extractaudio <url>", value="Downloads a video and extracts its audio as MP3.", inline=False)
    embed.add_field(
        name="Reply with .dl or .extract",
        value="Reply to a message that has a video attached with `.dl` (video) or `.extract` (audio) to process it.",
        inline=False,
    )
    embed.add_field(name="/ping or !ping", value="Check if the bot is online.", inline=False)
    embed.set_footer(text="Note: YouTube links may fail without cookie setup — TikTok and direct links work best.")
    return embed


# --- Slash commands ---
@bot.tree.command(name="ping", description="Check if the bot is online")
async def slash_ping(interaction: discord.Interaction):
    await interaction.response.send_message("Pong! 🚀")


@bot.tree.command(name="help", description="Show all available commands")
async def slash_help(interaction: discord.Interaction):
    await interaction.response.send_message(embed=build_help_embed())


@bot.tree.command(name="vhq", description="Download a video and re-encode it in 1080p")
@app_commands.describe(url="Video URL (TikTok, direct link, etc.)")
async def slash_vhq(interaction: discord.Interaction, url: str):
    await interaction.response.send_message("⏳ Downloading video...")
    status_msg = await interaction.original_response()
    await handle_video_job(interaction.channel, status_msg, url, interaction.user.id, want_audio=False)


@bot.tree.command(name="extractaudio", description="Download a video and extract its audio as MP3")
@app_commands.describe(url="Video URL (TikTok, direct link, etc.)")
async def slash_extractaudio(interaction: discord.Interaction, url: str):
    await interaction.response.send_message("⏳ Downloading video...")
    status_msg = await interaction.original_response()
    await handle_video_job(interaction.channel, status_msg, url, interaction.user.id, want_audio=True)


TOKEN = os.environ.get("DISCORD_TOKEN")
if not TOKEN:
    raise RuntimeError("DISCORD_TOKEN environment variable is missing! Set it in Render under Environment.")

bot.run(TOKEN)
