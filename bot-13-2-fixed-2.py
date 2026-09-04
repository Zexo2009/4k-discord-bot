"""
bot.py — Zexo, all-in-one (everything except the Flask website): config/constants/storage,
the Discord bot instance, every command/event/job and embed builder, AND the process entry
point at the bottom (guarded by `if __name__ == "__main__":` so website.py can still safely
`from bot import *` without accidentally starting the bot a second time).

website.py imports from this module (constants, storage helpers, `bot`, and the job runners)
to power the web dashboard's manual trigger buttons and live status.
"""
import os
import time
import json
import re
import random
import asyncio
import base64
import subprocess
import tempfile
from io import BytesIO
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

import discord
from discord import app_commands
from discord.ext import commands, tasks
import psycopg2
import psycopg2.pool
from PIL import Image, ImageDraw, ImageFont
import yt_dlp
import requests as http_requests
from ddgs import DDGS

# ============================================================
# CONFIG
# ============================================================
# ============================================================
# CONFIG
# ============================================================
SUBMIT_CHANNEL_ID = 1453098499301314662
DISCUSSION_CHANNEL_ID = 1514944188838576270
RESULTS_CHANNEL_ID = 1479559357363650653
LOG_CHANNEL_ID = 1538882280221712394  # points audit log

PICKER_ROLE_ID = 1514920107912990841       # Top Edit Picker
MANAGER_ROLE_ID = 1537794514306080809      # Top Edit Picker Manager
STAFF_ROLE_ID = 1463596580430020772        # Staff
TOP_EDITS_ROLE_ID = 1514918405193596928    # pinged when the daily winner is posted
UNRANKED_ROLE_ID = 1538880654123601940     # Unranked

SUBMIT_CHANNEL_NAME = "editing-rating"
DISCUSSION_CHANNEL_NAME = "top-edit-discussion"
RESULTS_CHANNEL_NAME = "top-edits"
LOG_CHANNEL_NAME = "points-log"
PICKER_ROLE_NAME = "Top Edit Picker"
MANAGER_ROLE_NAME = "Top Edit Picker Manager"
STAFF_ROLE_NAME = "Staff"
TOP_EDITS_ROLE_NAME = "Top Edits"
UNRANKED_ROLE_NAME = "Unranked"

COLLECT_HOUR = 16
RESULTS_HOUR = 20
EU_TZ = ZoneInfo("Europe/Berlin")

POLL_DURATION_HOURS = 4
# This is Discord's own hard limit per native poll (not a limit we impose) — it's used as the
# batch size when splitting an unlimited number of edits across multiple simultaneous polls.
MAX_POLL_ANSWERS = 10

WINNER_POINTS = 1
# A video URL that was already posted to a vote is excluded forever — no time window.

POINTS_FILE = "points.json"
DAY_FILE = "day_counter.json"
VIDEO_HISTORY_FILE = "video_history.json"
LAST_COLLECT_FILE = "last_collect.json"
BADWORDS_FILE = "badwords.json"

# Optional: connection string for a free external Postgres (Neon/Supabase/etc).
# When set, points/day/video-history/last-collect survive redeploys and restarts.
# Without it, the bot falls back to local JSON files, which Render's free tier wipes on every redeploy.
DATABASE_URL = os.environ.get("DATABASE_URL")
DEFAULT_DAY = 65  # "today" was day 64 when this was written -> next run is day 65

# (threshold, role_id, label, emoji)
RANK_TIERS = [
    (10, 1459931456859144308, "D", "🔹"),
    (20, 1459931371567976592, "C", "🔷"),
    (35, 1459931236045820126, "B", "💠"),
    (50, 1459931151664676884, "A", "🔶"),
    (70, 1459931062665871626, "S", "👑"),
]
UNRANKED_LABEL = "Unranked"
UNRANKED_EMOJI = "⚪"

# Accent colors used for the image-based leaderboard (per tier)
TIER_COLORS = {
    "Unranked": (130, 130, 145),
    "D": (99, 155, 255),
    "C": (64, 209, 255),
    "B": (176, 110, 255),
    "A": (255, 150, 60),
    "S": (255, 205, 60),
}

# ============================================================


# ============================================================
# Shared runtime state — read/written by both the bot and the website
# ============================================================
# Shared, thread-safe-ish state the Flask dashboard reads from
# Shared, thread-safe-ish state the Flask dashboard reads from
dashboard_state = {
    "guild_name": None,
    "member_count": 0,
}

START_TIME = datetime.now(timezone.utc)
command_usage = {}
resolved_names = {}  # user_id (str) -> last known display name, for the web dashboard

# guild_id -> {"polls": [{"message_id":, "channel_id":, "offset":}, ...], "entries": [...]}
# "polls" is a list because Discord's native Poll object hard-caps at 10 answers — with no
# limit on how many edits can be submitted, one day's vote may need several poll messages,
# each covering a slice of "entries" starting at its "offset". Results are tallied across all
# of them together.
current_polls = {}


def get_poll_state(guild_id: int) -> dict:
    return current_polls.setdefault(guild_id, {"polls": [], "entries": []})
last_collect_dates = {}  # guild_id -> date() of the last collect run for that server
last_results_dates = {}  # guild_id -> date() of the last results run for that server


def find_channel(guild: discord.Guild, channel_id, name: str):
    if channel_id:
        ch = guild.get_channel(channel_id)
        if ch:
            return ch
    for ch in guild.text_channels:
        if ch.name == name:
            return ch
    return None


def find_role(guild: discord.Guild, role_id, name: str):
    if role_id:
        role = guild.get_role(role_id)
        if role:
            return role
    for role in guild.roles:
        if role.name == name:
            return role
    return None


def find_any_role(guild: discord.Guild, role_ids, name: str):
    """Like find_role, but accepts a list of role IDs — returns the first one that still
    exists in the guild, falling back to a name match like find_role does."""
    for role_id in (role_ids or []):
        role = guild.get_role(role_id)
        if role:
            return role
    for role in guild.roles:
        if role.name == name:
            return role
    return None


def _member_has_role(member: discord.Member, role_id: int, role_name: str) -> bool:
    if role_id and any(r.id == role_id for r in member.roles):
        return True
    return any(role.name == role_name for role in member.roles)


def _member_has_any_role(member: discord.Member, role_ids, role_name: str) -> bool:
    """Like _member_has_role, but accepts a list of role IDs — True if the member has
    ANY of them, or falls back to the legacy name match if none are configured."""
    member_role_ids = {r.id for r in member.roles}
    if any((rid in member_role_ids) for rid in (role_ids or [])):
        return True
    return any(role.name == role_name for role in member.roles)


def has_picker_permission(member: discord.Member) -> bool:
    """Top Edit Picker, Manager, Staff, or admin: everything except giving/removing points."""
    if member.guild_permissions.administrator:
        return True
    config = load_guild_config(member.guild.id)
    return (
        _member_has_any_role(member, config["picker_role_ids"], PICKER_ROLE_NAME)
        or _member_has_any_role(member, config["manager_role_ids"], MANAGER_ROLE_NAME)
        or _member_has_any_role(member, config["staff_role_ids"], STAFF_ROLE_NAME)
    )


def has_points_permission(member: discord.Member) -> bool:
    """Only Top Edit Picker Manager, Staff, or admin can give/remove points."""
    if member.guild_permissions.administrator:
        return True
    config = load_guild_config(member.guild.id)
    return (
        _member_has_any_role(member, config["manager_role_ids"], MANAGER_ROLE_NAME)
        or _member_has_any_role(member, config["staff_role_ids"], STAFF_ROLE_NAME)
    )


def format_timedelta(td: timedelta) -> str:
    total_seconds = int(td.total_seconds())
    hours, remainder = divmod(total_seconds, 3600)
    minutes, _ = divmod(remainder, 60)
    if hours and minutes:
        return f"{hours}h {minutes}m"
    if hours:
        return f"{hours}h"
    return f"{minutes}m"


def progress_bar(current: int, total: int, width: int = 10) -> str:
    if total <= 0:
        return "▰" * width
    filled = min(width, round((current / total) * width))
    return "▰" * filled + "▱" * (width - filled)



# --- Persistent storage (Postgres if DATABASE_URL is set, else local JSON files) ---

# Kept alive across requests instead of opening a brand-new TCP+TLS+auth connection on every
# single load_guild_config()/load_badwords()/db_get_raw() call — that per-call reconnect cost
# was the main reason the web dashboard felt like it "took forever" to load.
_db_pool = None


class _PooledConnWrapper:
    """Thin wrapper so every existing call site (`conn = get_db_connection(); ... conn.close()`)
    keeps working unchanged — .close() returns the connection to the pool instead of actually
    closing the socket."""

    def __init__(self, raw_conn):
        self._raw_conn = raw_conn

    def __getattr__(self, name):
        return getattr(self._raw_conn, name)

    def close(self):
        _db_pool.putconn(self._raw_conn)


def get_db_connection():
    global _db_pool
    if _db_pool is None:
        _db_pool = psycopg2.pool.ThreadedConnectionPool(
            1, 10, DATABASE_URL, sslmode="require", connect_timeout=8
        )
    return _PooledConnWrapper(_db_pool.getconn())


def init_db():
    if not DATABASE_URL:
        print("⚠️ DATABASE_URL not set — using local JSON files. Points WILL be lost on every redeploy/restart on Render's free tier.")
        return
    try:
        conn = get_db_connection()
        try:
            with conn.cursor() as cur:
                cur.execute("CREATE TABLE IF NOT EXISTS kv_store (key TEXT PRIMARY KEY, value TEXT NOT NULL)")
            conn.commit()
        finally:
            conn.close()
        print("✅ Connected to database (pooled) — points will persist across restarts/redeploys.")
    except Exception as e:
        print(f"⚠️ Could not connect to DATABASE_URL ({e}). Falling back to local JSON files.")


def db_get_raw(key: str):
    """Returns the stored string for `key`, or None if missing/DB unavailable."""
    if not DATABASE_URL:
        return None
    try:
        conn = get_db_connection()
        try:
            with conn.cursor() as cur:
                cur.execute("SELECT value FROM kv_store WHERE key = %s", (key,))
                row = cur.fetchone()
                return row[0] if row else None
        finally:
            conn.close()
    except Exception as e:
        print(f"⚠️ DB read failed for '{key}': {e}")
        return None


def db_set_raw(key: str, value: str) -> bool:
    """Stores `value` under `key`. Returns True on success."""
    if not DATABASE_URL:
        return False
    try:
        conn = get_db_connection()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    "INSERT INTO kv_store (key, value) VALUES (%s, %s) "
                    "ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value",
                    (key, value),
                )
            conn.commit()
            return True
        finally:
            conn.close()
    except Exception as e:
        print(f"⚠️ DB write failed for '{key}': {e}")
        return False


# ============================================================
# PER-GUILD CONFIG (so any server can use the bot with its own channels/roles)
# ============================================================
_DEFAULT_RANK_ROLE_IDS = {label: role_id for _t, role_id, label, _e in RANK_TIERS}


def default_guild_config() -> dict:
    """Fallback config: matches this bot's original/home server exactly, so nothing
    changes for it. Any other server should override these via the website dashboard's Settings page."""
    return {
        "submit_channel_id": SUBMIT_CHANNEL_ID,
        "discussion_channel_id": DISCUSSION_CHANNEL_ID,
        "results_channel_id": RESULTS_CHANNEL_ID,
        "log_channel_id": LOG_CHANNEL_ID,
        "picker_role_ids": [PICKER_ROLE_ID] if PICKER_ROLE_ID else [],
        "manager_role_ids": [MANAGER_ROLE_ID] if MANAGER_ROLE_ID else [],
        "staff_role_ids": [STAFF_ROLE_ID] if STAFF_ROLE_ID else [],
        "top_edits_role_id": TOP_EDITS_ROLE_ID,
        "unranked_role_id": UNRANKED_ROLE_ID,
        "rank_role_ids": dict(_DEFAULT_RANK_ROLE_IDS),
        "rank_thresholds": {},
        "rank_emojis": {},
        "collect_hour": COLLECT_HOUR,
        "results_hour": RESULTS_HOUR,
        "collect_minute": 0,
        "results_minute": 0,
        "winner_points": WINNER_POINTS,
        "poll_duration_hours": POLL_DURATION_HOURS,
        # Fully custom text, editable from the web dashboard. Empty/None means "use the
        # built-in default". {member} is replaced with a mention of the relevant user.
        "custom_winner_messages": [],  # list of strings; if non-empty, replaces TOP_EDIT_WIN_MESSAGES entirely
        "custom_reminder_message": None,  # overrides the "you forgot to ping" nudge text
        "custom_poll_question": None,  # overrides "Vote for today's top edit!"
    }


def load_guild_config(guild_id: int) -> dict:
    config = default_guild_config()
    raw = db_get_raw(f"config:{guild_id}")
    if raw:
        try:
            saved = json.loads(raw)
            for k, v in saved.items():
                if v is None:
                    continue
                if k == "rank_role_ids" and isinstance(v, dict):
                    config["rank_role_ids"].update(v)
                else:
                    config[k] = v
        except json.JSONDecodeError:
            pass
    # Migration: servers saved before the multi-role update stored a single
    # "picker_role_id" (etc.) integer instead of a "picker_role_ids" list.
    for singular, plural in (
        ("picker_role_id", "picker_role_ids"),
        ("manager_role_id", "manager_role_ids"),
        ("staff_role_id", "staff_role_ids"),
    ):
        if singular in config:
            old_val = config.pop(singular)
            if old_val and old_val not in config[plural]:
                config[plural] = list(config[plural]) + [old_val]
    return config


def save_guild_config(guild_id: int, updates: dict) -> dict:
    config = load_guild_config(guild_id)
    for k, v in updates.items():
        if k == "rank_role_ids" and isinstance(v, dict):
            config["rank_role_ids"].update(v)
        else:
            config[k] = v
    db_set_raw(f"config:{guild_id}", json.dumps(config))
    return config



def load_points(guild_id: int):
    raw = db_get_raw(f"points:{guild_id}")
    if raw is not None:
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            return {}
    path = f"points_{guild_id}.json"
    if not os.path.exists(path):
        return {}
    try:
        with open(path, "r") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return {}


def save_points(guild_id: int, data):
    if db_set_raw(f"points:{guild_id}", json.dumps(data)):
        return
    with open(f"points_{guild_id}.json", "w") as f:
        json.dump(data, f)


def add_points(guild_id: int, user_id: int, amount: int):
    # Loads the existing file, only ever changes the single key being touched,
    # so points for every other user are always preserved across restarts/redeploys.
    data = load_points(guild_id)
    key = str(user_id)
    data[key] = max(0, data.get(key, 0) + amount)
    save_points(guild_id, data)
    return data[key]


async def apply_point_roles(guild: discord.Guild, member_id: int, total_points: int):
    member = guild.get_member(member_id)
    if not member:
        try:
            member = await guild.fetch_member(member_id)
        except discord.NotFound:
            return

    resolved_names[str(member_id)] = member.display_name
    config = load_guild_config(guild.id)
    rank_role_ids = config["rank_role_ids"]
    unranked_role_id = config.get("unranked_role_id")

    target_label = current_rank_label(total_points, guild.id)
    all_tier_role_ids = {rid for rid in rank_role_ids.values() if rid}
    desired_ids = set()
    if target_label and rank_role_ids.get(target_label):
        desired_ids.add(rank_role_ids[target_label])
    elif unranked_role_id:
        desired_ids.add(unranked_role_id)

    roles_to_remove = [
        r for r in member.roles
        if (r.id in all_tier_role_ids or r.id == unranked_role_id) and r.id not in desired_ids
    ]
    roles_to_add = [
        guild.get_role(rid) for rid in desired_ids
        if guild.get_role(rid) and guild.get_role(rid) not in member.roles
    ]

    try:
        if roles_to_remove:
            await member.remove_roles(*roles_to_remove, reason="Point tier update")
        if roles_to_add:
            await member.add_roles(*roles_to_add, reason="Point tier update")
    except discord.Forbidden:
        print(f"⚠️ Missing permission to manage roles for {member}.")


async def award_points(guild: discord.Guild, member_id: int, amount: int):
    new_total = add_points(guild.id, member_id, amount)
    await apply_point_roles(guild, member_id, new_total)
    return new_total


async def log_points_action(guild: discord.Guild, actor: discord.Member, target_id: int, amount: int, new_total: int, action: str) -> bool:
    """Posts an audit-log entry whenever someone gives/removes points, so it's always visible who did it.
    Returns True/False so the calling command can warn the user if logging silently failed."""
    config = load_guild_config(guild.id)
    log_channel_id = config["log_channel_id"]
    log_channel = guild.get_channel(log_channel_id) or find_channel(guild, log_channel_id, LOG_CHANNEL_NAME)
    if not log_channel:
        try:
            log_channel = await guild.fetch_channel(log_channel_id)
        except (discord.NotFound, discord.Forbidden, discord.HTTPException):
            log_channel = None
    if not log_channel:
        print(f"⚠️ Points log channel not found (ID {log_channel_id}). Check the ID and that the bot can see it.")
        return False

    verb = "added" if action == "add" else "removed"
    sign = "+" if action == "add" else "-"
    embed = discord.Embed(
        title="🧾 Points Log",
        description=(
            f"**{actor.mention}** {verb} **{sign}{abs(amount)}** point(s) "
            f"{'to' if action == 'add' else 'from'} <@{target_id}>."
        ),
        color=discord.Color.orange() if action == "add" else discord.Color.red(),
        timestamp=datetime.now(timezone.utc),
    )
    embed.add_field(name="New total", value=str(new_total), inline=True)
    embed.set_footer(text=f"Actor ID: {actor.id}")
    try:
        await log_channel.send(embed=embed)
        return True
    except discord.Forbidden:
        print(f"⚠️ Missing permission to post in the points log channel (ID {log_channel_id}).")
        return False
    except discord.HTTPException as e:
        print(f"⚠️ Failed to post to the points log channel: {e}")
        return False


def get_guild_rank_tiers(guild_id: int = None):
    """The (threshold, role_id, label, emoji) list for a server — using that server's own
    custom thresholds, emoji, and role assignments where set, falling back to the built-in
    defaults for anything not customized. Pass no guild_id to get the raw defaults. The tier
    label (D/C/B/A/S) itself always stays fixed — it's the internal key rank_role_ids and
    rank_thresholds are stored under, so renaming it would silently break the role lookup."""
    if guild_id is None:
        return RANK_TIERS
    config = load_guild_config(guild_id)
    thresholds = config.get("rank_thresholds") or {}
    role_ids = config.get("rank_role_ids") or {}
    emojis = config.get("rank_emojis") or {}
    tiers = []
    for default_threshold, default_role_id, label, default_emoji in RANK_TIERS:
        threshold = thresholds.get(label, default_threshold)
        role_id = role_ids.get(label, default_role_id)
        emoji = emojis.get(label) or default_emoji
        tiers.append((threshold, role_id, label, emoji))
    tiers.sort(key=lambda t: t[0])
    return tiers


def next_rank_progress(total: int, guild_id: int = None):
    """Returns (label, points_needed, current_threshold, next_threshold) for the next rank."""
    tiers = get_guild_rank_tiers(guild_id)
    prev_threshold = 0
    for threshold, _role_id, label, _emoji in tiers:
        if total < threshold:
            return label, threshold - total, prev_threshold, threshold
        prev_threshold = threshold
    return None, 0, prev_threshold, prev_threshold


def current_rank_label(total: int, guild_id: int = None):
    tiers = get_guild_rank_tiers(guild_id)
    label = None
    for threshold, _role_id, tier_label, _emoji in tiers:
        if total >= threshold:
            label = tier_label
    return label


def current_rank_emoji(total: int, guild_id: int = None):
    tiers = get_guild_rank_tiers(guild_id)
    emoji = UNRANKED_EMOJI
    for threshold, _role_id, _label, tier_emoji in tiers:
        if total >= threshold:
            emoji = tier_emoji
    return emoji


def current_rank_role_id(total: int, guild_id: int = None):
    tiers = get_guild_rank_tiers(guild_id)
    role_id = UNRANKED_ROLE_ID
    for threshold, tier_role_id, _label, _emoji in tiers:
        if total >= threshold:
            role_id = tier_role_id
    return role_id


# --- Day counter ---
def load_day(guild_id: int):
    raw = db_get_raw(f"day:{guild_id}")
    if raw is not None:
        try:
            return json.loads(raw).get("day", DEFAULT_DAY)
        except json.JSONDecodeError:
            return DEFAULT_DAY
    path = f"day_{guild_id}.json"
    if not os.path.exists(path):
        save_day(guild_id, DEFAULT_DAY)
        return DEFAULT_DAY
    try:
        with open(path, "r") as f:
            return json.load(f).get("day", DEFAULT_DAY)
    except (json.JSONDecodeError, OSError):
        return DEFAULT_DAY


def save_day(guild_id: int, day: int):
    if db_set_raw(f"day:{guild_id}", json.dumps({"day": day})):
        return
    with open(f"day_{guild_id}.json", "w") as f:
        json.dump({"day": day}, f)


# --- Video de-dupe history (permanent: a used video is never eligible again) ---
def load_video_history(guild_id: int):
    raw = db_get_raw(f"video_history:{guild_id}")
    if raw is not None:
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            return {}
    path = f"video_history_{guild_id}.json"
    if not os.path.exists(path):
        return {}
    try:
        with open(path, "r") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return {}


def save_video_history(guild_id: int, data):
    if db_set_raw(f"video_history:{guild_id}", json.dumps(data)):
        return
    with open(f"video_history_{guild_id}.json", "w") as f:
        json.dump(data, f)


# --- Risk-word list (staff-maintained, used only by the on-demand purge command below —
# nothing is auto-deleted; a Manager/Staff member has to run the command themselves) ---
def load_badwords(guild_id: int):
    raw = db_get_raw(f"badwords:{guild_id}")
    if raw is not None:
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            return []
    path = f"badwords_{guild_id}.json"
    if not os.path.exists(path):
        return []
    try:
        with open(path, "r") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return []


def save_badwords(guild_id: int, words):
    if db_set_raw(f"badwords:{guild_id}", json.dumps(words)):
        return
    with open(f"badwords_{guild_id}.json", "w") as f:
        json.dump(words, f)


# --- Ping-reminder tracking: each user only ever gets the "you forgot to ping the Picker
# role" nudge once, the very first time they post a video without it. Persisted the same
# way as everything else so it survives restarts/redeploys. ---
def load_reminded_users(guild_id: int) -> set:
    raw = db_get_raw(f"ping_reminded:{guild_id}")
    if raw is not None:
        try:
            return set(json.loads(raw))
        except json.JSONDecodeError:
            return set()
    path = f"ping_reminded_{guild_id}.json"
    if not os.path.exists(path):
        return set()
    try:
        with open(path, "r") as f:
            return set(json.load(f))
    except (json.JSONDecodeError, OSError):
        return set()


def save_reminded_users(guild_id: int, user_ids: set):
    data = list(user_ids)
    if db_set_raw(f"ping_reminded:{guild_id}", json.dumps(data)):
        return
    with open(f"ping_reminded_{guild_id}.json", "w") as f:
        json.dump(data, f)


def mark_user_reminded(guild_id: int, user_id: int):
    users = load_reminded_users(guild_id)
    users.add(user_id)
    save_reminded_users(guild_id, users)


def load_ai_rated_users(guild_id: int) -> set:
    """Unused since /rate-edit became unlimited — kept around in case a per-user limit
    (or a cooldown) is wanted again later. Tracks which users have used /rate-edit at least once."""
    raw = db_get_raw(f"ai_rated:{guild_id}")
    if raw is not None:
        try:
            return set(json.loads(raw))
        except json.JSONDecodeError:
            return set()
    path = f"ai_rated_{guild_id}.json"
    if not os.path.exists(path):
        return set()
    try:
        with open(path, "r") as f:
            return set(json.load(f))
    except (json.JSONDecodeError, OSError):
        return set()


def mark_user_ai_rated(guild_id: int, user_id: int):
    users = load_ai_rated_users(guild_id)
    users.add(user_id)
    data = list(users)
    if db_set_raw(f"ai_rated:{guild_id}", json.dumps(data)):
        return
    with open(f"ai_rated_{guild_id}.json", "w") as f:
        json.dump(data, f)


def load_ai_rating_hinted_users(guild_id: int) -> set:
    """Users (per guild) who already saw the 'you can ask for /rate-edit' tip once."""
    raw = db_get_raw(f"ai_rating_hinted:{guild_id}")
    if raw is not None:
        try:
            return set(json.loads(raw))
        except json.JSONDecodeError:
            return set()
    path = f"ai_rating_hinted_{guild_id}.json"
    if not os.path.exists(path):
        return set()
    try:
        with open(path, "r") as f:
            return set(json.load(f))
    except (json.JSONDecodeError, OSError):
        return set()


def mark_user_ai_rating_hinted(guild_id: int, user_id: int):
    users = load_ai_rating_hinted_users(guild_id)
    users.add(user_id)
    data = list(users)
    if db_set_raw(f"ai_rating_hinted:{guild_id}", json.dumps(data)):
        return
    with open(f"ai_rating_hinted_{guild_id}.json", "w") as f:
        json.dump(data, f)

# --- Has-pinged-Picker tracking: the AI-rating hint only starts showing once someone has
# successfully pinged the Picker role at least once — before that, the ping reminder is the
# only thing that matters, so we don't dilute it with an unrelated tip. ---
def load_has_pinged_users(guild_id: int) -> set:
    raw = db_get_raw(f"has_pinged_picker:{guild_id}")
    if raw is not None:
        try:
            return set(json.loads(raw))
        except json.JSONDecodeError:
            return set()
    path = f"has_pinged_picker_{guild_id}.json"
    if not os.path.exists(path):
        return set()
    try:
        with open(path, "r") as f:
            return set(json.load(f))
    except (json.JSONDecodeError, OSError):
        return set()


def mark_user_has_pinged(guild_id: int, user_id: int):
    users = load_has_pinged_users(guild_id)
    users.add(user_id)
    data = list(users)
    if db_set_raw(f"has_pinged_picker:{guild_id}", json.dumps(data)):
        return
    with open(f"has_pinged_picker_{guild_id}.json", "w") as f:
        json.dump(data, f)


# --- Tournament-poll tracking: unlike the daily Top Edit vote (which just tallies), a
# tournament poll gives every voter a role automatically and takes it back automatically once
# the poll is over. Each active poll is tracked as {message_id, channel_id, role_id, ends_at}
# so on_raw_poll_vote_add/remove and the scheduler can find which role belongs to which poll. ---
def load_tournament_polls(guild_id: int) -> list:
    raw = db_get_raw(f"tournament_polls:{guild_id}")
    if raw is not None:
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            return []
    path = f"tournament_polls_{guild_id}.json"
    if not os.path.exists(path):
        return []
    try:
        with open(path, "r") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return []


def save_tournament_polls(guild_id: int, polls: list):
    data = json.dumps(polls)
    if db_set_raw(f"tournament_polls:{guild_id}", data):
        return
    with open(f"tournament_polls_{guild_id}.json", "w") as f:
        f.write(data)


async def remove_role_from_everyone(guild: discord.Guild, role_id: int) -> int:
    """Best-effort strip of a role from every member currently holding it. Returns how many
    members it was actually removed from."""
    role = guild.get_role(role_id)
    if role is None:
        return 0
    removed = 0
    for member in list(role.members):
        try:
            await member.remove_roles(role, reason="Tournament poll ended")
            removed += 1
        except discord.HTTPException:
            pass
    return removed


# Letters commonly swapped for lookalike characters to dodge word filters.
_LEET_VARIANTS = {
    "a": "a4@",
    "e": "e3",
    "i": "i1!",
    "o": "o0",
    "s": "s5$",
    "t": "t7",
}


def _fuzzy_char_class(ch: str) -> str:
    variants = _LEET_VARIANTS.get(ch.lower())
    if variants:
        return "[" + re.escape(variants) + "]"
    return re.escape(ch)


def _build_fuzzy_word_pattern(word: str, allow_suffix: bool = True) -> str:
    """Builds a regex fragment for one word that also catches common evasion:
    leetspeak substitutions (p3d0), repeated letters (peeedo), and letters split up
    with punctuation/spaces (p.e.d.o, p-e-d-o). Still anchored to a real word start
    (\\b), so it won't false-positive on a word that merely contains it mid-word
    (e.g. 'torpedo' is safe even with an entry for 'pedo').
    allow_suffix=True also matches trailing letters (pedo -> pedos); set False for
    an exact whole-word match only (used for pure numbers, so '12' doesn't also
    match '120' or '512')."""
    parts = []
    for ch in word:
        if ch.isalnum():
            parts.append(_fuzzy_char_class(ch) + "+")  # "+" catches letter repeats
        else:
            parts.append(re.escape(ch))
        parts.append(r"[\W_]{0,2}")  # up to 2 separators (spaces/punctuation) between letters
    core = r"\b" + "".join(parts)
    return core + (r"\w*" if allow_suffix else r"\b")


def build_badwords_pattern(words):
    """Matches ANY word in `words`, fuzzy-tolerant to common filter evasion (see
    _build_fuzzy_word_pattern) while staying anchored to real word starts."""
    fuzzy_words = [_build_fuzzy_word_pattern(w.lower().strip()) for w in words if w.strip()]
    if not fuzzy_words:
        return None
    return re.compile("(?:" + "|".join(fuzzy_words) + ")", re.IGNORECASE)


def prune_video_history(data: dict) -> dict:
    # No pruning: once a video URL has been used, it stays excluded forever.
    return data


def is_video_recently_used(url: str, history: dict) -> bool:
    return url in history


def mark_video_used(url: str, history: dict):
    history[url] = datetime.now(timezone.utc).isoformat()


# --- Last collection timestamp (fixes the "yesterday's edits reappear" bug) ---
def load_last_collect_ts(guild_id: int) -> datetime:
    raw = db_get_raw(f"last_collect:{guild_id}")
    if raw is not None:
        try:
            iso_ts = json.loads(raw).get("ts")
            return datetime.fromisoformat(iso_ts)
        except (json.JSONDecodeError, TypeError, ValueError):
            return datetime.now(timezone.utc) - timedelta(hours=24)
    path = f"last_collect_{guild_id}.json"
    if not os.path.exists(path):
        return datetime.now(timezone.utc) - timedelta(hours=24)
    try:
        with open(path, "r") as f:
            iso_ts = json.load(f).get("ts")
        return datetime.fromisoformat(iso_ts)
    except (json.JSONDecodeError, OSError, TypeError, ValueError):
        return datetime.now(timezone.utc) - timedelta(hours=24)


def save_last_collect_ts(guild_id: int, ts: datetime):
    if db_set_raw(f"last_collect:{guild_id}", json.dumps({"ts": ts.isoformat()})):
        return
    with open(f"last_collect_{guild_id}.json", "w") as f:
        json.dump({"ts": ts.isoformat()}, f)


# ============================================================
# Fun message pools
# ============================================================

COIN_FLIP_WIN_MESSAGES = [
    "🪙 {member}, you lucky bastard, the coin loved you today!",
    "🪙 {member} called it (kind of) and the universe agreed. Lucky!",
    "🪙 The coin gods have spoken: {member} wins by pure chance!",
    "🪙 {member} just won a coin flip. Statistically unremarkable, emotionally huge.",
    "🪙 Flip go brrr, {member} comes out on top!",
    "🪙 {member} — no skill, all luck, and honestly? Respect.",
    "🪙 The coin landed in {member}'s favor. Somewhere, a butterfly flapped its wings.",
    "🪙 {member} wins the tiebreaker! Physics has chosen a side today.",
    "🪙 Against all odds (well, 50/50 odds), {member} takes it!",
    "🪙 {member}, the coin has spoken. Try not to let it go to your head.",
    "🪙 It's random, but {member} will absolutely brag about this anyway.",
    "🪙 {member} wins! Somewhere a mathematician is shrugging.",
    "🪙 The tiebreaker gods smiled upon {member} today.",
    "🪙 {member} — pure chaos energy, and it worked out!",
    "🪙 Heads, tails, whatever — {member} came out on top.",
    "🪙 {member} just out-flipped the competition. Legendary.",
    "🪙 A coin decided your fate, {member}, and it decided well.",
    "🪙 {member} wins the flip. No skill required, all glory earned.",
    "🪙 The odds were 50/50 and {member} took the good half.",
    "🪙 {member}, today luck is your co-pilot!",
]

# 100 unique lines used when the daily Top Edit winner is announced.
TOP_EDIT_WIN_MESSAGES = [
    "🏆 {member} cooked today. No notes.",
    "🏆 {member}'s edit just broke the internet (locally, in this server).",
    "🏆 Everyone else can go home, {member} won today.",
    "🏆 {member} really said 'watch this' and delivered.",
    "🏆 The votes are in and {member} is simply built different.",
    "🏆 {member}'s edit hit different. Congrats!",
    "🏆 Certified banger by {member}. Take a bow.",
    "🏆 {member} out here making everyone else's edits look like homework.",
    "🏆 The people have spoken: {member} is today's champion.",
    "🏆 {member} cooked so hard the kitchen's still smoking.",
    "🏆 Absolute cinema by {member}. Well deserved.",
    "🏆 {member}'s edit was simply unmatched today.",
    "🏆 Chef's kiss, {member}. Chef's kiss.",
    "🏆 {member} understood the assignment perfectly.",
    "🏆 The votes don't lie: {member} is today's top editor.",
    "🏆 {member} really pulled up with the heat today.",
    "🏆 No cap, {member}'s edit was elite.",
    "🏆 {member} took the crown fair and square.",
    "🏆 That edit from {member} was pure art.",
    "🏆 {member} — respectfully, that was insane. Congrats!",
    "🏆 {member} just set the bar for the rest of the week.",
    "🏆 Another day, another masterclass from {member}.",
    "🏆 {member}'s timing, transitions, everything — flawless.",
    "🏆 The server has spoken and {member} takes the win.",
    "🏆 {member} turned raw clips into a certified banger.",
    "🏆 That's a wrap — {member} owns today's crown.",
    "🏆 {member} really out here separating themselves from the pack.",
    "🏆 Somebody notify the judges, {member} just leveled up.",
    "🏆 {member}'s edit had the whole server talking. Deserved win.",
    "🏆 Precision, style, impact — {member} brought all three.",
    "🏆 {member} made it look effortless. Congrats, champ.",
    "🏆 The scoreboard says it all: {member} on top today.",
    "🏆 {member} cooked, plated, and served a five-star edit.",
    "🏆 That transition sequence from {member}? Unreal.",
    "🏆 {member} just added another trophy to the shelf.",
    "🏆 Editors take notes — {member} showed how it's done.",
    "🏆 {member}'s sync was so clean it should be illegal.",
    "🏆 The votes rolled in fast for {member}. Clear winner.",
    "🏆 {member} brought main-character energy to the timeline today.",
    "🏆 That's what a top edit looks like, courtesy of {member}.",
    "🏆 {member} just made everyone else's export look rushed.",
    "🏆 Big respect to {member} — today's edit was next level.",
    "🏆 {member} turned the timeline into a highlight reel.",
    "🏆 The community picked {member}, and rightfully so.",
    "🏆 {member}'s pacing alone deserved the win.",
    "🏆 Consider the bar raised, courtesy of {member}.",
    "🏆 {member} just dropped a masterpiece and walked away with it.",
    "🏆 That color grade from {member} was chef's kiss.",
    "🏆 {member} — clean cuts, cleaner win.",
    "🏆 The people wanted fire and {member} delivered.",
    "🏆 {member} just claimed the crown, no contest.",
    "🏆 Every frame from {member} today was intentional. Well earned.",
    "🏆 {member} turned a simple clip into a certified moment.",
    "🏆 Today's top edit belongs to {member}, hands down.",
    "🏆 {member}'s creativity carried the whole vote.",
    "🏆 The judges (aka everyone) agreed: {member} takes it.",
    "🏆 {member} just showed the server what elite editing looks like.",
    "🏆 That's a wrap on today's poll — {member} wins big.",
    "🏆 {member} brought the heat and the server felt it.",
    "🏆 Somebody get {member} a trophy case at this point.",
    "🏆 {member}'s edit was the clear standout of the day.",
    "🏆 The vibes, the sync, the flow — {member} nailed it all.",
    "🏆 {member} just reminded everyone why they submit daily.",
    "🏆 That edit from {member} deserves a rewatch. Congrats!",
    "🏆 {member} out-edited the entire lineup today.",
    "🏆 Certified heat, straight from {member}.",
    "🏆 {member}'s submission was simply on another level.",
    "🏆 The server's verdict is in — {member} takes the crown.",
    "🏆 {member} just cooked up today's undisputed winner.",
    "🏆 That energy from {member} was unmatched. Well done.",
    "🏆 {member} really just ended the competition early.",
    "🏆 Flawless victory for {member} today.",
    "🏆 {member}'s edit had zero weak points. Deserved win.",
    "🏆 The crown goes to {member} — no debate needed.",
    "🏆 {member} just cemented themselves as one to watch.",
    "🏆 That's today's top edit, brought to you by {member}.",
    "🏆 {member} made the grind look easy today.",
    "🏆 Respect where it's due — {member} earned this one.",
    "🏆 {member}'s edit was the definition of clean.",
    "🏆 The community crowned {member} today, and it shows.",
    "🏆 {member} just delivered a top-tier performance.",
    "🏆 That was a statement edit from {member}.",
    "🏆 {member} took the win with style to spare.",
    "🏆 Top marks all around for {member}'s edit today.",
    "🏆 {member} just outclassed the whole lineup.",
    "🏆 The scoreboard doesn't lie — {member} is today's best.",
    "🏆 {member}'s creativity is on a different level today.",
    "🏆 Congrats {member}, that edit earned every single vote.",
    "🏆 {member} just proved consistency pays off. Well deserved.",
    "🏆 That's the kind of edit that wins polls — thanks {member}.",
    "🏆 {member} brought their A-game and it showed.",
    "🏆 The timeline belongs to {member} today.",
    "🏆 {member}'s submission was simply the best of the day.",
    "🏆 A clean sweep for {member} — congrats!",
    "🏆 {member} just gave the server something to talk about.",
    "🏆 That's a certified win for {member}. Take the crown.",
    "🏆 {member}'s edit had range, rhythm, and results.",
    "🏆 The community's pick today: {member}, and it's obvious why.",
    "🏆 {member} just closed out today's poll in style.",
    "🏆 Today belongs to {member}. Absolute standout.",
]

# Used as flavor text for /points and elsewhere — professional English lines.
POINTS_CHECK_FLAVOR = [
    "Keep grinding, the ranks don't climb themselves.",
    "Every point counts, keep it up!",
    "You're closer than you think.",
    "Consistency beats talent. Keep submitting!",
    "Rank up season is always open.",
    "One good edit could change everything.",
    "Slow and steady still wins ranks.",
    "The grind is real, but so are the rewards.",
    "Discipline compounds — one submission at a time.",
    "Progress isn't always loud, but it's always visible on the leaderboard.",
    "Your next rank is closer than your last excuse.",
    "Small, consistent effort outperforms occasional bursts of brilliance.",
    "Every submission is a rep. Reps build rank.",
    "The editors who show up daily are the ones who climb.",
    "Momentum is built one edit at a time — keep the streak alive.",
    "Quality plus consistency is the formula. You're on the right track.",
    "The leaderboard rewards patience as much as skill.",
    "Today's effort is tomorrow's rank.",
    "Great editors are made through repetition, not luck.",
    "Stay sharp — the next tier is within reach.",
    "Growth in this community is earned, not given. Keep earning it.",
    "Your consistency is noticed, even when the votes are close.",
    "One more submission could be the one that ranks you up.",
    "The best editors treat every day like it matters. It does.",
    "Focus on the process — the points will follow.",
    "You don't need to win every day, just keep showing up.",
    "Reputation here is built edit by edit.",
    "Keep refining your craft — the next milestone is close.",
    "Steady contributors are the backbone of this leaderboard.",
    "Your progress speaks for itself. Keep building on it.",
]

# 50+ random one-liners shown under the leaderboard, so it never feels static.
LEADERBOARD_PAGE_SIZE = 10
LEADERBOARD_MAX_PAGES = 2  # /leaderboard only ever shows ranks 1-10, then 11-20 — that's it
LEADERBOARD_FLAVOR = [
    "The gap between #1 and #2 is one great submission away.",
    "New day, new chance to shake up this board.",
    "Somewhere on this list, tomorrow's champion is grinding right now.",
    "This board resets nobody's effort — only the numbers move.",
    "Every name here earned its spot the hard way: one edit at a time.",
    "Today's leaderboard is tomorrow's highlight reel.",
    "Ranks change fast around here. Stay sharp.",
    "The top spot has never stayed still for long.",
    "Somebody's about to overtake somebody. Keep watching.",
    "This isn't luck — it's reps, taste, and timing.",
    "The editors below #1 aren't far behind. Watch this space.",
    "Consistency built this board, not one lucky day.",
    "Every point on this list came from a real submission.",
    "The energy in this server shows up right here on the board.",
    "Somebody's climbing. Somebody's grinding. Everybody's watching.",
    "This leaderboard doesn't lie — it just updates.",
    "One more win could flip this whole board upside down.",
    "The names change, the standard doesn't.",
    "Respect to everyone who shows up here daily.",
    "This is what showing up looks like, ranked.",
    "The gap at the top is closer than it looks.",
    "Somebody's studying this list for motivation right now.",
    "Every entry here started at zero.",
    "The board rewards the ones who keep submitting.",
    "This is a snapshot, not a final answer — check back tomorrow.",
    "Nobody stays on top without staying consistent.",
    "The real competition is with yesterday's version of you.",
    "This leaderboard has seen a lot of comebacks.",
    "The next big shake-up could happen tonight at 8PM.",
    "Somewhere in this list is next week's Top Edit winner.",
    "Points don't lie, and neither does this board.",
    "The grind behind this leaderboard is real.",
    "This is what daily consistency looks like, visualized.",
    "Every rank here was earned one vote at a time.",
    "The top 10 is never permanent. Keep pushing.",
    "This board is proof that showing up matters.",
    "Somebody just moved up — check who.",
    "The community decides this list, one vote at a time.",
    "This leaderboard is a highlight reel of who's putting in the work.",
    "The next tier-up is closer than you think for a few of these names.",
    "Every submission is a vote for your own spot on this board.",
    "This list rewards patience as much as talent.",
    "The climb never really stops around here.",
    "Somebody's about to break into the top 3.",
    "This board is a live record of who's been cooking.",
    "The best time to climb this list was yesterday. The next best time is today.",
    "This leaderboard is proof the grind is paying off for someone.",
    "Every name here shows up because they submitted, not because they got lucky.",
    "The board updates fast — don't get too comfortable at the top.",
    "This is what consistency looks like when it's ranked.",
    "Somebody on this list is one edit away from their next rank.",
    "The top of this board has changed hands before. It'll happen again.",
    "This leaderboard is the server's own hall of fame, updated daily.",
]

# ============================================================
# Scheduler
# ============================================================


GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY")
GEMINI_VISION_MODEL = "gemini-2.5-flash-lite"  # most generous free-tier quota
# Optional fallback used only when Gemini itself fails (overloaded/quota/etc). OpenRouter is a
# free-model AGGREGATOR — it auto-routes to whichever provider actually has capacity, so a
# single provider's outage doesn't take the fallback down with it. Free at openrouter.ai
# (sign in with Google/GitHub — no separate account/email needed). If not set, the bot just
# behaves like before (Gemini-only).
OPENROUTER_API_KEY = os.environ.get("OPENROUTER_API_KEY")
OPENROUTER_VISION_MODEL = "meta-llama/llama-3.2-11b-vision-instruct:free"

intents = discord.Intents.default()
intents.message_content = True
intents.guilds = True
intents.members = True
bot = commands.Bot(command_prefix=commands.when_mentioned_or("!", "."), intents=intents, help_command=None)


async def migrate_legacy_data_once():
    """One-time move of this bot's original (single-server) data into the new
    per-guild storage keys. Runs once ever — guarded by a marker — so a brand new
    server joining later never inherits the old server's points by accident."""
    if db_get_raw("migrated_v2"):
        return
    for guild in bot.guilds:
        for base in ("points", "day", "video_history", "last_collect", "badwords"):
            legacy = db_get_raw(base)
            if legacy is not None and db_get_raw(f"{base}:{guild.id}") is None:
                db_set_raw(f"{base}:{guild.id}", legacy)
    db_set_raw("migrated_v2", "1")
    print("✅ Migrated legacy single-server data to per-guild storage.")


@bot.tree.error
async def on_app_command_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    """Without this, an unhandled exception in ANY slash command (a slow DB read blowing
    past Discord's 3-second response window, a permission-check bug, anything) just prints
    a traceback server-side and leaves Discord showing nothing at all to the user — it looks
    like the bot 'did nothing.' This makes sure something user-visible always happens."""
    print(f"⚠️ Slash command error in /{interaction.command.name if interaction.command else '?'}: {error}")
    message = "⚠️ Something went wrong running that command. Try again in a moment."
    try:
        if interaction.response.is_done():
            await interaction.followup.send(message, ephemeral=True)
        else:
            await interaction.response.send_message(message, ephemeral=True)
    except discord.HTTPException:
        pass  # interaction token already expired — nothing more we can do


@bot.event
async def on_ready():
    print(f"✅ Zexo is online as {bot.user}")
    print(f"📦 yt-dlp version: {yt_dlp.version.__version__}")
    if not scheduler_loop.is_running():
        scheduler_loop.start()
    for guild in bot.guilds:
        dashboard_state["guild_name"] = guild.name
        dashboard_state["member_count"] = guild.member_count or 0
    await migrate_legacy_data_once()
    try:
        synced = await bot.tree.sync()
        print(f"Synced {len(synced)} slash command(s)")
    except Exception as e:
        print(f"Slash command sync failed: {e}")


@bot.event
async def on_command_completion(ctx):
    command_usage[ctx.command.name] = command_usage.get(ctx.command.name, 0) + 1


@bot.event
async def on_member_join(member: discord.Member):
    # Add the new member to the leaderboard right away (0 points) so the total
    # editor count and rankings update immediately, without waiting for their first point.
    data = load_points(member.guild.id)
    uid = str(member.id)
    if uid not in data:
        data[uid] = 0
        save_points(member.guild.id, data)
    resolved_names[uid] = member.display_name


@bot.event
async def on_guild_join(guild: discord.Guild):
    print(f"➕ Joined new server: {guild.name} ({guild.id}) — configure it on the website dashboard's Settings page.")


@bot.event
async def on_message(message: discord.Message):
    # Nudge someone the FIRST time they post a video/link in the submissions channel without
    # pinging the Picker role — after that one nudge (ever, persisted), we stay quiet even if
    # they forget again. This does not affect collection itself: the ping is still required
    # for an edit to count, this just helps people learn the rule once instead of silently
    # losing submissions forever.
    if message.guild and not message.author.bot:
        config = load_guild_config(message.guild.id)
        submit_channel = find_channel(message.guild, config["submit_channel_id"], SUBMIT_CHANNEL_NAME)
        picker_role = find_any_role(message.guild, config["picker_role_ids"], PICKER_ROLE_NAME)
        if submit_channel and picker_role and message.channel.id == submit_channel.id:
            sources = await extract_video_sources(message)
            pinged = message_pings_role(message, picker_role)

            # Ping reminder — pinging is required for the edit to count at all, so it's the
            # more urgent of the two and goes first whenever both apply on the same message.
            show_ping_reminder = False
            reminder_text = None
            if sources and not pinged:
                reminded = load_reminded_users(message.guild.id)
                if message.author.id not in reminded:
                    mark_user_reminded(message.guild.id, message.author.id)
                    show_ping_reminder = True
                    default_reminder = f"Ping **@{PICKER_ROLE_NAME}** in the same message so your edit counts."
                    reminder_text = (config.get("custom_reminder_message") or default_reminder).format(
                        member=message.author.mention
                    )

            # AI-rating hint — only once this person has actually pinged the Picker role
            # successfully at least once (on this message or an earlier one).
            if sources and pinged:
                mark_user_has_pinged(message.guild.id, message.author.id)
            show_hint = False
            if sources and message.author.id in load_has_pinged_users(message.guild.id):
                hint_key_users = load_ai_rating_hinted_users(message.guild.id)
                if message.author.id not in hint_key_users:
                    mark_user_ai_rating_hinted(message.guild.id, message.author.id)
                    show_hint = True

            # Both fit in one short, single embed — ping section first, AI-rating second —
            # instead of two separate messages.
            if show_ping_reminder or show_hint:
                sections = []
                if show_ping_reminder:
                    sections.append(f"📌 **Don't forget to ping!**\n{reminder_text}")
                if show_hint:
                    sections.append("✨ **Get AI feedback** — run `.airating` for a score, software guess, and tips.")
                combo_embed = discord.Embed(
                    description="\n\n".join(sections),
                    color=discord.Color.from_rgb(245, 158, 11) if show_ping_reminder else discord.Color.from_rgb(34, 255, 176),
                    timestamp=discord.utils.utcnow(),
                )
                combo_embed.set_thumbnail(url=message.author.display_avatar.url)
                combo_embed.set_footer(
                    text="Zexo • Top Edit",
                    icon_url=bot.user.display_avatar.url if bot.user else discord.Embed.Empty,
                )
                try:
                    await message.reply(embed=combo_embed, mention_author=False)
                except discord.HTTPException:
                    pass

    await bot.process_commands(message)


@bot.event
async def on_raw_poll_vote_add(payload: discord.RawPollVoteActionEvent):
    """Tournament polls (see /tournamentpoll) give the configured role to anyone who votes —
    this is what actually assigns it the moment someone votes."""
    if payload.guild_id is None:
        return
    polls = load_tournament_polls(payload.guild_id)
    match = next((p for p in polls if p["message_id"] == payload.message_id), None)
    if match is None:
        return
    guild = bot.get_guild(payload.guild_id)
    if guild is None:
        return
    role = guild.get_role(match["role_id"])
    if role is None:
        return
    try:
        member = guild.get_member(payload.user_id) or await guild.fetch_member(payload.user_id)
    except discord.NotFound:
        return
    try:
        await member.add_roles(role, reason="Voted in tournament poll")
    except discord.HTTPException:
        pass


@bot.event
async def on_raw_poll_vote_remove(payload: discord.RawPollVoteActionEvent):
    """If someone retracts their tournament-poll vote, take the role back too."""
    if payload.guild_id is None:
        return
    polls = load_tournament_polls(payload.guild_id)
    match = next((p for p in polls if p["message_id"] == payload.message_id), None)
    if match is None:
        return
    guild = bot.get_guild(payload.guild_id)
    if guild is None:
        return
    role = guild.get_role(match["role_id"])
    if role is None:
        return
    try:
        member = guild.get_member(payload.user_id) or await guild.fetch_member(payload.user_id)
    except discord.NotFound:
        return
    try:
        await member.remove_roles(role, reason="Retracted tournament poll vote")
    except discord.HTTPException:
        pass


@tasks.loop(minutes=1)
async def scheduler_loop():
    now = datetime.now(EU_TZ)
    for guild in bot.guilds:
        config = load_guild_config(guild.id)
        gid = guild.id

        collect_hour = config.get("collect_hour", COLLECT_HOUR)
        collect_minute = config.get("collect_minute", 0)
        if now.hour == collect_hour and now.minute == collect_minute and last_collect_dates.get(gid) != now.date():
            last_collect_dates[gid] = now.date()
            await run_collect_job_for_guild(guild)

        results_hour = config.get("results_hour", RESULTS_HOUR)
        results_minute = config.get("results_minute", 0)
        if now.hour == results_hour and now.minute == results_minute and last_results_dates.get(gid) != now.date():
            last_results_dates[gid] = now.date()
            await run_results_job_for_guild(guild)


def make_word_matcher(word: str) -> re.Pattern:
    """Fuzzy match (leetspeak, split-up letters, repeats) for one word. Pure numbers
    stay a strict, exact whole-word match — no fuzz at all — so searching '12'
    matches only an actual standalone '12', not '123', '512', or '1 2 3'."""
    word = word.strip()
    if word.isdigit():
        return re.compile(rf"\b{re.escape(word)}\b")
    pattern = _build_fuzzy_word_pattern(word.lower(), allow_suffix=True)
    return re.compile(pattern, re.IGNORECASE)


async def _purge_channel_core(channel: discord.TextChannel, pattern: re.Pattern, on_batch=None) -> tuple:
    """Low-level scan+delete loop for one channel, matching ANY word in `pattern`.
    Scans the ENTIRE channel history and deletes as it goes (not after collecting
    everything first). `on_batch(scanned, deleted)`, if given, is called periodically
    so callers can report live progress. Returns (scanned, deleted)."""
    deleted_total = 0
    scanned = 0
    bulk_batch = []

    async def flush_bulk_batch():
        nonlocal deleted_total, bulk_batch
        if not bulk_batch:
            return
        try:
            await channel.delete_messages(bulk_batch)
            deleted_total += len(bulk_batch)
        except discord.HTTPException:
            pass
        bulk_batch = []

    try:
        async for msg in channel.history(limit=None):
            scanned += 1
            if pattern.search(msg.content):
                if datetime.now(timezone.utc) - msg.created_at < timedelta(days=14):
                    bulk_batch.append(msg)
                    if len(bulk_batch) >= 100:
                        await flush_bulk_batch()
                else:
                    try:
                        await msg.delete()
                        deleted_total += 1
                    except discord.HTTPException:
                        pass
                    await asyncio.sleep(0.5)  # avoid rate limits on single (>14 day old) deletes

            if on_batch and scanned % 250 == 0:
                await on_batch(scanned, deleted_total)
    except discord.Forbidden:
        pass

    await flush_bulk_batch()
    return scanned, deleted_total


async def purge_messages_with_word(channel: discord.TextChannel, word: str, progress=None) -> int:
    """Single channel, single word — used by !purgeword / /purgeword.
    `progress`, if given, is an async callable: progress(scanned, deleted, final=False)."""
    pattern = make_word_matcher(word)

    async def on_batch(scanned, deleted):
        if progress:
            await progress(scanned, deleted)

    scanned, deleted = await _purge_channel_core(channel, pattern, on_batch=on_batch if progress else None)
    if progress:
        await progress(scanned, deleted, final=True)
    return deleted


async def purge_channel_with_words(channel: discord.TextChannel, words, progress=None) -> int:
    """Single channel, checked against EVERY word in `words` at once — used by !purgebadwords."""
    pattern = build_badwords_pattern(words)
    if not pattern:
        return 0

    async def on_batch(scanned, deleted):
        if progress:
            await progress(scanned, deleted)

    scanned, deleted = await _purge_channel_core(channel, pattern, on_batch=on_batch if progress else None)
    if progress:
        await progress(scanned, deleted, final=True)
    return deleted


async def purge_guild_with_words(guild: discord.Guild, words, progress=None) -> tuple:
    """Every word in `words`, across EVERY text channel the bot can manage in the server.
    `progress(channel, channels_done, channels_total, total_scanned, total_deleted)` is
    called after each channel finishes. Returns (channels_scanned, total_scanned, total_deleted)."""
    pattern = build_badwords_pattern(words)
    if not pattern:
        return 0, 0, 0

    channels = [
        c for c in guild.text_channels
        if c.permissions_for(guild.me).manage_messages and c.permissions_for(guild.me).read_message_history
    ]
    total_scanned = 0
    total_deleted = 0

    for i, channel in enumerate(channels, start=1):
        scanned, deleted = await _purge_channel_core(channel, pattern, on_batch=None)
        total_scanned += scanned
        total_deleted += deleted
        if progress:
            await progress(channel, i, len(channels), total_scanned, total_deleted)

    return len(channels), total_scanned, total_deleted


# YouTube/TikTok/Instagram/Streamable/etc links get downloaded and re-posted as a real video
# attachment (instead of a bare link) so they preview/play properly in Discord like a native
# upload. Rather than a fixed whitelist (which silently skipped anything not on the list, e.g.
# Streamable or random reupload hosts like video.itzcrih.it), we now try yt-dlp on ANY link that
# isn't already a direct file/CDN URL, and just fall back to posting the raw link if yt-dlp
# doesn't recognize the site or the download fails.
SOCIAL_VIDEO_DOMAINS = (
    "youtube.com", "youtu.be", "m.youtube.com",
    "tiktok.com", "vm.tiktok.com", "vt.tiktok.com",
    "instagram.com", "instagr.am",
    "streamable.com",
)
# Hosts that already serve a direct file / native Discord-friendly embed — no point routing
# these through yt-dlp.
DIRECT_LINK_DOMAINS = (
    "cdn.discordapp.com", "media.discordapp.net", "discordapp.com",
)
# No hardcoded cap anymore — Discord itself enforces a per-guild upload ceiling depending on
# boost level (25MB normally, 50MB/100MB with enough boosts). guild.filesize_limit already
# reflects that in real time, so we ask yt-dlp to fill up to whatever that guild is actually
# allowed, instead of an arbitrary constant that under-used boosted servers.


def _get_host(url: str) -> str:
    try:
        host = re.sub(r"^https?://", "", url).split("/")[0].lower()
        host = re.sub(r"^www\.", "", host)
        return host
    except Exception:
        return ""


def is_social_video_link(url: str) -> bool:
    """True for anything worth attempting a yt-dlp download on — the known big platforms,
    plus every other link that isn't a direct Discord CDN file. This is intentionally broad:
    yt-dlp supports hundreds of sites (Streamable, X/Twitter, Reddit, custom reupload hosts,
    etc.), and download_social_video() already falls back to the raw link on any failure, so
    being permissive here just means "try to convert it" rather than "only convert these five
    domains"."""
    host = _get_host(url)
    if not host:
        return False
    if any(host == d or host.endswith("." + d) for d in DIRECT_LINK_DOMAINS):
        return False
    return True


def _yt_dlp_download(url: str, out_path: str, max_bytes: int):
    ydl_opts = {
        # Was "mp4/bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[filesize<X]/best" — too narrow:
        # the Android/iOS player clients below don't always expose separate ext=mp4/m4a-tagged
        # streams, so that combo can fail outright with "Requested format is not available"
        # even though perfectly good streams exist. merge_output_format below already forces
        # an mp4 container regardless of source codec, so we don't need the ext filters here.
        "format": "bestvideo*+bestaudio/best",
        "outtmpl": out_path,
        "quiet": True,
        "no_warnings": True,
        "noplaylist": True,
        "max_filesize": max_bytes,
        "merge_output_format": "mp4",
        # Cloud-hosted IPs (Render etc.) regularly get hit with YouTube's "Sign in to confirm
        # you're not a bot" wall. Cookies (below) are what actually fix that — once they're
        # set, the web client gets the FULL format list again, so it goes first. Android/iOS
        # are kept only as a fallback for when cookies are missing/expired, since those clients
        # often expose a much narrower set of formats (which is what caused "Requested format
        # is not available" even after the bot-check itself was solved).
        "extractor_args": {
            "youtube": {"player_client": ["web", "android", "ios"]},
        },
        "http_headers": {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                          "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
        },
    }
    # Optional: a PO-Token provider fixes YouTube's newer "Requested format is not available"
    # wall (a proof-of-origin check that Cloud IPs increasingly hit even with valid cookies +
    # up-to-date yt-dlp). Set POT_PROVIDER_URL to a running bgutil-ytdlp-pot-provider server's
    # base URL (see the setup notes) to enable it — does nothing if unset, so this is a no-op
    # until it's actually configured.
    pot_base_url = os.environ.get("POT_PROVIDER_URL")
    if pot_base_url:
        ydl_opts["extractor_args"]["youtubepot-bgutilhttp"] = {"base_url": [pot_base_url]}

    # Optional: if YT/TikTok still get bot-walled even with the client spoofing above, you can
    # export cookies from a real logged-in browser session (e.g. with the "Get cookies.txt"
    # extension) and point one of these env vars at that file's path on the server. This is the
    # single most reliable fix for persistent "sign in to confirm you're not a bot" errors —
    # the client-spoofing trick above only helps some of the time. Separate files per platform
    # since YouTube and TikTok cookies aren't interchangeable.
    host = _get_host(url)
    if "tiktok.com" in host:
        cookies_path = os.environ.get("YTDLP_COOKIES_FILE_TIKTOK")
    elif "youtube.com" in host or "youtu.be" in host:
        cookies_path = os.environ.get("YTDLP_COOKIES_FILE_YOUTUBE")
    else:
        cookies_path = None
    if cookies_path and os.path.exists(cookies_path):
        ydl_opts["cookiefile"] = cookies_path
    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        ydl.download([url])


def _download_social_photos(url: str, max_images: int = 4) -> list[str]:
    """Best-effort fallback for TikTok/Instagram-style 'photo mode' posts (a slideshow of
    images with no actual video stream) — these fail the normal video download since there's
    no video to grab. Pulls the individual slide images straight from yt-dlp's metadata instead.
    Returns local JPEG paths (caller deletes them). Empty list on any failure."""
    ydl_opts = {
        "quiet": True, "no_warnings": True, "skip_download": True,
        "http_headers": {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                          "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
        },
    }
    try:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
    except Exception as e:
        print(f"⚠️ Photo-post metadata fetch failed for {url}: {e}")
        return []

    image_urls = []
    # Newer yt-dlp exposes TikTok photo-mode slides directly as info["images"].
    if info.get("images"):
        for img in info["images"]:
            u = img.get("url")
            if u:
                image_urls.append(u)
    elif info.get("thumbnails"):
        # Older yt-dlp: thumbnails list is many sizes of the SAME slide(s) mixed together,
        # so keep only the largest thumbnail per distinct slide id.
        best_by_id = {}
        for th in info["thumbnails"]:
            tid = th.get("id", th.get("url"))
            if tid not in best_by_id or (th.get("width") or 0) > (best_by_id[tid].get("width") or 0):
                best_by_id[tid] = th
        image_urls = [th["url"] for th in best_by_id.values() if th.get("url")]

    paths = []
    for img_url in image_urls[:max_images]:
        try:
            resp = http_requests.get(img_url, timeout=20)
            if resp.status_code == 200 and resp.content:
                out_path = f"/tmp/photo_{random.randint(0, 10**9)}.jpg"
                with open(out_path, "wb") as f:
                    f.write(resp.content)
                paths.append(out_path)
        except Exception as e:
            print(f"⚠️ Failed downloading slide image {img_url}: {e}")
    return paths


def _download_streamable_direct(url: str, out_path: str, max_bytes: int) -> bool:
    """Fallback for streamable.com links when yt-dlp's extractor fails (site changes /
    CDN quirks break it more often than most). Streamable exposes a small public JSON API
    that gives the direct mp4 CDN URL for a given short code — no auth needed. Returns True
    on success (out_path written), False on any failure so the caller can fall back further."""
    try:
        m = re.search(r"streamable\.com/(?:e/)?([a-zA-Z0-9]+)", url)
        if not m:
            return False
        shortcode = m.group(1)
        resp = http_requests.get(f"https://api.streamable.com/videos/{shortcode}", timeout=15)
        resp.raise_for_status()
        data = resp.json()
        files = data.get("files", {})
        candidate = files.get("mp4") or files.get("mp4-mobile")
        if not candidate or not candidate.get("url"):
            return False
        video_url = candidate["url"]
        if video_url.startswith("//"):
            video_url = "https:" + video_url
        size = candidate.get("size")
        if size and size > max_bytes:
            return False
        with http_requests.get(video_url, stream=True, timeout=60) as r:
            r.raise_for_status()
            total = 0
            with open(out_path, "wb") as f:
                for chunk in r.iter_content(chunk_size=1024 * 256):
                    total += len(chunk)
                    if total > max_bytes:
                        raise ValueError("Streamable direct download exceeded guild upload limit")
                    f.write(chunk)
        return os.path.exists(out_path) and os.path.getsize(out_path) > 0
    except Exception as e:
        print(f"⚠️ Streamable direct-API fallback failed for {url}: {e}")
        if os.path.exists(out_path):
            os.remove(out_path)
        return False


async def download_social_video(url: str, guild: discord.Guild = None) -> str | None:
    """Downloads a link as an actual mp4 via yt-dlp, so it can be re-uploaded as a real Discord
    video attachment. Returns a local file path on success, or None if the download fails / is
    too large for THIS guild's actual upload ceiling — callers should fall back to the raw link
    in that case."""
    max_bytes = guild.filesize_limit if guild is not None else (25 * 1024 * 1024)
    out_path = f"/tmp/dl_{random.randint(0, 10**9)}.mp4"
    loop = asyncio.get_running_loop()
    try:
        await loop.run_in_executor(None, _yt_dlp_download, url, out_path, max_bytes)
    except Exception as e:
        print(f"⚠️ yt-dlp download failed for {url}: {type(e).__name__}: {e}")
        if os.path.exists(out_path):
            os.remove(out_path)
        # yt-dlp's streamable.com extractor breaks whenever the site tweaks its page/CDN —
        # try Streamable's own public API directly before giving up on this link entirely.
        if "streamable.com" in _get_host(url):
            ok = await loop.run_in_executor(None, _download_streamable_direct, url, out_path, max_bytes)
            if not ok:
                return None
        else:
            return None

    if not os.path.exists(out_path) or os.path.getsize(out_path) == 0:
        return None
    if os.path.getsize(out_path) > max_bytes:
        os.remove(out_path)
        print(f"⚠️ Downloaded video too large for this guild's upload limit, falling back to link: {url}")
        return None
    return out_path


# ============================================================
# AI features: /rate-edit and /find-asset helpers
# ============================================================

def _extract_frames(video_path: str, count: int = 4) -> list[str]:
    """Grabs `count` evenly-spaced JPEG frames from a video via ffmpeg/ffprobe.
    Returns a list of temp file paths (caller must delete them). Best-effort — returns
    fewer frames (or an empty list) instead of raising if the video is very short/odd."""
    try:
        probe = subprocess.run(
            ["ffprobe", "-v", "error", "-show_entries", "format=duration",
             "-of", "default=noprint_wrappers=1:nokey=1", video_path],
            capture_output=True, text=True, timeout=20,
        )
        duration = float(probe.stdout.strip())
    except Exception:
        duration = 0

    if duration <= 0:
        timestamps = [0.5]
    else:
        # Evenly spaced, staying slightly inside the start/end so we don't grab black frames.
        timestamps = [duration * (i + 1) / (count + 1) for i in range(count)]

    frame_paths = []
    for ts in timestamps:
        out_path = f"/tmp/frame_{random.randint(0, 10**9)}.jpg"
        try:
            subprocess.run(
                ["ffmpeg", "-y", "-ss", str(ts), "-i", video_path, "-frames:v", "1",
                 "-q:v", "2", out_path],
                capture_output=True, timeout=20,
            )
            if os.path.exists(out_path) and os.path.getsize(out_path) > 0:
                frame_paths.append(out_path)
        except Exception as e:
            print(f"⚠️ Frame extraction failed at {ts}s: {e}")
    return frame_paths


_gemini_working_model = None  # cached once we successfully discover a model that works


def _call_openrouter_vision(frame_paths: list[str], prompt: str) -> str:
    """Fallback backend — same job as _call_gemini_vision but via OpenRouter's OpenAI-compatible
    endpoint. OpenRouter auto-routes each request to whichever backing provider of the model
    actually has capacity right now, and we also hand it a couple of alternate free vision
    models to fall back through — so this is used whenever Gemini itself is down/overloaded/
    quota-exhausted. Raises RuntimeError on failure."""
    content = [{"type": "text", "text": prompt}]
    for path in frame_paths:
        with open(path, "rb") as f:
            b64 = base64.b64encode(f.read()).decode("utf-8")
        content.append({"type": "image_url", "image_url": {"url": f"data:image/jpeg;base64,{b64}"}})

    resp = http_requests.post(
        "https://openrouter.ai/api/v1/chat/completions",
        headers={
            "Authorization": f"Bearer {OPENROUTER_API_KEY}",
            "Content-Type": "application/json",
            "HTTP-Referer": "https://sapph.xyz/",
            "X-Title": "Zexo Discord Bot",
        },
        json={
            "model": OPENROUTER_VISION_MODEL,
            # If the primary free model is also down/rate-limited, OpenRouter tries these next
            # automatically — no code changes needed if one of them gets retired later.
            "models": [
                OPENROUTER_VISION_MODEL,
                "qwen/qwen2.5-vl-32b-instruct:free",
                "google/gemini-2.0-flash-exp:free",
            ],
            "messages": [{"role": "user", "content": content}],
            "max_tokens": 1024,
        },
        timeout=60,
    )
    if resp.status_code != 200:
        print(f"⚠️ OpenRouter API error {resp.status_code}: {resp.text[:300]}")
        raise RuntimeError(f"OpenRouter fallback also failed (HTTP {resp.status_code}).")

    data = resp.json()
    try:
        return data["choices"][0]["message"]["content"].strip() or "No feedback returned."
    except (KeyError, IndexError):
        print(f"⚠️ Unexpected OpenRouter response shape: {data}")
        raise RuntimeError("OpenRouter fallback also failed (unexpected response).")


def _discover_working_gemini_model() -> str | None:
    """Calls Gemini's ListModels endpoint to find a model this exact API key actually has
    access to that supports generateContent — used as a fallback when GEMINI_VISION_MODEL
    404s (wrong/retired name, or key scoped to different models)."""
    try:
        resp = http_requests.get(
            "https://generativelanguage.googleapis.com/v1beta/models",
            params={"key": GEMINI_API_KEY},
            timeout=20,
        )
        if resp.status_code != 200:
            print(f"⚠️ Gemini ListModels failed too ({resp.status_code}): {resp.text[:300]}")
            return None
        models = resp.json().get("models", [])
        candidates = [
            m["name"].removeprefix("models/") for m in models
            if "generateContent" in m.get("supportedGenerationMethods", [])
        ]
        # Prefer a flash-lite/flash model (cheap, generous free-tier quota) over pro if we have a choice.
        for pref in ("flash-lite", "flash", ""):
            for name in candidates:
                if pref in name:
                    print(f"✅ Gemini auto-discovered working model: {name}")
                    return name
        return None
    except Exception as e:
        print(f"⚠️ Gemini ListModels request failed: {e}")
        return None


def _call_gemini_vision(frame_paths: list[str], prompt: str) -> str:
    """Sends the given frames + prompt to the free Gemini API and returns the text reply.
    Raises RuntimeError with a user-safe message on any failure."""
    global _gemini_working_model
    if not GEMINI_API_KEY:
        raise RuntimeError("AI rating isn't configured yet — ask a server admin to set GEMINI_API_KEY (it's free, see setup notes).")

    parts = [{"text": prompt}]
    for path in frame_paths:
        with open(path, "rb") as f:
            b64 = base64.b64encode(f.read()).decode("utf-8")
        parts.append({"inline_data": {"mime_type": "image/jpeg", "data": b64}})

    model_to_use = _gemini_working_model or GEMINI_VISION_MODEL

    def _do_request(model_name):
        return http_requests.post(
            f"https://generativelanguage.googleapis.com/v1beta/models/{model_name}:generateContent",
            params={"key": GEMINI_API_KEY},
            json={"contents": [{"parts": parts}]},
            timeout=60,
        )

    resp = _do_request(model_to_use)

    # 503 = Google's servers are momentarily overloaded, not a config problem — retry a
    # couple times with a short pause before giving up.
    retries = 0
    while resp.status_code == 503 and retries < 2:
        time.sleep(2)
        resp = _do_request(model_to_use)
        retries += 1

    # First-ever 404 on the configured model → look up a model this key can actually use,
    # remember it for every future call, and retry immediately instead of failing this one.
    if resp.status_code == 404 and model_to_use == GEMINI_VISION_MODEL:
        discovered = _discover_working_gemini_model()
        if discovered and discovered != model_to_use:
            _gemini_working_model = discovered
            resp = _do_request(discovered)
            model_to_use = discovered

    if resp.status_code != 200:
        print(f"⚠️ Gemini API error {resp.status_code} (model={model_to_use}): {resp.text[:300]}")

        # Gemini itself is down/overloaded/quota-exhausted — try OpenRouter (aggregates many
        # providers, auto-routes to whichever has capacity) before giving up entirely.
        if OPENROUTER_API_KEY:
            try:
                return _call_openrouter_vision(frame_paths, prompt)
            except RuntimeError as or_err:
                print(f"⚠️ OpenRouter fallback also failed: {or_err}")

        if resp.status_code == 404:
            reason = (
                f"model `{model_to_use}` wasn't found (404), and no working model could be "
                "auto-discovered — GEMINI_API_KEY likely doesn't have Generative Language API "
                "access enabled on its Google Cloud project."
            )
        elif resp.status_code == 403:
            reason = "access denied (403) — GEMINI_API_KEY is invalid or the API isn't enabled for that project."
        elif resp.status_code == 429:
            reason = "rate limit / free-tier quota exceeded (429) — try again in a minute."
        elif resp.status_code == 400:
            reason = "bad request (400) — check the request format or that the key itself is correctly formatted."
        elif resp.status_code == 503:
            reason = "Google's AI servers are temporarily overloaded (503) — this usually clears up within a minute, just try again."
        else:
            reason = f"HTTP {resp.status_code}"
        raise RuntimeError(f"The AI rating service didn't respond correctly ({reason}).")

    data = resp.json()
    try:
        text_parts = [p["text"] for p in data["candidates"][0]["content"]["parts"] if "text" in p]
        return "\n".join(text_parts).strip() or "No feedback returned."
    except (KeyError, IndexError):
        print(f"⚠️ Unexpected Gemini response shape: {data}")
        raise RuntimeError("The AI rating service didn't respond correctly. Try again in a bit.")


ASK_AI_PROMPT_HEADER = (
    "You are a helpful, knowledgeable general-purpose AI assistant living inside a Discord "
    "server for video editors — answer like ChatGPT or Gemini would, direct and useful, not "
    "just about editing specifically. If image(s) are attached (screenshots of software, "
    "settings, error messages, or sampled video frames), actually look at them and use what "
    "you see in your answer. Keep it focused and readable in a Discord message — roughly under "
    "300 words unless the question genuinely needs more — and use markdown (bold, bullet "
    "points) where it helps clarity. Here is their question: "
)


async def _gather_ask_ai_media(message: discord.Message) -> tuple[list[str], list[str]]:
    """Pulls up to 4 images to hand the AI for /askai — either direct image attachments
    (e.g. a screenshot of an editing-software error), or sampled frames from a video
    attachment/link if that's what's there instead. Returns (image_paths, video_paths) —
    video_paths holds any downloaded video file that also needs deleting once its frames
    have been extracted, since it isn't sent to the AI itself."""
    image_paths = []
    for att in message.attachments:
        if att.content_type and att.content_type.startswith("image") and len(image_paths) < 4:
            out_path = f"/tmp/askai_{random.randint(0, 10**9)}.jpg"
            await att.save(out_path)
            image_paths.append(out_path)

    if image_paths:
        return image_paths, []

    video_path, _ = await _get_video_path_from_message(message)
    if not video_path:
        return [], []
    frames = await asyncio.get_running_loop().run_in_executor(None, _extract_frames, video_path, 4)
    return frames, [video_path]


def _web_search(query: str, image_search: bool = True, num: int = 5) -> list[dict]:
    """Free web/image search via DuckDuckGo (no API key needed). Returns a list of
    {title, link, image} dicts. Raises RuntimeError with a user-safe message on failure."""
    try:
        with DDGS() as ddgs:
            if image_search:
                raw = list(ddgs.images(query, max_results=num, safesearch="moderate"))
                return [{"title": r.get("title", "Untitled"), "link": r.get("url"), "image": r.get("image")} for r in raw]
            else:
                raw = list(ddgs.text(query, max_results=num, safesearch="moderate"))
                return [{"title": r.get("title", "Untitled"), "link": r.get("href"), "image": None} for r in raw]
    except Exception as e:
        print(f"⚠️ DuckDuckGo search failed: {e}")
        raise RuntimeError("The web search didn't respond correctly. Try again in a bit.")


async def _get_video_path_from_message(message: discord.Message) -> tuple[str | None, bool]:
    """Best-effort: pulls a local mp4 path out of a message, either from a video
    attachment or the first social-video link found in its content. Returns
    (path, link_found) — path is None if nothing usable was downloaded, and
    link_found tells the caller WHY: True means a link/attachment was there but the
    download itself failed (so show the real error, not "you didn't give me a link"),
    False means there was genuinely nothing to work with. Caller is responsible for
    deleting the returned path when done."""
    for att in message.attachments:
        if att.content_type and att.content_type.startswith("video"):
            out_path = f"/tmp/rate_{random.randint(0, 10**9)}.mp4"
            await att.save(out_path)
            return out_path, True

    url_match = re.search(r"https?://\S+", message.content or "")
    if url_match and is_social_video_link(url_match.group(0)):
        path = await download_social_video(url_match.group(0), message.guild)
        return path, True

    return None, False


def message_pings_role(msg: discord.Message, role: discord.Role) -> bool:
    """True if the Picker role is pinged anywhere relevant to this message.

    msg.role_mentions only reflects a real <@&ROLE_ID> mention typed directly in the
    top-level message. That misses two real cases we were silently dropping edits for:
      1. Forwarded messages — Discord puts the original content in msg.message_snapshots,
         not msg.content, so a ping that was part of the *original* message never shows up
         in msg.role_mentions on the forward wrapper.
      2. The literal mention token <@&ROLE_ID> appearing in raw content/snapshot text even
         when, for whatever client-side reason, it didn't get parsed into msg.role_mentions.
    We check both the parsed mentions and a raw-text search for the mention token, on both
    the message itself and any forwarded snapshots.
    """
    if role in msg.role_mentions:
        return True

    token = f"<@&{role.id}>"
    if token in (msg.content or ""):
        return True

    for snapshot in (getattr(msg, "message_snapshots", None) or []):
        if token in (getattr(snapshot, "content", "") or ""):
            return True
        snapshot_role_mentions = getattr(snapshot, "role_mentions", None)
        if snapshot_role_mentions and role in snapshot_role_mentions:
            return True

    return False


async def extract_video_sources(msg: discord.Message):
    """Returns every distinct video/attachment/link found in a message as (url, author) pairs
    (supports multiple). `author` is normally msg.author, EXCEPT for a video pulled from a
    replied-to message (see below), where it's the original poster of that video — not
    whoever added the reply/ping — so credit/leaderboard points go to the right person.

    Also looks inside forwarded messages: Discord's "Forward" feature does not copy the
    original attachments/content into msg.attachments/msg.content — they live in
    msg.message_snapshots instead, so without this a forwarded video would be silently
    missed and never counted at all. (Discord doesn't expose the original author on a
    forward snapshot, so those stay attributed to whoever forwarded them.)

    Also looks at the message being REPLIED to: a "reply" only carries the video if it's
    the reply's own attachment/link — if someone replies to an earlier video post (e.g. to
    add the Picker ping they forgot the first time), the video itself lives on the original
    message, not the reply, and msg.reference doesn't expose its content directly. We pull
    it in via msg.reference.resolved (or a fetch if Discord didn't hand us a cached copy),
    and credit it to that original message's author."""
    sources = []
    for attachment in msg.attachments:
        sources.append((attachment.url, msg.author))
    for word in msg.content.split():
        if word.startswith("http://") or word.startswith("https://"):
            sources.append((word, msg.author))

    for snapshot in (getattr(msg, "message_snapshots", None) or []):
        for attachment in getattr(snapshot, "attachments", []) or []:
            sources.append((attachment.url, msg.author))
        snapshot_content = getattr(snapshot, "content", "") or ""
        for word in snapshot_content.split():
            if word.startswith("http://") or word.startswith("https://"):
                sources.append((word, msg.author))
        for embed in getattr(snapshot, "embeds", []) or []:
            if getattr(embed, "url", None):
                sources.append((embed.url, msg.author))
            if getattr(embed, "video", None) and getattr(embed.video, "url", None):
                sources.append((embed.video.url, msg.author))

    reference = getattr(msg, "reference", None)
    if reference is not None:
        replied = reference.resolved
        if replied is None and reference.message_id and reference.channel_id:
            try:
                ref_channel = msg.guild.get_channel(reference.channel_id) or await msg.guild.fetch_channel(reference.channel_id)
                replied = await ref_channel.fetch_message(reference.message_id)
            except (discord.NotFound, discord.Forbidden, discord.HTTPException):
                replied = None
        if isinstance(replied, discord.Message):
            for attachment in replied.attachments:
                sources.append((attachment.url, replied.author))
            for word in (replied.content or "").split():
                if word.startswith("http://") or word.startswith("https://"):
                    sources.append((word, replied.author))

    seen = set()
    unique_sources = []
    for url, author in sources:
        if url not in seen:
            seen.add(url)
            unique_sources.append((url, author))
    return unique_sources


async def collect_pending_entries(guild: discord.Guild):
    """Live look at what the next collect run would pick up: scans the submission channel for
    edits already posted with the Picker-role ping since the last collect, without posting or
    marking anything as used. Returns None if the channel/role can't be found, else a list."""
    config = load_guild_config(guild.id)
    submit_channel = find_channel(guild, config["submit_channel_id"], SUBMIT_CHANNEL_NAME)
    picker_role = find_any_role(guild, config["picker_role_ids"], PICKER_ROLE_NAME)
    if not submit_channel or not picker_role:
        return None

    since = load_last_collect_ts(guild.id)
    video_history = load_video_history(guild.id)
    entries = []

    async for msg in submit_channel.history(after=since, limit=None):
        if msg.author.bot:
            continue
        if not message_pings_role(msg, picker_role):
            continue
        for video_source, video_author in await extract_video_sources(msg):
            if is_video_recently_used(video_source, video_history):
                continue
            entries.append({"author_id": video_author.id, "author_name": video_author.display_name, "video_url": video_source})

    return entries


async def run_collect_job():
    """Runs independently for every server the bot is in — used by the manual
    'Run Collect Now' button, which intentionally fires for every server at once."""
    for guild in bot.guilds:
        await run_collect_job_for_guild(guild)


async def run_collect_job_for_guild(guild: discord.Guild):
    """Collect + open today's poll for exactly one server, using that server's own
    channels/roles, dedupe history, poll state, poll duration and poll question —
    one server's vote can never overwrite another's. No cap on how many edits get
    collected: every qualifying, not-recently-used edit posted since the last run
    is included, however many that is."""
    poll_state = get_poll_state(guild.id)
    poll_state["entries"] = []
    poll_state["polls"] = []

    config = load_guild_config(guild.id)
    submit_channel = find_channel(guild, config["submit_channel_id"], SUBMIT_CHANNEL_NAME)
    discussion_channel = find_channel(guild, config["discussion_channel_id"], DISCUSSION_CHANNEL_NAME)
    picker_role = find_any_role(guild, config["picker_role_ids"], PICKER_ROLE_NAME)

    if not submit_channel or not discussion_channel or not picker_role:
        print(f"⚠️ Missing channel/role in guild {guild.name} — configure it on the website dashboard's Settings page first. Skipping.")
        return

    since = load_last_collect_ts(guild.id)
    run_ts = datetime.now(timezone.utc)
    video_history = prune_video_history(load_video_history(guild.id))
    entries = []

    async for msg in submit_channel.history(after=since, limit=None):
        if msg.author.bot:
            continue
        if not message_pings_role(msg, picker_role):
            continue

        for video_source, video_author in await extract_video_sources(msg):
            if is_video_recently_used(video_source, video_history):
                continue
            entries.append(
                {"author_id": video_author.id, "author_name": video_author.display_name, "video_url": video_source}
            )
            resolved_names[str(video_author.id)] = video_author.display_name

    if not entries:
        print(f"No valid edits found in {guild.name} today.")
        save_last_collect_ts(guild.id, run_ts)
        return

    for entry in entries:
        downloaded_path = None
        if is_social_video_link(entry["video_url"]):
            downloaded_path = await download_social_video(entry["video_url"], guild)

        if downloaded_path:
            try:
                await discussion_channel.send(
                    content=f"**Edit by {entry['author_name']}**",
                    file=discord.File(downloaded_path, filename="edit.mp4"),
                )
            finally:
                os.remove(downloaded_path)
        else:
            # Direct attachments/CDN links, or a download that failed/was too big, post as-is.
            await discussion_channel.send(content=f"**Edit by {entry['author_name']}**\n{entry['video_url']}")

        mark_video_used(entry["video_url"], video_history)

    # Discord's native Poll object hard-caps every poll at 10 answers — that's enforced by
    # Discord itself, not something we can configure away. To support an unlimited number of
    # edits per day, we split entries into batches of MAX_POLL_ANSWERS and open one poll per
    # batch; all of them run simultaneously and their votes are combined when results are
    # tallied. With 10 or fewer entries this is exactly one poll, same as before.
    batches = [entries[i:i + MAX_POLL_ANSWERS] for i in range(0, len(entries), MAX_POLL_ANSWERS)]
    polls_meta = []
    base_question = config.get("custom_poll_question") or "Vote for today's top edit!"
    poll_duration_hours = config.get("poll_duration_hours", POLL_DURATION_HOURS)
    for batch_index, batch in enumerate(batches):
        question = base_question if len(batches) == 1 else f"{base_question} (part {batch_index + 1}/{len(batches)})"
        poll = discord.Poll(question=question, duration=timedelta(hours=poll_duration_hours))
        for entry in batch:
            poll.add_answer(text=f"Vote for {entry['author_name']}"[:55])

        ping = f"{picker_role.mention} 📊 {base_question}" if batch_index == 0 else (
            f"📊 Vote continues — part {batch_index + 1}/{len(batches)}"
        )
        sent = await discussion_channel.send(content=ping, poll=poll)
        polls_meta.append({
            "message_id": sent.id,
            "channel_id": discussion_channel.id,
            "offset": batch_index * MAX_POLL_ANSWERS,
        })

    poll_state["polls"] = polls_meta
    poll_state["entries"] = entries

    save_video_history(guild.id, video_history)
    save_last_collect_ts(guild.id, run_ts)
    print(f"Collect job done for {guild.name}: {len(entries)} edit(s) in today's poll.")


async def resolve_tiebreak(tied_indices, results_channel):
    remaining = list(tied_indices)
    while len(remaining) > 1:
        assignment = {i: random.choice(["heads", "tails"]) for i in remaining}
        heads = [i for i, side in assignment.items() if side == "heads"]
        tails = [i for i, side in assignment.items() if side == "tails"]
        if not heads or not tails:
            continue
        advancing_side = random.choice(["heads", "tails"])
        remaining = heads if advancing_side == "heads" else tails
    return remaining[0]


async def run_results_job():
    """Runs independently for every server — used by the manual 'Run Results Now' button,
    which intentionally fires for every server at once."""
    for guild in bot.guilds:
        await run_results_job_for_guild(guild)


async def run_results_job_for_guild(guild: discord.Guild):
    """Resolve exactly one server's poll(s) and announce its own winner. One server's
    result can never leak into another's.

    Because a day's vote can now span several poll messages (Discord caps a single native poll
    at 10 answers), we fetch every poll message, line up each answer's vote count with its
    global position in poll_state["entries"] via that poll's stored offset, and pick the overall
    winner across all of them combined."""
    poll_state = get_poll_state(guild.id)
    polls_meta = poll_state.get("polls") or []
    if not polls_meta:
        print(f"No active poll to resolve today in {guild.name}.")
        return

    config = load_guild_config(guild.id)
    entries = poll_state["entries"]
    votes = [0] * len(entries)
    last_channel = None
    any_found = False

    for poll_meta in polls_meta:
        channel = bot.get_channel(poll_meta["channel_id"])
        if not channel:
            continue
        last_channel = channel
        try:
            msg = await channel.fetch_message(poll_meta["message_id"])
        except discord.NotFound:
            print(f"Poll message not found in {guild.name}.")
            continue
        if not msg.poll or not msg.poll.answers:
            continue
        any_found = True
        offset = poll_meta.get("offset", 0)
        for i, answer in enumerate(msg.poll.answers):
            global_index = offset + i
            if global_index < len(votes):
                votes[global_index] = answer.vote_count

    if not any_found or not votes:
        return

    max_votes = max(votes)
    tied_indices = [i for i, v in enumerate(votes) if v == max_votes]

    used_tiebreak = len(tied_indices) > 1
    if used_tiebreak:
        winner_index = await resolve_tiebreak(tied_indices, last_channel)
    else:
        winner_index = tied_indices[0]

    if winner_index >= len(entries):
        return

    best_entry = entries[winner_index]
    best_votes = max_votes
    day_number = load_day(guild.id)

    results_channel = find_channel(guild, config["results_channel_id"], RESULTS_CHANNEL_NAME)
    discussion_channel = find_channel(guild, config["discussion_channel_id"], DISCUSSION_CHANNEL_NAME)
    top_edits_role = find_role(guild, config["top_edits_role_id"], TOP_EDITS_ROLE_NAME)

    if results_channel:
        winner_points = config.get("winner_points", WINNER_POINTS)
        new_total = await award_points(guild, best_entry["author_id"], winner_points)

        ping = top_edits_role.mention if top_edits_role else ""
        member_mention = f"<@{best_entry['author_id']}>"
        win_line = random.choice(config["custom_winner_messages"] or TOP_EDIT_WIN_MESSAGES).format(
            member=member_mention
        )
        vote_word = "vote" if best_votes == 1 else "votes"

        embed = discord.Embed(
            title=f"🏆 TOP EDIT OF THE DAY — DAY {day_number}",
            description=(
                f"{win_line}\n\n"
                f"✨ **{member_mention}** just claimed the crown — the community has spoken, "
                f"and this edit stood out above the rest.\n"
                f"━━━━━━━━━━━━━━━━━━━\n"
                f"🔥 A well-earned win. Keep that momentum going — tomorrow's throne is up for grabs again!"
            ),
            color=discord.Color.gold(),
        )
        embed.add_field(name="🗳️ Votes", value=f"**{best_votes}** {vote_word}", inline=True)
        embed.add_field(name="💰 Points earned", value=f"**+{winner_points}** (total: **{new_total}**)", inline=True)

        downloaded_path = None
        if is_social_video_link(best_entry["video_url"]):
            downloaded_path = await download_social_video(best_entry["video_url"], guild)

        if downloaded_path:
            embed.set_footer(text="🎬 The winning edit is attached below")
            try:
                await results_channel.send(
                    content=ping,
                    embed=embed,
                    file=discord.File(downloaded_path, filename="winning_edit.mp4"),
                )
            finally:
                os.remove(downloaded_path)
        else:
            embed.set_footer(text="🎬 The winning edit is linked below")
            # Embed goes out FIRST, then the raw link in its OWN follow-up message — so the
            # video appears below the announcement embed, not above it. It still has to be
            # its own message (not combined with the embed) or Discord suppresses the link's
            # own preview/player and the video never unfurls at all.
            await results_channel.send(content=ping if ping else None, embed=embed)
            await results_channel.send(content=best_entry["video_url"])

        if used_tiebreak and discussion_channel:
            flavor = random.choice(COIN_FLIP_WIN_MESSAGES).format(member=f"<@{best_entry['author_id']}>")
            await discussion_channel.send(
                content=f"🪙 *Today's winner was decided by a coin-flip tiebreaker!* {flavor}"
            )

        print(f"Winner announced in {guild.name}: {best_entry['author_name']} with {best_votes} votes (day {day_number}).")

    save_day(guild.id, day_number + 1)
    poll_state["entries"] = []
    poll_state["polls"] = []


# ============================================================
# Shared embed builders
# ============================================================

HELP_CATEGORIES = {
    "points": {
        "label": "🏅 Points & Ranks",
        "description": (
            "**`points [@user]`**\n"
            "Check points and progress to the next rank. Has a *Press for more info* button "
            "that reveals your exact leaderboard standing.\n\n"
            "**`ranks`**\n"
            "See every rank, its point threshold, and how to earn points.\n\n"
            "**`leaderboard`**\n"
            "Top 20 rankings — shows 1-10 first, swipe for 11-20."
        ),
    },
    "voting": {
        "label": "🎬 Top Edit Voting",
        "description": (
            "**`timeleft`**\n"
            "Time left until voting starts or ends.\n\n"
            "**`previewvotes`**\n"
            "Live preview of edits already queued for the next vote. *Only visible to you.*\n\n"
            "**`tournamentpoll <role> [question] [duration_hours]`** *(Manage Roles/Admin)*\n"
            "Starts a poll where everyone who votes gets the chosen role automatically — great "
            "for tournament sign-ups. The role stays until you take it back — it's **not** removed "
            "on its own.\n\n"
            "**`tournamentpollend [role]`** *(Manage Roles/Admin)*\n"
            "Removes the tournament role from everyone who has it, whenever you're ready. "
            "Leave `role` empty to target the most recently started poll.\n\n"
            "**`removerolefrom <role> <users>`** *(Manage Roles/Admin)*\n"
            "Removes a role from several specific people at once — @mention them or paste their "
            "IDs, space-separated."
        ),
    },
    "editing": {
        "label": "🎨 Editing Tools",
        "description": (
            "**`rate-edit [video_url]`**\n"
            "Honest AI feedback on an edit — score, software guess, and tips. Use with a link, "
            "or right-click a message with a video → Apps → **Rate this Edit**.\n\n"
            "**`find-asset <query>`**\n"
            "Searches the web for an overlay/asset based on your description.\n\n"
            "**`youtube-tiktok-caption [media_url]`**\n"
            "AI-generated eye-catching title, hashtags, and a long description for your edit — "
            "use with a link, or right-click a message with a video/image → Apps → **Make YT/TikTok Caption**. "
            "Didn't quite fit? Hit 🔄 Regenerate on the result.\n\n"
            "**`airating`** *(text-command, also `.airating`)*\n"
            "Same as `rate-edit`, but works as a chat command — reply to a video, attach one, "
            "or give a link. Supports YouTube, TikTok, Streamable, and most other video links.\n\n"
            "**`aicaption [platform] [topic]`** *(text-command, also `.aicaption`)*\n"
            "Attach/reply with a video or image (TikTok photo-posts included) to caption THAT, "
            "or type `.aicaption tiktok my new setup` for a text-only topic. No arguments? "
            "It asks you step by step for platform and topic.\n\n"
            "**`askai <question>`** *(text-command, also `.askai`/`.ai`)*\n"
            "A general AI assistant, like Gemini or ChatGPT — ask it anything. Attach or reply "
            "to a screenshot/video and it'll actually look at it too (an editing-software error, "
            "a settings screen, whatever)."
        ),
    },
    "staff": {
        "label": "🛠️ Staff Tools",
        "description": (
            "*Top Edit Picker Manager / Staff only — replies are only visible to you.*\n\n"
            "**`testcollect`**\n"
            "Manually run the collect job.\n\n"
            "**`testresults`**\n"
            "Manually run the results job.\n\n"
            "**`addpoints @user <amount>`**\n"
            "Add points to a user.\n\n"
            "**`removepoints @user <amount>`**\n"
            "Remove points from a user.\n\n"
            "**`purgeword #channel word`**\n"
            "Delete every message containing that word.\n\n"
            "**`badwords add/remove/list <word>`**\n"
            "Manage the risk-word list.\n\n"
            "**`purgebadwords #channel|all`**\n"
            "Purge every risk-word match, in one channel or across all of them.\n\n"
            "**`create-embed`**\n"
            "Build a custom embed (title, description, bullet points, color, image, footer) "
            "and post it to any channel — no code needed. Same builder is also available on the "
            "website dashboard's Control Room.\n\n"
            "*Server channels/roles are configured on the website dashboard's Settings page "
            "(Administrator only) — there's no in-Discord setup command anymore.*"
        ),
    },
    "utility": {
        "label": "⚙️ Utility",
        "description": (
            "**`ping`**\n"
            "Detailed latency and status check.\n\n"
            "**`dashboard`**\n"
            "Live bot stats.\n\n"
            "**`tutorial`**\n"
            "Full walkthrough of how the Top Edit system works.\n\n"
            "**`flip`**\n"
            "Flip a coin."
        ),
    },
}


def build_help_home_embed():
    embed = discord.Embed(
        title="Zexo — Command Overview",
        description=(
            "Every command works as `!command`, `.command`, and `/command`.\n"
            "New here? Run **`/tutorial`** for a full walkthrough of how the whole system works.\n\n"
            "🌐 Full web dashboard: **https://fourk-discord-bot-6.onrender.com**\n\n"
            "**Pick a category below** 👇"
        ),
        color=discord.Color.blurple(),
    )
    for cat in HELP_CATEGORIES.values():
        preview = cat["description"].split("\n\n")[0].split("\n")[0]
        embed.add_field(name=cat["label"], value=f"{preview} ...", inline=False)
    embed.set_footer(text="Tap a button to open that category.")
    return embed


def build_help_category_embed(key: str):
    cat = HELP_CATEGORIES[key]
    embed = discord.Embed(title=cat["label"], description=cat["description"], color=discord.Color.blurple())
    embed.set_footer(text="Press 🏠 Home to see all categories again.")
    return embed


class HelpView(discord.ui.View):
    """Category-sorted /help — press a button to jump between sections."""

    def __init__(self):
        super().__init__(timeout=180)
        self.message = None

    @discord.ui.button(label="🏅 Points & Ranks", style=discord.ButtonStyle.secondary, row=0)
    async def points_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(embed=build_help_category_embed("points"), view=self)

    @discord.ui.button(label="🎬 Top Edit Voting", style=discord.ButtonStyle.secondary, row=0)
    async def voting_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(embed=build_help_category_embed("voting"), view=self)

    @discord.ui.button(label="🎨 Editing Tools", style=discord.ButtonStyle.secondary, row=0)
    async def editing_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(embed=build_help_category_embed("editing"), view=self)

    @discord.ui.button(label="🛠️ Staff Tools", style=discord.ButtonStyle.secondary, row=0)
    async def staff_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(embed=build_help_category_embed("staff"), view=self)

    @discord.ui.button(label="⚙️ Utility", style=discord.ButtonStyle.secondary, row=0)
    async def utility_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(embed=build_help_category_embed("utility"), view=self)

    @discord.ui.button(label="🏠 Home", style=discord.ButtonStyle.primary, row=1)
    async def home_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(embed=build_help_home_embed(), view=self)

    async def on_timeout(self):
        if self.message:
            for child in self.children:
                child.disabled = True
            try:
                await self.message.edit(view=self)
            except discord.HTTPException:
                pass


def build_tutorial_embed(guild: discord.Guild):
    config = load_guild_config(guild.id)
    embed = discord.Embed(
        title="📖 How the Top Edit System Works",
        description="A full walkthrough — from posting your edit to earning points.",
        color=discord.Color.blurple(),
    )
    embed.add_field(
        name="1️⃣ Submit your edit",
        value=(
            f"Post your edit video in <#{config['submit_channel_id']}> and **@mention the {PICKER_ROLE_NAME} role** "
            "in the same message. Forwarded videos count too — you don't have to re-upload."
        ),
        inline=False,
    )
    collect_time_str = f"{config['collect_hour']:02d}:{config.get('collect_minute', 0):02d}"
    results_time_str = f"{config['results_hour']:02d}:{config.get('results_minute', 0):02d}"
    embed.add_field(
        name="2️⃣ Daily collection",
        value=(
            f"Every day at **{collect_time_str} (Europe/Berlin)**, the bot scans that channel for new "
            f"submissions and collects **all** of them — no cap. If there are more than {MAX_POLL_ANSWERS} "
            "(Discord's limit per poll), several polls run at once to cover them all. Once a video has been "
            "used in a vote, it can **never** be picked again — no matter how long ago that was."
        ),
        inline=False,
    )
    embed.add_field(
        name="3️⃣ Voting",
        value=(
            f"The bot posts every collected edit in <#{config['discussion_channel_id']}> and opens a poll, pinging "
            f"**@{PICKER_ROLE_NAME}**. Voting stays open for **{config.get('poll_duration_hours', POLL_DURATION_HOURS)} hours**, closing at "
            f"**{results_time_str}**. Use `/previewvotes` any time to privately see what's currently in the vote."
        ),
        inline=False,
    )
    embed.add_field(
        name="4️⃣ Winner & points",
        value=(
            f"When voting ends, the bot tallies the poll and announces the winner in <#{config['results_channel_id']}>. "
            f"The winner earns **+{config.get('winner_points', WINNER_POINTS)} point(s)**. Ties are broken with a coin-flip bracket."
        ),
        inline=False,
    )
    tier_lines = "\n".join(f"{emoji} **{label}** — from **{threshold}** points" for threshold, _rid, label, emoji in RANK_TIERS)
    embed.add_field(
        name="5️⃣ Ranks",
        value=f"Points add up over time and unlock ranks:\n{tier_lines}\n\nUse `/ranks` for the full breakdown.",
        inline=False,
    )
    embed.add_field(
        name="📊 Track your progress",
        value=(
            "`/points` — your points, rank progress, and a *Press for more info* button showing your exact "
            "leaderboard standing\n"
            "`/leaderboard` — top 20 rankings\n"
            "`/timeleft` — countdown to the next voting phase\n"
            "`/previewvotes` — private peek at today's vote"
        ),
        inline=False,
    )
    embed.set_footer(text="Run /help for the full command list. Server admins: configure channels & roles on the website dashboard's Settings page.")
    return embed


async def resolve_display_name(guild: discord.Guild, uid: str) -> str:
    if uid in resolved_names:
        return resolved_names[uid]
    member = guild.get_member(int(uid))
    if not member:
        try:
            member = await guild.fetch_member(int(uid))
        except (discord.NotFound, discord.HTTPException):
            member = None
    if member:
        resolved_names[uid] = member.display_name
        return member.display_name
    return f"Unknown user ({uid})"


async def build_leaderboard_embed(guild: discord.Guild, page: int = 1):
    data = load_points(guild.id)
    embed = discord.Embed(
        title="🏆 Zexo Leaderboard",
        color=discord.Color.gold(),
    )
    if not data:
        embed.description = "No points recorded yet. Win a Top Edit to get on the board!"
        return embed

    sorted_entries = sorted(data.items(), key=lambda x: x[1], reverse=True)
    total_editors = len(sorted_entries)
    start = (page - 1) * LEADERBOARD_PAGE_SIZE
    page_entries = sorted_entries[start:start + LEADERBOARD_PAGE_SIZE]

    if not page_entries:
        embed.description = "No editors on this page."
        embed.set_footer(text=f"Day {load_day(guild.id)} · {total_editors} editor(s) total")
        return embed

    medals = ["🥇", "🥈", "🥉"]
    lines = []
    for i, (uid, score) in enumerate(page_entries, start=start):
        name = await resolve_display_name(guild, uid)
        position = medals[i] if i < 3 else f"**#{i + 1}**"
        rank_emoji = current_rank_emoji(score)
        rank_label = current_rank_label(score) or UNRANKED_LABEL
        role_obj = guild.get_role(current_rank_role_id(score))
        role_display = role_obj.mention if role_obj else f"*{rank_label}*"
        lines.append(f"{position} **{name}** — `{score}` pts {rank_emoji} {role_display}")

    intro = "Top editors of this server, ranked by total points." if page == 1 else f"Ranks {start + 1}–{start + len(page_entries)}."
    description = intro + "\n\n" + "\n".join(lines)
    if page == 1:
        description += f"\n\n_{random.choice(LEADERBOARD_FLAVOR)}_"
    embed.description = description
    total_pages = min(LEADERBOARD_MAX_PAGES, max(1, (total_editors + LEADERBOARD_PAGE_SIZE - 1) // LEADERBOARD_PAGE_SIZE))
    embed.set_footer(text=f"Day {load_day(guild.id)} · Page {page}/{total_pages} · {total_editors} editor(s) total")
    return embed


class LeaderboardView(discord.ui.View):
    """Top 10 as the classic film-strip image, with a swipe button to see 11-20. Nothing beyond that."""

    def __init__(self, guild: discord.Guild):
        super().__init__(timeout=180)
        self.guild = guild
        self.page = 1
        self.message = None
        self._sync_buttons()

    def _sync_buttons(self):
        self.prev_button.disabled = self.page <= 1
        self.next_button.disabled = self.page >= LEADERBOARD_MAX_PAGES

    async def _render(self, interaction: discord.Interaction):
        file = await generate_leaderboard_image(self.guild, page=self.page)
        if file:
            await interaction.response.edit_message(attachments=[file], embed=None, view=self)
        else:
            await interaction.response.edit_message(embed=await build_leaderboard_embed(self.guild, self.page), attachments=[], view=self)

    @discord.ui.button(label="◀ 1-10", style=discord.ButtonStyle.secondary, disabled=True)
    async def prev_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page = 1
        self._sync_buttons()
        await self._render(interaction)

    @discord.ui.button(label="11-20 ▶", style=discord.ButtonStyle.secondary)
    async def next_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page = 2
        self._sync_buttons()
        await self._render(interaction)

    async def on_timeout(self):
        if self.message:
            for child in self.children:
                child.disabled = True
            try:
                await self.message.edit(view=self)
            except discord.HTTPException:
                pass


# --- Image-based leaderboard (film-strip / editing themed) ---
_FONT_CACHE = {}


def get_font(size: int, bold: bool = False) -> ImageFont.FreeTypeFont:
    key = (size, bold)
    if key in _FONT_CACHE:
        return _FONT_CACHE[key]
    candidates = [
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf" if bold else "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
        "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf" if bold else "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
        "/usr/share/fonts/truetype/noto/NotoSans-Bold.ttf" if bold else "/usr/share/fonts/truetype/noto/NotoSans-Regular.ttf",
    ]
    font = None
    for path in candidates:
        if os.path.exists(path):
            try:
                font = ImageFont.truetype(path, size)
                break
            except OSError:
                continue
    if font is None:
        font = ImageFont.load_default()
    _FONT_CACHE[key] = font
    return font


async def generate_leaderboard_image(guild: discord.Guild, page: int = 1):
    """Renders the leaderboard as a film-strip themed PNG (avatars, tier colors, progress bars).
    page=1 -> ranks 1-10, page=2 -> ranks 11-20."""
    data = load_points(guild.id)
    if not data:
        return None

    sorted_all = sorted(data.items(), key=lambda x: x[1], reverse=True)
    start = (page - 1) * LEADERBOARD_PAGE_SIZE
    sorted_entries = sorted_all[start:start + LEADERBOARD_PAGE_SIZE]
    if not sorted_entries:
        return None

    row_h = 96
    header_h = 130
    footer_h = 70
    width = 1000
    height = header_h + row_h * len(sorted_entries) + footer_h

    img = Image.new("RGB", (width, height), (10, 10, 16))
    draw = ImageDraw.Draw(img)

    # Vertical gradient background
    top_color = (28, 18, 48)
    bottom_color = (10, 10, 16)
    for y in range(height):
        t = y / height
        r = int(top_color[0] + (bottom_color[0] - top_color[0]) * t)
        g = int(top_color[1] + (bottom_color[1] - top_color[1]) * t)
        b = int(top_color[2] + (bottom_color[2] - top_color[2]) * t)
        draw.line([(0, y), (width, y)], fill=(r, g, b))

    # Film-strip perforation holes along top & bottom edges
    hole_w, hole_h, gap = 26, 18, 20
    for strip_y in (10, height - 10 - hole_h):
        x = 20
        while x < width - 20:
            draw.rounded_rectangle([x, strip_y, x + hole_w, strip_y + hole_h], radius=4, fill=(0, 0, 0), outline=(60, 60, 75))
            x += hole_w + gap

    title_font = get_font(44, bold=True)
    sub_font = get_font(20)
    name_font = get_font(28, bold=True)
    small_font = get_font(20)
    badge_font = get_font(22, bold=True)

    draw.text((width / 2, 46), "EDITOR LEADERBOARD", font=title_font, fill=(255, 255, 255), anchor="mm")
    draw.text((width / 2, 86), f"Day {load_day(guild.id)} · Ranks {start + 1}-{start + len(sorted_entries)} of {len(sorted_all)}", font=sub_font, fill=(175, 170, 195), anchor="mm")

    medal_colors = {0: (255, 215, 0), 1: (205, 205, 215), 2: (205, 127, 50)}
    y = header_h

    for i, (uid, score) in enumerate(sorted_entries, start=start):
        member = guild.get_member(int(uid))
        if not member:
            try:
                member = await guild.fetch_member(int(uid))
            except (discord.NotFound, discord.HTTPException):
                member = None
        name = member.display_name if member else resolved_names.get(uid, f"User {uid}")
        if member:
            resolved_names[uid] = member.display_name

        tier_label = current_rank_label(score) or UNRANKED_LABEL
        color = TIER_COLORS.get(tier_label, (150, 150, 165))

        row_top = y
        row_bottom = y + row_h - 12
        draw.rounded_rectangle([30, row_top, width - 30, row_bottom], radius=18, fill=(22, 19, 32))
        draw.rounded_rectangle([30, row_top, 42, row_bottom], radius=8, fill=color)

        # Avatar
        avatar_size = 64
        avatar_x, avatar_y = 62, row_top + (row_h - 12 - avatar_size) // 2
        avatar_img = None
        if member:
            try:
                avatar_bytes = await member.display_avatar.replace(size=128).read()
                avatar_img = Image.open(BytesIO(avatar_bytes)).convert("RGBA").resize((avatar_size, avatar_size))
            except (discord.HTTPException, OSError):
                avatar_img = None
        if avatar_img is None:
            avatar_img = Image.new("RGBA", (avatar_size, avatar_size), color + (255,))
        mask = Image.new("L", (avatar_size, avatar_size), 0)
        ImageDraw.Draw(mask).ellipse((0, 0, avatar_size, avatar_size), fill=255)
        img.paste(avatar_img, (avatar_x, avatar_y), mask)
        draw.ellipse([avatar_x - 3, avatar_y - 3, avatar_x + avatar_size + 3, avatar_y + avatar_size + 3], outline=color, width=3)

        # Rank medal badge
        badge_r = 20
        badge_cx, badge_cy = avatar_x - 4, avatar_y - 4
        badge_fill = medal_colors.get(i, (42, 40, 56))
        draw.ellipse([badge_cx - badge_r, badge_cy - badge_r, badge_cx + badge_r, badge_cy + badge_r], fill=badge_fill, outline=(255, 255, 255))
        draw.text((badge_cx, badge_cy), str(i + 1), font=badge_font, fill=(10, 10, 16) if i < 3 else (255, 255, 255), anchor="mm")

        # Name, points, tier
        text_x = avatar_x + avatar_size + 26
        draw.text((text_x, row_top + 14), name, font=name_font, fill=(255, 255, 255))
        draw.text((text_x, row_top + 50), f"{score} pts · {tier_label}", font=small_font, fill=color)

        # Progress bar toward next tier
        next_label, _needed, low, high = next_rank_progress(score)
        bar_x0, bar_x1 = text_x, width - 60
        bar_y = row_top + 78
        bar_w = bar_x1 - bar_x0
        draw.rounded_rectangle([bar_x0, bar_y, bar_x1, bar_y + 10], radius=5, fill=(45, 42, 60))
        frac = ((score - low) / max(1, (high - low))) if next_label else 1.0
        fill_w = int(bar_w * min(1, max(0, frac)))
        if fill_w > 4:
            draw.rounded_rectangle([bar_x0, bar_y, bar_x0 + fill_w, bar_y + 10], radius=5, fill=color)

        y += row_h

    draw.text((width / 2, height - footer_h / 2), random.choice(LEADERBOARD_FLAVOR), font=sub_font, fill=(175, 170, 195), anchor="mm")

    buf = BytesIO()
    img.save(buf, format="PNG")
    buf.seek(0)
    return discord.File(buf, filename="leaderboard.png")


async def build_points_message(guild: discord.Guild, member: discord.Member) -> str:
    data = load_points(guild.id)
    total = data.get(str(member.id), 0)
    resolved_names[str(member.id)] = member.display_name
    rank_label = current_rank_label(total)
    rank_emoji = current_rank_emoji(total)
    next_label, needed, low, high = next_rank_progress(total)
    flavor = random.choice(POINTS_CHECK_FLAVOR)

    rank_text = f"Current rank: {rank_emoji} **{rank_label}**" if rank_label else f"Current rank: {UNRANKED_EMOJI} *{UNRANKED_LABEL}*"
    if next_label:
        bar = progress_bar(total - low, high - low)
        progress_text = f"{bar}  **{needed}** more point(s) to reach **{next_label}**."
    else:
        progress_text = "You're at the highest rank! 🎉👑"

    # --- Where you stand on the leaderboard ---
    sorted_entries = sorted(data.items(), key=lambda x: x[1], reverse=True)
    position = None
    for i, (uid, _score) in enumerate(sorted_entries):
        if uid == str(member.id):
            position = i + 1
            break

    if position is None:
        standing_text = "📊 Not on the leaderboard yet — earn points to appear."
    elif position == 1:
        standing_text = f"📊 Rank **#1** of **{len(sorted_entries)}** editors. 👑 You're in first place!"
    else:
        above_uid, above_score = sorted_entries[position - 2]
        above_name = await resolve_display_name(guild, above_uid)
        above_rank_emoji = current_rank_emoji(above_score)
        above_rank_label = current_rank_label(above_score) or UNRANKED_LABEL
        gap = above_score - total
        standing_text = (
            f"📊 Rank **#{position}** of **{len(sorted_entries)}** editors.\n"
            f"⬆️ Above you: **{above_name}** — `{above_score}` pts {above_rank_emoji} *{above_rank_label}* "
            f"(**{gap}** point(s) to catch up)"
        )

    return f"🏅 {member.mention} has **{total}** point(s).\n{rank_text}\n{progress_text}\n{standing_text}\n*{flavor}*"


async def build_points_standing_embed(guild: discord.Guild, member: discord.Member) -> discord.Embed:
    data = load_points(guild.id)
    total = data.get(str(member.id), 0)
    sorted_entries = sorted(data.items(), key=lambda x: x[1], reverse=True)
    total_editors = len(sorted_entries)

    position = None
    for i, (uid, _score) in enumerate(sorted_entries):
        if uid == str(member.id):
            position = i + 1
            break

    embed = discord.Embed(title=f"📊 {member.display_name}'s Leaderboard Standing", color=discord.Color.blurple())

    if position is None:
        embed.description = "Not on the leaderboard yet — earn points to appear."
        embed.set_footer(text="Only visible to you")
        return embed

    embed.description = f"Rank **#{position}** of **{total_editors}** editors on this server."

    if position == 1:
        embed.add_field(name="👑 Above you", value="Nobody — you're in first place!", inline=False)
    else:
        start = max(0, position - 1 - 5)
        above_entries = sorted_entries[start:position - 1]
        lines = []
        for i, (uid, score) in enumerate(above_entries, start=start):
            name = await resolve_display_name(guild, uid)
            rank_emoji = current_rank_emoji(score)
            rank_label = current_rank_label(score) or UNRANKED_LABEL
            lines.append(f"**#{i + 1}** {name} — `{score}` pts {rank_emoji} *{rank_label}*")
        embed.add_field(name="⬆️ Closest above you", value="\n".join(lines) or "—", inline=False)

    own_rank_label = current_rank_label(total) or UNRANKED_LABEL
    own_rank_emoji = current_rank_emoji(total)
    embed.add_field(name="You", value=f"**#{position}** {member.display_name} — `{total}` pts {own_rank_emoji} *{own_rank_label}*", inline=False)
    embed.set_footer(text="Only visible to you")
    return embed


class PointsInfoView(discord.ui.View):
    """Adds a 'press for more info' button under a /points reply, revealing the full leaderboard
    standing (rank + closest 5 above) — visible only to whoever ran the command."""

    def __init__(self, guild: discord.Guild, member: discord.Member, author_id: int):
        super().__init__(timeout=180)
        self.guild = guild
        self.member = member
        self.author_id = author_id

    @discord.ui.button(label="📊 Press for more info", style=discord.ButtonStyle.primary)
    async def more_info(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("❌ Only the person who ran this command can view this.", ephemeral=True)
            return
        embed = await build_points_standing_embed(self.guild, self.member)
        await interaction.response.send_message(embed=embed, ephemeral=True)


def build_ranks_embed():
    embed = discord.Embed(
        title="🏅 Editor Rankings",
        description=(
            "Earn points by winning **Top Edit of the Day** (+1 point automatically) "
            "or through tournaments (awarded manually by a Top Edit Manager/Staff).\n\u200b"
        ),
        color=discord.Color.blurple(),
    )
    embed.add_field(
        name=f"{UNRANKED_EMOJI} Unranked",
        value="0 – 9 points\n*Everyone starts here.*",
        inline=True,
    )
    for idx, (threshold, _role_id, label, emoji) in enumerate(RANK_TIERS):
        next_index = idx + 1
        upper = f"{RANK_TIERS[next_index][0] - 1}" if next_index < len(RANK_TIERS) else "∞"
        embed.add_field(
            name=f"{emoji} Editor {label}",
            value=f"{threshold} – {upper} points",
            inline=True,
        )
    embed.set_footer(text="Ranks update automatically as your points change.")
    return embed


def build_timeleft_message(guild_id: int = None):
    config = load_guild_config(guild_id) if guild_id else default_guild_config()
    now = datetime.now(EU_TZ)
    collect_dt = now.replace(hour=config.get("collect_hour", COLLECT_HOUR), minute=config.get("collect_minute", 0), second=0, microsecond=0)
    results_dt = now.replace(hour=config.get("results_hour", RESULTS_HOUR), minute=config.get("results_minute", 0), second=0, microsecond=0)

    if now < collect_dt:
        diff = collect_dt - now
        return f"🕒 Voting hasn't started yet. Starts in **{format_timedelta(diff)}**."
    elif collect_dt <= now < results_dt:
        diff = results_dt - now
        return f"🗳️ Voting is **live**! Ends in **{format_timedelta(diff)}**."
    else:
        next_collect = collect_dt + timedelta(days=1)
        diff = next_collect - now
        return f"✅ Voting has ended for today. Next round starts in **{format_timedelta(diff)}**."


def build_ping_embed(latency_ms: float):
    uptime = datetime.now(timezone.utc) - START_TIME
    embed = discord.Embed(title="🏓 Pong!", color=discord.Color.green())
    embed.add_field(name="Latency", value=f"{latency_ms}ms", inline=True)
    embed.add_field(name="Uptime", value=format_timedelta(uptime), inline=True)
    embed.add_field(name="Servers", value=str(len(bot.guilds)), inline=True)
    embed.add_field(name="discord.py", value=discord.__version__, inline=True)
    return embed


def build_dashboard_embed():
    uptime = datetime.now(timezone.utc) - START_TIME
    members_reachable = sum(g.member_count or 0 for g in bot.guilds)

    embed = discord.Embed(title="📊 Bot Dashboard", color=discord.Color.blurple())
    embed.add_field(name="Status", value="🟢 Online", inline=False)
    embed.add_field(name="Uptime", value=format_timedelta(uptime), inline=True)
    embed.add_field(name="Latency", value=f"{round(bot.latency * 1000)}ms", inline=True)
    embed.add_field(name="Servers", value=str(len(bot.guilds)), inline=True)
    embed.add_field(name="Members reachable", value=str(members_reachable), inline=True)

    if command_usage:
        usage_lines = "\n".join(f"`{name}` — {count}" for name, count in sorted(command_usage.items(), key=lambda x: -x[1])[:10])
    else:
        usage_lines = "No commands used yet."
    embed.add_field(name="Command usage (since last restart)", value=usage_lines, inline=False)
    embed.add_field(name="🌐 Full web dashboard", value="https://fourk-discord-bot-6.onrender.com", inline=False)
    embed.set_footer(text=f"discord.py {discord.__version__}")
    return embed


# ============================================================
# Prefix commands (!)
# ============================================================

@bot.command()
async def ping(ctx):
    await ctx.send(embed=build_ping_embed(round(bot.latency * 1000)))


@bot.command()
async def dashboard(ctx):
    await ctx.send(embed=build_dashboard_embed())


@bot.command()
async def help(ctx):
    view = HelpView()
    view.message = await ctx.send(embed=build_help_home_embed(), view=view)


@bot.command()
async def tutorial(ctx):
    await ctx.send(embed=build_tutorial_embed(ctx.guild))


@bot.command()
async def flip(ctx):
    result = random.choice(["Heads", "Tails"])
    await ctx.send(f"🪙 The coin landed on **{result}**!")


@bot.command()
async def timeleft(ctx):
    await ctx.send(build_timeleft_message(ctx.guild.id if ctx.guild else None))


@bot.command()
async def ranks(ctx):
    await ctx.send(embed=build_ranks_embed())


@bot.command()
async def testcollect(ctx):
    if not has_picker_permission(ctx.author):
        await ctx.send("❌ Only Top Edit Picker/Manager/Staff can use this.")
        return
    await ctx.send("⏳ Running collect job manually...")
    await run_collect_job()
    entries = get_poll_state(ctx.guild.id)["entries"]
    await ctx.send(f"✅ Done. {len(entries)} edit(s) posted for voting.")


@bot.command()
async def testresults(ctx):
    if not has_picker_permission(ctx.author):
        await ctx.send("❌ Only Top Edit Picker/Manager/Staff can use this.")
        return
    await ctx.send("⏳ Running results job manually...")
    await run_results_job()
    await ctx.send("✅ Done.")


@bot.command()
async def addpoints(ctx, member: discord.Member = None, amount: int = None):
    if not has_points_permission(ctx.author):
        await ctx.send("❌ Only Top Edit Manager or Staff can use this.")
        return
    if member is None or amount is None:
        await ctx.send("Usage: `!addpoints @user <amount>`")
        return
    new_total = await award_points(ctx.guild, member.id, amount)
    logged = await log_points_action(ctx.guild, ctx.author, member.id, amount, new_total, "add")
    warning = "" if logged else f"\n⚠️ *Couldn't post to the points log channel — check it's configured on the website dashboard's Settings page and that the bot can see/send in it.*"
    await ctx.send(f"✅ Added **{amount}** point(s) to {member.mention}. New total: **{new_total}**{warning}")


@bot.command()
async def removepoints(ctx, member: discord.Member = None, amount: int = None):
    if not has_points_permission(ctx.author):
        await ctx.send("❌ Only Top Edit Manager or Staff can use this.")
        return
    if member is None or amount is None:
        await ctx.send("Usage: `!removepoints @user <amount>`")
        return
    new_total = await award_points(ctx.guild, member.id, -amount)
    logged = await log_points_action(ctx.guild, ctx.author, member.id, amount, new_total, "remove")
    warning = "" if logged else f"\n⚠️ *Couldn't post to the points log channel — check it's configured on the website dashboard's Settings page and that the bot can see/send in it.*"
    await ctx.send(f"✅ Removed **{amount}** point(s) from {member.mention}. New total: **{new_total}**{warning}")


@bot.command()
async def points(ctx, member: discord.Member = None):
    member = member or ctx.author
    view = PointsInfoView(ctx.guild, member, ctx.author.id)
    await ctx.send(await build_points_message(ctx.guild, member), view=view)


@bot.command()
async def leaderboard(ctx):
    view = LeaderboardView(ctx.guild)
    file = await generate_leaderboard_image(ctx.guild, page=1)
    if file:
        view.message = await ctx.send(file=file, view=view)
    else:
        view.message = await ctx.send(embed=await build_leaderboard_embed(ctx.guild, page=1), view=view)


@bot.command()
async def previewvotes(ctx):
    entries = await collect_pending_entries(ctx.guild)
    if entries is None:
        await ctx.send("⚠️ Couldn't find the submission channel or Picker role in this server.")
        return
    if not entries:
        try:
            await ctx.author.send("📭 No edits queued for the next vote yet — post one in the submissions channel and ping the Picker role.")
        except discord.Forbidden:
            await ctx.send("📭 No edits queued for the next vote yet. *(couldn't DM you — check your privacy settings)*")
            return
    else:
        lines = [f"**{i}.** {entry['author_name']} — {entry['video_url']}" for i, entry in enumerate(entries, start=1)]
        embed = discord.Embed(
            title="🗳️ Pending Edits Preview",
            description=(
                "These are the edits currently queued to go into the **next voting poll** — "
                "not a ranking, not results, just what's lined up so far:\n\n" + "\n".join(lines)
            ),
            color=discord.Color.blurple(),
        )
        embed.set_footer(text=f"{len(entries)} edit(s) will go into the next vote")
        try:
            await ctx.author.send(embed=embed)
        except discord.Forbidden:
            await ctx.send("❌ Couldn't DM you the preview — check your privacy settings, or use `/previewvotes` instead.")
            return
    try:
        await ctx.message.add_reaction("📬")
    except discord.HTTPException:
        pass


@bot.command()
async def purgeword(ctx, channel: discord.TextChannel = None, *, word: str = None):
    if not has_points_permission(ctx.author):
        await ctx.send("❌ Only Top Edit Manager or Staff can use this.")
        return
    if channel is None or not word:
        await ctx.send("Usage: `!purgeword #channel word`\nDeletes every message in that channel containing the exact word.")
        return
    if not channel.permissions_for(ctx.guild.me).manage_messages:
        await ctx.send(f"❌ I don't have **Manage Messages** permission in {channel.mention}.")
        return

    status = await ctx.send(f"⏳ Scanning {channel.mention} for **{word}**... (0 scanned, 0 deleted)")
    last_edit = datetime.now(timezone.utc)

    async def progress(scanned, deleted, final=False):
        nonlocal last_edit
        now = datetime.now(timezone.utc)
        if not final and (now - last_edit).total_seconds() < 4:
            return
        last_edit = now
        try:
            if final:
                await status.edit(content=f"✅ Done. Scanned **{scanned}** message(s), deleted **{deleted}** containing '{word}' in {channel.mention}.")
            else:
                await status.edit(content=f"⏳ Scanning {channel.mention} for **{word}**... ({scanned} scanned, {deleted} deleted so far)")
        except discord.HTTPException:
            pass

    await purge_messages_with_word(channel, word, progress=progress)


@bot.command(name="badwords")
async def badwords_cmd(ctx, action: str = None, *, word: str = None):
    if not has_points_permission(ctx.author):
        await ctx.send("❌ Only Top Edit Manager or Staff can use this.")
        return
    action = (action or "").lower()
    words = load_badwords(ctx.guild.id)

    if action == "add" and word:
        if word.lower().strip() in [w.lower() for w in words]:
            await ctx.send(f"`{word}` is already on the list.")
            return
        words.append(word.lower().strip())
        save_badwords(ctx.guild.id, words)
        await ctx.send(f"✅ Added `{word}` to the risk-word list. Run `!purgebadwords` to purge with it — nothing is deleted automatically.")
    elif action == "remove" and word:
        new_words = [w for w in words if w.lower() != word.lower().strip()]
        if len(new_words) == len(words):
            await ctx.send(f"`{word}` wasn't on the list.")
            return
        save_badwords(ctx.guild.id, new_words)
        await ctx.send(f"✅ Removed `{word}` from the list.")
    elif action == "list":
        if words:
            await ctx.send(f"⚠️ Risk-word list ({len(words)}): " + ", ".join(f"`{w}`" for w in words))
        else:
            await ctx.send("List is empty. Add one with `!badwords add <word>`.")
    else:
        await ctx.send(
            "Usage:\n"
            "`!badwords add <word>` — add a word/phrase to the risk list (matches suffixes too, e.g. 'pedo' also catches 'pedos')\n"
            "`!badwords remove <word>`\n"
            "`!badwords list`\n"
            "Nothing gets deleted just by adding a word — run `!purgebadwords` to actually purge."
        )


AI_CAPTION_PLATFORM_KEYWORDS = {
    "tiktok": "TikTok", "tt": "TikTok",
    "instagram": "Instagram", "insta": "Instagram", "ig": "Instagram",
    "youtube": "YouTube Shorts", "yt": "YouTube Shorts", "shorts": "YouTube Shorts",
    "twitter": "X (Twitter)", "x": "X (Twitter)",
    "allgemein": "social media", "general": "social media", "andere": "social media",
}


@bot.command(name="airating", aliases=["aiRating"])
async def airating_cmd(ctx, *, video_url: str = None):
    """Text-command version of /rate-edit.
    Usage: `.airating` (reply to / attach a video), or `.airating <link>`."""
    source_message = ctx.message
    if video_url:
        source_message = type("Obj", (), {"attachments": [], "content": video_url, "guild": ctx.guild})()
    elif ctx.message.reference:
        try:
            source_message = await ctx.channel.fetch_message(ctx.message.reference.message_id)
        except discord.HTTPException:
            pass

    async with ctx.typing():
        video_path, link_found = await _get_video_path_from_message(source_message)
        if not video_path:
            await ctx.send(embed=_rating_unavailable_embed())
            return

        frame_paths = []
        try:
            frame_paths = await asyncio.get_running_loop().run_in_executor(None, _extract_frames, video_path, 4)
            if not frame_paths:
                await ctx.send("⚠️ Couldn't extract any frames from that video.")
                return
            feedback = await asyncio.get_running_loop().run_in_executor(
                None, _call_gemini_vision, frame_paths, RATE_EDIT_PROMPT
            )
            embed = discord.Embed(title="🎬 Edit Rating", description=feedback, color=discord.Color.purple())
            embed.set_footer(text="AI-generated feedback from a few sampled frames — take it as a starting point, not gospel.")
            _style_ai_result_embed(embed, ctx.author.display_avatar.url)
            await ctx.send(embed=embed)
        except RuntimeError as e:
            await ctx.send(f"⚠️ {e}")
        except Exception as e:
            print(f"⚠️ .airating failed: {e}")
            await ctx.send("⚠️ Something went wrong with the rating. Try again in a bit.")
        finally:
            if os.path.exists(video_path):
                os.remove(video_path)
            for fp in frame_paths:
                if os.path.exists(fp):
                    os.remove(fp)


@bot.command(name="askai", aliases=["ai"])
async def askai_cmd(ctx, *, question: str = None):
    """General-purpose AI assistant, like Gemini/ChatGPT — ask it anything. Attach or reply to
    a screenshot/video and it'll actually look at it (e.g. an editing-software error, a
    settings screen, a clip you want help with).
    Usage: `.askai <question>` (optionally attach/reply with an image or video)."""
    source_message = ctx.message
    if ctx.message.reference and not ctx.message.attachments:
        try:
            replied = await ctx.channel.fetch_message(ctx.message.reference.message_id)
            if replied.attachments:
                source_message = replied
        except discord.HTTPException:
            pass

    if not question and not source_message.attachments:
        await ctx.send("Usage: `.askai <your question>` — you can also attach or reply to a screenshot/video.")
        return

    async with ctx.typing():
        image_paths, video_cleanup = await _gather_ask_ai_media(source_message)
        prompt = ASK_AI_PROMPT_HEADER + (question or "What do you see here? Help with whatever's shown.")
        try:
            answer = await asyncio.get_running_loop().run_in_executor(None, _call_gemini_vision, image_paths, prompt)
            embed = discord.Embed(title="🤖 Ask AI", description=answer[:4000], color=discord.Color.teal())
            if image_paths:
                embed.set_footer(text="Looked at the attached image/video to answer.")
            _style_ai_result_embed(embed, ctx.author.display_avatar.url)
            await ctx.send(embed=embed)
        except RuntimeError as e:
            await ctx.send(f"⚠️ {e}")
        except Exception as e:
            print(f"⚠️ .askai failed: {e}")
            await ctx.send("⚠️ Something went wrong answering that. Try again in a bit.")
        finally:
            for fp in image_paths:
                if os.path.exists(fp):
                    os.remove(fp)
            for vp in video_cleanup:
                if os.path.exists(vp):
                    os.remove(vp)


@bot.command(name="aicaption", aliases=["aiCaption"])
async def aicaption_cmd(ctx, *, args: str = None):
    """Text-command version of /ai-caption — also works with an attached/replied video or image
    (then it captions THAT, like /youtube-tiktok-caption, instead of asking for a topic).
    Usage: `.aicaption <platform> <topic>` (e.g. `.aicaption tiktok my new setup`).
    No arguments? The bot asks step by step."""
    source_message = ctx.message
    if ctx.message.reference and not ctx.message.attachments:
        try:
            source_message = await ctx.channel.fetch_message(ctx.message.reference.message_id)
        except discord.HTTPException:
            pass

    platform_value = None
    topic = None
    if args:
        parts = args.strip().split(maxsplit=1)
        first_word = parts[0].lower()
        if first_word in AI_CAPTION_PLATFORM_KEYWORDS and len(parts) > 1:
            platform_value = AI_CAPTION_PLATFORM_KEYWORDS[first_word]
            topic = parts[1].strip()
        else:
            topic = args.strip()

    media_paths, _ = await _get_media_paths_from_message(source_message)

    def check(m):
        return m.author.id == ctx.author.id and m.channel.id == ctx.channel.id

    # Media (video/image/TikTok-photo-post) beats a topic — same behaviour as the slash command
    # family: if there's something to look at, describe THAT instead of asking questions.
    if not media_paths:
        if platform_value is None:
            await ctx.send("📱 Which platform? Reply with e.g. `tiktok`, `instagram`, `youtube`, `x`, or `general`.")
            try:
                reply = await bot.wait_for("message", check=check, timeout=60)
            except asyncio.TimeoutError:
                await ctx.send("⌛ No response in time — cancelling. Try again with `.aicaption <platform> <topic>`.")
                return
            platform_value = AI_CAPTION_PLATFORM_KEYWORDS.get(reply.content.strip().lower(), reply.content.strip())

        if not topic:
            await ctx.send("📝 What's it about? Briefly describe the topic (or attach an image/video now and I'll describe that instead).")
            try:
                reply = await bot.wait_for("message", check=check, timeout=90)
            except asyncio.TimeoutError:
                await ctx.send("⌛ No response in time — cancelling.")
                return
            if reply.attachments or re.search(r"https?://\S+", reply.content or ""):
                media_paths, _ = await _get_media_paths_from_message(reply)
            topic = reply.content.strip()

    async with ctx.typing():
        try:
            if media_paths:
                raw = await asyncio.get_running_loop().run_in_executor(
                    None, _call_gemini_vision, media_paths, CONTENT_INFO_PROMPT
                )
                parsed = _parse_content_info(raw)
                view = ContentInfoView(media_paths)
                await ctx.send(embed=_style_ai_result_embed(_build_content_info_embed(parsed), ctx.author.display_avatar.url), view=view)
            else:
                prompt = AI_CAPTION_PROMPT_TEMPLATE.format(
                    platform=platform_value, topic=topic or "no specific topic given"
                )
                raw = await asyncio.get_running_loop().run_in_executor(None, _call_gemini_vision, [], prompt)
                parsed = _parse_content_info(raw)
                view = AICaptionView(topic or "", platform_value)
                await ctx.send(embed=_style_ai_result_embed(_build_ai_caption_embed(parsed, platform_value), ctx.author.display_avatar.url), view=view)
        except RuntimeError as e:
            await ctx.send(f"⚠️ {e}")
        except Exception as e:
            print(f"⚠️ .aicaption failed: {e}")
            await ctx.send("⚠️ Something went wrong. Try again in a bit.")


@bot.command()
async def purgebadwords(ctx, target: str = None):
    if not has_points_permission(ctx.author):
        await ctx.send("❌ Only Top Edit Manager or Staff can use this.")
        return
    words = load_badwords(ctx.guild.id)
    if not words:
        await ctx.send("Your risk-word list is empty. Add words first with `!badwords add <word>`.")
        return
    if not target:
        await ctx.send("Usage: `!purgebadwords #channel` for one channel, or `!purgebadwords all` for every channel.")
        return

    if target.lower() == "all":
        status = await ctx.send(f"⏳ Scanning **all channels** against {len(words)} risk word(s)... (0/0 channels)")
        last_edit = datetime.now(timezone.utc)

        async def progress(channel, done, total, scanned, deleted):
            nonlocal last_edit
            now = datetime.now(timezone.utc)
            if done < total and (now - last_edit).total_seconds() < 4:
                return
            last_edit = now
            try:
                if done >= total:
                    await status.edit(content=f"✅ Done. Scanned {total} channel(s), **{scanned}** message(s) total, deleted **{deleted}**.")
                else:
                    await status.edit(content=f"⏳ Scanned {channel.mention} ({done}/{total} channels)... {scanned} messages scanned, {deleted} deleted so far.")
            except discord.HTTPException:
                pass

        await purge_guild_with_words(ctx.guild, words, progress=progress)
        return

    try:
        channel = await commands.TextChannelConverter().convert(ctx, target)
    except commands.BadArgument:
        await ctx.send("Couldn't find that channel. Use `!purgebadwords #channel` or `!purgebadwords all`.")
        return

    if not channel.permissions_for(ctx.guild.me).manage_messages:
        await ctx.send(f"❌ I don't have **Manage Messages** permission in {channel.mention}.")
        return

    status = await ctx.send(f"⏳ Scanning {channel.mention} against {len(words)} risk word(s)... (0 scanned, 0 deleted)")
    last_edit = datetime.now(timezone.utc)

    async def progress(scanned, deleted, final=False):
        nonlocal last_edit
        now = datetime.now(timezone.utc)
        if not final and (now - last_edit).total_seconds() < 4:
            return
        last_edit = now
        try:
            if final:
                await status.edit(content=f"✅ Done. Scanned **{scanned}** message(s), deleted **{deleted}** in {channel.mention}.")
            else:
                await status.edit(content=f"⏳ Scanning {channel.mention}... ({scanned} scanned, {deleted} deleted so far)")
        except discord.HTTPException:
            pass

    await purge_channel_with_words(channel, words, progress=progress)


@bot.command(name="create-embed", aliases=["createembed"])
async def create_embed_cmd(ctx):
    """Points staff to the visual embed builder on the website dashboard — build title,
    description, fields, color, image, footer etc. with a live preview and send it to any
    channel on this server, no code needed."""
    if not has_picker_permission(ctx.author):
        await ctx.send("❌ Only Top Edit Picker, Manager, or Staff can use this.")
        return
    base = (DASHBOARD_BASE_URL or "").rstrip("/")
    if not base:
        await ctx.send("⚠️ Embed builder isn't configured yet — ask an admin to set `DISCORD_REDIRECT_URI`.")
        return
    url = f"{base}/dashboard/{ctx.guild.id}/embed-builder"
    embed = discord.Embed(
        title="🎨 Embed Builder",
        description=(
            f"Build your embed visually — title, description, fields, color, image, footer, "
            f"live preview — then send it straight to any channel here.\n\n**[Open the Embed Builder]({url})**\n\n"
            f"*(Log in with Discord if asked — you need Administrator on this server.)*"
        ),
        color=discord.Color.purple(),
    )
    await ctx.send(embed=embed)


# ============================================================
# Slash commands (/)
# ============================================================

@bot.tree.command(name="ping", description="Check the bot's latency and status")
async def slash_ping(interaction: discord.Interaction):
    await interaction.response.send_message(embed=build_ping_embed(round(bot.latency * 1000)))


@bot.tree.command(name="dashboard", description="Show live bot stats")
async def slash_dashboard(interaction: discord.Interaction):
    await interaction.response.send_message(embed=build_dashboard_embed())


@bot.tree.command(name="help", description="Show all available commands")
async def slash_help(interaction: discord.Interaction):
    view = HelpView()
    await interaction.response.send_message(embed=build_help_home_embed(), view=view)
    view.message = await interaction.original_response()


@bot.tree.command(name="tutorial", description="Full walkthrough of how the Top Edit system works")
async def slash_tutorial(interaction: discord.Interaction):
    await interaction.response.send_message(embed=build_tutorial_embed(interaction.guild))


@bot.tree.command(name="flip", description="Flip a coin")
async def slash_flip(interaction: discord.Interaction):
    result = random.choice(["Heads", "Tails"])
    await interaction.response.send_message(f"🪙 The coin landed on **{result}**!")


@bot.tree.command(name="timeleft", description="See how much time is left until voting starts/ends")
async def slash_timeleft(interaction: discord.Interaction):
    await interaction.response.send_message(build_timeleft_message(interaction.guild.id if interaction.guild else None))


@bot.tree.command(name="previewvotes", description="Preview which edits are queued for the next vote (only visible to you)")
async def slash_previewvotes(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    entries = await collect_pending_entries(interaction.guild)
    if entries is None:
        await interaction.followup.send("⚠️ Couldn't find the submission channel or Picker role in this server.", ephemeral=True)
        return
    if not entries:
        await interaction.followup.send("📭 No edits queued for the next vote yet — post one in the submissions channel and ping the Picker role.", ephemeral=True)
        return

    lines = [f"**{i}.** {entry['author_name']} — {entry['video_url']}" for i, entry in enumerate(entries, start=1)]
    embed = discord.Embed(
        title="🗳️ Pending Edits Preview",
        description=(
            "These are the edits currently queued to go into the **next voting poll** — "
            "not a ranking, not results, just what's lined up so far:\n\n" + "\n".join(lines)
        ),
        color=discord.Color.blurple(),
    )
    embed.set_footer(text=f"{len(entries)} edit(s) will go into the next vote · Only visible to you")
    await interaction.followup.send(embed=embed, ephemeral=True)


@bot.tree.command(name="ranks", description="See every editor rank and how to earn points")
async def slash_ranks(interaction: discord.Interaction):
    await interaction.response.send_message(embed=build_ranks_embed())


@bot.tree.command(name="points", description="Check a user's points")
@app_commands.describe(member="Whose points to check (defaults to you)")
async def slash_points(interaction: discord.Interaction, member: discord.Member = None):
    member = member or interaction.user
    view = PointsInfoView(interaction.guild, member, interaction.user.id)
    await interaction.response.send_message(await build_points_message(interaction.guild, member), view=view)


@bot.tree.command(name="leaderboard", description="Show the top 20 point rankings")
async def slash_leaderboard(interaction: discord.Interaction):
    await interaction.response.defer()
    view = LeaderboardView(interaction.guild)
    file = await generate_leaderboard_image(interaction.guild, page=1)
    if file:
        view.message = await interaction.followup.send(file=file, view=view)
    else:
        view.message = await interaction.followup.send(embed=await build_leaderboard_embed(interaction.guild, page=1), view=view)


@bot.tree.command(name="purgeword", description="Delete every message in a channel containing a specific word (Manager/Staff only)")
@app_commands.describe(channel="Channel to clean up", word="Word to delete messages for (whole-word match, case-insensitive)")
async def slash_purgeword(interaction: discord.Interaction, channel: discord.TextChannel, word: str):
    if not has_points_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Manager or Staff can use this.", ephemeral=True)
        return
    if not channel.permissions_for(interaction.guild.me).manage_messages:
        await interaction.response.send_message(f"❌ I don't have **Manage Messages** permission in {channel.mention}.", ephemeral=True)
        return

    await interaction.response.send_message(f"⏳ Scanning {channel.mention} for **{word}**... (0 scanned, 0 deleted)")
    last_edit = datetime.now(timezone.utc)

    async def progress(scanned, deleted, final=False):
        nonlocal last_edit
        now = datetime.now(timezone.utc)
        if not final and (now - last_edit).total_seconds() < 4:
            return
        last_edit = now
        try:
            if final:
                await interaction.edit_original_response(content=f"✅ Done. Scanned **{scanned}** message(s), deleted **{deleted}** containing '{word}' in {channel.mention}.")
            else:
                await interaction.edit_original_response(content=f"⏳ Scanning {channel.mention} for **{word}**... ({scanned} scanned, {deleted} deleted so far)")
        except discord.HTTPException:
            pass

    await purge_messages_with_word(channel, word, progress=progress)


@bot.tree.command(name="badwords", description="Manage the risk-word list used by /purgebadwords (Manager/Staff only)")
@app_commands.describe(action="What to do", word="The word/phrase (not needed for 'list')")
@app_commands.choices(action=[
    app_commands.Choice(name="add", value="add"),
    app_commands.Choice(name="remove", value="remove"),
    app_commands.Choice(name="list", value="list"),
])
async def slash_badwords(interaction: discord.Interaction, action: app_commands.Choice[str], word: str = None):
    if not has_points_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Manager or Staff can use this.", ephemeral=True)
        return
    words = load_badwords(interaction.guild.id)

    if action.value == "add":
        if not word:
            await interaction.response.send_message("Give me a word to add.", ephemeral=True)
            return
        if word.lower().strip() in [w.lower() for w in words]:
            await interaction.response.send_message(f"`{word}` is already on the list.", ephemeral=True)
            return
        words.append(word.lower().strip())
        save_badwords(interaction.guild.id, words)
        await interaction.response.send_message(f"✅ Added `{word}` to the risk-word list. Run `/purgebadwords` to purge with it — nothing is deleted automatically.")
    elif action.value == "remove":
        if not word:
            await interaction.response.send_message("Give me a word to remove.", ephemeral=True)
            return
        new_words = [w for w in words if w.lower() != word.lower().strip()]
        if len(new_words) == len(words):
            await interaction.response.send_message(f"`{word}` wasn't on the list.", ephemeral=True)
            return
        save_badwords(interaction.guild.id, new_words)
        await interaction.response.send_message(f"✅ Removed `{word}` from the list.")
    else:
        if words:
            await interaction.response.send_message(f"⚠️ Risk-word list ({len(words)}): " + ", ".join(f"`{w}`" for w in words), ephemeral=True)
        else:
            await interaction.response.send_message("List is empty. Add one with `/badwords add`.", ephemeral=True)


@bot.tree.command(name="purgebadwords", description="Purge every risk-word list match in one channel, or ALL channels if none given (Manager/Staff only)")
@app_commands.describe(channel="Leave empty to scan EVERY channel instead of just one")
async def slash_purgebadwords(interaction: discord.Interaction, channel: discord.TextChannel = None):
    if not has_points_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Manager or Staff can use this.", ephemeral=True)
        return
    words = load_badwords(interaction.guild.id)
    if not words:
        await interaction.response.send_message("Your risk-word list is empty. Add words first with `/badwords add`.", ephemeral=True)
        return

    if channel is None:
        await interaction.response.send_message(f"⏳ Scanning **all channels** against {len(words)} risk word(s)... (0/0 channels)")
        last_edit = datetime.now(timezone.utc)

        async def progress(ch, done, total, scanned, deleted):
            nonlocal last_edit
            now = datetime.now(timezone.utc)
            if done < total and (now - last_edit).total_seconds() < 4:
                return
            last_edit = now
            try:
                if done >= total:
                    await interaction.edit_original_response(content=f"✅ Done. Scanned {total} channel(s), **{scanned}** message(s) total, deleted **{deleted}**.")
                else:
                    await interaction.edit_original_response(content=f"⏳ Scanned {ch.mention} ({done}/{total} channels)... {scanned} messages scanned, {deleted} deleted so far.")
            except discord.HTTPException:
                pass

        await purge_guild_with_words(interaction.guild, words, progress=progress)
        return

    if not channel.permissions_for(interaction.guild.me).manage_messages:
        await interaction.response.send_message(f"❌ I don't have **Manage Messages** permission in {channel.mention}.", ephemeral=True)
        return

    await interaction.response.send_message(f"⏳ Scanning {channel.mention} against {len(words)} risk word(s)... (0 scanned, 0 deleted)")
    last_edit = datetime.now(timezone.utc)

    async def progress(scanned, deleted, final=False):
        nonlocal last_edit
        now = datetime.now(timezone.utc)
        if not final and (now - last_edit).total_seconds() < 4:
            return
        last_edit = now
        try:
            if final:
                await interaction.edit_original_response(content=f"✅ Done. Scanned **{scanned}** message(s), deleted **{deleted}** in {channel.mention}.")
            else:
                await interaction.edit_original_response(content=f"⏳ Scanning {channel.mention}... ({scanned} scanned, {deleted} deleted so far)")
        except discord.HTTPException:
            pass

    await purge_channel_with_words(channel, words, progress=progress)
@bot.tree.command(name="addpoints", description="Add points to a user (Top Edit Manager/Staff only)")
@app_commands.describe(member="User to add points to", amount="How many points to add")
async def slash_addpoints(interaction: discord.Interaction, member: discord.Member, amount: int):
    if not has_points_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Manager or Staff can use this.", ephemeral=True)
        return
    new_total = await award_points(interaction.guild, member.id, amount)
    logged = await log_points_action(interaction.guild, interaction.user, member.id, amount, new_total, "add")
    warning = "" if logged else f"\n⚠️ *Couldn't post to the points log channel — check it's configured on the website dashboard's Settings page and that the bot can see/send in it.*"
    await interaction.response.send_message(f"✅ Added **{amount}** point(s) to {member.mention}. New total: **{new_total}**{warning}", ephemeral=True)


@bot.tree.command(name="removepoints", description="Remove points from a user (Top Edit Manager/Staff only)")
@app_commands.describe(member="User to remove points from", amount="How many points to remove")
async def slash_removepoints(interaction: discord.Interaction, member: discord.Member, amount: int):
    if not has_points_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Manager or Staff can use this.", ephemeral=True)
        return
    new_total = await award_points(interaction.guild, member.id, -amount)
    logged = await log_points_action(interaction.guild, interaction.user, member.id, amount, new_total, "remove")
    warning = "" if logged else f"\n⚠️ *Couldn't post to the points log channel — check it's configured on the website dashboard's Settings page and that the bot can see/send in it.*"
    await interaction.response.send_message(f"✅ Removed **{amount}** point(s) from {member.mention}. New total: **{new_total}**{warning}", ephemeral=True)


@bot.tree.command(name="tournamentpoll", description="Start a poll that gives a role to everyone who votes (Manage Roles/Admin only)")
@app_commands.describe(
    role="Role to give to everyone who votes on this poll",
    question="The poll question shown to everyone",
    duration_hours="How long the poll stays open, in hours (1-168, default 24)",
)
async def slash_tournamentpoll(
    interaction: discord.Interaction,
    role: discord.Role,
    question: str = "Vote to join the tournament!",
    duration_hours: app_commands.Range[int, 1, 168] = 24,
):
    if not (interaction.user.guild_permissions.administrator or interaction.user.guild_permissions.manage_roles):
        await interaction.response.send_message("❌ You need Manage Roles or Administrator permission to use this.", ephemeral=True)
        return
    if role >= interaction.guild.me.top_role:
        await interaction.response.send_message(
            f"❌ I can't manage {role.mention} — it's above my own top role. Move my role above it in Server Settings → Roles.",
            ephemeral=True,
        )
        return
    poll = discord.Poll(question=question, duration=timedelta(hours=duration_hours))
    poll.add_answer(text="I'm in! 🏆")
    await interaction.response.send_message("⏳ Starting the tournament poll...", ephemeral=True)
    sent = await interaction.channel.send(poll=poll)
    polls = load_tournament_polls(interaction.guild.id)
    ends_at = (datetime.now(timezone.utc) + timedelta(hours=duration_hours)).isoformat()
    polls.append({
        "message_id": sent.id,
        "channel_id": sent.channel.id,
        "role_id": role.id,
        "ends_at": ends_at,
    })
    save_tournament_polls(interaction.guild.id, polls)
    await interaction.followup.send(
        f"✅ Tournament poll live in {sent.channel.mention} — anyone who votes gets {role.mention} "
        f"automatically. Voting stays open **{duration_hours}h**. The role is **not** removed "
        f"automatically — run `/tournamentpollend` whenever you're ready to strip it from everyone.",
        ephemeral=True,
    )


@bot.tree.command(name="tournamentpollend", description="End a tournament poll early and remove its role from everyone who has it (Manage Roles/Admin only)")
@app_commands.describe(role="The tournament role to remove from everyone (leave empty to end the most recently started one)")
async def slash_tournamentpollend(interaction: discord.Interaction, role: discord.Role = None):
    if not (interaction.user.guild_permissions.administrator or interaction.user.guild_permissions.manage_roles):
        await interaction.response.send_message("❌ You need Manage Roles or Administrator permission to use this.", ephemeral=True)
        return
    polls = load_tournament_polls(interaction.guild.id)
    if not polls:
        await interaction.response.send_message("❌ No active tournament poll found for this server.", ephemeral=True)
        return
    if role is not None:
        target = next((p for p in polls if p["role_id"] == role.id), None)
        if target is None:
            await interaction.response.send_message(f"❌ No active tournament poll is using {role.mention}.", ephemeral=True)
            return
    else:
        target = polls[-1]
    await interaction.response.send_message("⏳ Ending tournament poll and removing the role from everyone...", ephemeral=True)
    removed_count = await remove_role_from_everyone(interaction.guild, target["role_id"])
    remaining = [p for p in polls if p is not target]
    save_tournament_polls(interaction.guild.id, remaining)
    role_obj = interaction.guild.get_role(target["role_id"])
    role_label = role_obj.mention if role_obj else "the role"
    await interaction.followup.send(f"✅ Tournament poll ended — removed {role_label} from **{removed_count}** member(s).", ephemeral=True)


@bot.tree.command(name="removerolefrom", description="Remove a role from several specific users at once (Manage Roles/Admin only)")
@app_commands.describe(role="Role to remove", users="The users to remove it from — @mention or paste their IDs, space-separated")
async def slash_removerolefrom(interaction: discord.Interaction, role: discord.Role, users: str):
    if not (interaction.user.guild_permissions.administrator or interaction.user.guild_permissions.manage_roles):
        await interaction.response.send_message("❌ You need Manage Roles or Administrator permission to use this.", ephemeral=True)
        return
    if role >= interaction.guild.me.top_role:
        await interaction.response.send_message(
            f"❌ I can't manage {role.mention} — it's above my own top role. Move my role above it in Server Settings → Roles.",
            ephemeral=True,
        )
        return
    user_ids = re.findall(r"\d{15,20}", users)
    if not user_ids:
        await interaction.response.send_message("❌ Couldn't find any user mentions or IDs in that list.", ephemeral=True)
        return
    await interaction.response.send_message(f"⏳ Removing {role.mention} from {len(user_ids)} user(s)...", ephemeral=True)
    removed, no_role, not_found = [], [], []
    seen = set()
    for uid_str in user_ids:
        uid = int(uid_str)
        if uid in seen:
            continue
        seen.add(uid)
        try:
            member = interaction.guild.get_member(uid) or await interaction.guild.fetch_member(uid)
        except discord.NotFound:
            not_found.append(uid_str)
            continue
        if role not in member.roles:
            no_role.append(member.mention)
            continue
        try:
            await member.remove_roles(role, reason=f"Bulk role removal by {interaction.user}")
            removed.append(member.mention)
        except discord.HTTPException:
            not_found.append(member.mention)
    summary = f"✅ Removed {role.mention} from **{len(removed)}** user(s)."
    if no_role:
        summary += f"\n⚠️ Already didn't have the role: {', '.join(no_role[:15])}" + ("..." if len(no_role) > 15 else "")
    if not_found:
        summary += f"\n⚠️ Couldn't find/update: {', '.join(str(x) for x in not_found[:15])}" + ("..." if len(not_found) > 15 else "")
    await interaction.followup.send(summary, ephemeral=True)


@bot.tree.command(name="testcollect", description="Manually run the collect-edits job (Picker/Manager/Staff only)")
async def slash_testcollect(interaction: discord.Interaction):
    # Defer FIRST, before any permission check or config/DB read. Those can be slow
    # enough (a cold Postgres connection on Render's free tier, etc.) to blow past
    # Discord's 3-second response window — and once that window is gone, send_message()
    # raises silently (no error handler existed to surface it), so the command looked
    # like it "did nothing." Deferring immediately buys the full 15-minute followup
    # window instead, so this can never go silent again.
    await interaction.response.defer(ephemeral=True)
    if not has_picker_permission(interaction.user):
        await interaction.followup.send("❌ Only Top Edit Picker/Manager/Staff can use this.", ephemeral=True)
        return
    await interaction.followup.send("⏳ Running collect job manually...")
    try:
        await run_collect_job()
    except Exception as e:
        print(f"⚠️ /testcollect failed: {e}")
        await interaction.followup.send(f"⚠️ Collect job failed: {e}")
        return
    entries = get_poll_state(interaction.guild.id)["entries"]
    if entries:
        names = ", ".join(dict.fromkeys(e["author_name"] for e in entries))  # de-duped, order-preserved
        await interaction.followup.send(f"✅ Done. {len(entries)} edit(s) posted for voting — from {names}.")
    else:
        await interaction.followup.send("✅ Done. No new edits found to post.")


@bot.tree.command(name="testresults", description="Manually run the announce-winner job (Picker/Manager/Staff only)")
async def slash_testresults(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    if not has_picker_permission(interaction.user):
        await interaction.followup.send("❌ Only Top Edit Picker/Manager/Staff can use this.", ephemeral=True)
        return
    await interaction.followup.send("⏳ Running results job manually...")
    try:
        await run_results_job()
    except Exception as e:
        print(f"⚠️ /testresults failed: {e}")
        await interaction.followup.send(f"⚠️ Results job failed: {e}")
        return
    await interaction.followup.send("✅ Done.")


@bot.tree.command(name="setday", description="Set the Top Edit day counter for this server (Picker/Manager/Staff only)")
@app_commands.describe(day="The day number the NEXT results announcement should show, e.g. 80")
async def slash_setday(interaction: discord.Interaction, day: int):
    await interaction.response.defer(ephemeral=True)
    if not has_picker_permission(interaction.user):
        await interaction.followup.send("❌ Only Top Edit Picker/Manager/Staff can use this.", ephemeral=True)
        return
    if day < 1:
        await interaction.followup.send("❌ Day number has to be 1 or higher.", ephemeral=True)
        return
    save_day(interaction.guild.id, day)
    await interaction.followup.send(f"✅ Day counter set. The next winner announcement will show **DAY {day}**.")



# ============================================================
# /find-asset — searches the web for an overlay/asset from a text description
# ============================================================

@bot.tree.command(name="find-asset", description="Search the web for an editing overlay/asset (e.g. 'dad overlay')")
@app_commands.describe(query="Describe exactly what you're looking for — the more specific, the better")
async def slash_find_asset(interaction: discord.Interaction, query: str):
    await interaction.response.defer()
    try:
        results = await asyncio.get_running_loop().run_in_executor(None, _web_search, query, True, 5)
    except RuntimeError as e:
        await interaction.followup.send(f"⚠️ {e}")
        return
    except Exception as e:
        print(f"⚠️ /find-asset failed: {e}")
        await interaction.followup.send("⚠️ Something went wrong while searching. Try again in a bit.")
        return

    if not results:
        await interaction.followup.send(f"No results found for **{query}**. Try a more specific description.")
        return

    embed = discord.Embed(
        title=f"🔎 Results for: {query}",
        description="\n".join(f"[{r['title']}]({r['link']})" for r in results if r["link"]),
        color=discord.Color.blurple(),
    )
    if results[0].get("image"):
        embed.set_image(url=results[0]["image"])
    embed.set_footer(text="Search results — always double-check quality/license before using an asset.")
    await interaction.followup.send(embed=embed)


# ============================================================
# /rate-edit — AI feedback on an edit's editing quality
# ============================================================

def _rating_unavailable_embed() -> discord.Embed:
    """Shown whenever .airating/rate-edit can't get a video to actually rate — whether no
    link/attachment was found at all, or a link was found but the download itself failed
    (almost always a YouTube link right now, see below)."""
    embed = discord.Embed(
        title="⚠️ Couldn't Rate That",
        description=(
            "Right now only **TikTok links** and **direct video attachments** work reliably "
            "for rating — YouTube support is currently limited due to cookie/token restrictions.\n\n"
            "Send your video as a **raw attachment**, then reply to it with `.airating`."
        ),
        color=discord.Color.orange(),
    )
    return embed


def _style_ai_result_embed(embed: discord.Embed, avatar_url: str = None) -> discord.Embed:
    """Applies the same clean, eye-catching finish used across Zexo's other embeds (the ping/
    AI-rating reminders) to an AI-result embed: a timestamp, the requester's avatar as a
    thumbnail, and the bot's icon next to the footer text."""
    embed.timestamp = discord.utils.utcnow()
    if avatar_url:
        embed.set_thumbnail(url=avatar_url)
    icon = bot.user.display_avatar.url if bot.user else None
    embed.set_footer(text=embed.footer.text if embed.footer and embed.footer.text else "Zexo", icon_url=icon)
    return embed


RATE_EDIT_PROMPT = (
    "You are an experienced, honest video editor giving direct feedback on frames pulled from "
    "someone's edit. Judge purely on what's actually visible in these frames — score based on "
    "genuine merit, not on hitting a preset distribution, and not on being polite. Most casual "
    "submissions are genuinely mediocre — basic cuts, no real color grading, no sync/impact "
    "framing, generic look — and that should land as a low score, not get rounded up out of "
    "courtesy. Don't inflate weak work with empty praise, but just as importantly, don't deflate "
    "a genuinely strong edit just to seem strict — if it's excellent, say so and score it that "
    "way. Based only on what's visible in these frames, write a short, direct review covering:\n"
    "1. An overall score out of 10 for visual polish (grading, sync/impact framing, composition). "
    "Use the full range and be exact, not generous: 9-10 for exceptional, professional-grade work; "
    "7-8 for genuinely strong work with only minor issues; 5-6 for competent but unremarkable work "
    "with clear room to improve; 3-4 for weak work with real, noticeable problems (flat grading, "
    "sloppy cuts, no real technique); 1-2 for barely-edited or effectively raw footage. If you're "
    "torn between two scores, pick the lower one — err toward accuracy over kindness.\n"
    "2. A skill tier that best fits this edit — pick exactly one of: Beginner, Intermediate, "
    "Advanced, Pro. The tier must line up with the score you gave, not be more generous than it: "
    "Beginner for scores 1-4, Intermediate for 5-6, Advanced for 7-8, Pro for 9-10. Base the score "
    "itself only on the technique actually visible in the frames, not on an assumption that most "
    "submissions are beginner-level — but don't hand out a nicer-sounding tier than the score earns "
    "either.\n"
    "3. Your best guess at what software was likely used (e.g. CapCut, Alight Motion, Premiere, "
    "After Effects) — only name a specific one if the visual style gives a clear, distinctive "
    "signal (a recognizable preset, transition style, or text-animation look). If the frames don't "
    "clearly point to one, say the software isn't confidently identifiable from stills rather than "
    "guessing.\n"
    "4. 2-3 concrete, specific tips or criticisms — call out real weaknesses if there are any "
    "(flat/unbalanced color grading, muddy composition, low-effort framing, generic look, etc.), "
    "but don't invent flaws in an edit that's genuinely well done — note what's working instead.\n"
    "Be honest and direct, not falsely encouraging AND not artificially harsh — accurate feedback "
    "either way. Keep it under 170 words. "
    "Important: you're judging a handful of still frames, not the full video's motion/timing/sync, "
    "so don't claim to assess smoothness or transitions you can't actually see, and don't claim to "
    "compare this against other specific edits or a live leaderboard — you have no access to those. "
    "The skill tier is your own read of these frames, not a placement on any official server rank."
)


async def _run_rate_edit(interaction: discord.Interaction, source_message: discord.Message):
    if not interaction.guild:
        await interaction.response.send_message("⚠️ This only works inside a server.", ephemeral=True)
        return

    await interaction.response.defer()

    video_path, link_found = await _get_video_path_from_message(source_message)
    if not video_path:
        await interaction.followup.send(embed=_rating_unavailable_embed(), ephemeral=True)
        return

    frame_paths = []
    try:
        frame_paths = await asyncio.get_running_loop().run_in_executor(None, _extract_frames, video_path, 4)
        if not frame_paths:
            await interaction.followup.send("⚠️ Couldn't extract frames from that video.", ephemeral=True)
            return

        feedback = await asyncio.get_running_loop().run_in_executor(
            None, _call_gemini_vision, frame_paths, RATE_EDIT_PROMPT
        )

        embed = discord.Embed(
            title="🎬 Edit Rating",
            description=feedback,
            color=discord.Color.purple(),
        )
        embed.set_footer(text="AI-generated feedback from a few sampled frames — take it as a starting point, not gospel.")
        _style_ai_result_embed(embed, interaction.user.display_avatar.url)
        await interaction.followup.send(embed=embed)

    except RuntimeError as e:
        await interaction.followup.send(f"⚠️ {e}")
    except Exception as e:
        print(f"⚠️ /rate-edit failed: {e}")
        await interaction.followup.send("⚠️ Something went wrong while rating that edit. Try again in a bit.")
    finally:
        if os.path.exists(video_path):
            os.remove(video_path)
        for fp in frame_paths:
            if os.path.exists(fp):
                os.remove(fp)


@bot.tree.command(name="rate-edit", description="Get honest AI feedback on an edit (reply-context or paste a link)")
@app_commands.describe(video_url="Link to the edit — leave empty if you're using this on a message with a video attached")
async def slash_rate_edit(interaction: discord.Interaction, video_url: str = None):
    if video_url:
        fake_message = type("Obj", (), {"attachments": [], "content": video_url, "guild": interaction.guild})()
        await _run_rate_edit(interaction, fake_message)
        return

    if isinstance(interaction.channel, discord.TextChannel):
        async for msg in interaction.channel.history(limit=1, before=interaction.created_at):
            if msg.author.id == interaction.user.id and (msg.attachments or re.search(r"https?://\S+", msg.content or "")):
                await _run_rate_edit(interaction, msg)
                return

    await interaction.response.send_message(
        "⚠️ Give me a `video_url`, or use the **Rate this Edit** option from right-clicking the message (Apps menu).",
        ephemeral=True,
    )


@bot.tree.context_menu(name="Rate this Edit")
async def context_rate_edit(interaction: discord.Interaction, message: discord.Message):
    await _run_rate_edit(interaction, message)


@bot.tree.command(name="askai", description="Ask the AI assistant anything — attach a screenshot or video for it to look at too")
@app_commands.describe(question="Your question", attachment="Optional screenshot or video for the AI to look at")
async def slash_askai(interaction: discord.Interaction, question: str, attachment: discord.Attachment = None):
    await interaction.response.defer()
    image_paths: list[str] = []
    video_cleanup: list[str] = []
    try:
        if attachment is not None:
            if attachment.content_type and attachment.content_type.startswith("image"):
                out_path = f"/tmp/askai_{random.randint(0, 10**9)}.jpg"
                await attachment.save(out_path)
                image_paths.append(out_path)
            elif attachment.content_type and attachment.content_type.startswith("video"):
                out_path = f"/tmp/askai_{random.randint(0, 10**9)}.mp4"
                await attachment.save(out_path)
                video_cleanup.append(out_path)
                image_paths = await asyncio.get_running_loop().run_in_executor(None, _extract_frames, out_path, 4)

        prompt = ASK_AI_PROMPT_HEADER + question
        answer = await asyncio.get_running_loop().run_in_executor(None, _call_gemini_vision, image_paths, prompt)
        embed = discord.Embed(title="🤖 Ask AI", description=answer[:4000], color=discord.Color.teal())
        if image_paths:
            embed.set_footer(text="Looked at the attached image/video to answer.")
        _style_ai_result_embed(embed, interaction.user.display_avatar.url)
        await interaction.followup.send(embed=embed)
    except RuntimeError as e:
        await interaction.followup.send(f"⚠️ {e}")
    except Exception as e:
        print(f"⚠️ /askai failed: {e}")
        await interaction.followup.send("⚠️ Something went wrong answering that. Try again in a bit.")
    finally:
        for fp in image_paths:
            if os.path.exists(fp):
                os.remove(fp)
        for vp in video_cleanup:
            if os.path.exists(vp):
                os.remove(vp)


# ============================================================
# /youtube-tiktok-caption — eye-catching title, tags, and a long description for a video/screenshot
# (name makes it clear this is for writing your YouTube/TikTok post caption, not a generic label)
# ============================================================

CONTENT_INFO_PROMPT = (
    "You are a social media strategist writing metadata for a short-form video/edit based on "
    "the attached frame(s). Look closely at the visual style, subject, mood, and any text/logos "
    "visible, then reply with EXACTLY these four sections, each on its own line starting with "
    "the label shown:\n"
    "TITLE: a short, eye-catching, scroll-stopping title (under 10 words, no quotation marks)\n"
    "TAGS: 8-12 relevant hashtags, space-separated, each starting with #\n"
    "DESCRIPTION: a long, professional description (3-5 sentences) suitable for a video "
    "platform caption — describe the style/mood/content, don't invent specific facts you can't "
    "see (no fake creator names, software, or events).\n"
    "NOTE: one honest sentence flagging anything you're unsure about or couldn't clearly see.\n"
    "Base everything only on what's actually visible in the frame(s)."
)


def _parse_content_info(raw: str) -> dict:
    """Pulls TITLE/TAGS/DESCRIPTION/NOTE out of the model's labeled-line response."""
    result = {"TITLE": "", "TAGS": "", "DESCRIPTION": "", "NOTE": ""}
    current = None
    for line in raw.splitlines():
        matched = False
        for label in result:
            if line.strip().upper().startswith(f"{label}:"):
                current = label
                result[label] = line.split(":", 1)[1].strip()
                matched = True
                break
        if not matched and current:
            result[current] = (result[current] + " " + line.strip()).strip()
    return result


def _build_content_info_embed(parsed: dict) -> discord.Embed:
    embed = discord.Embed(
        title=parsed["TITLE"] or "Untitled",
        description=parsed["DESCRIPTION"] or "*No description generated.*",
        color=discord.Color.teal(),
    )
    if parsed["TAGS"]:
        embed.add_field(name="Tags", value=parsed["TAGS"], inline=False)
    if parsed["NOTE"]:
        embed.add_field(name="⚠️ Note", value=parsed["NOTE"], inline=False)
    embed.set_footer(text="AI-generated — doesn't fit? Hit 🔄 Regenerate below.")
    return embed


async def _get_media_paths_from_message(message: discord.Message) -> tuple[list[str], bool]:
    """Returns (frame_paths, is_temp_video) — either JPEG frames pulled from a video, or a
    downloaded still image saved as a single-entry list. Caller deletes the returned paths."""
    for att in message.attachments:
        if att.content_type and att.content_type.startswith("image"):
            out_path = f"/tmp/img_{random.randint(0, 10**9)}.jpg"
            await att.save(out_path)
            return [out_path], False

    video_path, _ = await _get_video_path_from_message(message)
    if video_path:
        frames = await asyncio.get_running_loop().run_in_executor(None, _extract_frames, video_path, 4)
        if os.path.exists(video_path):
            os.remove(video_path)
        return frames, False

    # No video attachment/link worked — if it's a TikTok/IG-style link, it might be a
    # "photo mode" slideshow post (no video stream at all, which is exactly why the video
    # download above came back empty). Fall back to grabbing the slide images directly.
    url_match = re.search(r"https?://\S+", message.content or "")
    if url_match and is_social_video_link(url_match.group(0)):
        photos = await asyncio.get_running_loop().run_in_executor(
            None, _download_social_photos, url_match.group(0)
        )
        if photos:
            return photos, False

    return [], False


class ContentInfoView(discord.ui.View):
    """Holds the 🔄 Regenerate button so a bad first result can be re-rolled without
    re-running the whole command from scratch."""

    def __init__(self, media_paths: list[str]):
        super().__init__(timeout=300)
        self.media_paths = media_paths

    @discord.ui.button(label="🔄 Regenerate", style=discord.ButtonStyle.secondary)
    async def regenerate(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.defer()
        try:
            raw = await asyncio.get_running_loop().run_in_executor(
                None, _call_gemini_vision, self.media_paths, CONTENT_INFO_PROMPT
            )
            parsed = _parse_content_info(raw)
            embed = _style_ai_result_embed(_build_content_info_embed(parsed), interaction.user.display_avatar.url)
            await interaction.edit_original_response(embed=embed, view=self)
        except RuntimeError as e:
            await interaction.followup.send(f"⚠️ {e}", ephemeral=True)
        except Exception as e:
            print(f"⚠️ /youtube-tiktok-caption regenerate failed: {e}")
            await interaction.followup.send("⚠️ Something went wrong regenerating. Try again in a bit.", ephemeral=True)

    async def on_timeout(self):
        for child in self.children:
            child.disabled = True


async def _run_youtube_tiktok_caption(interaction: discord.Interaction, source_message: discord.Message):
    await interaction.response.defer()

    media_paths, _ = await _get_media_paths_from_message(source_message)
    if not media_paths:
        await interaction.followup.send(
            "⚠️ Couldn't find a video or image attachment/link on that message.", ephemeral=True
        )
        return

    try:
        raw = await asyncio.get_running_loop().run_in_executor(
            None, _call_gemini_vision, media_paths, CONTENT_INFO_PROMPT
        )
        parsed = _parse_content_info(raw)
        view = ContentInfoView(media_paths)
        embed = _style_ai_result_embed(_build_content_info_embed(parsed), interaction.user.display_avatar.url)
        await interaction.followup.send(embed=embed, view=view)
        # media_paths are intentionally NOT deleted here — the Regenerate button reuses them.
        # They're temp files under /tmp and get cleaned up on the next deploy/restart.
    except RuntimeError as e:
        await interaction.followup.send(f"⚠️ {e}")
        for p in media_paths:
            if os.path.exists(p):
                os.remove(p)
    except Exception as e:
        print(f"⚠️ /youtube-tiktok-caption failed: {e}")
        await interaction.followup.send("⚠️ Something went wrong generating that. Try again in a bit.")
        for p in media_paths:
            if os.path.exists(p):
                os.remove(p)


@bot.tree.command(name="youtube-tiktok-caption", description="AI-generated title, tags, and description for your YouTube/TikTok post")
@app_commands.describe(media_url="Link to the video/image — leave empty if using this on a message with an attachment")
async def slash_youtube_tiktok_caption(interaction: discord.Interaction, media_url: str = None):
    if media_url:
        fake_message = type("Obj", (), {"attachments": [], "content": media_url, "guild": interaction.guild})()
        await _run_youtube_tiktok_caption(interaction, fake_message)
        return

    if isinstance(interaction.channel, discord.TextChannel):
        async for msg in interaction.channel.history(limit=1, before=interaction.created_at):
            if msg.author.id == interaction.user.id and (msg.attachments or re.search(r"https?://\S+", msg.content or "")):
                await _run_youtube_tiktok_caption(interaction, msg)
                return

    await interaction.response.send_message(
        "⚠️ Give me a `media_url`, or use the **Make YT/TikTok Caption** option from right-clicking the message (Apps menu).",
        ephemeral=True,
    )


@bot.tree.context_menu(name="Make YT/TikTok Caption")
async def context_youtube_tiktok_caption(interaction: discord.Interaction, message: discord.Message):
    await _run_youtube_tiktok_caption(interaction, message)


# ============================================================
# /ai-caption — pure text-in, text-out caption generator: user gives a topic + picks a
# platform, no media/attachment needed. Reuses the same GEMINI_API_KEY / _call_gemini_vision
# helper as /rate-edit and /youtube-tiktok-caption (frame_paths=[] just skips the image part).
# ============================================================
AI_CAPTION_PROMPT_TEMPLATE = (
    "You are a social media strategist writing a caption/post for {platform}. "
    "The topic/theme given by the user is: \"{topic}\".\n"
    "Reply with EXACTLY these four sections, each on its own line starting with the label shown:\n"
    "TITLE: a short, eye-catching, scroll-stopping title/hook (under 10 words, no quotation marks)\n"
    "TAGS: 8-12 relevant hashtags for {platform}, space-separated, each starting with #\n"
    "DESCRIPTION: an engaging caption (3-5 sentences) written in a tone that fits {platform}, "
    "based only on the given topic — don't invent specific facts, names, or events.\n"
    "NOTE: one short tip for making this post perform better on {platform}.\n"
)

def _build_ai_caption_embed(parsed: dict, platform: str) -> discord.Embed:
    embed = discord.Embed(
        title=parsed["TITLE"] or "Untitled",
        description=parsed["DESCRIPTION"] or "*No description generated.*",
        color=discord.Color.teal(),
    )
    if parsed["TAGS"]:
        embed.add_field(name="Tags", value=parsed["TAGS"], inline=False)
    if parsed["NOTE"]:
        embed.add_field(name="💡 Tip", value=parsed["NOTE"], inline=False)
    embed.set_footer(text=f"AI-generated caption for {platform} — doesn't fit? Hit 🔄 Regenerate below.")
    return embed


class AICaptionView(discord.ui.View):
    """Holds the 🔄 Regenerate button so a bad first result can be re-rolled without
    re-running the whole command (keeps the original topic/platform)."""

    def __init__(self, topic: str, platform: str):
        super().__init__(timeout=300)
        self.topic = topic
        self.platform = platform

    @discord.ui.button(label="🔄 Regenerate", style=discord.ButtonStyle.secondary)
    async def regenerate(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.defer()
        try:
            prompt = AI_CAPTION_PROMPT_TEMPLATE.format(platform=self.platform, topic=self.topic)
            raw = await asyncio.get_running_loop().run_in_executor(
                None, _call_gemini_vision, [], prompt
            )
            parsed = _parse_content_info(raw)
            embed = _style_ai_result_embed(_build_ai_caption_embed(parsed, self.platform), interaction.user.display_avatar.url)
            await interaction.edit_original_response(embed=embed, view=self)
        except RuntimeError as e:
            await interaction.followup.send(f"⚠️ {e}", ephemeral=True)
        except Exception as e:
            print(f"⚠️ /ai-caption regenerate failed: {e}")
            await interaction.followup.send("⚠️ Something went wrong regenerating. Try again in a bit.", ephemeral=True)

    async def on_timeout(self):
        for child in self.children:
            child.disabled = True


# ============================================================
# website.py content — the Flask side of Zexo (OAuth login, dashboard, Control Room, API)
# ============================================================
from flask import Flask, render_template_string, request, redirect, session, url_for
import threading

app = Flask(__name__)
app.secret_key = os.environ.get("FLASK_SECRET_KEY") or os.environ.get("DISCORD_TOKEN", "zexo-dev-secret")
# Without these, some mobile / in-app browsers (e.g. Discord's own webview) drop the login
# cookie between the OAuth redirect hops, which looks like the login "just repeating itself"
# forever — Discord silently re-approves and bounces you right back to /login. Marking the
# session permanent + giving cookies explicit, browser-friendly attributes fixes that.
app.config.update(
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=True,
    SESSION_COOKIE_HTTPONLY=True,
    PERMANENT_SESSION_LIFETIME=timedelta(days=30),
)

# --- Discord OAuth2 login, for the "Settings" pages on the dashboard ---
# Create these under your bot's application at https://discord.com/developers/applications
# -> OAuth2, and set them as env vars on Render:
#   DISCORD_CLIENT_ID       the application's Client ID
#   DISCORD_CLIENT_SECRET   the application's Client Secret
#   DISCORD_REDIRECT_URI    e.g. https://your-app.onrender.com/callback (must also be added
#                            under OAuth2 -> Redirects in the Discord dev portal, exactly)
OAUTH_CLIENT_ID = os.environ.get("DISCORD_CLIENT_ID")
OAUTH_CLIENT_SECRET = os.environ.get("DISCORD_CLIENT_SECRET")
OAUTH_REDIRECT_URI = os.environ.get("DISCORD_REDIRECT_URI")
# e.g. "https://your-app.onrender.com/callback" -> "https://your-app.onrender.com" — used to
# build links back to the dashboard from inside Discord (e.g. the `create-embed` command).
DASHBOARD_BASE_URL = (OAUTH_REDIRECT_URI or "").rsplit("/callback", 1)[0] if OAUTH_REDIRECT_URI else ""
DISCORD_API = "https://discord.com/api"
ADMINISTRATOR_BIT = 0x8
VOID_HQ_INVITE_URL = "https://discord.gg/y4CBUdzf2z"
# Permissions Zexo actually asks for when being added to a server: view/send/manage messages,
# embeds, attachments, message history, reactions, managing rank roles, and creating polls.
BOT_INVITE_PERMISSIONS = 562950221982784


def bot_invite_url(guild_id: int = None) -> str:
    """The link that actually ADDS the Zexo bot to a server (scope=bot+applications.commands).
    This is different from VOID_HQ_INVITE_URL, which just joins the Void HQ Discord server —
    using the wrong one here was why 'invite' didn't let people add the bot anywhere new."""
    url = (
        f"{DISCORD_API}/oauth2/authorize?client_id={OAUTH_CLIENT_ID}"
        f"&scope=bot%20applications.commands&permissions={BOT_INVITE_PERMISSIONS}"
    )
    if guild_id:
        url += f"&guild_id={guild_id}&disable_guild_select=true"
    return url


def oauth_configured() -> bool:
    return bool(OAUTH_CLIENT_ID and OAUTH_CLIENT_SECRET and OAUTH_REDIRECT_URI)


# Flask's default session is a SIGNED COOKIE stored in the browser — cookies have a hard ~4KB
# limit. Storing every guild (name + icon hash + permissions) for someone in 10+ servers blows
# past that easily; the browser then silently drops the cookie, so the "login" never actually
# sticks and immediately bounces back to /login — a fast, invisible loop. Fix: keep the cookie
# tiny (just id/username/avatar/access_token) and cache each user's guild list server-side here.
_user_guild_cache = {}  # user_id (str) -> list[{"id","name","permissions","icon"}]


def fetch_user_guilds(user_id: str, access_token: str):
    cached = _user_guild_cache.get(user_id)
    if cached is not None:
        return cached
    res = http_requests.get(
        f"{DISCORD_API}/users/@me/guilds",
        headers={"Authorization": f"Bearer {access_token}"},
        timeout=10,
    )
    if res.status_code != 200:
        return []
    guilds = [
        {"id": g["id"], "name": g["name"], "permissions": g.get("permissions", "0"), "icon": g.get("icon")}
        for g in res.json()
    ]
    _user_guild_cache[user_id] = guilds
    return guilds


@app.route('/login')
def login():
    if not oauth_configured():
        return "⚠️ Discord login isn't configured yet — set DISCORD_CLIENT_ID, DISCORD_CLIENT_SECRET and DISCORD_REDIRECT_URI.", 500
    params = {
        "client_id": OAUTH_CLIENT_ID,
        "redirect_uri": OAUTH_REDIRECT_URI,
        "response_type": "code",
        "scope": "identify guilds",
    }
    query = "&".join(f"{k}={http_requests.utils.quote(v)}" for k, v in params.items())
    return redirect(f"{DISCORD_API}/oauth2/authorize?{query}")


@app.route('/logout')
def logout():
    session.clear()
    return redirect(url_for('home'))


@app.route('/callback')
def oauth_callback():
    if not oauth_configured():
        return "⚠️ Discord login isn't configured yet.", 500
    code = request.args.get("code")
    if not code:
        return redirect(url_for('login'))

    token_res = http_requests.post(
        f"{DISCORD_API}/oauth2/token",
        data={
            "client_id": OAUTH_CLIENT_ID,
            "client_secret": OAUTH_CLIENT_SECRET,
            "grant_type": "authorization_code",
            "code": code,
            "redirect_uri": OAUTH_REDIRECT_URI,
        },
        headers={"Content-Type": "application/x-www-form-urlencoded"},
        timeout=10,
    )
    if token_res.status_code != 200:
        return "❌ Login failed while exchanging the code with Discord. Try again.", 400
    access_token = token_res.json().get("access_token")

    auth_header = {"Authorization": f"Bearer {access_token}"}
    user_res = http_requests.get(f"{DISCORD_API}/users/@me", headers=auth_header, timeout=10)
    guilds_res = http_requests.get(f"{DISCORD_API}/users/@me/guilds", headers=auth_header, timeout=10)
    if user_res.status_code != 200 or guilds_res.status_code != 200:
        return "❌ Login failed while fetching your Discord profile. Try again.", 400

    user = user_res.json()
    guilds = [
        {"id": g["id"], "name": g["name"], "permissions": g.get("permissions", "0"), "icon": g.get("icon")}
        for g in guilds_res.json()
    ]
    _user_guild_cache[str(user.get("id"))] = guilds

    session.permanent = True
    # Keep this small on purpose — see the comment above _user_guild_cache. Guilds live
    # server-side; the cookie only needs enough to look them back up.
    session["user"] = {
        "id": user.get("id"),
        "username": user.get("username"),
        "avatar": user.get("avatar"),
        "access_token": access_token,
    }
    return redirect(url_for('my_servers'))


def current_user():
    return session.get("user")


def user_guilds(user=None):
    """The (possibly cached) list of guilds for the logged-in user — never trust
    session["user"]["guilds"], that key no longer exists; always go through this."""
    user = user or current_user()
    if not user:
        return []
    return fetch_user_guilds(str(user["id"]), user.get("access_token", ""))


def user_is_admin_of(guild_id: int) -> bool:
    """True if the logged-in user has Administrator permission on this guild — the website
    Settings page is the only way to configure Zexo now, so this is the sole permission gate
    for it."""
    user = current_user()
    if not user:
        return False
    for g in user_guilds(user):
        if int(g["id"]) == guild_id:
            try:
                return (int(g["permissions"]) & ADMINISTRATOR_BIT) != 0
            except (ValueError, TypeError):
                return False
    return False



@app.route('/')
def home():
    return """
    <!DOCTYPE html><html><head><meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Zexo — by Void HQ</title>
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;500;600;700;800;900&display=swap" rel="stylesheet">
    <style>
      * { box-sizing:border-box; }
      html { scroll-behavior:smooth; }
      body { margin:0; background:#07070d; font-family:'Poppins',Arial,sans-serif; color:#f4f4f8;
             position:relative; overflow-x:hidden; cursor:none; }
      a, button { cursor:none; }
      @media (hover:none) { body, a, button { cursor:auto; } #cursor-glow { display:none; } }

      #particles { position:fixed; inset:0; z-index:0; opacity:0.55; }

      #cursor-glow { position:fixed; top:0; left:0; width:26px; height:26px; border-radius:50%;
                     background:radial-gradient(circle, rgba(139,92,246,0.9), rgba(245,158,11,0.4) 60%, transparent 75%);
                     pointer-events:none; z-index:9999; mix-blend-mode:screen; filter:blur(1px);
                     transform:translate(-50%,-50%); transition:width 0.2s ease, height 0.2s ease, opacity 0.2s ease; }
      #cursor-glow.big { width:52px; height:52px; }

      .orb { position:fixed; border-radius:50%; filter:blur(100px); opacity:0.4; z-index:0; animation:float 14s ease-in-out infinite; }
      .orb1 { width:420px; height:420px; background:#8b5cf6; top:-120px; left:-100px; }
      .orb2 { width:380px; height:380px; background:#f59e0b; bottom:20%; right:-120px; animation-delay:3s; }
      .orb3 { width:280px; height:280px; background:#22d3ee; top:55%; left:60%; animation-delay:6s; }
      @keyframes float { 0%,100%{ transform:translate(0,0) scale(1); } 50%{ transform:translate(30px,-30px) scale(1.08); } }

      /* --- entrance / preloader --- */
      #preloader { position:fixed; inset:0; z-index:999; background:#07070d; display:flex; align-items:center;
                   justify-content:center; transition:opacity 0.6s ease, visibility 0.6s ease; }
      #preloader.hide { opacity:0; visibility:hidden; }
      #preloader .mark { font-size:2rem; font-weight:900; letter-spacing:0.15em;
                          background:linear-gradient(90deg,#8b5cf6,#f59e0b,#22d3ee); background-size:200% auto;
                          -webkit-background-clip:text; background-clip:text; color:transparent; animation:shine 2s linear infinite;
                          opacity:0; animation:fadeInScale 1.1s ease forwards, shine 2s linear infinite 1.1s; }
      @keyframes fadeInScale { 0%{ opacity:0; transform:scale(0.85); } 100%{ opacity:1; transform:scale(1); } }

      nav { position:sticky; top:0; z-index:10; display:flex; align-items:center; justify-content:space-between;
            padding:16px 26px; background:rgba(7,7,13,0.75); backdrop-filter:blur(14px); border-bottom:1px solid rgba(255,255,255,0.06);
            opacity:0; transform:translateY(-14px); animation:navIn 0.8s ease 0.3s forwards; }
      @keyframes navIn { to { opacity:1; transform:translateY(0); } }
      nav .brand { font-weight:800; font-size:1.2rem; }
      nav .nav-btns { display:flex; gap:10px; }
      nav a.cta { display:inline-block; padding:9px 20px; border-radius:999px;
          background:linear-gradient(90deg,#8b5cf6,#f59e0b); color:#fff; text-decoration:none; font-weight:600; font-size:0.85rem;
          transition:transform 0.2s ease, box-shadow 0.2s ease; }
      nav a.cta:hover { transform:translateY(-2px); box-shadow:0 8px 24px rgba(139,92,246,0.45); }
      nav a.invite { display:inline-block; padding:9px 20px; border-radius:999px; background:rgba(255,255,255,0.06);
          border:1px solid rgba(255,255,255,0.14); color:#f4f4f8; text-decoration:none; font-weight:600; font-size:0.85rem;
          transition:background 0.2s ease; }
      nav a.invite:hover { background:rgba(255,255,255,0.12); }

      .hero { min-height:88vh; display:flex; flex-direction:column; align-items:center; justify-content:center;
              text-align:center; padding:60px 20px; position:relative; z-index:1; }
      .badge { display:inline-flex; align-items:center; gap:8px; padding:6px 16px; border-radius:999px; background:rgba(255,255,255,0.06);
               border:1px solid rgba(255,255,255,0.12); font-size:0.8rem; color:#9a9ab0; margin-bottom:18px;
               opacity:0; transform:translateY(16px); animation:riseIn 0.8s ease 0.4s forwards; }
      .dot { width:8px; height:8px; border-radius:50%; background:#22c55e; box-shadow:0 0 10px #22c55e; animation:pulse 1.6s infinite; }
      @keyframes pulse { 0%,100%{ opacity:1; } 50%{ opacity:0.35; } }
      @keyframes riseIn { to { opacity:1; transform:translateY(0); } }
      h1 { font-size:3.2rem; font-weight:900; margin:0; letter-spacing:-0.02em; line-height:1.05;
           background:linear-gradient(90deg,#8b5cf6,#f59e0b,#22d3ee); background-size:200% auto;
           -webkit-background-clip:text; background-clip:text; color:transparent;
           opacity:0; transform:translateY(24px) scale(0.96); animation:riseInBig 1s cubic-bezier(.2,.8,.2,1) 0.55s forwards, shine 4s linear infinite 1.55s;
           position:relative; }
      @keyframes riseInBig { to { opacity:1; transform:translateY(0) scale(1); } }
      @keyframes shine { to { background-position:200% center; } }

      /* --- glitch title: two color-split ghost layers that snap-offset briefly --- */
      #glitch-title::before, #glitch-title::after {
        content: attr(data-text); position:absolute; top:0; left:0; width:100%; height:100%;
        background:inherit; -webkit-background-clip:text; background-clip:text; color:transparent;
        opacity:0; pointer-events:none;
      }
      #glitch-title::before { text-shadow:2px 0 #ff2bd6; }
      #glitch-title::after { text-shadow:-2px 0 #22d3ee; }
      #glitch-title.glitching::before { opacity:0.8; animation:glitchShift 0.28s steps(2) both; }
      #glitch-title.glitching::after { opacity:0.8; animation:glitchShift 0.28s steps(2) both reverse; }
      @keyframes glitchShift {
        0% { clip-path: inset(10% 0 70% 0); transform:translate(-3px,0); }
        20% { clip-path: inset(60% 0 5% 0); transform:translate(3px,0); }
        40% { clip-path: inset(20% 0 55% 0); transform:translate(-2px,0); }
        60% { clip-path: inset(75% 0 2% 0); transform:translate(2px,0); }
        80% { clip-path: inset(5% 0 80% 0); transform:translate(-3px,0); }
        100% { clip-path: inset(40% 0 40% 0); transform:translate(0,0); }
      }

      p.tag { color:#9a9ab0; margin:16px 0 6px; max-width:560px; font-size:1.05rem; line-height:1.5;
              opacity:0; transform:translateY(18px); animation:riseIn 0.9s ease 0.85s forwards; }
      p.credit { color:#6b6b80; font-size:0.85rem; margin:0 0 26px;
                 opacity:0; transform:translateY(14px); animation:riseIn 0.9s ease 1.05s forwards; }
      p.credit .void { color:#c4b5fd; font-weight:700; }
      p.credit .owner { color:#fcd34d; font-weight:600; }
      .btn-row { display:flex; gap:14px; flex-wrap:wrap; justify-content:center;
                 opacity:0; transform:translateY(18px); animation:riseIn 0.9s ease 1.2s forwards; }
      a.primary { display:inline-block; padding:14px 32px; border-radius:999px;
          background:linear-gradient(90deg,#8b5cf6,#f59e0b); color:#fff; text-decoration:none; font-weight:600;
          box-shadow:0 8px 30px rgba(139,92,246,0.4); transition:transform 0.2s ease, box-shadow 0.2s ease; }
      a.primary:hover { transform:translateY(-3px) scale(1.03); box-shadow:0 12px 40px rgba(139,92,246,0.6); }
      a.secondary { display:inline-block; padding:14px 32px; border-radius:999px; background:rgba(255,255,255,0.06);
          border:1px solid rgba(255,255,255,0.14); color:#f4f4f8; text-decoration:none; font-weight:600; transition:background 0.2s ease; }
      a.secondary:hover { background:rgba(255,255,255,0.12); }
      .scroll-hint { position:absolute; bottom:30px; color:#6b6b80; font-size:0.8rem; animation:bounce 2s infinite, fadeIn 1s ease 1.6s both; }
      @keyframes bounce { 0%,100%{ transform:translateY(0); } 50%{ transform:translateY(8px); } }
      @keyframes fadeIn { from{ opacity:0; } to{ opacity:1; } }

      section { max-width:1080px; margin:0 auto; padding:70px 20px; position:relative; z-index:1; }
      section h2 { text-align:center; font-size:2rem; font-weight:800; margin-bottom:8px; }
      section .sub { text-align:center; color:#9a9ab0; margin-bottom:44px; font-size:1rem; }

      /* --- scroll reveal: fades in AND fades back out as it leaves the viewport, with a blur resolve --- */
      .reveal { opacity:0; transform:translateY(38px) scale(0.96); filter:blur(6px);
                transition:opacity 0.7s cubic-bezier(.2,.8,.2,1), transform 0.7s cubic-bezier(.2,.8,.2,1), filter 0.7s ease; }
      .reveal.in { opacity:1; transform:translateY(0) scale(1); filter:blur(0); }
      .reveal.out-up { opacity:0; transform:translateY(-38px) scale(0.97); filter:blur(4px); }

      /* --- whole-page fade/slide transition when navigating away --- */
      body.page-leaving { animation:pageLeave 0.45s cubic-bezier(.6,0,.9,.2) forwards; }
      @keyframes pageLeave { to { opacity:0; transform:scale(0.97) translateY(-10px); filter:blur(4px); } }
      body { transform-origin:center top; }

      .grid { display:grid; grid-template-columns:repeat(auto-fit, minmax(240px, 1fr)); gap:20px; perspective:900px; }
      .card { background:rgba(20,20,31,0.6); border:1px solid rgba(255,255,255,0.08); border-radius:18px;
              padding:26px; backdrop-filter:blur(12px); transition:transform 0.12s ease-out, border-color 0.25s ease, opacity 0.6s ease;
              transform-style:preserve-3d; will-change:transform; }
      .card:hover { border-color:rgba(139,92,246,0.5); }
      .card .icon { font-size:1.8rem; margin-bottom:12px; }
      .icon-node { position:relative; width:56px; height:56px; border-radius:50%; display:flex; align-items:center;
                   justify-content:center; font-size:1.5rem; margin-bottom:14px;
                   background:radial-gradient(circle, rgba(139,92,246,0.16), transparent 72%); }
      .icon-node::before { content:''; position:absolute; inset:0; border-radius:50%;
                   border:1px solid rgba(139,92,246,0.4); }
      .icon-node::after { content:''; position:absolute; inset:-7px; border-radius:50%;
                   border:1px solid rgba(139,92,246,0.14); }
      .card:hover .icon-node { box-shadow:0 0 22px rgba(139,92,246,0.45); }
      .card:hover .icon-node::before { border-color:rgba(245,158,11,0.55); }
      .card h3 { margin:0 0 8px; font-size:1.05rem; }
      .card p { margin:0; color:#9a9ab0; font-size:0.88rem; line-height:1.55; }

      .steps { display:flex; flex-direction:column; gap:18px; max-width:640px; margin:0 auto; }
      .step { display:flex; gap:16px; align-items:flex-start; }
      .step .num { flex-shrink:0; width:36px; height:36px; border-radius:50%; background:linear-gradient(135deg,#8b5cf6,#f59e0b);
                   display:flex; align-items:center; justify-content:center; font-weight:700; font-size:0.9rem; }
      .step .txt h4 { margin:0 0 4px; font-size:0.98rem; }
      .step .txt p { margin:0; color:#9a9ab0; font-size:0.85rem; }

      .owner-band { display:flex; align-items:center; gap:16px; background:rgba(20,20,31,0.6);
                    border:1px solid rgba(255,255,255,0.08); border-radius:20px; padding:22px 26px; backdrop-filter:blur(12px); }
      .owner-band .crown { font-size:2rem; flex-shrink:0; }
      .owner-band h3 { margin:0 0 4px; font-size:1.05rem; }
      .owner-band p { margin:0; color:#9a9ab0; font-size:0.88rem; line-height:1.5; }
      .owner-band b.void { color:#c4b5fd; }
      .owner-band b.owner { color:#fcd34d; }

      .cta-band { text-align:center; background:linear-gradient(135deg, rgba(139,92,246,0.16), rgba(245,158,11,0.10));
                  border:1px solid rgba(255,255,255,0.08); border-radius:24px; padding:50px 26px; }
      .cta-band h2 { margin-bottom:14px; }

      footer { text-align:center; padding:36px 20px 46px; color:#6b6b80; font-size:0.85rem; position:relative; z-index:1; }
      footer .void { color:#c4b5fd; font-weight:600; }
      footer .owner { color:#fcd34d; font-weight:600; }

      /* ---------- team / staff carousel ---------- */
      .cyber-staff{ position:relative; width:100%; height:560px; border-radius:20px; overflow:hidden;
        border:1px solid rgba(255,255,255,0.08); background:#04050a; }
      #staff-canvas{ position:absolute; inset:0; width:100%; height:100%; display:block; }
      .cyber-overlay{ position:absolute; inset:0; z-index:2; pointer-events:none;
        display:flex; flex-direction:column; justify-content:flex-end; align-items:flex-end;
        padding:clamp(16px,3vw,28px); gap:12px; }
      .cyber-hint{ font-family:monospace; font-size:0.7rem; letter-spacing:0.12em; color:#9a9ab0; opacity:0.8; }
      .cyber-controls{ pointer-events:auto; display:flex; gap:10px; }
      .cyber-controls button{ padding:10px 20px; font-size:0.8rem; font-weight:600; cursor:pointer;
        background:rgba(255,255,255,0.06); border:1px solid rgba(255,255,255,0.14); color:#f4f4f8;
        border-radius:999px; transition:background 0.2s ease; font-family:'Poppins',Arial,sans-serif; }
      .cyber-controls button:hover{ background:rgba(255,255,255,0.12); }
      @media (max-width:640px){ .cyber-staff{ height:460px; } }
    </style></head>
    <body>
      <canvas id="particles"></canvas>
      <div id="cursor-glow"></div>
      <div id="preloader"><span class="mark">⚡ ZEXO</span></div>
      <div class="orb orb1"></div><div class="orb orb2"></div><div class="orb orb3"></div>

      <nav>
        <span class="brand">⚡ ZEXO</span>
        <div class="nav-btns">
          <a class="invite" href="/commands">Commands</a>
          <a class="invite" href="#staff">Team</a>
          <a class="invite" href="__INVITE_URL__" target="_blank">Join Void HQ ↗</a>
          <a class="cta" href="/dashboard">Dashboard →</a>
        </div>
      </nav>

      <div class="hero">
        <div class="badge"><span class="dot"></span> Online &amp; voting daily</div>
        <h1 id="glitch-title" data-text="⚡ ZEXO">⚡ ZEXO</h1>
        <p class="tag">The Top Edit voting system your server actually needs. Submissions, live polls,
          points, ranks, and a full web dashboard — all automatic, all customizable.</p>
        <p class="credit">Built by <span class="void">Zexo</span> for <span class="void">Void HQ</span> · Server owner: <span class="owner">you</span></p>
        <div class="btn-row">
          <a class="primary" href="/dashboard">Open Dashboard →</a>
          <a class="secondary" href="__INVITE_URL__" target="_blank">Join Void HQ ↗</a>
          <a class="secondary" href="#features">See what it does ↓</a>
        </div>
        <div class="scroll-hint">scroll for more ↓</div>
      </div>

      <section id="features">
        <h2 class="reveal">Everything the bot does</h2>
        <div class="sub reveal">One system, fully automated, every single day.</div>
        <div class="grid">
          <div class="card reveal"><div class="icon-node">🎬</div><h3>Any video source</h3>
            <p>YouTube, TikTok, Instagram, Streamable, forwards, replies — anything gets picked up and converted into a real playable clip.</p></div>
          <div class="card reveal"><div class="icon-node">🗳️</div><h3>Daily live polls</h3>
            <p>Every submission that pings the Picker role goes into a real Discord poll, automatically — no cap on how many edits per day.</p></div>
          <div class="card reveal"><div class="icon-node">🏆</div><h3>Points &amp; ranks</h3>
            <p>Winners earn points automatically, rank roles sync themselves, and the leaderboard updates in real time.</p></div>
          <div class="card reveal"><div class="icon-node">⚙️</div><h3>Full web dashboard</h3>
            <p>Log in with Discord and manage everything from your browser — no memorizing slash commands.</p></div>
          <div class="card reveal"><div class="icon-node">✍️</div><h3>100% customizable text</h3>
            <p>Winner announcements, reminders, poll questions, and every timing — write your own, down to the last detail.</p></div>
          <div class="card reveal"><div class="icon-node">🚫</div><h3>Badword filtering</h3>
            <p>Keep the server clean automatically, editable live from the dashboard, no restart needed.</p></div>
        </div>
      </section>

      <section>
        <h2 class="reveal">How it works</h2>
        <div class="sub reveal">Set up once, runs itself every day after that.</div>
        <div class="steps">
          <div class="step reveal"><div class="num">1</div><div class="txt">
            <h4>Post your edit</h4><p>Drop your video in the submissions channel and ping the Picker role.</p></div></div>
          <div class="step reveal"><div class="num">2</div><div class="txt">
            <h4>Zexo collects it</h4><p>At collect time, every valid submission gets pulled together and posted for voting.</p></div></div>
          <div class="step reveal"><div class="num">3</div><div class="txt">
            <h4>The server votes</h4><p>A real Discord poll runs for hours — everyone gets a say in who wins.</p></div></div>
          <div class="step reveal"><div class="num">4</div><div class="txt">
            <h4>Winner gets crowned</h4><p>Points, a custom announcement, and a spot on the leaderboard — fully automatic.</p></div></div>
        </div>
      </section>

      <section id="staff">
        <h2 class="reveal">Who's actually running this.</h2>
        <div class="sub reveal">The people behind Top Edit and everything Zexo automates for it.</div>
        <div class="cyber-staff">
          <canvas id="staff-canvas"></canvas>
          <div class="cyber-overlay">
            <span class="cyber-hint">[ SCROLL / DRAG TO ROTATE ]</span>
            <div class="cyber-controls">
              <button id="cyberPrev">&larr; Prev</button>
              <button id="cyberNext">Next &rarr;</button>
            </div>
          </div>
        </div>
      </section>

      <section>
        <div class="owner-band reveal">
          <div class="crown">👑</div>
          <div>
            <h3>Made for <b class="void">Void HQ</b></h3>
            <p>Zexo was built by <b class="void">Zexo</b> specifically for the Void HQ community. Every setting on the
              dashboard — channels, roles, timings, and every piece of text the bot sends — is fully in the hands of
              the server <b class="owner">owner</b>.</p>
          </div>
        </div>
      </section>

      <section>
        <div class="cta-band reveal">
          <h2>Ready to see it live?</h2>
          <p style="color:#9a9ab0; margin-bottom:24px;">Check the leaderboard, today's vote, and full server config in one place.</p>
          <a class="primary" href="/dashboard">Open Dashboard →</a>
        </div>
      </section>

      <footer>
        Built by <span class="void">Zexo</span> for <span class="void">Void HQ</span> · Owner-managed via the <span class="owner">full dashboard</span>.
      </footer>

      <script>
        window.addEventListener('load', () => {
          setTimeout(() => document.getElementById('preloader').classList.add('hide'), 500);
        });
        const revealEls = document.querySelectorAll('.reveal');
        const io = new IntersectionObserver((entries) => {
          entries.forEach(entry => {
            const el = entry.target;
            if (entry.isIntersecting) {
              el.classList.remove('out-up');
              el.classList.add('in');
            } else {
              // fade back out only if it left ABOVE the viewport, so first-load elements
              // below the fold don't flicker before the user ever scrolls to them
              const rect = entry.boundingClientRect;
              if (rect.top < 0) { el.classList.remove('in'); el.classList.add('out-up'); }
            }
          });
        }, { threshold: 0.15 });
        revealEls.forEach(el => io.observe(el));

        // --- particle network background ---
        const canvas = document.getElementById('particles');
        const ctx = canvas.getContext('2d');
        let W, H, particles;
        const COUNT = window.innerWidth < 700 ? 34 : 70;
        function resize() {
          W = canvas.width = window.innerWidth;
          H = canvas.height = window.innerHeight;
        }
        function initParticles() {
          particles = Array.from({ length: COUNT }, () => ({
            x: Math.random() * W, y: Math.random() * H,
            vx: (Math.random() - 0.5) * 0.4, vy: (Math.random() - 0.5) * 0.4,
            r: Math.random() * 1.6 + 0.6,
          }));
        }
        resize(); initParticles();
        window.addEventListener('resize', () => { resize(); initParticles(); });

        const mouse = { x: -9999, y: -9999 };
        function drawParticles() {
          ctx.clearRect(0, 0, W, H);
          for (const p of particles) {
            p.x += p.vx; p.y += p.vy;
            if (p.x < 0 || p.x > W) p.vx *= -1;
            if (p.y < 0 || p.y > H) p.vy *= -1;
            const dx = p.x - mouse.x, dy = p.y - mouse.y;
            const distToMouse = Math.sqrt(dx * dx + dy * dy);
            if (distToMouse < 140) { p.x += dx / distToMouse * 0.6; p.y += dy / distToMouse * 0.6; }
          }
          for (let i = 0; i < particles.length; i++) {
            for (let j = i + 1; j < particles.length; j++) {
              const a = particles[i], b = particles[j];
              const d = Math.hypot(a.x - b.x, a.y - b.y);
              if (d < 130) {
                ctx.strokeStyle = `rgba(139,92,246,${0.22 * (1 - d / 130)})`;
                ctx.lineWidth = 1;
                ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
              }
            }
          }
          for (const p of particles) {
            ctx.beginPath(); ctx.arc(p.x, p.y, p.r, 0, Math.PI * 2);
            ctx.fillStyle = 'rgba(196,181,253,0.85)'; ctx.fill();
          }
          requestAnimationFrame(drawParticles);
        }
        drawParticles();

        // --- cursor glow (desktop / mouse only) ---
        const glow = document.getElementById('cursor-glow');
        window.addEventListener('mousemove', (e) => {
          mouse.x = e.clientX; mouse.y = e.clientY;
          glow.style.left = e.clientX + 'px';
          glow.style.top = e.clientY + 'px';
        });
        document.querySelectorAll('a, button').forEach(el => {
          el.addEventListener('mouseenter', () => glow.classList.add('big'));
          el.addEventListener('mouseleave', () => glow.classList.remove('big'));
        });
        window.addEventListener('mouseleave', () => { mouse.x = -9999; mouse.y = -9999; });

        // --- glitch title, fires briefly every few seconds ---
        const glitchTitle = document.getElementById('glitch-title');
        function fireGlitch() {
          glitchTitle.classList.add('glitching');
          setTimeout(() => glitchTitle.classList.remove('glitching'), 280);
        }
        setInterval(fireGlitch, 3400);
        glitchTitle.addEventListener('mouseenter', fireGlitch);

        // --- magnetic 3D tilt on feature cards ---
        document.querySelectorAll('.card').forEach(card => {
          card.addEventListener('mousemove', (e) => {
            const rect = card.getBoundingClientRect();
            const px = (e.clientX - rect.left) / rect.width - 0.5;
            const py = (e.clientY - rect.top) / rect.height - 0.5;
            card.style.transform = `translateY(-6px) rotateX(${py * -8}deg) rotateY(${px * 10}deg)`;
          });
          card.addEventListener('mouseleave', () => { card.style.transform = ''; });
        });
        // --- fade/slide-out page transition on internal navigation ---
        document.querySelectorAll('a[href]').forEach(link => {
          const href = link.getAttribute('href');
          if (!href || href.startsWith('#') || link.target === '_blank') return;
          link.addEventListener('click', (e) => {
            e.preventDefault();
            document.body.classList.add('page-leaving');
            setTimeout(() => { window.location.href = href; }, 380);
          });
        });

      </script>

      <script src="https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js"></script>
      <script>
  (function(){
    const team = [
      { name: "Zexo", role: "Owner", age: 17, country: "Turkey", hobbies: ["Sport", "Editing"], img: "data:image/jpeg;base64,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", color: "#00ffff", bg: "#0d2b45" },
      { name: "Mayto", role: "Owner", age: 16, country: "Syria", hobbies: ["Gaming", "Editing"], img: "data:image/jpeg;base64,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", color: "#9d4edd", bg: "#240046" },
      { name: "Arya", role: "Co-Founder", age: 18, country: "India", hobbies: ["Editing", "Coding"], img: "data:image/jpeg;base64,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", color: "#ff0055", bg: "#4a001f" },
      { name: "Prizm Aultrim", role: "Co-Founder", age: 15, country: "India", hobbies: ["Editing", "Sport"], img: "data:image/jpeg;base64,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", color: "#00ff88", bg: "#003820" },
      { name: "Specter", role: "Chief Admin", age: 14, country: "India", hobbies: ["Gaming"], img: "data:image/png;base64,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", color: "#0088ff", bg: "#002b5c" }
    ];

    let currentIndex = 0;
    const container = document.querySelector('.cyber-staff');
    const canvas = document.getElementById('staff-canvas');
    const scene = new THREE.Scene();
    const camera = new THREE.PerspectiveCamera(50, container.clientWidth / container.clientHeight, 0.1, 100);
    camera.position.z = 6.6;

    const renderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: true });
    renderer.setSize(container.clientWidth, container.clientHeight);
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));

    // Draw an image into a box, cropping to fill it (object-fit: cover) so
    // portraits never get squashed/stretched regardless of their real ratio.
    function drawImageCover(ctx, img, x, y, w, h) {
      const scale = Math.max(w / img.width, h / img.height);
      const sw = w / scale, sh = h / scale;
      const sx = (img.width - sw) / 2, sy = (img.height - sh) / 2;
      ctx.drawImage(img, sx, sy, sw, sh, x, y, w, h);
    }

    function loadImage(src) {
      return new Promise((resolve) => {
        const img = new Image();
        img.onload = () => resolve(img);
        img.onerror = () => resolve(null); // fall back gracefully if a photo is missing
        img.src = src;
      });
    }

    // Particle field
    const particleCount = 20000;
    const pGeo = new THREE.BufferGeometry();
    const pPos = new Float32Array(particleCount * 3);
    const pCol = new Float32Array(particleCount * 3);

    for (let i = 0; i < particleCount * 3; i += 3) {
      const radius = 2.0 + Math.random() * 3.5;
      const theta = Math.random() * Math.PI * 2;
      const phi = Math.acos((Math.random() * 2) - 1);

      pPos[i] = radius * Math.sin(phi) * Math.cos(theta);
      pPos[i + 1] = radius * Math.sin(phi) * Math.sin(theta);
      pPos[i + 2] = radius * Math.cos(phi);

      const color = new THREE.Color(Math.random() > 0.5 ? 0x00ffff : (Math.random() > 0.5 ? 0xff0055 : 0x9d4edd));
      pCol[i] = color.r;
      pCol[i + 1] = color.g;
      pCol[i + 2] = color.b;
    }
    pGeo.setAttribute('position', new THREE.BufferAttribute(pPos, 3));
    pGeo.setAttribute('color', new THREE.BufferAttribute(pCol, 3));

    const pMat = new THREE.PointsMaterial({
      size: 0.018,
      vertexColors: true,
      blending: THREE.AdditiveBlending,
      transparent: true,
      opacity: 0.75
    });
    const particles = new THREE.Points(pGeo, pMat);
    scene.add(particles);

    // 3D member cards with canvas texture
    const cardGroup = new THREE.Group();
    scene.add(cardGroup);

    function drawRoleBadge(ctx, member, badgeX, badgeY, badgeW, badgeH, alpha) {
      const r = 8;
      ctx.globalAlpha = alpha;
      ctx.beginPath();
      ctx.moveTo(badgeX + r, badgeY);
      ctx.arcTo(badgeX + badgeW, badgeY, badgeX + badgeW, badgeY + badgeH, r);
      ctx.arcTo(badgeX + badgeW, badgeY + badgeH, badgeX, badgeY + badgeH, r);
      ctx.arcTo(badgeX, badgeY + badgeH, badgeX, badgeY, r);
      ctx.arcTo(badgeX, badgeY, badgeX + badgeW, badgeY, r);
      ctx.closePath();
      ctx.fillStyle = member.color + '26';
      ctx.fill();
      ctx.strokeStyle = member.color;
      ctx.lineWidth = 1.5;
      ctx.stroke();
      ctx.fillStyle = member.color;
      ctx.textAlign = 'left';
      ctx.textBaseline = 'middle';
      ctx.font = '600 20px monospace';
      ctx.fillText(member.role.toUpperCase(), badgeX + 16, badgeY + badgeH / 2 + 1);
      ctx.textBaseline = 'alphabetic';
      ctx.globalAlpha = 1;
    }

    function createCardTexture(member, photo) {
      const c = document.createElement('canvas');
      c.width = 512;
      c.height = 680;
      const ctx = c.getContext('2d');

      const grad = ctx.createLinearGradient(0, 0, 512, 680);
      grad.addColorStop(0, member.bg);
      grad.addColorStop(1, '#050508');
      ctx.fillStyle = grad;
      ctx.fillRect(0, 0, 512, 680);

      ctx.strokeStyle = member.color;
      ctx.lineWidth = 12;
      ctx.strokeRect(6, 6, 500, 668);

      ctx.fillStyle = 'rgba(255, 255, 255, 0.04)';
      for (let y = 0; y < 680; y += 40) ctx.fillRect(0, y, 512, 2);

      // Photo box — cover-fit so every portrait fills the frame with no
      // stretching, no matter its native aspect ratio.
      ctx.fillStyle = 'rgba(0, 0, 0, 0.5)';
      ctx.fillRect(40, 40, 432, 460);
      if (photo) {
        drawImageCover(ctx, photo, 40, 40, 432, 460);
      } else {
        ctx.fillStyle = member.color;
        ctx.font = 'bold 22px monospace';
        ctx.textAlign = 'center';
        ctx.fillText('NO SIGNAL', 256, 270);
      }
      ctx.strokeStyle = member.color;
      ctx.lineWidth = 3;
      ctx.strokeRect(40, 40, 432, 460);

      ctx.textAlign = 'left';

      // Role badge geometry — drawn via drawRoleBadge() so it can be
      // redrawn each frame with a pulsing alpha (blink effect).
      ctx.font = '600 20px monospace';
      const roleTextW = ctx.measureText(member.role.toUpperCase()).width;
      const padX = 16, badgeH = 34;
      const badgeW = roleTextW + padX * 2;
      const badgeX = 40, badgeY = 522;
      // Snapshot the clean background under the badge (pad a bit for the glow/stroke)
      // so every frame can restore it before redrawing the badge at a new alpha.
      const badgeSnapshot = ctx.getImageData(badgeX - 4, badgeY - 4, badgeW + 8, badgeH + 8);
      drawRoleBadge(ctx, member, badgeX, badgeY, badgeW, badgeH, 1);

      // Name — bold, with a soft brand-color glow, sitting on a level baseline
      ctx.shadowColor = member.color;
      ctx.shadowBlur = 14;
      ctx.fillStyle = '#ffffff';
      ctx.font = "700 38px 'Chakra Petch', sans-serif";
      ctx.fillText(member.name, 40, 602);
      ctx.shadowBlur = 0;

      ctx.fillStyle = 'rgba(255, 255, 255, 0.7)';
      ctx.font = '17px monospace';
      ctx.fillText(`AGE ${member.age} \u2022 ${member.country.toUpperCase()}`, 40, 630);

      ctx.fillStyle = member.color;
      ctx.font = '16px monospace';
      ctx.fillText(member.hobbies.join(' / ').toUpperCase(), 40, 656);

      const texture = new THREE.CanvasTexture(c);
      return { texture, ctx, badge: { x: badgeX, y: badgeY, w: badgeW, h: badgeH, snapshot: badgeSnapshot } };
    }

    const cards = [];
    const radius = 3.6;
    const angleStep = (Math.PI * 2) / team.length;

    Promise.all(team.map(m => loadImage(m.img))).then((photos) => {
      team.forEach((member, i) => {
        const geo = new THREE.PlaneGeometry(1.15, 1.53);
        const { texture, ctx, badge } = createCardTexture(member, photos[i]);
        const mat = new THREE.MeshBasicMaterial({
          map: texture,
          side: THREE.DoubleSide,
          transparent: true,
          opacity: 0.92
        });

        const mesh = new THREE.Mesh(geo, mat);
        const angle = i * angleStep;
        mesh.position.set(Math.sin(angle) * radius, 0, Math.cos(angle) * radius);
        mesh.rotation.y = angle;
        cardGroup.add(mesh);
        cards.push({ mesh, texture, ctx, badge, member });
      });
    });

    function nextCard() {
      currentIndex = (currentIndex + 1) % team.length;
    }
    function prevCard() {
      currentIndex = (currentIndex - 1 + team.length) % team.length;
    }

    document.getElementById('cyberNext').addEventListener('click', nextCard);
    document.getElementById('cyberPrev').addEventListener('click', prevCard);

    container.addEventListener('wheel', (e) => {
      if (e.deltaY > 30) nextCard();
      else if (e.deltaY < -30) prevCard();
    }, { passive: true });

    // Mouse parallax, scoped to this container only
    let mouseX = 0, mouseY = 0;
    container.addEventListener('mousemove', (e) => {
      const r = container.getBoundingClientRect();
      mouseX = ((e.clientX - r.left) / r.width - 0.5) * 0.8;
      mouseY = -((e.clientY - r.top) / r.height - 0.5) * 0.8;
    });
    container.addEventListener('mouseleave', () => { mouseX = 0; mouseY = 0; });

    window.addEventListener('resize', () => {
      camera.aspect = container.clientWidth / container.clientHeight;
      camera.updateProjectionMatrix();
      renderer.setSize(container.clientWidth, container.clientHeight);
    });

    let targetRotation = 0;
    const clock = new THREE.Clock();

    function animateStaff() {
      requestAnimationFrame(animateStaff);
      const time = clock.getElapsedTime();

      particles.rotation.y = time * 0.04;
      particles.rotation.x = time * 0.02;

      targetRotation = -currentIndex * angleStep;
      cardGroup.rotation.y += (targetRotation + mouseX * 0.3 - cardGroup.rotation.y) * 0.08;
      cardGroup.rotation.x += (0 - cardGroup.rotation.x) * 0.08;

      const blinkAlpha = 0.35 + 0.65 * ((Math.sin(time * 4) + 1) / 2);
      cards.forEach(({ ctx, texture, badge, member }) => {
        ctx.putImageData(badge.snapshot, badge.x - 4, badge.y - 4);
        drawRoleBadge(ctx, member, badge.x, badge.y, badge.w, badge.h, blinkAlpha);
        texture.needsUpdate = true;
      });

      renderer.render(scene, camera);
    }
    animateStaff();
  })();
      </script>
    </body></html>
    """.replace("__INVITE_URL__", VOID_HQ_INVITE_URL)


DASHBOARD_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Zexo Dashboard</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;600;700;800&family=Space+Mono:wght@700&display=swap" rel="stylesheet">
<style>
  :root {
    --bg: #07070d;
    --card: rgba(20,20,31,0.65);
    --border: rgba(255,255,255,0.08);
    --accent: #8b5cf6;
    --accent2: #f59e0b;
    --accent3: #22d3ee;
    --text: #f4f4f8;
    --muted: #9a9ab0;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    font-family: 'Poppins', 'Segoe UI', Arial, sans-serif;
    background: var(--bg);
    color: var(--text);
    padding: 36px 16px 64px;
    position: relative;
    overflow-x: hidden;
  }
  .orb { position: fixed; border-radius: 50%; filter: blur(110px); opacity: 0.4; z-index: -1; animation: float 14s ease-in-out infinite; }
  .orb1 { width: 480px; height: 480px; background: var(--accent); top: -160px; left: -120px; }
  .orb2 { width: 420px; height: 420px; background: var(--accent2); bottom: -160px; right: -100px; animation-delay: 4s; }
  .orb3 { width: 320px; height: 320px; background: var(--accent3); top: 45%; left: 55%; animation-delay: 8s; }
  @keyframes float { 0%,100%{ transform:translate(0,0) scale(1); } 50%{ transform:translate(40px,-40px) scale(1.1); } }

  h1 {
    text-align: center;
    font-size: 2.6rem;
    font-weight: 800;
    letter-spacing: -0.02em;
    margin-bottom: 4px;
    background: linear-gradient(90deg, var(--accent), var(--accent2), var(--accent3));
    background-size: 200% auto;
    -webkit-background-clip: text;
    background-clip: text;
    color: transparent;
    animation: shine 5s linear infinite;
  }
  @keyframes shine { to { background-position: 200% center; } }
  .subtitle { text-align: center; color: var(--muted); margin-bottom: 28px; }

  .status-badge { display: flex; align-items: center; justify-content: center; gap: 8px; margin-bottom: 32px; }
  .status-badge span.pill { display: inline-flex; align-items: center; gap: 8px; padding: 7px 18px; border-radius: 999px;
    background: rgba(255,255,255,0.06); border: 1px solid var(--border); font-size: 0.85rem; color: var(--muted); }
  .status-dot { width: 9px; height: 9px; border-radius: 50%; background: #22c55e; box-shadow: 0 0 10px #22c55e; animation: pulse 1.6s infinite; }
  @keyframes pulse { 0%,100%{ opacity:1; } 50%{ opacity:0.35; } }

  .hero {
    max-width: 1100px; margin: 0 auto 28px; padding: 26px 30px; border-radius: 20px;
    background: linear-gradient(135deg, rgba(139,92,246,0.18), rgba(245,158,11,0.10));
    border: 1px solid var(--border); backdrop-filter: blur(14px);
    display: flex; align-items: center; justify-content: space-between; flex-wrap: wrap; gap: 16px;
    box-shadow: 0 10px 40px rgba(0,0,0,0.35);
  }
  .hero .phase { font-size: 1.05rem; color: var(--muted); margin-bottom: 6px; }
  .hero .phase b { color: var(--text); }
  .countdown { font-family: 'Space Mono', monospace; font-size: 2.4rem; font-weight: 700; letter-spacing: 0.02em;
    background: linear-gradient(90deg, var(--accent3), var(--accent)); -webkit-background-clip: text; background-clip: text; color: transparent; }
  .live-tag { display: inline-flex; align-items: center; gap: 6px; padding: 4px 14px; border-radius: 999px;
    background: rgba(34,197,94,0.15); color: #4ade80; font-weight: 700; font-size: 0.8rem; border: 1px solid rgba(74,222,128,0.35); }
  .entries-tag { color: var(--muted); font-size: 0.9rem; }

  .grid {
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(190px, 1fr));
    gap: 16px;
    max-width: 1100px;
    margin: 0 auto 32px;
  }
  .stat-card {
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 16px;
    padding: 18px 20px;
    backdrop-filter: blur(14px);
    box-shadow: 0 4px 22px rgba(0,0,0,0.35);
    transition: transform 0.2s ease, box-shadow 0.2s ease, border-color 0.2s ease;
  }
  .stat-card:hover { transform: translateY(-4px); border-color: rgba(139,92,246,0.5); box-shadow: 0 10px 30px rgba(139,92,246,0.25); }
  .stat-card .label { color: var(--muted); font-size: 0.75rem; text-transform: uppercase; letter-spacing: 0.06em; }
  .stat-card .value { font-size: 1.7rem; font-weight: 700; margin-top: 6px; }
  .hint { color: var(--muted); font-size: 0.75rem; }

  .section {
    max-width: 1100px;
    margin: 0 auto 28px;
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 18px;
    padding: 22px 26px;
    backdrop-filter: blur(14px);
    box-shadow: 0 4px 22px rgba(0,0,0,0.35);
  }
  .section h2 { margin-top: 0; font-size: 1.25rem; display: flex; align-items: center; gap: 8px; }

  .lb-row {
    display: flex; align-items: center; gap: 14px; padding: 12px 10px; border-radius: 12px;
    border-left: 3px solid var(--tier-color, #444); margin-bottom: 8px; background: rgba(255,255,255,0.02);
    transition: background 0.2s ease, transform 0.15s ease;
  }
  .lb-row:hover { background: rgba(255,255,255,0.05); transform: translateX(4px); }
  .lb-rank { width: 34px; text-align: center; font-weight: 700; font-size: 1.05rem; flex-shrink: 0; }
  .lb-avatar {
    width: 38px; height: 38px; border-radius: 50%; flex-shrink: 0; display: flex; align-items: center; justify-content: center;
    font-weight: 700; font-size: 0.95rem; color: #0b0b12;
    background: var(--tier-color, #666); box-shadow: 0 0 12px color-mix(in srgb, var(--tier-color, #666) 60%, transparent);
  }
  .lb-main { flex: 1; min-width: 0; }
  .lb-name { font-weight: 600; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .lb-bar-track { height: 6px; border-radius: 4px; background: rgba(255,255,255,0.08); margin-top: 6px; overflow: hidden; }
  .lb-bar-fill { height: 100%; border-radius: 4px; background: var(--tier-color, #666); }
  .lb-points { font-family: 'Space Mono', monospace; font-weight: 700; white-space: nowrap; }
  .lb-tier { font-size: 0.72rem; padding: 3px 10px; border-radius: 999px; font-weight: 700; white-space: nowrap;
    background: color-mix(in srgb, var(--tier-color, #666) 25%, transparent); color: var(--tier-color, #ccc); }
  .empty-note { color: var(--muted); text-align: center; padding: 20px 0; }

  .usage-row { display: flex; align-items: center; gap: 12px; margin-bottom: 10px; }
  .usage-name { width: 140px; flex-shrink: 0; font-size: 0.88rem; color: var(--text); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .usage-track { flex: 1; height: 10px; border-radius: 6px; background: rgba(255,255,255,0.06); overflow: hidden; }
  .usage-fill { height: 100%; border-radius: 6px; background: linear-gradient(90deg, var(--accent), var(--accent3)); }
  .usage-count { width: 34px; text-align: right; font-family: 'Space Mono', monospace; font-size: 0.85rem; color: var(--muted); }

  .footer { text-align: center; color: var(--muted); font-size: 0.8rem; margin-top: 36px; }
  .footer .pulse { color: #4ade80; }
</style>
</head>
<body>
  <div class="orb orb1"></div><div class="orb orb2"></div><div class="orb orb3"></div>

  <h1>⚡ Zexo Dashboard</h1>
  <div class="subtitle">Live stats for {{ server_name }}</div>

  <div class="status-badge"><span class="pill"><span class="status-dot"></span> Bot online · auto-refreshing</span></div>
  <div class="status-badge">
    {% if user %}
    <span class="pill">👤 {{ user.username }}
      {% if is_admin %}<a href="/dashboard/{{ guild_id }}/settings" style="color:#4ade80; margin-left:10px;">⚙️ Settings</a>
      <a href="/dashboard/{{ guild_id }}/commands" style="color:#22ffb0; margin-left:10px;">⌁ Control Room</a>
      <a href="/dashboard/{{ guild_id }}/embed-builder" style="color:#c4b5fd; margin-left:10px;">🎨 Embeds</a>{% endif %}
      <a href="/logout" style="color:#f87171; margin-left:10px;">Log out</a>
    </span>
    {% else %}
    <span class="pill"><a href="/login" style="color:#c4b5fd;">🔐 Login with Discord (for settings access)</a></span>
    {% endif %}
  </div>
  <div class="status-badge">
    <span class="pill">
      🔀 <a href="/servers" style="color:#c4b5fd;">All my servers</a>
      {% if other_servers %} · Quick switch:
      {% for s in other_servers %}<a href="/dashboard/{{ s.id }}" style="color:#c4b5fd; margin-left:6px;">{{ s.name }}</a>{% if not loop.last %},{% endif %}{% endfor %}
      {% endif %}
    </span>
  </div>

  <div class="hero">
    <div>
      <div class="phase">
        {% if voting_live %}<span class="live-tag">🔴 LIVE</span>{% endif %}
        <b>{{ phase_label }}</b>
      </div>
      <div class="entries-tag">{{ entries_note }}</div>
    </div>
    <div class="countdown" id="countdown" data-target="{{ countdown_target }}">--:--:--</div>
  </div>

  <div class="grid">
    <div class="stat-card"><div class="label">Members in {{ server_name }}</div><div class="value">👥 {{ member_count }}</div></div>
    <div class="stat-card"><div class="label">Top editor here</div><div class="value">🏆 {{ top_editor.name if top_editor else "—" }}</div></div>
    <div class="stat-card"><div class="label">Current day</div><div class="value">📅 #{{ day_number }}</div></div>
    <div class="stat-card"><div class="label">Uptime</div><div class="value">⏱️ {{ uptime }}</div></div>
    <div class="stat-card"><div class="label">discord.py</div><div class="value">🧩 {{ dpy_version }}</div></div>
  </div>
  <div class="grid" style="margin-top:12px;">
    <div class="stat-card"><div class="label">🌐 Zexo network — servers</div><div class="value">{{ server_count }}</div></div>
    <div class="stat-card"><div class="label">🌐 Zexo network — members</div><div class="value">{{ network_member_count }}</div></div>
  </div>
  <div class="hint" style="margin:10px 2px 0;">💡 The top row is <b>{{ server_name }}</b> only. The 🌐 row is live, real-time totals across every server Zexo is currently in — not fixed to any one server.</div>

  <div class="section">
    <h2>🏆 Leaderboard</h2>
    {% for row in leaderboard %}
    <div class="lb-row" style="--tier-color: {{ row.color }};">
      <div class="lb-rank">{{ row.medal }}</div>
      <div class="lb-avatar">{{ row.initial }}</div>
      <div class="lb-main">
        <div class="lb-name">{{ row.name }}</div>
        <div class="lb-bar-track"><div class="lb-bar-fill" style="width: {{ row.progress }}%;"></div></div>
      </div>
      <span class="lb-tier">{{ row.rank }}</span>
      <div class="lb-points">{{ row.points }} pts</div>
    </div>
    {% else %}
    <div class="empty-note">No points recorded yet. Win a Top Edit to get on the board!</div>
    {% endfor %}
  </div>

  <div class="section">
    <h2>🎬 Command usage since last restart</h2>
    {% for row in usage %}
    <div class="usage-row">
      <div class="usage-name">/{{ row.name }}</div>
      <div class="usage-track"><div class="usage-fill" style="width: {{ row.pct }}%;"></div></div>
      <div class="usage-count">{{ row.count }}</div>
    </div>
    {% else %}
    <div class="empty-note">No commands used yet.</div>
    {% endfor %}
  </div>

  <div class="footer">Zexo by Void HQ · <span class="pulse">●</span> auto-refreshing every 30s</div>
  <script>
    setTimeout(() => location.reload(), 30000);
    const el = document.getElementById('countdown');
    const target = new Date(el.dataset.target).getTime();
    function tick() {
      const diff = Math.max(0, target - Date.now());
      const h = Math.floor(diff / 3600000);
      const m = Math.floor((diff % 3600000) / 60000);
      const s = Math.floor((diff % 60000) / 1000);
      el.textContent = String(h).padStart(2,'0') + ':' + String(m).padStart(2,'0') + ':' + String(s).padStart(2,'0');
    }
    tick();
    setInterval(tick, 1000);
  </script>
</body>
</html>
"""


MY_SERVERS_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Your Servers — Zexo</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;600;700;800&family=Space+Mono:wght@700&display=swap" rel="stylesheet">
<style>
  * { box-sizing:border-box; }
  body { margin:0; font-family:'Poppins',Arial,sans-serif; background:#07070d; color:#f4f4f8; padding:36px 16px 64px;
         position:relative; overflow-x:hidden; }
  .orb { position:fixed; border-radius:50%; filter:blur(110px); opacity:0.4; z-index:-1; animation:float 14s ease-in-out infinite; }
  .orb1 { width:420px; height:420px; background:#8b5cf6; top:-140px; left:-100px; }
  .orb2 { width:380px; height:380px; background:#f59e0b; bottom:-140px; right:-100px; animation-delay:4s; }
  .orb3 { width:280px; height:280px; background:#22d3ee; top:50%; right:60%; animation-delay:7s; }
  @keyframes float { 0%,100%{ transform:translate(0,0) scale(1); } 50%{ transform:translate(30px,-30px) scale(1.08); } }
  .wrap { max-width:680px; margin:0 auto; }

  .top { display:flex; align-items:center; justify-content:space-between; margin-bottom:6px;
         opacity:0; transform:translateY(-10px); animation:fadeDown 0.6s ease forwards; }
  @keyframes fadeDown { to { opacity:1; transform:translateY(0); } }
  h1 { font-size:2rem; font-weight:800; margin:0; background:linear-gradient(90deg,#8b5cf6,#f59e0b,#22d3ee);
       background-size:200% auto; -webkit-background-clip:text; background-clip:text; color:transparent;
       animation:shine 5s linear infinite; }
  @keyframes shine { to { background-position:200% center; } }
  .sub { color:#9a9ab0; font-size:0.88rem; }
  .logout { color:#f87171; text-decoration:none; font-size:0.85rem; }

  .search-wrap { position:relative; margin:22px 0 18px;
                 opacity:0; transform:translateY(14px); animation:riseIn 0.6s ease 0.15s forwards; }
  @keyframes riseIn { to { opacity:1; transform:translateY(0); } }
  .search-wrap .icn { position:absolute; left:16px; top:50%; transform:translateY(-50%); opacity:0.5; font-size:1.05rem; }
  #search { width:100%; padding:13px 16px 13px 44px; border-radius:14px; background:rgba(20,20,31,0.65);
            border:1px solid rgba(255,255,255,0.1); color:#f4f4f8; font-family:inherit; font-size:0.95rem;
            backdrop-filter:blur(14px); }
  #search:focus { outline:none; border-color:rgba(139,92,246,0.6); box-shadow:0 0 0 3px rgba(139,92,246,0.15); }

  .stat-row { display:flex; gap:10px; flex-wrap:wrap; margin-bottom:24px;
              opacity:0; transform:translateY(14px); animation:riseIn 0.6s ease 0.3s forwards; }
  .stat-pill { display:flex; align-items:center; gap:7px; padding:8px 16px; border-radius:999px; font-size:0.82rem; font-weight:600;
               background:rgba(255,255,255,0.05); border:1px solid rgba(255,255,255,0.1); }
  .stat-pill b { font-family:'Space Mono', monospace; }
  .stat-pill.total b { color:#c4b5fd; }
  .stat-pill.active { color:#4ade80; } .stat-pill.active b { color:#4ade80; }
  .stat-pill.missing { color:#f87171; } .stat-pill.missing b { color:#f87171; }
  .stat-dot { width:7px; height:7px; border-radius:50%; }
  .stat-pill.active .stat-dot { background:#4ade80; box-shadow:0 0 8px #4ade80; animation:pulse 1.6s infinite; }
  .stat-pill.missing .stat-dot { background:#f87171; }
  @keyframes pulse { 0%,100%{ opacity:1; } 50%{ opacity:0.35; } }

  .card { display:flex; align-items:center; justify-content:space-between; gap:14px;
          background:rgba(20,20,31,0.65); border:1px solid rgba(255,255,255,0.08); border-radius:18px;
          padding:16px 18px; margin-bottom:14px; backdrop-filter:blur(14px);
          transition:transform 0.22s ease, border-color 0.22s ease, box-shadow 0.22s ease;
          opacity:0; transform:translateY(20px); animation:cardIn 0.5s ease forwards; }
  .card:hover { transform:translateY(-4px); border-color:rgba(139,92,246,0.45); box-shadow:0 10px 30px rgba(139,92,246,0.2); }
  @keyframes cardIn { to { opacity:1; transform:translateY(0); } }
  .card-left { display:flex; align-items:center; gap:14px; min-width:0; }

  /* --- glowing circular icon ring, TicketKing-style hub node --- */
  .icon-ring { position:relative; width:52px; height:52px; flex-shrink:0; border-radius:50%;
               display:flex; align-items:center; justify-content:center;
               background:radial-gradient(circle, rgba(139,92,246,0.18), transparent 70%); }
  .icon-ring::before { content:''; position:absolute; inset:0; border-radius:50%; border:1px solid rgba(139,92,246,0.35); }
  .icon-ring.missing::before { border-color:rgba(248,113,113,0.35); }
  .icon-ring img, .icon-ring .fallback { width:42px; height:42px; border-radius:50%; object-fit:cover;
        box-shadow:0 0 14px rgba(139,92,246,0.35); }
  .icon-ring .fallback { display:flex; align-items:center; justify-content:center; font-weight:800; font-size:1rem;
        background:linear-gradient(135deg,#8b5cf6,#f59e0b); color:#0b0b12; }
  .icon-ring.active::after { content:''; position:absolute; bottom:1px; right:1px; width:13px; height:13px; border-radius:50%;
        background:#4ade80; border:2px solid #07070d; box-shadow:0 0 8px #4ade80; }

  .name-block { min-width:0; }
  .name { font-weight:700; font-size:1rem; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; max-width:220px; }
  .tag { display:inline-block; margin-top:4px; font-size:0.7rem; padding:3px 10px; border-radius:999px; }
  .tag.admin { background:rgba(74,222,128,0.15); color:#4ade80; border:1px solid rgba(74,222,128,0.35); }
  .tag.view { background:rgba(255,255,255,0.06); color:#9a9ab0; border:1px solid rgba(255,255,255,0.12); }
  .tag.missing { background:rgba(248,113,113,0.12); color:#f87171; border:1px solid rgba(248,113,113,0.3); }

  .btns { display:flex; gap:8px; flex-shrink:0; }
  a.btn { display:inline-block; padding:9px 15px; border-radius:999px; text-decoration:none; font-weight:600; font-size:0.8rem;
          background:linear-gradient(90deg,#8b5cf6,#f59e0b); color:#fff; white-space:nowrap;
          transition:transform 0.2s ease, box-shadow 0.2s ease; }
  a.btn:hover { transform:translateY(-2px); box-shadow:0 8px 20px rgba(139,92,246,0.4); }
  a.btn.ghost { background:rgba(255,255,255,0.06); border:1px solid rgba(255,255,255,0.14); color:#f4f4f8; }

  .empty { color:#9a9ab0; text-align:center; padding:40px 20px; background:rgba(20,20,31,0.5);
           border:1px solid rgba(255,255,255,0.08); border-radius:16px; }
  .empty a { color:#c4b5fd; }
  .no-match { display:none; color:#6b6b80; text-align:center; padding:26px 0; font-size:0.85rem; }
</style></head>
<body>
<div class="orb orb1"></div><div class="orb orb2"></div><div class="orb orb3"></div>
<div class="wrap">
  <div class="top">
    <div><h1>⚡ Your Servers</h1><div class="sub">Logged in as {{ user.username }}</div></div>
    <a class="logout" href="/logout">Log out</a>
  </div>

  <div class="search-wrap">
    <span class="icn">🔎</span>
    <input id="search" type="text" placeholder="Search for a server..." oninput="filterServers()">
  </div>

  <div class="stat-row">
    <span class="stat-pill total">🌐 <b>{{ servers|length }}</b> Servers</span>
    <span class="stat-pill active"><span class="stat-dot"></span> <b>{{ active_count }}</b> Active</span>
    <span class="stat-pill missing"><span class="stat-dot"></span> <b>{{ missing_count }}</b> Missing</span>
  </div>

  <div id="server-list">
  {% for s in servers %}
  <div class="card" data-name="{{ s.name|lower }}" style="animation-delay: {{ (loop.index0 * 0.05)|round(2) }}s;">
    <div class="card-left">
      <div class="icon-ring {{ 'active' if s.bot_present else 'missing' }}">
        {% if s.icon_url %}<img src="{{ s.icon_url }}" alt="">
        {% else %}<span class="fallback">{{ s.name[:1]|upper }}</span>{% endif %}
      </div>
      <div class="name-block">
        <div class="name">{{ s.name }}</div>
        {% if not s.bot_present %}<span class="tag missing">Zexo not here</span>
        {% elif s.is_admin %}<span class="tag admin">✓ Admin — full access</span>
        {% else %}<span class="tag view">View only</span>{% endif %}
      </div>
    </div>
    <div class="btns">
      {% if s.bot_present %}
        <a class="btn ghost" href="/dashboard/{{ s.id }}">Dashboard</a>
        {% if s.is_admin %}<a class="btn" href="/dashboard/{{ s.id }}/settings">⚙️ Settings</a>{% endif %}
      {% else %}
        <a class="btn ghost" href="{{ s.invite_url }}" target="_blank">Invite</a>
      {% endif %}
    </div>
  </div>
  {% else %}
  <div class="empty">No mutual servers found. Make sure Zexo is invited to your server, then <a href="/servers">refresh</a>.</div>
  {% endfor %}
  </div>
  <div class="no-match" id="no-match">No servers match your search.</div>
</div>
<script>
  function filterServers() {
    const q = document.getElementById('search').value.trim().toLowerCase();
    const cards = document.querySelectorAll('#server-list .card');
    let visible = 0;
    cards.forEach(c => {
      const match = c.dataset.name.includes(q);
      c.style.display = match ? '' : 'none';
      if (match) visible++;
    });
    document.getElementById('no-match').style.display = (visible === 0 && cards.length > 0) ? 'block' : 'none';
  }
</script>
</body></html>
"""


def _render_help_category_html(cat: dict) -> str:
    """Turns a HELP_CATEGORIES description (Discord markdown: **bold**, `code`, \\n\\n) into
    simple HTML — same source of truth /help uses, so this page can't drift out of sync."""
    import html as _html
    text = _html.escape(cat["description"])
    text = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", text)
    text = re.sub(r"`(.+?)`", r"<code>\1</code>", text)
    paragraphs = text.split("\n\n")
    return "".join(f"<p>{p.replace(chr(10), '<br>')}</p>" for p in paragraphs)


@app.route('/commands')
def commands_page():
    # Pulls straight from HELP_CATEGORIES — the exact same dict /help in Discord reads from —
    # so any command added/edited/removed there shows up here automatically on next page load.
    sections_html = "".join(
        f'<div class="cmd-card"><h2>{cat["label"]}</h2>{_render_help_category_html(cat)}</div>'
        for cat in HELP_CATEGORIES.values()
    )
    return f"""
    <!DOCTYPE html><html><head><meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Zexo — Commands</title>
    <link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;500;600;700;800&display=swap" rel="stylesheet">
    <style>
      * {{ box-sizing:border-box; }}
      body {{ margin:0; background:#07070d; font-family:'Poppins',Arial,sans-serif; color:#f4f4f8; padding:40px 20px 80px; }}
      .wrap {{ max-width:820px; margin:0 auto; }}
      .top-nav a {{ color:#9ca3af; text-decoration:none; font-size:14px; }}
      .top-nav a:hover {{ color:#f4f4f8; }}
      h1 {{ font-size:34px; font-weight:800; margin:24px 0 6px; background:linear-gradient(90deg,#8b5cf6,#f59e0b,#22d3ee);
            background-size:200% auto; -webkit-background-clip:text; background-clip:text; color:transparent;
            animation:shine 5s linear infinite; }}
      @keyframes shine {{ to {{ background-position:200% center; }} }}
      .sub {{ color:#9ca3af; margin-bottom:32px; }}
      .cmd-card {{ background:#101018; border:1px solid #1f1f2b; border-radius:16px; padding:24px 26px; margin-bottom:18px; }}
      .cmd-card h2 {{ margin:0 0 14px; font-size:20px; }}
      .cmd-card p {{ margin:0 0 14px; line-height:1.6; color:#d1d1db; font-size:14.5px; }}
      .cmd-card code {{ background:#1f1f2b; padding:2px 7px; border-radius:6px; color:#f59e0b; font-size:13.5px; }}
      .cmd-card b {{ color:#c4b5fd; }}
    </style>
    </head><body>
      <div class="wrap">
        <div class="top-nav"><a href="/">← Back home</a></div>
        <h1>⚡ Zexo Commands</h1>
        <p class="sub">Every command works as both <code>!command</code> and <code>/command</code>. This list stays in sync with <code>/help</code> in Discord automatically.</p>
        {sections_html}
      </div>
    </body></html>
    """


@app.route('/servers')
def my_servers():
    user = current_user()
    if not user:
        return redirect(url_for('login'))

    servers = []
    for g in user_guilds(user):
        gid = int(g["id"])
        bot_guild = bot.get_guild(gid)
        try:
            is_admin = (int(g["permissions"]) & ADMINISTRATOR_BIT) != 0
        except (ValueError, TypeError):
            is_admin = False
        icon_hash = g.get("icon")
        icon_url = f"https://cdn.discordapp.com/icons/{gid}/{icon_hash}.png?size=64" if icon_hash else None
        servers.append({
            "id": gid,
            "name": g["name"],
            "bot_present": bot_guild is not None,
            "is_admin": is_admin,
            "icon_url": icon_url,
            "invite_url": bot_invite_url(gid),
        })
    # Servers Zexo is actually in come first, admin ones first among those.
    servers.sort(key=lambda s: (not s["bot_present"], not s["is_admin"], s["name"].lower()))
    active_count = sum(1 for s in servers if s["bot_present"])
    missing_count = len(servers) - active_count

    return render_template_string(
        MY_SERVERS_HTML,
        user=user,
        servers=servers,
        active_count=active_count,
        missing_count=missing_count,
        invite_url=bot_invite_url(),
    )


@app.route('/dashboard')
def web_dashboard_default():
    # Used to silently show bot.guilds[0] here — meaning whichever server the bot happened
    # to join first (in practice, almost always the same one server) no matter who you are
    # or which server you actually manage. Send people to pick explicitly instead.
    if current_user():
        return redirect(url_for('my_servers'))
    if not bot.guilds:
        return "Zexo isn't in any server yet."
    return web_dashboard(bot.guilds[0].id)


@app.route('/dashboard/<int:guild_id>')
def web_dashboard(guild_id):
    guild = bot.get_guild(guild_id)
    if not guild:
        return "Server not found, or Zexo isn't in that server.", 404

    uptime = datetime.now(timezone.utc) - START_TIME
    data = load_points(guild_id)
    sorted_entries = sorted(data.items(), key=lambda x: x[1], reverse=True)[:15]
    medals = ["🥇", "🥈", "🥉"]

    leaderboard = []
    for i, (uid, score) in enumerate(sorted_entries):
        name = resolved_names.get(str(uid), f"User {uid}")
        rank_label = current_rank_label(score, guild_id) or UNRANKED_LABEL
        color = "rgb({},{},{})".format(*TIER_COLORS.get(rank_label, (130, 130, 145)))
        medal = medals[i] if i < 3 else f"{i + 1}."
        _next_label, _needed, low, high = next_rank_progress(score, guild_id)
        progress = int(100 * min(1, max(0, (score - low) / max(1, (high - low))))) if high > low else 100
        leaderboard.append({
            "medal": medal, "name": name, "points": score, "rank": rank_label,
            "color": color, "initial": (name[:1] or "?").upper(), "progress": progress,
        })

    total_uses = sum(command_usage.values()) or 1
    usage = [
        {"name": name, "count": count, "pct": int(100 * count / total_uses)}
        for name, count in sorted(command_usage.items(), key=lambda x: -x[1])[:10]
    ]

    # --- Live vote countdown (mirrors build_timeleft_message's logic, but for the browser clock) ---
    config = load_guild_config(guild_id)
    now = datetime.now(EU_TZ)
    collect_dt = now.replace(hour=config["collect_hour"], minute=config.get("collect_minute", 0), second=0, microsecond=0)
    results_dt = now.replace(hour=config["results_hour"], minute=config.get("results_minute", 0), second=0, microsecond=0)
    entries_count = len(get_poll_state(guild_id).get("entries") or [])

    if now < collect_dt:
        countdown_target, phase_label, voting_live = collect_dt, "Voting hasn't started yet", False
        entries_note = "Submissions are still open — check back at collect time."
    elif collect_dt <= now < results_dt:
        countdown_target, phase_label, voting_live = results_dt, "Voting is live", True
        entries_note = f"{entries_count} edit(s) currently in today's vote."
    else:
        countdown_target, phase_label, voting_live = collect_dt + timedelta(days=1), "Voting has ended for today", False
        entries_note = "Winner announced — next round starts soon."

    other_servers = [{"id": g.id, "name": g.name} for g in bot.guilds if g.id != guild_id]

    # Real, live-computed network stats — summed across every server the bot is actually
    # in right now, not hardcoded to any one server.
    network_member_count = sum((g.member_count or 0) for g in bot.guilds)
    network_server_count = len(bot.guilds)
    top_editor = leaderboard[0] if leaderboard else None

    return render_template_string(
        DASHBOARD_HTML,
        uptime=format_timedelta(uptime),
        server_name=guild.name,
        server_count=network_server_count,
        member_count=guild.member_count or 0,
        network_member_count=network_member_count,
        top_editor=top_editor,
        day_number=load_day(guild_id),
        dpy_version=discord.__version__,
        leaderboard=leaderboard,
        usage=usage,
        countdown_target=countdown_target.astimezone(timezone.utc).isoformat(),
        phase_label=phase_label,
        voting_live=voting_live,
        entries_note=entries_note,
        other_servers=other_servers,
        user=current_user(),
        is_admin=user_is_admin_of(guild_id),
        guild_id=guild_id,
    )


SETTINGS_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Zexo Settings</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;600;700;800&family=Space+Mono:wght@700&display=swap" rel="stylesheet">
<style>
  * { box-sizing: border-box; }
  body { margin:0; font-family:'Poppins',Arial,sans-serif; background:#07070d; color:#f4f4f8; padding:36px 16px 64px; }
  .wrap { max-width:760px; margin:0 auto; }
  h1 { font-size:2rem; font-weight:800; background:linear-gradient(90deg,#8b5cf6,#f59e0b,#22d3ee);
       background-size:200% auto; -webkit-background-clip:text; background-clip:text; color:transparent;
       margin-bottom:4px; animation:shine 5s linear infinite; filter:drop-shadow(0 0 14px rgba(139,92,246,0.35)); }
  @keyframes shine { to { background-position:200% center; } }
  .sub { color:#9a9ab0; font-size:0.9rem; margin-bottom:6px; }
  .back { color:#9a9ab0; text-decoration:none; font-size:0.9rem; }
  .card { background:rgba(20,20,31,0.65); border:1px solid rgba(255,255,255,0.08); border-radius:18px;
          padding:24px 26px; margin-top:22px; backdrop-filter:blur(14px); }
  .card h2 { margin:0 0 4px; font-size:1.1rem; display:flex; align-items:center; gap:8px; }
  .card .desc { color:#9a9ab0; font-size:0.8rem; margin-bottom:14px; }
  label { display:block; font-size:0.8rem; color:#9a9ab0; text-transform:uppercase; letter-spacing:0.05em;
          margin:16px 0 6px; }
  label:first-of-type { margin-top:0; }
  select, input[type=number], input[type=text] {
    width:100%; padding:10px 12px; border-radius:10px; background:rgba(255,255,255,0.05);
    border:1px solid rgba(255,255,255,0.12); color:#f4f4f8; font-family:inherit; font-size:0.95rem;
  }
  .row { display:grid; grid-template-columns:1fr 1fr; gap:16px; }
  .row3 { display:grid; grid-template-columns:1fr 1fr 1fr; gap:16px; }
  .hint { color:#6b6b80; font-size:0.72rem; margin-top:5px; }
  button {
    margin-top:26px; width:100%; padding:13px; border:none; border-radius:999px; cursor:pointer;
    background:linear-gradient(90deg,#8b5cf6,#f59e0b); color:#fff; font-weight:700; font-size:1rem;
  }
  .flash { background:rgba(34,197,94,0.15); border:1px solid rgba(74,222,128,0.35); color:#4ade80;
           padding:10px 16px; border-radius:12px; margin-top:18px; }
  .tier-edit { border:1px solid rgba(255,255,255,0.08); border-radius:12px; padding:14px 16px 4px;
               margin:14px 0; background:rgba(255,255,255,0.02); }
  .tier-edit-head { font-weight:700; font-size:0.85rem; color:#c4b5fd; margin-bottom:2px; }
</style></head>
<body>
<div class="wrap">
  <a class="back" href="/servers">🔀 All servers</a>
  <a class="back" href="/dashboard/{{ guild_id }}" style="margin-left:14px;">← Back to dashboard</a>
  <a class="back" href="/dashboard/{{ guild_id }}/commands" style="margin-left:14px;">⌁ Control Room →</a>
  <a class="back" href="/dashboard/{{ guild_id }}/embed-builder" style="margin-left:14px;">🎨 Embeds →</a>
  <h1>⚙️ {{ server_name }} Settings</h1>
  <div class="sub">Every channel, role, timing and point value the bot uses — fully in your hands.</div>
  {% if saved %}<div class="flash">✅ Saved — changes take effect on the next collection/results run.</div>{% endif %}
  <form method="POST">

    <div class="card">
      <h2>📺 Channels</h2>
      <div class="desc">Where the bot reads submissions from and posts to.</div>
      <label>Submissions channel</label>
      <select name="submit_channel_id">
        {% for c in channels %}<option value="{{ c.id }}" {% if c.id == config.submit_channel_id %}selected{% endif %}>#{{ c.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Where people post their edits. A submission only counts if it pings the Picker role below.</div>
      <label>Discussion / voting channel</label>
      <select name="discussion_channel_id">
        {% for c in channels %}<option value="{{ c.id }}" {% if c.id == config.discussion_channel_id %}selected{% endif %}>#{{ c.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Where the bot reposts each collected edit and opens the daily poll.</div>
      <label>Results channel</label>
      <select name="results_channel_id">
        {% for c in channels %}<option value="{{ c.id }}" {% if c.id == config.results_channel_id %}selected{% endif %}>#{{ c.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Where the daily winner announcement gets posted.</div>
      <label>Points log channel</label>
      <select name="log_channel_id">
        {% for c in channels %}<option value="{{ c.id }}" {% if c.id == config.log_channel_id %}selected{% endif %}>#{{ c.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 An audit trail of every manual points change (who gave/removed points and why).</div>
    </div>

    <div class="card">
      <h2>🛡️ Roles</h2>
      <div class="desc">Who can submit, who manages, and who gets pinged. Hold Ctrl/Cmd (or ⌘) to pick more than one.</div>
      <label>Picker role(s) (must ping one of these to submit)</label>
      <select name="picker_role_ids" multiple size="5">
        {% for r in roles %}<option value="{{ r.id }}" {% if r.id in config.picker_role_ids %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Anyone can post — but the bot only picks up a submission if one of these roles gets pinged in the message. Pick as many as you want.</div>
      <label>Manager role(s)</label>
      <select name="manager_role_ids" multiple size="5">
        {% for r in roles %}<option value="{{ r.id }}" {% if r.id in config.manager_role_ids %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Can use manual point-adjustment and moderation commands in Discord. Pick as many as you want.</div>
      <label>Staff role(s)</label>
      <select name="staff_role_ids" multiple size="5">
        {% for r in roles %}<option value="{{ r.id }}" {% if r.id in config.staff_role_ids %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 A lighter permission tier — staff-only slash commands, below Manager. Pick as many as you want.</div>
      <label>Top-Edits ping role</label>
      <select name="top_edits_role_id">
        {% for r in roles %}<option value="{{ r.id }}" {% if r.id == config.top_edits_role_id %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Pinged when the daily winner is announced — give members this role to get notified.</div>
    </div>

    <div class="card">
      <h2>🏆 Ranks &amp; points</h2>
      <div class="desc">Fully custom per server: how many points each rank needs, its emoji, its role, and how many points a win is worth.</div>
      <label>Unranked role (below the lowest rank)</label>
      <select name="unranked_role_id">
        {% for r in roles %}<option value="{{ r.id }}" {% if r.id == config.unranked_role_id %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Given to anyone with fewer points than your lowest rank's threshold below.</div>
      {% for threshold, _rid, tier_label, emoji in rank_tiers %}
      <div class="tier-edit">
        <div class="tier-edit-head">Rank {{ tier_label }}</div>
        <div class="row3">
          <div>
            <label>Points needed</label>
            <input type="number" name="rank_threshold_{{ tier_label }}" min="0" max="100000" value="{{ threshold }}">
          </div>
          <div>
            <label>Emoji</label>
            <input type="text" name="rank_emoji_{{ tier_label }}" maxlength="8" value="{{ emoji }}">
          </div>
          <div>
            <label>Role</label>
            <select name="rank_role_{{ tier_label }}">
              {% for r in roles %}<option value="{{ r.id }}" {% if r.id == config.rank_role_ids.get(tier_label) %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
            </select>
          </div>
        </div>
      </div>
      {% endfor %}
      <div class="hint">💡 Rank names (D/C/B/A/S) stay fixed, but you fully control the points needed, the emoji shown, and which role each rank grants — set any order or spacing you want.</div>
      <label>Points awarded per daily win</label>
      <input type="number" name="winner_points" min="0" max="1000" value="{{ config.winner_points }}">
      <div class="hint">💡 How many points the daily winner earns — this is what moves people up through the ranks above.</div>
    </div>

    <div class="card">
      <h2>⏰ Timing (Europe/Berlin)</h2>
      <div class="desc">Exactly when submissions are collected, and when voting closes — down to the minute.</div>
      <div class="row3">
        <div>
          <label>Collect hour (0-23)</label>
          <input type="number" name="collect_hour" min="0" max="23" value="{{ config.collect_hour }}">
        </div>
        <div>
          <label>Collect minute (0-59)</label>
          <input type="number" name="collect_minute" min="0" max="59" value="{{ config.collect_minute }}">
        </div>
      </div>
      <div class="hint">💡 The daily moment the bot sweeps up new submissions and opens the vote.</div>
      <div class="row3">
        <div>
          <label>Results hour (0-23)</label>
          <input type="number" name="results_hour" min="0" max="23" value="{{ config.results_hour }}">
        </div>
        <div>
          <label>Results minute (0-59)</label>
          <input type="number" name="results_minute" min="0" max="59" value="{{ config.results_minute }}">
        </div>
      </div>
      <div class="hint">💡 The daily moment the bot tallies votes and announces the winner — should be after the poll duration below has had time to run.</div>
      <label>Poll duration (hours)</label>
      <input type="number" name="poll_duration_hours" min="1" max="48" value="{{ config.poll_duration_hours }}">
      <div class="hint">💡 How long each daily poll stays open for voting. Note: this only changes how long a poll stays open, not the results time above — keep the poll duration shorter than the gap between collect and results so it's closed by the time results run.</div>
    </div>

    <button type="submit">Save changes</button>
  </form>
</div>
</body></html>
"""


@app.route('/dashboard/<int:guild_id>/settings', methods=['GET', 'POST'])
def web_settings(guild_id):
    if not current_user():
        return redirect(url_for('login'))
    if not user_is_admin_of(guild_id):
        return "❌ You need Administrator permission on that server to view its settings.", 403

    guild = bot.get_guild(guild_id)
    if not guild:
        return "Server not found, or Zexo isn't in that server.", 404

    saved = False
    if request.method == 'POST':
        channel_ids = {c.id for c in guild.text_channels}
        role_ids = {r.id for r in guild.roles}
        updates = {}
        for field in ("submit_channel_id", "discussion_channel_id", "results_channel_id", "log_channel_id"):
            try:
                val = int(request.form.get(field, 0))
            except ValueError:
                val = 0
            if val in channel_ids:
                updates[field] = val
        for field in ("top_edits_role_id", "unranked_role_id"):
            try:
                val = int(request.form.get(field, 0))
            except ValueError:
                val = 0
            if val in role_ids:
                updates[field] = val
        for field in ("picker_role_ids", "manager_role_ids", "staff_role_ids"):
            picked = []
            for raw_val in request.form.getlist(field):
                try:
                    val = int(raw_val)
                except ValueError:
                    continue
                if val in role_ids:
                    picked.append(val)
            updates[field] = picked
        rank_role_updates = {}
        rank_threshold_updates = {}
        rank_emoji_updates = {}
        for _threshold, _rid, tier_label, _emoji in RANK_TIERS:
            try:
                val = int(request.form.get(f"rank_role_{tier_label}", 0))
            except ValueError:
                val = 0
            if val in role_ids:
                rank_role_updates[tier_label] = val

            try:
                threshold_val = int(request.form.get(f"rank_threshold_{tier_label}", 0))
            except ValueError:
                threshold_val = None
            if threshold_val is not None and 0 <= threshold_val <= 100000:
                rank_threshold_updates[tier_label] = threshold_val

            emoji_val = (request.form.get(f"rank_emoji_{tier_label}") or "").strip()
            if emoji_val:
                rank_emoji_updates[tier_label] = emoji_val[:8]
        if rank_role_updates:
            updates["rank_role_ids"] = rank_role_updates
        if rank_threshold_updates:
            updates["rank_thresholds"] = rank_threshold_updates
        if rank_emoji_updates:
            updates["rank_emojis"] = rank_emoji_updates
        for field in ("collect_hour", "results_hour"):
            try:
                val = int(request.form.get(field, 0))
            except ValueError:
                val = None
            if val is not None and 0 <= val <= 23:
                updates[field] = val
        for field in ("collect_minute", "results_minute"):
            try:
                val = int(request.form.get(field, 0))
            except ValueError:
                val = None
            if val is not None and 0 <= val <= 59:
                updates[field] = val
        try:
            val = int(request.form.get("winner_points", 0))
        except ValueError:
            val = None
        if val is not None and 0 <= val <= 1000:
            updates["winner_points"] = val
        try:
            val = int(request.form.get("poll_duration_hours", 0))
        except ValueError:
            val = None
        if val is not None and 1 <= val <= 48:
            updates["poll_duration_hours"] = val
        save_guild_config(guild_id, updates)
        saved = True

    config = load_guild_config(guild_id)
    channels = [{"id": c.id, "name": c.name} for c in guild.text_channels]
    roles = [{"id": r.id, "name": r.name} for r in guild.roles if not r.is_default()]

    return render_template_string(
        SETTINGS_HTML,
        guild_id=guild_id,
        server_name=guild.name,
        config=config,
        channels=channels,
        roles=roles,
        rank_tiers=get_guild_rank_tiers(guild_id),
        saved=saved,
    )


def run_on_bot_loop(coro, timeout=30):
    """Bridges a Flask request (its own thread) into an async bot coroutine, running it on
    the bot's actual event loop and blocking until it's done. Needed for any dashboard action
    that touches Discord itself (giving points → role sync, forcing a collect/results run)."""
    future = asyncio.run_coroutine_threadsafe(coro, bot.loop)
    return future.result(timeout=timeout)


def require_admin_json(guild_id: int):
    """Returns a Flask error response if the caller isn't logged in / isn't an admin of this
    guild, else None. Used at the top of every /api/ route below."""
    if not current_user():
        return {"ok": False, "error": "Not logged in."}, 401
    if not user_is_admin_of(guild_id):
        return {"ok": False, "error": "Administrator permission required on that server."}, 403
    return None


COMMANDS_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Zexo Control Room</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Sora:wght@400;600;700;800&family=JetBrains+Mono:wght@500;700&display=swap" rel="stylesheet">
<style>
  :root {
    --bg: #05070a;
    --panel: rgba(16,20,26,0.75);
    --border: rgba(120,255,190,0.14);
    --accent: #22ffb0;
    --accent2: #ff7a3d;
    --text: #e8f2ee;
    --muted: #7c9088;
    --danger: #ff5c7a;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0; font-family: 'Sora', Arial, sans-serif; background: var(--bg); color: var(--text);
    padding: 30px 16px 70px; background-image:
      linear-gradient(rgba(34,255,176,0.035) 1px, transparent 1px),
      linear-gradient(90deg, rgba(34,255,176,0.035) 1px, transparent 1px);
    background-size: 34px 34px;
  }
  .wrap { max-width: 980px; margin: 0 auto; }
  .topbar { display:flex; align-items:center; justify-content:space-between; flex-wrap:wrap; gap:12px; margin-bottom:26px; }
  h1 { font-size: 1.9rem; font-weight: 800; margin:0; letter-spacing:-0.01em; color: var(--accent);
       animation: pulseGlow 2.4s ease-in-out infinite; }
  @keyframes pulseGlow { 0%,100% { text-shadow: 0 0 14px rgba(34,255,176,0.3); }
                          50% { text-shadow: 0 0 30px rgba(34,255,176,0.75), 0 0 50px rgba(34,255,176,0.3); } }
  .tag { color: var(--muted); font-size: 0.85rem; font-family:'JetBrains Mono',monospace; }
  .nav a { color: var(--muted); text-decoration:none; font-size:0.85rem; margin-left:16px; }
  .nav a:hover { color: var(--accent); }
  .tabbar { display:flex; gap:8px; flex-wrap:wrap; margin-bottom:26px; }
  .tabbar a { padding:9px 18px; border-radius:10px; text-decoration:none; font-size:0.85rem; font-weight:600;
              color: var(--muted); border:1px solid var(--border); background: rgba(255,255,255,0.02); }
  .tabbar a.active { color:#04120b; background: var(--accent); border-color: var(--accent); }

  .panel { background: var(--panel); border: 1px solid var(--border); border-radius: 16px; padding: 22px 24px;
           margin-bottom: 20px; backdrop-filter: blur(16px); box-shadow: 0 8px 30px rgba(0,0,0,0.4); }
  .panel h2 { margin: 0 0 4px; font-size: 1.05rem; display:flex; align-items:center; gap:8px; }
  .panel .desc { color: var(--muted); font-size: 0.82rem; margin-bottom: 16px; }
  .field { margin-bottom: 12px; }
  .field label { display:block; font-size:0.72rem; text-transform:uppercase; letter-spacing:0.06em; color:var(--muted); margin-bottom:5px; }
  input[type=text], input[type=number], textarea, select {
    width:100%; padding:10px 12px; border-radius:9px; background: rgba(255,255,255,0.04);
    border:1px solid var(--border); color: var(--text); font-family: inherit; font-size:0.92rem;
  }
  textarea { min-height: 90px; resize: vertical; font-family:'JetBrains Mono',monospace; font-size:0.82rem; }
  .row { display:grid; grid-template-columns:1fr 1fr; gap:12px; }
  .row3 { display:grid; grid-template-columns:2fr 1fr auto; gap:12px; align-items:end; }
  button, .btn {
    padding:10px 18px; border-radius:9px; border:1px solid var(--accent); background: rgba(34,255,176,0.1);
    color: var(--accent); font-weight:700; font-size:0.85rem; cursor:pointer; font-family:inherit;
  }
  button:hover, .btn:hover { background: var(--accent); color:#04120b; }
  button.danger, .btn.danger { border-color: var(--danger); color: var(--danger); }
  button.danger:hover { background: var(--danger); color:#1a0006; }
  button.wide { width:100%; margin-top:6px; }
  .chip-list { display:flex; flex-wrap:wrap; gap:8px; margin-top:10px; }
  .chip { display:flex; align-items:center; gap:8px; padding:6px 12px; border-radius:999px;
          background: rgba(255,90,120,0.1); border:1px solid rgba(255,90,120,0.3); font-size:0.8rem;
          font-family:'JetBrains Mono',monospace; }
  .chip button { padding:2px 7px; font-size:0.7rem; border-radius:999px; }
  .toast { position:fixed; bottom:22px; left:50%; transform:translateX(-50%); background: var(--accent);
           color:#04120b; padding:10px 22px; border-radius:999px; font-weight:700; font-size:0.85rem;
           opacity:0; pointer-events:none; transition:opacity 0.25s ease, transform 0.25s ease; z-index:50; }
  .toast.show { opacity:1; transform:translateX(-50%) translateY(-6px); }
  .empty { color: var(--muted); font-size:0.85rem; font-style:italic; }
  .hint { color: var(--muted); font-size:0.72rem; margin-top:6px; }
</style></head>
<body>
<div class="wrap">
  <div class="topbar">
    <div><h1>⌁ Zexo Control Room</h1><div class="tag">{{ server_name }} · live command center</div></div>
    <div class="nav">
      <a href="/servers">🔀 All servers</a>
      <a href="/dashboard/{{ guild_id }}">Dashboard</a>
      <a href="/dashboard/{{ guild_id }}/settings">Config</a>
      <a href="/dashboard/{{ guild_id }}/embed-builder">🎨 Embeds</a>
      <a href="/logout">Log out</a>
    </div>
  </div>

  <div class="tabbar">
    <a class="active" href="#points">Points</a>
    <a href="#badwords">Badwords</a>
    <a href="#triggers">Manual Runs</a>
    <a href="#texts">Custom Texts</a>
  </div>

  <div class="panel" id="points">
    <h2>🏅 Points</h2>
    <div class="desc">Give, remove, or wipe a user's points. Rank roles update automatically, same as the Discord command.</div>
    <div class="row3">
      <div class="field"><label>Discord User ID</label><input type="text" id="pt-user" placeholder="e.g. 123456789012345678"></div>
      <div class="field"><label>Amount</label><input type="number" id="pt-amount" value="1"></div>
      <button onclick="doPoints('add')">Give</button>
    </div>
    <div style="display:flex; gap:10px; margin-top:6px;">
      <button onclick="doPoints('remove')">Remove amount</button>
      <button class="danger" onclick="doPoints('reset')">Reset this user</button>
      <button class="danger" onclick="if(confirm('Reset points for EVERYONE on this server?')) doPoints('reset_all')">Reset ALL points</button>
    </div>
    <div id="points-result" class="hint"></div>
  </div>

  <div class="panel" id="badwords">
    <h2>🚫 Badwords</h2>
    <div class="desc">Words/phrases the bot filters. Changes apply immediately, no restart needed.</div>
    <div class="row3">
      <div class="field"><label>Word or phrase</label><input type="text" id="bw-word" placeholder="add a badword..."></div>
      <div></div>
      <button onclick="addBadword()">Add</button>
    </div>
    <div class="chip-list" id="bw-list">{{ badwords_html|safe }}</div>
  </div>

  <div class="panel" id="triggers">
    <h2>⚡ Manual Runs</h2>
    <div class="desc">Force today's collect or results step right now instead of waiting for the scheduled hour.
      Runs only for <b>{{ server_name }}</b> — every other server the bot is in is completely unaffected.</div>
    <div style="display:flex; gap:10px;">
      <button onclick="doTrigger('collect')">Run Collect Now</button>
      <button onclick="doTrigger('results')">Run Results Now</button>
    </div>
    <div class="hint">💡 Collect pulls in every new submission since the last run and opens today's poll. Results tallies whatever poll is currently open and announces the winner — use it once voting has actually had time to run, not right after Collect.</div>
    <div id="trigger-result" class="hint"></div>
  </div>

  <div class="panel" id="texts">
    <h2>✍️ Custom Texts</h2>
    <div class="desc">100% customizable — leave blank to use the built-in default text. Use <code>{member}</code> where the winner/user should be mentioned.</div>
    <div class="field">
      <label>Winner announcement lines (one per line — a random one is picked each time; leave empty for the built-in 100-line pool)</label>
      <textarea id="tx-winners" placeholder="🏆 {member} takes today's crown!">{{ config.custom_winner_messages|join('\\n') }}</textarea>
    </div>
    <div class="field">
      <label>"Forgot to ping" reminder text</label>
      <textarea id="tx-reminder" placeholder="👋 {member}, don't forget to ping the Picker role!">{{ config.custom_reminder_message or '' }}</textarea>
    </div>
    <div class="field">
      <label>Poll question</label>
      <input type="text" id="tx-question" value="{{ config.custom_poll_question or '' }}" placeholder="Vote for today's top edit!">
    </div>
    <button class="wide" onclick="saveTexts()">Save texts</button>
  </div>
</div>

<div class="toast" id="toast"></div>

<script>
const guildId = {{ guild_id }};
function toast(msg, ok=true) {
  const t = document.getElementById('toast');
  t.textContent = msg;
  t.style.background = ok ? 'var(--accent)' : 'var(--danger)';
  t.classList.add('show');
  setTimeout(() => t.classList.remove('show'), 2200);
}
async function api(path, body) {
  const res = await fetch(path, { method: 'POST', headers: {'Content-Type':'application/json'}, body: JSON.stringify(body) });
  const data = await res.json();
  if (!res.ok || !data.ok) { toast(data.error || 'Something went wrong', false); throw new Error(data.error); }
  return data;
}
async function doPoints(action) {
  const user_id = document.getElementById('pt-user').value.trim();
  const amount = parseInt(document.getElementById('pt-amount').value || '0', 10);
  if (!user_id) { toast('Enter a user ID first', false); return; }
  try {
    const data = await api(`/dashboard/${guildId}/api/points`, { action, user_id, amount });
    document.getElementById('points-result').textContent = data.message;
    toast(data.message);
  } catch (e) {}
}
function renderBadwordChip(word) {
  const span = document.createElement('span');
  span.className = 'chip';
  span.dataset.word = word;
  span.innerHTML = `<span>${word}</span>`;
  const btn = document.createElement('button');
  btn.textContent = '✕';
  btn.onclick = () => removeBadword(word, span);
  span.appendChild(btn);
  return span;
}
async function addBadword() {
  const input = document.getElementById('bw-word');
  const word = input.value.trim();
  if (!word) return;
  try {
    await api(`/dashboard/${guildId}/api/badwords`, { action: 'add', word });
    document.getElementById('bw-list').appendChild(renderBadwordChip(word));
    input.value = '';
    toast(`Added "${word}"`);
  } catch (e) {}
}
async function removeBadword(word, el) {
  try {
    await api(`/dashboard/${guildId}/api/badwords`, { action: 'remove', word });
    el.remove();
    toast(`Removed "${word}"`);
  } catch (e) {}
}
async function doTrigger(action) {
  document.getElementById('trigger-result').textContent = 'Running...';
  try {
    const data = await api(`/dashboard/${guildId}/api/trigger`, { action });
    document.getElementById('trigger-result').textContent = data.message;
    toast(data.message);
  } catch (e) {
    document.getElementById('trigger-result').textContent = '';
  }
}
async function saveTexts() {
  const custom_winner_messages = document.getElementById('tx-winners').value.split('\\n').map(s => s.trim()).filter(Boolean);
  const custom_reminder_message = document.getElementById('tx-reminder').value.trim();
  const custom_poll_question = document.getElementById('tx-question').value.trim();
  try {
    await api(`/dashboard/${guildId}/api/messages`, { custom_winner_messages, custom_reminder_message, custom_poll_question });
    toast('Texts saved ✓');
  } catch (e) {}
}
</script>
</body></html>
"""


@app.route('/dashboard/<int:guild_id>/commands')
def web_commands(guild_id):
    if not current_user():
        return redirect(url_for('login'))
    if not user_is_admin_of(guild_id):
        return "❌ You need Administrator permission on that server to view its command center.", 403

    guild = bot.get_guild(guild_id)
    if not guild:
        return "Server not found, or Zexo isn't in that server.", 404

    try:
        config = load_guild_config(guild_id)
        words = load_badwords(guild_id)
    except Exception as e:
        print(f"⚠️ Control Room failed to load data for guild {guild_id}: {e}")
        return (
            "⚠️ Couldn't reach the database right now (it may be waking up from sleep on "
            "Render's free tier — try again in ~30 seconds).",
            503,
        )
    badwords_html = "".join(
        f'<span class="chip" data-word="{w}"><span>{w}</span>'
        f'<button onclick="removeBadword(\'{w}\', this.parentElement)">✕</button></span>'
        for w in words
    ) or '<span class="empty">No badwords configured.</span>'

    return render_template_string(
        COMMANDS_HTML,
        guild_id=guild_id,
        server_name=guild.name,
        config=config,
        badwords_html=badwords_html,
    )


@app.route('/dashboard/<int:guild_id>/api/points', methods=['POST'])
def api_points(guild_id):
    err = require_admin_json(guild_id)
    if err:
        return err
    guild = bot.get_guild(guild_id)
    if not guild:
        return {"ok": False, "error": "Server not found."}, 404

    data = request.get_json(force=True) or {}
    action = data.get("action")
    try:
        user_id = int(data.get("user_id"))
    except (TypeError, ValueError):
        return {"ok": False, "error": "Invalid user ID."}, 400
    try:
        amount = int(data.get("amount", 0))
    except (TypeError, ValueError):
        amount = 0

    if action == "add":
        new_total = run_on_bot_loop(award_points(guild, user_id, amount))
        return {"ok": True, "message": f"Gave {amount} points → total {new_total}."}
    if action == "remove":
        new_total = run_on_bot_loop(award_points(guild, user_id, -amount))
        return {"ok": True, "message": f"Removed {amount} points → total {new_total}."}
    if action == "reset":
        points = load_points(guild_id)
        points[str(user_id)] = 0
        save_points(guild_id, points)
        run_on_bot_loop(apply_point_roles(guild, user_id, 0))
        return {"ok": True, "message": "Points reset for that user."}
    if action == "reset_all":
        save_points(guild_id, {})
        return {"ok": True, "message": "All points on this server were reset."}
    return {"ok": False, "error": "Unknown action."}, 400


@app.route('/dashboard/<int:guild_id>/api/badwords', methods=['POST'])
def api_badwords(guild_id):
    err = require_admin_json(guild_id)
    if err:
        return err
    data = request.get_json(force=True) or {}
    action = data.get("action")
    word = (data.get("word") or "").strip().lower()
    if not word:
        return {"ok": False, "error": "No word given."}, 400

    words = load_badwords(guild_id)
    if action == "add":
        if word not in words:
            words.append(word)
            save_badwords(guild_id, words)
        return {"ok": True, "message": f'Added "{word}".'}
    if action == "remove":
        if word in words:
            words.remove(word)
            save_badwords(guild_id, words)
        return {"ok": True, "message": f'Removed "{word}".'}
    return {"ok": False, "error": "Unknown action."}, 400


@app.route('/dashboard/<int:guild_id>/api/trigger', methods=['POST'])
def api_trigger(guild_id):
    err = require_admin_json(guild_id)
    if err:
        return err
    guild = bot.get_guild(guild_id)
    if not guild:
        return {"ok": False, "error": "Zexo isn't in that server."}, 404
    data = request.get_json(force=True) or {}
    action = data.get("action")
    if action == "collect":
        # Scoped to THIS server only — this used to call the all-servers version and
        # would fire the collect job for every server the bot is in, not just the
        # one you're managing.
        run_on_bot_loop(run_collect_job_for_guild(guild), timeout=120)
        return {"ok": True, "message": f"Collect run finished for {guild.name}."}
    if action == "results":
        run_on_bot_loop(run_results_job_for_guild(guild), timeout=120)
        return {"ok": True, "message": f"Results run finished for {guild.name}."}
    return {"ok": False, "error": "Unknown action."}, 400


@app.route('/dashboard/<int:guild_id>/api/messages', methods=['POST'])
def api_messages(guild_id):
    err = require_admin_json(guild_id)
    if err:
        return err
    data = request.get_json(force=True) or {}
    updates = {}
    if "custom_winner_messages" in data and isinstance(data["custom_winner_messages"], list):
        updates["custom_winner_messages"] = [str(s)[:300] for s in data["custom_winner_messages"]][:200]
    if "custom_reminder_message" in data:
        updates["custom_reminder_message"] = (data["custom_reminder_message"] or None)
    if "custom_poll_question" in data:
        updates["custom_poll_question"] = (data["custom_poll_question"] or None)
    save_guild_config(guild_id, updates)
    return {"ok": True, "message": "Saved."}


EMBED_BUILDER_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Zexo Embed Builder</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Sora:wght@400;600;700;800&family=JetBrains+Mono:wght@500;700&display=swap" rel="stylesheet">
<style>
  :root {
    --bg: #05070a; --panel: rgba(16,20,26,0.75); --border: rgba(120,255,190,0.14);
    --accent: #22ffb0; --accent2: #ff7a3d; --text: #e8f2ee; --muted: #7c9088; --danger: #ff5c7a;
  }
  * { box-sizing: border-box; }
  body { margin:0; font-family:'Sora',Arial,sans-serif; background:var(--bg); color:var(--text); padding:30px 16px 70px;
    background-image: linear-gradient(rgba(34,255,176,0.035) 1px, transparent 1px), linear-gradient(90deg, rgba(34,255,176,0.035) 1px, transparent 1px);
    background-size:34px 34px; }
  .wrap { max-width:1100px; margin:0 auto; }
  .topbar { display:flex; align-items:center; justify-content:space-between; flex-wrap:wrap; gap:12px; margin-bottom:26px; }
  h1 { font-size:1.9rem; font-weight:800; margin:0; letter-spacing:-0.01em; color:var(--accent);
       animation: pulseGlow 2.4s ease-in-out infinite; }
  @keyframes pulseGlow { 0%,100% { text-shadow: 0 0 14px rgba(34,255,176,0.3); }
                          50% { text-shadow: 0 0 30px rgba(34,255,176,0.75), 0 0 50px rgba(34,255,176,0.3); } }
  .tag { color:var(--muted); font-size:0.85rem; font-family:'JetBrains Mono',monospace; }
  .nav a { color:var(--muted); text-decoration:none; font-size:0.85rem; margin-left:16px; }
  .nav a:hover { color:var(--accent); }
  .cols { display:grid; grid-template-columns: 1.1fr 0.9fr; gap:20px; align-items:start; }
  @media (max-width: 860px) { .cols { grid-template-columns: 1fr; } }
  .panel { background:var(--panel); border:1px solid var(--border); border-radius:16px; padding:22px 24px; margin-bottom:20px;
    backdrop-filter: blur(16px); box-shadow:0 8px 30px rgba(0,0,0,0.4); }
  .panel h2 { margin:0 0 4px; font-size:1.05rem; }
  .panel .desc { color:var(--muted); font-size:0.82rem; margin-bottom:16px; }
  .field { margin-bottom:12px; }
  .field label { display:block; font-size:0.72rem; text-transform:uppercase; letter-spacing:0.06em; color:var(--muted); margin-bottom:5px; }
  input[type=text], input[type=color], input[type=checkbox], textarea, select {
    width:100%; padding:10px 12px; border-radius:9px; background:rgba(255,255,255,0.04);
    border:1px solid var(--border); color:var(--text); font-family:inherit; font-size:0.92rem;
  }
  input[type=color] { padding:4px; height:42px; cursor:pointer; }
  textarea { min-height:80px; resize:vertical; font-family:'JetBrains Mono',monospace; font-size:0.82rem; }
  .row { display:grid; grid-template-columns:1fr 1fr; gap:12px; }
  button, .btn { padding:10px 18px; border-radius:9px; border:1px solid var(--accent); background:rgba(34,255,176,0.1);
    color:var(--accent); font-weight:700; font-size:0.85rem; cursor:pointer; font-family:inherit; }
  button:hover, .btn:hover { background:var(--accent); color:#04120b; }
  button.wide { width:100%; margin-top:6px; }
  button.ghost { background:transparent; border-color:var(--border); color:var(--muted); }
  .fieldrow { display:grid; grid-template-columns:1fr 1fr auto auto; gap:8px; align-items:center; margin-bottom:8px; }
  .toast { position:fixed; bottom:22px; left:50%; transform:translateX(-50%); background:var(--accent); color:#04120b;
    padding:10px 22px; border-radius:999px; font-weight:700; font-size:0.85rem; opacity:0; pointer-events:none;
    transition:opacity 0.25s ease, transform 0.25s ease; z-index:50; }
  .toast.show { opacity:1; transform:translateX(-50%) translateY(-6px); }
  .hint { color:var(--muted); font-size:0.72rem; margin-top:6px; }
  /* Discord-style live preview */
  .preview-outer { background:#313338; border-radius:10px; padding:16px; font-family: 'gg sans', 'Sora', sans-serif; }
  .preview-embed { display:flex; }
  .preview-bar { width:4px; border-radius:3px 0 0 3px; flex-shrink:0; }
  .preview-body { background:#2b2d31; border-radius:0 4px 4px 0; padding:12px 16px; max-width:520px; flex:1; }
  .preview-author { display:flex; align-items:center; gap:8px; font-size:0.8rem; font-weight:600; color:#f2f3f5; margin-bottom:6px; }
  .preview-author img { width:20px; height:20px; border-radius:50%; }
  .preview-title { font-weight:700; color:#f2f3f5; font-size:0.95rem; margin-bottom:6px; }
  .preview-desc { color:#dbdee1; font-size:0.85rem; white-space:pre-wrap; line-height:1.4; }
  .preview-fields { display:grid; grid-template-columns:1fr 1fr; gap:8px; margin-top:10px; }
  .preview-fields .full { grid-column:1/-1; }
  .preview-field-name { font-weight:700; color:#f2f3f5; font-size:0.8rem; margin-bottom:2px; }
  .preview-field-value { color:#dbdee1; font-size:0.82rem; }
  .preview-thumb { width:80px; height:80px; object-fit:cover; border-radius:4px; margin-left:16px; }
  .preview-image { margin-top:10px; max-width:100%; border-radius:4px; display:block; }
  .preview-footer { display:flex; align-items:center; gap:6px; margin-top:10px; color:#949ba4; font-size:0.75rem; }
  .preview-footer img { width:16px; height:16px; border-radius:50%; }
  .empty { color:var(--muted); font-style:italic; font-size:0.85rem; }
  .emoji-trigger-row { display:flex; justify-content:flex-end; margin:-4px 0 12px; }
  .emoji-picker { position:relative; margin-bottom:14px; background:rgba(255,255,255,0.03); border:1px solid var(--border);
    border-radius:12px; padding:14px; display:flex; flex-direction:column; gap:10px; }
  .emoji-picker.hidden { display:none; }
  .emoji-picker input[type=text] { padding:8px 10px; font-size:0.82rem; }
  .emoji-grid { display:grid; grid-template-columns:repeat(auto-fill, minmax(44px,1fr)); gap:7px; overflow-y:auto; max-height:220px; }
  .emoji-btn { background:rgba(255,255,255,0.04); border:1px solid transparent; border-radius:9px; padding:5px; cursor:pointer;
    display:flex; align-items:center; justify-content:center; transition:transform 0.12s ease, border-color 0.12s ease, background 0.12s ease; }
  .emoji-btn:hover { transform:scale(1.18); border-color:var(--accent); background:rgba(34,255,176,0.12); }
  .emoji-btn img { width:26px; height:26px; object-fit:contain; }
  .preview-emoji { width:20px; height:20px; vertical-align:-5px; object-fit:contain; }
</style></head>
<body>
<div class="wrap">
  <div class="topbar">
    <div><h1>🎨 Embed Builder</h1><div class="tag">{{ server_name }} · build &amp; send rich embeds, no code needed</div></div>
    <div class="nav">
      <a href="/dashboard/{{ guild_id }}">Dashboard</a>
      <a href="/dashboard/{{ guild_id }}/commands">⌁ Control Room</a>
      <a href="/logout">Log out</a>
    </div>
  </div>

  <div class="cols">
    <div>
      <div class="panel">
        <h2>✍️ Content</h2>
        <div class="emoji-trigger-row">
          <button type="button" class="ghost" onclick="toggleEmojiPicker(event)">😀 Insert server emoji</button>
        </div>
        <div id="emoji-picker" class="emoji-picker hidden">
          <input type="text" id="emoji-search" placeholder="Search this server's emojis..." oninput="filterEmojis()">
          <div id="emoji-grid" class="emoji-grid"></div>
          <div class="hint">Click a field below first, then click an emoji to drop it in right where your cursor is — works with Nitro/animated emojis too.</div>
        </div>
        <div class="field"><label>Plain text above the embed (optional)</label><input type="text" id="eb-content" placeholder="@everyone or just a short heads-up..."></div>
        <div class="row">
          <div class="field"><label>Author name</label><input type="text" id="eb-author" placeholder=""></div>
          <div class="field"><label>Author icon URL</label><input type="text" id="eb-author-icon" placeholder=""></div>
        </div>
        <div class="field"><label>Title</label><input type="text" id="eb-title" placeholder="Big bold headline"></div>
        <div class="field"><label>Description</label><textarea id="eb-desc" placeholder="The main body text of the embed..."></textarea></div>
        <div class="row">
          <div class="field"><label>Color</label><input type="color" id="eb-color" value="#22ffb0"></div>
          <div class="field"><label>Show timestamp</label><select id="eb-timestamp"><option value="0">No</option><option value="1">Yes</option></select></div>
        </div>
        <div class="row">
          <div class="field"><label>Thumbnail URL (small, top-right)</label><input type="text" id="eb-thumb" placeholder=""></div>
          <div class="field"><label>Image URL (large, bottom)</label><input type="text" id="eb-image" placeholder=""></div>
        </div>
        <div class="row">
          <div class="field"><label>Footer text</label><input type="text" id="eb-footer" placeholder=""></div>
          <div class="field"><label>Footer icon URL</label><input type="text" id="eb-footer-icon" placeholder=""></div>
        </div>
      </div>

      <div class="panel">
        <h2>📋 Fields</h2>
        <div class="desc">Up to 25 name/value pairs, shown side-by-side unless "full width" is checked.</div>
        <div id="eb-fields"></div>
        <button class="ghost" onclick="addField()">+ Add field</button>
      </div>

      <div class="panel">
        <h2>🚀 Send</h2>
        <div class="field"><label>Channel</label>
          <select id="eb-channel">
            {% for c in channels %}<option value="{{ c.id }}">#{{ c.name }}</option>{% endfor %}
          </select>
        </div>
        <button class="wide" onclick="sendEmbed()">Send to channel</button>
        <div id="eb-result" class="hint"></div>
      </div>
    </div>

    <div>
      <div class="panel" style="position:sticky; top:20px;">
        <h2>👁️ Live preview</h2>
        <div class="preview-outer"><div id="eb-preview"></div></div>
      </div>
    </div>
  </div>
</div>

<div class="toast" id="toast"></div>

<script>
const guildId = {{ guild_id }};
const guildEmojis = [
  {% for em in emojis %}{ name: {{ em.name|tojson }}, id: {{ em.id|tojson }}, animated: {{ em.animated|tojson }}, url: {{ em.url|tojson }} },
  {% endfor %}
];
let fieldCount = 0;
let lastFocusedField = null;
function toast(msg, ok=true) {
  const t = document.getElementById('toast');
  t.textContent = msg;
  t.style.background = ok ? 'var(--accent)' : 'var(--danger)';
  t.classList.add('show');
  setTimeout(() => t.classList.remove('show'), 2200);
}
function trackFocus(el) {
  el.addEventListener('focus', () => { lastFocusedField = el; });
}
function toggleEmojiPicker(ev) {
  ev.preventDefault();
  const picker = document.getElementById('emoji-picker');
  picker.classList.toggle('hidden');
  if (!picker.classList.contains('hidden')) renderEmojiGrid();
}
function renderEmojiGrid(filter='') {
  const grid = document.getElementById('emoji-grid');
  if (!guildEmojis.length) {
    grid.innerHTML = '<span class="empty">This server has no custom emojis uploaded yet — add some in Server Settings → Emoji.</span>';
    return;
  }
  const f = filter.toLowerCase();
  const filtered = guildEmojis.filter(e => e.name.toLowerCase().includes(f));
  if (!filtered.length) { grid.innerHTML = '<span class="empty">No emojis match that search.</span>'; return; }
  grid.innerHTML = filtered.map(e =>
    `<button type="button" class="emoji-btn" title=":${e.name}:" onclick="insertEmoji('${e.name}','${e.id}',${e.animated})"><img src="${e.url}" alt=":${e.name}:" loading="lazy"></button>`
  ).join('');
}
function filterEmojis() { renderEmojiGrid(document.getElementById('emoji-search').value); }
function insertEmoji(name, id, animated) {
  const code = `<${animated ? 'a' : ''}:${name}:${id}>`;
  const field = lastFocusedField || document.getElementById('eb-desc');
  const start = field.selectionStart ?? field.value.length;
  const end = field.selectionEnd ?? field.value.length;
  field.value = field.value.slice(0, start) + code + field.value.slice(end);
  const caret = start + code.length;
  field.focus();
  field.setSelectionRange(caret, caret);
  renderPreview();
}
function addField(name='', value='', inline=true) {
  const id = fieldCount++;
  const row = document.createElement('div');
  row.className = 'fieldrow';
  row.dataset.id = id;
  row.innerHTML = `
    <input type="text" placeholder="Field name" class="ef-name" value="${name.replace(/"/g,'&quot;')}">
    <input type="text" placeholder="Field value" class="ef-value" value="${value.replace(/"/g,'&quot;')}">
    <label style="display:flex; align-items:center; gap:4px; font-size:0.72rem; color:var(--muted); white-space:nowrap;">
      <input type="checkbox" class="ef-inline" style="width:auto;" ${inline ? 'checked' : ''}> inline</label>
    <button class="ghost" onclick="this.parentElement.remove(); renderPreview();">✕</button>`;
  document.getElementById('eb-fields').appendChild(row);
  row.querySelectorAll('input').forEach(el => el.addEventListener('input', renderPreview));
  row.querySelector('.ef-name').addEventListener('focus', () => { lastFocusedField = row.querySelector('.ef-name'); });
  row.querySelector('.ef-value').addEventListener('focus', () => { lastFocusedField = row.querySelector('.ef-value'); });
  renderPreview();
}
function escapeHtml(s) {
  return (s || '').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
}
// Renders text the way Discord itself does: plain text gets HTML-escaped as usual, but any
// <:name:id> / <a:name:id> custom-emoji token gets swapped for the real emoji image instead
// of showing up as raw text — same as what people would actually see in the channel.
function renderTextWithEmojis(raw) {
  if (!raw) return '';
  const parts = raw.split(/(<a?:[A-Za-z0-9_]+:[0-9]+>)/g);
  return parts.map(part => {
    const m = part.match(/^<(a)?:([A-Za-z0-9_]+):([0-9]+)>$/);
    if (m) {
      const animated = m[1] === 'a';
      const ext = animated ? 'gif' : 'png';
      return `<img class="preview-emoji" src="https://cdn.discordapp.com/emojis/${m[3]}.${ext}" alt=":${m[2]}:">`;
    }
    return escapeHtml(part);
  }).join('');
}
function collectEmbed() {
  const fields = [...document.querySelectorAll('#eb-fields .fieldrow')].map(row => ({
    name: row.querySelector('.ef-name').value.trim(),
    value: row.querySelector('.ef-value').value.trim(),
    inline: row.querySelector('.ef-inline').checked,
  })).filter(f => f.name && f.value);
  return {
    content: document.getElementById('eb-content').value.trim(),
    author_name: document.getElementById('eb-author').value.trim(),
    author_icon_url: document.getElementById('eb-author-icon').value.trim(),
    title: document.getElementById('eb-title').value.trim(),
    description: document.getElementById('eb-desc').value.trim(),
    color: document.getElementById('eb-color').value,
    timestamp: document.getElementById('eb-timestamp').value === '1',
    thumbnail_url: document.getElementById('eb-thumb').value.trim(),
    image_url: document.getElementById('eb-image').value.trim(),
    footer_text: document.getElementById('eb-footer').value.trim(),
    footer_icon_url: document.getElementById('eb-footer-icon').value.trim(),
    fields,
  };
}
function renderPreview() {
  const e = collectEmbed();
  if (!e.title && !e.description && !e.author_name && e.fields.length === 0 && !e.image_url) {
    document.getElementById('eb-preview').innerHTML = '<span class="empty">Nothing to preview yet — fill in a title or description.</span>';
    return;
  }
  let html = `<div class="preview-embed"><div class="preview-bar" style="background:${e.color}"></div><div class="preview-body">`;
  if (e.author_name) html += `<div class="preview-author">${e.author_icon_url ? `<img src="${e.author_icon_url}">` : ''}${renderTextWithEmojis(e.author_name)}</div>`;
  if (e.title) html += `<div class="preview-title">${renderTextWithEmojis(e.title)}</div>`;
  if (e.description) html += `<div class="preview-desc">${renderTextWithEmojis(e.description)}</div>`;
  if (e.fields.length) {
    html += '<div class="preview-fields">';
    e.fields.forEach(f => {
      html += `<div class="${f.inline ? '' : 'full'}"><div class="preview-field-name">${renderTextWithEmojis(f.name)}</div><div class="preview-field-value">${renderTextWithEmojis(f.value)}</div></div>`;
    });
    html += '</div>';
  }
  if (e.image_url) html += `<img class="preview-image" src="${e.image_url}">`;
  if (e.footer_text || e.timestamp) {
    html += `<div class="preview-footer">${e.footer_icon_url ? `<img src="${e.footer_icon_url}">` : ''}${renderTextWithEmojis(e.footer_text)}${e.timestamp ? (e.footer_text ? ' • ' : '') + 'Just now' : ''}</div>`;
  }
  html += '</div>';
  if (e.thumbnail_url) html += `<img class="preview-thumb" src="${e.thumbnail_url}">`;
  html += '</div>';
  document.getElementById('eb-preview').innerHTML = html;
}
['eb-content','eb-author','eb-author-icon','eb-title','eb-desc','eb-color','eb-timestamp','eb-thumb','eb-image','eb-footer','eb-footer-icon'].forEach(id => {
  const el = document.getElementById(id);
  el.addEventListener('input', renderPreview);
  trackFocus(el);
});
async function sendEmbed() {
  const embed = collectEmbed();
  const channel_id = document.getElementById('eb-channel').value;
  if (!channel_id) { toast('Pick a channel first', false); return; }
  if (!embed.title && !embed.description) { toast('Add at least a title or description', false); return; }
  try {
    const res = await fetch(`/dashboard/${guildId}/api/embed-builder/send`, {
      method: 'POST', headers: {'Content-Type':'application/json'},
      body: JSON.stringify({ channel_id, embed })
    });
    const data = await res.json();
    if (!res.ok || !data.ok) { toast(data.error || 'Something went wrong', false); return; }
    document.getElementById('eb-result').textContent = data.message;
    toast(data.message);
  } catch (e) { toast('Network error', false); }
}
addField();
renderPreview();
</script>
</body></html>
"""


@app.route('/dashboard/<int:guild_id>/embed-builder')
def web_embed_builder(guild_id):
    if not current_user():
        return redirect(url_for('login'))
    if not user_is_admin_of(guild_id):
        return "❌ You need Administrator permission on that server to use the embed builder.", 403

    guild = bot.get_guild(guild_id)
    if not guild:
        return "Server not found, or Zexo isn't in that server.", 404

    channels = [{"id": c.id, "name": c.name} for c in guild.text_channels]
    emojis = [
        {
            "name": e.name,
            "id": e.id,
            "animated": e.animated,
            "url": f"https://cdn.discordapp.com/emojis/{e.id}.{'gif' if e.animated else 'png'}",
        }
        for e in guild.emojis
    ]
    return render_template_string(
        EMBED_BUILDER_HTML,
        guild_id=guild_id,
        server_name=guild.name,
        channels=channels,
        emojis=emojis,
    )


@app.route('/dashboard/<int:guild_id>/api/embed-builder/send', methods=['POST'])
def api_embed_builder_send(guild_id):
    err = require_admin_json(guild_id)
    if err:
        return err
    guild = bot.get_guild(guild_id)
    if not guild:
        return {"ok": False, "error": "Zexo isn't in that server."}, 404

    data = request.get_json(force=True) or {}
    try:
        channel_id = int(data.get("channel_id"))
    except (TypeError, ValueError):
        return {"ok": False, "error": "Invalid channel."}, 400
    channel = guild.get_channel(channel_id)
    if not channel:
        return {"ok": False, "error": "Channel not found in this server."}, 404

    e = data.get("embed") or {}
    title = (e.get("title") or "").strip()[:256]
    description = (e.get("description") or "").strip()[:4096]
    if not title and not description:
        return {"ok": False, "error": "Embed needs at least a title or description."}, 400

    try:
        color_hex = (e.get("color") or "#22ffb0").lstrip("#")
        color = discord.Color(int(color_hex, 16))
    except (ValueError, TypeError):
        color = discord.Color.default()

    embed = discord.Embed(title=title or discord.Embed.Empty, description=description or discord.Embed.Empty, color=color)
    author_name = (e.get("author_name") or "").strip()[:256]
    if author_name:
        embed.set_author(name=author_name, icon_url=(e.get("author_icon_url") or "").strip() or None)
    thumbnail_url = (e.get("thumbnail_url") or "").strip()
    if thumbnail_url:
        embed.set_thumbnail(url=thumbnail_url)
    image_url = (e.get("image_url") or "").strip()
    if image_url:
        embed.set_image(url=image_url)
    footer_text = (e.get("footer_text") or "").strip()[:2048]
    if footer_text or (e.get("footer_icon_url") or "").strip():
        embed.set_footer(text=footer_text, icon_url=(e.get("footer_icon_url") or "").strip() or None)
    if e.get("timestamp"):
        embed.timestamp = datetime.now(timezone.utc)
    for f in (e.get("fields") or [])[:25]:
        name = (f.get("name") or "").strip()[:256]
        value = (f.get("value") or "").strip()[:1024]
        if name and value:
            embed.add_field(name=name, value=value, inline=bool(f.get("inline", True)))

    content = (data.get("content") or "").strip()[:2000] or None
    try:
        run_on_bot_loop(channel.send(content=content, embed=embed), timeout=30)
    except Exception as ex:
        print(f"⚠️ Embed builder send failed: {ex}")
        return {"ok": False, "error": "Failed to send — check the URLs (image/thumbnail/icon) are valid direct links."}, 500

    return {"ok": True, "message": f"Sent to #{channel.name} ✅"}


def run_web():
    port = int(os.environ.get("PORT", 10000))
    app.run(host='0.0.0.0', port=port)


def run_web_in_background():
    """Starts the Flask site on a daemon thread so it runs alongside the bot, which owns
    the main thread. Called once from main.py, after both bot.py and website.py have
    finished importing (i.e. every route and every bot command already exists)."""
    threading.Thread(target=run_web, daemon=True).start()

# ============================================================
# Process entry point — only runs when this file is executed directly
# (`python bot.py`), never when website.py imports it.
# ============================================================
if __name__ == "__main__":
    TOKEN = os.environ.get("DISCORD_TOKEN")
    if not TOKEN:
        raise RuntimeError("DISCORD_TOKEN environment variable is missing! Set it in Render under Environment.")

    init_db()
    run_web_in_background()
    bot.run(TOKEN)
