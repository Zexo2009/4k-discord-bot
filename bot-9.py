"""
bot.py — Zexo, all-in-one (everything except the Flask website): config/constants/storage,
the Discord bot instance, every command/event/job and embed builder, AND the process entry
point at the bottom (guarded by `if __name__ == "__main__":` so website.py can still safely
`from bot import *` without accidentally starting the bot a second time).

website.py imports from this module (constants, storage helpers, `bot`, and the job runners)
to power the web dashboard's manual trigger buttons and live status.
"""
import os
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
    changes for it. Any other server should override these via /setup."""
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


@bot.event
async def on_ready():
    print(f"✅ Zexo is online as {bot.user}")
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
    print(f"➕ Joined new server: {guild.name} ({guild.id}) — run /setup there to configure channels/roles.")


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
            sources_for_rating_hint = await extract_video_sources(message)
            if sources_for_rating_hint:
                hint_key_users = load_ai_rating_hinted_users(message.guild.id)
                if message.author.id not in hint_key_users:
                    mark_user_ai_rating_hinted(message.guild.id, message.author.id)
                    try:
                        await message.reply(
                            "💡 Want feedback on this edit? Right-click your message → Apps → "
                            "**Rate this Edit** for honest AI feedback (score, software guess, tips, "
                            "and a suggested skill tier). "
                            "(You'll only see this tip once.)",
                            mention_author=False,
                        )
                    except discord.HTTPException:
                        pass
            if not message_pings_role(message, picker_role):
                sources = await extract_video_sources(message)
                if sources:
                    reminded = load_reminded_users(message.guild.id)
                    if message.author.id not in reminded:
                        mark_user_reminded(message.guild.id, message.author.id)
                        default_reminder = (
                            f"👋 Heads up {{member}} — to have your edit count for "
                            f"voting, ping **@{PICKER_ROLE_NAME}** in the same message next time! "
                            "This edit won't be picked up since it wasn't pinged. "
                            "(You'll only see this reminder once.)"
                        )
                        reminder_text = (config.get("custom_reminder_message") or default_reminder).format(
                            member=message.author.mention
                        )
                        try:
                            await message.reply(reminder_text, mention_author=False)
                        except discord.HTTPException:
                            pass

    await bot.process_commands(message)


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
        "format": f"mp4/bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[filesize<{max_bytes}]/best",
        "outtmpl": out_path,
        "quiet": True,
        "no_warnings": True,
        "noplaylist": True,
        "max_filesize": max_bytes,
        "merge_output_format": "mp4",
    }
    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        ydl.download([url])


def _download_social_photos(url: str, max_images: int = 4) -> list[str]:
    """Best-effort fallback for TikTok/Instagram-style 'photo mode' posts (a slideshow of
    images with no actual video stream) — these fail the normal video download since there's
    no video to grab. Pulls the individual slide images straight from yt-dlp's metadata instead.
    Returns local JPEG paths (caller deletes them). Empty list on any failure."""
    ydl_opts = {"quiet": True, "no_warnings": True, "skip_download": True}
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
        print(f"⚠️ Video download failed for {url}: {e}")
        if os.path.exists(out_path):
            os.remove(out_path)
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


def _call_gemini_vision(frame_paths: list[str], prompt: str) -> str:
    """Sends the given frames + prompt to the free Gemini API and returns the text reply.
    Raises RuntimeError with a user-safe message on any failure."""
    if not GEMINI_API_KEY:
        raise RuntimeError("AI rating isn't configured yet — ask a server admin to set GEMINI_API_KEY (it's free, see setup notes).")

    parts = [{"text": prompt}]
    for path in frame_paths:
        with open(path, "rb") as f:
            b64 = base64.b64encode(f.read()).decode("utf-8")
        parts.append({"inline_data": {"mime_type": "image/jpeg", "data": b64}})

    resp = http_requests.post(
        f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_VISION_MODEL}:generateContent",
        params={"key": GEMINI_API_KEY},
        json={"contents": [{"parts": parts}]},
        timeout=60,
    )
    if resp.status_code != 200:
        print(f"⚠️ Gemini API error {resp.status_code}: {resp.text[:300]}")
        if resp.status_code == 404:
            reason = (
                f"model `{GEMINI_VISION_MODEL}` wasn't found (404) — the model name may be "
                "outdated/retired, or GEMINI_API_KEY belongs to a project without access to it."
            )
        elif resp.status_code == 403:
            reason = "access denied (403) — GEMINI_API_KEY is invalid or the API isn't enabled for that project."
        elif resp.status_code == 429:
            reason = "rate limit / free-tier quota exceeded (429) — try again in a minute."
        elif resp.status_code == 400:
            reason = "bad request (400) — check the request format or that the key itself is correctly formatted."
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


async def _get_video_path_from_message(message: discord.Message) -> str | None:
    """Best-effort: pulls a local mp4 path out of a message, either from a video
    attachment or the first social-video link found in its content. Returns None
    (and cleans up) if nothing usable was found. Caller is responsible for deleting
    the returned path when done."""
    for att in message.attachments:
        if att.content_type and att.content_type.startswith("video"):
            out_path = f"/tmp/rate_{random.randint(0, 10**9)}.mp4"
            await att.save(out_path)
            return out_path

    url_match = re.search(r"https?://\S+", message.content or "")
    if url_match and is_social_video_link(url_match.group(0)):
        return await download_social_video(url_match.group(0), message.guild)

    return None


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
        print(f"⚠️ Missing channel/role in guild {guild.name} — run /setup there first. Skipping.")
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
            "or give a link.\n\n"
            "**`aicaption [plattform] [thema]`** *(text-command, also `.aicaption`)*\n"
            "Attach/reply with a video or image (TikTok photo-posts included) to caption THAT, "
            "or type `.aicaption tiktok mein neues Setup` for a text-only topic. No arguments? "
            "It asks you step by step for platform and topic."
        ),
    },
    "staff": {
        "label": "🛠️ Staff Tools",
        "description": (
            "*Top Edit Picker Manager / Staff only — replies are only visible to you.*\n\n"
            "**`setup`** *(Admin only)*\n"
            "One-time setup: pick this server's channels and roles via dropdown menus.\n\n"
            "**`setupstatus`** *(Admin only)*\n"
            "Shows the current channel/role config for this server.\n\n"
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
            "website dashboard's Control Room."
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
    embed.set_footer(text="Run /help for the full command list. Server admins: /setup to configure channels & roles.")
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
    warning = "" if logged else f"\n⚠️ *Couldn't post to the points log channel — check it's configured (see /setup) and that the bot can see/send in it.*"
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
    warning = "" if logged else f"\n⚠️ *Couldn't post to the points log channel — check it's configured (see /setup) and that the bot can see/send in it.*"
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
        video_path = await _get_video_path_from_message(source_message)
        if not video_path:
            await ctx.send(
                "⚠️ Ich finde da kein Video — häng eins an, antworte (reply) auf eine "
                "Nachricht mit Video, oder gib einen Link mit: `.airating <link>`."
            )
            return

        frame_paths = []
        try:
            frame_paths = await asyncio.get_running_loop().run_in_executor(None, _extract_frames, video_path, 4)
            if not frame_paths:
                await ctx.send("⚠️ Konnte keine Frames aus dem Video extrahieren.")
                return
            feedback = await asyncio.get_running_loop().run_in_executor(
                None, _call_gemini_vision, frame_paths, RATE_EDIT_PROMPT
            )
            embed = discord.Embed(title="🎬 Edit Rating", description=feedback, color=discord.Color.purple())
            embed.set_footer(text="AI-generated feedback from a few sampled frames — take it as a starting point, not gospel.")
            await ctx.send(embed=embed)
        except RuntimeError as e:
            await ctx.send(f"⚠️ {e}")
        except Exception as e:
            print(f"⚠️ .airating failed: {e}")
            await ctx.send("⚠️ Etwas ist beim Rating schiefgelaufen. Versuch's gleich nochmal.")
        finally:
            if os.path.exists(video_path):
                os.remove(video_path)
            for fp in frame_paths:
                if os.path.exists(fp):
                    os.remove(fp)


@bot.command(name="aicaption", aliases=["aiCaption"])
async def aicaption_cmd(ctx, *, args: str = None):
    """Text-command version of /ai-caption — also works with an attached/replied video or image
    (then it captions THAT, like /youtube-tiktok-caption, instead of asking for a topic).
    Usage: `.aicaption <plattform> <thema>` (z.B. `.aicaption tiktok mein neues Setup`).
    Ohne Angaben fragt der Bot Schritt für Schritt nach."""
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
            await ctx.send("📱 Für welche Plattform? Antworte z. B. mit `tiktok`, `instagram`, `youtube`, `x` oder `allgemein`.")
            try:
                reply = await bot.wait_for("message", check=check, timeout=60)
            except asyncio.TimeoutError:
                await ctx.send("⌛ Zu lange keine Antwort — brich ab. Versuch's nochmal mit `.aicaption <plattform> <thema>`.")
                return
            platform_value = AI_CAPTION_PLATFORM_KEYWORDS.get(reply.content.strip().lower(), reply.content.strip())

        if not topic:
            await ctx.send("📝 Worum geht's? Beschreib kurz das Thema (oder häng jetzt ein Bild/Video an, dann beschreibe ich das).")
            try:
                reply = await bot.wait_for("message", check=check, timeout=90)
            except asyncio.TimeoutError:
                await ctx.send("⌛ Zu lange keine Antwort — brich ab.")
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
                await ctx.send(embed=_build_content_info_embed(parsed), view=view)
            else:
                prompt = AI_CAPTION_PROMPT_TEMPLATE.format(
                    platform=platform_value, topic=topic or "kein spezifisches Thema angegeben"
                )
                raw = await asyncio.get_running_loop().run_in_executor(None, _call_gemini_vision, [], prompt)
                parsed = _parse_content_info(raw)
                view = AICaptionView(topic or "", platform_value)
                await ctx.send(embed=_build_ai_caption_embed(parsed, platform_value), view=view)
        except RuntimeError as e:
            await ctx.send(f"⚠️ {e}")
        except Exception as e:
            print(f"⚠️ .aicaption failed: {e}")
            await ctx.send("⚠️ Etwas ist schiefgelaufen. Versuch's gleich nochmal.")


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


class SetupChannelsView(discord.ui.View):
    """Step 1 of /setup: pick the 3 channels the bot needs, using Discord's native channel picker."""

    def __init__(self, guild_id: int):
        super().__init__(timeout=300)
        self.guild_id = guild_id
        self.picked = {}

    @discord.ui.select(cls=discord.ui.ChannelSelect, channel_types=[discord.ChannelType.text],
                        placeholder="1. Submissions channel (where edits get posted)", row=0)
    async def submit_select(self, interaction: discord.Interaction, select: discord.ui.ChannelSelect):
        self.picked["submit_channel_id"] = select.values[0].id
        await interaction.response.defer()

    @discord.ui.select(cls=discord.ui.ChannelSelect, channel_types=[discord.ChannelType.text],
                        placeholder="2. Discussion channel (where votes get posted)", row=1)
    async def discussion_select(self, interaction: discord.Interaction, select: discord.ui.ChannelSelect):
        self.picked["discussion_channel_id"] = select.values[0].id
        await interaction.response.defer()

    @discord.ui.select(cls=discord.ui.ChannelSelect, channel_types=[discord.ChannelType.text],
                        placeholder="3. Results channel (where the winner is announced)", row=2)
    async def results_select(self, interaction: discord.Interaction, select: discord.ui.ChannelSelect):
        self.picked["results_channel_id"] = select.values[0].id
        await interaction.response.defer()

    @discord.ui.select(cls=discord.ui.ChannelSelect, channel_types=[discord.ChannelType.text],
                        placeholder="4. Points log channel (optional but recommended)", row=3)
    async def log_select(self, interaction: discord.Interaction, select: discord.ui.ChannelSelect):
        self.picked["log_channel_id"] = select.values[0].id
        await interaction.response.defer()

    @discord.ui.button(label="Save & continue to roles ▶", style=discord.ButtonStyle.success, row=4)
    async def save_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not all(k in self.picked for k in ("submit_channel_id", "discussion_channel_id", "results_channel_id")):
            await interaction.response.send_message("⚠️ Pick at least the first 3 channels before continuing.", ephemeral=True)
            return
        save_guild_config(self.guild_id, self.picked)
        for child in self.children:
            child.disabled = True
        await interaction.response.edit_message(content="✅ Channels saved! Now pick your roles:", view=self)
        role_view = SetupRolesView(self.guild_id)
        await interaction.followup.send(view=role_view, ephemeral=True)


class SetupRolesView(discord.ui.View):
    """Step 2 of /setup: pick the roles used for permissions and pings."""

    def __init__(self, guild_id: int):
        super().__init__(timeout=300)
        self.guild_id = guild_id
        self.picked = {}

    @discord.ui.select(cls=discord.ui.RoleSelect, placeholder="1. Picker role(s) (can vote / run /testcollect)",
                        min_values=0, max_values=10, row=0)
    async def picker_select(self, interaction: discord.Interaction, select: discord.ui.RoleSelect):
        self.picked["picker_role_ids"] = [r.id for r in select.values]
        await interaction.response.defer()

    @discord.ui.select(cls=discord.ui.RoleSelect, placeholder="2. Manager role(s) (can give/remove points)",
                        min_values=0, max_values=10, row=1)
    async def manager_select(self, interaction: discord.Interaction, select: discord.ui.RoleSelect):
        self.picked["manager_role_ids"] = [r.id for r in select.values]
        await interaction.response.defer()

    @discord.ui.select(cls=discord.ui.RoleSelect, placeholder="3. Staff role(s) (full permissions, optional)",
                        min_values=0, max_values=10, row=2)
    async def staff_select(self, interaction: discord.Interaction, select: discord.ui.RoleSelect):
        self.picked["staff_role_ids"] = [r.id for r in select.values]
        await interaction.response.defer()

    @discord.ui.select(cls=discord.ui.RoleSelect, placeholder="4. Role pinged when a winner is announced", row=3)
    async def top_edits_select(self, interaction: discord.Interaction, select: discord.ui.RoleSelect):
        self.picked["top_edits_role_id"] = select.values[0].id
        await interaction.response.defer()

    @discord.ui.button(label="Save setup ✅", style=discord.ButtonStyle.success, row=4)
    async def save_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not self.picked.get("picker_role_ids"):
            await interaction.response.send_message("⚠️ Pick at least one Picker role before saving.", ephemeral=True)
            return
        save_guild_config(self.guild_id, self.picked)
        for child in self.children:
            child.disabled = True
        await interaction.response.edit_message(
            content="✅ **Setup complete!** Zexo is now configured for this server. Run `/tutorial` to see the full walkthrough, or `/testcollect` to try a run.",
            view=self,
        )


@bot.tree.command(name="setup", description="Configure Zexo's channels and roles for this server (Admin only)")
async def slash_setup(interaction: discord.Interaction):
    if not interaction.user.guild_permissions.administrator:
        await interaction.response.send_message("❌ Only server admins can run setup.", ephemeral=True)
        return
    view = SetupChannelsView(interaction.guild.id)
    await interaction.response.send_message(
        "**Zexo Setup — Step 1/2: Channels**\nPick the channels below, then hit Save.",
        view=view,
        ephemeral=True,
    )


@bot.tree.command(name="setupstatus", description="Show this server's current Zexo configuration (Admin only)")
async def slash_setupstatus(interaction: discord.Interaction):
    if not interaction.user.guild_permissions.administrator:
        await interaction.response.send_message("❌ Only server admins can view this.", ephemeral=True)
        return
    config = load_guild_config(interaction.guild.id)
    guild = interaction.guild

    def fmt_channel(cid):
        ch = guild.get_channel(cid)
        return ch.mention if ch else f"⚠️ not found (ID `{cid}`)"

    def fmt_role(rid):
        r = guild.get_role(rid) if rid else None
        return r.mention if r else (f"⚠️ not found (ID `{rid}`)" if rid else "*not set*")

    def fmt_roles(rids):
        rids = rids or []
        if not rids:
            return "*not set*"
        mentions = [fmt_role(rid) for rid in rids]
        return ", ".join(mentions)

    embed = discord.Embed(title="⚙️ Zexo Setup Status", color=discord.Color.blurple())
    embed.add_field(name="Submissions channel", value=fmt_channel(config["submit_channel_id"]), inline=False)
    embed.add_field(name="Discussion channel", value=fmt_channel(config["discussion_channel_id"]), inline=False)
    embed.add_field(name="Results channel", value=fmt_channel(config["results_channel_id"]), inline=False)
    embed.add_field(name="Points log channel", value=fmt_channel(config["log_channel_id"]), inline=False)
    embed.add_field(name="Picker role(s)", value=fmt_roles(config["picker_role_ids"]), inline=True)
    embed.add_field(name="Manager role(s)", value=fmt_roles(config["manager_role_ids"]), inline=True)
    embed.add_field(name="Staff role(s)", value=fmt_roles(config["staff_role_ids"]), inline=True)
    embed.add_field(name="Top-Edits ping role", value=fmt_role(config["top_edits_role_id"]), inline=True)
    embed.set_footer(text="Run /setup to change any of these.")
    await interaction.response.send_message(embed=embed, ephemeral=True)


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
    warning = "" if logged else f"\n⚠️ *Couldn't post to the points log channel — check it's configured (see /setup) and that the bot can see/send in it.*"
    await interaction.response.send_message(f"✅ Added **{amount}** point(s) to {member.mention}. New total: **{new_total}**{warning}", ephemeral=True)


@bot.tree.command(name="removepoints", description="Remove points from a user (Top Edit Manager/Staff only)")
@app_commands.describe(member="User to remove points from", amount="How many points to remove")
async def slash_removepoints(interaction: discord.Interaction, member: discord.Member, amount: int):
    if not has_points_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Manager or Staff can use this.", ephemeral=True)
        return
    new_total = await award_points(interaction.guild, member.id, -amount)
    logged = await log_points_action(interaction.guild, interaction.user, member.id, amount, new_total, "remove")
    warning = "" if logged else f"\n⚠️ *Couldn't post to the points log channel — check it's configured (see /setup) and that the bot can see/send in it.*"
    await interaction.response.send_message(f"✅ Removed **{amount}** point(s) from {member.mention}. New total: **{new_total}**{warning}", ephemeral=True)


@bot.tree.command(name="testcollect", description="Manually run the collect-edits job (Picker/Manager/Staff only)")
async def slash_testcollect(interaction: discord.Interaction):
    if not has_picker_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Picker/Manager/Staff can use this.", ephemeral=True)
        return
    await interaction.response.send_message("⏳ Running collect job manually...")
    await run_collect_job()
    entries = get_poll_state(interaction.guild.id)["entries"]
    await interaction.followup.send(f"✅ Done. {len(entries)} edit(s) posted for voting.")


@bot.tree.command(name="testresults", description="Manually run the announce-winner job (Picker/Manager/Staff only)")
async def slash_testresults(interaction: discord.Interaction):
    if not has_picker_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Picker/Manager/Staff can use this.", ephemeral=True)
        return
    await interaction.response.send_message("⏳ Running results job manually...")
    await run_results_job()
    await interaction.followup.send("✅ Done.")



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

RATE_EDIT_PROMPT = (
    "You are an experienced video editor giving honest, constructive feedback on frames "
    "pulled from someone's edit. Based only on what's visible in these frames, write a short, "
    "direct review covering:\n"
    "1. An overall score out of 10 for visual polish (grading, sync/impact framing, composition).\n"
    "2. A skill tier that best fits this edit — pick exactly one of: Beginner, Intermediate, "
    "Advanced, Pro. Label it clearly as 'Skill tier: X'.\n"
    "3. Your best guess at what software was likely used (e.g. CapCut, Alight Motion, Premiere, "
    "After Effects) based on visual style — say clearly if you're not sure.\n"
    "4. 2-3 concrete, specific tips to improve.\n"
    "Be honest, not falsely encouraging — but stay constructive. Keep it under 170 words. "
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

    video_path = await _get_video_path_from_message(source_message)
    if not video_path:
        await interaction.followup.send(
            "⚠️ Couldn't find a video attachment or link on that message.", ephemeral=True
        )
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

    video_path = await _get_video_path_from_message(message)
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
            await interaction.edit_original_response(embed=_build_content_info_embed(parsed), view=self)
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
        await interaction.followup.send(embed=_build_content_info_embed(parsed), view=view)
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
            await interaction.edit_original_response(embed=_build_ai_caption_embed(parsed, self.platform), view=self)
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
    """True if the logged-in user has Administrator permission on this guild (matches the
    same gate /setup already uses in Discord, so nobody gets more power from the website
    than they'd have with the slash command)."""
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
      h1 {{ font-size:34px; font-weight:800; margin:24px 0 6px; }}
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
       -webkit-background-clip:text; background-clip:text; color:transparent; margin-bottom:4px; }
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
       text-shadow: 0 0 22px rgba(34,255,176,0.35); }
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
  h1 { font-size:1.9rem; font-weight:800; margin:0; letter-spacing:-0.01em; color:var(--accent); text-shadow:0 0 22px rgba(34,255,176,0.35); }
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
let fieldCount = 0;
function toast(msg, ok=true) {
  const t = document.getElementById('toast');
  t.textContent = msg;
  t.style.background = ok ? 'var(--accent)' : 'var(--danger)';
  t.classList.add('show');
  setTimeout(() => t.classList.remove('show'), 2200);
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
  renderPreview();
}
function escapeHtml(s) {
  return (s || '').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
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
  if (e.author_name) html += `<div class="preview-author">${e.author_icon_url ? `<img src="${e.author_icon_url}">` : ''}${escapeHtml(e.author_name)}</div>`;
  if (e.title) html += `<div class="preview-title">${escapeHtml(e.title)}</div>`;
  if (e.description) html += `<div class="preview-desc">${escapeHtml(e.description)}</div>`;
  if (e.fields.length) {
    html += '<div class="preview-fields">';
    e.fields.forEach(f => {
      html += `<div class="${f.inline ? '' : 'full'}"><div class="preview-field-name">${escapeHtml(f.name)}</div><div class="preview-field-value">${escapeHtml(f.value)}</div></div>`;
    });
    html += '</div>';
  }
  if (e.image_url) html += `<img class="preview-image" src="${e.image_url}">`;
  if (e.footer_text || e.timestamp) {
    html += `<div class="preview-footer">${e.footer_icon_url ? `<img src="${e.footer_icon_url}">` : ''}${escapeHtml(e.footer_text)}${e.timestamp ? (e.footer_text ? ' • ' : '') + 'Just now' : ''}</div>`;
  }
  html += '</div>';
  if (e.thumbnail_url) html += `<img class="preview-thumb" src="${e.thumbnail_url}">`;
  html += '</div>';
  document.getElementById('eb-preview').innerHTML = html;
}
['eb-content','eb-author','eb-author-icon','eb-title','eb-desc','eb-color','eb-timestamp','eb-thumb','eb-image','eb-footer','eb-footer-icon'].forEach(id => {
  document.getElementById(id).addEventListener('input', renderPreview);
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
    return render_template_string(
        EMBED_BUILDER_HTML,
        guild_id=guild_id,
        server_name=guild.name,
        channels=channels,
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
