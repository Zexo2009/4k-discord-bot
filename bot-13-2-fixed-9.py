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

# Anti-raid: known scam/phishing domain patterns (fake Discord Nitro, typosquatted Discord or
# Steam domains, etc.). Deliberately does NOT match ordinary discord.gg invites — those are
# legitimate most of the time, so blocking them outright would cause far more harm than good.
SCAM_LINK_REGEX = re.compile(
    r"(discord-?nitro\.(?!com\b)|discordgift\.|discord-?gift\.(?!com\b)|dlscord\.|discrod\.|discocl\."
    r"|discordapp-?nitro|dlscordapp\.|steamcommunlty\.|steamcomunity\.|stearncommunity\."
    r"|steancommunity\.|free-?nitro\S*\.(gg|com|net|xyz|ru|tk|cf|ml|ga)|nitro-?generator)",
    re.IGNORECASE,
)

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

# Anti-raid: a single bot being added is completely normal (staff adding a real bot) — it is
# never touched just for joining. What actually gets watched is NUKE/RAID BEHAVIOR: a bot
# rapid-firing channel creations, channel deletions, or message spam right after joining. The
# moment that pattern shows up, that specific bot gets timed out + kicked immediately, and
# whoever added it loses its roles and gets a 1-week timeout too.
NUKE_ACTION_THRESHOLD = 3        # this many rapid actions of the same kind...
NUKE_ACTION_WINDOW_SECONDS = 8    # ...within this many seconds = nuke pattern
NUKE_SPAM_MSG_THRESHOLD = 6
NUKE_SPAM_WINDOW_SECONDS = 6
_bot_action_times = {}  # (guild_id, user_id, action_name) -> list of timestamps
_bot_channel_create_events = {}  # (guild_id, user_id) -> list of {"channel_id", "time", "handled"}
_bot_channel_rename_events = {}  # (guild_id, user_id) -> list of {"channel_id", "old_name", "time", "handled"}
_channels_being_purged = set()  # channel IDs we're deleting ourselves as raid cleanup — on_guild_channel_delete skips recreating/punishing for these


def _record_and_check_nuke_pattern(guild_id: int, user_id: int, action: str, threshold: int, window_seconds: int) -> bool:
    """Records one action of this kind for this user and returns True the moment the count
    within the trailing time window reaches the threshold — i.e. the instant a nuke pattern
    is detected, not after the fact."""
    key = (guild_id, user_id, action)
    now = discord.utils.utcnow()
    times = _bot_action_times.setdefault(key, [])
    times[:] = [t for t in times if (now - t).total_seconds() <= window_seconds]
    times.append(now)
    return len(times) >= threshold


def _record_channel_create_event(guild_id: int, user_id: int, channel_id: int, window_seconds: int):
    """Same idea as _record_and_check_nuke_pattern, but also remembers WHICH channels were
    created so the burst of junk channels can be deleted once it's confirmed as a raid, not
    just stopped from growing further. Returns the live (pruned) event list for this user."""
    key = (guild_id, user_id)
    now = discord.utils.utcnow()
    events = _bot_channel_create_events.setdefault(key, [])
    events[:] = [e for e in events if (now - e["time"]).total_seconds() <= window_seconds]
    events.append({"channel_id": channel_id, "time": now, "handled": False})
    return events


def _record_channel_rename_event(guild_id: int, user_id: int, channel_id: int, old_name: str, window_seconds: int):
    """Same pattern as _record_channel_create_event, but for renames — remembers each
    channel's name from BEFORE the rename so a rename-spam attack (e.g. renaming every
    channel to something like 'nuked-by-x') can be reverted once confirmed, not just stopped
    from spreading further."""
    key = (guild_id, user_id)
    now = discord.utils.utcnow()
    events = _bot_channel_rename_events.setdefault(key, [])
    events[:] = [e for e in events if (now - e["time"]).total_seconds() <= window_seconds]
    events.append({"channel_id": channel_id, "old_name": old_name, "time": now, "handled": False})
    return events

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
        # Fully custom ranks: a list of {"name","threshold","emoji","role_id"} dicts, in any
        # order, any count. When this is non-empty it completely replaces the fixed D/C/B/A/S
        # system above (which stays only as the fallback default for servers that never
        # customized ranks).
        "custom_ranks": [],
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
    unranked_role_id = config.get("unranked_role_id")

    tiers = get_guild_rank_tiers(guild.id)
    all_tier_role_ids = {role_id for _threshold, role_id, _label, _emoji in tiers if role_id}
    target_role_id = current_rank_role_id(total_points, guild.id)
    desired_ids = set()
    if target_role_id and target_role_id != UNRANKED_ROLE_ID:
        desired_ids.add(target_role_id)
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
    """The (threshold, role_id, label, emoji) list for a server. If that server has set up
    fully-custom ranks (any names, any count, via the dashboard), those are used as-is —
    sorted by threshold. Otherwise falls back to the built-in fixed D/C/B/A/S system with
    that server's custom thresholds/emoji/roles layered on top. Pass no guild_id to get the
    raw defaults."""
    if guild_id is None:
        return RANK_TIERS
    config = load_guild_config(guild_id)
    custom_ranks = config.get("custom_ranks") or []
    if custom_ranks:
        tiers = [
            (r.get("threshold", 0), r.get("role_id", 0), r.get("name", "Rank"), r.get("emoji") or "🔸")
            for r in custom_ranks
        ]
        tiers.sort(key=lambda t: t[0])
        return tiers
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


async def punish_raider(guild: discord.Guild, user, reason: str):
    """Strips all roles and applies a 1-week timeout to whoever triggered an anti-raid action.
    Always-on, no per-server setup required. Skips the server owner (Discord's API won't let a
    bot timeout/role-strip the owner anyway, and it avoids ever locking an owner out of their
    own server on a false positive)."""
    if not isinstance(user, discord.Member) or user.id == guild.owner_id:
        return
    try:
        strippable = [r for r in user.roles if r != guild.default_role and r < guild.me.top_role]
        if strippable:
            await user.remove_roles(*strippable, reason=reason)
    except discord.Forbidden:
        print(f"⚠️ Anti-raid: missing permission to strip roles from {user} in {guild.name}")
    except discord.HTTPException as e:
        print(f"⚠️ Anti-raid: failed to strip roles from {user}: {e}")
    try:
        await user.timeout(discord.utils.utcnow() + timedelta(days=7), reason=reason)
    except discord.Forbidden:
        print(f"⚠️ Anti-raid: missing permission to timeout {user} in {guild.name}")
    except discord.HTTPException as e:
        print(f"⚠️ Anti-raid: failed to timeout {user}: {e}")


async def handle_nuke_bot_detected(guild: discord.Guild, bot_member: discord.Member, reason: str):
    """A bot just showed an actual nuke/raid pattern (mass channel create/delete or message
    spam). Timeout first — an instant, unconditional lock that stops it from doing anything
    else even if the ban call is briefly delayed — then BAN it (not just kick, so it can't
    just get re-invited a second later), then punish whoever added it."""
    print(f"🚨 Anti-raid: nuke pattern detected from {bot_member} in {guild.name} — {reason}")
    try:
        await bot_member.timeout(discord.utils.utcnow() + timedelta(days=7), reason=reason)
    except discord.Forbidden:
        print(f"⚠️ Anti-raid: missing 'Moderate Members' permission in {guild.name} — could not timeout {bot_member}.")
    except discord.HTTPException as e:
        print(f"⚠️ Anti-raid: failed to timeout {bot_member}: {e}")
    try:
        await guild.ban(bot_member, reason=reason, delete_message_seconds=0)
    except discord.Forbidden:
        print(f"⚠️ Anti-raid: missing 'Ban Members' permission in {guild.name} — could not ban {bot_member}.")
    except discord.HTTPException as e:
        print(f"⚠️ Anti-raid: failed to ban {bot_member}: {e}")

    adder = None
    try:
        async for entry in guild.audit_logs(limit=10, action=discord.AuditLogAction.bot_add):
            if entry.target and entry.target.id == bot_member.id:
                adder = entry.user
                break
    except discord.Forbidden:
        pass
    if adder:
        await punish_raider(guild, adder, reason=f"Automatic anti-raid: added a bot that started raiding ({reason})")


@bot.event
async def on_member_join(member: discord.Member):
    # A bot joining is never acted on by itself — only actual nuke/raid BEHAVIOR afterward
    # (see on_guild_channel_create/delete and on_message below) triggers anything.
    if member.bot:
        return

    # Add the new member to the leaderboard right away (0 points) so the total
    # editor count and rankings update immediately, without waiting for their first point.
    data = load_points(member.guild.id)
    uid = str(member.id)
    if uid not in data:
        data[uid] = 0
        save_points(member.guild.id, data)
    resolved_names[uid] = member.display_name


@bot.event
async def on_guild_channel_update(before, after):
    # A third nuke-bot signature, alongside mass create/delete: renaming every channel to
    # something like "nuked-by-x" instead of deleting them outright. Same burst detection —
    # a single rename (a mod tidying up channel names) is ignored; only a rapid-fire burst
    # from a bot gets reverted.
    if before.name == after.name:
        return
    guild = after.guild
    editor = None
    try:
        async for entry in guild.audit_logs(limit=5, action=discord.AuditLogAction.channel_update):
            if entry.target and entry.target.id == after.id:
                editor = entry.user
                break
    except discord.Forbidden:
        return
    if not editor or not editor.bot or not bot.user or editor.id == bot.user.id:
        return

    events = _record_channel_rename_event(guild.id, editor.id, after.id, before.name, NUKE_ACTION_WINDOW_SECONDS)
    if len(events) >= NUKE_ACTION_THRESHOLD:
        to_restore = [e for e in events if not e["handled"]]
        for e in events:
            e["handled"] = True

        editor_member = guild.get_member(editor.id)
        if editor_member:
            await handle_nuke_bot_detected(guild, editor_member, reason="mass channel renaming (nuke pattern)")

        for e in to_restore:
            ch = guild.get_channel(e["channel_id"])
            if ch is None:
                continue
            try:
                await ch.edit(name=e["old_name"], reason="Automatic anti-raid: restoring the channel name after a rename-spam attack")
            except (discord.Forbidden, discord.HTTPException) as err:
                print(f"⚠️ Anti-raid: failed to restore name for channel {ch.id}: {err}")


async def _delete_raid_channel(guild: discord.Guild, channel_id: int):
    raid_channel = guild.get_channel(channel_id)
    if raid_channel is None:
        return
    _channels_being_purged.add(channel_id)
    try:
        await raid_channel.delete(reason="Automatic anti-raid: removing a channel created by a nuke bot")
    except (discord.Forbidden, discord.HTTPException) as e:
        _channels_being_purged.discard(channel_id)
        print(f"⚠️ Anti-raid: failed to delete raid channel '{raid_channel.name}': {e}")


@bot.event
async def on_guild_channel_create(channel):
    # The other half of a nuke bot's pattern: instead of deleting channels, some nuke bots
    # flood the server with junk channels. Same detection approach as deletion above — but
    # here we also clean up the actual junk channels once the pattern is confirmed, not just
    # stop it from growing.
    guild = channel.guild
    creator = None
    try:
        async for entry in guild.audit_logs(limit=5, action=discord.AuditLogAction.channel_create):
            if entry.target and entry.target.id == channel.id:
                creator = entry.user
                break
    except discord.Forbidden:
        return
    if not creator or not creator.bot or not bot.user or creator.id == bot.user.id:
        return

    events = _record_channel_create_event(guild.id, creator.id, channel.id, NUKE_ACTION_WINDOW_SECONDS)
    if len(events) >= NUKE_ACTION_THRESHOLD:
        to_delete = [e["channel_id"] for e in events if not e["handled"]]
        for e in events:
            e["handled"] = True

        # Delete every junk channel AND ban/timeout the bot all at the same time instead of
        # one after another — each of those is a separate Discord API round-trip, so doing
        # them sequentially was the main reason cleanup felt slow.
        tasks = [asyncio.create_task(_delete_raid_channel(guild, cid)) for cid in to_delete]
        creator_member = guild.get_member(creator.id)
        if creator_member:
            tasks.append(asyncio.create_task(handle_nuke_bot_detected(guild, creator_member, reason="mass channel creation (nuke pattern)")))
        if tasks:
            await asyncio.gather(*tasks, return_exceptions=True)


@bot.event
async def on_guild_channel_delete(channel):
    # Anti-raid: automatically rebuild any channel that gets deleted, with the same name,
    # position, category, and permission overwrites — and punish whoever deleted it, the same
    # way as an unauthorized bot add. EXCEPT when we deleted it ourselves as raid cleanup
    # (see on_guild_channel_create above) — recreating a junk channel we just removed on
    # purpose would defeat the whole point.
    if channel.id in _channels_being_purged:
        _channels_being_purged.discard(channel.id)
        return

    guild = channel.guild
    reason = "Automatic anti-raid: recreating a deleted channel"
    new_channel = None
    try:
        if isinstance(channel, discord.TextChannel):
            new_channel = await guild.create_text_channel(
                name=channel.name, category=channel.category, position=channel.position,
                overwrites=channel.overwrites, topic=channel.topic, nsfw=channel.nsfw,
                slowmode_delay=channel.slowmode_delay, reason=reason,
            )
        elif isinstance(channel, discord.VoiceChannel):
            new_channel = await guild.create_voice_channel(
                name=channel.name, category=channel.category, position=channel.position,
                overwrites=channel.overwrites, bitrate=channel.bitrate, user_limit=channel.user_limit, reason=reason,
            )
        elif isinstance(channel, discord.CategoryChannel):
            new_channel = await guild.create_category(
                name=channel.name, position=channel.position, overwrites=channel.overwrites, reason=reason,
            )
        elif isinstance(channel, discord.ForumChannel):
            new_channel = await guild.create_forum(
                name=channel.name, category=channel.category, position=channel.position,
                overwrites=channel.overwrites, topic=channel.topic or None, reason=reason,
            )
        elif isinstance(channel, discord.StageChannel):
            new_channel = await guild.create_stage_channel(
                name=channel.name, category=channel.category, position=channel.position,
                overwrites=channel.overwrites, reason=reason,
            )
    except discord.Forbidden:
        print(f"⚠️ Anti-raid: missing permission to recreate deleted channel '{channel.name}' in {guild.name}.")
    except discord.HTTPException as e:
        print(f"⚠️ Anti-raid: failed to recreate channel '{channel.name}': {e}")

    if isinstance(new_channel, discord.TextChannel):
        try:
            await new_channel.send("🛡️ This channel was deleted and has been automatically restored by Zexo's anti-raid protection.")
        except discord.HTTPException:
            pass

    deleter = None
    try:
        async for entry in guild.audit_logs(limit=5, action=discord.AuditLogAction.channel_delete):
            if entry.target and entry.target.id == channel.id:
                deleter = entry.user
                break
    except discord.Forbidden:
        pass

    if deleter and deleter.bot and bot.user and deleter.id != bot.user.id:
        # Bot rapid-deleting channels is a classic nuke signature — check the pattern, not
        # just this one deletion.
        if _record_and_check_nuke_pattern(guild.id, deleter.id, "channel_delete", NUKE_ACTION_THRESHOLD, NUKE_ACTION_WINDOW_SECONDS):
            deleter_member = guild.get_member(deleter.id)
            if deleter_member:
                await handle_nuke_bot_detected(guild, deleter_member, reason="mass channel deletion (nuke pattern)")
    elif deleter:
        await punish_raider(guild, deleter, reason="Automatic anti-raid: deleted a server channel")


@bot.event
async def on_guild_join(guild: discord.Guild):
    print(f"➕ Joined new server: {guild.name} ({guild.id}) — configure it on the website dashboard's Settings page.")


@bot.event
async def on_message(message: discord.Message):
    # Anti-raid: a bot rapid-firing messages (the third classic nuke-bot signature, alongside
    # mass channel create/delete above) gets timed out + kicked immediately, adder punished too.
    if message.guild and message.author.bot and bot.user and message.author.id != bot.user.id:
        if _record_and_check_nuke_pattern(message.guild.id, message.author.id, "message", NUKE_SPAM_MSG_THRESHOLD, NUKE_SPAM_WINDOW_SECONDS):
            member_obj = message.guild.get_member(message.author.id)
            if member_obj:
                await handle_nuke_bot_detected(message.guild, member_obj, reason="mass message spam (nuke pattern)")
            return

    # Anti-raid: auto-delete messages matching known scam/phishing link patterns (fake nitro,
    # typosquatted Discord/Steam domains, etc.) — always on, no setup. This intentionally does
    # NOT touch ordinary discord.gg invite links, since those are legitimate most of the time;
    # it only matches known scam-domain patterns.
    if message.guild and not message.author.bot and message.content:
        if SCAM_LINK_REGEX.search(message.content):
            try:
                await message.delete()
            except (discord.Forbidden, discord.NotFound):
                pass
            try:
                await message.channel.send(
                    f"🛡️ A message from {message.author.mention} was automatically removed — it matched a known scam/phishing pattern.",
                    delete_after=8,
                )
            except discord.HTTPException:
                pass
            return

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
    the message itself and any forwarded snapshots (falling back to a raw API read of the
    snapshot if discord.py didn't model it — see _raw_message_snapshots).
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


async def message_pings_role_async(msg: discord.Message, role: discord.Role) -> bool:
    """Same as message_pings_role, but also falls back to a raw API read of the forward
    snapshot when discord.py's modeled message_snapshots came back empty. Use this in the
    actual collect job; the sync version stays available for any call site that can't await."""
    if message_pings_role(msg, role):
        return True
    token = f"<@&{role.id}>"
    if not getattr(msg, "message_snapshots", None) and getattr(msg, "reference", None) is not None:
        for raw_snap in await _raw_message_snapshots(msg):
            snap_msg = raw_snap.get("message", {}) or {}
            if token in (snap_msg.get("content") or ""):
                return True
            for mention_role_id in snap_msg.get("mention_roles", []) or []:
                if str(mention_role_id) == str(role.id):
                    return True
    return False


async def _raw_message_snapshots(msg: discord.Message):
    """Low-level fallback for forwarded-message content: asks Discord's REST API directly
    for this message's raw JSON and pulls message_snapshots out of it by hand.

    discord.py's Message.message_snapshots relies on the installed library version having
    fully modeled Discord's (comparatively new) Message Forwarding feature. If that version
    doesn't — or models it slightly differently than expected — msg.message_snapshots can
    come back empty even though Discord's actual API response for that message DOES contain
    the forwarded content. Going straight to the raw HTTP response sidesteps that entirely:
    it reads exactly what Discord sent, regardless of what the installed library understood."""
    try:
        raw = await msg._state.http.get_message(msg.channel.id, msg.id)
    except Exception:
        return []
    return raw.get("message_snapshots") or []


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

    if not getattr(msg, "message_snapshots", None) and getattr(msg, "reference", None) is not None:
        for raw_snap in await _raw_message_snapshots(msg):
            snap_msg = raw_snap.get("message", {}) or {}
            for attachment in snap_msg.get("attachments", []) or []:
                if attachment.get("url"):
                    sources.append((attachment["url"], msg.author))
            for word in (snap_msg.get("content") or "").split():
                if word.startswith("http://") or word.startswith("https://"):
                    sources.append((word, msg.author))
            for embed in snap_msg.get("embeds", []) or []:
                if embed.get("url"):
                    sources.append((embed["url"], msg.author))
                video = embed.get("video") or {}
                if video.get("url"):
                    sources.append((video["url"], msg.author))

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
        if not await message_pings_role_async(msg, picker_role):
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
        if not await message_pings_role_async(msg, picker_role):
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
    tier_lines = "\n".join(f"{emoji} **{label}** — from **{threshold}** points" for threshold, _rid, label, emoji in get_guild_rank_tiers(guild.id))
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


def build_ranks_embed(guild_id: int = None):
    embed = discord.Embed(
        title="🏅 Editor Rankings",
        description=(
            "Earn points by winning **Top Edit of the Day** (+1 point automatically) "
            "or through tournaments (awarded manually by a Top Edit Manager/Staff).\n\u200b"
        ),
        color=discord.Color.blurple(),
    )
    tiers = get_guild_rank_tiers(guild_id)
    embed.add_field(
        name=f"{UNRANKED_EMOJI} Unranked",
        value=f"0 – {tiers[0][0] - 1 if tiers else 9} points\n*Everyone starts here.*",
        inline=True,
    )
    for idx, (threshold, _role_id, label, emoji) in enumerate(tiers):
        next_index = idx + 1
        upper = f"{tiers[next_index][0] - 1}" if next_index < len(tiers) else "∞"
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
    await ctx.send(embed=build_ranks_embed(ctx.guild.id if ctx.guild else None))


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
    await interaction.response.send_message(embed=build_ranks_embed(interaction.guild.id if interaction.guild else None))


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
#
# The cache has a short TTL (not "forever") — a permanent cache meant a server you created or
# joined AFTER logging in never showed up on the dashboard until the bot process happened to
# restart, since nothing ever invalidated the entry. A few minutes is enough to avoid hammering
# Discord's API on every page load while still picking up new servers quickly.
_user_guild_cache = {}  # user_id (str) -> {"guilds": [...], "fetched_at": datetime}
USER_GUILD_CACHE_TTL_SECONDS = 180


def fetch_user_guilds(user_id: str, access_token: str, force_refresh: bool = False):
    cached = _user_guild_cache.get(user_id)
    if cached is not None and not force_refresh:
        age = (datetime.now(timezone.utc) - cached["fetched_at"]).total_seconds()
        if age < USER_GUILD_CACHE_TTL_SECONDS:
            return cached["guilds"]
    res = http_requests.get(
        f"{DISCORD_API}/users/@me/guilds",
        headers={"Authorization": f"Bearer {access_token}"},
        timeout=10,
    )
    if res.status_code != 200:
        # Discord hiccup / rate limit — serve the last known list rather than wiping the
        # dashboard down to nothing.
        return cached["guilds"] if cached is not None else []
    guilds = [
        {"id": g["id"], "name": g["name"], "permissions": g.get("permissions", "0"), "icon": g.get("icon")}
        for g in res.json()
    ]
    _user_guild_cache[user_id] = {"guilds": guilds, "fetched_at": datetime.now(timezone.utc)}
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
    _user_guild_cache[str(user.get("id"))] = {"guilds": guilds, "fetched_at": datetime.now(timezone.utc)}

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


def user_guilds(user=None, force_refresh: bool = False):
    """The (possibly cached) list of guilds for the logged-in user — never trust
    session["user"]["guilds"], that key no longer exists; always go through this."""
    user = user or current_user()
    if not user:
        return []
    return fetch_user_guilds(str(user["id"]), user.get("access_token", ""), force_refresh=force_refresh)


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
          <div class="card reveal"><div class="icon-node">🛡️</div><h3>Anti-raid protection</h3>
            <p>Runs automatically, zero setup — watches for actual raid behavior and shuts it down in seconds. <a href="#antiraid" style="color:#c4b5fd;">See how ↓</a></p></div>
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

      <section id="antiraid">
        <h2 class="reveal">🛡️ Anti-raid protection</h2>
        <div class="sub reveal">Always on. No setup, no toggle, no command — it just watches.</div>
        <div class="steps">
          <div class="step reveal"><div class="num">👀</div><div class="txt">
            <h4>It watches behavior, not just events</h4><p>Adding a bot is never punished by itself — staff add real bots all the time. Zexo only reacts once a bot actually starts <b>doing</b> raid things.</p></div></div>
          <div class="step reveal"><div class="num">🚨</div><div class="txt">
            <h4>It looks for the raid signature</h4><p>Spamming channels into existence, mass-deleting channels, renaming everything to something like "nuked-by-x", or flooding messages — a real burst of any of these in a few seconds is what triggers it.</p></div></div>
          <div class="step reveal"><div class="num">⚡</div><div class="txt">
            <h4>The bot gets shut down instantly</h4><p>The offending bot is timed out and <b>banned</b> the moment the pattern is confirmed — not just kicked, so it can't be re-invited a second later.</p></div></div>
          <div class="step reveal"><div class="num">🧹</div><div class="txt">
            <h4>The damage gets undone</h4><p>Junk channels it created are deleted, channels it deleted are rebuilt (name, permissions, position — everything, including forum channels), and any names it changed get reverted automatically.</p></div></div>
          <div class="step reveal"><div class="num">🔗</div><div class="txt">
            <h4>Whoever added it gets punished too</h4><p>Zexo checks the audit log for who added the raid bot, strips every role from them, and times them out for a week — automatically.</p></div></div>
        </div>
        <div class="sub" style="margin-top:22px;">Needs the Kick, Ban, Timeout, Manage Roles, Manage Channels and View Audit Log permissions to act — everything else (scam-link deletion, etc.) needs nothing extra.</div>
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

      <script src="https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js" defer></script>
      <script defer>
  function initStaffCarousel(){
    const team = [
      { name: "Zexo", role: "Owner", age: 17, country: "Turkey", hobbies: ["Sport", "Editing"], img: "data:image/jpeg;base64,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", color: "#00ffff", bg: "#0d2b45" },
      { name: "Mayto", role: "Owner", age: 16, country: "Syria", hobbies: ["Gaming", "Editing"], img: "data:image/jpeg;base64,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", color: "#9d4edd", bg: "#240046" },
      { name: "Arya", role: "Co-Founder", age: 18, country: "India", hobbies: ["Editing", "Coding"], img: "data:image/jpeg;base64,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", color: "#ff0055", bg: "#4a001f" },
      { name: "Prizm Aultrim", role: "Co-Founder", age: 15, country: "India", hobbies: ["Editing", "Sport"], img: "data:image/jpeg;base64,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", color: "#00ff88", bg: "#003820" },
      { name: "Specter", role: "Chief Admin", age: 14, country: "India", hobbies: ["Gaming"], img: "data:image/jpeg;base64,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", color: "#0088ff", bg: "#002b5c" }
    ];

    let currentIndex = 0;
    let lastBlinkUpdate = 0;
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

      // Throttled to ~10 updates/sec instead of every single frame — redrawing 5 full
      // textures at 60fps was heavy enough to make mobile browsers feel sluggish.
      if (time - lastBlinkUpdate > 0.1) {
        lastBlinkUpdate = time;
        const blinkAlpha = 0.35 + 0.65 * ((Math.sin(time * 4) + 1) / 2);
        cards.forEach(({ ctx, texture, badge, member }) => {
          ctx.putImageData(badge.snapshot, badge.x - 4, badge.y - 4);
          drawRoleBadge(ctx, member, badge.x, badge.y, badge.w, badge.h, blinkAlpha);
          texture.needsUpdate = true;
        });
      }

      renderer.render(scene, camera);
    }
    animateStaff();
  }
      </script>

      <script>
        // Lazy-init: three.js and the whole carousel only spin up once the
        // staff section is actually about to scroll into view, so the initial
        // page load stays fast even though this feature is heavy.
        document.addEventListener('DOMContentLoaded', function () {
          const el = document.getElementById('staff');
          if (!el || typeof IntersectionObserver === 'undefined') { initStaffCarousel(); return; }
          const io = new IntersectionObserver(function (entries) {
            entries.forEach(function (entry) {
              if (entry.isIntersecting) {
                io.disconnect();
                initStaffCarousel();
              }
            });
          }, { rootMargin: '400px' });
          io.observe(el);
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
    <div style="display:flex; gap:10px; align-items:center;">
      <a class="logout" href="/servers?refresh=1" title="Don't see a server you just created or joined? Click this.">🔄 Refresh list</a>
      <a class="logout" href="/logout">Log out</a>
    </div>
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

    force_refresh = request.args.get("refresh") == "1"
    servers = []
    for g in user_guilds(user, force_refresh=force_refresh):
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
  .row4 { display:grid; grid-template-columns:2fr 1fr 1fr 1.6fr; gap:16px; }
  @media (max-width:700px){ .row4{ grid-template-columns:1fr 1fr; } }
  #addRankBtn { width:auto; margin-top:10px; padding:10px 22px; font-size:0.85rem; }
  .btn-remove-rank { width:auto; margin:10px 0 12px; padding:7px 16px; font-size:0.75rem; font-weight:600;
    background:rgba(239,68,68,0.15); border:1px solid rgba(248,113,113,0.4); color:#f87171;
    border-radius:999px; cursor:pointer; }
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
      <div id="rankRows">
        {% for threshold, role_id, tier_label, emoji in rank_tiers %}
        <div class="tier-edit rank-row">
          <div class="row4">
            <div>
              <label>Rank name</label>
              <input type="text" name="rank_name[]" maxlength="30" value="{{ tier_label }}" placeholder="e.g. Bronze">
            </div>
            <div>
              <label>Points needed</label>
              <input type="number" name="rank_threshold[]" min="0" max="100000" value="{{ threshold }}">
            </div>
            <div>
              <label>Emoji</label>
              <input type="text" name="rank_emoji[]" maxlength="8" value="{{ emoji }}">
            </div>
            <div>
              <label>Role</label>
              <select name="rank_role[]">
                <option value="0">— none —</option>
                {% for r in roles %}<option value="{{ r.id }}" {% if r.id == role_id %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
              </select>
            </div>
          </div>
          <button type="button" class="btn-remove-rank" onclick="this.closest('.rank-row').remove()">✕ Remove rank</button>
        </div>
        {% endfor %}
      </div>
      <button type="button" class="btn" id="addRankBtn">+ Add rank</button>
      <template id="rankRowTemplate">
        <div class="tier-edit rank-row">
          <div class="row4">
            <div>
              <label>Rank name</label>
              <input type="text" name="rank_name[]" maxlength="30" value="" placeholder="e.g. Bronze">
            </div>
            <div>
              <label>Points needed</label>
              <input type="number" name="rank_threshold[]" min="0" max="100000" value="0">
            </div>
            <div>
              <label>Emoji</label>
              <input type="text" name="rank_emoji[]" maxlength="8" value="🔸">
            </div>
            <div>
              <label>Role</label>
              <select name="rank_role[]">
                <option value="0">— none —</option>
                {% for r in roles %}<option value="{{ r.id }}">@{{ r.name }}</option>{% endfor %}
              </select>
            </div>
          </div>
          <button type="button" class="btn-remove-rank" onclick="this.closest('.rank-row').remove()">✕ Remove rank</button>
        </div>
      </template>
      <script>
        document.getElementById('addRankBtn').addEventListener('click', function () {
          const tpl = document.getElementById('rankRowTemplate');
          const clone = tpl.content.cloneNode(true);
          document.getElementById('rankRows').appendChild(clone);
        });
      </script>
      <div class="hint">💡 Add, remove, rename, and reorder ranks freely — the rank order is decided by "points needed", not by the order of the boxes above.</div>
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
        names = request.form.getlist("rank_name[]")
        thresholds = request.form.getlist("rank_threshold[]")
        emojis = request.form.getlist("rank_emoji[]")
        role_picks = request.form.getlist("rank_role[]")
        custom_ranks = []
        for i in range(len(names)):
            name = (names[i] if i < len(names) else "").strip()[:30]
            if not name:
                continue
            try:
                threshold_val = int(thresholds[i]) if i < len(thresholds) else 0
            except (ValueError, IndexError):
                threshold_val = 0
            threshold_val = max(0, min(100000, threshold_val))
            emoji_val = ((emojis[i] if i < len(emojis) else "") or "🔸").strip()[:8] or "🔸"
            try:
                role_val = int(role_picks[i]) if i < len(role_picks) else 0
            except (ValueError, IndexError):
                role_val = 0
            if role_val not in role_ids:
                role_val = 0
            custom_ranks.append({"name": name, "threshold": threshold_val, "emoji": emoji_val, "role_id": role_val})
        updates["custom_ranks"] = custom_ranks
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
