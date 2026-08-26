"""
config.py — Zexo shared config, constants, and storage.

Everything here is used by BOTH bot.py (the Discord side) and website.py (the Flask
dashboard) — DB access, per-guild settings, points/ranks/day-counter/video-history/badwords
storage, and small bits of shared runtime state (dashboard_state, resolved_names, etc).

This module never imports bot.py or website.py, so both of them can import *this* freely
without any circular-import issues.
"""
import os
import json
import re
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

import discord
import psycopg2

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


def _member_has_role(member: discord.Member, role_id: int, role_name: str) -> bool:
    if role_id and any(r.id == role_id for r in member.roles):
        return True
    return any(role.name == role_name for role in member.roles)


def has_picker_permission(member: discord.Member) -> bool:
    """Top Edit Picker, Manager, Staff, or admin: everything except giving/removing points."""
    if member.guild_permissions.administrator:
        return True
    config = load_guild_config(member.guild.id)
    return (
        _member_has_role(member, config["picker_role_id"], PICKER_ROLE_NAME)
        or _member_has_role(member, config["manager_role_id"], MANAGER_ROLE_NAME)
        or _member_has_role(member, config["staff_role_id"], STAFF_ROLE_NAME)
    )


def has_points_permission(member: discord.Member) -> bool:
    """Only Top Edit Picker Manager, Staff, or admin can give/remove points."""
    if member.guild_permissions.administrator:
        return True
    config = load_guild_config(member.guild.id)
    return (
        _member_has_role(member, config["manager_role_id"], MANAGER_ROLE_NAME)
        or _member_has_role(member, config["staff_role_id"], STAFF_ROLE_NAME)
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

def get_db_connection():
    return psycopg2.connect(DATABASE_URL, sslmode="require")


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
        print("✅ Connected to database — points will persist across restarts/redeploys.")
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
        "picker_role_id": PICKER_ROLE_ID,
        "manager_role_id": MANAGER_ROLE_ID,
        "staff_role_id": STAFF_ROLE_ID,
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


