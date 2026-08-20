import os
import json
import random
import threading
import asyncio
import re
from io import BytesIO
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

from flask import Flask, render_template_string
import discord
from discord import app_commands
from discord.ext import commands, tasks
from PIL import Image, ImageDraw, ImageFont
import psycopg2

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
MAX_POLL_ANSWERS = 10

WINNER_POINTS = 1
VIDEO_DEDUPE_DAYS = 5  # same video URL can't be counted again within this window

POINTS_FILE = "points.json"
DAY_FILE = "day_counter.json"
VIDEO_HISTORY_FILE = "video_history.json"
LAST_COLLECT_FILE = "last_collect.json"

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

app = Flask(__name__)

# Shared, thread-safe-ish state the Flask dashboard reads from
dashboard_state = {
    "guild_name": None,
    "member_count": 0,
}


@app.route('/')
def home():
    return """
    <!DOCTYPE html><html><head><meta charset="UTF-8">
    <title>Zexo</title>
    <style>
      body { margin:0; min-height:100vh; display:flex; align-items:center; justify-content:center;
             background:radial-gradient(circle at top,#1a1a2e,#0b0b12 60%); font-family:'Segoe UI',Arial,sans-serif; color:#f4f4f8; }
      .box { text-align:center; }
      h1 { font-size:2.2rem; background:linear-gradient(90deg,#8b5cf6,#f59e0b); -webkit-background-clip:text; background-clip:text; color:transparent; }
      a { display:inline-block; margin-top:12px; padding:10px 22px; border-radius:999px;
          background:linear-gradient(90deg,#8b5cf6,#f59e0b); color:#fff; text-decoration:none; font-weight:600; }
    </style></head>
    <body><div class="box"><h1>⚡ Zexo is online</h1><a href="/dashboard">Open Dashboard →</a></div></body></html>
    """


DASHBOARD_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Zexo Dashboard</title>
<style>
  :root {
    --bg: #0b0b12;
    --card: #14141f;
    --accent: #8b5cf6;
    --accent2: #f59e0b;
    --text: #f4f4f8;
    --muted: #9a9ab0;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    font-family: 'Segoe UI', Roboto, Arial, sans-serif;
    background: radial-gradient(circle at top, #1a1a2e, var(--bg) 60%);
    color: var(--text);
    padding: 32px 16px 64px;
  }
  h1 {
    text-align: center;
    font-size: 2.4rem;
    margin-bottom: 4px;
    background: linear-gradient(90deg, var(--accent), var(--accent2));
    -webkit-background-clip: text;
    background-clip: text;
    color: transparent;
  }
  .subtitle { text-align: center; color: var(--muted); margin-bottom: 32px; }
  .grid {
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(220px, 1fr));
    gap: 16px;
    max-width: 1100px;
    margin: 0 auto 32px;
  }
  .stat-card {
    background: var(--card);
    border: 1px solid #26263a;
    border-radius: 14px;
    padding: 18px 20px;
    box-shadow: 0 4px 18px rgba(0,0,0,0.35);
  }
  .stat-card .label { color: var(--muted); font-size: 0.8rem; text-transform: uppercase; letter-spacing: 0.05em; }
  .stat-card .value { font-size: 1.8rem; font-weight: 700; margin-top: 4px; }
  .section {
    max-width: 1100px;
    margin: 0 auto 32px;
    background: var(--card);
    border: 1px solid #26263a;
    border-radius: 14px;
    padding: 20px 24px;
  }
  .section h2 { margin-top: 0; font-size: 1.3rem; }
  table { width: 100%; border-collapse: collapse; }
  th, td { text-align: left; padding: 10px 8px; border-bottom: 1px solid #26263a; }
  th { color: var(--muted); font-size: 0.78rem; text-transform: uppercase; letter-spacing: 0.04em; }
  tr:last-child td { border-bottom: none; }
  .rank-pill {
    display: inline-block;
    padding: 2px 10px;
    border-radius: 999px;
    font-weight: 600;
    font-size: 0.8rem;
    background: linear-gradient(90deg, var(--accent), var(--accent2));
  }
  .footer { text-align: center; color: var(--muted); font-size: 0.8rem; margin-top: 40px; }
  .medal { font-size: 1.1rem; }
</style>
</head>
<body>
  <h1>⚡ Zexo Dashboard</h1>
  <div class="subtitle">Live stats for the Top Edit voting system</div>

  <div class="grid">
    <div class="stat-card"><div class="label">Status</div><div class="value">🟢 Online</div></div>
    <div class="stat-card"><div class="label">Uptime</div><div class="value">{{ uptime }}</div></div>
    <div class="stat-card"><div class="label">Servers</div><div class="value">{{ server_count }}</div></div>
    <div class="stat-card"><div class="label">Members reachable</div><div class="value">{{ member_count }}</div></div>
    <div class="stat-card"><div class="label">Current day</div><div class="value">#{{ day_number }}</div></div>
    <div class="stat-card"><div class="label">discord.py</div><div class="value">{{ dpy_version }}</div></div>
  </div>

  <div class="section">
    <h2>🏆 Leaderboard</h2>
    <table>
      <tr><th>#</th><th>User</th><th>Points</th><th>Rank</th></tr>
      {% for row in leaderboard %}
      <tr>
        <td class="medal">{{ row.medal }}</td>
        <td>{{ row.name }}</td>
        <td>{{ row.points }}</td>
        <td><span class="rank-pill">{{ row.rank }}</span></td>
      </tr>
      {% else %}
      <tr><td colspan="4">No points recorded yet.</td></tr>
      {% endfor %}
    </table>
  </div>

  <div class="section">
    <h2>🎬 Command usage since last restart</h2>
    <table>
      <tr><th>Command</th><th>Uses</th></tr>
      {% for name, count in usage %}
      <tr><td>{{ name }}</td><td>{{ count }}</td></tr>
      {% else %}
      <tr><td colspan="2">No commands used yet.</td></tr>
      {% endfor %}
    </table>
  </div>

  <div class="footer">Zexo · auto-refreshing every 30s</div>
  <script>setTimeout(() => location.reload(), 30000);</script>
</body>
</html>
"""


@app.route('/dashboard')
def web_dashboard():
    uptime = datetime.now(timezone.utc) - START_TIME
    data = load_points()
    sorted_entries = sorted(data.items(), key=lambda x: x[1], reverse=True)[:15]
    medals = ["🥇", "🥈", "🥉"]

    leaderboard = []
    for i, (uid, score) in enumerate(sorted_entries):
        name = resolved_names.get(str(uid), f"User {uid}")
        rank_label = current_rank_label(score) or UNRANKED_LABEL
        medal = medals[i] if i < 3 else f"{i + 1}."
        leaderboard.append({"medal": medal, "name": name, "points": score, "rank": rank_label})

    usage = sorted(command_usage.items(), key=lambda x: -x[1])[:10]

    return render_template_string(
        DASHBOARD_HTML,
        uptime=format_timedelta(uptime),
        server_count=len(bot.guilds),
        member_count=sum(g.member_count or 0 for g in bot.guilds),
        day_number=load_day(),
        dpy_version=discord.__version__,
        leaderboard=leaderboard,
        usage=usage,
    )


def run_web():
    port = int(os.environ.get("PORT", 10000))
    app.run(host='0.0.0.0', port=port)


threading.Thread(target=run_web, daemon=True).start()

intents = discord.Intents.default()
intents.message_content = True
intents.guilds = True
intents.members = True
bot = commands.Bot(command_prefix="!", intents=intents, help_command=None)

START_TIME = datetime.now(timezone.utc)
command_usage = {}
resolved_names = {}  # user_id (str) -> last known display name, for the web dashboard

current_poll = {"message_id": None, "channel_id": None, "entries": []}
last_collect_date = None
last_results_date = None


# ============================================================
# Helpers
# ============================================================

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
    return (
        _member_has_role(member, PICKER_ROLE_ID, PICKER_ROLE_NAME)
        or _member_has_role(member, MANAGER_ROLE_ID, MANAGER_ROLE_NAME)
        or _member_has_role(member, STAFF_ROLE_ID, STAFF_ROLE_NAME)
    )


def has_points_permission(member: discord.Member) -> bool:
    """Only Top Edit Picker Manager, Staff, or admin can give/remove points."""
    if member.guild_permissions.administrator:
        return True
    return (
        _member_has_role(member, MANAGER_ROLE_ID, MANAGER_ROLE_NAME)
        or _member_has_role(member, STAFF_ROLE_ID, STAFF_ROLE_NAME)
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


# --- Points storage ---
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


def load_points():
    raw = db_get_raw("points")
    if raw is not None:
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            return {}
    if not os.path.exists(POINTS_FILE):
        return {}
    try:
        with open(POINTS_FILE, "r") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return {}


def save_points(data):
    if db_set_raw("points", json.dumps(data)):
        return
    with open(POINTS_FILE, "w") as f:
        json.dump(data, f)


def add_points(user_id: int, amount: int):
    # Loads the existing file, only ever changes the single key being touched,
    # so points for every other user are always preserved across restarts/redeploys.
    data = load_points()
    key = str(user_id)
    data[key] = max(0, data.get(key, 0) + amount)
    save_points(data)
    return data[key]


async def apply_point_roles(guild: discord.Guild, member_id: int, total_points: int):
    member = guild.get_member(member_id)
    if not member:
        try:
            member = await guild.fetch_member(member_id)
        except discord.NotFound:
            return

    resolved_names[str(member_id)] = member.display_name

    target_role_id = None
    for threshold, role_id, _label, _emoji in RANK_TIERS:
        if total_points >= threshold:
            target_role_id = role_id

    all_tier_role_ids = {rid for _, rid, _, _ in RANK_TIERS}
    desired_ids = set()
    if target_role_id:
        desired_ids.add(target_role_id)
    else:
        desired_ids.add(UNRANKED_ROLE_ID)

    roles_to_remove = [
        r for r in member.roles
        if (r.id in all_tier_role_ids or r.id == UNRANKED_ROLE_ID) and r.id not in desired_ids
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
    new_total = add_points(member_id, amount)
    await apply_point_roles(guild, member_id, new_total)
    return new_total


async def log_points_action(guild: discord.Guild, actor: discord.Member, target_id: int, amount: int, new_total: int, action: str) -> bool:
    """Posts an audit-log entry whenever someone gives/removes points, so it's always visible who did it.
    Returns True/False so the calling command can warn the user if logging silently failed."""
    log_channel = guild.get_channel(LOG_CHANNEL_ID) or find_channel(guild, LOG_CHANNEL_ID, LOG_CHANNEL_NAME)
    if not log_channel:
        try:
            log_channel = await guild.fetch_channel(LOG_CHANNEL_ID)
        except (discord.NotFound, discord.Forbidden, discord.HTTPException):
            log_channel = None
    if not log_channel:
        print(f"⚠️ Points log channel not found (ID {LOG_CHANNEL_ID}). Check the ID and that the bot can see it.")
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
        print(f"⚠️ Missing permission to post in the points log channel (ID {LOG_CHANNEL_ID}).")
        return False
    except discord.HTTPException as e:
        print(f"⚠️ Failed to post to the points log channel: {e}")
        return False


def next_rank_progress(total: int):
    """Returns (label, points_needed, current_threshold, next_threshold) for the next rank."""
    prev_threshold = 0
    for threshold, _role_id, label, _emoji in RANK_TIERS:
        if total < threshold:
            return label, threshold - total, prev_threshold, threshold
        prev_threshold = threshold
    return None, 0, prev_threshold, prev_threshold


def current_rank_label(total: int):
    label = None
    for threshold, _role_id, tier_label, _emoji in RANK_TIERS:
        if total >= threshold:
            label = tier_label
    return label


def current_rank_emoji(total: int):
    emoji = UNRANKED_EMOJI
    for threshold, _role_id, _label, tier_emoji in RANK_TIERS:
        if total >= threshold:
            emoji = tier_emoji
    return emoji


def current_rank_role_id(total: int):
    role_id = UNRANKED_ROLE_ID
    for threshold, tier_role_id, _label, _emoji in RANK_TIERS:
        if total >= threshold:
            role_id = tier_role_id
    return role_id


# --- Day counter ---
def load_day():
    raw = db_get_raw("day")
    if raw is not None:
        try:
            return json.loads(raw).get("day", DEFAULT_DAY)
        except json.JSONDecodeError:
            return DEFAULT_DAY
    if not os.path.exists(DAY_FILE):
        save_day(DEFAULT_DAY)
        return DEFAULT_DAY
    try:
        with open(DAY_FILE, "r") as f:
            return json.load(f).get("day", DEFAULT_DAY)
    except (json.JSONDecodeError, OSError):
        return DEFAULT_DAY


def save_day(day: int):
    if db_set_raw("day", json.dumps({"day": day})):
        return
    with open(DAY_FILE, "w") as f:
        json.dump({"day": day}, f)


# --- Video de-dupe history (5-day rule) ---
def load_video_history():
    raw = db_get_raw("video_history")
    if raw is not None:
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            return {}
    if not os.path.exists(VIDEO_HISTORY_FILE):
        return {}
    try:
        with open(VIDEO_HISTORY_FILE, "r") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return {}


def save_video_history(data):
    if db_set_raw("video_history", json.dumps(data)):
        return
    with open(VIDEO_HISTORY_FILE, "w") as f:
        json.dump(data, f)


def prune_video_history(data: dict) -> dict:
    cutoff = datetime.now(timezone.utc) - timedelta(days=VIDEO_DEDUPE_DAYS)
    pruned = {}
    for url, iso_ts in data.items():
        try:
            ts = datetime.fromisoformat(iso_ts)
        except ValueError:
            continue
        if ts >= cutoff:
            pruned[url] = iso_ts
    return pruned


def is_video_recently_used(url: str, history: dict) -> bool:
    iso_ts = history.get(url)
    if not iso_ts:
        return False
    try:
        ts = datetime.fromisoformat(iso_ts)
    except ValueError:
        return False
    return ts >= datetime.now(timezone.utc) - timedelta(days=VIDEO_DEDUPE_DAYS)


def mark_video_used(url: str, history: dict):
    history[url] = datetime.now(timezone.utc).isoformat()


# --- Last collection timestamp (fixes the "yesterday's edits reappear" bug) ---
def load_last_collect_ts() -> datetime:
    raw = db_get_raw("last_collect")
    if raw is not None:
        try:
            iso_ts = json.loads(raw).get("ts")
            return datetime.fromisoformat(iso_ts)
        except (json.JSONDecodeError, TypeError, ValueError):
            return datetime.now(timezone.utc) - timedelta(hours=24)
    if not os.path.exists(LAST_COLLECT_FILE):
        return datetime.now(timezone.utc) - timedelta(hours=24)
    try:
        with open(LAST_COLLECT_FILE, "r") as f:
            iso_ts = json.load(f).get("ts")
        return datetime.fromisoformat(iso_ts)
    except (json.JSONDecodeError, OSError, TypeError, ValueError):
        return datetime.now(timezone.utc) - timedelta(hours=24)


def save_last_collect_ts(ts: datetime):
    if db_set_raw("last_collect", json.dumps({"ts": ts.isoformat()})):
        return
    with open(LAST_COLLECT_FILE, "w") as f:
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

@bot.event
async def on_ready():
    print(f"✅ Zexo is online as {bot.user}")
    if not scheduler_loop.is_running():
        scheduler_loop.start()
    for guild in bot.guilds:
        dashboard_state["guild_name"] = guild.name
        dashboard_state["member_count"] = guild.member_count or 0
    try:
        synced = await bot.tree.sync()
        print(f"Synced {len(synced)} slash command(s)")
    except Exception as e:
        print(f"Slash command sync failed: {e}")


@bot.event
async def on_command_completion(ctx):
    command_usage[ctx.command.name] = command_usage.get(ctx.command.name, 0) + 1


@tasks.loop(minutes=1)
async def scheduler_loop():
    global last_collect_date, last_results_date
    now = datetime.now(EU_TZ)

    if now.hour == COLLECT_HOUR and now.minute == 0 and last_collect_date != now.date():
        last_collect_date = now.date()
        await run_collect_job()

    if now.hour == RESULTS_HOUR and now.minute == 0 and last_results_date != now.date():
        last_results_date = now.date()
        await run_results_job()


def make_word_matcher(word: str) -> re.Pattern:
    """Whole-word, case-insensitive match, so searching '12' doesn't also hit '123' or '512'."""
    return re.compile(rf"\b{re.escape(word)}\b", re.IGNORECASE)


async def purge_messages_with_word(channel: discord.TextChannel, word: str, progress=None) -> int:
    """Deletes every message in `channel` whose content contains `word` as a whole word,
    scanning the ENTIRE channel history. Deletes as it scans (not after collecting everything
    first), so progress is visible immediately instead of looking stuck.
    `progress`, if given, is an async callable: progress(scanned, deleted, final=False)."""
    matcher = make_word_matcher(word)
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

    async for msg in channel.history(limit=None):
        scanned += 1
        if matcher.search(msg.content):
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

        if progress and scanned % 250 == 0:
            await progress(scanned, deleted_total)

    await flush_bulk_batch()
    if progress:
        await progress(scanned, deleted_total, final=True)
    return deleted_total



def extract_video_sources(msg: discord.Message):
    """Returns every distinct video/attachment/link found in a message (supports multiple)."""
    sources = []
    for attachment in msg.attachments:
        sources.append(attachment.url)
    for word in msg.content.split():
        if word.startswith("http://") or word.startswith("https://"):
            sources.append(word)
    seen = set()
    unique_sources = []
    for url in sources:
        if url not in seen:
            seen.add(url)
            unique_sources.append(url)
    return unique_sources


async def run_collect_job():
    current_poll["entries"] = []
    current_poll["message_id"] = None
    current_poll["channel_id"] = None

    since = load_last_collect_ts()
    run_ts = datetime.now(timezone.utc)

    video_history = prune_video_history(load_video_history())

    for guild in bot.guilds:
        submit_channel = find_channel(guild, SUBMIT_CHANNEL_ID, SUBMIT_CHANNEL_NAME)
        discussion_channel = find_channel(guild, DISCUSSION_CHANNEL_ID, DISCUSSION_CHANNEL_NAME)
        picker_role = find_role(guild, PICKER_ROLE_ID, PICKER_ROLE_NAME)

        if not submit_channel or not discussion_channel or not picker_role:
            print(f"⚠️ Missing channel/role in guild {guild.name}, skipping.")
            continue

        entries = []

        async for msg in submit_channel.history(after=since, limit=200):
            if msg.author.bot:
                continue
            if picker_role not in msg.role_mentions:
                continue

            for video_source in extract_video_sources(msg):
                if is_video_recently_used(video_source, video_history):
                    continue
                entries.append(
                    {"author_id": msg.author.id, "author_name": msg.author.display_name, "video_url": video_source}
                )
                resolved_names[str(msg.author.id)] = msg.author.display_name
                if len(entries) >= MAX_POLL_ANSWERS:
                    break
            if len(entries) >= MAX_POLL_ANSWERS:
                break

        if not entries:
            print(f"No valid edits found in {guild.name} today.")
            continue

        for entry in entries:
            await discussion_channel.send(content=f"**Edit by {entry['author_name']}**\n{entry['video_url']}")
            mark_video_used(entry["video_url"], video_history)

        poll = discord.Poll(question="Vote for today's top edit!", duration=timedelta(hours=POLL_DURATION_HOURS))
        for entry in entries:
            poll.add_answer(text=f"Vote for {entry['author_name']}"[:55])

        sent = await discussion_channel.send(content=f"{picker_role.mention} 📊 Vote for today's top edit!", poll=poll)

        current_poll["message_id"] = sent.id
        current_poll["channel_id"] = discussion_channel.id
        current_poll["entries"] = entries

    save_video_history(video_history)
    save_last_collect_ts(run_ts)
    print(f"Collect job done. {len(current_poll['entries'])} edit(s) in today's poll.")


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
    if not current_poll["message_id"]:
        print("No active poll to resolve today.")
        return

    channel = bot.get_channel(current_poll["channel_id"])
    if not channel:
        return

    try:
        msg = await channel.fetch_message(current_poll["message_id"])
    except discord.NotFound:
        print("Poll message not found.")
        return

    if not msg.poll or not msg.poll.answers:
        return

    votes = [a.vote_count for a in msg.poll.answers]
    max_votes = max(votes)
    tied_indices = [i for i, v in enumerate(votes) if v == max_votes]

    used_tiebreak = len(tied_indices) > 1
    if used_tiebreak:
        winner_index = await resolve_tiebreak(tied_indices, channel)
    else:
        winner_index = tied_indices[0]

    if winner_index >= len(current_poll["entries"]):
        return

    best_entry = current_poll["entries"][winner_index]
    best_votes = max_votes
    day_number = load_day()

    for guild in bot.guilds:
        results_channel = find_channel(guild, RESULTS_CHANNEL_ID, RESULTS_CHANNEL_NAME)
        discussion_channel = find_channel(guild, DISCUSSION_CHANNEL_ID, DISCUSSION_CHANNEL_NAME)
        top_edits_role = find_role(guild, TOP_EDITS_ROLE_ID, TOP_EDITS_ROLE_NAME)
        if not results_channel:
            continue

        new_total = await award_points(guild, best_entry["author_id"], WINNER_POINTS)

        ping = top_edits_role.mention if top_edits_role else ""

        win_line = random.choice(TOP_EDIT_WIN_MESSAGES).format(member=f"<@{best_entry['author_id']}>")

        # The tiebreaker coin-flip is never mentioned in #top-edits — only in the discussion channel.
        content = (
            f"{ping} 🏆 **Top Edit of the Day — Day {day_number}**\n"
            f"{win_line}\n"
            f"Congrats <@{best_entry['author_id']}>! Your edit won with **{best_votes}** vote(s)! 🎉\n"
            f"You earned **+{WINNER_POINTS}** point(s) (total: **{new_total}**).\n"
            f"{best_entry['video_url']}"
        )
        await results_channel.send(content=content)

        if used_tiebreak and discussion_channel:
            flavor = random.choice(COIN_FLIP_WIN_MESSAGES).format(member=f"<@{best_entry['author_id']}>")
            await discussion_channel.send(
                content=f"🪙 *Today's winner was decided by a coin-flip tiebreaker!* {flavor}"
            )

        print(f"Winner announced: {best_entry['author_name']} with {best_votes} votes (day {day_number}).")

    save_day(day_number + 1)
    current_poll["entries"] = []
    current_poll["message_id"] = None
    current_poll["channel_id"] = None


# ============================================================
# Shared embed builders
# ============================================================

def build_help_embed():
    embed = discord.Embed(
        title="Zexo — Command Overview",
        description="Every command works as both `!command` and `/command`.",
        color=discord.Color.blurple(),
    )
    embed.add_field(
        name="🏅 Points & Ranks",
        value=(
            "`points [@user]` — Check points + progress to next rank\n"
            "`ranks` — See every rank, its threshold, and how to earn points\n"
            "`leaderboard` — Top 10 point rankings"
        ),
        inline=False,
    )
    embed.add_field(
        name="🎬 Top Edits Event",
        value=(
            "`timeleft` — Time left until voting starts/ends\n"
            "`testcollect` — Manually run the collect job *(Picker/Manager/Staff only)*\n"
            "`testresults` — Manually run the results job *(Picker/Manager/Staff only)*\n"
            "`addpoints @user <amount>` — Add points *(Manager/Staff only)*\n"
            "`removepoints @user <amount>` — Remove points *(Manager/Staff only)*\n"
            "`purgeword #channel word` — Delete every message with that word *(Manager/Staff only)*"
        ),
        inline=False,
    )
    embed.add_field(
        name="⚙️ Utility",
        value=(
            "`ping` — Detailed latency/status check\n"
            "`dashboard` — Live bot stats\n"
            "`flip` — Flip a coin"
        ),
        inline=False,
    )
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


async def build_leaderboard_embed(guild: discord.Guild):
    data = load_points()
    embed = discord.Embed(
        title="🏆 Zexo Leaderboard",
        description="Top editors of this server, ranked by total points.",
        color=discord.Color.gold(),
    )
    if not data:
        embed.description = "No points recorded yet. Win a Top Edit to get on the board!"
        return embed

    sorted_entries = sorted(data.items(), key=lambda x: x[1], reverse=True)[:10]
    medals = ["🥇", "🥈", "🥉"]
    lines = []
    for i, (uid, score) in enumerate(sorted_entries):
        name = await resolve_display_name(guild, uid)
        position = medals[i] if i < 3 else f"**#{i + 1}**"
        rank_emoji = current_rank_emoji(score)
        rank_label = current_rank_label(score) or UNRANKED_LABEL
        role_obj = guild.get_role(current_rank_role_id(score))
        role_display = role_obj.mention if role_obj else f"*{rank_label}*"
        lines.append(f"{position} **{name}** — `{score}` pts {rank_emoji} {role_display}")
    embed.description = "\n".join(lines) + f"\n\n_{random.choice(LEADERBOARD_FLAVOR)}_"
    embed.set_footer(text=f"Day {load_day()} · Ranks shown are each editor's current role")
    return embed


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


async def generate_leaderboard_image(guild: discord.Guild):
    """Renders the top-10 leaderboard as a film-strip themed PNG (avatars, tier colors, progress bars)."""
    data = load_points()
    if not data:
        return None

    sorted_entries = sorted(data.items(), key=lambda x: x[1], reverse=True)[:10]

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
    draw.text((width / 2, 86), f"Day {load_day()} · Top {len(sorted_entries)}", font=sub_font, fill=(175, 170, 195), anchor="mm")

    medal_colors = {0: (255, 215, 0), 1: (205, 205, 215), 2: (205, 127, 50)}
    y = header_h

    for i, (uid, score) in enumerate(sorted_entries):
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


def build_points_message(member: discord.Member) -> str:
    data = load_points()
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

    return f"🏅 {member.mention} has **{total}** point(s).\n{rank_text}\n{progress_text}\n*{flavor}*"


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


def build_timeleft_message():
    now = datetime.now(EU_TZ)
    collect_dt = now.replace(hour=COLLECT_HOUR, minute=0, second=0, microsecond=0)
    results_dt = now.replace(hour=RESULTS_HOUR, minute=0, second=0, microsecond=0)

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
    embed.set_footer(text=f"discord.py {discord.__version__} · Full dashboard: /dashboard on your Render URL")
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
    await ctx.send(embed=build_help_embed())


@bot.command()
async def flip(ctx):
    result = random.choice(["Heads", "Tails"])
    await ctx.send(f"🪙 The coin landed on **{result}**!")


@bot.command()
async def timeleft(ctx):
    await ctx.send(build_timeleft_message())


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
    await ctx.send(f"✅ Done. {len(current_poll['entries'])} edit(s) posted for voting.")


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
    warning = "" if logged else f"\n⚠️ *Couldn't post to the points log channel (ID `{LOG_CHANNEL_ID}`) — check the ID and that the bot can see/send in it.*"
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
    warning = "" if logged else f"\n⚠️ *Couldn't post to the points log channel (ID `{LOG_CHANNEL_ID}`) — check the ID and that the bot can see/send in it.*"
    await ctx.send(f"✅ Removed **{amount}** point(s) from {member.mention}. New total: **{new_total}**{warning}")


@bot.command()
async def points(ctx, member: discord.Member = None):
    member = member or ctx.author
    await ctx.send(build_points_message(member))


@bot.command()
async def leaderboard(ctx):
    file = await generate_leaderboard_image(ctx.guild)
    if file:
        await ctx.send(content="🎬🏆", file=file)
    else:
        await ctx.send(embed=await build_leaderboard_embed(ctx.guild))


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
    await interaction.response.send_message(embed=build_help_embed())


@bot.tree.command(name="flip", description="Flip a coin")
async def slash_flip(interaction: discord.Interaction):
    result = random.choice(["Heads", "Tails"])
    await interaction.response.send_message(f"🪙 The coin landed on **{result}**!")


@bot.tree.command(name="timeleft", description="See how much time is left until voting starts/ends")
async def slash_timeleft(interaction: discord.Interaction):
    await interaction.response.send_message(build_timeleft_message())


@bot.tree.command(name="ranks", description="See every editor rank and how to earn points")
async def slash_ranks(interaction: discord.Interaction):
    await interaction.response.send_message(embed=build_ranks_embed())


@bot.tree.command(name="points", description="Check a user's points")
@app_commands.describe(member="Whose points to check (defaults to you)")
async def slash_points(interaction: discord.Interaction, member: discord.Member = None):
    member = member or interaction.user
    await interaction.response.send_message(build_points_message(member))


@bot.tree.command(name="leaderboard", description="Show the top 10 point rankings")
async def slash_leaderboard(interaction: discord.Interaction):
    await interaction.response.defer()
    file = await generate_leaderboard_image(interaction.guild)
    if file:
        await interaction.followup.send(content="🎬🏆", file=file)
    else:
        await interaction.followup.send(embed=await build_leaderboard_embed(interaction.guild))


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


@bot.tree.command(name="addpoints", description="Add points to a user (Top Edit Manager/Staff only)")
@app_commands.describe(member="User to add points to", amount="How many points to add")
async def slash_addpoints(interaction: discord.Interaction, member: discord.Member, amount: int):
    if not has_points_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Manager or Staff can use this.", ephemeral=True)
        return
    new_total = await award_points(interaction.guild, member.id, amount)
    logged = await log_points_action(interaction.guild, interaction.user, member.id, amount, new_total, "add")
    warning = "" if logged else f"\n⚠️ *Couldn't post to the points log channel (ID `{LOG_CHANNEL_ID}`) — check the ID and that the bot can see/send in it.*"
    await interaction.response.send_message(f"✅ Added **{amount}** point(s) to {member.mention}. New total: **{new_total}**{warning}")


@bot.tree.command(name="removepoints", description="Remove points from a user (Top Edit Manager/Staff only)")
@app_commands.describe(member="User to remove points from", amount="How many points to remove")
async def slash_removepoints(interaction: discord.Interaction, member: discord.Member, amount: int):
    if not has_points_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Manager or Staff can use this.", ephemeral=True)
        return
    new_total = await award_points(interaction.guild, member.id, -amount)
    logged = await log_points_action(interaction.guild, interaction.user, member.id, amount, new_total, "remove")
    warning = "" if logged else f"\n⚠️ *Couldn't post to the points log channel (ID `{LOG_CHANNEL_ID}`) — check the ID and that the bot can see/send in it.*"
    await interaction.response.send_message(f"✅ Removed **{amount}** point(s) from {member.mention}. New total: **{new_total}**{warning}")


@bot.tree.command(name="testcollect", description="Manually run the collect-edits job (Picker/Manager/Staff only)")
async def slash_testcollect(interaction: discord.Interaction):
    if not has_picker_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Picker/Manager/Staff can use this.", ephemeral=True)
        return
    await interaction.response.send_message("⏳ Running collect job manually...")
    await run_collect_job()
    await interaction.followup.send(f"✅ Done. {len(current_poll['entries'])} edit(s) posted for voting.")


@bot.tree.command(name="testresults", description="Manually run the announce-winner job (Picker/Manager/Staff only)")
async def slash_testresults(interaction: discord.Interaction):
    if not has_picker_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Picker/Manager/Staff can use this.", ephemeral=True)
        return
    await interaction.response.send_message("⏳ Running results job manually...")
    await run_results_job()
    await interaction.followup.send("✅ Done.")


TOKEN = os.environ.get("DISCORD_TOKEN")
if not TOKEN:
    raise RuntimeError("DISCORD_TOKEN environment variable is missing! Set it in Render under Environment.")

init_db()
bot.run(TOKEN)
