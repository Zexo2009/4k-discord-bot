import os
import json
import threading
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

from flask import Flask
import discord
from discord.ext import commands, tasks

# ============================================================
# CONFIG - fill in IDs where you have them (most reliable).
# Leave as None to fall back to searching by name instead.
# (name fallback must match exactly, incl. case and hyphens)
# ============================================================
SUBMIT_CHANNEL_ID = 1453098499301314662       # editing-rating channel ID
DISCUSSION_CHANNEL_ID = 1514944188838576270   # top-edit-discussion channel ID
RESULTS_CHANNEL_ID = 1479559357363650653      # top-edits channel ID
PICKER_ROLE_ID = 1514920107912990841          # "Top Edit Picker" role ID
RESULTS_PING_ROLE_ID = 1514920107912990841    # role ID to ping on winner announcement

SUBMIT_CHANNEL_NAME = "editing-rating"        # fallback if ID above is None
DISCUSSION_CHANNEL_NAME = "top-edit-discussion"
RESULTS_CHANNEL_NAME = "top-edits"

PICKER_ROLE_NAME = "Top Edit Picker"
RESULTS_PING_ROLE_NAME = "Top Edit Picker"

COLLECT_HOUR = 15   # 15:00 Uhr EU-Zeit: Edits einsammeln + Polls erstellen
RESULTS_HOUR = 21   # 21:00 Uhr EU-Zeit: Gewinner ermitteln + posten
EU_TZ = ZoneInfo("Europe/Berlin")

POLL_DURATION_HOURS = 6  # muss zur Zeitspanne zwischen COLLECT_HOUR und RESULTS_HOUR passen

WINNER_POINTS = 10  # Punkte, die der Top-Edit-Gewinner automatisch bekommt
POINTS_FILE = "points.json"

# ============================================================

app = Flask(__name__)

@app.route('/')
def home():
    return "Zexo is running!"

def run_web():
    port = int(os.environ.get("PORT", 10000))
    app.run(host='0.0.0.0', port=port)

threading.Thread(target=run_web, daemon=True).start()

intents = discord.Intents.default()
intents.message_content = True
intents.guilds = True
bot = commands.Bot(command_prefix="!", intents=intents, help_command=None)

# Merkt sich die heutigen Poll-Nachrichten, um sie um 20 Uhr auszuwerten
# Format: [(message_id, channel_id, author_id, jump_url), ...]
active_polls = []

# Prevents double-triggering within the same minute
last_collect_date = None
last_results_date = None


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


# --- Points system (stored in a local JSON file) ---
def load_points():
    if not os.path.exists(POINTS_FILE):
        return {}
    try:
        with open(POINTS_FILE, "r") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return {}


def save_points(data):
    with open(POINTS_FILE, "w") as f:
        json.dump(data, f)


def add_points(user_id: int, amount: int):
    data = load_points()
    key = str(user_id)
    data[key] = data.get(key, 0) + amount
    save_points(data)
    return data[key]


def can_manage_points(ctx_or_member):
    member = ctx_or_member
    if member.guild_permissions.administrator:
        return True
    return any(role.name == PICKER_ROLE_NAME for role in member.roles)


@bot.command()
async def addpoints(ctx, member: discord.Member = None, amount: int = None):
    if not can_manage_points(ctx.author):
        await ctx.send("❌ You don't have permission to add points.")
        return
    if member is None or amount is None:
        await ctx.send("Usage: `!addpoints @user <amount>`")
        return

    new_total = add_points(member.id, amount)
    await ctx.send(f"✅ Added **{amount}** point(s) to {member.mention}. New total: **{new_total}**")


@bot.command()
async def points(ctx, member: discord.Member = None):
    member = member or ctx.author
    data = load_points()
    total = data.get(str(member.id), 0)
    await ctx.send(f"🏅 {member.mention} has **{total}** point(s).")


@bot.command()
async def leaderboard(ctx):
    data = load_points()
    if not data:
        await ctx.send("No points recorded yet.")
        return

    sorted_entries = sorted(data.items(), key=lambda x: x[1], reverse=True)[:10]

    embed = discord.Embed(title="🏆 Leaderboard", color=discord.Color.gold())
    lines = []
    for i, (user_id, score) in enumerate(sorted_entries, start=1):
        lines.append(f"**{i}.** <@{user_id}> — {score} point(s)")
    embed.description = "\n".join(lines)
    await ctx.send(embed=embed)


@bot.event
async def on_ready():
    print(f"✅ Zexo is online as {bot.user}")
    if not scheduler_loop.is_running():
        scheduler_loop.start()


@bot.command()
async def ping(ctx):
    await ctx.send("Pong! 🚀")


@bot.command()
async def testcollect(ctx):
    if not ctx.author.guild_permissions.administrator:
        await ctx.send("❌ Admins only.")
        return
    await ctx.send("⏳ Running collect job manually...")
    await run_collect_job()
    await ctx.send(f"✅ Done. {len(active_polls)} edit(s) posted for voting.")


@bot.command()
async def testresults(ctx):
    if not ctx.author.guild_permissions.administrator:
        await ctx.send("❌ Admins only.")
        return
    await ctx.send("⏳ Running results job manually...")
    await run_results_job()
    await ctx.send("✅ Done.")


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


async def run_collect_job():
    active_polls.clear()

    for guild in bot.guilds:
        submit_channel = find_channel(guild, SUBMIT_CHANNEL_ID, SUBMIT_CHANNEL_NAME)
        discussion_channel = find_channel(guild, DISCUSSION_CHANNEL_ID, DISCUSSION_CHANNEL_NAME)
        picker_role = find_role(guild, PICKER_ROLE_ID, PICKER_ROLE_NAME)

        if not submit_channel or not discussion_channel or not picker_role:
            print(f"⚠️ Missing channel/role in guild {guild.name}, skipping.")
            continue

        since = datetime.now(timezone.utc) - timedelta(hours=24)

        async for msg in submit_channel.history(after=since, limit=200):
            if msg.author.bot:
                continue
            if picker_role not in msg.role_mentions:
                continue

            # Edit in die Diskussion posten
            embed = discord.Embed(
                description=msg.content or "*(no caption)*",
                color=discord.Color.blurple(),
            )
            embed.set_author(name=str(msg.author), icon_url=msg.author.display_avatar.url)
            embed.add_field(name="Original message", value=f"[Jump to post]({msg.jump_url})", inline=False)
            if msg.attachments:
                embed.set_image(url=msg.attachments[0].url)

            poll = discord.Poll(
                question=f"Vote for {msg.author.display_name}'s edit!",
                duration=timedelta(hours=POLL_DURATION_HOURS),
            )
            poll.add_answer(text="Vote for this edit", emoji="🔥")

            sent = await discussion_channel.send(
                content=picker_role.mention,
                embed=embed,
                poll=poll,
            )

            active_polls.append(
                {
                    "message_id": sent.id,
                    "channel_id": discussion_channel.id,
                    "author_id": msg.author.id,
                    "author_name": msg.author.display_name,
                    "jump_url": msg.jump_url,
                    "attachment_url": msg.attachments[0].url if msg.attachments else None,
                }
            )

    print(f"Collect job done. {len(active_polls)} edit(s) posted for voting.")


async def run_results_job():
    if not active_polls:
        print("No active polls to resolve today.")
        return

    for guild in bot.guilds:
        results_channel = find_channel(guild, RESULTS_CHANNEL_ID, RESULTS_CHANNEL_NAME)
        results_role = find_role(guild, RESULTS_PING_ROLE_ID, RESULTS_PING_ROLE_NAME)
        discussion_channel = None
        for entry in active_polls:
            ch = bot.get_channel(entry["channel_id"])
            if ch and ch.guild.id == guild.id:
                discussion_channel = ch
                break

        if not results_channel or not discussion_channel:
            continue

        best_entry = None
        best_votes = -1

        for entry in active_polls:
            try:
                msg = await discussion_channel.fetch_message(entry["message_id"])
            except discord.NotFound:
                continue

            if not msg.poll or not msg.poll.answers:
                continue

            votes = msg.poll.answers[0].vote_count
            if votes > best_votes:
                best_votes = votes
                best_entry = entry

        if best_entry:
            new_total = add_points(best_entry["author_id"], WINNER_POINTS)

            embed = discord.Embed(
                title="🏆 Top Edit of the Day!",
                description=(
                    f"Congrats <@{best_entry['author_id']}>! Your edit won with **{best_votes}** vote(s)! 🎉\n"
                    f"You earned **+{WINNER_POINTS}** points (total: **{new_total}**)."
                ),
                color=discord.Color.gold(),
            )
            embed.add_field(name="Original post", value=f"[Jump to post]({best_entry['jump_url']})", inline=False)
            if best_entry["attachment_url"]:
                embed.set_image(url=best_entry["attachment_url"])

            content = results_role.mention if results_role else ""
            await results_channel.send(content=content, embed=embed)
            print(f"Winner announced: {best_entry['author_name']} with {best_votes} votes.")

    active_polls.clear()


TOKEN = os.environ.get("DISCORD_TOKEN")
if not TOKEN:
    raise RuntimeError("DISCORD_TOKEN environment variable is missing! Set it in Render under Environment.")

bot.run(TOKEN)
