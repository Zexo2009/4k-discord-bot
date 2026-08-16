import os
import json
import threading
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

from flask import Flask
import discord
from discord import app_commands
from discord.ext import commands, tasks

# ============================================================
# CONFIG
# ============================================================
SUBMIT_CHANNEL_ID = 1453098499301314662       # editing-rating channel ID
DISCUSSION_CHANNEL_ID = 1514944188838576270   # top-edit-discussion channel ID
RESULTS_CHANNEL_ID = 1479559357363650653      # top-edits channel ID
PICKER_ROLE_ID = 1514920107912990841          # "Top Edit Picker" role ID
RESULTS_PING_ROLE_ID = 1514920107912990841

SUBMIT_CHANNEL_NAME = "editing-rating"
DISCUSSION_CHANNEL_NAME = "top-edit-discussion"
RESULTS_CHANNEL_NAME = "top-edits"
PICKER_ROLE_NAME = "Top Edit Picker"
RESULTS_PING_ROLE_NAME = "Top Edit Picker"

COLLECT_HOUR = 16
RESULTS_HOUR = 20
EU_TZ = ZoneInfo("Europe/Berlin")

POLL_DURATION_HOURS = 4
MAX_POLL_ANSWERS = 10  # Discord's limit per poll

WINNER_POINTS = 1
POINTS_FILE = "points.json"

# Point-tier roles: (points_threshold, role_id). Highest qualifying tier
# replaces any lower tier role the member currently has.
POINT_ROLE_TIERS = sorted(
    [
        (1, 1459931456859144308),
        (5, 1459931371567976592),
        (14, 1459931236045820126),
        (25, 1459931151664676884),
        (40, 1459931062665871626),
    ],
    key=lambda x: x[0],
)

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
intents.members = True
bot = commands.Bot(command_prefix="!", intents=intents, help_command=None)

# Holds today's single poll: message_id, channel_id, and the list of
# entries in the same order the poll answers were added.
current_poll = {"message_id": None, "channel_id": None, "entries": []}

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


def has_picker_permission(member: discord.Member) -> bool:
    if member.guild_permissions.administrator:
        return True
    if PICKER_ROLE_ID and any(r.id == PICKER_ROLE_ID for r in member.roles):
        return True
    return any(role.name == PICKER_ROLE_NAME for role in member.roles)


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


async def apply_point_roles(guild: discord.Guild, member_id: int, total_points: int):
    member = guild.get_member(member_id)
    if not member:
        try:
            member = await guild.fetch_member(member_id)
        except discord.NotFound:
            return

    target_role_id = None
    for threshold, role_id in POINT_ROLE_TIERS:
        if total_points >= threshold:
            target_role_id = role_id  # keeps updating -> ends up as highest qualifying tier

    all_tier_role_ids = {rid for _, rid in POINT_ROLE_TIERS}
    roles_to_remove = [r for r in member.roles if r.id in all_tier_role_ids and r.id != target_role_id]
    role_to_add = guild.get_role(target_role_id) if target_role_id else None

    try:
        if roles_to_remove:
            await member.remove_roles(*roles_to_remove, reason="Point tier update")
        if role_to_add and role_to_add not in member.roles:
            await member.add_roles(role_to_add, reason="Point tier update")
    except discord.Forbidden:
        print(f"⚠️ Missing permission to manage roles for {member}.")


async def award_points(guild: discord.Guild, member_id: int, amount: int):
    """Adds points AND updates the member's tier role. Use this instead of add_points directly."""
    new_total = add_points(member_id, amount)
    await apply_point_roles(guild, member_id, new_total)
    return new_total


@bot.event
async def on_ready():
    print(f"✅ Zexo is online as {bot.user}")
    if not scheduler_loop.is_running():
        scheduler_loop.start()
    try:
        synced = await bot.tree.sync()
        print(f"Synced {len(synced)} slash command(s)")
    except Exception as e:
        print(f"Slash command sync failed: {e}")


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


def extract_video_source(msg: discord.Message):
    if msg.attachments:
        return msg.attachments[0].url
    for word in msg.content.split():
        if word.startswith("http://") or word.startswith("https://"):
            return word
    return None


async def run_collect_job():
    current_poll["entries"] = []
    current_poll["message_id"] = None
    current_poll["channel_id"] = None

    for guild in bot.guilds:
        submit_channel = find_channel(guild, SUBMIT_CHANNEL_ID, SUBMIT_CHANNEL_NAME)
        discussion_channel = find_channel(guild, DISCUSSION_CHANNEL_ID, DISCUSSION_CHANNEL_NAME)
        picker_role = find_role(guild, PICKER_ROLE_ID, PICKER_ROLE_NAME)

        if not submit_channel or not discussion_channel or not picker_role:
            print(f"⚠️ Missing channel/role in guild {guild.name}, skipping.")
            continue

        since = datetime.now(timezone.utc) - timedelta(hours=24)
        entries = []

        async for msg in submit_channel.history(after=since, limit=200):
            if msg.author.bot:
                continue
            if picker_role not in msg.role_mentions:
                continue

            video_source = extract_video_source(msg)
            if not video_source:
                continue

            entries.append(
                {
                    "author_id": msg.author.id,
                    "author_name": msg.author.display_name,
                    "video_url": video_source,
                }
            )

            if len(entries) >= MAX_POLL_ANSWERS:
                break

        if not entries:
            print(f"No valid edits found in {guild.name} today.")
            continue

        # Post each edit's actual video so it plays inline
        for entry in entries:
            await discussion_channel.send(
                content=f"**Edit by {entry['author_name']}**\n{entry['video_url']}"
            )

        # One combined poll for all of today's edits
        poll = discord.Poll(
            question="Vote for today's top edit!",
            duration=timedelta(hours=POLL_DURATION_HOURS),
        )
        for entry in entries:
            poll.add_answer(text=f"Vote for {entry['author_name']}"[:55])

        sent = await discussion_channel.send(
            content=f"{picker_role.mention} 📊 Vote for today's top edit!",
            poll=poll,
        )

        current_poll["message_id"] = sent.id
        current_poll["channel_id"] = discussion_channel.id
        current_poll["entries"] = entries

    print(f"Collect job done. {len(current_poll['entries'])} edit(s) in today's poll.")


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

    best_index = 0
    best_votes = -1
    for i, answer in enumerate(msg.poll.answers):
        if answer.vote_count > best_votes:
            best_votes = answer.vote_count
            best_index = i

    if best_index >= len(current_poll["entries"]):
        return

    best_entry = current_poll["entries"][best_index]

    for guild in bot.guilds:
        results_channel = find_channel(guild, RESULTS_CHANNEL_ID, RESULTS_CHANNEL_NAME)
        results_role = find_role(guild, RESULTS_PING_ROLE_ID, RESULTS_PING_ROLE_NAME)
        if not results_channel:
            continue

        new_total = await award_points(guild, best_entry["author_id"], WINNER_POINTS)

        ping = results_role.mention if results_role else ""
        content = (
            f"{ping} 🏆 **Top Edit of the Day!**\n"
            f"Congrats <@{best_entry['author_id']}>! Your edit won with **{best_votes}** vote(s)! 🎉\n"
            f"You earned **+{WINNER_POINTS}** points (total: **{new_total}**).\n"
            f"{best_entry['video_url']}"
        )
        await results_channel.send(content=content)
        print(f"Winner announced: {best_entry['author_name']} with {best_votes} votes.")

    current_poll["entries"] = []
    current_poll["message_id"] = None
    current_poll["channel_id"] = None


# ============================================================
# Prefix commands (!)
# ============================================================

@bot.command()
async def ping(ctx):
    await ctx.send("Pong! 🚀")


@bot.command()
async def help(ctx):
    await ctx.send(embed=build_help_embed())


@bot.command()
async def testcollect(ctx):
    if not has_picker_permission(ctx.author):
        await ctx.send("❌ Only Top Edit Picker can use this.")
        return
    await ctx.send("⏳ Running collect job manually...")
    await run_collect_job()
    await ctx.send(f"✅ Done. {len(current_poll['entries'])} edit(s) posted for voting.")


@bot.command()
async def testresults(ctx):
    if not has_picker_permission(ctx.author):
        await ctx.send("❌ Only Top Edit Picker can use this.")
        return
    await ctx.send("⏳ Running results job manually...")
    await run_results_job()
    await ctx.send("✅ Done.")


@bot.command()
async def addpoints(ctx, member: discord.Member = None, amount: int = None):
    if not has_picker_permission(ctx.author):
        await ctx.send("❌ Only Top Edit Picker can use this.")
        return
    if member is None or amount is None:
        await ctx.send("Usage: `!addpoints @user <amount>`")
        return
    new_total = await award_points(ctx.guild, member.id, amount)
    await ctx.send(f"✅ Added **{amount}** point(s) to {member.mention}. New total: **{new_total}**")


@bot.command()
async def points(ctx, member: discord.Member = None):
    member = member or ctx.author
    data = load_points()
    total = data.get(str(member.id), 0)
    await ctx.send(f"🏅 {member.mention} has **{total}** point(s).")


@bot.command()
async def leaderboard(ctx):
    await ctx.send(embed=build_leaderboard_embed())


# ============================================================
# Slash commands (/)
# ============================================================

def build_help_embed():
    embed = discord.Embed(
        title="Zexo Commands",
        description="Available as both `!command` and `/command`.",
        color=discord.Color.blurple(),
    )
    embed.add_field(name="ping", value="Check if the bot is online.", inline=False)
    embed.add_field(name="points [@user]", value="Check a user's points (yours if no user given).", inline=False)
    embed.add_field(name="leaderboard", value="Show the top 10 point rankings.", inline=False)
    embed.add_field(
        name="addpoints @user <amount>",
        value="Add points to a user. Top Edit Picker only.",
        inline=False,
    )
    embed.add_field(
        name="testcollect",
        value="Manually run the 'collect today's edits' job. Top Edit Picker only.",
        inline=False,
    )
    embed.add_field(
        name="testresults",
        value="Manually run the 'announce winner' job. Top Edit Picker only.",
        inline=False,
    )
    return embed


def build_leaderboard_embed():
    data = load_points()
    embed = discord.Embed(title="🏆 Leaderboard", color=discord.Color.gold())
    if not data:
        embed.description = "No points recorded yet."
        return embed
    sorted_entries = sorted(data.items(), key=lambda x: x[1], reverse=True)[:10]
    lines = [f"**{i}.** <@{uid}> — {score} point(s)" for i, (uid, score) in enumerate(sorted_entries, start=1)]
    embed.description = "\n".join(lines)
    return embed


@bot.tree.command(name="ping", description="Check if the bot is online")
async def slash_ping(interaction: discord.Interaction):
    await interaction.response.send_message("Pong! 🚀")


@bot.tree.command(name="help", description="Show all available commands")
async def slash_help(interaction: discord.Interaction):
    await interaction.response.send_message(embed=build_help_embed())


@bot.tree.command(name="points", description="Check a user's points")
@app_commands.describe(member="Whose points to check (defaults to you)")
async def slash_points(interaction: discord.Interaction, member: discord.Member = None):
    member = member or interaction.user
    data = load_points()
    total = data.get(str(member.id), 0)
    await interaction.response.send_message(f"🏅 {member.mention} has **{total}** point(s).")


@bot.tree.command(name="leaderboard", description="Show the top 10 point rankings")
async def slash_leaderboard(interaction: discord.Interaction):
    await interaction.response.send_message(embed=build_leaderboard_embed())


@bot.tree.command(name="addpoints", description="Add points to a user (Top Edit Picker only)")
@app_commands.describe(member="User to add points to", amount="How many points to add")
async def slash_addpoints(interaction: discord.Interaction, member: discord.Member, amount: int):
    if not has_picker_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Picker can use this.", ephemeral=True)
        return
    new_total = await award_points(interaction.guild, member.id, amount)
    await interaction.response.send_message(f"✅ Added **{amount}** point(s) to {member.mention}. New total: **{new_total}**")


@bot.tree.command(name="testcollect", description="Manually run the collect-edits job (Top Edit Picker only)")
async def slash_testcollect(interaction: discord.Interaction):
    if not has_picker_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Picker can use this.", ephemeral=True)
        return
    await interaction.response.send_message("⏳ Running collect job manually...")
    await run_collect_job()
    await interaction.followup.send(f"✅ Done. {len(current_poll['entries'])} edit(s) posted for voting.")


@bot.tree.command(name="testresults", description="Manually run the announce-winner job (Top Edit Picker only)")
async def slash_testresults(interaction: discord.Interaction):
    if not has_picker_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Picker can use this.", ephemeral=True)
        return
    await interaction.response.send_message("⏳ Running results job manually...")
    await run_results_job()
    await interaction.followup.send("✅ Done.")


TOKEN = os.environ.get("DISCORD_TOKEN")
if not TOKEN:
    raise RuntimeError("DISCORD_TOKEN environment variable is missing! Set it in Render under Environment.")

bot.run(TOKEN)
