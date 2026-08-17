import os
import json
import random
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
SUBMIT_CHANNEL_ID = 1453098499301314662
DISCUSSION_CHANNEL_ID = 1514944188838576270
RESULTS_CHANNEL_ID = 1479559357363650653
PICKER_ROLE_ID = 1514920107912990841
TOP_EDITS_ROLE_ID = 1514918405193596928  # pinged when the daily winner is posted

SUBMIT_CHANNEL_NAME = "editing-rating"
DISCUSSION_CHANNEL_NAME = "top-edit-discussion"
RESULTS_CHANNEL_NAME = "top-edits"
PICKER_ROLE_NAME = "Top Edit Picker"
TOP_EDITS_ROLE_NAME = "Top Edits"

COLLECT_HOUR = 16
RESULTS_HOUR = 20
EU_TZ = ZoneInfo("Europe/Berlin")

POLL_DURATION_HOURS = 4
MAX_POLL_ANSWERS = 10

WINNER_POINTS = 1
POINTS_FILE = "points.json"
DAY_FILE = "day_counter.json"
DEFAULT_DAY = 65  # "today" was day 64 when this was written -> next run is day 65

# (threshold, role_id, label)
RANK_TIERS = [
    (10, 1459931456859144308, "C"),
    (20, 1459931371567976592, "B"),
    (35, 1459931236045820126, "A"),
    (50, 1459931151664676884, "S"),
]

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

START_TIME = datetime.now(timezone.utc)
command_usage = {}

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


def has_picker_permission(member: discord.Member) -> bool:
    if member.guild_permissions.administrator:
        return True
    if PICKER_ROLE_ID and any(r.id == PICKER_ROLE_ID for r in member.roles):
        return True
    return any(role.name == PICKER_ROLE_NAME for role in member.roles)


def format_timedelta(td: timedelta) -> str:
    total_seconds = int(td.total_seconds())
    hours, remainder = divmod(total_seconds, 3600)
    minutes, _ = divmod(remainder, 60)
    if hours and minutes:
        return f"{hours}h {minutes}m"
    if hours:
        return f"{hours}h"
    return f"{minutes}m"


# --- Points storage ---
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

    target_role_id = None
    for threshold, role_id, _label in RANK_TIERS:
        if total_points >= threshold:
            target_role_id = role_id

    all_tier_role_ids = {rid for _, rid, _ in RANK_TIERS}
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
    new_total = add_points(member_id, amount)
    await apply_point_roles(guild, member_id, new_total)
    return new_total


def next_rank_progress(total: int):
    """Returns (label, points_needed) for the next rank, or (None, 0) if maxed out."""
    for threshold, _role_id, label in RANK_TIERS:
        if total < threshold:
            return label, threshold - total
    return None, 0


def current_rank_label(total: int):
    label = None
    for threshold, _role_id, tier_label in RANK_TIERS:
        if total >= threshold:
            label = tier_label
    return label


# --- Day counter ---
def load_day():
    if not os.path.exists(DAY_FILE):
        save_day(DEFAULT_DAY)
        return DEFAULT_DAY
    try:
        with open(DAY_FILE, "r") as f:
            return json.load(f).get("day", DEFAULT_DAY)
    except (json.JSONDecodeError, OSError):
        return DEFAULT_DAY


def save_day(day: int):
    with open(DAY_FILE, "w") as f:
        json.dump({"day": day}, f)


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
]

POINTS_CHECK_FLAVOR = [
    "Keep grinding, the ranks don't climb themselves.",
    "Every point counts, keep it up!",
    "You're closer than you think.",
    "Consistency beats talent. Keep submitting!",
    "Rank up season is always open.",
    "One good edit could change everything.",
    "Slow and steady still wins ranks.",
    "The grind is real, but so are the rewards.",
]

# ============================================================
# Scheduler
# ============================================================

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
                {"author_id": msg.author.id, "author_name": msg.author.display_name, "video_url": video_source}
            )
            if len(entries) >= MAX_POLL_ANSWERS:
                break

        if not entries:
            print(f"No valid edits found in {guild.name} today.")
            continue

        for entry in entries:
            await discussion_channel.send(content=f"**Edit by {entry['author_name']}**\n{entry['video_url']}")

        poll = discord.Poll(question="Vote for today's top edit!", duration=timedelta(hours=POLL_DURATION_HOURS))
        for entry in entries:
            poll.add_answer(text=f"Vote for {entry['author_name']}"[:55])

        sent = await discussion_channel.send(content=f"{picker_role.mention} 📊 Vote for today's top edit!", poll=poll)

        current_poll["message_id"] = sent.id
        current_poll["channel_id"] = discussion_channel.id
        current_poll["entries"] = entries

    print(f"Collect job done. {len(current_poll['entries'])} edit(s) in today's poll.")


async def resolve_tiebreak(tied_indices, results_channel):
    """Randomly splits tied entries into heads/tails, randomly picks the advancing side,
    and repeats until a single winner remains. Posts a running commentary message."""
    remaining = list(tied_indices)
    while len(remaining) > 1:
        assignment = {i: random.choice(["heads", "tails"]) for i in remaining}
        heads = [i for i, side in assignment.items() if side == "heads"]
        tails = [i for i, side in assignment.items() if side == "tails"]
        if not heads or not tails:
            continue  # everyone landed the same side, reflip
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
        top_edits_role = find_role(guild, TOP_EDITS_ROLE_ID, TOP_EDITS_ROLE_NAME)
        if not results_channel:
            continue

        new_total = await award_points(guild, best_entry["author_id"], WINNER_POINTS)

        ping = top_edits_role.mention if top_edits_role else ""

        if used_tiebreak:
            flavor = random.choice(TOP_EDIT_WIN_MESSAGES).format(member=f"<@{best_entry['author_id']}>")
            tiebreak_note = f"\n🪙 *This was decided by a coin-flip tiebreaker!* {flavor}"
        else:
            tiebreak_note = ""

        content = (
            f"{ping} 🏆 **Top Edit of the Day — Day {day_number}**\n"
            f"Congrats <@{best_entry['author_id']}>! Your edit won with **{best_votes}** vote(s)! 🎉\n"
            f"You earned **+{WINNER_POINTS}** point(s) (total: **{new_total}**).{tiebreak_note}\n"
            f"{best_entry['video_url']}"
        )
        await results_channel.send(content=content)
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
            "`testcollect` — Manually run the collect job *(Top Edit Picker only)*\n"
            "`testresults` — Manually run the results job *(Top Edit Picker only)*\n"
            "`addpoints @user <amount>` — Add points *(Top Edit Picker only)*\n"
            "`removepoints @user <amount>` — Remove points *(Top Edit Picker only)*"
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


def build_points_message(member: discord.Member) -> str:
    data = load_points()
    total = data.get(str(member.id), 0)
    rank_label = current_rank_label(total)
    next_label, needed = next_rank_progress(total)
    flavor = random.choice(POINTS_CHECK_FLAVOR)

    rank_text = f"Current rank: **{rank_label}**" if rank_label else "Current rank: *Unranked*"
    if next_label:
        progress_text = f"**{needed}** more point(s) to reach **{next_label}**."
    else:
        progress_text = "You're at the highest rank! 🎉"

    return f"🏅 {member.mention} has **{total}** point(s).\n{rank_text}\n{progress_text}\n*{flavor}*"


def build_ranks_embed():
    embed = discord.Embed(
        title="🏅 Editor Ranks",
        description=(
            "Earn points by winning **Top Edit of the Day** (+1 point automatically) "
            "or through tournaments (awarded manually by Top Edit Picker)."
        ),
        color=discord.Color.blurple(),
    )
    for threshold, _role_id, label in RANK_TIERS:
        embed.add_field(name=f"{label} — {threshold}+ points", value="\u200b", inline=True)
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
async def removepoints(ctx, member: discord.Member = None, amount: int = None):
    if not has_picker_permission(ctx.author):
        await ctx.send("❌ Only Top Edit Picker can use this.")
        return
    if member is None or amount is None:
        await ctx.send("Usage: `!removepoints @user <amount>`")
        return
    new_total = await award_points(ctx.guild, member.id, -amount)
    await ctx.send(f"✅ Removed **{amount}** point(s) from {member.mention}. New total: **{new_total}**")


@bot.command()
async def points(ctx, member: discord.Member = None):
    member = member or ctx.author
    await ctx.send(build_points_message(member))


@bot.command()
async def leaderboard(ctx):
    await ctx.send(embed=build_leaderboard_embed())


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
    await interaction.response.send_message(embed=build_leaderboard_embed())


@bot.tree.command(name="addpoints", description="Add points to a user (Top Edit Picker only)")
@app_commands.describe(member="User to add points to", amount="How many points to add")
async def slash_addpoints(interaction: discord.Interaction, member: discord.Member, amount: int):
    if not has_picker_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Picker can use this.", ephemeral=True)
        return
    new_total = await award_points(interaction.guild, member.id, amount)
    await interaction.response.send_message(f"✅ Added **{amount}** point(s) to {member.mention}. New total: **{new_total}**")


@bot.tree.command(name="removepoints", description="Remove points from a user (Top Edit Picker only)")
@app_commands.describe(member="User to remove points from", amount="How many points to remove")
async def slash_removepoints(interaction: discord.Interaction, member: discord.Member, amount: int):
    if not has_picker_permission(interaction.user):
        await interaction.response.send_message("❌ Only Top Edit Picker can use this.", ephemeral=True)
        return
    new_total = await award_points(interaction.guild, member.id, -amount)
    await interaction.response.send_message(f"✅ Removed **{amount}** point(s) from {member.mention}. New total: **{new_total}**")


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
