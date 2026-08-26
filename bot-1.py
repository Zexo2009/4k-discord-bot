"""
bot.py — the Discord side of Zexo: the bot instance, all commands/events, the daily
collect/results jobs, and every embed builder.

website.py imports `bot`, `run_collect_job`, `run_results_job`, and `get_poll_state` from
here (via config.py's re-export for get_poll_state) to power the web dashboard's manual
trigger buttons and live status — that's the only direction the dependency goes; bot.py
never imports website.py.
"""
import os
import random
import re
import asyncio
from io import BytesIO
from datetime import datetime, timedelta, timezone

import discord
from discord import app_commands
from discord.ext import commands, tasks
from PIL import Image, ImageDraw, ImageFont
import yt_dlp

from config import *  # noqa: F401,F403 — constants, storage, and shared state all live there

intents = discord.Intents.default()
intents.message_content = True
intents.guilds = True
intents.members = True
bot = commands.Bot(command_prefix="!", intents=intents, help_command=None)


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
        picker_role = find_role(message.guild, config["picker_role_id"], PICKER_ROLE_NAME)
        if submit_channel and picker_role and message.channel.id == submit_channel.id:
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
    picker_role = find_role(guild, config["picker_role_id"], PICKER_ROLE_NAME)
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
    picker_role = find_role(guild, config["picker_role_id"], PICKER_ROLE_NAME)

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
            title=f"🏆 Top Edit of the Day — Day {day_number}",
            description=(
                f"{win_line}\n"
                f"Congrats {member_mention}! Your edit won with **{best_votes}** {vote_word}! 🎉\n"
                f"You earned **+{winner_points}** point(s) (total: **{new_total}**)."
            ),
            color=discord.Color.gold(),
        )

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
            # Send the raw link in its OWN message first. If it shares a message with our
            # custom embed, Discord suppresses the link's own preview/player — that's what
            # was causing the winning video to not actually show up. Sending it alone lets
            # Discord unfurl it as a normal playable video, every time.
            await results_channel.send(content=f"{ping} {best_entry['video_url']}".strip())
            await results_channel.send(embed=embed)

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
            "Live preview of edits already queued for the next vote. *Only visible to you.*"
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
            "Purge every risk-word match, in one channel or across all of them."
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
            "Every command works as both `!command` and `/command`.\n"
            "New here? Run **`/tutorial`** for a full walkthrough of how the whole system works.\n\n"
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

    @discord.ui.select(cls=discord.ui.RoleSelect, placeholder="1. Picker role (can vote / run /testcollect)", row=0)
    async def picker_select(self, interaction: discord.Interaction, select: discord.ui.RoleSelect):
        self.picked["picker_role_id"] = select.values[0].id
        await interaction.response.defer()

    @discord.ui.select(cls=discord.ui.RoleSelect, placeholder="2. Manager role (can give/remove points)", row=1)
    async def manager_select(self, interaction: discord.Interaction, select: discord.ui.RoleSelect):
        self.picked["manager_role_id"] = select.values[0].id
        await interaction.response.defer()

    @discord.ui.select(cls=discord.ui.RoleSelect, placeholder="3. Staff role (full permissions, optional)", row=2)
    async def staff_select(self, interaction: discord.Interaction, select: discord.ui.RoleSelect):
        self.picked["staff_role_id"] = select.values[0].id
        await interaction.response.defer()

    @discord.ui.select(cls=discord.ui.RoleSelect, placeholder="4. Role pinged when a winner is announced", row=3)
    async def top_edits_select(self, interaction: discord.Interaction, select: discord.ui.RoleSelect):
        self.picked["top_edits_role_id"] = select.values[0].id
        await interaction.response.defer()

    @discord.ui.button(label="Save setup ✅", style=discord.ButtonStyle.success, row=4)
    async def save_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not self.picked.get("picker_role_id"):
            await interaction.response.send_message("⚠️ Pick at least the Picker role before saving.", ephemeral=True)
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

    embed = discord.Embed(title="⚙️ Zexo Setup Status", color=discord.Color.blurple())
    embed.add_field(name="Submissions channel", value=fmt_channel(config["submit_channel_id"]), inline=False)
    embed.add_field(name="Discussion channel", value=fmt_channel(config["discussion_channel_id"]), inline=False)
    embed.add_field(name="Results channel", value=fmt_channel(config["results_channel_id"]), inline=False)
    embed.add_field(name="Points log channel", value=fmt_channel(config["log_channel_id"]), inline=False)
    embed.add_field(name="Picker role", value=fmt_role(config["picker_role_id"]), inline=True)
    embed.add_field(name="Manager role", value=fmt_role(config["manager_role_id"]), inline=True)
    embed.add_field(name="Staff role", value=fmt_role(config["staff_role_id"]), inline=True)
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



