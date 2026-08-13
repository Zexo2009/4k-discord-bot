import os
import threading
import asyncio
import subprocess

from flask import Flask
import discord
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


@bot.event
async def on_ready():
    print(f"✅ Bot is online as {bot.user}")


@bot.command()
async def ping(ctx):
    await ctx.send("Pong! 🚀")


@bot.command()
async def help(ctx):
    embed = discord.Embed(
        title="Bot Commands",
        description="Here's what I can do:",
        color=discord.Color.blurple(),
    )
    embed.add_field(name="!ping", value="Check if the bot is online.", inline=False)
    embed.add_field(
        name="!vhq <video URL>",
        value=(
            "Downloads a video (e.g. TikTok) and re-encodes it in 1080p.\n"
            "Videos are trimmed to a max of 60 seconds.\n"
            "Note: YouTube links currently don't work reliably."
        ),
        inline=False,
    )
    embed.add_field(name="!help", value="Show this message.", inline=False)
    await ctx.send(embed=embed)


@bot.command()
async def vhq(ctx, url: str = None):
    """
    Usage: !vhq <video URL>
    Downloads a video and re-encodes it in good quality (1080p).
    """
    if url is None:
        await ctx.send("Please provide a video URL, e.g. `!vhq https://...`")
        return

    status_msg = await ctx.send("⏳ Downloading video...")

    input_template = os.path.join(DOWNLOAD_DIR, f"{ctx.author.id}_input.%(ext)s")
    output_path = os.path.join(DOWNLOAD_DIR, f"{ctx.author.id}_output.mp4")

    try:
        cookies_path = "/etc/secrets/cookies.txt"

        dl_cmd = [
            "yt-dlp",
            # Cap source at 1080p -> less raw data to hold in memory
            "-f", "bestvideo[height<=1080]+bestaudio/best[height<=1080]/best",
            "--merge-output-format", "mp4",
            "-o", input_template,
        ]

        if os.path.exists(cookies_path):
            dl_cmd += ["--cookies", cookies_path]

        dl_cmd.append(url)
        proc = await asyncio.create_subprocess_exec(
            *dl_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
        try:
            _, stderr = await asyncio.wait_for(proc.communicate(), timeout=180)
        except asyncio.TimeoutError:
            proc.kill()
            await status_msg.edit(content="❌ Download timed out. Try a shorter video.")
            return

        if proc.returncode != 0:
            await status_msg.edit(content=f"❌ Download failed:\n\`\`\`{stderr.decode()[-500:]}\`\`\`")
            return

        actual_input = None
        for f in os.listdir(DOWNLOAD_DIR):
            if f.startswith(f"{ctx.author.id}_input"):
                actual_input = os.path.join(DOWNLOAD_DIR, f)
                break

        if not actual_input:
            await status_msg.edit(content="❌ Downloaded file not found.")
            return

        await status_msg.edit(
            content=(
                "⏳ Encoding to 1080p... "
                "Note: on the free server, videos are trimmed to max 60 seconds "
                "to avoid running out of memory."
            )
        )

        MAX_SECONDS = 60  # limit due to 512 MB RAM on the free tier

        ff_cmd = [
            "ffmpeg", "-y",
            "-i", actual_input,
            "-t", str(MAX_SECONDS),          # trim to max length
            "-vf", "scale=-2:1080",
            "-c:v", "libx264",
            "-preset", "ultrafast",          # much less RAM than "medium"
            "-crf", "23",
            "-threads", "1",                 # avoid parallel memory spikes
            "-c:a", "aac",
            output_path,
        ]
        proc2 = await asyncio.create_subprocess_exec(
            *ff_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
        try:
            _, stderr2 = await asyncio.wait_for(proc2.communicate(), timeout=180)
        except asyncio.TimeoutError:
            proc2.kill()
            await status_msg.edit(content="❌ Encoding timed out. Try a shorter video.")
            return

        if proc2.returncode != 0:
            await status_msg.edit(content=f"❌ Encoding failed:\n\`\`\`{stderr2.decode()[-500:]}\`\`\`")
            return

        size_mb = os.path.getsize(output_path) / (1024 * 1024)

        if size_mb > 8:
            await status_msg.edit(
                content=(
                    f"⚠️ Done, but the file is {size_mb:.1f} MB — "
                    f"likely too large to upload on this server (Discord's default limit is ~10 MB "
                    f"unless the server is boosted). Try uploading it to a file host instead."
                )
            )
        else:
            await status_msg.edit(content="✅ Done! Uploading video...")
            try:
                await ctx.send(file=discord.File(output_path))
            except discord.HTTPException:
                await status_msg.edit(
                    content=(
                        f"⚠️ Encoding succeeded, but Discord rejected the upload "
                        f"({size_mb:.1f} MB — too large for this server). "
                        f"Try uploading it to a file host instead."
                    )
                )

    except Exception as e:
        await status_msg.edit(content=f"❌ Unexpected error: {e}")
    finally:
        for f in os.listdir(DOWNLOAD_DIR):
            if f.startswith(str(ctx.author.id)):
                try:
                    os.remove(os.path.join(DOWNLOAD_DIR, f))
                except OSError:
                    pass


TOKEN = os.environ.get("DISCORD_TOKEN")
if not TOKEN:
    raise RuntimeError("DISCORD_TOKEN environment variable is missing! Set it in Render under Environment.")

bot.run(TOKEN)
