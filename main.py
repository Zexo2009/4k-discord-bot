import discord
from discord.ext import commands
import subprocess
import os

intents = discord.Intents.default()
intents.message_content = True

bot = commands.Bot(command_prefix="!", intents=intents)

@bot.event
async def on_ready():
    print(f'✅ Bot ist online als {bot.user}')

@bot.command()
async def render4k(ctx):
    if not ctx.message.attachments:
        await ctx.send("❌ Bitte ein Video an den Befehl `!render4k` anhängen!")
        return

    attachment = ctx.message.attachments[0]
    input_file = f"temp_{attachment.filename}"
    output_file = f"4K_{attachment.filename}"

    await ctx.send("⚙️ **Rendere Video in 4K (3840x2160)...** Bitte warten.")
    await attachment.save(input_file)

    ffmpeg_command = [
        "ffmpeg", "-y",
        "-i", input_file,
        "-vf", "scale=3840:2160:flags=lanczos",
        "-c:v", "libx264",
        "-preset", "medium",
        "-crf", "18",
        "-c:a", "copy",
        output_file
    ]

    try:
        subprocess.run(ffmpeg_command, check=True)
        file_size_mb = os.path.getsize(output_file) / (1024 * 1024)

        if file_size_mb <= 10:
            await ctx.send(f"✨ **Hier ist dein 4K Render!**", file=discord.File(output_file))
        else:
            await ctx.send(f"⚠️ Rendern erfolgreich, aber das Video ist mit {file_size_mb:.1f} MB zu groß für das Discord-Upload-Limit.")

    except Exception as e:
        await ctx.send(f"❌ Fehler beim Rendering: {e}")

    finally:
        if os.path.exists(input_file): os.remove(input_file)
        if os.path.exists(output_file): os.remove(output_file)

# Token wird gleich aus den Systemeinstellungen geladen
bot.run(os.environ.get("BOT_TOKEN"))
