input_template,
            url,
        ]
        proc = await asyncio.create_subprocess_exec(
            *dl_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
        _, stderr = await proc.communicate()

        if proc.returncode != 0:
            await status_msg.edit(content=f"❌ Download fehlgeschlagen:\n```{stderr.decode()[-500:]}```")
            return

        actual_inpu
        for f in os.listdir(DOWNLOAD_DIR):
            if f.startswith(f"{ctx.author.id}_input"):
                actual_input = os.path.join(DOWNLOAD_DIR, f)
                break

        if not actual_input:
            await status_msg.edit(content="❌ Heruntergeladene Datei nicht gefunden.")
            return

        await status_msg.edit(content="⏳ Kodiere nach 4K (2160p)... das kann bei langen Videos dauern.")

        ff_cmd = [
            "ffmpeg", "-y",
            "-i", actual_input,
            "-vf", "scale=-2:2160",
            "-c:v", "libx264", "-preset", "medium", "-crf", "18",
            "-c:a", "aac",
            output_path,
        ]
        proc2 = await asyncio.create_subprocess_exec(
            *ff_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
        _, stderr2 = await proc2.communicate()

        if proc2.returncode != 0:
            await status_msg.edit(content=f"❌ Kodierung fehlgeschlagen:\n```{stderr2.decode()[-500:]}```")
            return

        size_mb = os.path.getsize(output_path) / (1024 * 1024)

        if size_mb > 24:
            await status_msg.edit(
                content=(
                    f"⚠️ Fertig, aber die Datei ist {size_mb:.1f} MB groß – "
                    f"zu groß für Discord-Upload ohne Nitro/Boost (Limit meist ~25 MB). "
                    f"Lade sie z.B. auf einen Filehoster hoch."
                )
            )
        else:
            await status_msg.edit(content="✅ Fertig! Lade Video hoch...")
            await ctx.send(file=discord.File(output_path))

    except Exception as e:
        await status_msg.edit(content=f"❌ Unerwarteter Fehler: {e}")
    finally:
        for f in os.listdir(DOWNLOAD_DIR):
            if f.startswith(str(ctx.author.id)):
                try:
                    os.remove(os.path.join(DOWNLOAD_DIR, f))
                except OSError:
                    pass


TOKEN = os.environ.get("DISCORD_TOKEN")
if not TOKEN:
    raise RuntimeError("DISCORD_TOKEN Umgebungsvariable fehlt! Auf Render unter Environment setzen.")

bot.run(TOKEN)
