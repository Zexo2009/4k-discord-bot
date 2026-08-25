"""
main.py — entry point. Starts the Flask website in a background thread, then runs the
Discord bot on the main thread.

Import order matters here and is deliberate:
  config.py    -> no dependencies on the other two, safe to import first
  bot.py       -> imports config.py, defines every command/event/job and the `bot` object
  website.py   -> imports config.py AND bot.py (routes call run_collect_job/run_results_job
                  and read the live `bot` instance)
That one-directional chain (config -> bot -> website) is what keeps this split free of
circular imports — website.py is the only file that knows about both of the others.
"""
import os

from config import init_db
from bot import bot
import website  # noqa: F401 — importing registers every @app.route with the Flask app

TOKEN = os.environ.get("DISCORD_TOKEN")
if not TOKEN:
    raise RuntimeError("DISCORD_TOKEN environment variable is missing! Set it in Render under Environment.")

init_db()
website.run_web_in_background()
bot.run(TOKEN)
