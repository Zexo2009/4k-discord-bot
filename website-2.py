"""
website.py — the Flask side of Zexo: Discord OAuth login, the "Your Servers" hub, the
per-server dashboard, the settings page, the Control Room (commands/points/badwords/texts),
and the small JSON API those pages call.

Reads/writes config through config.py, and reaches into the live bot via bot.py (the `bot`
instance itself, plus `run_collect_job`/`run_results_job` for the manual trigger buttons).
"""
from datetime import datetime, timedelta, timezone
import os
import threading

from flask import Flask, render_template_string, request, redirect, session, url_for
import requests as http_requests

from config import *  # noqa: F401,F403 — constants, storage, and shared state
from bot import bot, run_collect_job_for_guild, run_results_job_for_guild

app = Flask(__name__)
app.secret_key = os.environ.get("FLASK_SECRET_KEY") or os.environ.get("DISCORD_TOKEN", "zexo-dev-secret")
# Without these, some mobile / in-app browsers (e.g. Discord's own webview) drop the login
# cookie between the OAuth redirect hops, which looks like the login "just repeating itself"
# forever — Discord silently re-approves and bounces you right back to /login. Marking the
# session permanent + giving cookies explicit, browser-friendly attributes fixes that.
app.config.update(
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=True,
    SESSION_COOKIE_HTTPONLY=True,
    PERMANENT_SESSION_LIFETIME=timedelta(days=30),
)

# --- Discord OAuth2 login, for the "Settings" pages on the dashboard ---
# Create these under your bot's application at https://discord.com/developers/applications
# -> OAuth2, and set them as env vars on Render:
#   DISCORD_CLIENT_ID       the application's Client ID
#   DISCORD_CLIENT_SECRET   the application's Client Secret
#   DISCORD_REDIRECT_URI    e.g. https://your-app.onrender.com/callback (must also be added
#                            under OAuth2 -> Redirects in the Discord dev portal, exactly)
OAUTH_CLIENT_ID = os.environ.get("DISCORD_CLIENT_ID")
OAUTH_CLIENT_SECRET = os.environ.get("DISCORD_CLIENT_SECRET")
OAUTH_REDIRECT_URI = os.environ.get("DISCORD_REDIRECT_URI")
DISCORD_API = "https://discord.com/api"
ADMINISTRATOR_BIT = 0x8
VOID_HQ_INVITE_URL = "https://discord.gg/y4CBUdzf2z"
# Permissions Zexo actually asks for when being added to a server: view/send/manage messages,
# embeds, attachments, message history, reactions, managing rank roles, and creating polls.
BOT_INVITE_PERMISSIONS = 562950221982784


def bot_invite_url(guild_id: int = None) -> str:
    """The link that actually ADDS the Zexo bot to a server (scope=bot+applications.commands).
    This is different from VOID_HQ_INVITE_URL, which just joins the Void HQ Discord server —
    using the wrong one here was why 'invite' didn't let people add the bot anywhere new."""
    url = (
        f"{DISCORD_API}/oauth2/authorize?client_id={OAUTH_CLIENT_ID}"
        f"&scope=bot%20applications.commands&permissions={BOT_INVITE_PERMISSIONS}"
    )
    if guild_id:
        url += f"&guild_id={guild_id}&disable_guild_select=true"
    return url


def oauth_configured() -> bool:
    return bool(OAUTH_CLIENT_ID and OAUTH_CLIENT_SECRET and OAUTH_REDIRECT_URI)


# Flask's default session is a SIGNED COOKIE stored in the browser — cookies have a hard ~4KB
# limit. Storing every guild (name + icon hash + permissions) for someone in 10+ servers blows
# past that easily; the browser then silently drops the cookie, so the "login" never actually
# sticks and immediately bounces back to /login — a fast, invisible loop. Fix: keep the cookie
# tiny (just id/username/avatar/access_token) and cache each user's guild list server-side here.
_user_guild_cache = {}  # user_id (str) -> list[{"id","name","permissions","icon"}]


def fetch_user_guilds(user_id: str, access_token: str):
    cached = _user_guild_cache.get(user_id)
    if cached is not None:
        return cached
    res = http_requests.get(
        f"{DISCORD_API}/users/@me/guilds",
        headers={"Authorization": f"Bearer {access_token}"},
        timeout=10,
    )
    if res.status_code != 200:
        return []
    guilds = [
        {"id": g["id"], "name": g["name"], "permissions": g.get("permissions", "0"), "icon": g.get("icon")}
        for g in res.json()
    ]
    _user_guild_cache[user_id] = guilds
    return guilds


@app.route('/login')
def login():
    if not oauth_configured():
        return "⚠️ Discord login isn't configured yet — set DISCORD_CLIENT_ID, DISCORD_CLIENT_SECRET and DISCORD_REDIRECT_URI.", 500
    params = {
        "client_id": OAUTH_CLIENT_ID,
        "redirect_uri": OAUTH_REDIRECT_URI,
        "response_type": "code",
        "scope": "identify guilds",
    }
    query = "&".join(f"{k}={http_requests.utils.quote(v)}" for k, v in params.items())
    return redirect(f"{DISCORD_API}/oauth2/authorize?{query}")


@app.route('/logout')
def logout():
    session.clear()
    return redirect(url_for('home'))


@app.route('/callback')
def oauth_callback():
    if not oauth_configured():
        return "⚠️ Discord login isn't configured yet.", 500
    code = request.args.get("code")
    if not code:
        return redirect(url_for('login'))

    token_res = http_requests.post(
        f"{DISCORD_API}/oauth2/token",
        data={
            "client_id": OAUTH_CLIENT_ID,
            "client_secret": OAUTH_CLIENT_SECRET,
            "grant_type": "authorization_code",
            "code": code,
            "redirect_uri": OAUTH_REDIRECT_URI,
        },
        headers={"Content-Type": "application/x-www-form-urlencoded"},
        timeout=10,
    )
    if token_res.status_code != 200:
        return "❌ Login failed while exchanging the code with Discord. Try again.", 400
    access_token = token_res.json().get("access_token")

    auth_header = {"Authorization": f"Bearer {access_token}"}
    user_res = http_requests.get(f"{DISCORD_API}/users/@me", headers=auth_header, timeout=10)
    guilds_res = http_requests.get(f"{DISCORD_API}/users/@me/guilds", headers=auth_header, timeout=10)
    if user_res.status_code != 200 or guilds_res.status_code != 200:
        return "❌ Login failed while fetching your Discord profile. Try again.", 400

    user = user_res.json()
    guilds = [
        {"id": g["id"], "name": g["name"], "permissions": g.get("permissions", "0"), "icon": g.get("icon")}
        for g in guilds_res.json()
    ]
    _user_guild_cache[str(user.get("id"))] = guilds

    session.permanent = True
    # Keep this small on purpose — see the comment above _user_guild_cache. Guilds live
    # server-side; the cookie only needs enough to look them back up.
    session["user"] = {
        "id": user.get("id"),
        "username": user.get("username"),
        "avatar": user.get("avatar"),
        "access_token": access_token,
    }
    return redirect(url_for('my_servers'))


def current_user():
    return session.get("user")


def user_guilds(user=None):
    """The (possibly cached) list of guilds for the logged-in user — never trust
    session["user"]["guilds"], that key no longer exists; always go through this."""
    user = user or current_user()
    if not user:
        return []
    return fetch_user_guilds(str(user["id"]), user.get("access_token", ""))


def user_is_admin_of(guild_id: int) -> bool:
    """True if the logged-in user has Administrator permission on this guild (matches the
    same gate /setup already uses in Discord, so nobody gets more power from the website
    than they'd have with the slash command)."""
    user = current_user()
    if not user:
        return False
    for g in user_guilds(user):
        if int(g["id"]) == guild_id:
            try:
                return (int(g["permissions"]) & ADMINISTRATOR_BIT) != 0
            except (ValueError, TypeError):
                return False
    return False



@app.route('/')
def home():
    return """
    <!DOCTYPE html><html><head><meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Zexo — by Void HQ</title>
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;500;600;700;800;900&display=swap" rel="stylesheet">
    <style>
      * { box-sizing:border-box; }
      html { scroll-behavior:smooth; }
      body { margin:0; background:#07070d; font-family:'Poppins',Arial,sans-serif; color:#f4f4f8;
             position:relative; overflow-x:hidden; cursor:none; }
      a, button { cursor:none; }
      @media (hover:none) { body, a, button { cursor:auto; } #cursor-glow { display:none; } }

      #particles { position:fixed; inset:0; z-index:0; opacity:0.55; }

      #cursor-glow { position:fixed; top:0; left:0; width:26px; height:26px; border-radius:50%;
                     background:radial-gradient(circle, rgba(139,92,246,0.9), rgba(245,158,11,0.4) 60%, transparent 75%);
                     pointer-events:none; z-index:9999; mix-blend-mode:screen; filter:blur(1px);
                     transform:translate(-50%,-50%); transition:width 0.2s ease, height 0.2s ease, opacity 0.2s ease; }
      #cursor-glow.big { width:52px; height:52px; }

      .orb { position:fixed; border-radius:50%; filter:blur(100px); opacity:0.4; z-index:0; animation:float 14s ease-in-out infinite; }
      .orb1 { width:420px; height:420px; background:#8b5cf6; top:-120px; left:-100px; }
      .orb2 { width:380px; height:380px; background:#f59e0b; bottom:20%; right:-120px; animation-delay:3s; }
      .orb3 { width:280px; height:280px; background:#22d3ee; top:55%; left:60%; animation-delay:6s; }
      @keyframes float { 0%,100%{ transform:translate(0,0) scale(1); } 50%{ transform:translate(30px,-30px) scale(1.08); } }

      /* --- entrance / preloader --- */
      #preloader { position:fixed; inset:0; z-index:999; background:#07070d; display:flex; align-items:center;
                   justify-content:center; transition:opacity 0.6s ease, visibility 0.6s ease; }
      #preloader.hide { opacity:0; visibility:hidden; }
      #preloader .mark { font-size:2rem; font-weight:900; letter-spacing:0.15em;
                          background:linear-gradient(90deg,#8b5cf6,#f59e0b,#22d3ee); background-size:200% auto;
                          -webkit-background-clip:text; background-clip:text; color:transparent; animation:shine 2s linear infinite;
                          opacity:0; animation:fadeInScale 1.1s ease forwards, shine 2s linear infinite 1.1s; }
      @keyframes fadeInScale { 0%{ opacity:0; transform:scale(0.85); } 100%{ opacity:1; transform:scale(1); } }

      nav { position:sticky; top:0; z-index:10; display:flex; align-items:center; justify-content:space-between;
            padding:16px 26px; background:rgba(7,7,13,0.75); backdrop-filter:blur(14px); border-bottom:1px solid rgba(255,255,255,0.06);
            opacity:0; transform:translateY(-14px); animation:navIn 0.8s ease 0.3s forwards; }
      @keyframes navIn { to { opacity:1; transform:translateY(0); } }
      nav .brand { font-weight:800; font-size:1.2rem; }
      nav .nav-btns { display:flex; gap:10px; }
      nav a.cta { display:inline-block; padding:9px 20px; border-radius:999px;
          background:linear-gradient(90deg,#8b5cf6,#f59e0b); color:#fff; text-decoration:none; font-weight:600; font-size:0.85rem;
          transition:transform 0.2s ease, box-shadow 0.2s ease; }
      nav a.cta:hover { transform:translateY(-2px); box-shadow:0 8px 24px rgba(139,92,246,0.45); }
      nav a.invite { display:inline-block; padding:9px 20px; border-radius:999px; background:rgba(255,255,255,0.06);
          border:1px solid rgba(255,255,255,0.14); color:#f4f4f8; text-decoration:none; font-weight:600; font-size:0.85rem;
          transition:background 0.2s ease; }
      nav a.invite:hover { background:rgba(255,255,255,0.12); }

      .hero { min-height:88vh; display:flex; flex-direction:column; align-items:center; justify-content:center;
              text-align:center; padding:60px 20px; position:relative; z-index:1; }
      .badge { display:inline-flex; align-items:center; gap:8px; padding:6px 16px; border-radius:999px; background:rgba(255,255,255,0.06);
               border:1px solid rgba(255,255,255,0.12); font-size:0.8rem; color:#9a9ab0; margin-bottom:18px;
               opacity:0; transform:translateY(16px); animation:riseIn 0.8s ease 0.4s forwards; }
      .dot { width:8px; height:8px; border-radius:50%; background:#22c55e; box-shadow:0 0 10px #22c55e; animation:pulse 1.6s infinite; }
      @keyframes pulse { 0%,100%{ opacity:1; } 50%{ opacity:0.35; } }
      @keyframes riseIn { to { opacity:1; transform:translateY(0); } }
      h1 { font-size:3.2rem; font-weight:900; margin:0; letter-spacing:-0.02em; line-height:1.05;
           background:linear-gradient(90deg,#8b5cf6,#f59e0b,#22d3ee); background-size:200% auto;
           -webkit-background-clip:text; background-clip:text; color:transparent;
           opacity:0; transform:translateY(24px) scale(0.96); animation:riseInBig 1s cubic-bezier(.2,.8,.2,1) 0.55s forwards, shine 4s linear infinite 1.55s;
           position:relative; }
      @keyframes riseInBig { to { opacity:1; transform:translateY(0) scale(1); } }
      @keyframes shine { to { background-position:200% center; } }

      /* --- glitch title: two color-split ghost layers that snap-offset briefly --- */
      #glitch-title::before, #glitch-title::after {
        content: attr(data-text); position:absolute; top:0; left:0; width:100%; height:100%;
        background:inherit; -webkit-background-clip:text; background-clip:text; color:transparent;
        opacity:0; pointer-events:none;
      }
      #glitch-title::before { text-shadow:2px 0 #ff2bd6; }
      #glitch-title::after { text-shadow:-2px 0 #22d3ee; }
      #glitch-title.glitching::before { opacity:0.8; animation:glitchShift 0.28s steps(2) both; }
      #glitch-title.glitching::after { opacity:0.8; animation:glitchShift 0.28s steps(2) both reverse; }
      @keyframes glitchShift {
        0% { clip-path: inset(10% 0 70% 0); transform:translate(-3px,0); }
        20% { clip-path: inset(60% 0 5% 0); transform:translate(3px,0); }
        40% { clip-path: inset(20% 0 55% 0); transform:translate(-2px,0); }
        60% { clip-path: inset(75% 0 2% 0); transform:translate(2px,0); }
        80% { clip-path: inset(5% 0 80% 0); transform:translate(-3px,0); }
        100% { clip-path: inset(40% 0 40% 0); transform:translate(0,0); }
      }

      p.tag { color:#9a9ab0; margin:16px 0 6px; max-width:560px; font-size:1.05rem; line-height:1.5;
              opacity:0; transform:translateY(18px); animation:riseIn 0.9s ease 0.85s forwards; }
      p.credit { color:#6b6b80; font-size:0.85rem; margin:0 0 26px;
                 opacity:0; transform:translateY(14px); animation:riseIn 0.9s ease 1.05s forwards; }
      p.credit .void { color:#c4b5fd; font-weight:700; }
      p.credit .owner { color:#fcd34d; font-weight:600; }
      .btn-row { display:flex; gap:14px; flex-wrap:wrap; justify-content:center;
                 opacity:0; transform:translateY(18px); animation:riseIn 0.9s ease 1.2s forwards; }
      a.primary { display:inline-block; padding:14px 32px; border-radius:999px;
          background:linear-gradient(90deg,#8b5cf6,#f59e0b); color:#fff; text-decoration:none; font-weight:600;
          box-shadow:0 8px 30px rgba(139,92,246,0.4); transition:transform 0.2s ease, box-shadow 0.2s ease; }
      a.primary:hover { transform:translateY(-3px) scale(1.03); box-shadow:0 12px 40px rgba(139,92,246,0.6); }
      a.secondary { display:inline-block; padding:14px 32px; border-radius:999px; background:rgba(255,255,255,0.06);
          border:1px solid rgba(255,255,255,0.14); color:#f4f4f8; text-decoration:none; font-weight:600; transition:background 0.2s ease; }
      a.secondary:hover { background:rgba(255,255,255,0.12); }
      .scroll-hint { position:absolute; bottom:30px; color:#6b6b80; font-size:0.8rem; animation:bounce 2s infinite, fadeIn 1s ease 1.6s both; }
      @keyframes bounce { 0%,100%{ transform:translateY(0); } 50%{ transform:translateY(8px); } }
      @keyframes fadeIn { from{ opacity:0; } to{ opacity:1; } }

      section { max-width:1080px; margin:0 auto; padding:70px 20px; position:relative; z-index:1; }
      section h2 { text-align:center; font-size:2rem; font-weight:800; margin-bottom:8px; }
      section .sub { text-align:center; color:#9a9ab0; margin-bottom:44px; font-size:1rem; }

      /* --- scroll reveal: fades in AND fades back out as it leaves the viewport, with a blur resolve --- */
      .reveal { opacity:0; transform:translateY(38px) scale(0.96); filter:blur(6px);
                transition:opacity 0.7s cubic-bezier(.2,.8,.2,1), transform 0.7s cubic-bezier(.2,.8,.2,1), filter 0.7s ease; }
      .reveal.in { opacity:1; transform:translateY(0) scale(1); filter:blur(0); }
      .reveal.out-up { opacity:0; transform:translateY(-38px) scale(0.97); filter:blur(4px); }

      /* --- whole-page fade/slide transition when navigating away --- */
      body.page-leaving { animation:pageLeave 0.45s cubic-bezier(.6,0,.9,.2) forwards; }
      @keyframes pageLeave { to { opacity:0; transform:scale(0.97) translateY(-10px); filter:blur(4px); } }
      body { transform-origin:center top; }

      .grid { display:grid; grid-template-columns:repeat(auto-fit, minmax(240px, 1fr)); gap:20px; perspective:900px; }
      .card { background:rgba(20,20,31,0.6); border:1px solid rgba(255,255,255,0.08); border-radius:18px;
              padding:26px; backdrop-filter:blur(12px); transition:transform 0.12s ease-out, border-color 0.25s ease, opacity 0.6s ease;
              transform-style:preserve-3d; will-change:transform; }
      .card:hover { border-color:rgba(139,92,246,0.5); }
      .card .icon { font-size:1.8rem; margin-bottom:12px; }
      .icon-node { position:relative; width:56px; height:56px; border-radius:50%; display:flex; align-items:center;
                   justify-content:center; font-size:1.5rem; margin-bottom:14px;
                   background:radial-gradient(circle, rgba(139,92,246,0.16), transparent 72%); }
      .icon-node::before { content:''; position:absolute; inset:0; border-radius:50%;
                   border:1px solid rgba(139,92,246,0.4); }
      .icon-node::after { content:''; position:absolute; inset:-7px; border-radius:50%;
                   border:1px solid rgba(139,92,246,0.14); }
      .card:hover .icon-node { box-shadow:0 0 22px rgba(139,92,246,0.45); }
      .card:hover .icon-node::before { border-color:rgba(245,158,11,0.55); }
      .card h3 { margin:0 0 8px; font-size:1.05rem; }
      .card p { margin:0; color:#9a9ab0; font-size:0.88rem; line-height:1.55; }

      .steps { display:flex; flex-direction:column; gap:18px; max-width:640px; margin:0 auto; }
      .step { display:flex; gap:16px; align-items:flex-start; }
      .step .num { flex-shrink:0; width:36px; height:36px; border-radius:50%; background:linear-gradient(135deg,#8b5cf6,#f59e0b);
                   display:flex; align-items:center; justify-content:center; font-weight:700; font-size:0.9rem; }
      .step .txt h4 { margin:0 0 4px; font-size:0.98rem; }
      .step .txt p { margin:0; color:#9a9ab0; font-size:0.85rem; }

      .owner-band { display:flex; align-items:center; gap:16px; background:rgba(20,20,31,0.6);
                    border:1px solid rgba(255,255,255,0.08); border-radius:20px; padding:22px 26px; backdrop-filter:blur(12px); }
      .owner-band .crown { font-size:2rem; flex-shrink:0; }
      .owner-band h3 { margin:0 0 4px; font-size:1.05rem; }
      .owner-band p { margin:0; color:#9a9ab0; font-size:0.88rem; line-height:1.5; }
      .owner-band b.void { color:#c4b5fd; }
      .owner-band b.owner { color:#fcd34d; }

      .cta-band { text-align:center; background:linear-gradient(135deg, rgba(139,92,246,0.16), rgba(245,158,11,0.10));
                  border:1px solid rgba(255,255,255,0.08); border-radius:24px; padding:50px 26px; }
      .cta-band h2 { margin-bottom:14px; }

      footer { text-align:center; padding:36px 20px 46px; color:#6b6b80; font-size:0.85rem; position:relative; z-index:1; }
      footer .void { color:#c4b5fd; font-weight:600; }
      footer .owner { color:#fcd34d; font-weight:600; }
    </style></head>
    <body>
      <canvas id="particles"></canvas>
      <div id="cursor-glow"></div>
      <div id="preloader"><span class="mark">⚡ ZEXO</span></div>
      <div class="orb orb1"></div><div class="orb orb2"></div><div class="orb orb3"></div>

      <nav>
        <span class="brand">⚡ ZEXO</span>
        <div class="nav-btns">
          <a class="invite" href="__INVITE_URL__" target="_blank">Join Void HQ ↗</a>
          <a class="cta" href="/dashboard">Dashboard →</a>
        </div>
      </nav>

      <div class="hero">
        <div class="badge"><span class="dot"></span> Online &amp; voting daily</div>
        <h1 id="glitch-title" data-text="⚡ ZEXO">⚡ ZEXO</h1>
        <p class="tag">The Top Edit voting system your server actually needs. Submissions, live polls,
          points, ranks, and a full web dashboard — all automatic, all customizable.</p>
        <p class="credit">Built by <span class="void">Zexo</span> for <span class="void">Void HQ</span> · Server owner: <span class="owner">you</span></p>
        <div class="btn-row">
          <a class="primary" href="/dashboard">Open Dashboard →</a>
          <a class="secondary" href="__INVITE_URL__" target="_blank">Join Void HQ ↗</a>
          <a class="secondary" href="#features">See what it does ↓</a>
        </div>
        <div class="scroll-hint">scroll for more ↓</div>
      </div>

      <section id="features">
        <h2 class="reveal">Everything the bot does</h2>
        <div class="sub reveal">One system, fully automated, every single day.</div>
        <div class="grid">
          <div class="card reveal"><div class="icon-node">🎬</div><h3>Any video source</h3>
            <p>YouTube, TikTok, Instagram, Streamable, forwards, replies — anything gets picked up and converted into a real playable clip.</p></div>
          <div class="card reveal"><div class="icon-node">🗳️</div><h3>Daily live polls</h3>
            <p>Every submission that pings the Picker role goes into a real Discord poll, automatically — no cap on how many edits per day.</p></div>
          <div class="card reveal"><div class="icon-node">🏆</div><h3>Points &amp; ranks</h3>
            <p>Winners earn points automatically, rank roles sync themselves, and the leaderboard updates in real time.</p></div>
          <div class="card reveal"><div class="icon-node">⚙️</div><h3>Full web dashboard</h3>
            <p>Log in with Discord and manage everything from your browser — no memorizing slash commands.</p></div>
          <div class="card reveal"><div class="icon-node">✍️</div><h3>100% customizable text</h3>
            <p>Winner announcements, reminders, poll questions, and every timing — write your own, down to the last detail.</p></div>
          <div class="card reveal"><div class="icon-node">🚫</div><h3>Badword filtering</h3>
            <p>Keep the server clean automatically, editable live from the dashboard, no restart needed.</p></div>
        </div>
      </section>

      <section>
        <h2 class="reveal">How it works</h2>
        <div class="sub reveal">Set up once, runs itself every day after that.</div>
        <div class="steps">
          <div class="step reveal"><div class="num">1</div><div class="txt">
            <h4>Post your edit</h4><p>Drop your video in the submissions channel and ping the Picker role.</p></div></div>
          <div class="step reveal"><div class="num">2</div><div class="txt">
            <h4>Zexo collects it</h4><p>At collect time, every valid submission gets pulled together and posted for voting.</p></div></div>
          <div class="step reveal"><div class="num">3</div><div class="txt">
            <h4>The server votes</h4><p>A real Discord poll runs for hours — everyone gets a say in who wins.</p></div></div>
          <div class="step reveal"><div class="num">4</div><div class="txt">
            <h4>Winner gets crowned</h4><p>Points, a custom announcement, and a spot on the leaderboard — fully automatic.</p></div></div>
        </div>
      </section>

      <section>
        <div class="owner-band reveal">
          <div class="crown">👑</div>
          <div>
            <h3>Made for <b class="void">Void HQ</b></h3>
            <p>Zexo was built by <b class="void">Zexo</b> specifically for the Void HQ community. Every setting on the
              dashboard — channels, roles, timings, and every piece of text the bot sends — is fully in the hands of
              the server <b class="owner">owner</b>.</p>
          </div>
        </div>
      </section>

      <section>
        <div class="cta-band reveal">
          <h2>Ready to see it live?</h2>
          <p style="color:#9a9ab0; margin-bottom:24px;">Check the leaderboard, today's vote, and full server config in one place.</p>
          <a class="primary" href="/dashboard">Open Dashboard →</a>
        </div>
      </section>

      <footer>
        Built by <span class="void">Zexo</span> for <span class="void">Void HQ</span> · Owner-managed via the <span class="owner">full dashboard</span>.
      </footer>

      <script>
        window.addEventListener('load', () => {
          setTimeout(() => document.getElementById('preloader').classList.add('hide'), 500);
        });
        const revealEls = document.querySelectorAll('.reveal');
        const io = new IntersectionObserver((entries) => {
          entries.forEach(entry => {
            const el = entry.target;
            if (entry.isIntersecting) {
              el.classList.remove('out-up');
              el.classList.add('in');
            } else {
              // fade back out only if it left ABOVE the viewport, so first-load elements
              // below the fold don't flicker before the user ever scrolls to them
              const rect = entry.boundingClientRect;
              if (rect.top < 0) { el.classList.remove('in'); el.classList.add('out-up'); }
            }
          });
        }, { threshold: 0.15 });
        revealEls.forEach(el => io.observe(el));

        // --- particle network background ---
        const canvas = document.getElementById('particles');
        const ctx = canvas.getContext('2d');
        let W, H, particles;
        const COUNT = window.innerWidth < 700 ? 34 : 70;
        function resize() {
          W = canvas.width = window.innerWidth;
          H = canvas.height = window.innerHeight;
        }
        function initParticles() {
          particles = Array.from({ length: COUNT }, () => ({
            x: Math.random() * W, y: Math.random() * H,
            vx: (Math.random() - 0.5) * 0.4, vy: (Math.random() - 0.5) * 0.4,
            r: Math.random() * 1.6 + 0.6,
          }));
        }
        resize(); initParticles();
        window.addEventListener('resize', () => { resize(); initParticles(); });

        const mouse = { x: -9999, y: -9999 };
        function drawParticles() {
          ctx.clearRect(0, 0, W, H);
          for (const p of particles) {
            p.x += p.vx; p.y += p.vy;
            if (p.x < 0 || p.x > W) p.vx *= -1;
            if (p.y < 0 || p.y > H) p.vy *= -1;
            const dx = p.x - mouse.x, dy = p.y - mouse.y;
            const distToMouse = Math.sqrt(dx * dx + dy * dy);
            if (distToMouse < 140) { p.x += dx / distToMouse * 0.6; p.y += dy / distToMouse * 0.6; }
          }
          for (let i = 0; i < particles.length; i++) {
            for (let j = i + 1; j < particles.length; j++) {
              const a = particles[i], b = particles[j];
              const d = Math.hypot(a.x - b.x, a.y - b.y);
              if (d < 130) {
                ctx.strokeStyle = `rgba(139,92,246,${0.22 * (1 - d / 130)})`;
                ctx.lineWidth = 1;
                ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
              }
            }
          }
          for (const p of particles) {
            ctx.beginPath(); ctx.arc(p.x, p.y, p.r, 0, Math.PI * 2);
            ctx.fillStyle = 'rgba(196,181,253,0.85)'; ctx.fill();
          }
          requestAnimationFrame(drawParticles);
        }
        drawParticles();

        // --- cursor glow (desktop / mouse only) ---
        const glow = document.getElementById('cursor-glow');
        window.addEventListener('mousemove', (e) => {
          mouse.x = e.clientX; mouse.y = e.clientY;
          glow.style.left = e.clientX + 'px';
          glow.style.top = e.clientY + 'px';
        });
        document.querySelectorAll('a, button').forEach(el => {
          el.addEventListener('mouseenter', () => glow.classList.add('big'));
          el.addEventListener('mouseleave', () => glow.classList.remove('big'));
        });
        window.addEventListener('mouseleave', () => { mouse.x = -9999; mouse.y = -9999; });

        // --- glitch title, fires briefly every few seconds ---
        const glitchTitle = document.getElementById('glitch-title');
        function fireGlitch() {
          glitchTitle.classList.add('glitching');
          setTimeout(() => glitchTitle.classList.remove('glitching'), 280);
        }
        setInterval(fireGlitch, 3400);
        glitchTitle.addEventListener('mouseenter', fireGlitch);

        // --- magnetic 3D tilt on feature cards ---
        document.querySelectorAll('.card').forEach(card => {
          card.addEventListener('mousemove', (e) => {
            const rect = card.getBoundingClientRect();
            const px = (e.clientX - rect.left) / rect.width - 0.5;
            const py = (e.clientY - rect.top) / rect.height - 0.5;
            card.style.transform = `translateY(-6px) rotateX(${py * -8}deg) rotateY(${px * 10}deg)`;
          });
          card.addEventListener('mouseleave', () => { card.style.transform = ''; });
        });
        // --- fade/slide-out page transition on internal navigation ---
        document.querySelectorAll('a[href]').forEach(link => {
          const href = link.getAttribute('href');
          if (!href || href.startsWith('#') || link.target === '_blank') return;
          link.addEventListener('click', (e) => {
            e.preventDefault();
            document.body.classList.add('page-leaving');
            setTimeout(() => { window.location.href = href; }, 380);
          });
        });

      </script>
    </body></html>
    """.replace("__INVITE_URL__", VOID_HQ_INVITE_URL)


DASHBOARD_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Zexo Dashboard</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;600;700;800&family=Space+Mono:wght@700&display=swap" rel="stylesheet">
<style>
  :root {
    --bg: #07070d;
    --card: rgba(20,20,31,0.65);
    --border: rgba(255,255,255,0.08);
    --accent: #8b5cf6;
    --accent2: #f59e0b;
    --accent3: #22d3ee;
    --text: #f4f4f8;
    --muted: #9a9ab0;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    font-family: 'Poppins', 'Segoe UI', Arial, sans-serif;
    background: var(--bg);
    color: var(--text);
    padding: 36px 16px 64px;
    position: relative;
    overflow-x: hidden;
  }
  .orb { position: fixed; border-radius: 50%; filter: blur(110px); opacity: 0.4; z-index: -1; animation: float 14s ease-in-out infinite; }
  .orb1 { width: 480px; height: 480px; background: var(--accent); top: -160px; left: -120px; }
  .orb2 { width: 420px; height: 420px; background: var(--accent2); bottom: -160px; right: -100px; animation-delay: 4s; }
  .orb3 { width: 320px; height: 320px; background: var(--accent3); top: 45%; left: 55%; animation-delay: 8s; }
  @keyframes float { 0%,100%{ transform:translate(0,0) scale(1); } 50%{ transform:translate(40px,-40px) scale(1.1); } }

  h1 {
    text-align: center;
    font-size: 2.6rem;
    font-weight: 800;
    letter-spacing: -0.02em;
    margin-bottom: 4px;
    background: linear-gradient(90deg, var(--accent), var(--accent2), var(--accent3));
    background-size: 200% auto;
    -webkit-background-clip: text;
    background-clip: text;
    color: transparent;
    animation: shine 5s linear infinite;
  }
  @keyframes shine { to { background-position: 200% center; } }
  .subtitle { text-align: center; color: var(--muted); margin-bottom: 28px; }

  .status-badge { display: flex; align-items: center; justify-content: center; gap: 8px; margin-bottom: 32px; }
  .status-badge span.pill { display: inline-flex; align-items: center; gap: 8px; padding: 7px 18px; border-radius: 999px;
    background: rgba(255,255,255,0.06); border: 1px solid var(--border); font-size: 0.85rem; color: var(--muted); }
  .status-dot { width: 9px; height: 9px; border-radius: 50%; background: #22c55e; box-shadow: 0 0 10px #22c55e; animation: pulse 1.6s infinite; }
  @keyframes pulse { 0%,100%{ opacity:1; } 50%{ opacity:0.35; } }

  .hero {
    max-width: 1100px; margin: 0 auto 28px; padding: 26px 30px; border-radius: 20px;
    background: linear-gradient(135deg, rgba(139,92,246,0.18), rgba(245,158,11,0.10));
    border: 1px solid var(--border); backdrop-filter: blur(14px);
    display: flex; align-items: center; justify-content: space-between; flex-wrap: wrap; gap: 16px;
    box-shadow: 0 10px 40px rgba(0,0,0,0.35);
  }
  .hero .phase { font-size: 1.05rem; color: var(--muted); margin-bottom: 6px; }
  .hero .phase b { color: var(--text); }
  .countdown { font-family: 'Space Mono', monospace; font-size: 2.4rem; font-weight: 700; letter-spacing: 0.02em;
    background: linear-gradient(90deg, var(--accent3), var(--accent)); -webkit-background-clip: text; background-clip: text; color: transparent; }
  .live-tag { display: inline-flex; align-items: center; gap: 6px; padding: 4px 14px; border-radius: 999px;
    background: rgba(34,197,94,0.15); color: #4ade80; font-weight: 700; font-size: 0.8rem; border: 1px solid rgba(74,222,128,0.35); }
  .entries-tag { color: var(--muted); font-size: 0.9rem; }

  .grid {
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(190px, 1fr));
    gap: 16px;
    max-width: 1100px;
    margin: 0 auto 32px;
  }
  .stat-card {
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 16px;
    padding: 18px 20px;
    backdrop-filter: blur(14px);
    box-shadow: 0 4px 22px rgba(0,0,0,0.35);
    transition: transform 0.2s ease, box-shadow 0.2s ease, border-color 0.2s ease;
  }
  .stat-card:hover { transform: translateY(-4px); border-color: rgba(139,92,246,0.5); box-shadow: 0 10px 30px rgba(139,92,246,0.25); }
  .stat-card .label { color: var(--muted); font-size: 0.75rem; text-transform: uppercase; letter-spacing: 0.06em; }
  .stat-card .value { font-size: 1.7rem; font-weight: 700; margin-top: 6px; }
  .hint { color: var(--muted); font-size: 0.75rem; }

  .section {
    max-width: 1100px;
    margin: 0 auto 28px;
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 18px;
    padding: 22px 26px;
    backdrop-filter: blur(14px);
    box-shadow: 0 4px 22px rgba(0,0,0,0.35);
  }
  .section h2 { margin-top: 0; font-size: 1.25rem; display: flex; align-items: center; gap: 8px; }

  .lb-row {
    display: flex; align-items: center; gap: 14px; padding: 12px 10px; border-radius: 12px;
    border-left: 3px solid var(--tier-color, #444); margin-bottom: 8px; background: rgba(255,255,255,0.02);
    transition: background 0.2s ease, transform 0.15s ease;
  }
  .lb-row:hover { background: rgba(255,255,255,0.05); transform: translateX(4px); }
  .lb-rank { width: 34px; text-align: center; font-weight: 700; font-size: 1.05rem; flex-shrink: 0; }
  .lb-avatar {
    width: 38px; height: 38px; border-radius: 50%; flex-shrink: 0; display: flex; align-items: center; justify-content: center;
    font-weight: 700; font-size: 0.95rem; color: #0b0b12;
    background: var(--tier-color, #666); box-shadow: 0 0 12px color-mix(in srgb, var(--tier-color, #666) 60%, transparent);
  }
  .lb-main { flex: 1; min-width: 0; }
  .lb-name { font-weight: 600; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .lb-bar-track { height: 6px; border-radius: 4px; background: rgba(255,255,255,0.08); margin-top: 6px; overflow: hidden; }
  .lb-bar-fill { height: 100%; border-radius: 4px; background: var(--tier-color, #666); }
  .lb-points { font-family: 'Space Mono', monospace; font-weight: 700; white-space: nowrap; }
  .lb-tier { font-size: 0.72rem; padding: 3px 10px; border-radius: 999px; font-weight: 700; white-space: nowrap;
    background: color-mix(in srgb, var(--tier-color, #666) 25%, transparent); color: var(--tier-color, #ccc); }
  .empty-note { color: var(--muted); text-align: center; padding: 20px 0; }

  .usage-row { display: flex; align-items: center; gap: 12px; margin-bottom: 10px; }
  .usage-name { width: 140px; flex-shrink: 0; font-size: 0.88rem; color: var(--text); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .usage-track { flex: 1; height: 10px; border-radius: 6px; background: rgba(255,255,255,0.06); overflow: hidden; }
  .usage-fill { height: 100%; border-radius: 6px; background: linear-gradient(90deg, var(--accent), var(--accent3)); }
  .usage-count { width: 34px; text-align: right; font-family: 'Space Mono', monospace; font-size: 0.85rem; color: var(--muted); }

  .footer { text-align: center; color: var(--muted); font-size: 0.8rem; margin-top: 36px; }
  .footer .pulse { color: #4ade80; }
</style>
</head>
<body>
  <div class="orb orb1"></div><div class="orb orb2"></div><div class="orb orb3"></div>

  <h1>⚡ Zexo Dashboard</h1>
  <div class="subtitle">Live stats for {{ server_name }}</div>

  <div class="status-badge"><span class="pill"><span class="status-dot"></span> Bot online · auto-refreshing</span></div>
  <div class="status-badge">
    {% if user %}
    <span class="pill">👤 {{ user.username }}
      {% if is_admin %}<a href="/dashboard/{{ guild_id }}/settings" style="color:#4ade80; margin-left:10px;">⚙️ Settings</a>
      <a href="/dashboard/{{ guild_id }}/commands" style="color:#22ffb0; margin-left:10px;">⌁ Control Room</a>{% endif %}
      <a href="/logout" style="color:#f87171; margin-left:10px;">Log out</a>
    </span>
    {% else %}
    <span class="pill"><a href="/login" style="color:#c4b5fd;">🔐 Login with Discord (for settings access)</a></span>
    {% endif %}
  </div>
  <div class="status-badge">
    <span class="pill">
      🔀 <a href="/servers" style="color:#c4b5fd;">All my servers</a>
      {% if other_servers %} · Quick switch:
      {% for s in other_servers %}<a href="/dashboard/{{ s.id }}" style="color:#c4b5fd; margin-left:6px;">{{ s.name }}</a>{% if not loop.last %},{% endif %}{% endfor %}
      {% endif %}
    </span>
  </div>

  <div class="hero">
    <div>
      <div class="phase">
        {% if voting_live %}<span class="live-tag">🔴 LIVE</span>{% endif %}
        <b>{{ phase_label }}</b>
      </div>
      <div class="entries-tag">{{ entries_note }}</div>
    </div>
    <div class="countdown" id="countdown" data-target="{{ countdown_target }}">--:--:--</div>
  </div>

  <div class="grid">
    <div class="stat-card"><div class="label">Members in {{ server_name }}</div><div class="value">👥 {{ member_count }}</div></div>
    <div class="stat-card"><div class="label">Top editor here</div><div class="value">🏆 {{ top_editor.name if top_editor else "—" }}</div></div>
    <div class="stat-card"><div class="label">Current day</div><div class="value">📅 #{{ day_number }}</div></div>
    <div class="stat-card"><div class="label">Uptime</div><div class="value">⏱️ {{ uptime }}</div></div>
    <div class="stat-card"><div class="label">discord.py</div><div class="value">🧩 {{ dpy_version }}</div></div>
  </div>
  <div class="grid" style="margin-top:12px;">
    <div class="stat-card"><div class="label">🌐 Zexo network — servers</div><div class="value">{{ server_count }}</div></div>
    <div class="stat-card"><div class="label">🌐 Zexo network — members</div><div class="value">{{ network_member_count }}</div></div>
  </div>
  <div class="hint" style="margin:10px 2px 0;">💡 The top row is <b>{{ server_name }}</b> only. The 🌐 row is live, real-time totals across every server Zexo is currently in — not fixed to any one server.</div>

  <div class="section">
    <h2>🏆 Leaderboard</h2>
    {% for row in leaderboard %}
    <div class="lb-row" style="--tier-color: {{ row.color }};">
      <div class="lb-rank">{{ row.medal }}</div>
      <div class="lb-avatar">{{ row.initial }}</div>
      <div class="lb-main">
        <div class="lb-name">{{ row.name }}</div>
        <div class="lb-bar-track"><div class="lb-bar-fill" style="width: {{ row.progress }}%;"></div></div>
      </div>
      <span class="lb-tier">{{ row.rank }}</span>
      <div class="lb-points">{{ row.points }} pts</div>
    </div>
    {% else %}
    <div class="empty-note">No points recorded yet. Win a Top Edit to get on the board!</div>
    {% endfor %}
  </div>

  <div class="section">
    <h2>🎬 Command usage since last restart</h2>
    {% for row in usage %}
    <div class="usage-row">
      <div class="usage-name">/{{ row.name }}</div>
      <div class="usage-track"><div class="usage-fill" style="width: {{ row.pct }}%;"></div></div>
      <div class="usage-count">{{ row.count }}</div>
    </div>
    {% else %}
    <div class="empty-note">No commands used yet.</div>
    {% endfor %}
  </div>

  <div class="footer">Zexo by Void HQ · <span class="pulse">●</span> auto-refreshing every 30s</div>
  <script>
    setTimeout(() => location.reload(), 30000);
    const el = document.getElementById('countdown');
    const target = new Date(el.dataset.target).getTime();
    function tick() {
      const diff = Math.max(0, target - Date.now());
      const h = Math.floor(diff / 3600000);
      const m = Math.floor((diff % 3600000) / 60000);
      const s = Math.floor((diff % 60000) / 1000);
      el.textContent = String(h).padStart(2,'0') + ':' + String(m).padStart(2,'0') + ':' + String(s).padStart(2,'0');
    }
    tick();
    setInterval(tick, 1000);
  </script>
</body>
</html>
"""


MY_SERVERS_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Your Servers — Zexo</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;600;700;800&family=Space+Mono:wght@700&display=swap" rel="stylesheet">
<style>
  * { box-sizing:border-box; }
  body { margin:0; font-family:'Poppins',Arial,sans-serif; background:#07070d; color:#f4f4f8; padding:36px 16px 64px;
         position:relative; overflow-x:hidden; }
  .orb { position:fixed; border-radius:50%; filter:blur(110px); opacity:0.4; z-index:-1; animation:float 14s ease-in-out infinite; }
  .orb1 { width:420px; height:420px; background:#8b5cf6; top:-140px; left:-100px; }
  .orb2 { width:380px; height:380px; background:#f59e0b; bottom:-140px; right:-100px; animation-delay:4s; }
  .orb3 { width:280px; height:280px; background:#22d3ee; top:50%; right:60%; animation-delay:7s; }
  @keyframes float { 0%,100%{ transform:translate(0,0) scale(1); } 50%{ transform:translate(30px,-30px) scale(1.08); } }
  .wrap { max-width:680px; margin:0 auto; }

  .top { display:flex; align-items:center; justify-content:space-between; margin-bottom:6px;
         opacity:0; transform:translateY(-10px); animation:fadeDown 0.6s ease forwards; }
  @keyframes fadeDown { to { opacity:1; transform:translateY(0); } }
  h1 { font-size:2rem; font-weight:800; margin:0; background:linear-gradient(90deg,#8b5cf6,#f59e0b,#22d3ee);
       background-size:200% auto; -webkit-background-clip:text; background-clip:text; color:transparent;
       animation:shine 5s linear infinite; }
  @keyframes shine { to { background-position:200% center; } }
  .sub { color:#9a9ab0; font-size:0.88rem; }
  .logout { color:#f87171; text-decoration:none; font-size:0.85rem; }

  .search-wrap { position:relative; margin:22px 0 18px;
                 opacity:0; transform:translateY(14px); animation:riseIn 0.6s ease 0.15s forwards; }
  @keyframes riseIn { to { opacity:1; transform:translateY(0); } }
  .search-wrap .icn { position:absolute; left:16px; top:50%; transform:translateY(-50%); opacity:0.5; font-size:1.05rem; }
  #search { width:100%; padding:13px 16px 13px 44px; border-radius:14px; background:rgba(20,20,31,0.65);
            border:1px solid rgba(255,255,255,0.1); color:#f4f4f8; font-family:inherit; font-size:0.95rem;
            backdrop-filter:blur(14px); }
  #search:focus { outline:none; border-color:rgba(139,92,246,0.6); box-shadow:0 0 0 3px rgba(139,92,246,0.15); }

  .stat-row { display:flex; gap:10px; flex-wrap:wrap; margin-bottom:24px;
              opacity:0; transform:translateY(14px); animation:riseIn 0.6s ease 0.3s forwards; }
  .stat-pill { display:flex; align-items:center; gap:7px; padding:8px 16px; border-radius:999px; font-size:0.82rem; font-weight:600;
               background:rgba(255,255,255,0.05); border:1px solid rgba(255,255,255,0.1); }
  .stat-pill b { font-family:'Space Mono', monospace; }
  .stat-pill.total b { color:#c4b5fd; }
  .stat-pill.active { color:#4ade80; } .stat-pill.active b { color:#4ade80; }
  .stat-pill.missing { color:#f87171; } .stat-pill.missing b { color:#f87171; }
  .stat-dot { width:7px; height:7px; border-radius:50%; }
  .stat-pill.active .stat-dot { background:#4ade80; box-shadow:0 0 8px #4ade80; animation:pulse 1.6s infinite; }
  .stat-pill.missing .stat-dot { background:#f87171; }
  @keyframes pulse { 0%,100%{ opacity:1; } 50%{ opacity:0.35; } }

  .card { display:flex; align-items:center; justify-content:space-between; gap:14px;
          background:rgba(20,20,31,0.65); border:1px solid rgba(255,255,255,0.08); border-radius:18px;
          padding:16px 18px; margin-bottom:14px; backdrop-filter:blur(14px);
          transition:transform 0.22s ease, border-color 0.22s ease, box-shadow 0.22s ease;
          opacity:0; transform:translateY(20px); animation:cardIn 0.5s ease forwards; }
  .card:hover { transform:translateY(-4px); border-color:rgba(139,92,246,0.45); box-shadow:0 10px 30px rgba(139,92,246,0.2); }
  @keyframes cardIn { to { opacity:1; transform:translateY(0); } }
  .card-left { display:flex; align-items:center; gap:14px; min-width:0; }

  /* --- glowing circular icon ring, TicketKing-style hub node --- */
  .icon-ring { position:relative; width:52px; height:52px; flex-shrink:0; border-radius:50%;
               display:flex; align-items:center; justify-content:center;
               background:radial-gradient(circle, rgba(139,92,246,0.18), transparent 70%); }
  .icon-ring::before { content:''; position:absolute; inset:0; border-radius:50%; border:1px solid rgba(139,92,246,0.35); }
  .icon-ring.missing::before { border-color:rgba(248,113,113,0.35); }
  .icon-ring img, .icon-ring .fallback { width:42px; height:42px; border-radius:50%; object-fit:cover;
        box-shadow:0 0 14px rgba(139,92,246,0.35); }
  .icon-ring .fallback { display:flex; align-items:center; justify-content:center; font-weight:800; font-size:1rem;
        background:linear-gradient(135deg,#8b5cf6,#f59e0b); color:#0b0b12; }
  .icon-ring.active::after { content:''; position:absolute; bottom:1px; right:1px; width:13px; height:13px; border-radius:50%;
        background:#4ade80; border:2px solid #07070d; box-shadow:0 0 8px #4ade80; }

  .name-block { min-width:0; }
  .name { font-weight:700; font-size:1rem; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; max-width:220px; }
  .tag { display:inline-block; margin-top:4px; font-size:0.7rem; padding:3px 10px; border-radius:999px; }
  .tag.admin { background:rgba(74,222,128,0.15); color:#4ade80; border:1px solid rgba(74,222,128,0.35); }
  .tag.view { background:rgba(255,255,255,0.06); color:#9a9ab0; border:1px solid rgba(255,255,255,0.12); }
  .tag.missing { background:rgba(248,113,113,0.12); color:#f87171; border:1px solid rgba(248,113,113,0.3); }

  .btns { display:flex; gap:8px; flex-shrink:0; }
  a.btn { display:inline-block; padding:9px 15px; border-radius:999px; text-decoration:none; font-weight:600; font-size:0.8rem;
          background:linear-gradient(90deg,#8b5cf6,#f59e0b); color:#fff; white-space:nowrap;
          transition:transform 0.2s ease, box-shadow 0.2s ease; }
  a.btn:hover { transform:translateY(-2px); box-shadow:0 8px 20px rgba(139,92,246,0.4); }
  a.btn.ghost { background:rgba(255,255,255,0.06); border:1px solid rgba(255,255,255,0.14); color:#f4f4f8; }

  .empty { color:#9a9ab0; text-align:center; padding:40px 20px; background:rgba(20,20,31,0.5);
           border:1px solid rgba(255,255,255,0.08); border-radius:16px; }
  .empty a { color:#c4b5fd; }
  .no-match { display:none; color:#6b6b80; text-align:center; padding:26px 0; font-size:0.85rem; }
</style></head>
<body>
<div class="orb orb1"></div><div class="orb orb2"></div><div class="orb orb3"></div>
<div class="wrap">
  <div class="top">
    <div><h1>⚡ Your Servers</h1><div class="sub">Logged in as {{ user.username }}</div></div>
    <a class="logout" href="/logout">Log out</a>
  </div>

  <div class="search-wrap">
    <span class="icn">🔎</span>
    <input id="search" type="text" placeholder="Search for a server..." oninput="filterServers()">
  </div>

  <div class="stat-row">
    <span class="stat-pill total">🌐 <b>{{ servers|length }}</b> Servers</span>
    <span class="stat-pill active"><span class="stat-dot"></span> <b>{{ active_count }}</b> Active</span>
    <span class="stat-pill missing"><span class="stat-dot"></span> <b>{{ missing_count }}</b> Missing</span>
  </div>

  <div id="server-list">
  {% for s in servers %}
  <div class="card" data-name="{{ s.name|lower }}" style="animation-delay: {{ (loop.index0 * 0.05)|round(2) }}s;">
    <div class="card-left">
      <div class="icon-ring {{ 'active' if s.bot_present else 'missing' }}">
        {% if s.icon_url %}<img src="{{ s.icon_url }}" alt="">
        {% else %}<span class="fallback">{{ s.name[:1]|upper }}</span>{% endif %}
      </div>
      <div class="name-block">
        <div class="name">{{ s.name }}</div>
        {% if not s.bot_present %}<span class="tag missing">Zexo not here</span>
        {% elif s.is_admin %}<span class="tag admin">✓ Admin — full access</span>
        {% else %}<span class="tag view">View only</span>{% endif %}
      </div>
    </div>
    <div class="btns">
      {% if s.bot_present %}
        <a class="btn ghost" href="/dashboard/{{ s.id }}">Dashboard</a>
        {% if s.is_admin %}<a class="btn" href="/dashboard/{{ s.id }}/settings">⚙️ Settings</a>{% endif %}
      {% else %}
        <a class="btn ghost" href="{{ s.invite_url }}" target="_blank">Invite</a>
      {% endif %}
    </div>
  </div>
  {% else %}
  <div class="empty">No mutual servers found. Make sure Zexo is invited to your server, then <a href="/servers">refresh</a>.</div>
  {% endfor %}
  </div>
  <div class="no-match" id="no-match">No servers match your search.</div>
</div>
<script>
  function filterServers() {
    const q = document.getElementById('search').value.trim().toLowerCase();
    const cards = document.querySelectorAll('#server-list .card');
    let visible = 0;
    cards.forEach(c => {
      const match = c.dataset.name.includes(q);
      c.style.display = match ? '' : 'none';
      if (match) visible++;
    });
    document.getElementById('no-match').style.display = (visible === 0 && cards.length > 0) ? 'block' : 'none';
  }
</script>
</body></html>
"""


@app.route('/servers')
def my_servers():
    user = current_user()
    if not user:
        return redirect(url_for('login'))

    servers = []
    for g in user_guilds(user):
        gid = int(g["id"])
        bot_guild = bot.get_guild(gid)
        try:
            is_admin = (int(g["permissions"]) & ADMINISTRATOR_BIT) != 0
        except (ValueError, TypeError):
            is_admin = False
        icon_hash = g.get("icon")
        icon_url = f"https://cdn.discordapp.com/icons/{gid}/{icon_hash}.png?size=64" if icon_hash else None
        servers.append({
            "id": gid,
            "name": g["name"],
            "bot_present": bot_guild is not None,
            "is_admin": is_admin,
            "icon_url": icon_url,
            "invite_url": bot_invite_url(gid),
        })
    # Servers Zexo is actually in come first, admin ones first among those.
    servers.sort(key=lambda s: (not s["bot_present"], not s["is_admin"], s["name"].lower()))
    active_count = sum(1 for s in servers if s["bot_present"])
    missing_count = len(servers) - active_count

    return render_template_string(
        MY_SERVERS_HTML,
        user=user,
        servers=servers,
        active_count=active_count,
        missing_count=missing_count,
        invite_url=bot_invite_url(),
    )


@app.route('/dashboard')
def web_dashboard_default():
    # Used to silently show bot.guilds[0] here — meaning whichever server the bot happened
    # to join first (in practice, almost always the same one server) no matter who you are
    # or which server you actually manage. Send people to pick explicitly instead.
    if current_user():
        return redirect(url_for('my_servers'))
    if not bot.guilds:
        return "Zexo isn't in any server yet."
    return web_dashboard(bot.guilds[0].id)


@app.route('/dashboard/<int:guild_id>')
def web_dashboard(guild_id):
    guild = bot.get_guild(guild_id)
    if not guild:
        return "Server not found, or Zexo isn't in that server.", 404

    uptime = datetime.now(timezone.utc) - START_TIME
    data = load_points(guild_id)
    sorted_entries = sorted(data.items(), key=lambda x: x[1], reverse=True)[:15]
    medals = ["🥇", "🥈", "🥉"]

    leaderboard = []
    for i, (uid, score) in enumerate(sorted_entries):
        name = resolved_names.get(str(uid), f"User {uid}")
        rank_label = current_rank_label(score, guild_id) or UNRANKED_LABEL
        color = "rgb({},{},{})".format(*TIER_COLORS.get(rank_label, (130, 130, 145)))
        medal = medals[i] if i < 3 else f"{i + 1}."
        _next_label, _needed, low, high = next_rank_progress(score, guild_id)
        progress = int(100 * min(1, max(0, (score - low) / max(1, (high - low))))) if high > low else 100
        leaderboard.append({
            "medal": medal, "name": name, "points": score, "rank": rank_label,
            "color": color, "initial": (name[:1] or "?").upper(), "progress": progress,
        })

    total_uses = sum(command_usage.values()) or 1
    usage = [
        {"name": name, "count": count, "pct": int(100 * count / total_uses)}
        for name, count in sorted(command_usage.items(), key=lambda x: -x[1])[:10]
    ]

    # --- Live vote countdown (mirrors build_timeleft_message's logic, but for the browser clock) ---
    config = load_guild_config(guild_id)
    now = datetime.now(EU_TZ)
    collect_dt = now.replace(hour=config["collect_hour"], minute=config.get("collect_minute", 0), second=0, microsecond=0)
    results_dt = now.replace(hour=config["results_hour"], minute=config.get("results_minute", 0), second=0, microsecond=0)
    entries_count = len(get_poll_state(guild_id).get("entries") or [])

    if now < collect_dt:
        countdown_target, phase_label, voting_live = collect_dt, "Voting hasn't started yet", False
        entries_note = "Submissions are still open — check back at collect time."
    elif collect_dt <= now < results_dt:
        countdown_target, phase_label, voting_live = results_dt, "Voting is live", True
        entries_note = f"{entries_count} edit(s) currently in today's vote."
    else:
        countdown_target, phase_label, voting_live = collect_dt + timedelta(days=1), "Voting has ended for today", False
        entries_note = "Winner announced — next round starts soon."

    other_servers = [{"id": g.id, "name": g.name} for g in bot.guilds if g.id != guild_id]

    # Real, live-computed network stats — summed across every server the bot is actually
    # in right now, not hardcoded to any one server.
    network_member_count = sum((g.member_count or 0) for g in bot.guilds)
    network_server_count = len(bot.guilds)
    top_editor = leaderboard[0] if leaderboard else None

    return render_template_string(
        DASHBOARD_HTML,
        uptime=format_timedelta(uptime),
        server_name=guild.name,
        server_count=network_server_count,
        member_count=guild.member_count or 0,
        network_member_count=network_member_count,
        top_editor=top_editor,
        day_number=load_day(guild_id),
        dpy_version=discord.__version__,
        leaderboard=leaderboard,
        usage=usage,
        countdown_target=countdown_target.astimezone(timezone.utc).isoformat(),
        phase_label=phase_label,
        voting_live=voting_live,
        entries_note=entries_note,
        other_servers=other_servers,
        user=current_user(),
        is_admin=user_is_admin_of(guild_id),
        guild_id=guild_id,
    )


SETTINGS_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Zexo Settings</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;600;700;800&family=Space+Mono:wght@700&display=swap" rel="stylesheet">
<style>
  * { box-sizing: border-box; }
  body { margin:0; font-family:'Poppins',Arial,sans-serif; background:#07070d; color:#f4f4f8; padding:36px 16px 64px; }
  .wrap { max-width:760px; margin:0 auto; }
  h1 { font-size:2rem; font-weight:800; background:linear-gradient(90deg,#8b5cf6,#f59e0b,#22d3ee);
       -webkit-background-clip:text; background-clip:text; color:transparent; margin-bottom:4px; }
  .sub { color:#9a9ab0; font-size:0.9rem; margin-bottom:6px; }
  .back { color:#9a9ab0; text-decoration:none; font-size:0.9rem; }
  .card { background:rgba(20,20,31,0.65); border:1px solid rgba(255,255,255,0.08); border-radius:18px;
          padding:24px 26px; margin-top:22px; backdrop-filter:blur(14px); }
  .card h2 { margin:0 0 4px; font-size:1.1rem; display:flex; align-items:center; gap:8px; }
  .card .desc { color:#9a9ab0; font-size:0.8rem; margin-bottom:14px; }
  label { display:block; font-size:0.8rem; color:#9a9ab0; text-transform:uppercase; letter-spacing:0.05em;
          margin:16px 0 6px; }
  label:first-of-type { margin-top:0; }
  select, input[type=number], input[type=text] {
    width:100%; padding:10px 12px; border-radius:10px; background:rgba(255,255,255,0.05);
    border:1px solid rgba(255,255,255,0.12); color:#f4f4f8; font-family:inherit; font-size:0.95rem;
  }
  .row { display:grid; grid-template-columns:1fr 1fr; gap:16px; }
  .row3 { display:grid; grid-template-columns:1fr 1fr 1fr; gap:16px; }
  .hint { color:#6b6b80; font-size:0.72rem; margin-top:5px; }
  button {
    margin-top:26px; width:100%; padding:13px; border:none; border-radius:999px; cursor:pointer;
    background:linear-gradient(90deg,#8b5cf6,#f59e0b); color:#fff; font-weight:700; font-size:1rem;
  }
  .flash { background:rgba(34,197,94,0.15); border:1px solid rgba(74,222,128,0.35); color:#4ade80;
           padding:10px 16px; border-radius:12px; margin-top:18px; }
  .tier-edit { border:1px solid rgba(255,255,255,0.08); border-radius:12px; padding:14px 16px 4px;
               margin:14px 0; background:rgba(255,255,255,0.02); }
  .tier-edit-head { font-weight:700; font-size:0.85rem; color:#c4b5fd; margin-bottom:2px; }
</style></head>
<body>
<div class="wrap">
  <a class="back" href="/servers">🔀 All servers</a>
  <a class="back" href="/dashboard/{{ guild_id }}" style="margin-left:14px;">← Back to dashboard</a>
  <a class="back" href="/dashboard/{{ guild_id }}/commands" style="margin-left:14px;">⌁ Control Room →</a>
  <h1>⚙️ {{ server_name }} Settings</h1>
  <div class="sub">Every channel, role, timing and point value the bot uses — fully in your hands.</div>
  {% if saved %}<div class="flash">✅ Saved — changes take effect on the next collection/results run.</div>{% endif %}
  <form method="POST">

    <div class="card">
      <h2>📺 Channels</h2>
      <div class="desc">Where the bot reads submissions from and posts to.</div>
      <label>Submissions channel</label>
      <select name="submit_channel_id">
        {% for c in channels %}<option value="{{ c.id }}" {% if c.id == config.submit_channel_id %}selected{% endif %}>#{{ c.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Where people post their edits. A submission only counts if it pings the Picker role below.</div>
      <label>Discussion / voting channel</label>
      <select name="discussion_channel_id">
        {% for c in channels %}<option value="{{ c.id }}" {% if c.id == config.discussion_channel_id %}selected{% endif %}>#{{ c.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Where the bot reposts each collected edit and opens the daily poll.</div>
      <label>Results channel</label>
      <select name="results_channel_id">
        {% for c in channels %}<option value="{{ c.id }}" {% if c.id == config.results_channel_id %}selected{% endif %}>#{{ c.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Where the daily winner announcement gets posted.</div>
      <label>Points log channel</label>
      <select name="log_channel_id">
        {% for c in channels %}<option value="{{ c.id }}" {% if c.id == config.log_channel_id %}selected{% endif %}>#{{ c.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 An audit trail of every manual points change (who gave/removed points and why).</div>
    </div>

    <div class="card">
      <h2>🛡️ Roles</h2>
      <div class="desc">Who can submit, who manages, and who gets pinged.</div>
      <label>Picker role (must ping this to submit)</label>
      <select name="picker_role_id">
        {% for r in roles %}<option value="{{ r.id }}" {% if r.id == config.picker_role_id %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Anyone can post — but the bot only picks up a submission if this role gets pinged in the message.</div>
      <label>Manager role</label>
      <select name="manager_role_id">
        {% for r in roles %}<option value="{{ r.id }}" {% if r.id == config.manager_role_id %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Can use manual point-adjustment and moderation commands in Discord.</div>
      <label>Staff role</label>
      <select name="staff_role_id">
        {% for r in roles %}<option value="{{ r.id }}" {% if r.id == config.staff_role_id %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 A lighter permission tier — staff-only slash commands, below Manager.</div>
      <label>Top-Edits ping role</label>
      <select name="top_edits_role_id">
        {% for r in roles %}<option value="{{ r.id }}" {% if r.id == config.top_edits_role_id %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Pinged when the daily winner is announced — give members this role to get notified.</div>
    </div>

    <div class="card">
      <h2>🏆 Ranks &amp; points</h2>
      <div class="desc">Fully custom per server: how many points each rank needs, its emoji, its role, and how many points a win is worth.</div>
      <label>Unranked role (below the lowest rank)</label>
      <select name="unranked_role_id">
        {% for r in roles %}<option value="{{ r.id }}" {% if r.id == config.unranked_role_id %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
      </select>
      <div class="hint">💡 Given to anyone with fewer points than your lowest rank's threshold below.</div>
      {% for threshold, _rid, tier_label, emoji in rank_tiers %}
      <div class="tier-edit">
        <div class="tier-edit-head">Rank {{ tier_label }}</div>
        <div class="row3">
          <div>
            <label>Points needed</label>
            <input type="number" name="rank_threshold_{{ tier_label }}" min="0" max="100000" value="{{ threshold }}">
          </div>
          <div>
            <label>Emoji</label>
            <input type="text" name="rank_emoji_{{ tier_label }}" maxlength="8" value="{{ emoji }}">
          </div>
          <div>
            <label>Role</label>
            <select name="rank_role_{{ tier_label }}">
              {% for r in roles %}<option value="{{ r.id }}" {% if r.id == config.rank_role_ids.get(tier_label) %}selected{% endif %}>@{{ r.name }}</option>{% endfor %}
            </select>
          </div>
        </div>
      </div>
      {% endfor %}
      <div class="hint">💡 Rank names (D/C/B/A/S) stay fixed, but you fully control the points needed, the emoji shown, and which role each rank grants — set any order or spacing you want.</div>
      <label>Points awarded per daily win</label>
      <input type="number" name="winner_points" min="0" max="1000" value="{{ config.winner_points }}">
      <div class="hint">💡 How many points the daily winner earns — this is what moves people up through the ranks above.</div>
    </div>

    <div class="card">
      <h2>⏰ Timing (Europe/Berlin)</h2>
      <div class="desc">Exactly when submissions are collected, and when voting closes — down to the minute.</div>
      <div class="row3">
        <div>
          <label>Collect hour (0-23)</label>
          <input type="number" name="collect_hour" min="0" max="23" value="{{ config.collect_hour }}">
        </div>
        <div>
          <label>Collect minute (0-59)</label>
          <input type="number" name="collect_minute" min="0" max="59" value="{{ config.collect_minute }}">
        </div>
      </div>
      <div class="hint">💡 The daily moment the bot sweeps up new submissions and opens the vote.</div>
      <div class="row3">
        <div>
          <label>Results hour (0-23)</label>
          <input type="number" name="results_hour" min="0" max="23" value="{{ config.results_hour }}">
        </div>
        <div>
          <label>Results minute (0-59)</label>
          <input type="number" name="results_minute" min="0" max="59" value="{{ config.results_minute }}">
        </div>
      </div>
      <div class="hint">💡 The daily moment the bot tallies votes and announces the winner — should be after the poll duration below has had time to run.</div>
      <label>Poll duration (hours)</label>
      <input type="number" name="poll_duration_hours" min="1" max="48" value="{{ config.poll_duration_hours }}">
      <div class="hint">💡 How long each daily poll stays open for voting. Note: this only changes how long a poll stays open, not the results time above — keep the poll duration shorter than the gap between collect and results so it's closed by the time results run.</div>
    </div>

    <button type="submit">Save changes</button>
  </form>
</div>
</body></html>
"""


@app.route('/dashboard/<int:guild_id>/settings', methods=['GET', 'POST'])
def web_settings(guild_id):
    if not current_user():
        return redirect(url_for('login'))
    if not user_is_admin_of(guild_id):
        return "❌ You need Administrator permission on that server to view its settings.", 403

    guild = bot.get_guild(guild_id)
    if not guild:
        return "Server not found, or Zexo isn't in that server.", 404

    saved = False
    if request.method == 'POST':
        channel_ids = {c.id for c in guild.text_channels}
        role_ids = {r.id for r in guild.roles}
        updates = {}
        for field in ("submit_channel_id", "discussion_channel_id", "results_channel_id", "log_channel_id"):
            try:
                val = int(request.form.get(field, 0))
            except ValueError:
                val = 0
            if val in channel_ids:
                updates[field] = val
        for field in ("picker_role_id", "manager_role_id", "staff_role_id", "top_edits_role_id", "unranked_role_id"):
            try:
                val = int(request.form.get(field, 0))
            except ValueError:
                val = 0
            if val in role_ids:
                updates[field] = val
        rank_role_updates = {}
        rank_threshold_updates = {}
        rank_emoji_updates = {}
        for _threshold, _rid, tier_label, _emoji in RANK_TIERS:
            try:
                val = int(request.form.get(f"rank_role_{tier_label}", 0))
            except ValueError:
                val = 0
            if val in role_ids:
                rank_role_updates[tier_label] = val

            try:
                threshold_val = int(request.form.get(f"rank_threshold_{tier_label}", 0))
            except ValueError:
                threshold_val = None
            if threshold_val is not None and 0 <= threshold_val <= 100000:
                rank_threshold_updates[tier_label] = threshold_val

            emoji_val = (request.form.get(f"rank_emoji_{tier_label}") or "").strip()
            if emoji_val:
                rank_emoji_updates[tier_label] = emoji_val[:8]
        if rank_role_updates:
            updates["rank_role_ids"] = rank_role_updates
        if rank_threshold_updates:
            updates["rank_thresholds"] = rank_threshold_updates
        if rank_emoji_updates:
            updates["rank_emojis"] = rank_emoji_updates
        for field in ("collect_hour", "results_hour"):
            try:
                val = int(request.form.get(field, 0))
            except ValueError:
                val = None
            if val is not None and 0 <= val <= 23:
                updates[field] = val
        for field in ("collect_minute", "results_minute"):
            try:
                val = int(request.form.get(field, 0))
            except ValueError:
                val = None
            if val is not None and 0 <= val <= 59:
                updates[field] = val
        try:
            val = int(request.form.get("winner_points", 0))
        except ValueError:
            val = None
        if val is not None and 0 <= val <= 1000:
            updates["winner_points"] = val
        try:
            val = int(request.form.get("poll_duration_hours", 0))
        except ValueError:
            val = None
        if val is not None and 1 <= val <= 48:
            updates["poll_duration_hours"] = val
        save_guild_config(guild_id, updates)
        saved = True

    config = load_guild_config(guild_id)
    channels = [{"id": c.id, "name": c.name} for c in guild.text_channels]
    roles = [{"id": r.id, "name": r.name} for r in guild.roles if not r.is_default()]

    return render_template_string(
        SETTINGS_HTML,
        guild_id=guild_id,
        server_name=guild.name,
        config=config,
        channels=channels,
        roles=roles,
        rank_tiers=get_guild_rank_tiers(guild_id),
        saved=saved,
    )


def run_on_bot_loop(coro, timeout=30):
    """Bridges a Flask request (its own thread) into an async bot coroutine, running it on
    the bot's actual event loop and blocking until it's done. Needed for any dashboard action
    that touches Discord itself (giving points → role sync, forcing a collect/results run)."""
    future = asyncio.run_coroutine_threadsafe(coro, bot.loop)
    return future.result(timeout=timeout)


def require_admin_json(guild_id: int):
    """Returns a Flask error response if the caller isn't logged in / isn't an admin of this
    guild, else None. Used at the top of every /api/ route below."""
    if not current_user():
        return {"ok": False, "error": "Not logged in."}, 401
    if not user_is_admin_of(guild_id):
        return {"ok": False, "error": "Administrator permission required on that server."}, 403
    return None


COMMANDS_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Zexo Control Room</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Sora:wght@400;600;700;800&family=JetBrains+Mono:wght@500;700&display=swap" rel="stylesheet">
<style>
  :root {
    --bg: #05070a;
    --panel: rgba(16,20,26,0.75);
    --border: rgba(120,255,190,0.14);
    --accent: #22ffb0;
    --accent2: #ff7a3d;
    --text: #e8f2ee;
    --muted: #7c9088;
    --danger: #ff5c7a;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0; font-family: 'Sora', Arial, sans-serif; background: var(--bg); color: var(--text);
    padding: 30px 16px 70px; background-image:
      linear-gradient(rgba(34,255,176,0.035) 1px, transparent 1px),
      linear-gradient(90deg, rgba(34,255,176,0.035) 1px, transparent 1px);
    background-size: 34px 34px;
  }
  .wrap { max-width: 980px; margin: 0 auto; }
  .topbar { display:flex; align-items:center; justify-content:space-between; flex-wrap:wrap; gap:12px; margin-bottom:26px; }
  h1 { font-size: 1.9rem; font-weight: 800; margin:0; letter-spacing:-0.01em; color: var(--accent);
       text-shadow: 0 0 22px rgba(34,255,176,0.35); }
  .tag { color: var(--muted); font-size: 0.85rem; font-family:'JetBrains Mono',monospace; }
  .nav a { color: var(--muted); text-decoration:none; font-size:0.85rem; margin-left:16px; }
  .nav a:hover { color: var(--accent); }
  .tabbar { display:flex; gap:8px; flex-wrap:wrap; margin-bottom:26px; }
  .tabbar a { padding:9px 18px; border-radius:10px; text-decoration:none; font-size:0.85rem; font-weight:600;
              color: var(--muted); border:1px solid var(--border); background: rgba(255,255,255,0.02); }
  .tabbar a.active { color:#04120b; background: var(--accent); border-color: var(--accent); }

  .panel { background: var(--panel); border: 1px solid var(--border); border-radius: 16px; padding: 22px 24px;
           margin-bottom: 20px; backdrop-filter: blur(16px); box-shadow: 0 8px 30px rgba(0,0,0,0.4); }
  .panel h2 { margin: 0 0 4px; font-size: 1.05rem; display:flex; align-items:center; gap:8px; }
  .panel .desc { color: var(--muted); font-size: 0.82rem; margin-bottom: 16px; }
  .field { margin-bottom: 12px; }
  .field label { display:block; font-size:0.72rem; text-transform:uppercase; letter-spacing:0.06em; color:var(--muted); margin-bottom:5px; }
  input[type=text], input[type=number], textarea, select {
    width:100%; padding:10px 12px; border-radius:9px; background: rgba(255,255,255,0.04);
    border:1px solid var(--border); color: var(--text); font-family: inherit; font-size:0.92rem;
  }
  textarea { min-height: 90px; resize: vertical; font-family:'JetBrains Mono',monospace; font-size:0.82rem; }
  .row { display:grid; grid-template-columns:1fr 1fr; gap:12px; }
  .row3 { display:grid; grid-template-columns:2fr 1fr auto; gap:12px; align-items:end; }
  button, .btn {
    padding:10px 18px; border-radius:9px; border:1px solid var(--accent); background: rgba(34,255,176,0.1);
    color: var(--accent); font-weight:700; font-size:0.85rem; cursor:pointer; font-family:inherit;
  }
  button:hover, .btn:hover { background: var(--accent); color:#04120b; }
  button.danger, .btn.danger { border-color: var(--danger); color: var(--danger); }
  button.danger:hover { background: var(--danger); color:#1a0006; }
  button.wide { width:100%; margin-top:6px; }
  .chip-list { display:flex; flex-wrap:wrap; gap:8px; margin-top:10px; }
  .chip { display:flex; align-items:center; gap:8px; padding:6px 12px; border-radius:999px;
          background: rgba(255,90,120,0.1); border:1px solid rgba(255,90,120,0.3); font-size:0.8rem;
          font-family:'JetBrains Mono',monospace; }
  .chip button { padding:2px 7px; font-size:0.7rem; border-radius:999px; }
  .toast { position:fixed; bottom:22px; left:50%; transform:translateX(-50%); background: var(--accent);
           color:#04120b; padding:10px 22px; border-radius:999px; font-weight:700; font-size:0.85rem;
           opacity:0; pointer-events:none; transition:opacity 0.25s ease, transform 0.25s ease; z-index:50; }
  .toast.show { opacity:1; transform:translateX(-50%) translateY(-6px); }
  .empty { color: var(--muted); font-size:0.85rem; font-style:italic; }
  .hint { color: var(--muted); font-size:0.72rem; margin-top:6px; }
</style></head>
<body>
<div class="wrap">
  <div class="topbar">
    <div><h1>⌁ Zexo Control Room</h1><div class="tag">{{ server_name }} · live command center</div></div>
    <div class="nav">
      <a href="/servers">🔀 All servers</a>
      <a href="/dashboard/{{ guild_id }}">Dashboard</a>
      <a href="/dashboard/{{ guild_id }}/settings">Config</a>
      <a href="/logout">Log out</a>
    </div>
  </div>

  <div class="tabbar">
    <a class="active" href="#points">Points</a>
    <a href="#badwords">Badwords</a>
    <a href="#triggers">Manual Runs</a>
    <a href="#texts">Custom Texts</a>
  </div>

  <div class="panel" id="points">
    <h2>🏅 Points</h2>
    <div class="desc">Give, remove, or wipe a user's points. Rank roles update automatically, same as the Discord command.</div>
    <div class="row3">
      <div class="field"><label>Discord User ID</label><input type="text" id="pt-user" placeholder="e.g. 123456789012345678"></div>
      <div class="field"><label>Amount</label><input type="number" id="pt-amount" value="1"></div>
      <button onclick="doPoints('add')">Give</button>
    </div>
    <div style="display:flex; gap:10px; margin-top:6px;">
      <button onclick="doPoints('remove')">Remove amount</button>
      <button class="danger" onclick="doPoints('reset')">Reset this user</button>
      <button class="danger" onclick="if(confirm('Reset points for EVERYONE on this server?')) doPoints('reset_all')">Reset ALL points</button>
    </div>
    <div id="points-result" class="hint"></div>
  </div>

  <div class="panel" id="badwords">
    <h2>🚫 Badwords</h2>
    <div class="desc">Words/phrases the bot filters. Changes apply immediately, no restart needed.</div>
    <div class="row3">
      <div class="field"><label>Word or phrase</label><input type="text" id="bw-word" placeholder="add a badword..."></div>
      <div></div>
      <button onclick="addBadword()">Add</button>
    </div>
    <div class="chip-list" id="bw-list">{{ badwords_html|safe }}</div>
  </div>

  <div class="panel" id="triggers">
    <h2>⚡ Manual Runs</h2>
    <div class="desc">Force today's collect or results step right now instead of waiting for the scheduled hour.
      Runs only for <b>{{ server_name }}</b> — every other server the bot is in is completely unaffected.</div>
    <div style="display:flex; gap:10px;">
      <button onclick="doTrigger('collect')">Run Collect Now</button>
      <button onclick="doTrigger('results')">Run Results Now</button>
    </div>
    <div class="hint">💡 Collect pulls in every new submission since the last run and opens today's poll. Results tallies whatever poll is currently open and announces the winner — use it once voting has actually had time to run, not right after Collect.</div>
    <div id="trigger-result" class="hint"></div>
  </div>

  <div class="panel" id="texts">
    <h2>✍️ Custom Texts</h2>
    <div class="desc">100% customizable — leave blank to use the built-in default text. Use <code>{member}</code> where the winner/user should be mentioned.</div>
    <div class="field">
      <label>Winner announcement lines (one per line — a random one is picked each time; leave empty for the built-in 100-line pool)</label>
      <textarea id="tx-winners" placeholder="🏆 {member} takes today's crown!">{{ config.custom_winner_messages|join('\\n') }}</textarea>
    </div>
    <div class="field">
      <label>"Forgot to ping" reminder text</label>
      <textarea id="tx-reminder" placeholder="👋 {member}, don't forget to ping the Picker role!">{{ config.custom_reminder_message or '' }}</textarea>
    </div>
    <div class="field">
      <label>Poll question</label>
      <input type="text" id="tx-question" value="{{ config.custom_poll_question or '' }}" placeholder="Vote for today's top edit!">
    </div>
    <button class="wide" onclick="saveTexts()">Save texts</button>
  </div>
</div>

<div class="toast" id="toast"></div>

<script>
const guildId = {{ guild_id }};
function toast(msg, ok=true) {
  const t = document.getElementById('toast');
  t.textContent = msg;
  t.style.background = ok ? 'var(--accent)' : 'var(--danger)';
  t.classList.add('show');
  setTimeout(() => t.classList.remove('show'), 2200);
}
async function api(path, body) {
  const res = await fetch(path, { method: 'POST', headers: {'Content-Type':'application/json'}, body: JSON.stringify(body) });
  const data = await res.json();
  if (!res.ok || !data.ok) { toast(data.error || 'Something went wrong', false); throw new Error(data.error); }
  return data;
}
async function doPoints(action) {
  const user_id = document.getElementById('pt-user').value.trim();
  const amount = parseInt(document.getElementById('pt-amount').value || '0', 10);
  if (!user_id) { toast('Enter a user ID first', false); return; }
  try {
    const data = await api(`/dashboard/${guildId}/api/points`, { action, user_id, amount });
    document.getElementById('points-result').textContent = data.message;
    toast(data.message);
  } catch (e) {}
}
function renderBadwordChip(word) {
  const span = document.createElement('span');
  span.className = 'chip';
  span.dataset.word = word;
  span.innerHTML = `<span>${word}</span>`;
  const btn = document.createElement('button');
  btn.textContent = '✕';
  btn.onclick = () => removeBadword(word, span);
  span.appendChild(btn);
  return span;
}
async function addBadword() {
  const input = document.getElementById('bw-word');
  const word = input.value.trim();
  if (!word) return;
  try {
    await api(`/dashboard/${guildId}/api/badwords`, { action: 'add', word });
    document.getElementById('bw-list').appendChild(renderBadwordChip(word));
    input.value = '';
    toast(`Added "${word}"`);
  } catch (e) {}
}
async function removeBadword(word, el) {
  try {
    await api(`/dashboard/${guildId}/api/badwords`, { action: 'remove', word });
    el.remove();
    toast(`Removed "${word}"`);
  } catch (e) {}
}
async function doTrigger(action) {
  document.getElementById('trigger-result').textContent = 'Running...';
  try {
    const data = await api(`/dashboard/${guildId}/api/trigger`, { action });
    document.getElementById('trigger-result').textContent = data.message;
    toast(data.message);
  } catch (e) {
    document.getElementById('trigger-result').textContent = '';
  }
}
async function saveTexts() {
  const custom_winner_messages = document.getElementById('tx-winners').value.split('\\n').map(s => s.trim()).filter(Boolean);
  const custom_reminder_message = document.getElementById('tx-reminder').value.trim();
  const custom_poll_question = document.getElementById('tx-question').value.trim();
  try {
    await api(`/dashboard/${guildId}/api/messages`, { custom_winner_messages, custom_reminder_message, custom_poll_question });
    toast('Texts saved ✓');
  } catch (e) {}
}
</script>
</body></html>
"""


@app.route('/dashboard/<int:guild_id>/commands')
def web_commands(guild_id):
    if not current_user():
        return redirect(url_for('login'))
    if not user_is_admin_of(guild_id):
        return "❌ You need Administrator permission on that server to view its command center.", 403

    guild = bot.get_guild(guild_id)
    if not guild:
        return "Server not found, or Zexo isn't in that server.", 404

    config = load_guild_config(guild_id)
    words = load_badwords(guild_id)
    badwords_html = "".join(
        f'<span class="chip" data-word="{w}"><span>{w}</span>'
        f'<button onclick="removeBadword(\'{w}\', this.parentElement)">✕</button></span>'
        for w in words
    ) or '<span class="empty">No badwords configured.</span>'

    return render_template_string(
        COMMANDS_HTML,
        guild_id=guild_id,
        server_name=guild.name,
        config=config,
        badwords_html=badwords_html,
    )


@app.route('/dashboard/<int:guild_id>/api/points', methods=['POST'])
def api_points(guild_id):
    err = require_admin_json(guild_id)
    if err:
        return err
    guild = bot.get_guild(guild_id)
    if not guild:
        return {"ok": False, "error": "Server not found."}, 404

    data = request.get_json(force=True) or {}
    action = data.get("action")
    try:
        user_id = int(data.get("user_id"))
    except (TypeError, ValueError):
        return {"ok": False, "error": "Invalid user ID."}, 400
    try:
        amount = int(data.get("amount", 0))
    except (TypeError, ValueError):
        amount = 0

    if action == "add":
        new_total = run_on_bot_loop(award_points(guild, user_id, amount))
        return {"ok": True, "message": f"Gave {amount} points → total {new_total}."}
    if action == "remove":
        new_total = run_on_bot_loop(award_points(guild, user_id, -amount))
        return {"ok": True, "message": f"Removed {amount} points → total {new_total}."}
    if action == "reset":
        points = load_points(guild_id)
        points[str(user_id)] = 0
        save_points(guild_id, points)
        run_on_bot_loop(apply_point_roles(guild, user_id, 0))
        return {"ok": True, "message": "Points reset for that user."}
    if action == "reset_all":
        save_points(guild_id, {})
        return {"ok": True, "message": "All points on this server were reset."}
    return {"ok": False, "error": "Unknown action."}, 400


@app.route('/dashboard/<int:guild_id>/api/badwords', methods=['POST'])
def api_badwords(guild_id):
    err = require_admin_json(guild_id)
    if err:
        return err
    data = request.get_json(force=True) or {}
    action = data.get("action")
    word = (data.get("word") or "").strip().lower()
    if not word:
        return {"ok": False, "error": "No word given."}, 400

    words = load_badwords(guild_id)
    if action == "add":
        if word not in words:
            words.append(word)
            save_badwords(guild_id, words)
        return {"ok": True, "message": f'Added "{word}".'}
    if action == "remove":
        if word in words:
            words.remove(word)
            save_badwords(guild_id, words)
        return {"ok": True, "message": f'Removed "{word}".'}
    return {"ok": False, "error": "Unknown action."}, 400


@app.route('/dashboard/<int:guild_id>/api/trigger', methods=['POST'])
def api_trigger(guild_id):
    err = require_admin_json(guild_id)
    if err:
        return err
    guild = bot.get_guild(guild_id)
    if not guild:
        return {"ok": False, "error": "Zexo isn't in that server."}, 404
    data = request.get_json(force=True) or {}
    action = data.get("action")
    if action == "collect":
        # Scoped to THIS server only — this used to call the all-servers version and
        # would fire the collect job for every server the bot is in, not just the
        # one you're managing.
        run_on_bot_loop(run_collect_job_for_guild(guild), timeout=120)
        return {"ok": True, "message": f"Collect run finished for {guild.name}."}
    if action == "results":
        run_on_bot_loop(run_results_job_for_guild(guild), timeout=120)
        return {"ok": True, "message": f"Results run finished for {guild.name}."}
    return {"ok": False, "error": "Unknown action."}, 400


@app.route('/dashboard/<int:guild_id>/api/messages', methods=['POST'])
def api_messages(guild_id):
    err = require_admin_json(guild_id)
    if err:
        return err
    data = request.get_json(force=True) or {}
    updates = {}
    if "custom_winner_messages" in data and isinstance(data["custom_winner_messages"], list):
        updates["custom_winner_messages"] = [str(s)[:300] for s in data["custom_winner_messages"]][:200]
    if "custom_reminder_message" in data:
        updates["custom_reminder_message"] = (data["custom_reminder_message"] or None)
    if "custom_poll_question" in data:
        updates["custom_poll_question"] = (data["custom_poll_question"] or None)
    save_guild_config(guild_id, updates)
    return {"ok": True, "message": "Saved."}


def run_web():
    port = int(os.environ.get("PORT", 10000))
    app.run(host='0.0.0.0', port=port)


def run_web_in_background():
    """Starts the Flask site on a daemon thread so it runs alongside the bot, which owns
    the main thread. Called once from main.py, after both bot.py and website.py have
    finished importing (i.e. every route and every bot command already exists)."""
    threading.Thread(target=run_web, daemon=True).start()

