"""
MtagwaBOT - Mfumo kamili wa mauzo (faili moja: bot.py)
=======================================================
Kila kitu kiko ndani ya faili hii moja. Huhitaji tena mauzo_track.py wala mauzo_plus.py.
Data zote za zamani (watumiaji, bidhaa, mauzo, madeni, malipo...) zinabaki kwenye mauzo.db.

VIPENGELE
  Akaunti      : usajili wa simu + password (password imefichwa kwa hashing), /akaunti
  Usajili      : ofa ya siku 7, kisha 10,000 TZS kwa mwezi; kufungwa/kufunguliwa kiotomatiki
  Malipo       : /lipia + ID ya muamala, admin anathibitisha kwa kitufe (/malipo)
  Rufaa        : aliyemleta mtu anapata 5,000 TZS pale mtu huyo anapolipia
  Bidhaa       : /weka_bidhaa (na picha), /bidhaa_zangu, /jaza_stoo, /badili_bei,
                 /futa_bidhaa, /hariri_jina, /picha, /tazama, /katalogi
  Mauzo        : 🛒 Uza kwa vitufe, /uza, /tengua, mauzo ya mkopo
  Fedha        : /faida (faida halisi), /matumizi, /deni /madeni /lipa_deni
  Ripoti       : /leo, ripoti ya kila usiku, /ripoti_excel, /historia
  Kutoa pesa   : /withdraw (admin anaidhinisha)
  Soko         : 🎬 Soko (video/picha kama TikTok), /chapisha, likes, 🛍️ Agiza, /tafuta, /maarufu, link za kushiriki
  Zaidi        : /pointi (kutazama video), /risiti, /wateja + /ofa (WhatsApp), /ongeza_msaidizi,
                 /badili_password, 💬 Admin (msaada), /masharti
  Admin        : /watumiaji /mtumiaji /bidhaa_za /malipo /ongeza_siku /funga /reset_password
                 /ripoti /takwimu /maombi /tangaza /backup /ping /tiketi /jibu /futa_akaunti
                 /soko_ripoti /soko_ondoa /soko_rudisha

KUWASHA: weka siri kwenye faili ya .env (folda moja na bot.py), kisha: python bot.py
  BOT_TOKEN=...            ADMIN_ID=8604025635
  PAY_INFO=Tuma kwa M-Pesa namba 0756639110 (jina: Gidion Kinyina)
  TZ=Africa/Dar_es_Salaam  (kwenye server zenye saa ya UTC)
  SQLITE_WAL=0             (kwenye PythonAnywhere)      PROXY_URL=...  (akaunti ya bure ya PythonAnywhere)

MAHITAJI: pip install -U "python-telegram-bot[job-queue]" openpyxl
"""
import asyncio
import csv
import functools
import hashlib
import hmac
import io
import math
import os
import random
import re
import sqlite3
import tempfile
import time
import urllib.parse
from contextlib import closing
from datetime import datetime, timedelta, timezone

from telegram import (
    BotCommand, BotCommandScopeChat, InlineKeyboardButton, InlineKeyboardMarkup,
    InputMediaPhoto, InputMediaVideo, ReplyKeyboardMarkup, Update,
)
from telegram import InlineKeyboardButton as Btn
from telegram import InlineKeyboardMarkup as Kb
from telegram.ext import (
    Application, CallbackQueryHandler, CommandHandler, ContextTypes,
    ConversationHandler, MessageHandler, filters,
)

BASE_DIR = os.path.dirname(os.path.abspath(__file__))


def load_env_file():
    """Inasoma faili ya .env iliyo folda moja na bot.py (BOT_TOKEN=..., ADMIN_ID=..., n.k.).
    Mazingira yaliyowekwa tayari (export / hosting panel) yanashinda faili hii."""
    path = os.path.join(BASE_DIR, ".env")
    if not os.path.exists(path):
        return
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            if line.startswith("export "):
                line = line[7:].strip()
            key, _, val = line.partition("=")
            val = val.strip()
            if len(val) >= 2 and val[0] == val[-1] and val[0] in "\"'":
                val = val[1:-1]
            os.environ.setdefault(key.strip(), val)
    if "TZ" in os.environ and hasattr(time, "tzset"):
        time.tzset()          # TZ=Africa/Dar_es_Salaam kwenye server zenye saa ya UTC


load_env_file()

# ====== MIPANGILIO ======
DB_FILE = os.environ.get("DB_PATH") or os.path.join(BASE_DIR, "mauzo.db")   # kwa chaguo-msingi: folda ya bot.py
USE_WAL = os.environ.get("SQLITE_WAL", "1") != "0"   # weka SQLITE_WAL=0 kwenye hosting yenye diski ya mtandao (mf. PythonAnywhere)
# Admin ID inasomwa kutoka ADMIN_ID (export ADMIN_ID="123,456" kwa admin zaidi ya mmoja)
ADMIN_IDS = [int(x) for x in os.environ.get("ADMIN_ID", "").split(",") if x.strip().isdigit()]
COMMISSION_RATE = 0.0            # commission ya 2% imeondolewa (weka 0.02 kuirudisha)
REFERRAL_RATE = 0.0              # % ya mauzo kwa aliyemleta (imeondolewa)
# --- Usajili wa mwezi ---
SUB_PRICE = 10000                # TZS kwa mwezi
SUB_DAYS = 30                    # siku zinazoongezwa kila malipo
TRIAL_DAYS = 7                   # siku za ofa bure baada ya kujisajili
REFERRAL_BONUS = 5000            # TZS anazopata aliyemleta mtu pale mtu huyo anapolipia
BONUS_EVERY_PAYMENT = False      # False = bonasi mara ya kwanza tu mtu anapolipia; True = kila malipo
PAY_INFO = os.environ.get(
    "PAY_INFO",
    "Tuma pesa kwa M-Pesa / Tigo Pesa / Airtel Money kwenda namba 07XXXXXXXX (jina: JINA LAKO).",
)
REMINDER_HOURS = 6               # bot inakagua kila masaa haya kutuma vikumbusho
MAX_FAILED_LOGINS = 5           # makosa ya password kabla ya account kufungwa
MIN_WITHDRAW = 1000              # kiwango cha chini cha kutoa (TZS)
CURRENCY = "TZS"
BOT_USERNAME = "MtagwaBOT"


# ====== DATABASE ======
def db():
    conn = sqlite3.connect(DB_FILE, timeout=10)
    conn.row_factory = sqlite3.Row
    if USE_WAL:
        conn.execute("PRAGMA synchronous=NORMAL")  # kwa WAL: hakuna kusubiri diski kila ukiandika (salama)
    return conn


PRODUCTS_SQL = """CREATE TABLE IF NOT EXISTS products(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT,
    price REAL,
    stock INTEGER,
    owner_id INTEGER,
    cost REAL DEFAULT 0
)"""


_KEEPER = None   # muunganisho mmoja unaobaki wazi: unazuia WAL isifungwe na kuundwa upya kila amri


def init_db():
    global _KEEPER
    with closing(db()) as c0:
        c0.execute("PRAGMA journal_mode=WAL" if USE_WAL else "PRAGMA journal_mode=DELETE")
    if USE_WAL and _KEEPER is None:
        _KEEPER = db()
        _KEEPER.execute("SELECT 1").fetchone()
    with closing(db()) as conn, conn:
        conn.executescript("""
        CREATE TABLE IF NOT EXISTS users(
            user_id INTEGER PRIMARY KEY,
            name TEXT,
            referrer_id INTEGER,
            balance REAL DEFAULT 0,
            joined TEXT
        );
        CREATE TABLE IF NOT EXISTS sales(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            seller_id INTEGER,
            product_id INTEGER,
            qty INTEGER,
            total REAL,
            commission REAL,
            ref_commission REAL,
            ts TEXT,
            profit REAL DEFAULT 0
        );
        CREATE TABLE IF NOT EXISTS payments(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            amount REAL,
            txn_ref TEXT UNIQUE,
            note TEXT,
            status TEXT DEFAULT 'pending',
            ts TEXT,
            decided_ts TEXT
        );
        CREATE TABLE IF NOT EXISTS bonuses(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            from_user INTEGER,
            amount REAL,
            ts TEXT
        );
        CREATE TABLE IF NOT EXISTS expenses(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            amount REAL,
            note TEXT,
            ts TEXT
        );
        CREATE TABLE IF NOT EXISTS debts(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            customer TEXT,
            amount REAL,
            paid REAL DEFAULT 0,
            note TEXT,
            ts TEXT,
            sale_id INTEGER
        );
        CREATE TABLE IF NOT EXISTS settings(
            key TEXT PRIMARY KEY,
            value TEXT
        );
        CREATE TABLE IF NOT EXISTS posts(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            kind TEXT,
            file_id TEXT,
            caption TEXT,
            ts TEXT,
            active INTEGER DEFAULT 1,
            likes INTEGER DEFAULT 0,
            views INTEGER DEFAULT 0
        );
        CREATE TABLE IF NOT EXISTS post_likes(
            post_id INTEGER, user_id INTEGER, PRIMARY KEY(post_id, user_id)
        );
        CREATE TABLE IF NOT EXISTS post_seen(
            user_id INTEGER, post_id INTEGER, PRIMARY KEY(user_id, post_id)
        );
        CREATE TABLE IF NOT EXISTS post_reports(
            post_id INTEGER, user_id INTEGER, ts TEXT, PRIMARY KEY(post_id, user_id)
        );
        CREATE TABLE IF NOT EXISTS tickets(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER, text TEXT, status TEXT DEFAULT 'open',
            ts TEXT, answer TEXT, answered_ts TEXT
        );
        CREATE TABLE IF NOT EXISTS customers(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER, name TEXT, phone TEXT, note TEXT, ts TEXT
        );
        CREATE TABLE IF NOT EXISTS staff(
            owner_id INTEGER, staff_id INTEGER, status TEXT DEFAULT 'pending', ts TEXT,
            PRIMARY KEY(owner_id, staff_id)
        );
        CREATE TABLE IF NOT EXISTS orders(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            post_id INTEGER, buyer_id INTEGER, seller_id INTEGER, text TEXT,
            status TEXT DEFAULT 'pending', ts TEXT
        );
        CREATE TABLE IF NOT EXISTS view_rewards(
            user_id INTEGER, post_id INTEGER, ts TEXT, PRIMARY KEY(user_id, post_id)
        );
        CREATE TABLE IF NOT EXISTS point_redemptions(
            id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, days INTEGER, ts TEXT
        );
        CREATE TABLE IF NOT EXISTS withdrawals(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            amount REAL,
            phone TEXT,
            status TEXT DEFAULT 'pending',
            ts TEXT
        );
        """)
        # Jedwali la bidhaa: owner_id NULL = bidhaa za duka (admin), vinginevyo ni bidhaa za mtumiaji
        conn.execute(PRODUCTS_SQL)
        old = conn.execute("SELECT sql FROM sqlite_master WHERE name='products'").fetchone()[0]
        if "UNIQUE" in old.upper().split("PRIMARY KEY")[1]:   # jedwali la zamani lenye name UNIQUE
            conn.execute("ALTER TABLE products RENAME TO products_old")
            conn.execute(PRODUCTS_SQL)
            conn.execute("INSERT INTO products(id,name,price,stock) SELECT id,name,price,stock FROM products_old")
            conn.execute("DROP TABLE products_old")
        pcols = {r["name"] for r in conn.execute("PRAGMA table_info(products)")}
        for col, typ in [("owner_id", "INTEGER"), ("cost", "REAL DEFAULT 0"), ("active", "INTEGER DEFAULT 1"), ("photo_id", "TEXT")]:
            if col not in pcols:
                conn.execute(f"ALTER TABLE products ADD COLUMN {col} {typ}")
        scols = {r["name"] for r in conn.execute("PRAGMA table_info(sales)")}
        if "profit" not in scols:
            conn.execute("ALTER TABLE sales ADD COLUMN profit REAL DEFAULT 0")
        if "sold_by" not in scols:
            conn.execute("ALTER TABLE sales ADD COLUMN sold_by INTEGER")
        conn.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_products_owner_name ON products(IFNULL(owner_id,0), name)")
        # Safu mpya za akaunti (zinaongezwa kama hazipo, data ya zamani haipotei)
        cols = {r["name"] for r in conn.execute("PRAGMA table_info(users)")}
        for col, typ in [
            ("username", "TEXT"), ("phone", "TEXT"), ("password_hash", "TEXT"),
            ("salt", "TEXT"), ("registered_at", "TEXT"),
            ("failed_logins", "INTEGER DEFAULT 0"),
            ("trial_until", "TEXT"), ("paid_until", "TEXT"), ("last_reminder", "TEXT"),
            ("report_on", "INTEGER DEFAULT 1"), ("last_report", "TEXT"),
            ("points", "INTEGER DEFAULT 0"), ("shop_name", "TEXT"), ("terms_at", "TEXT"),
        ]:
            if col not in cols:
                conn.execute(f"ALTER TABLE users ADD COLUMN {col} {typ}")
        conn.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_users_phone ON users(phone) WHERE phone IS NOT NULL")
        for ix in (
            "CREATE INDEX IF NOT EXISTS idx_sales_seller_ts ON sales(seller_id, ts)",
            "CREATE INDEX IF NOT EXISTS idx_sales_product ON sales(product_id)",
            "CREATE INDEX IF NOT EXISTS idx_products_owner ON products(owner_id, active)",
            "CREATE INDEX IF NOT EXISTS idx_debts_user ON debts(user_id)",
            "CREATE INDEX IF NOT EXISTS idx_expenses_user_ts ON expenses(user_id, ts)",
            "CREATE INDEX IF NOT EXISTS idx_payments_user ON payments(user_id, status)",
            "CREATE INDEX IF NOT EXISTS idx_withdrawals_user ON withdrawals(user_id, status)",
            "CREATE INDEX IF NOT EXISTS idx_users_referrer ON users(referrer_id)",
            "CREATE INDEX IF NOT EXISTS idx_posts_active ON posts(active, id)",
            "CREATE INDEX IF NOT EXISTS idx_posts_user ON posts(user_id)",
            "CREATE INDEX IF NOT EXISTS idx_orders_seller ON orders(seller_id, status)",
            "CREATE INDEX IF NOT EXISTS idx_customers_user ON customers(user_id)",
            "CREATE INDEX IF NOT EXISTS idx_tickets_status ON tickets(status)",
        ):
            conn.execute(ix)
        # Watumiaji waliokuwa wamesajiliwa kabla ya mfumo wa malipo wanapewa ofa ya siku TRIAL_DAYS kuanzia sasa
        conn.execute(
            "UPDATE users SET trial_until=? WHERE password_hash IS NOT NULL AND trial_until IS NULL AND paid_until IS NULL",
            (add_days(now(), TRIAL_DAYS),),
        )


FMT = "%Y-%m-%d %H:%M:%S"


def now():
    return datetime.now().strftime(FMT)


def add_days(ts, days):
    return (datetime.strptime(ts, FMT) + timedelta(days=days)).strftime(FMT)


def money(x):
    return f"{x:,.0f} {CURRENCY}"


def is_admin(uid):
    return uid in ADMIN_IDS


# ====== USALAMA WA PASSWORD ======
def hash_password(password, salt=None):
    salt = salt or os.urandom(16).hex()
    h = hashlib.pbkdf2_hmac("sha256", password.encode(), bytes.fromhex(salt), 200_000).hex()
    return h, salt


def check_password(uid, password):
    """Inarudisha (ok, ujumbe). Inafunga account baada ya makosa mengi."""
    with closing(db()) as conn, conn:
        u = conn.execute("SELECT * FROM users WHERE user_id=?", (uid,)).fetchone()
        if not u or not u["password_hash"]:
            return False, "Bado hujajisajili. Tumia /jisajili"
        if u["failed_logins"] >= MAX_FAILED_LOGINS:
            return False, "🔒 Account imefungwa kwa makosa mengi. Wasiliana na admin."
        h, _ = hash_password(password, u["salt"])
        if hmac.compare_digest(h, u["password_hash"]):
            conn.execute("UPDATE users SET failed_logins=0 WHERE user_id=?", (uid,))
            return True, ""
        conn.execute("UPDATE users SET failed_logins=failed_logins+1 WHERE user_id=?", (uid,))
        left = MAX_FAILED_LOGINS - u["failed_logins"] - 1
        return False, f"❌ Password si sahihi. Nafasi zilizobaki: {left}"


def is_registered(uid):
    with closing(db()) as conn:
        r = conn.execute("SELECT password_hash FROM users WHERE user_id=?", (uid,)).fetchone()
    return bool(r and r["password_hash"])


def normalize_phone(text):
    t = re.sub(r"[\s\-]", "", text)
    m = re.fullmatch(r"(?:\+?255|0)([67]\d{8})", t)
    return "255" + m.group(1) if m else None


NOT_REG_MSG = "⚠️ Jisajili kwanza kwa kutumia /jisajili"

# ====== MENYU YA VITUFE ======
BTN_BALANCE = "💰 Balance"
BTN_WITHDRAW = "💸 Withdraw Commission"
BTN_HISTORY = "📜 History"
BTN_PRODUCTS = "📦 Bidhaa"
BTN_SALES = "📊 Mauzo"
BTN_REFER = "🔗 Rufaa"
BTN_ACCOUNT = "👤 Akaunti"
BTN_MYPROD = "💼 Bidhaa Zangu"
BTN_PROFIT = "💹 Faida"
BTN_PAY = "💳 Lipia"
BTN_SELL = "🛒 Uza"
BTN_FEED = "🎬 Soko"
BTN_CUSTOMERS = "👥 Wateja"
BTN_POINTS = "⭐ Pointi"
BTN_SUPPORT = "💬 Admin"
BTN_ORDERS = "🛍️ Maagizo"
BTN_STATS = "📈 Takwimu"
BTN_TICKETS = "🎫 Tiketi"
BTN_POST = "📣 Chapisha"
BTN_TODAY = "📊 Leo"
BTN_DEBTS = "📒 Madeni"
BTN_EXPENSES = "🧮 Matumizi"
BTN_HELP = "❓ Msaada"
BTN_PAYMENTS = "💳 Malipo"
BTN_STATUS = "📅 Hali"
BTN_USERS = "👥 Watumiaji"
BTN_REPORT = "📈 Ripoti"
BTN_REQUESTS = "🧾 Maombi"
MENU_TEXTS = {BTN_BALANCE, BTN_WITHDRAW, BTN_HISTORY, BTN_PRODUCTS, BTN_SALES,
              BTN_REFER, BTN_ACCOUNT, BTN_MYPROD, BTN_PROFIT, BTN_PAY, BTN_STATUS, BTN_SELL, BTN_TODAY, BTN_FEED, BTN_POST, BTN_CUSTOMERS, BTN_POINTS, BTN_SUPPORT, BTN_ORDERS, BTN_STATS, BTN_TICKETS, BTN_DEBTS, BTN_EXPENSES, BTN_HELP, BTN_PAYMENTS, BTN_USERS, BTN_REPORT, BTN_REQUESTS}


def menu_for(uid):
    rows = [
        [BTN_FEED, BTN_POST],
        [BTN_SELL, BTN_TODAY],
        [BTN_MYPROD, BTN_PROFIT],
        [BTN_DEBTS, BTN_EXPENSES],
        [BTN_CUSTOMERS, BTN_ORDERS],
        [BTN_POINTS, BTN_SUPPORT],
        [BTN_BALANCE, BTN_HISTORY],
        [BTN_WITHDRAW, BTN_REFER],
        [BTN_PAY, BTN_STATUS],
        [BTN_ACCOUNT, BTN_HELP],
    ]
    if is_admin(uid):
        rows += [[BTN_USERS, BTN_REPORT], [BTN_REQUESTS, BTN_PAYMENTS], [BTN_STATS, BTN_TICKETS]]
    return ReplyKeyboardMarkup(rows, resize_keyboard=True)


def onboarding_hint(uid):
    with closing(db()) as conn:
        n = conn.execute("SELECT COUNT(*) n FROM products WHERE owner_id=? AND active=1", (uid,)).fetchone()["n"]
        sl = conn.execute("SELECT COUNT(*) n FROM sales WHERE seller_id=?", (uid,)).fetchone()["n"]
    if n == 0:
        return ("👉 Hatua ya 1: weka bidhaa yako ya kwanza.\n"
                "Mfano: /weka_bidhaa Sukari 2500 3000 20\n(jina, bei ya kununua, bei ya kuuza, idadi ya stoo)")
    if sl == 0:
        return "👉 Hatua ya 2: rekodi mauzo yako ya kwanza kwa kubonyeza 🛒 Uza."
    return ""


# ====== USAJILI WA MWEZI: OFA YA SIKU 7 + MALIPO ======
def access_end(u):
    ends = [x for x in (u["trial_until"], u["paid_until"]) if x]
    return max(ends) if ends else None


def sub_state(u):
    """Inarudisha (active, until, kind): kind = admin | paid | trial | none"""
    if is_admin(u["user_id"]):
        return True, None, "admin"
    end = access_end(u)
    if not end:
        return False, None, "none"
    kind = "paid" if u["paid_until"] and u["paid_until"] == end else "trial"
    return end > now(), end, kind


def days_left(end):
    secs = (datetime.strptime(end, FMT) - datetime.now()).total_seconds()
    return max(0, math.ceil(secs / 86400))


def status_text(u):
    active, end, kind = sub_state(u)
    if kind == "admin":
        return "👑 Admin (hakuna ukomo)"
    if not end:
        return "🔒 Hujaanza. Jisajili kwa /jisajili"
    if active and kind == "trial":
        return f"🎁 Ofa ya bure: siku {days_left(end)} zimebaki (inaisha {end[:10]})"
    if active:
        return f"🟢 Umelipia hadi {end[:10]} (siku {days_left(end)} zimebaki)"
    return f"🔒 Imefungwa. Muda uliisha {end[:10]}. Lipia: /lipia"


def lock_message(u):
    end = access_end(u)
    what = "ofa ya bure" if not u["paid_until"] else "malipo yako"
    return (
        f"🔒 Account yako imefungwa kwa sababu muda wa {what} umeisha"
        f"{' (' + end[:10] + ')' if end else ''}.\n\n"
        f"💳 Lipia {money(SUB_PRICE)} kwa mwezi: /lipia\n"
        f"Utafunguliwa mara tu malipo yako yatakapothibitishwa."
    )


def check_access(uid):
    with closing(db()) as conn:
        u = conn.execute("SELECT * FROM users WHERE user_id=?", (uid,)).fetchone()
    if is_admin(uid) or not u or not u["password_hash"]:
        return True, ""      # asiyesajiliwa anaelekezwa kujisajili na amri yenyewe
    active, _, _ = sub_state(u)
    return (True, "") if active else (False, lock_message(u))


def require_active(fn):
    """Amri zilizofungwa kwa watumiaji ambao ofa/malipo yao yameisha."""
    @functools.wraps(fn)
    async def wrapper(update, context):
        ok, msg = check_access(update.effective_user.id)
        if not ok:
            await update.message.reply_text(msg)
            return ConversationHandler.END
        return await fn(update, context)
    return wrapper


# ====== ORODHA YA AMRI (inaonekana pia kwenye menyu ya "/" ya Telegram) ======
USER_COMMANDS = [
    ("soko", "tazama bidhaa za wauzaji (video/picha)"),
    ("chapisha", "chapisha video/picha ya bidhaa yako"),
    ("posti_zangu", "matangazo yako na takwimu"),
    ("maarufu", "wauzaji maarufu zaidi"),
    ("jisajili", "fungua account (simu + password)"),
    ("badili_password", "badilisha password yako"),
    ("wasiliana", "tuma ujumbe kwa admin (msaada)"),
    ("pointi", "pointi za kutazama video na zawadi"),
    ("risiti", "risiti ya mauzo ya mwisho: [id]"),
    ("jina_la_duka", "weka jina la duka kwenye risiti"),
    ("mteja", "hifadhi mteja: <jina> <simu> [maelezo]"),
    ("wateja", "orodha ya wateja wako"),
    ("ofa", "tuma ofa kwa wateja kupitia WhatsApp"),
    ("ongeza_msaidizi", "ongeza msaidizi wa mauzo: <simu au id>"),
    ("wasaidizi", "wasaidizi wako"),
    ("maagizo", "maagizo ya Soko (uliyopokea/uliyotuma)"),
    ("tafuta", "tafuta bidhaa Sokoni: <neno>"),
    ("masharti", "masharti na faragha"),
    ("akaunti", "taarifa za account yako"),
    ("lipia", f"lipia mwezi ({SUB_PRICE:,} TZS)"),
    ("hali", "hali ya account na siku zilizobaki"),
    ("salio", "salio la bonasi (Balance)"),
    ("withdraw", "toa pesa (Withdraw)"),
    ("historia", "historia ya mauzo na pesa (History)"),
    ("weka_bidhaa", "weka bidhaa yako: <jina> <bei ya kununua> <bei ya kuuza> <stoo>"),
    ("bidhaa_zangu", "bidhaa zako, stoo na faida kwa kila moja"),
    ("jaza_stoo", "ongeza stoo ya bidhaa yako: <id> <idadi>"),
    ("badili_bei", "badili bei: <id> <bei ya kununua> <bei ya kuuza>"),
    ("faida", "faida ya mauzo yako"),
    ("bidhaa", "bidhaa za duka"),
    ("uza", "uza kwa vitufe (au /uza <id> <idadi>)"),
    ("tengua", "tengua mauzo ya mwisho"),
    ("leo", "muhtasari wa leo"),
    ("deni", "andika deni: <jina> <kiasi> [maelezo]"),
    ("madeni", "orodha ya wanaokudai"),
    ("lipa_deni", "deni limelipwa: <id> [kiasi]"),
    ("matumizi", "andika matumizi: <kiasi> <maelezo>"),
    ("futa_bidhaa", "futa bidhaa yako: <id>"),
    ("hariri_jina", "badili jina la bidhaa: <id> <jina>"),
    ("picha", "weka/badilisha picha ya bidhaa: <id>"),
    ("tazama", "tazama bidhaa na picha yake: <id>"),
    ("katalogi", "tuma katalogi ya bidhaa zenye picha"),
    ("ripoti_excel", "pakua ripoti ya Excel (wiki|mwezi|yote)"),
    ("ripoti_usiku", "washa/zima ripoti ya kila usiku"),
    ("msaada", "mwongozo wa kutumia bot"),
    ("mauzo", "ripoti ya mauzo yako"),
    ("rufaa", "link yako ya rufaa"),
    ("menu", "rudisha vitufe"),
]
ADMIN_COMMANDS = [
    ("ongeza_bidhaa", "ongeza bidhaa: <jina> <bei> <stoo>"),
    ("ongeza_stoo", "ongeza stoo: <id> <idadi>"),
    ("maombi", "maombi ya kutoa pesa"),
    ("malipo", "malipo ya usajili yanayosubiri"),
    ("ongeza_siku", "ongeza siku: <id> <siku>"),
    ("funga", "funga account: <id>"),
    ("ripoti", "ripoti ya biashara nzima"),
    ("watumiaji", "orodha ya watumiaji wote"),
    ("bidhaa_za", "bidhaa za mtumiaji: <id yake>"),
    ("tangaza", "tuma ujumbe kwa watumiaji wote"),
    ("soko_ripoti", "matangazo yaliyoripotiwa"),
    ("takwimu", "takwimu za ukuaji wa bot"),
    ("tiketi", "ujumbe wa msaada usiojibiwa"),
    ("jibu", "jibu tiketi: <id> <jibu>"),
    ("futa_akaunti", "futa taarifa binafsi za mtumiaji: <id>"),
    ("soko_ondoa", "ondoa tangazo: <id>"),
    ("soko_rudisha", "rudisha tangazo: <id>"),
    ("backup", "tuma nakala ya database sasa"),
    ("ping", "pima kasi ya bot"),
    ("mtumiaji", "taarifa kamili: <id au simu>"),
    ("reset_password", "badilisha password: <id> <mpya>"),
]


async def setup_commands(app: Application):
    """Weka kwenye bot.py: Application.builder()...post_init(mauzo_track.setup_commands)"""
    await app.bot.set_my_commands([BotCommand(c, d) for c, d in USER_COMMANDS])
    for a in ADMIN_IDS:
        try:
            await app.bot.set_my_commands(
                [BotCommand(c, d) for c, d in USER_COMMANDS + ADMIN_COMMANDS],
                scope=BotCommandScopeChat(a),
            )
        except Exception:
            pass


def ensure_user(user, referrer_id=None):
    with closing(db()) as conn, conn:
        row = conn.execute("SELECT * FROM users WHERE user_id=?", (user.id,)).fetchone()
        if row is None:
            if referrer_id == user.id:
                referrer_id = None
            conn.execute(
                "INSERT INTO users(user_id,name,username,referrer_id,joined) VALUES(?,?,?,?,?)",
                (user.id, user.full_name, user.username, referrer_id, now()),
            )
            return True
        return False


# ====== AMRI ZA WATUMIAJI ======
async def start_mauzo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Unaweza kuiita kutoka /start yako. Inasoma referral: /start ref_12345"""
    ref, post_id = None, None
    if context.args:
        arg = context.args[0]
        pm = re.fullmatch(r"p(\d+)(?:r(\d+))?", arg)      # link ya tangazo: /start p12r8604025635
        if arg.startswith("ref_"):
            try:
                ref = int(arg[4:])
            except ValueError:
                pass
        elif pm:
            post_id = int(pm.group(1))
            ref = int(pm.group(2)) if pm.group(2) else None
    uid = update.effective_user.id
    new = ensure_user(update.effective_user, ref)
    msg = "Karibu! 👋\n"
    if new and ref:
        msg += "Umejiunga kupitia link ya rufaa.\n"
    if not is_registered(uid):
        msg += "\n👉 Anza kwa kujisajili: /jisajili\n"
    msg += "\n📋 AMRI ZA MTUMIAJI\n" + "\n".join(f"/{c} - {d}" for c, d in USER_COMMANDS)
    if is_admin(uid):
        msg += "\n\n🔐 AMRI ZA ADMIN\n" + "\n".join(f"/{c} - {d}" for c, d in ADMIN_COMMANDS)
    msg += "\n\nAu tumia vitufe vilivyo chini ya skrini."
    if is_registered(uid):
        hint = onboarding_hint(uid)
        if hint:
            msg += "\n\n" + hint
    # Hakuna Markdown hapa, ili alama _ kwenye amri zisiharibu majina yake
    await update.message.reply_text(msg, reply_markup=menu_for(uid))
    if post_id:
        await _send_post(update.message, post_id, uid)


@require_active
async def bidhaa(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    with closing(db()) as conn:
        rows = conn.execute("SELECT * FROM products WHERE owner_id IS NULL AND active=1 ORDER BY id").fetchall()
    if not rows:
        await update.message.reply_text("Hakuna bidhaa za duka bado. Weka zako kwa /weka_bidhaa")
        return
    lines = ["📦 BIDHAA ZA DUKA "]
    for r in rows:
        warn = " ⚠️ inaisha" if r["stock"] <= 5 else ""
        lines.append(f"{r['id']}. {r['name']} - {money(r['price'])} | stoo: {r['stock']}{warn}")
    lines.append("\nKuuza: /uza <id> <idadi>")
    await update.message.reply_text("\n".join(lines))


# ====== BIDHAA ZA MTUMIAJI MWENYEWE + FAIDA ======
def _num(x):
    return float(x.replace(",", ""))


@require_active
async def weka_bidhaa(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    photo_id = context.user_data.pop("_photo_for_new", None)   # picha iliyotumwa pamoja na amri
    ensure_user(user)
    if not is_registered(user.id):
        await update.message.reply_text(NOT_REG_MSG)
        return
    usage = (
        "Tumia: /weka_bidhaa <jina> <bei ya kununua> <bei ya kuuza> <stoo>\n"
        "Mfano: /weka_bidhaa Sukari 2500 3000 50\n"
        "(Sukari ulinunua 2,500 kila moja, unauza 3,000, una pcs 50)"
    )
    try:
        stock = int(context.args[-1])
        sell = _num(context.args[-2])
        cost = _num(context.args[-3])
        name = " ".join(context.args[:-3]).strip()
        assert name and stock >= 0 and sell > 0 and cost >= 0
    except (IndexError, ValueError, AssertionError):
        await update.message.reply_text(usage)
        return
    try:
        with closing(db()) as conn, conn:
            pid = conn.execute(
                "INSERT INTO products(name,price,stock,owner_id,cost,photo_id) VALUES(?,?,?,?,?,?)",
                (name, sell, stock, user.id, cost, photo_id),
            ).lastrowid
    except sqlite3.IntegrityError:
        await update.message.reply_text("❌ Tayari una bidhaa yenye jina hilo. Tumia /jaza_stoo kuongeza stoo.")
        return
    per = sell - cost
    warn = "\n⚠️ Bei ya kuuza ni ndogo kuliko ya kununua, utapata hasara." if per < 0 else ""
    if photo_id:
        photo_line = "📷 Picha imehifadhiwa."
    else:
        context.user_data["await_photo"] = (pid, time.time())      # picha inayofuata ni ya bidhaa hii
        photo_line = "📷 Tuma picha ya bidhaa hii sasa (dakika 10), au endelea bila picha."
    await update.message.reply_text(
        f"✅ Bidhaa imewekwa (ID {pid})\n{name}\n"
        f"Kununua: {money(cost)} | Kuuza: {money(sell)}\n"
        f"Faida kwa kila moja: {money(per)} | Stoo: {stock}{warn}\n"
        f"{photo_line}\n\n"
        f"Kuuza: bonyeza 🛒 Uza"
    )


@require_active
async def bidhaa_zangu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    with closing(db()) as conn:
        rows = conn.execute("SELECT * FROM products WHERE owner_id=? AND active=1 ORDER BY id", (uid,)).fetchall()
    if not rows:
        await update.message.reply_text(
            "Bado huna bidhaa.\nWeka kwa: /weka_bidhaa <jina> <bei ya kununua> <bei ya kuuza> <stoo>"
        )
        return
    out = ["💼 BIDHAA ZANGU"]
    for r in rows:
        warn = " ⚠️ inaisha" if r["stock"] <= 5 else ""
        out.append(
            f"{r['id']}. {r['name']}{' 📷' if r['photo_id'] else ''}\n"
            f"   Kununua {money(r['cost'])} | Kuuza {money(r['price'])} | Faida/pc {money(r['price'] - r['cost'])}\n"
            f"   Stoo: {r['stock']}{warn}"
        )
    out.append("\nKuuza: /uza <id> <idadi>\nKuongeza stoo: /jaza_stoo <id> <idadi>")
    text = "\n".join(out)
    for i in range(0, len(text), 3800):
        await update.message.reply_text(text[i:i + 3800])


@require_active
async def jaza_stoo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    try:
        pid, qty = int(context.args[0]), int(context.args[1])
        assert qty > 0
    except (IndexError, ValueError, AssertionError):
        await update.message.reply_text("Tumia: /jaza_stoo <id> <idadi>\nMfano: /jaza_stoo 3 20")
        return
    with closing(db()) as conn, conn:
        cur = conn.execute("UPDATE products SET stock=stock+? WHERE id=? AND owner_id=?", (qty, pid, uid))
        row = conn.execute("SELECT name, stock FROM products WHERE id=?", (pid,)).fetchone() if cur.rowcount else None
    if not row:
        await update.message.reply_text("❌ Huna bidhaa yenye ID hiyo. Angalia /bidhaa_zangu")
        return
    await update.message.reply_text(f"✅ {row['name']}: stoo sasa ni {row['stock']}")


@require_active
async def badili_bei(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    try:
        pid = int(context.args[0])
        cost, sell = _num(context.args[1]), _num(context.args[2])
        assert cost >= 0 and sell > 0
    except (IndexError, ValueError, AssertionError):
        await update.message.reply_text("Tumia: /badili_bei <id> <bei ya kununua> <bei ya kuuza>\nMfano: /badili_bei 3 2600 3200")
        return
    with closing(db()) as conn, conn:
        cur = conn.execute("UPDATE products SET cost=?, price=? WHERE id=? AND owner_id=?", (cost, sell, pid, uid))
    if not cur.rowcount:
        await update.message.reply_text("❌ Huna bidhaa yenye ID hiyo. Angalia /bidhaa_zangu")
        return
    await update.message.reply_text(
        f"✅ Bei imebadilishwa.\nKununua {money(cost)} | Kuuza {money(sell)} | Faida/pc {money(sell - cost)}\n"
        f"(Mauzo ya zamani yanabaki na faida yake ya wakati huo.)"
    )


@require_active
async def faida(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    today = datetime.now().replace(hour=0, minute=0, second=0).strftime(FMT)
    week = (datetime.now() - timedelta(days=7)).strftime(FMT)
    month = (datetime.now() - timedelta(days=30)).strftime(FMT)

    def agg(conn, since):
        sales = conn.execute(
            "SELECT COUNT(*) n, COALESCE(SUM(s.total),0) t, COALESCE(SUM(s.profit),0) f "
            "FROM sales s JOIN products p ON p.id=s.product_id "
            "WHERE s.seller_id=? AND p.owner_id=? AND s.ts>=?", (uid, uid, since)
        ).fetchone()
        exp = conn.execute(
            "SELECT COALESCE(SUM(amount),0) e FROM expenses WHERE user_id=? AND ts>=?", (uid, since)
        ).fetchone()["e"]
        return sales, exp

    with closing(db()) as conn:
        d, w, m, a = (agg(conn, x) for x in (today, week, month, "0000"))
        st = conn.execute(
            "SELECT COALESCE(SUM(stock*cost),0) cap, COALESCE(SUM(stock*(price-cost)),0) exp, COUNT(*) n "
            "FROM products WHERE owner_id=? AND active=1", (uid,)
        ).fetchone()
        top = conn.execute(
            "SELECT p.name, SUM(s.profit) f, SUM(s.qty) q FROM sales s JOIN products p ON p.id=s.product_id "
            "WHERE s.seller_id=? AND p.owner_id=? GROUP BY p.id ORDER BY f DESC LIMIT 3", (uid, uid)
        ).fetchall()
    if not st["n"] and not a[0]["n"]:
        await update.message.reply_text("Bado huna bidhaa. Weka kwa: /weka_bidhaa <jina> <bei ya kununua> <bei ya kuuza> <stoo>")
        return

    def line(label, pair):
        sl, ex = pair
        return (f"{label}: mauzo {money(sl['t'])} | faida {money(sl['f'])} | matumizi {money(ex)} "
                f"| HALISI {money(sl['f'] - ex)}")

    out = [
        "💹 FAIDA YAKO (faida halisi = faida ya mauzo minus matumizi)",
        line("Leo", d), line("Wiki (siku 7)", w), line("Mwezi (siku 30)", m), line("Jumla yote", a),
        f"\n📦 Mtaji ulio kwenye stoo: {money(st['cap'])}",
        f"Faida inayotarajiwa ukiuza stoo yote: {money(st['exp'])}",
    ]
    if top:
        out.append("\n🏆 Bidhaa zenye faida zaidi:")
        out += [f"- {r['name']}: {money(r['f'])} ({r['q']} zimeuzwa)" for r in top]
    out.append("\nAndika matumizi: /matumizi <kiasi> <maelezo>")
    await update.message.reply_text("\n".join(out))


def do_sale(uid, pid, qty, credit_to=None, actor=None):
    """Inarekodi mauzo. Inarudisha (ok, ujumbe, info). credit_to = jina la mteja akinunua kwa mkopo."""
    with closing(db()) as conn, conn:
        p = conn.execute("SELECT * FROM products WHERE id=?", (pid,)).fetchone()
        if not p or p["active"] == 0 or (p["owner_id"] is not None and p["owner_id"] != uid):
            return False, "❌ Bidhaa haipo.", None
        if p["stock"] < qty:
            return False, f"❌ Stoo haitoshi. Zilizobaki: {p['stock']}", None

        total = p["price"] * qty
        personal = p["owner_id"] == uid
        ref_id, comm, ref_comm, profit = None, 0, 0, 0
        if personal:
            profit = (p["price"] - p["cost"]) * qty       # bidhaa yake: faida
        else:
            comm = total * COMMISSION_RATE                # bidhaa ya duka (commission imezimwa kwa sasa)
            u = conn.execute("SELECT referrer_id FROM users WHERE user_id=?", (uid,)).fetchone()
            ref_id = u["referrer_id"] if u else None
            ref_comm = total * REFERRAL_RATE if ref_id else 0

        conn.execute("UPDATE products SET stock=stock-? WHERE id=?", (qty, pid))
        if comm:
            conn.execute("UPDATE users SET balance=balance+? WHERE user_id=?", (comm, uid))
        if ref_comm:
            conn.execute("UPDATE users SET balance=balance+? WHERE user_id=?", (ref_comm, ref_id))
        sid = conn.execute(
            "INSERT INTO sales(seller_id,product_id,qty,total,commission,ref_commission,ts,profit,sold_by) "
            "VALUES(?,?,?,?,?,?,?,?,?)",
            (uid, pid, qty, total, comm, ref_comm, now(), profit, actor),
        ).lastrowid
        if credit_to:
            conn.execute(
                "INSERT INTO debts(user_id,customer,amount,paid,note,ts,sale_id) VALUES(?,?,?,?,?,?,?)",
                (uid, credit_to.strip()[:60], total, 0, f"{p['name']} x{qty}", now(), sid),
            )
        left = p["stock"] - qty

    text = f"✅ Mauzo yamerekodiwa\nBidhaa: {p['name']} x{qty}\nJumla: {money(total)}\n"
    if personal and not actor:                       # msaidizi haoni faida
        text += f"💹 Faida yako: {money(profit)}\n"
    elif comm:
        text += f"Commission yako ({COMMISSION_RATE*100:.0f}%): {money(comm)}\n"
    if credit_to:
        text += f"📒 Deni: {credit_to.strip()[:60]} anadaiwa {money(total)}\n"
    text += f"Stoo iliyobaki: {left}"
    if personal and left <= 5:
        text += "\n⚠️ Stoo inaisha, jaza kwa /jaza_stoo"
    info = {"sale_id": sid, "ref_id": ref_id, "ref_comm": ref_comm, "left": left,
            "personal": personal, "name": p["name"], "owner": uid, "actor": actor, "qty": qty, "total": total}
    return True, text, info


async def notify_after_sale(context, info):
    if not info:
        return
    if info.get("actor"):                            # mmiliki anaarifiwa mauzo ya msaidizi
        try:
            await context.bot.send_message(
                info["owner"], f"👷 Msaidizi ameuza {info['name']} x{info['qty']} ({money(info['total'])}). Stoo: {info['left']}"
            )
        except Exception:
            pass
    if info["ref_comm"]:
        try:
            await context.bot.send_message(info["ref_id"], f"🎉 Umepata commission ya rufaa: {money(info['ref_comm'])}")
        except Exception:
            pass
    if not info["personal"] and info["left"] <= 5:
        for a in ADMIN_IDS:
            try:
                await context.bot.send_message(a, f"⚠️ Stoo ya {info['name']} inaisha: {info['left']} zimebaki.")
            except Exception:
                pass


@require_active
async def uza(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    ensure_user(user)
    eff = eff_uid(user.id)
    if eff == user.id and not is_registered(user.id):
        await update.message.reply_text(NOT_REG_MSG)
        return
    if eff != user.id:
        ok_o, msg_o = check_access(eff)
        if not ok_o:
            await update.message.reply_text("🔒 Account ya bosi wako imefungwa. Mwambie alipie: /lipia")
            return
    if not context.args:                      # /uza peke yake = vitufe
        return await uza_menu(update, context)
    try:
        pid, qty = int(context.args[0]), int(context.args[1])
        assert qty > 0
    except (IndexError, ValueError, AssertionError):
        await update.message.reply_text(
            "Tumia vitufe: bonyeza 🛒 Uza\nAu andika: /uza <id> <idadi>\nMfano: /uza 1 3\n"
            "Kwa mkopo: /uza 1 3 deni Juma"
        )
        return
    credit = None
    if len(context.args) >= 4 and context.args[2].lower() == "deni":
        credit = " ".join(context.args[3:])
    ok, text, info = do_sale(eff, pid, qty, credit, actor=user.id if eff != user.id else None)
    if not ok:
        await update.message.reply_text(text)
        return
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("↩️ Tengua", callback_data=f"tg_{info['sale_id']}"),
        InlineKeyboardButton("📄 Risiti", callback_data=f"rc_{info['sale_id']}"),
    ]])
    await update.message.reply_text(text, reply_markup=kb)
    await notify_after_sale(context, info)


def _summary(conn, since, seller_id=None):
    q = "SELECT COUNT(*) n, COALESCE(SUM(total),0) t, COALESCE(SUM(commission),0) c, COALESCE(SUM(profit),0) f FROM sales WHERE ts>=?"
    args = [since]
    if seller_id:
        q += " AND seller_id=?"
        args.append(seller_id)
    return conn.execute(q, args).fetchone()


@require_active
async def mauzo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    today = datetime.now().replace(hour=0, minute=0, second=0).strftime("%Y-%m-%d %H:%M:%S")
    week = (datetime.now() - timedelta(days=7)).strftime("%Y-%m-%d %H:%M:%S")
    month = (datetime.now() - timedelta(days=30)).strftime("%Y-%m-%d %H:%M:%S")
    with closing(db()) as conn:
        d, w, m = (_summary(conn, s, uid) for s in (today, week, month))
        top = conn.execute(
            "SELECT p.name, SUM(s.qty) q FROM sales s JOIN products p ON p.id=s.product_id "
            "WHERE s.seller_id=? GROUP BY p.id ORDER BY q DESC LIMIT 3", (uid,)
        ).fetchall()
    text = (
        "📊 *Mauzo yako*\n"
        f"Leo: {d['n']} mauzo | {money(d['t'])}\n"
        f"Wiki (siku 7): {w['n']} mauzo | {money(w['t'])}\n"
        f"Mwezi (siku 30): {m['n']} mauzo | {money(m['t'])}\n"
        f"Faida ya bidhaa zako (mwezi): {money(m['f'])}\n"
    )
    if top:
        text += "\n🏆 *Zinazouzwa zaidi:*\n" + "\n".join(f"- {r['name']} ({r['q']})" for r in top)
    await update.message.reply_text(text, parse_mode="Markdown")


async def salio(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    with closing(db()) as conn:
        u = conn.execute("SELECT balance FROM users WHERE user_id=?", (update.effective_user.id,)).fetchone()
        refs = conn.execute(
            "SELECT COUNT(*) n FROM users WHERE referrer_id=?", (update.effective_user.id,)
        ).fetchone()
    await update.message.reply_text(
        f"💰 Salio lako: {money(u['balance'])}\n👥 Watu uliowaleta: {refs['n']}"
    )


async def rufaa(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    link = f"https://t.me/{BOT_USERNAME}?start=ref_{update.effective_user.id}"
    await update.message.reply_text(
        f"🔗 Link yako ya rufaa:\n{link}\n\n"
        f"Kila mtu atakayejiunga kupitia link hii na kulipia {money(SUB_PRICE)}, utapata bonasi ya {money(REFERRAL_BONUS)}."
    )


# ====== KUTOA PESA ======
@require_active
async def toa(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    ensure_user(user)
    if not is_registered(user.id):
        await update.message.reply_text(NOT_REG_MSG)
        return
    try:
        amount = float(context.args[0])
        phone = context.args[1]
        password = context.args[2]
    except (IndexError, ValueError):
        await update.message.reply_text(
            "Tumia: /toa <kiasi> <namba ya simu> <password>\nMfano: /toa 5000 0712345678 pass123"
        )
        return
    try:  # futa ujumbe wenye password usionekane kwenye chat
        await update.message.delete()
    except Exception:
        pass
    ok, err = await asyncio.to_thread(check_password, user.id, password)   # haizuii bot nyingine
    if not ok:
        await context.bot.send_message(user.id, err)
        return
    if amount < MIN_WITHDRAW:
        await context.bot.send_message(user.id, f"❌ Kiwango cha chini ni {money(MIN_WITHDRAW)}")
        return

    with closing(db()) as conn, conn:
        bal = conn.execute("SELECT balance FROM users WHERE user_id=?", (user.id,)).fetchone()["balance"]
        if amount > bal:
            await context.bot.send_message(user.id, f"❌ Salio halitoshi. Salio lako: {money(bal)}")
            return
        conn.execute("UPDATE users SET balance=balance-? WHERE user_id=?", (amount, user.id))
        cur = conn.execute(
            "INSERT INTO withdrawals(user_id,amount,phone,ts) VALUES(?,?,?,?)",
            (user.id, amount, phone, now()),
        )
        wid = cur.lastrowid

    await context.bot.send_message(user.id, f"⏳ Ombi #{wid} la {money(amount)} limetumwa. Subiri idhini ya admin.")
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Idhinisha", callback_data=f"wd_ok_{wid}"),
        InlineKeyboardButton("❌ Kataa", callback_data=f"wd_no_{wid}"),
    ]])
    for a in ADMIN_IDS:
        try:
            await context.bot.send_message(
                a,
                f"💸 Ombi #{wid}\nMtumiaji: {user.full_name} ({user.id})\n"
                f"Kiasi: {money(amount)}\nSimu: {phone}",
                reply_markup=kb,
            )
        except Exception:
            pass


async def wd_buttons(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    if not is_admin(q.from_user.id):
        await q.answer("Huna ruhusa.", show_alert=True)
        return
    _, action, wid = q.data.split("_")
    wid = int(wid)
    with closing(db()) as conn, conn:
        w = conn.execute("SELECT * FROM withdrawals WHERE id=?", (wid,)).fetchone()
        if not w or w["status"] != "pending":
            await q.edit_message_text(f"Ombi #{wid} limeshashughulikiwa.")
            return
        if action == "ok":
            conn.execute("UPDATE withdrawals SET status='approved' WHERE id=?", (wid,))
            note = f"✅ Ombi #{wid} la {money(w['amount'])} limeidhinishwa. Utatumiwa pesa kwenda {w['phone']}."
            admin_note = f"✅ Ombi #{wid} limeidhinishwa. Tuma {money(w['amount'])} kwa {w['phone']}."
        else:
            conn.execute("UPDATE withdrawals SET status='rejected' WHERE id=?", (wid,))
            conn.execute("UPDATE users SET balance=balance+? WHERE user_id=?", (w["amount"], w["user_id"]))
            note = f"❌ Ombi #{wid} limekataliwa. Pesa imerudishwa kwenye salio lako."
            admin_note = f"❌ Ombi #{wid} limekataliwa."
    await q.edit_message_text(admin_note)
    try:
        await context.bot.send_message(w["user_id"], note)
    except Exception:
        pass


# ====== AMRI ZA ADMIN ======
async def ongeza_bidhaa(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    try:
        stock = int(context.args[-1])
        price = float(context.args[-2])
        name = " ".join(context.args[:-2])
        assert name
    except (IndexError, ValueError, AssertionError):
        await update.message.reply_text("Tumia: /ongeza_bidhaa <jina> <bei> <stoo>\nMfano: /ongeza_bidhaa Sukari 3000 50")
        return
    try:
        with closing(db()) as conn, conn:
            conn.execute("INSERT INTO products(name,price,stock) VALUES(?,?,?)", (name, price, stock))
        await update.message.reply_text(f"✅ {name} imeongezwa.")
    except sqlite3.IntegrityError:
        await update.message.reply_text("❌ Bidhaa hiyo tayari ipo.")


async def ongeza_stoo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    try:
        pid, qty = int(context.args[0]), int(context.args[1])
    except (IndexError, ValueError):
        await update.message.reply_text("Tumia: /ongeza_stoo <id> <idadi>")
        return
    with closing(db()) as conn, conn:
        cur = conn.execute("UPDATE products SET stock=stock+? WHERE id=?", (qty, pid))
    await update.message.reply_text("✅ Stoo imeongezwa." if cur.rowcount else "❌ Bidhaa haipo.")


async def maombi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    with closing(db()) as conn:
        rows = conn.execute("SELECT * FROM withdrawals WHERE status='pending'").fetchall()
    if not rows:
        await update.message.reply_text("Hakuna maombi yanayosubiri.")
        return
    for w in rows:
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("✅ Idhinisha", callback_data=f"wd_ok_{w['id']}"),
            InlineKeyboardButton("❌ Kataa", callback_data=f"wd_no_{w['id']}"),
        ]])
        await update.message.reply_text(
            f"Ombi #{w['id']} | User {w['user_id']}\n{money(w['amount'])} -> {w['phone']}",
            reply_markup=kb,
        )


async def ripoti(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    today = datetime.now().replace(hour=0, minute=0, second=0).strftime("%Y-%m-%d %H:%M:%S")
    month = (datetime.now() - timedelta(days=30)).strftime("%Y-%m-%d %H:%M:%S")
    with closing(db()) as conn:
        d, m = _summary(conn, today), _summary(conn, month)
        users = conn.execute("SELECT COUNT(*) n FROM users").fetchone()["n"]
        pending = conn.execute(
            "SELECT COUNT(*) n, COALESCE(SUM(amount),0) a FROM withdrawals WHERE status='pending'"
        ).fetchone()
        top = conn.execute(
            "SELECT u.name, SUM(s.total) t FROM sales s JOIN users u ON u.user_id=s.seller_id "
            "GROUP BY s.seller_id ORDER BY t DESC LIMIT 5"
        ).fetchall()
    with closing(db()) as conn:
        urows = conn.execute("SELECT * FROM users WHERE password_hash IS NOT NULL").fetchall()
        rev = conn.execute(
            "SELECT COALESCE(SUM(amount),0) a, COUNT(*) n FROM payments WHERE status='approved' AND decided_ts>=?",
            (month,),
        ).fetchone()
        pend_pay = conn.execute("SELECT COUNT(*) n FROM payments WHERE status='pending'").fetchone()["n"]
    cnt = {"paid": 0, "trial": 0, "locked": 0}
    for r in urows:
        act, _, kd = sub_state(r)
        if kd != "admin":
            cnt[kd if act else "locked"] += 1
    sub_lines = (
        f"🟢 Waliolipa: {cnt['paid']} | 🎁 Ofa: {cnt['trial']} | 🔒 Waliofungwa: {cnt['locked']}\n"
        f"💳 Mapato ya usajili (siku 30): {money(rev['a'])} ({rev['n']} malipo)\n"
        f"Malipo yanayosubiri: {pend_pay}\n"
    )
    text = (
        "📈 *Ripoti ya biashara*\n"
        f"Watumiaji: {users}\n"
        f"Leo: {d['n']} mauzo | {money(d['t'])}\n"
        f"Mwezi: {m['n']} mauzo | {money(m['t'])}\n"
        f"{sub_lines}"
        f"Maombi yanayosubiri: {pending['n']} ({money(pending['a'])})\n"
    )
    if top:
        text += "\n🏆 *Wauzaji bora:*\n" + "\n".join(f"- {r['name']}: {money(r['t'])}" for r in top)
    await update.message.reply_text(text, parse_mode="Markdown")


# ====== KUJISAJILI (simu + password) ======
ASK_PHONE, ASK_PASS, ASK_PASS2 = range(3)
ASK_TERMS = 5


async def jisajili(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_chat.type != "private":
        await update.message.reply_text("Jisajili kwenye chat binafsi na bot.")
        return ConversationHandler.END
    ensure_user(update.effective_user)
    if is_registered(update.effective_user.id):
        await update.message.reply_text("✅ Tayari umejisajili. Angalia /akaunti")
        return ConversationHandler.END
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Nakubali", callback_data="tm_yes"),
        InlineKeyboardButton("❌ Sikubali", callback_data="tm_no"),
    ]])
    await update.message.reply_text(TERMS_TEXT + "\nUnakubali masharti haya?", reply_markup=kb)
    return ASK_TERMS


async def get_phone(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.message.text in MENU_TEXTS:
        return await ghairi(update, context)
    phone = normalize_phone(update.message.text)
    if not phone:
        await update.message.reply_text("❌ Namba si sahihi. Mfano: 0712345678")
        return ASK_PHONE
    with closing(db()) as conn:
        used = conn.execute(
            "SELECT 1 FROM users WHERE phone=? AND user_id!=?", (phone, update.effective_user.id)
        ).fetchone()
    if used:
        await update.message.reply_text("❌ Namba hii tayari imesajiliwa. Tumia nyingine.")
        return ASK_PHONE
    context.user_data["phone"] = phone
    await update.message.reply_text("🔑 Weka password (angalau herufi 6). Ujumbe wako utafutwa kwa usalama.")
    return ASK_PASS


async def get_pass(update: Update, context: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text
    try:
        await update.message.delete()
    except Exception:
        pass
    if len(pw) < 6:
        await context.bot.send_message(update.effective_chat.id, "❌ Password fupi mno. Angalau herufi 6.")
        return ASK_PASS
    context.user_data["pw"] = pw
    await context.bot.send_message(update.effective_chat.id, "🔁 Rudia password ili kuthibitisha.")
    return ASK_PASS2


async def get_pass2(update: Update, context: ContextTypes.DEFAULT_TYPE):
    pw2 = update.message.text
    try:
        await update.message.delete()
    except Exception:
        pass
    chat = update.effective_chat.id
    if pw2 != context.user_data.get("pw"):
        await context.bot.send_message(chat, "❌ Hazifanani. Weka password tena.")
        return ASK_PASS
    h, salt = await asyncio.to_thread(hash_password, pw2)
    user = update.effective_user
    try:
        with closing(db()) as conn, conn:
            conn.execute(
                "UPDATE users SET phone=?, password_hash=?, salt=?, registered_at=?, "
                "name=?, username=?, failed_logins=0, trial_until=COALESCE(trial_until, ?) WHERE user_id=?",
                (context.user_data["phone"], h, salt, now(), user.full_name, user.username,
                 add_days(now(), TRIAL_DAYS), user.id),
            )
    except sqlite3.IntegrityError:
        await context.bot.send_message(chat, "❌ Namba hii imeshatumika. Anza tena: /jisajili")
        context.user_data.clear()
        return ConversationHandler.END
    phone = context.user_data["phone"]
    context.user_data.clear()
    await context.bot.send_message(
        chat, f"🎉 Umefanikiwa kujisajili!\nSimu: {phone}\n🎁 Una siku {TRIAL_DAYS} za ofa BURE. Baada ya hapo ni {money(SUB_PRICE)} kwa mwezi (/lipia).\nTumia vitufe vilivyo chini.\n\n{onboarding_hint(user.id)}",
        reply_markup=menu_for(user.id),
    )
    for a in ADMIN_IDS:
        try:
            await context.bot.send_message(
                a, f"🆕 Mtumiaji mpya: {user.full_name} (@{user.username})\nID: {user.id}\nSimu: {phone}"
            )
        except Exception:
            pass
    return ConversationHandler.END


async def ghairi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.clear()
    await update.message.reply_text("Umeghairi.")
    return ConversationHandler.END


async def akaunti(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    with closing(db()) as conn:
        u = conn.execute("SELECT * FROM users WHERE user_id=?", (update.effective_user.id,)).fetchone()
    if not u["password_hash"]:
        await update.message.reply_text(NOT_REG_MSG)
        return
    await update.message.reply_text(
        f"👤 *Account yako*\nJina: {u['name']}\nSimu: {u['phone']}\n"
        f"Salio: {money(u['balance'])}\nUmejisajili: {u['registered_at']}\n"
        f"Hali: {status_text(u)}",
        parse_mode="Markdown",
    )


# ====== HISTORIA ======
STATUS_ICON = {"pending": "⏳ inasubiri", "approved": "✅ imelipwa", "rejected": "❌ imekataliwa"}


@require_active
async def historia(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    with closing(db()) as conn:
        sales = conn.execute(
            "SELECT s.ts, p.name, s.qty, s.total, s.commission, s.profit FROM sales s "
            "JOIN products p ON p.id=s.product_id WHERE s.seller_id=? ORDER BY s.id DESC LIMIT 10",
            (uid,),
        ).fetchall()
        refs = conn.execute(
            "SELECT s.ts, u.name, s.ref_commission FROM sales s "
            "JOIN users u ON u.user_id=s.seller_id WHERE u.referrer_id=? AND s.ref_commission>0 "
            "ORDER BY s.id DESC LIMIT 5", (uid,),
        ).fetchall()
        bons = conn.execute(
            "SELECT b.ts, b.amount, u.name FROM bonuses b LEFT JOIN users u ON u.user_id=b.from_user "
            "WHERE b.user_id=? ORDER BY b.id DESC LIMIT 10", (uid,),
        ).fetchall()
        wds = conn.execute(
            "SELECT id, ts, amount, status FROM withdrawals WHERE user_id=? ORDER BY id DESC LIMIT 10",
            (uid,),
        ).fetchall()
    if not (sales or refs or wds or bons):
        await update.message.reply_text("📜 Bado hakuna historia.")
        return
    out = ["📜 HISTORIA YAKO"]
    if sales:
        out.append("\n🛒 Mauzo ya hivi karibuni:")
        for r in sales:
            gain = f" | faida {money(r['profit'])}" if r["profit"] else (
                f" | commission {money(r['commission'])}" if r["commission"] else "")
            out.append(f"{r['ts'][:16]} | {r['name']} x{r['qty']} | {money(r['total'])}{gain}")
    if refs:
        out.append("\n👥 Commission za rufaa:")
        for r in refs:
            out.append(f"{r['ts'][:16]} | {r['name']} | +{money(r['ref_commission'])}")
    if bons:
        out.append("\n🎁 Bonasi za rufaa:")
        for r in bons:
            out.append(f"{r['ts'][:16]} | {r['name'] or '-'} amelipia | +{money(r['amount'])}")
    if wds:
        out.append("\n💸 Maombi ya kutoa pesa:")
        for r in wds:
            out.append(f"#{r['id']} | {r['ts'][:16]} | {money(r['amount'])} | {STATUS_ICON.get(r['status'], r['status'])}")
    await update.message.reply_text("\n".join(out))


async def menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    await update.message.reply_text("📋 Chagua kitufe hapo chini.", reply_markup=menu_for(update.effective_user.id))


# ====== KITUFE CHA WITHDRAW COMMISSION ======
W_AMOUNT, W_PASS = range(10, 12)


@require_active
async def wd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    ensure_user(user)
    if not is_registered(user.id):
        await update.message.reply_text(NOT_REG_MSG)
        return ConversationHandler.END
    with closing(db()) as conn:
        u = conn.execute("SELECT balance, phone FROM users WHERE user_id=?", (user.id,)).fetchone()
    if u["balance"] < MIN_WITHDRAW:
        await update.message.reply_text(
            f"❌ Salio lako ni {money(u['balance'])}. Kiwango cha chini cha kutoa ni {money(MIN_WITHDRAW)}."
        )
        return ConversationHandler.END
    context.user_data["wd_phone"] = u["phone"]
    await update.message.reply_text(
        f"💸 Salio lako: {money(u['balance'])}\n"
        f"Pesa itatumwa kwenda: {u['phone']}\n\n"
        f"Andika kiasi unachotaka kutoa (mfano 5000).\nKughairi: /ghairi"
    )
    return W_AMOUNT


async def wd_amount(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = update.message.text
    if text in MENU_TEXTS:
        return await ghairi(update, context)
    try:
        amount = float(text.replace(",", "").replace(" ", ""))
    except ValueError:
        await update.message.reply_text("❌ Andika namba tu, mfano 5000")
        return W_AMOUNT
    with closing(db()) as conn:
        bal = conn.execute("SELECT balance FROM users WHERE user_id=?", (update.effective_user.id,)).fetchone()["balance"]
    if amount < MIN_WITHDRAW:
        await update.message.reply_text(f"❌ Kiwango cha chini ni {money(MIN_WITHDRAW)}")
        return W_AMOUNT
    if amount > bal:
        await update.message.reply_text(f"❌ Salio halitoshi. Salio lako: {money(bal)}")
        return W_AMOUNT
    context.user_data["wd_amount"] = amount
    await update.message.reply_text("🔑 Weka password yako kuthibitisha. Ujumbe wako utafutwa kwa usalama.")
    return W_PASS


async def wd_pass(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    pw = update.message.text
    try:
        await update.message.delete()
    except Exception:
        pass
    ok, err = await asyncio.to_thread(check_password, user.id, pw)
    if not ok:
        await context.bot.send_message(user.id, err)
        return ConversationHandler.END if "imefungwa" in err else W_PASS
    amount, phone = context.user_data.get("wd_amount"), context.user_data.get("wd_phone")
    context.user_data.clear()
    with closing(db()) as conn, conn:
        bal = conn.execute("SELECT balance FROM users WHERE user_id=?", (user.id,)).fetchone()["balance"]
        if not amount or amount > bal:
            await context.bot.send_message(user.id, f"❌ Salio halitoshi. Salio lako: {money(bal)}")
            return ConversationHandler.END
        conn.execute("UPDATE users SET balance=balance-? WHERE user_id=?", (amount, user.id))
        wid = conn.execute(
            "INSERT INTO withdrawals(user_id,amount,phone,ts) VALUES(?,?,?,?)", (user.id, amount, phone, now())
        ).lastrowid
    await context.bot.send_message(
        user.id, f"⏳ Ombi #{wid} la {money(amount)} limetumwa. Subiri idhini ya admin.",
        reply_markup=menu_for(user.id),
    )
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Idhinisha", callback_data=f"wd_ok_{wid}"),
        InlineKeyboardButton("❌ Kataa", callback_data=f"wd_no_{wid}"),
    ]])
    for a in ADMIN_IDS:
        try:
            await context.bot.send_message(
                a, f"💸 Ombi #{wid}\nMtumiaji: {user.full_name} ({user.id})\nKiasi: {money(amount)}\nSimu: {phone}",
                reply_markup=kb,
            )
        except Exception:
            pass
    return ConversationHandler.END


# ====== ADMIN: KUONA WATUMIAJI ======
def _user_card(conn, u):
    refs = conn.execute("SELECT COUNT(*) n FROM users WHERE referrer_id=?", (u["user_id"],)).fetchone()["n"]
    s = conn.execute(
        "SELECT COUNT(*) n, COALESCE(SUM(total),0) t, COALESCE(SUM(commission),0) c "
        "FROM sales WHERE seller_id=?", (u["user_id"],)
    ).fetchone()
    w = conn.execute(
        "SELECT COALESCE(SUM(amount),0) a FROM withdrawals WHERE user_id=? AND status='approved'",
        (u["user_id"],),
    ).fetchone()["a"]
    wp = conn.execute(
        "SELECT COALESCE(SUM(amount),0) a FROM withdrawals WHERE user_id=? AND status='pending'",
        (u["user_id"],),
    ).fetchone()["a"]
    mine = conn.execute(
        "SELECT COUNT(*) n, COALESCE(SUM(stock*cost),0) cap FROM products WHERE owner_id=?", (u["user_id"],)
    ).fetchone()
    pr = conn.execute(
        "SELECT COALESCE(SUM(profit),0) f FROM sales WHERE seller_id=?", (u["user_id"],)
    ).fetchone()["f"]
    bon = conn.execute("SELECT COALESCE(SUM(amount),0) a FROM bonuses WHERE user_id=?", (u["user_id"],)).fetchone()["a"]
    uname = f"@{u['username']}" if u["username"] else "-"
    ref = u["referrer_id"] or "-"
    return (
        f"👤 {u['name']} ({uname})\n"
        f"ID: {u['user_id']}\n"
        f"Simu: {u['phone'] or 'hajasajili'}\n"
        f"Password: imehifadhiwa kwa usalama (hashed, haionekani)\n"
        f"Hali: {status_text(u)}\n"
        f"Alijiunga: {u['joined']}\n"
        f"Alikubali masharti: {u['terms_at'] or 'hapana (mtumiaji wa zamani)'}\n"
        f"Alisajiliwa: {u['registered_at'] or '-'}\n"
        f"Aliletwa na: {ref}\n"
        f"Watu aliowaleta: {refs}\n"
        f"Mauzo: {s['n']} | {money(s['t'])}\n"
        f"Bonasi za rufaa: {money(bon)}\n"
        f"Bidhaa zake: {mine['n']} | Mtaji kwenye stoo: {money(mine['cap'])} | Faida ya jumla: {money(pr)}\n"
        f"Salio: {money(u['balance'])}\n"
        f"Alizotoa: {money(w)} | Zinasubiri: {money(wp)}\n"
        f"Makosa ya password: {u['failed_logins']}/{MAX_FAILED_LOGINS}"
    )


async def watumiaji(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    with closing(db()) as conn:
        rows = conn.execute("SELECT * FROM users ORDER BY joined DESC").fetchall()
    if not rows:
        await update.message.reply_text("Hakuna watumiaji bado.")
        return
    lines = [f"👥 Watumiaji: {len(rows)}\n"]
    for r in rows:
        active, end, kind = sub_state(r)
        tag = ({"admin": "👑", "paid": "🟢 lipa", "trial": "🎁 ofa"}[kind] if active else ("🔒" if r["phone"] else "")) + (f" {end[:10]}" if end else "")
        lines.append(f"{r['user_id']} | {r['name']} | {r['phone'] or 'hajasajili'} | {tag.strip()}")
    text = "\n".join(lines)
    for i in range(0, len(text), 3800):   # Telegram inakata ujumbe mrefu
        await update.message.reply_text(text[i:i + 3800])


async def mtumiaji(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    if not context.args:
        await update.message.reply_text("Tumia: /mtumiaji <id au namba ya simu>")
        return
    key = context.args[0]
    phone = normalize_phone(key)
    with closing(db()) as conn:
        if phone:
            u = conn.execute("SELECT * FROM users WHERE phone=?", (phone,)).fetchone()
        else:
            try:
                u = conn.execute("SELECT * FROM users WHERE user_id=?", (int(key),)).fetchone()
            except ValueError:
                u = None
        if not u:
            await update.message.reply_text("❌ Mtumiaji hapatikani.")
            return
        card = _user_card(conn, u)
    await update.message.reply_text(card)


async def bidhaa_za(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    try:
        uid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("Tumia: /bidhaa_za <id ya mtumiaji>")
        return
    with closing(db()) as conn:
        u = conn.execute("SELECT name, phone FROM users WHERE user_id=?", (uid,)).fetchone()
        rows = conn.execute(
            "SELECT p.*, COALESCE((SELECT SUM(profit) FROM sales WHERE product_id=p.id),0) f, "
            "COALESCE((SELECT SUM(qty) FROM sales WHERE product_id=p.id),0) q "
            "FROM products p WHERE p.owner_id=? ORDER BY p.id", (uid,)
        ).fetchall()
    if not u:
        await update.message.reply_text("❌ Mtumiaji hapatikani.")
        return
    if not rows:
        await update.message.reply_text(f"{u['name']} bado hana bidhaa.")
        return
    out = [f"💼 Bidhaa za {u['name']} ({u['phone'] or '-'})"]
    for r in rows:
        out.append(
            f"{r['id']}. {r['name']} | kununua {money(r['cost'])} | kuuza {money(r['price'])} | "
            f"stoo {r['stock']} | zimeuzwa {r['q']} | faida {money(r['f'])}"
        )
    text = "\n".join(out)
    for i in range(0, len(text), 3800):
        await update.message.reply_text(text[i:i + 3800])


async def reset_password(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    try:
        uid, new = int(context.args[0]), context.args[1]
        assert len(new) >= 6
    except (IndexError, ValueError, AssertionError):
        await update.message.reply_text("Tumia: /reset_password <id> <password mpya (angalau 6)>")
        return
    try:
        await update.message.delete()
    except Exception:
        pass
    h, salt = await asyncio.to_thread(hash_password, new)
    with closing(db()) as conn, conn:
        cur = conn.execute(
            "UPDATE users SET password_hash=?, salt=?, failed_logins=0 WHERE user_id=?", (h, salt, uid)
        )
    msg = "✅ Password imebadilishwa na account imefunguliwa." if cur.rowcount else "❌ Mtumiaji hapatikani."
    await context.bot.send_message(update.effective_user.id, msg)
    if cur.rowcount:
        try:
            await context.bot.send_message(uid, "🔑 Admin amebadilisha password yako. Mwombe akupe mpya.")
        except Exception:
            pass


# ====== MALIPO YA USAJILI ======
P_REF = 20


async def hali(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    with closing(db()) as conn:
        u = conn.execute("SELECT * FROM users WHERE user_id=?", (update.effective_user.id,)).fetchone()
    if not u["password_hash"]:
        await update.message.reply_text(NOT_REG_MSG)
        return
    await update.message.reply_text(f"📅 {status_text(u)}\n\nUsajili: {money(SUB_PRICE)} kwa siku {SUB_DAYS}. Lipia: /lipia")


async def lipia(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    ensure_user(user)
    if not is_registered(user.id):
        await update.message.reply_text(NOT_REG_MSG)
        return ConversationHandler.END
    with closing(db()) as conn:
        pend = conn.execute("SELECT id FROM payments WHERE user_id=? AND status='pending'", (user.id,)).fetchone()
    if pend:
        await update.message.reply_text(
            f"⏳ Una malipo #{pend['id']} yanayosubiri uthibitisho wa admin. Utafunguliwa mara yakithibitishwa."
        )
        return ConversationHandler.END
    await update.message.reply_text(
        f"💳 MALIPO YA USAJILI\n"
        f"Kiasi: {money(SUB_PRICE)} kwa siku {SUB_DAYS}\n\n"
        f"{PAY_INFO}\n\n"
        f"Ukishalipa, tuma hapa ID ya muamala (mfano SK12AB34CD) au nakili ujumbe wote wa muamala.\n"
        f"Kughairi: /ghairi"
    )
    return P_REF


async def lipia_ref(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    text = update.message.text.strip()
    if text in MENU_TEXTS:
        return await ghairi(update, context)
    note = re.sub(r"\s+", " ", text)[:300]
    tokens = [t for t in re.findall(r"\b[A-Za-z0-9]{8,12}\b", note) if re.search(r"\d", t) and re.search(r"[A-Za-z]", t)]
    key = (tokens[0] if tokens else note).upper()
    if len(note) < 6:
        await update.message.reply_text("❌ Tuma ID ya muamala au ujumbe wote wa malipo.")
        return P_REF
    try:
        with closing(db()) as conn, conn:
            pid = conn.execute(
                "INSERT INTO payments(user_id,amount,txn_ref,note,ts) VALUES(?,?,?,?,?)",
                (user.id, SUB_PRICE, key, note, now()),
            ).lastrowid
    except sqlite3.IntegrityError:
        await update.message.reply_text("❌ ID hii ya muamala imeshatumika. Hakikisha umetuma ID sahihi.")
        return P_REF
    with closing(db()) as conn:
        u = conn.execute("SELECT * FROM users WHERE user_id=?", (user.id,)).fetchone()
    await update.message.reply_text(
        f"✅ Malipo #{pid} yametumwa. Utafunguliwa mara tu admin atakapothibitisha.",
        reply_markup=menu_for(user.id),
    )
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Thibitisha", callback_data=f"pay_ok_{pid}"),
        InlineKeyboardButton("❌ Kataa", callback_data=f"pay_no_{pid}"),
    ]])
    for a in ADMIN_IDS:
        try:
            await context.bot.send_message(
                a,
                f"💳 Malipo #{pid}\nMtumiaji: {u['name']} ({user.id})\nSimu: {u['phone']}\n"
                f"Kiasi: {money(SUB_PRICE)}\nID/Ujumbe: {note}",
                reply_markup=kb,
            )
        except Exception:
            pass
    return ConversationHandler.END


async def pay_buttons(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    if not is_admin(q.from_user.id):
        await q.answer("Huna ruhusa.", show_alert=True)
        return
    _, action, pid = q.data.split("_")
    pid = int(pid)
    bonus, ref_id, new_until, user_id, name = 0, None, None, None, ""
    with closing(db()) as conn, conn:
        p = conn.execute("SELECT * FROM payments WHERE id=?", (pid,)).fetchone()
        if not p or p["status"] != "pending":
            await q.edit_message_text(f"Malipo #{pid} yameshashughulikiwa.")
            return
        u = conn.execute("SELECT * FROM users WHERE user_id=?", (p["user_id"],)).fetchone()
        user_id, name = u["user_id"], u["name"]
        if action == "ok":
            end = access_end(u)
            base = end if end and end > now() else now()      # siku za ofa zilizobaki hazipotei
            new_until = add_days(base, SUB_DAYS)
            first = conn.execute(
                "SELECT COUNT(*) n FROM payments WHERE user_id=? AND status='approved'", (u["user_id"],)
            ).fetchone()["n"] == 0
            conn.execute("UPDATE users SET paid_until=? WHERE user_id=?", (new_until, user_id))
            conn.execute("UPDATE payments SET status='approved', decided_ts=? WHERE id=?", (now(), pid))
            if u["referrer_id"] and (first or BONUS_EVERY_PAYMENT):
                ref_id, bonus = u["referrer_id"], REFERRAL_BONUS
                conn.execute("UPDATE users SET balance=balance+? WHERE user_id=?", (bonus, ref_id))
                conn.execute(
                    "INSERT INTO bonuses(user_id,from_user,amount,ts) VALUES(?,?,?,?)",
                    (ref_id, user_id, bonus, now()),
                )
        else:
            conn.execute("UPDATE payments SET status='rejected', decided_ts=? WHERE id=?", (now(), pid))
    if action == "ok":
        await q.edit_message_text(
            f"✅ Malipo #{pid} yamethibitishwa. {name} amefunguliwa hadi {new_until[:10]}."
            + (f"\n🎁 Bonasi ya {money(bonus)} imeingia kwa aliyemleta ({ref_id})." if bonus else "")
        )
        try:
            await context.bot.send_message(
                user_id, f"🎉 Malipo yamethibitishwa! Account yako imefunguliwa hadi {new_until[:10]}.",
                reply_markup=menu_for(user_id),
            )
        except Exception:
            pass
        if bonus:
            try:
                await context.bot.send_message(ref_id, f"🎁 {name} amelipia usajili kupitia rufaa yako. Umepata {money(bonus)}!")
            except Exception:
                pass
    else:
        await q.edit_message_text(f"❌ Malipo #{pid} yamekataliwa.")
        try:
            await context.bot.send_message(
                user_id, f"❌ Malipo #{pid} hayakuthibitishwa. Hakikisha ID ya muamala ni sahihi kisha jaribu tena: /lipia"
            )
        except Exception:
            pass


async def malipo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    with closing(db()) as conn:
        rows = conn.execute(
            "SELECT p.*, u.name, u.phone FROM payments p JOIN users u ON u.user_id=p.user_id "
            "WHERE p.status='pending' ORDER BY p.id"
        ).fetchall()
    if not rows:
        await update.message.reply_text("Hakuna malipo yanayosubiri.")
        return
    for r in rows:
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("✅ Thibitisha", callback_data=f"pay_ok_{r['id']}"),
            InlineKeyboardButton("❌ Kataa", callback_data=f"pay_no_{r['id']}"),
        ]])
        await update.message.reply_text(
            f"💳 Malipo #{r['id']}\n{r['name']} ({r['user_id']}) | {r['phone']}\n"
            f"{money(r['amount'])}\nID/Ujumbe: {r['note']}\n{r['ts']}",
            reply_markup=kb,
        )


async def ongeza_siku(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    try:
        uid, days = int(context.args[0]), int(context.args[1])
        assert days != 0
    except (IndexError, ValueError, AssertionError):
        await update.message.reply_text("Tumia: /ongeza_siku <id> <siku>\nMfano: /ongeza_siku 123456 30")
        return
    with closing(db()) as conn, conn:
        u = conn.execute("SELECT * FROM users WHERE user_id=?", (uid,)).fetchone()
        if not u or not u["password_hash"]:
            await update.message.reply_text("❌ Mtumiaji hajasajiliwa au hapatikani.")
            return
        end = access_end(u)
        base = end if end and end > now() else now()
        new_until = add_days(base, days)
        conn.execute("UPDATE users SET paid_until=? WHERE user_id=?", (new_until, uid))
    await update.message.reply_text(f"✅ {u['name']} sasa ana access hadi {new_until[:10]}.")
    try:
        await context.bot.send_message(uid, f"🎁 Admin amekuongezea siku {days}. Account yako iko hai hadi {new_until[:10]}.")
    except Exception:
        pass


async def funga(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    try:
        uid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("Tumia: /funga <id ya mtumiaji>")
        return
    with closing(db()) as conn, conn:
        cur = conn.execute("UPDATE users SET trial_until=?, paid_until=? WHERE user_id=? AND password_hash IS NOT NULL",
                           (now(), now(), uid))
    await update.message.reply_text("🔒 Account imefungwa. Kufungua: /ongeza_siku <id> <siku>" if cur.rowcount else "❌ Mtumiaji hapatikani.")


async def reminders(context: ContextTypes.DEFAULT_TYPE):
    """Inatumwa kila REMINDER_HOURS: kikumbusho siku 2 kabla ya kuisha, na taarifa ya kufungwa."""
    today = datetime.now().strftime("%Y-%m-%d")
    with closing(db()) as conn:
        users = conn.execute("SELECT * FROM users WHERE password_hash IS NOT NULL").fetchall()
    for u in users:
        await asyncio.sleep(0)          # acha amri za watumiaji ziendelee wakati kazi hii inaendelea
        active, end, kind = sub_state(u)
        if kind in ("admin", "none"):
            continue
        left = (datetime.strptime(end, FMT) - datetime.now()).total_seconds()
        msg, mark = None, None
        if active and left <= 2 * 86400 and u["last_reminder"] != f"R:{today}":
            what = "ofa yako ya bure" if kind == "trial" else "usajili wako"
            msg, mark = (f"⏰ {what} unaisha {end[:10]} (siku {days_left(end)} zimebaki). "
                         f"Lipia {money(SUB_PRICE)} ili usifungiwe: /lipia"), f"R:{today}"
        elif not active and -86400 <= left <= 0 and u["last_reminder"] != f"E:{today}":
            msg, mark = lock_message(u), f"E:{today}"
        if msg:
            try:
                await context.bot.send_message(u["user_id"], msg)
            except Exception:
                pass
            with closing(db()) as conn, conn:
                conn.execute("UPDATE users SET last_reminder=? WHERE user_id=?", (mark, u["user_id"]))


# ====== USAJILI ======
def register(app: Application):
    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("jisajili", jisajili)],
        states={
            ASK_TERMS: [CallbackQueryHandler(terms_accept, pattern=r"^tm_(yes|no)$")],
            ASK_PHONE: [MessageHandler(filters.TEXT & ~filters.COMMAND, get_phone)],
            ASK_PASS: [MessageHandler(filters.TEXT & ~filters.COMMAND, get_pass)],
            ASK_PASS2: [MessageHandler(filters.TEXT & ~filters.COMMAND, get_pass2)],
        },
        fallbacks=[CommandHandler("ghairi", ghairi)],
    ))
    app.add_handler(ConversationHandler(
        entry_points=[
            MessageHandler(filters.Regex(f"^{re.escape(BTN_WITHDRAW)}$"), wd_start),
            CommandHandler("withdraw", wd_start),
        ],
        states={
            W_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, wd_amount)],
            W_PASS: [MessageHandler(filters.TEXT & ~filters.COMMAND, wd_pass)],
        },
        fallbacks=[CommandHandler("ghairi", ghairi)],
    ))
    # Vitufe vya menyu vinafanya kazi kama amri zilizopo
    for text, fn in [
        (BTN_BALANCE, salio), (BTN_HISTORY, historia), (BTN_PRODUCTS, bidhaa),
        (BTN_SALES, mauzo), (BTN_REFER, rufaa), (BTN_ACCOUNT, akaunti),
        (BTN_MYPROD, bidhaa_zangu), (BTN_PROFIT, faida), (BTN_STATUS, hali),
        (BTN_USERS, watumiaji), (BTN_REPORT, ripoti), (BTN_REQUESTS, maombi), (BTN_PAYMENTS, malipo),
    ]:
        app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(text)}$"), fn))
    app.add_handler(CommandHandler("historia", historia))
    app.add_handler(ConversationHandler(
        entry_points=[
            MessageHandler(filters.Regex(f"^{re.escape(BTN_PAY)}$"), lipia),
            CommandHandler("lipia", lipia),
        ],
        states={P_REF: [MessageHandler(filters.TEXT & ~filters.COMMAND, lipia_ref)]},
        fallbacks=[CommandHandler("ghairi", ghairi)],
    ))
    app.add_handler(CallbackQueryHandler(pay_buttons, pattern=r"^pay_(ok|no)_\d+$"))
    app.add_handler(CommandHandler("hali", hali))
    app.add_handler(CommandHandler("malipo", malipo))
    app.add_handler(CommandHandler("ongeza_siku", ongeza_siku))
    app.add_handler(CommandHandler("funga", funga))
    if app.job_queue:      # vikumbusho vinahitaji: pip install "python-telegram-bot[job-queue]"
        app.job_queue.run_repeating(reminders, interval=REMINDER_HOURS * 3600, first=60)
    app.add_handler(CommandHandler("history", historia))
    app.add_handler(CommandHandler("weka_bidhaa", weka_bidhaa))
    app.add_handler(CommandHandler("bidhaa_zangu", bidhaa_zangu))
    app.add_handler(CommandHandler("jaza_stoo", jaza_stoo))
    app.add_handler(CommandHandler("badili_bei", badili_bei))
    app.add_handler(CommandHandler("faida", faida))
    app.add_handler(CommandHandler("bidhaa_za", bidhaa_za))
    app.add_handler(CommandHandler("balance", salio))
    app.add_handler(CommandHandler("menu", menu))
    app.add_handler(CommandHandler("akaunti", akaunti))
    app.add_handler(CommandHandler("watumiaji", watumiaji))
    app.add_handler(CommandHandler("mtumiaji", mtumiaji))
    app.add_handler(CommandHandler("reset_password", reset_password))
    app.add_handler(CommandHandler("start", start_mauzo))
    app.add_handler(CommandHandler("bidhaa", bidhaa))
    app.add_handler(CommandHandler("uza", uza))
    app.add_handler(CommandHandler("mauzo", mauzo))
    app.add_handler(CommandHandler("salio", salio))
    app.add_handler(CommandHandler("rufaa", rufaa))
    app.add_handler(CommandHandler("toa", toa))
    app.add_handler(CommandHandler("ongeza_bidhaa", ongeza_bidhaa))
    app.add_handler(CommandHandler("ongeza_stoo", ongeza_stoo))
    app.add_handler(CommandHandler("maombi", maombi))
    app.add_handler(CommandHandler("ripoti", ripoti))
    app.add_handler(CallbackQueryHandler(wd_buttons, pattern=r"^wd_(ok|no)_\d+$"))
    register_plus(app)         # vipengele vya ziada: kuuza kwa vitufe, madeni, matumizi, ripoti, backup...


# ################################################################
# VIPENGELE VYA ZIADA
# ################################################################
REPORT_HOUR = 20      # ripoti ya usiku inatumwa kuanzia saa hii (saa ya simu/server)
BACKUP_HOUR = 3       # nakala ya database inatumwa kuanzia saa hii kila siku
LOW_STOCK = 5


# ====== MSAIDIZI ======
def get_setting(key):
    with closing(db()) as conn:
        r = conn.execute("SELECT value FROM settings WHERE key=?", (key,)).fetchone()
    return r["value"] if r else None


def set_setting(key, value):
    with closing(db()) as conn, conn:
        conn.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)", (key, value))


def clean_name(name):
    """Jina la bidhaa iliyofutwa linaonyeshwa bila namba ya ndani."""
    return re.sub(r" \[imefutwa \d+\]$", " (imefutwa)", name)


async def _guard(q):
    """Ukaguzi wa vitufe: lazima awe amesajiliwa na account iwe hai."""
    uid = q.from_user.id
    eff = eff_uid(uid)
    if eff != uid:                                     # msaidizi: tunakagua account ya bosi
        ok_o, _ = check_access(eff)
        if not ok_o:
            await q.answer("🔒 Account ya bosi wako imefungwa.", show_alert=True)
        return ok_o
    if not is_registered(uid) and not is_admin(uid):
        await q.answer("Jisajili kwanza: /jisajili", show_alert=True)
        return False
    ok, _ = check_access(uid)
    if not ok:
        await q.answer("🔒 Account imefungwa. Lipia kwa /lipia", show_alert=True)
        return False
    return True


async def _edit(q, text, kb=None):
    """Hariri ujumbe wa kitufe, iwe ni maandishi au picha yenye caption."""
    if q.message.photo:
        await q.edit_message_caption(caption=text, reply_markup=kb)
    else:
        await q.edit_message_text(text, reply_markup=kb)


# ====== 1. KUUZA KWA VITUFE ======
def _products_keyboard(uid):
    with closing(db()) as conn:
        rows = conn.execute(
            "SELECT id,name,price,stock,owner_id,photo_id FROM products "
            "WHERE active=1 AND stock>0 AND (owner_id=? OR owner_id IS NULL) "
            "ORDER BY owner_id IS NULL, id LIMIT 40", (uid,)
        ).fetchall()
    kb = Kb([[Btn(
        f"{'🏪 ' if r['owner_id'] is None else ''}{'📷 ' if r['photo_id'] else ''}{r['name']} · {int(r['price']):,} · stoo {r['stock']}",
        callback_data=f"up_{r['id']}")] for r in rows])
    return kb, rows


@require_active
async def uza_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    eff = eff_uid(uid)
    if eff == uid and not is_registered(uid):
        await update.message.reply_text(NOT_REG_MSG)
        return
    if eff != uid:
        ok_o, _ = check_access(eff)
        if not ok_o:
            await update.message.reply_text("🔒 Account ya bosi wako imefungwa. Mwambie alipie: /lipia")
            return
    kb, rows = _products_keyboard(eff)
    if not rows:
        await update.message.reply_text(
            "Huna bidhaa zenye stoo.\nWeka kwa: /weka_bidhaa <jina> <bei ya kununua> <bei ya kuuza> <stoo>\n"
            "Mfano: /weka_bidhaa Sukari 2500 3000 20"
        )
        return
    await update.message.reply_text("🛒 Chagua bidhaa unayouza:", reply_markup=kb)


async def pick_product(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not await _guard(q):
        return
    pid = int(q.data.split("_")[1])
    with closing(db()) as conn:
        p = conn.execute("SELECT * FROM products WHERE id=?", (pid,)).fetchone()
    if not p or p["active"] == 0 or (p["owner_id"] is not None and p["owner_id"] != eff_uid(q.from_user.id)):
        await q.answer("Bidhaa haipo.", show_alert=True)
        return
    await q.answer()
    kb = Kb([
        [Btn(str(n), callback_data=f"uq_{pid}_{n}") for n in (1, 2, 3, 5, 10)],
        [Btn("✍️ Idadi nyingine", callback_data=f"uo_{pid}"), Btn("📒 Kwa deni", callback_data=f"ud_{pid}")],
        [Btn("⬅️ Rudi", callback_data="ub")],
    ])
    text = f"🛒 {p['name']}\nBei: {money(p['price'])} | Stoo: {p['stock']}\n\nChagua idadi:"
    if p["photo_id"]:
        try:
            await q.message.reply_photo(photo=p["photo_id"], caption=text, reply_markup=kb)
            await q.message.delete()
            return
        except Exception:
            pass                       # picha ikishindwa kupakia, tunaendelea na maandishi
    await _edit(q, text, kb)


async def back_to_products(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not await _guard(q):
        return
    await q.answer()
    kb, rows = _products_keyboard(eff_uid(q.from_user.id))
    if not rows:
        await _edit(q, "Huna bidhaa zenye stoo. Weka kwa /weka_bidhaa")
        return
    if q.message.photo:                # ujumbe wa picha hauwezi kugeuzwa kuwa maandishi
        await q.message.reply_text("🛒 Chagua bidhaa unayouza:", reply_markup=kb)
        await q.message.delete()
        return
    await q.edit_message_text("🛒 Chagua bidhaa unayouza:", reply_markup=kb)


def _after_kb(info):
    return Kb([
        [Btn("↩️ Tengua", callback_data=f"tg_{info['sale_id']}"), Btn("📄 Risiti", callback_data=f"rc_{info['sale_id']}")],
        [Btn("🛒 Uza tena", callback_data="ub")],
    ])


async def quick_qty(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not await _guard(q):
        return
    _, pid, qty = q.data.split("_")
    eff = eff_uid(q.from_user.id)
    ok, text, info = do_sale(eff, int(pid), int(qty), actor=q.from_user.id if eff != q.from_user.id else None)
    await q.answer()
    if not ok:
        await _edit(q, text, Kb([[Btn("⬅️ Rudi", callback_data="ub")]]))
        return
    await _edit(q, text, _after_kb(info))
    await notify_after_sale(context, info)


SELL_QTY = 30


async def custom_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not await _guard(q):
        return ConversationHandler.END
    await q.answer()
    kind, pid = q.data.split("_")
    context.user_data["sell_pid"] = int(pid)
    context.user_data["sell_credit"] = kind == "ud"
    if kind == "ud":
        msg = "📒 Andika idadi kisha jina la mteja.\nMfano: 3 Juma"
    else:
        msg = "✍️ Andika idadi uliyouza. Mfano: 4"
    await q.message.reply_text(msg + "\nKughairi: /ghairi")
    return SELL_QTY


async def custom_qty(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = update.message.text.strip()
    if text in MENU_TEXTS:
        return await ghairi(update, context)
    parts = text.split(None, 1)
    try:
        qty = int(parts[0])
        assert qty > 0
    except (ValueError, AssertionError, IndexError):
        await update.message.reply_text("❌ Andika namba ya idadi. Mfano: 4")
        return SELL_QTY
    credit = context.user_data.get("sell_credit")
    customer = parts[1].strip() if len(parts) > 1 else None
    if credit and not customer:
        await update.message.reply_text("❌ Andika pia jina la mteja. Mfano: 3 Juma")
        return SELL_QTY
    me = update.effective_user.id
    eff = eff_uid(me)
    ok, msg, info = do_sale(eff, context.user_data["sell_pid"], qty, customer if credit else None,
                            actor=me if eff != me else None)
    context.user_data.clear()
    if not ok:
        await update.message.reply_text(msg)
        return ConversationHandler.END
    await update.message.reply_text(msg, reply_markup=_after_kb(info))
    await notify_after_sale(context, info)
    return ConversationHandler.END


# ====== 2. KUTENGUA MAUZO ======
def undo_sale(uid, sale_id=None):
    with closing(db()) as conn, conn:
        if sale_id:
            s = conn.execute("SELECT * FROM sales WHERE id=? AND (seller_id=? OR sold_by=?)", (sale_id, uid, uid)).fetchone()
        else:
            s = conn.execute("SELECT * FROM sales WHERE seller_id=? OR sold_by=? ORDER BY id DESC LIMIT 1", (uid, uid)).fetchone()
        if not s:
            return False, "❌ Hakuna mauzo ya kutengua (au yameshatenguliwa)."
        if s["ts"] < add_days(now(), -1):
            return False, "❌ Mauzo ya zaidi ya saa 24 hayawezi kutenguliwa."
        p = conn.execute("SELECT name FROM products WHERE id=?", (s["product_id"],)).fetchone()
        conn.execute("UPDATE products SET stock=stock+? WHERE id=?", (s["qty"], s["product_id"]))
        if s["commission"]:
            conn.execute("UPDATE users SET balance=balance-? WHERE user_id=?", (s["commission"], s["seller_id"]))
        if s["ref_commission"]:
            ref = conn.execute("SELECT referrer_id FROM users WHERE user_id=?", (s["seller_id"],)).fetchone()
            if ref and ref["referrer_id"]:
                conn.execute("UPDATE users SET balance=balance-? WHERE user_id=?", (s["ref_commission"], ref["referrer_id"]))
        conn.execute("DELETE FROM debts WHERE sale_id=?", (s["id"],))
        conn.execute("DELETE FROM sales WHERE id=?", (s["id"],))
    return True, f"↩️ Mauzo yametenguliwa: {p['name'] if p else ''} x{s['qty']} ({money(s['total'])}). Stoo imerudishwa."


@require_active
async def tengua(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    with closing(db()) as conn:
        s = conn.execute(
            "SELECT s.id, s.qty, s.total, s.ts, p.name FROM sales s JOIN products p ON p.id=s.product_id "
            "WHERE (s.seller_id=? OR s.sold_by=?) ORDER BY s.id DESC LIMIT 1", (uid, uid)
        ).fetchone()
    if not s:
        await update.message.reply_text("Hakuna mauzo ya kutengua.")
        return
    kb = Kb([[Btn("↩️ Ndiyo, tengua", callback_data=f"tg_{s['id']}"), Btn("❌ Hapana", callback_data="tgx")]])
    await update.message.reply_text(
        f"Tengua mauzo ya mwisho?\n{s['ts'][:16]} | {s['name']} x{s['qty']} | {money(s['total'])}", reply_markup=kb
    )


async def undo_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if q.data == "tgx":
        await q.answer()
        await _edit(q, "Sawa, hakuna kilichobadilishwa.")
        return
    if not await _guard(q):
        return
    await q.answer()
    ok, msg = undo_sale(q.from_user.id, int(q.data.split("_")[1]))
    await _edit(q, msg)


# ====== 3. MUHTASARI WA LEO + RIPOTI YA USIKU ======
def build_summary(uid):
    """Inarudisha (maandishi, kuna_cha_kuripoti)."""
    start = datetime.now().replace(hour=0, minute=0, second=0).strftime(FMT)
    with closing(db()) as conn:
        s = conn.execute(
            "SELECT COUNT(*) n, COALESCE(SUM(total),0) t, COALESCE(SUM(profit),0) f FROM sales "
            "WHERE seller_id=? AND ts>=?", (uid, start)
        ).fetchone()
        e = conn.execute("SELECT COALESCE(SUM(amount),0) e FROM expenses WHERE user_id=? AND ts>=?", (uid, start)).fetchone()["e"]
        top = conn.execute(
            "SELECT p.name, SUM(s.qty) q FROM sales s JOIN products p ON p.id=s.product_id "
            "WHERE s.seller_id=? AND s.ts>=? GROUP BY p.id ORDER BY q DESC LIMIT 3", (uid, start)
        ).fetchall()
        low = conn.execute(
            "SELECT name, stock FROM products WHERE owner_id=? AND active=1 AND stock<=? ORDER BY stock LIMIT 5",
            (uid, LOW_STOCK),
        ).fetchall()
        d = conn.execute(
            "SELECT COALESCE(SUM(amount-paid),0) due, COUNT(*) n FROM debts WHERE user_id=? AND amount-paid>0.009", (uid,)
        ).fetchone()
        old = conn.execute(
            "SELECT COUNT(*) n FROM debts WHERE user_id=? AND amount-paid>0.009 AND ts<?",
            (uid, add_days(now(), -7)),
        ).fetchone()["n"]
    out = [
        "📊 MUHTASARI WA LEO",
        f"Mauzo: {s['n']} | {money(s['t'])}",
        f"Faida ya mauzo: {money(s['f'])}",
        f"Matumizi: {money(e)}",
        f"💹 FAIDA HALISI: {money(s['f'] - e)}",
    ]
    if top:
        out.append("\n🏆 Zilizouzwa zaidi leo: " + ", ".join(f"{clean_name(r['name'])} ({r['q']})" for r in top))
    if low:
        out.append("\n⚠️ Stoo inaisha:\n" + "\n".join(f"- {r['name']}: {r['stock']}" for r in low))
    if d["n"]:
        out.append(f"\n📒 Madeni yasiyolipwa: {money(d['due'])} ({d['n']})" + (f"\n   {old} yamezidi siku 7. Tazama /madeni" if old else ""))
    return "\n".join(out), bool(s["n"] or e or low or d["n"])


@require_active
async def leo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    if not is_registered(update.effective_user.id):
        await update.message.reply_text(NOT_REG_MSG)
        return
    await update.message.reply_text(build_summary(update.effective_user.id)[0])


async def ripoti_usiku(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    arg = (context.args[0].lower() if context.args else "")
    if arg not in ("washa", "zima"):
        with closing(db()) as conn:
            u = conn.execute("SELECT report_on FROM users WHERE user_id=?", (uid,)).fetchone()
        state = "IMEWASHWA ✅" if (u["report_on"] is None or u["report_on"]) else "IMEZIMWA ⛔"
        await update.message.reply_text(f"Ripoti ya kila usiku (saa {REPORT_HOUR}:00) {state}\nBadilisha: /ripoti_usiku washa  au  /ripoti_usiku zima")
        return
    with closing(db()) as conn, conn:
        conn.execute("UPDATE users SET report_on=? WHERE user_id=?", (1 if arg == "washa" else 0, uid))
    await update.message.reply_text("✅ Ripoti ya kila usiku imewashwa." if arg == "washa" else "⛔ Ripoti ya kila usiku imezimwa.")


# ====== 4. MADENI ======
@require_active
async def deni(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    if not is_registered(uid):
        await update.message.reply_text(NOT_REG_MSG)
        return
    try:
        customer, amount = context.args[0], _num(context.args[1])
        note = " ".join(context.args[2:])[:120]
        assert amount > 0
    except (IndexError, ValueError, AssertionError):
        await update.message.reply_text(
            "Tumia: /deni <jina la mteja (neno moja)> <kiasi> [maelezo]\nMfano: /deni Juma 5000 sukari 2kg\n"
            "Kuuza kwa mkopo moja kwa moja: bonyeza 🛒 Uza → 📒 Kwa deni"
        )
        return
    with closing(db()) as conn, conn:
        did = conn.execute(
            "INSERT INTO debts(user_id,customer,amount,paid,note,ts) VALUES(?,?,?,?,?,?)",
            (uid, customer[:60], amount, 0, note, now()),
        ).lastrowid
    await update.message.reply_text(f"📒 Deni #{did}: {customer} anadaiwa {money(amount)}.\nAkilipa: /lipa_deni {did}  au bonyeza 📒 Madeni")


def _debts_view(uid):
    with closing(db()) as conn:
        rows = conn.execute(
            "SELECT * FROM debts WHERE user_id=? AND amount-paid>0.009 ORDER BY ts", (uid,)
        ).fetchall()
    if not rows:
        return "📒 Hakuna madeni. Wateja wote wamelipa 🎉\nAndika deni: /deni Juma 5000 sukari", None
    per = {}
    for r in rows:
        per[r["customer"]] = per.get(r["customer"], 0) + (r["amount"] - r["paid"])
    total = sum(per.values())
    out = [f"📒 MADENI YA WATEJA\nJumla: {money(total)} (wateja {len(per)})\n"]
    out += [f"• {c}: {money(v)}" for c, v in sorted(per.items(), key=lambda x: -x[1])]
    out.append("\nMaelezo:")
    today = datetime.now()
    for r in rows[:15]:
        days = (today - datetime.strptime(r["ts"], FMT)).days
        part = f" (kati ya {money(r['amount'])})" if r["paid"] > 0 else ""
        out.append(f"#{r['id']} {r['customer']} | {money(r['amount'] - r['paid'])}{part} | siku {days}" + (f" | {r['note']}" if r["note"] else ""))
    out.append("\nBonyeza kuashiria amelipa, au /lipa_deni <id> <kiasi> kwa malipo ya sehemu.")
    kb = Kb([[Btn(f"✅ #{r['id']} {r['customer']} amelipa {int(r['amount'] - r['paid']):,}", callback_data=f"dp_{r['id']}")]
             for r in rows[:8]])
    return "\n".join(out), kb


@require_active
async def madeni(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    if not is_registered(update.effective_user.id):
        await update.message.reply_text(NOT_REG_MSG)
        return
    text, kb = _debts_view(update.effective_user.id)
    await update.message.reply_text(text, reply_markup=kb)


async def debt_paid_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not await _guard(q):
        return
    did = int(q.data.split("_")[1])
    with closing(db()) as conn, conn:
        d = conn.execute("SELECT * FROM debts WHERE id=? AND user_id=?", (did, q.from_user.id)).fetchone()
        if not d or d["amount"] - d["paid"] <= 0.009:
            await q.answer("Deni hili limeshalipwa au halipo.", show_alert=True)
            return
        conn.execute("UPDATE debts SET paid=amount WHERE id=?", (did,))
    await q.answer("✅ Imeandikwa")
    text, kb = _debts_view(q.from_user.id)
    await q.edit_message_text(f"✅ {d['customer']} amelipa deni #{did}.\n\n" + text, reply_markup=kb)


@require_active
async def lipa_deni(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    try:
        did = int(context.args[0])
        amt = _num(context.args[1]) if len(context.args) > 1 else None
        assert amt is None or amt > 0
    except (IndexError, ValueError, AssertionError):
        await update.message.reply_text("Tumia: /lipa_deni <id> [kiasi]\nBila kiasi = amelipa lote.\nMfano: /lipa_deni 3 2000")
        return
    with closing(db()) as conn, conn:
        d = conn.execute("SELECT * FROM debts WHERE id=? AND user_id=?", (did, uid)).fetchone()
        if not d:
            await update.message.reply_text("❌ Deni halipo. Angalia /madeni")
            return
        rem = d["amount"] - d["paid"]
        pay = rem if amt is None else min(amt, rem)
        conn.execute("UPDATE debts SET paid=paid+? WHERE id=?", (pay, did))
    left = rem - pay
    await update.message.reply_text(
        f"✅ {d['customer']} amelipa {money(pay)}." + (f" Bado anadaiwa {money(left)}." if left > 0.009 else " Deni limeisha. 🎉")
    )


# ====== 5. MATUMIZI ======
@require_active
async def matumizi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    if not is_registered(uid):
        await update.message.reply_text(NOT_REG_MSG)
        return
    if not context.args:
        month = (datetime.now() - timedelta(days=30)).strftime(FMT)
        today = datetime.now().replace(hour=0, minute=0, second=0).strftime(FMT)
        with closing(db()) as conn:
            tm = conn.execute("SELECT COALESCE(SUM(amount),0) a FROM expenses WHERE user_id=? AND ts>=?", (uid, month)).fetchone()["a"]
            td = conn.execute("SELECT COALESCE(SUM(amount),0) a FROM expenses WHERE user_id=? AND ts>=?", (uid, today)).fetchone()["a"]
            rows = conn.execute("SELECT * FROM expenses WHERE user_id=? ORDER BY id DESC LIMIT 10", (uid,)).fetchall()
        out = [f"🧮 MATUMIZI\nLeo: {money(td)} | Siku 30: {money(tm)}"]
        if rows:
            out.append("\nYa hivi karibuni:")
            out += [f"#{r['id']} {r['ts'][:16]} | {money(r['amount'])} | {r['note']}" for r in rows]
        out.append("\nAndika: /matumizi <kiasi> <maelezo>\nMfano: /matumizi 2000 usafiri\nKufuta: /futa_matumizi <id>")
        await update.message.reply_text("\n".join(out))
        return
    try:
        amount = _num(context.args[0])
        assert amount > 0
    except (ValueError, AssertionError):
        await update.message.reply_text("Tumia: /matumizi <kiasi> <maelezo>\nMfano: /matumizi 2000 usafiri")
        return
    note = " ".join(context.args[1:])[:120] or "matumizi"
    start = datetime.now().replace(hour=0, minute=0, second=0).strftime(FMT)
    with closing(db()) as conn, conn:
        eid = conn.execute("INSERT INTO expenses(user_id,amount,note,ts) VALUES(?,?,?,?)", (uid, amount, note, now())).lastrowid
        tot = conn.execute("SELECT COALESCE(SUM(amount),0) a FROM expenses WHERE user_id=? AND ts>=?", (uid, start)).fetchone()["a"]
    await update.message.reply_text(f"🧮 Matumizi #{eid} yameandikwa: {money(amount)} ({note})\nJumla ya leo: {money(tot)}")


@require_active
async def futa_matumizi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        eid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("Tumia: /futa_matumizi <id>")
        return
    with closing(db()) as conn, conn:
        cur = conn.execute("DELETE FROM expenses WHERE id=? AND user_id=?", (eid, update.effective_user.id))
    await update.message.reply_text("🗑️ Imefutwa." if cur.rowcount else "❌ Haipo.")


# ====== 6. KUFUTA / KUHARIRI BIDHAA ======
@require_active
async def futa_bidhaa(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    try:
        pid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("Tumia: /futa_bidhaa <id>\nAngalia ID kwenye /bidhaa_zangu")
        return
    with closing(db()) as conn, conn:
        p = conn.execute("SELECT name FROM products WHERE id=? AND owner_id=? AND active=1", (pid, uid)).fetchone()
        if not p:
            await update.message.reply_text("❌ Huna bidhaa yenye ID hiyo.")
            return
        # Historia ya mauzo inabaki; bidhaa inaondolewa kwenye orodha
        conn.execute("UPDATE products SET active=0, name=name||' [imefutwa '||id||']' WHERE id=?", (pid,))
    await update.message.reply_text(f"🗑️ {p['name']} imefutwa. Historia ya mauzo yake inabaki.")


@require_active
async def hariri_jina(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    try:
        pid = int(context.args[0])
        name = " ".join(context.args[1:]).strip()
        assert name
    except (IndexError, ValueError, AssertionError):
        await update.message.reply_text("Tumia: /hariri_jina <id> <jina jipya>\nMfano: /hariri_jina 2 Sukari Kilombero")
        return
    try:
        with closing(db()) as conn, conn:
            cur = conn.execute("UPDATE products SET name=? WHERE id=? AND owner_id=? AND active=1", (name, pid, uid))
    except sqlite3.IntegrityError:
        await update.message.reply_text("❌ Tayari una bidhaa yenye jina hilo.")
        return
    await update.message.reply_text(f"✅ Jina sasa ni: {name}" if cur.rowcount else "❌ Huna bidhaa yenye ID hiyo.")


# ====== 7. RIPOTI YA EXCEL ======
@require_active
async def ripoti_excel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    if not is_registered(uid):
        await update.message.reply_text(NOT_REG_MSG)
        return
    period = (context.args[0].lower() if context.args else "mwezi")
    days = {"wiki": 7, "mwezi": 30, "yote": None}.get(period)
    if period not in ("wiki", "mwezi", "yote"):
        await update.message.reply_text("Tumia: /ripoti_excel wiki | mwezi | yote")
        return
    since = "0000" if days is None else (datetime.now() - timedelta(days=days)).strftime(FMT)
    with closing(db()) as conn:
        sales = conn.execute(
            "SELECT s.ts, p.name, s.qty, s.total, s.profit FROM sales s JOIN products p ON p.id=s.product_id "
            "WHERE s.seller_id=? AND s.ts>=? ORDER BY s.ts", (uid, since)).fetchall()
        exps = conn.execute("SELECT ts, amount, note FROM expenses WHERE user_id=? AND ts>=? ORDER BY ts", (uid, since)).fetchall()
        debts = conn.execute(
            "SELECT ts, customer, amount, paid, note FROM debts WHERE user_id=? ORDER BY ts", (uid,)).fetchall()
        stock = conn.execute(
            "SELECT name, cost, price, stock FROM products WHERE owner_id=? AND active=1 ORDER BY id", (uid,)).fetchall()
    tot_sales = sum(r["total"] for r in sales)
    tot_profit = sum(r["profit"] for r in sales)
    tot_exp = sum(r["amount"] for r in exps)
    due = sum(r["amount"] - r["paid"] for r in debts)
    stamp = datetime.now().strftime("%Y-%m-%d")
    path = os.path.join(tempfile.gettempdir(), f"ripoti_{uid}_{stamp}.xlsx")
    try:
        from openpyxl import Workbook
        from openpyxl.styles import Font
        wb = Workbook()
        ws = wb.active
        ws.title = "Muhtasari"
        for row in [
            ("RIPOTI YA BIASHARA", ""), ("Kipindi", period), ("Tarehe", stamp), ("", ""),
            ("Jumla ya mauzo", tot_sales), ("Faida ya mauzo", tot_profit), ("Matumizi", tot_exp),
            ("FAIDA HALISI", tot_profit - tot_exp), ("Madeni yasiyolipwa", due),
        ]:
            ws.append(row)
        ws["A1"].font = Font(bold=True, size=14)
        ws["A8"].font = Font(bold=True)
        for title, header, data in [
            ("Mauzo", ["Tarehe", "Bidhaa", "Idadi", "Jumla", "Faida"], [tuple(r) for r in sales]),
            ("Matumizi", ["Tarehe", "Kiasi", "Maelezo"], [tuple(r) for r in exps]),
            ("Madeni", ["Tarehe", "Mteja", "Kiasi", "Kilicholipwa", "Maelezo"], [tuple(r) for r in debts]),
            ("Stoo", ["Bidhaa", "Bei ya kununua", "Bei ya kuuza", "Stoo"], [tuple(r) for r in stock]),
        ]:
            sh = wb.create_sheet(title)
            sh.append(header)
            for c in sh[1]:
                c.font = Font(bold=True)
            for row in data:
                sh.append(list(row))
            for col in sh.columns:
                sh.column_dimensions[col[0].column_letter].width = 18
        ws.column_dimensions["A"].width = 26
        ws.column_dimensions["B"].width = 18
        wb.save(path)
        with open(path, "rb") as f:
            await update.message.reply_document(f, filename=f"ripoti_{period}_{stamp}.xlsx",
                                                caption=f"📑 Ripoti ya {period}. Faida halisi: {money(tot_profit - tot_exp)}")
        os.remove(path)
    except ImportError:
        buf = io.StringIO()
        w = csv.writer(buf)
        w.writerow(["Tarehe", "Bidhaa", "Idadi", "Jumla", "Faida"])
        w.writerows([tuple(r) for r in sales])
        data = io.BytesIO(buf.getvalue().encode("utf-8-sig"))
        data.name = f"mauzo_{period}_{stamp}.csv"
        await update.message.reply_document(
            data, caption="📑 Excel haijasakinishwa, hii ni CSV (inafunguka kwenye Excel).\nKupata Excel kamili: pip install openpyxl"
        )


# ====== 7b. PICHA ZA BIDHAA ======
PHOTO_WAIT_SECONDS = 600


def _can_edit_product(conn, uid, pid):
    return conn.execute(
        "SELECT * FROM products WHERE id=? AND active=1 AND (owner_id=? OR (owner_id IS NULL AND ?))",
        (pid, uid, 1 if is_admin(uid) else 0),
    ).fetchone()


@require_active
async def picha(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    try:
        pid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text(
            "Tumia: /picha <id ya bidhaa>, kisha tuma picha.\nMfano: /picha 2\n"
            "Au tuma picha moja kwa moja pamoja na maelezo (caption):\n/weka_bidhaa Juice 1000 3000 100"
        )
        return
    with closing(db()) as conn:
        p = _can_edit_product(conn, uid, pid)
    if not p:
        await update.message.reply_text("❌ Huna bidhaa yenye ID hiyo. Angalia /bidhaa_zangu")
        return
    context.user_data["await_photo"] = (pid, time.time())
    await update.message.reply_text(f"📷 Tuma picha ya {p['name']} sasa (dakika 10).")


async def photo_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    msg = update.message
    if not is_registered(uid):
        return
    ok, lock = check_access(uid)
    if not ok:
        await msg.reply_text(lock)
        return
    file_id = msg.photo[-1].file_id            # picha kubwa zaidi
    caption = (msg.caption or "").strip()
    m = re.match(r"^/weka_bidhaa(?:@\w+)?(?:\s+(.*))?$", caption, re.S)
    if m:                                      # picha + /weka_bidhaa kwenye caption
        context.args = (m.group(1) or "").split()
        context.user_data["_photo_for_new"] = file_id
        await weka_bidhaa(update, context)
        context.user_data.pop("_photo_for_new", None)
        return
    wait = context.user_data.get("await_photo")
    if wait and time.time() - wait[1] <= PHOTO_WAIT_SECONDS:
        pid = wait[0]
        context.user_data.pop("await_photo", None)
        with closing(db()) as conn, conn:
            p = _can_edit_product(conn, uid, pid)
            if not p:
                await msg.reply_text("❌ Bidhaa haipo tena.")
                return
            conn.execute("UPDATE products SET photo_id=? WHERE id=?", (file_id, pid))
        await msg.reply_text(f"✅ Picha ya {p['name']} imehifadhiwa. 📷")
        return
    await msg.reply_text(
        "📷 Kuweka picha ya bidhaa: /picha <id>, kisha tuma picha.\n"
        "Au tuma picha na caption: /weka_bidhaa Juice 1000 3000 100"
    )


@require_active
async def ondoa_picha(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    try:
        pid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("Tumia: /ondoa_picha <id>")
        return
    with closing(db()) as conn, conn:
        p = _can_edit_product(conn, uid, pid)
        if not p:
            await update.message.reply_text("❌ Huna bidhaa yenye ID hiyo.")
            return
        conn.execute("UPDATE products SET photo_id=NULL WHERE id=?", (pid,))
    await update.message.reply_text("🗑️ Picha imeondolewa.")


@require_active
async def tazama(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    try:
        pid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("Tumia: /tazama <id ya bidhaa>")
        return
    with closing(db()) as conn:
        p = conn.execute(
            "SELECT * FROM products WHERE id=? AND active=1 AND (owner_id=? OR owner_id IS NULL)", (pid, uid)
        ).fetchone()
    if not p:
        await update.message.reply_text("❌ Bidhaa haipo.")
        return
    text = f"{p['name']}\nBei: {money(p['price'])} | Stoo: {p['stock']}"
    if p["owner_id"] == uid:
        text += f"\nKununua: {money(p['cost'])} | Faida/pc: {money(p['price'] - p['cost'])}"
    if p["photo_id"]:
        try:
            await update.message.reply_photo(photo=p["photo_id"], caption=text)
            return
        except Exception:
            text += "\n(Picha haikupakia, itume tena kwa /picha)"
    else:
        text += f"\n📷 Hakuna picha. Weka kwa /picha {pid}"
    await update.message.reply_text(text)


@require_active
async def katalogi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Katalogi ya kutuma kwa wateja: picha + jina + bei (bila bei ya kununua)."""
    from telegram import InputMediaPhoto
    uid = update.effective_user.id
    with closing(db()) as conn:
        rows = conn.execute(
            "SELECT name, price, stock, photo_id FROM products "
            "WHERE owner_id=? AND active=1 AND photo_id IS NOT NULL ORDER BY id LIMIT 30", (uid,)
        ).fetchall()
    if not rows:
        await update.message.reply_text("Huna bidhaa zenye picha. Weka kwa /picha <id>")
        return
    await update.message.reply_text(
        f"🖼️ Katalogi yako ({len(rows)} bidhaa). Unaweza kuisambaza (forward) kwa wateja wako."
    )
    for i in range(0, len(rows), 10):         # Telegram inaruhusu picha 10 kwa kikundi
        chunk = rows[i:i + 10]
        media = [InputMediaPhoto(r["photo_id"], caption=f"{r['name']}\n💰 {money(r['price'])}"
                                 + ("" if r["stock"] > 0 else "\n(Imeisha)")) for r in chunk]
        try:
            await context.bot.send_media_group(update.effective_chat.id, media=media)
        except Exception:
            await update.message.reply_text("⚠️ Baadhi ya picha hazikupakia. Zitume tena kwa /picha <id>.")


# ====== 8. MSAADA ======
async def msaada(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    text = (
        "❓ MWONGOZO WA HARAKA\n\n"
        "1️⃣ Weka bidhaa: /weka_bidhaa Sukari 2500 3000 20\n   📷 Weka picha: tuma picha hapo hapo, au /picha <id>\n"
        "   (jina, bei ya kununua, bei ya kuuza, stoo)\n"
        "   🖼️ Katalogi ya wateja: /katalogi\n"
        "2️⃣ Uza: bonyeza 🛒 Uza, chagua bidhaa, chagua idadi. Umekosea? ↩️ Tengua.\n"
        "3️⃣ Anauziwa kwa mkopo? 🛒 Uza → 📒 Kwa deni. Angalia 📒 Madeni.\n"
        "4️⃣ Gharama: /matumizi 2000 usafiri\n"
        "5️⃣ Angalia biashara: 📊 Leo, 💹 Faida, /ripoti_excel\n"
        "6️⃣ Stoo ikiisha: /jaza_stoo <id> <idadi>\n"
        "7️⃣ Ripoti ya kila usiku inakuja saa 2 usiku yenyewe (/ripoti_usiku zima kuzima)\n"
        "8️⃣ Lipia mwezi: 💳 Lipia. Hali ya account: 📅 Hali\n"
        "9️⃣ Alika marafiki: 🔗 Rufaa. Anapolipia, unapata bonasi.\n"
        "🔟 🎬 Soko: tazama bidhaa za wauzaji wengine. 📣 Chapisha: tangaza video/picha ya bidhaa yako."
    )
    hint = onboarding_hint(uid) if is_registered(uid) else "👉 Anza kwa kujisajili: /jisajili"
    if hint:
        text += "\n\n" + hint
    await update.message.reply_text(text, reply_markup=menu_for(uid))


# ====== 9. BACKUP YA DATABASE (admin) ======
async def send_backup(context, to=None):
    ids = [to] if to else ADMIN_IDS
    tmp = tempfile.mktemp(suffix=".db")
    src = sqlite3.connect(DB_FILE)
    dst = sqlite3.connect(tmp)
    src.backup(dst)
    dst.close()
    src.close()
    stamp = datetime.now().strftime("%Y-%m-%d")
    for a in ids:
        try:
            with open(tmp, "rb") as f:
                await context.bot.send_document(a, document=f, filename=f"mauzo_{stamp}.db",
                                                caption="💾 Nakala ya database. Ihifadhi mahali salama.")
        except Exception:
            pass
    os.remove(tmp)


async def backup(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if is_admin(update.effective_user.id):
        await send_backup(context, update.effective_user.id)


# ====== KUPIMA KASI (admin) ======
async def ping(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Inaonyesha kinachochelewesha: mtandao, database, au kuhesabu password."""
    if not is_admin(update.effective_user.id):
        return
    lag = (datetime.now(timezone.utc) - update.message.date).total_seconds() * 1000
    t = time.perf_counter()
    for _ in range(20):
        with closing(db()) as conn:
            conn.execute("SELECT COUNT(*) FROM users").fetchone()
            conn.execute("SELECT COUNT(*) FROM sales").fetchone()
    db_ms = (time.perf_counter() - t) * 1000 / 20
    t = time.perf_counter()
    await asyncio.to_thread(hash_password, "x")
    hash_ms = (time.perf_counter() - t) * 1000
    t = time.perf_counter()
    m = await update.message.reply_text("🏓 Napima...")
    send_ms = (time.perf_counter() - t) * 1000
    await m.edit_text(
        "🏓 KASI YA BOT\n"
        f"• Ujumbe ulifika baada ya: {lag:,.0f} ms\n"
        f"• Kutuma jibu kwa Telegram: {send_ms:,.0f} ms\n"
        f"• Database (maswali 2): {db_ms:,.1f} ms\n"
        f"• Kuhesabu password: {hash_ms:,.0f} ms (haizuii bot)\n\n"
        "Kama nambari mbili za kwanza ni kubwa (>800 ms), tatizo ni mtandao au simu. "
        "Database kubwa (>50 ms) ni tatizo la diski."
    )


# ====== 10. MATANGAZO (admin) ======
def _audience(kind):
    with closing(db()) as conn:
        rows = conn.execute("SELECT * FROM users WHERE password_hash IS NOT NULL").fetchall()
    out = []
    for r in rows:
        active, _, k = sub_state(r)
        if kind == "hai" and not active:
            continue
        if kind == "waliofungwa" and (active or k == "admin"):
            continue
        out.append(r["user_id"])
    return out


async def tangaza(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    m = re.match(r"/tangaza(?:@\w+)?\s*(wote|hai|waliofungwa)?\s*(.*)", update.message.text, re.S | re.I)
    audience = (m.group(1) or "wote").lower() if m else "wote"
    text = (m.group(2) if m else "").strip()
    if not text:
        await update.message.reply_text(
            "Tumia: /tangaza [wote|hai|waliofungwa] <ujumbe>\n"
            "Mfano: /tangaza waliofungwa Lipia sasa upate huduma tena: /lipia\n"
            "• wote = waliosajiliwa wote (chaguo-msingi)\n• hai = wenye account hai\n• waliofungwa = ofa/malipo yameisha"
        )
        return
    context.user_data["bc"] = (audience, text)
    n = len(_audience(audience))
    kb = Kb([[Btn(f"✅ Tuma kwa {n}", callback_data="bc_ok"), Btn("❌ Ghairi", callback_data="bc_no")]])
    await update.message.reply_text(f"📢 Hakiki ujumbe ({audience}, watu {n}):\n\n{text}", reply_markup=kb)


async def bc_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not is_admin(q.from_user.id):
        await q.answer("Huna ruhusa.", show_alert=True)
        return
    await q.answer()
    pending = context.user_data.pop("bc", None)
    if q.data == "bc_no" or not pending:
        await q.edit_message_text("Umeghairi. Hakuna ujumbe uliotumwa." if q.data == "bc_no" else "Hakuna ujumbe unaosubiri.")
        return
    audience, text = pending
    ids = _audience(audience)
    await q.edit_message_text(f"⏳ Natuma kwa watu {len(ids)}...")
    ok = fail = 0
    for uid in ids:
        try:
            await context.bot.send_message(uid, f"📢 {text}")
            ok += 1
        except Exception:
            fail += 1
        await asyncio.sleep(0.05)          # Telegram inazuia kutuma haraka sana
    await q.message.reply_text(f"✅ Imetumwa: {ok} | Imeshindwa: {fail} (waliozuia bot)")


# ====== KAZI ZA KILA SAA: RIPOTI YA USIKU + BACKUP ======
async def hourly(context: ContextTypes.DEFAULT_TYPE):
    now_dt = datetime.now()
    today = now_dt.strftime("%Y-%m-%d")
    if now_dt.hour >= BACKUP_HOUR and get_setting("last_backup") != today:
        await send_backup(context)
        set_setting("last_backup", today)
    if now_dt.hour < REPORT_HOUR:
        return
    with closing(db()) as conn:
        users = conn.execute(
            "SELECT * FROM users WHERE password_hash IS NOT NULL AND COALESCE(report_on,1)=1 "
            "AND COALESCE(last_report,'')!=?", (today,)
        ).fetchall()
    for u in users:
        await asyncio.sleep(0)          # usizuie amri za watumiaji wengine
        active, _, _ = sub_state(u)
        if not active:
            continue
        text, has = build_summary(u["user_id"])
        if has:
            try:
                await context.bot.send_message(u["user_id"], "🌙 " + text + "\n\n(Zima: /ripoti_usiku zima)")
            except Exception:
                pass
            await asyncio.sleep(0.05)
        with closing(db()) as conn, conn:
            conn.execute("UPDATE users SET last_report=? WHERE user_id=?", (today, u["user_id"]))


# ====== USAJILI WA HANDLERS ======
def register_plus(app: Application):
    register_feed(app)         # lazima iwe ya kwanza: inapokea picha/video wakati wa /chapisha
    register_v2(app)
    app.add_handler(ConversationHandler(
        entry_points=[CallbackQueryHandler(custom_start, pattern=r"^u[od]_\d+$")],
        states={SELL_QTY: [MessageHandler(filters.TEXT & ~filters.COMMAND, custom_qty)]},
        fallbacks=[CommandHandler("ghairi", ghairi)],
    ))
    app.add_handler(CallbackQueryHandler(pick_product, pattern=r"^up_\d+$"))
    app.add_handler(CallbackQueryHandler(quick_qty, pattern=r"^uq_\d+_\d+$"))
    app.add_handler(CallbackQueryHandler(back_to_products, pattern=r"^ub$"))
    app.add_handler(CallbackQueryHandler(undo_button, pattern=r"^(tg_\d+|tgx)$"))
    app.add_handler(CallbackQueryHandler(debt_paid_button, pattern=r"^dp_\d+$"))
    app.add_handler(CallbackQueryHandler(bc_button, pattern=r"^bc_(ok|no)$"))
    for name, fn in [
        ("tengua", tengua), ("leo", leo), ("ripoti_usiku", ripoti_usiku),
        ("deni", deni), ("madeni", madeni), ("lipa_deni", lipa_deni),
        ("matumizi", matumizi), ("futa_matumizi", futa_matumizi),
        ("futa_bidhaa", futa_bidhaa), ("hariri_jina", hariri_jina),
        ("ripoti_excel", ripoti_excel), ("msaada", msaada),
        ("backup", backup), ("tangaza", tangaza), ("ping", ping),
        ("picha", picha), ("ondoa_picha", ondoa_picha), ("tazama", tazama), ("katalogi", katalogi),
    ]:
        app.add_handler(CommandHandler(name, fn))
    app.add_handler(MessageHandler(filters.PHOTO, photo_handler))
    # Vitufe vya menyu
    for text, fn in [
        (BTN_SELL, uza_menu), (BTN_TODAY, leo), (BTN_DEBTS, madeni),
        (BTN_EXPENSES, matumizi), (BTN_HELP, msaada),
    ]:
        app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(text)}$"), fn))
    if app.job_queue:      # inahitaji: pip install "python-telegram-bot[job-queue]"
        app.job_queue.run_repeating(hourly, interval=3600, first=120)


# ####################################################################
# 🎬 SOKO: video/picha za bidhaa zinazotelezeshwa kama TikTok
# ####################################################################
FEED_MAX_POSTS_PER_DAY = 5          # matangazo kwa mtu kwa saa 24 (kuzuia spam)
FEED_MAX_VIDEO_SECONDS = 90
FEED_REPORTS_TO_HIDE = 3            # ripoti ngapi ili tangazo lifichwe kiotomatiki
FEED_NOTIFY_ADMIN = os.environ.get("SOKO_NOTIFY", "1") != "0"   # SOKO_NOTIFY=0 kuzima taarifa kwa admin
POST_MEDIA, POST_TEXT = 40, 41
SOKO_RULES = (
    "📜 SHERIA ZA SOKO\n"
    "• Tangaza bidhaa au huduma halali tu. Hakuna maudhui ya ngono, vurugu, silaha, dawa za kulevya au utapeli.\n"
    "• Picha/video ziwe zako, usitumie za watu wengine bila ruhusa.\n"
    "• Wateja watawasiliana nawe kwa username yako ya Telegram (ukikosa, wataona namba yako ya simu).\n"
    f"• Tangazo likiripotiwa mara {FEED_REPORTS_TO_HIDE} linafichwa, na admin anaweza kuliondoa.\n"
)


def _ago(ts):
    secs = (datetime.now() - datetime.strptime(ts, FMT)).total_seconds()
    if secs < 3600:
        return f"dakika {max(1, int(secs // 60))} zilizopita"
    if secs < 86400:
        return f"saa {int(secs // 3600)} zilizopita"
    return f"siku {int(secs // 86400)} zilizopita"


def _post_row(pid):
    with closing(db()) as conn:
        return conn.execute(
            "SELECT p.*, u.name seller_name, u.username seller_username FROM posts p "
            "JOIN users u ON u.user_id=p.user_id WHERE p.id=?", (pid,)
        ).fetchone()


def _post_text(p):
    return f"{p['caption']}\n\n👤 {p['seller_name']} · 🕒 {_ago(p['ts'])}\n❤️ {p['likes']} · 👁 {p['views']}"[:1024]


def _feed_kb(p, uid):
    with closing(db()) as conn:
        liked = conn.execute("SELECT 1 FROM post_likes WHERE post_id=? AND user_id=?", (p["id"], uid)).fetchone()
    uname = p["seller_username"]
    if uname and re.fullmatch(r"[A-Za-z0-9_]{4,32}", uname):
        contact = Btn("📞 Wasiliana", url=f"https://t.me/{uname}")
    else:
        contact = Btn("📞 Wasiliana", callback_data=f"fc_{p['id']}")
    return Kb([
        [Btn(f"{'❤️' if liked else '🤍'} {p['likes']}", callback_data=f"fl_{p['id']}"),
         Btn("⏭ Inayofuata", callback_data="fn")],
        [contact, Btn("🔗 Shiriki", callback_data=f"fs_{p['id']}")],
        [Btn("🛍️ Agiza", callback_data=f"fo_{p['id']}"), Btn("🚩 Ripoti", callback_data=f"fr_{p['id']}")],
    ])


def _media_for(p):
    text = _post_text(p)
    if p["kind"] == "video":
        return InputMediaVideo(p["file_id"], caption=text, supports_streaming=True)
    return InputMediaPhoto(p["file_id"], caption=text)


def mark_seen(pid, uid):
    with closing(db()) as conn, conn:
        cur = conn.execute("INSERT OR IGNORE INTO post_seen(user_id,post_id) VALUES(?,?)", (uid, pid))
        if cur.rowcount:
            conn.execute("UPDATE posts SET views=views+1 WHERE id=?", (pid,))


def pick_post(uid):
    """Tangazo lisilokuwa limeonekana: wapya na wenye likes nyingi wanapewa nafasi kubwa."""
    def query():
        with closing(db()) as conn:
            return conn.execute(
                "SELECT id, likes, ts FROM posts WHERE active=1 AND user_id!=? "
                "AND id NOT IN (SELECT post_id FROM post_seen WHERE user_id=?) ORDER BY id DESC LIMIT 60",
                (uid, uid),
            ).fetchall()
    rows = query()
    if not rows:                                   # amemaliza yote: anza mzunguko mpya
        with closing(db()) as conn, conn:
            conn.execute("DELETE FROM post_seen WHERE user_id=?", (uid,))
        rows = query()
    if not rows:
        return None
    now_dt = datetime.now()

    def score(r):
        age_days = (now_dt - datetime.strptime(r["ts"], FMT)).total_seconds() / 86400
        return r["likes"] * 3 + 10 / (1 + age_days) + random.random() * 6
    return max(rows, key=score)["id"]


async def _send_post(msg, pid, uid, ud=None):
    p = _post_row(pid)
    if not p or not p["active"]:
        await msg.reply_text("Tangazo hili halipatikani tena. Tazama mengine: /soko")
        return False
    mark_seen(pid, uid)
    if ud is not None:
        ud["last_pid"], ud["last_ts"] = pid, time.time()
    p = _post_row(pid)
    kb, text = _feed_kb(p, uid), _post_text(p)
    if p["kind"] == "video":
        await msg.reply_video(video=p["file_id"], caption=text, reply_markup=kb, supports_streaming=True)
    else:
        await msg.reply_photo(photo=p["file_id"], caption=text, reply_markup=kb)
    return True


async def soko(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    pid = pick_post(uid)
    if not pid:
        await update.message.reply_text("🎬 Soko bado halina matangazo. Kuwa wa kwanza kuchapisha: /chapisha")
        return
    await _send_post(update.message, pid, uid, context.user_data)


async def feed_next(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    uid = q.from_user.id
    pid = pick_post(uid)
    if not pid:
        await q.answer("Hakuna matangazo mengine kwa sasa.", show_alert=True)
        return
    toast = None
    last_pid, last_ts = context.user_data.get("last_pid"), context.user_data.get("last_ts", 0)
    if last_pid and time.time() - last_ts >= MIN_WATCH_SECONDS:      # alikaa kwenye video kwa muda wa kutosha
        got, total = award_view_point(uid, last_pid)
        if got:
            toast = f"⭐ +{POINTS_PER_VIDEO} pointi (jumla {total})"
    await q.answer(toast)
    mark_seen(pid, uid)
    context.user_data["last_pid"], context.user_data["last_ts"] = pid, time.time()
    p = _post_row(pid)
    try:
        await q.edit_message_media(media=_media_for(p), reply_markup=_feed_kb(p, uid))
    except Exception:
        await _send_post(q.message, pid, uid)
    if not is_registered(uid):                   # mwaliko mpole kwa wanaotazama tu
        with closing(db()) as conn:
            n = conn.execute("SELECT COUNT(*) n FROM post_seen WHERE user_id=?", (uid,)).fetchone()["n"]
        if n and n % 5 == 0:
            await q.message.reply_text(
                f"✨ Unapenda Soko? Jisajili upate siku {TRIAL_DAYS} BURE na pointi kila unapotazama video "
                f"({POINTS_PER_DAY} pointi = siku 1 bure). Pia utaweza kuuza, kufuatilia faida na kuchapisha: /jisajili"
            )


async def feed_like(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    uid = q.from_user.id
    pid = int(q.data.split("_")[1])
    with closing(db()) as conn, conn:
        exists = conn.execute("SELECT 1 FROM post_likes WHERE post_id=? AND user_id=?", (pid, uid)).fetchone()
        if exists:
            conn.execute("DELETE FROM post_likes WHERE post_id=? AND user_id=?", (pid, uid))
        else:
            conn.execute("INSERT INTO post_likes(post_id,user_id) VALUES(?,?)", (pid, uid))
        conn.execute(
            "UPDATE posts SET likes=(SELECT COUNT(*) FROM post_likes WHERE post_id=?) WHERE id=?", (pid, pid)
        )
    p = _post_row(pid)
    if not p:
        await q.answer("Tangazo halipo.", show_alert=True)
        return
    await q.answer("❤️" if not exists else "💔")
    try:
        await q.edit_message_caption(caption=_post_text(p), reply_markup=_feed_kb(p, uid))
    except Exception:
        pass
    if not exists and p["likes"] in (10, 50, 100, 500, 1000):     # pongezi kwa muuzaji
        try:
            await context.bot.send_message(p["user_id"], f"🎉 Tangazo lako #{pid} limefikisha likes {p['likes']}!")
        except Exception:
            pass


async def feed_share(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    pid = int(q.data.split("_")[1])
    await q.answer()
    link = f"https://t.me/{BOT_USERNAME}?start=p{pid}r{q.from_user.id}"
    await q.message.reply_text(
        f"🔗 Tuma link hii kwa marafiki:\n{link}\n\n"
        f"Ukiwaleta watu wapya wakajisajili na kulipia, unapata bonasi ya {money(REFERRAL_BONUS)}."
    )


async def feed_contact(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    pid = int(q.data.split("_")[1])
    p = _post_row(pid)
    with closing(db()) as conn:
        u = conn.execute("SELECT phone FROM users WHERE user_id=?", (p["user_id"],)).fetchone() if p else None
    if u and u["phone"]:
        await q.answer(f"📞 {p['seller_name']}: +{u['phone']}", show_alert=True)
    else:
        await q.answer("Muuzaji hana njia ya mawasiliano.", show_alert=True)


async def feed_report(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    pid = int(q.data.split("_")[1])
    with closing(db()) as conn, conn:
        conn.execute("INSERT OR IGNORE INTO post_reports(post_id,user_id,ts) VALUES(?,?,?)", (pid, q.from_user.id, now()))
        n = conn.execute("SELECT COUNT(*) n FROM post_reports WHERE post_id=?", (pid,)).fetchone()["n"]
        hide = n >= FEED_REPORTS_TO_HIDE
        if hide:
            conn.execute("UPDATE posts SET active=0 WHERE id=?", (pid,))
    await q.answer("🚩 Asante, tumepokea ripoti yako.", show_alert=True)
    if hide:
        for a in ADMIN_IDS:
            try:
                await context.bot.send_message(
                    a, f"🚩 Tangazo #{pid} limefichwa kiotomatiki baada ya ripoti {n}.\n"
                       f"Kuliondoa kabisa: /soko_ondoa {pid}\nKulirudisha: /soko_rudisha {pid}"
                )
            except Exception:
                pass


# ---- kuchapisha ----
@require_active
async def chapisha_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    if not is_registered(uid):
        await update.message.reply_text(NOT_REG_MSG)
        return ConversationHandler.END
    with closing(db()) as conn:
        n = conn.execute(
            "SELECT COUNT(*) n FROM posts WHERE user_id=? AND ts>=?", (uid, add_days(now(), -1))
        ).fetchone()["n"]
    if n >= FEED_MAX_POSTS_PER_DAY and not is_admin(uid):
        await update.message.reply_text(f"⏳ Umefikia kikomo cha matangazo {FEED_MAX_POSTS_PER_DAY} kwa siku. Jaribu kesho.")
        return ConversationHandler.END
    await update.message.reply_text(
        SOKO_RULES + f"\n📹 Tuma video fupi (hadi sekunde {FEED_MAX_VIDEO_SECONDS}) au picha ya bidhaa yako.\nKughairi: /ghairi"
    )
    return POST_MEDIA


async def chapisha_media(update: Update, context: ContextTypes.DEFAULT_TYPE):
    m = update.message
    if m.video:
        if m.video.duration and m.video.duration > FEED_MAX_VIDEO_SECONDS:
            await m.reply_text(f"❌ Video ni ndefu mno. Tuma ya hadi sekunde {FEED_MAX_VIDEO_SECONDS}.")
            return POST_MEDIA
        context.user_data["post"] = {"kind": "video", "fid": m.video.file_id}
    elif m.photo:
        context.user_data["post"] = {"kind": "photo", "fid": m.photo[-1].file_id}
    else:
        await m.reply_text("📹 Tuma video au picha, tafadhali.")
        return POST_MEDIA
    cap = (m.caption or "").strip()
    if len(cap) >= 10:                               # maelezo yametumwa pamoja na media
        return await _publish(update, context, cap[:300])
    await m.reply_text("✍️ Sasa andika maelezo: jina la bidhaa, bei na mahali ulipo (herufi 10 hadi 300).")
    return POST_TEXT


async def chapisha_wrong(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.message.text in MENU_TEXTS:
        return await ghairi(update, context)
    await update.message.reply_text("📹 Tuma video au picha ya bidhaa yako. Kughairi: /ghairi")
    return POST_MEDIA


async def chapisha_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = update.message.text.strip()
    if text in MENU_TEXTS:
        return await ghairi(update, context)
    if len(text) < 10:
        await update.message.reply_text("❌ Maelezo ni mafupi mno (angalau herufi 10).")
        return POST_TEXT
    return await _publish(update, context, text[:300])


async def _publish(update, context, caption):
    d = context.user_data.pop("post", None)
    user = update.effective_user
    if not d:
        return ConversationHandler.END
    with closing(db()) as conn, conn:
        pid = conn.execute(
            "INSERT INTO posts(user_id,kind,file_id,caption,ts) VALUES(?,?,?,?,?)",
            (user.id, d["kind"], d["fid"], caption, now()),
        ).lastrowid
    link = f"https://t.me/{BOT_USERNAME}?start=p{pid}r{user.id}"
    await update.message.reply_text(
        f"✅ Tangazo limechapishwa (#{pid})! Linaonekana kwenye 🎬 Soko.\n\n"
        f"🔗 Link ya kulishiriki (WhatsApp, TikTok, status):\n{link}\n\n"
        f"Kila mtu atakayejiunga kupitia link hii na kulipia, unapata bonasi ya {money(REFERRAL_BONUS)}.",
        reply_markup=menu_for(user.id),
    )
    if FEED_NOTIFY_ADMIN:
        kb = Kb([[Btn("🗑️ Ondoa", callback_data=f"pa_{pid}")]])
        for a in ADMIN_IDS:
            if a == user.id:
                continue
            try:
                text = f"🆕 Tangazo #{pid} kutoka {user.full_name}\n{caption}"
                if d["kind"] == "video":
                    await context.bot.send_video(a, d["fid"], caption=text, reply_markup=kb)
                else:
                    await context.bot.send_photo(a, d["fid"], caption=text, reply_markup=kb)
            except Exception:
                pass
    return ConversationHandler.END


async def admin_remove_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not is_admin(q.from_user.id):
        await q.answer("Huna ruhusa.", show_alert=True)
        return
    pid = int(q.data.split("_")[1])
    with closing(db()) as conn, conn:
        conn.execute("UPDATE posts SET active=0 WHERE id=?", (pid,))
    await q.answer("🗑️ Limeondolewa")
    try:
        await q.edit_message_caption(caption=f"🗑️ Tangazo #{pid} limeondolewa.")
    except Exception:
        pass


# ---- matangazo yangu, wauzaji maarufu, usimamizi ----
def _my_posts_view(uid):
    with closing(db()) as conn:
        rows = conn.execute(
            "SELECT * FROM posts WHERE user_id=? AND active=1 ORDER BY id DESC LIMIT 10", (uid,)
        ).fetchall()
    if not rows:
        return "Huna matangazo. Chapisha la kwanza: /chapisha", None
    out = ["📣 MATANGAZO YAKO"]
    for r in rows:
        out.append(f"#{r['id']} {'🎥' if r['kind'] == 'video' else '🖼️'} ❤️{r['likes']} 👁{r['views']} | {r['caption'][:50]}")
    kb = Kb([[Btn(f"🗑️ Futa #{r['id']}", callback_data=f"pd_{r['id']}")] for r in rows])
    return "\n".join(out), kb


async def posti_zangu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    text, kb = _my_posts_view(update.effective_user.id)
    await update.message.reply_text(text, reply_markup=kb)


async def my_post_delete(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    pid = int(q.data.split("_")[1])
    with closing(db()) as conn, conn:
        cur = conn.execute(
            "UPDATE posts SET active=0 WHERE id=? AND (user_id=? OR ?)", (pid, q.from_user.id, 1 if is_admin(q.from_user.id) else 0)
        )
    await q.answer("🗑️ Imefutwa" if cur.rowcount else "Huwezi kufuta tangazo hili.", show_alert=not cur.rowcount)
    text, kb = _my_posts_view(q.from_user.id)
    try:
        await q.edit_message_text(text, reply_markup=kb)
    except Exception:
        pass


async def maarufu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    with closing(db()) as conn:
        rows = conn.execute(
            "SELECT u.name, SUM(p.likes) l, SUM(p.views) v, COUNT(*) n FROM posts p "
            "JOIN users u ON u.user_id=p.user_id WHERE p.active=1 GROUP BY p.user_id "
            "ORDER BY l DESC, v DESC LIMIT 10"
        ).fetchall()
    if not rows:
        await update.message.reply_text("Bado hakuna wauzaji kwenye Soko. Kuwa wa kwanza: /chapisha")
        return
    medals = ["🥇", "🥈", "🥉"]
    out = ["🏆 WAUZAJI MAARUFU"]
    for i, r in enumerate(rows):
        out.append(f"{medals[i] if i < 3 else str(i + 1) + '.'} {r['name']} | ❤️{r['l']} 👁{r['v']} | matangazo {r['n']}")
    await update.message.reply_text("\n".join(out))


async def soko_ondoa(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    try:
        pid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("Tumia: /soko_ondoa <id ya tangazo>")
        return
    with closing(db()) as conn, conn:
        p = conn.execute("SELECT user_id FROM posts WHERE id=?", (pid,)).fetchone()
        conn.execute("UPDATE posts SET active=0 WHERE id=?", (pid,))
    await update.message.reply_text(f"🗑️ Tangazo #{pid} limeondolewa." if p else "❌ Tangazo halipo.")
    if p:
        try:
            await context.bot.send_message(p["user_id"], f"⚠️ Tangazo lako #{pid} limeondolewa na admin kwa kukiuka sheria za Soko.")
        except Exception:
            pass


async def soko_rudisha(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    try:
        pid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("Tumia: /soko_rudisha <id ya tangazo>")
        return
    with closing(db()) as conn, conn:
        cur = conn.execute("UPDATE posts SET active=1 WHERE id=?", (pid,))
        conn.execute("DELETE FROM post_reports WHERE post_id=?", (pid,))
    await update.message.reply_text(f"✅ Tangazo #{pid} limerudishwa." if cur.rowcount else "❌ Tangazo halipo.")


async def soko_ripoti(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    with closing(db()) as conn:
        rows = conn.execute(
            "SELECT * FROM (SELECT p.id, p.active, p.caption, u.name, "
            "(SELECT COUNT(*) FROM post_reports r WHERE r.post_id=p.id) n FROM posts p "
            "JOIN users u ON u.user_id=p.user_id) WHERE n>0 ORDER BY n DESC LIMIT 15"
        ).fetchall()
    if not rows:
        await update.message.reply_text("🚩 Hakuna matangazo yaliyoripotiwa.")
        return
    out = ["🚩 MATANGAZO YALIYORIPOTIWA"]
    out += [f"#{r['id']} | ripoti {r['n']} | {'hai' if r['active'] else 'limefichwa'} | {r['name']} | {r['caption'][:40]}" for r in rows]
    out.append("\nKuondoa: /soko_ondoa <id>   Kurudisha: /soko_rudisha <id>")
    await update.message.reply_text("\n".join(out))


def register_feed(app: Application):
    app.add_handler(ConversationHandler(
        entry_points=[
            MessageHandler(filters.Regex(f"^{re.escape(BTN_POST)}$"), chapisha_start),
            CommandHandler("chapisha", chapisha_start),
        ],
        states={
            POST_MEDIA: [
                MessageHandler((filters.VIDEO | filters.PHOTO) & ~filters.COMMAND, chapisha_media),
                MessageHandler(filters.TEXT & ~filters.COMMAND, chapisha_wrong),
            ],
            POST_TEXT: [MessageHandler(filters.TEXT & ~filters.COMMAND, chapisha_text)],
        },
        fallbacks=[CommandHandler("ghairi", ghairi)],
    ))
    for pattern, fn in [
        (r"^fn$", feed_next), (r"^fl_\d+$", feed_like), (r"^fs_\d+$", feed_share),
        (r"^fc_\d+$", feed_contact), (r"^fr_\d+$", feed_report),
        (r"^pa_\d+$", admin_remove_button), (r"^pd_\d+$", my_post_delete),
    ]:
        app.add_handler(CallbackQueryHandler(fn, pattern=pattern))
    for name, fn in [
        ("soko", soko), ("posti_zangu", posti_zangu), ("maarufu", maarufu),
        ("soko_ondoa", soko_ondoa), ("soko_rudisha", soko_rudisha), ("soko_ripoti", soko_ripoti),
    ]:
        app.add_handler(CommandHandler(name, fn))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_FEED)}$"), soko))


# ####################################################################
# 🧩 VIPENGELE VYA ZIADA 2
#   password · msaada kwa admin · masharti · pointi · risiti · wateja ·
#   wasaidizi · maagizo ya Soko · kutafuta · takwimu · kufuta taarifa
# ####################################################################
POINTS_PER_VIDEO = 1
POINTS_DAILY_CAP = 10            # pointi za juu kwa siku (video 10)
POINTS_PER_DAY = 20              # pointi 20 = siku 1 ya usajili bure
POINTS_MONTHLY_DAYS_CAP = 10     # kikomo cha siku za bure kupitia pointi kwa siku 30
MIN_WATCH_SECONDS = 4            # video inahesabiwa akikaa angalau sekunde hizi
MAX_STAFF = 3
ORDERS_PER_DAY = 5
TICKETS_PER_DAY = 5
TERMS_TEXT = (
    "📜 MASHARTI NA FARAGHA\n"
    "1. Bot hii inakusaidia kufuatilia biashara yako: bidhaa, mauzo, madeni, matumizi na matangazo.\n"
    "2. Tunahifadhi: jina na username yako ya Telegram, namba yako ya simu, password (imefichwa, "
    "hakuna anayeweza kuisoma) na data ya biashara unayoandika.\n"
    "3. Admin anaweza kuona taarifa za akaunti yako ili kukuhudumia na kutatua matatizo.\n"
    "4. Username au namba yako ya simu inaweza kuonekana kwa wateja unapochapisha tangazo Sokoni.\n"
    "5. Huwezi kuchapisha maudhui haramu (angalia Sheria za Soko). Akaunti inaweza kufungwa ukikiuka.\n"
    f"6. Usajili ni {SUB_PRICE:,} TZS kwa siku {SUB_DAYS}. Siku {TRIAL_DAYS} za kwanza ni bure.\n"
    "7. Unaweza kuomba taarifa zako binafsi zifutwe kupitia 💬 Admin.\n"
)


async def _del_msg(update):
    try:
        await update.message.delete()
    except Exception:
        pass


# ---------------- masharti ----------------
async def terms_accept(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    if q.data == "tm_no":
        await q.edit_message_text("Sawa. Bila kukubali masharti huwezi kujisajili. Ukibadili mawazo: /jisajili")
        return ConversationHandler.END
    with closing(db()) as conn, conn:
        conn.execute("UPDATE users SET terms_at=? WHERE user_id=?", (now(), q.from_user.id))
    await q.edit_message_text("✅ Umekubali masharti.")
    await q.message.reply_text("📝 Kujisajili\nTuma namba yako ya simu (mfano 0712345678).\nKughairi: /ghairi")
    return ASK_PHONE


async def masharti(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(TERMS_TEXT + "\n" + SOKO_RULES)


# ---------------- kubadili password ----------------
PW_OLD, PW_NEW, PW_NEW2 = 50, 51, 52


async def bp_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_registered(update.effective_user.id):
        await update.message.reply_text(NOT_REG_MSG)
        return ConversationHandler.END
    await update.message.reply_text("🔑 Andika password yako ya SASA. Ujumbe wako utafutwa kwa usalama.\nKughairi: /ghairi")
    return PW_OLD


async def bp_old(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid, pw = update.effective_user.id, update.message.text
    await _del_msg(update)
    ok, err = await asyncio.to_thread(check_password, uid, pw)
    if not ok:
        await context.bot.send_message(uid, err)
        return ConversationHandler.END if "imefungwa" in err else PW_OLD
    context.user_data["old_pw"] = pw
    await context.bot.send_message(uid, "✅ Sahihi. Sasa andika password MPYA (angalau herufi 6).")
    return PW_NEW


async def bp_new(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid, pw = update.effective_user.id, update.message.text
    await _del_msg(update)
    if len(pw) < 6:
        await context.bot.send_message(uid, "❌ Password fupi mno. Angalau herufi 6.")
        return PW_NEW
    if pw == context.user_data.get("old_pw"):
        await context.bot.send_message(uid, "❌ Password mpya lazima itofautiane na ya zamani.")
        return PW_NEW
    context.user_data["new_pw"] = pw
    await context.bot.send_message(uid, "🔁 Rudia password mpya ili kuthibitisha.")
    return PW_NEW2


async def bp_new2(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid, pw = update.effective_user.id, update.message.text
    await _del_msg(update)
    if pw != context.user_data.get("new_pw"):
        await context.bot.send_message(uid, "❌ Hazifanani. Andika password mpya tena.")
        return PW_NEW
    h, salt = await asyncio.to_thread(hash_password, pw)
    with closing(db()) as conn, conn:
        conn.execute("UPDATE users SET password_hash=?, salt=?, failed_logins=0 WHERE user_id=?", (h, salt, uid))
    context.user_data.clear()
    await context.bot.send_message(uid, "✅ Password yako imebadilishwa.", reply_markup=menu_for(uid))
    return ConversationHandler.END


# ---------------- msaada kwa admin (tiketi) ----------------
SP_TEXT, TK_REPLY = 60, 61


async def sp_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    with closing(db()) as conn:
        n = conn.execute("SELECT COUNT(*) n FROM tickets WHERE user_id=? AND ts>=?", (uid, add_days(now(), -1))).fetchone()["n"]
    if n >= TICKETS_PER_DAY and not is_admin(uid):
        await update.message.reply_text("⏳ Umetuma ujumbe mwingi leo. Subiri majibu au jaribu kesho.")
        return ConversationHandler.END
    await update.message.reply_text("💬 Andika ujumbe wako kwa admin (tatizo, swali au maoni).\nKughairi: /ghairi")
    return SP_TEXT


async def sp_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    text = update.message.text.strip()
    if text in MENU_TEXTS:
        return await ghairi(update, context)
    if len(text) < 5:
        await update.message.reply_text("❌ Ujumbe ni mfupi mno. Eleza kidogo zaidi.")
        return SP_TEXT
    text = text[:800]
    with closing(db()) as conn, conn:
        tid = conn.execute("INSERT INTO tickets(user_id,text,ts) VALUES(?,?,?)", (user.id, text, now())).lastrowid
        u = conn.execute("SELECT phone FROM users WHERE user_id=?", (user.id,)).fetchone()
    await update.message.reply_text(f"✅ Ujumbe wako umetumwa (#{tid}). Utajibiwa hapa hapa kwenye bot.", reply_markup=menu_for(user.id))
    kb = Kb([[Btn("↩️ Jibu", callback_data=f"tk_{tid}")]])
    for a in ADMIN_IDS:
        try:
            await context.bot.send_message(
                a, f"🎫 Tiketi #{tid}\nKutoka: {user.full_name} (@{user.username or '-'}) | ID {user.id} | simu {(u['phone'] if u else None) or '-'}\n\n{text}",
                reply_markup=kb,
            )
        except Exception:
            pass
    return ConversationHandler.END


async def tk_reply_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not is_admin(q.from_user.id):
        await q.answer("Huna ruhusa.", show_alert=True)
        return ConversationHandler.END
    tid = int(q.data.split("_")[1])
    with closing(db()) as conn:
        t = conn.execute("SELECT * FROM tickets WHERE id=?", (tid,)).fetchone()
    if not t or t["status"] != "open":
        await q.answer("Tiketi hii imeshajibiwa.", show_alert=True)
        return ConversationHandler.END
    context.user_data["reply_tid"] = tid
    await q.answer()
    await q.message.reply_text(f"✍️ Andika jibu kwa tiketi #{tid}.\nKughairi: /ghairi")
    return TK_REPLY


async def _send_ticket_reply(context, tid, text):
    with closing(db()) as conn, conn:
        t = conn.execute("SELECT * FROM tickets WHERE id=?", (tid,)).fetchone()
        if not t:
            return False, "❌ Tiketi haipo."
        conn.execute("UPDATE tickets SET status='answered', answer=?, answered_ts=? WHERE id=?", (text, now(), tid))
    try:
        await context.bot.send_message(
            t["user_id"], f"💬 Jibu kutoka kwa admin (tiketi #{tid}):\n\n{text}\n\nUkihitaji zaidi, bonyeza 💬 Admin."
        )
    except Exception:
        return True, f"⚠️ Jibu limehifadhiwa lakini mtumiaji amezuia bot (tiketi #{tid})."
    return True, f"✅ Jibu limetumwa (tiketi #{tid})."


async def tk_reply_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return ConversationHandler.END
    text = update.message.text.strip()
    if text in MENU_TEXTS:
        return await ghairi(update, context)
    tid = context.user_data.pop("reply_tid", None)
    if not tid:
        return ConversationHandler.END
    _, msg = await _send_ticket_reply(context, tid, text)
    await update.message.reply_text(msg)
    return ConversationHandler.END


async def jibu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    try:
        tid = int(context.args[0])
        text = " ".join(context.args[1:]).strip()
        assert text
    except (IndexError, ValueError, AssertionError):
        await update.message.reply_text("Tumia: /jibu <id ya tiketi> <jibu>")
        return
    _, msg = await _send_ticket_reply(context, tid, text)
    await update.message.reply_text(msg)


async def tiketi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    with closing(db()) as conn:
        rows = conn.execute(
            "SELECT t.*, u.name FROM tickets t LEFT JOIN users u ON u.user_id=t.user_id "
            "WHERE t.status='open' ORDER BY t.id LIMIT 10"
        ).fetchall()
    if not rows:
        await update.message.reply_text("🎫 Hakuna tiketi zinazosubiri. ✅")
        return
    for r in rows:
        await update.message.reply_text(
            f"🎫 #{r['id']} | {r['name']} ({r['user_id']}) | {r['ts'][:16]}\n\n{r['text']}",
            reply_markup=Kb([[Btn("↩️ Jibu", callback_data=f"tk_{r['id']}")]]),
        )


# ---------------- kufuta taarifa binafsi (admin) ----------------
async def futa_akaunti(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    try:
        uid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("Tumia: /futa_akaunti <id ya mtumiaji>")
        return
    with closing(db()) as conn:
        u = conn.execute("SELECT name, phone FROM users WHERE user_id=?", (uid,)).fetchone()
    if not u:
        await update.message.reply_text("❌ Mtumiaji hapatikani.")
        return
    kb = Kb([[Btn("🗑️ Ndiyo, futa", callback_data=f"fa_ok_{uid}"), Btn("❌ Hapana", callback_data="fa_no")]])
    await update.message.reply_text(
        f"Futa taarifa binafsi za {u['name']} (simu {u['phone'] or '-'})?\n"
        "Jina, username, simu, password, wateja wake na matangazo vitaondolewa. Takwimu za mauzo zinabaki bila utambulisho.",
        reply_markup=kb,
    )


async def futa_akaunti_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not is_admin(q.from_user.id):
        await q.answer("Huna ruhusa.", show_alert=True)
        return
    await q.answer()
    if q.data == "fa_no":
        await q.edit_message_text("Sawa, hakuna kilichofutwa.")
        return
    uid = int(q.data.split("_")[2])
    with closing(db()) as conn, conn:
        conn.execute(
            "UPDATE users SET name='(amefutwa)', username=NULL, phone=NULL, password_hash=NULL, salt=NULL, "
            "trial_until=NULL, paid_until=NULL, terms_at=NULL, shop_name=NULL WHERE user_id=?", (uid,)
        )
        conn.execute("UPDATE posts SET active=0 WHERE user_id=?", (uid,))
        conn.execute("DELETE FROM customers WHERE user_id=?", (uid,))
        conn.execute("DELETE FROM staff WHERE owner_id=? OR staff_id=?", (uid, uid))
        conn.execute("UPDATE tickets SET text='(imefutwa)', answer=NULL WHERE user_id=?", (uid,))
    await q.edit_message_text(f"🗑️ Taarifa binafsi za {uid} zimefutwa.")


# ---------------- pointi za kutazama ----------------
def award_view_point(uid, pid):
    """Inarudisha (imetolewa, jumla). Pointi 1 kwa video mpya (haijirudii), kikomo POINTS_DAILY_CAP kwa siku."""
    with closing(db()) as conn, conn:
        u = conn.execute("SELECT points, password_hash FROM users WHERE user_id=?", (uid,)).fetchone()
        if not u or not u["password_hash"]:
            return False, 0
        if conn.execute("SELECT 1 FROM view_rewards WHERE user_id=? AND post_id=?", (uid, pid)).fetchone():
            return False, u["points"] or 0
        start = datetime.now().replace(hour=0, minute=0, second=0).strftime(FMT)
        n = conn.execute("SELECT COUNT(*) n FROM view_rewards WHERE user_id=? AND ts>=?", (uid, start)).fetchone()["n"]
        if n >= POINTS_DAILY_CAP:
            return False, u["points"] or 0
        conn.execute("INSERT INTO view_rewards(user_id,post_id,ts) VALUES(?,?,?)", (uid, pid, now()))
        conn.execute("UPDATE users SET points=COALESCE(points,0)+? WHERE user_id=?", (POINTS_PER_VIDEO, uid))
        return True, (u["points"] or 0) + POINTS_PER_VIDEO


def _points_view(uid):
    start = datetime.now().replace(hour=0, minute=0, second=0).strftime(FMT)
    with closing(db()) as conn:
        u = conn.execute("SELECT points, password_hash FROM users WHERE user_id=?", (uid,)).fetchone()
        today = conn.execute("SELECT COUNT(*) n FROM view_rewards WHERE user_id=? AND ts>=?", (uid, start)).fetchone()["n"]
        used = conn.execute(
            "SELECT COALESCE(SUM(days),0) d FROM point_redemptions WHERE user_id=? AND ts>=?", (uid, add_days(now(), -30))
        ).fetchone()["d"]
    pts = (u["points"] or 0) if u else 0
    text = (
        "⭐ POINTI ZAKO\n"
        f"Pointi: {pts}\n"
        f"Leo: {today}/{POINTS_DAILY_CAP} (pointi {POINTS_PER_VIDEO} kwa kila video mpya unayotazama kwenye 🎬 Soko)\n"
        f"{POINTS_PER_DAY} pointi = siku 1 ya usajili BURE (siku {used}/{POINTS_MONTHLY_DAYS_CAP} zimetumika mwezi huu)\n"
        "Video ile ile haihesabiwi mara mbili, na unahitaji kukaa kwenye video angalau sekunde chache."
    )
    kb = Kb([[Btn(f"🎁 Badilisha pointi {POINTS_PER_DAY} → siku 1", callback_data="pt_redeem")]]) if pts >= POINTS_PER_DAY else None
    return text, kb


async def pointi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    if not is_registered(update.effective_user.id):
        await update.message.reply_text("⭐ Jisajili kwanza ili kukusanya pointi: /jisajili")
        return
    text, kb = _points_view(update.effective_user.id)
    await update.message.reply_text(text, reply_markup=kb)


async def points_redeem(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    uid = q.from_user.id
    with closing(db()) as conn, conn:
        u = conn.execute("SELECT * FROM users WHERE user_id=?", (uid,)).fetchone()
        if not u or not u["password_hash"]:
            await q.answer("Jisajili kwanza.", show_alert=True)
            return
        if (u["points"] or 0) < POINTS_PER_DAY:
            await q.answer("Pointi hazitoshi.", show_alert=True)
            return
        used = conn.execute(
            "SELECT COALESCE(SUM(days),0) d FROM point_redemptions WHERE user_id=? AND ts>=?", (uid, add_days(now(), -30))
        ).fetchone()["d"]
        if used + 1 > POINTS_MONTHLY_DAYS_CAP:
            await q.answer(f"Umefikia kikomo cha siku {POINTS_MONTHLY_DAYS_CAP} za bure kwa mwezi.", show_alert=True)
            return
        end = access_end(u)
        base = end if end and end > now() else now()
        new_until = add_days(base, 1)
        conn.execute("UPDATE users SET paid_until=?, points=points-? WHERE user_id=?", (new_until, POINTS_PER_DAY, uid))
        conn.execute("INSERT INTO point_redemptions(user_id,days,ts) VALUES(?,?,?)", (uid, 1, now()))
    await q.answer("🎁 Imefanikiwa!")
    text, kb = _points_view(uid)
    await q.edit_message_text(f"🎁 Umebadilisha pointi {POINTS_PER_DAY} kuwa siku 1. Account iko hai hadi {new_until[:10]}.\n\n{text}", reply_markup=kb)


# ---------------- risiti ----------------
def build_receipt(sale_id, uid):
    with closing(db()) as conn:
        s = conn.execute(
            "SELECT s.*, p.name pname FROM sales s JOIN products p ON p.id=s.product_id "
            "WHERE s.id=? AND (s.seller_id=? OR s.sold_by=?)", (sale_id, uid, uid)
        ).fetchone()
        if not s:
            return None
        u = conn.execute("SELECT name, phone, shop_name FROM users WHERE user_id=?", (s["seller_id"],)).fetchone()
        d = conn.execute("SELECT customer, amount-paid due FROM debts WHERE sale_id=?", (sale_id,)).fetchone()
    shop = (u["shop_name"] or u["name"]) if u else ""
    lines = [
        f"🧾 RISITI #{s['id']}", f"{shop}",
        f"Simu: +{u['phone']}" if u and u["phone"] else "",
        f"Tarehe: {s['ts'][:16]}", "────────────────",
        f"Bidhaa: {s['pname']}",
        f"Idadi: {s['qty']} × {money(s['total'] / s['qty'])}",
        f"JUMLA: {money(s['total'])}",
    ]
    if d and d["due"] > 0.009:
        lines.append(f"Deni: {d['customer']} anadaiwa {money(d['due'])}")
    lines += ["────────────────", "Asante kwa kununua! 🙏"]
    return "\n".join(x for x in lines if x != "")


def _receipt_kb(text):
    return Kb([[Btn("📤 Tuma kwa WhatsApp", url="https://wa.me/?text=" + urllib.parse.quote(text))]])


async def receipt_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not await _guard(q):
        return
    text = build_receipt(int(q.data.split("_")[1]), q.from_user.id)
    if not text:
        await q.answer("Mauzo hayapatikani.", show_alert=True)
        return
    await q.answer()
    await q.message.reply_text(text, reply_markup=_receipt_kb(text))


@require_active
async def risiti(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    try:
        sid = int(context.args[0]) if context.args else None
    except ValueError:
        await update.message.reply_text("Tumia: /risiti [namba ya mauzo]")
        return
    if sid is None:
        with closing(db()) as conn:
            r = conn.execute("SELECT id FROM sales WHERE seller_id=? OR sold_by=? ORDER BY id DESC LIMIT 1", (uid, uid)).fetchone()
        sid = r["id"] if r else None
    text = build_receipt(sid, uid) if sid else None
    if not text:
        await update.message.reply_text("Hakuna mauzo ya kutolea risiti.")
        return
    await update.message.reply_text(text, reply_markup=_receipt_kb(text))


@require_active
async def jina_la_duka(update: Update, context: ContextTypes.DEFAULT_TYPE):
    name = " ".join(context.args).strip()[:40]
    if not name:
        await update.message.reply_text("Tumia: /jina_la_duka <jina>\nMfano: /jina_la_duka Duka la Asha")
        return
    with closing(db()) as conn, conn:
        conn.execute("UPDATE users SET shop_name=? WHERE user_id=?", (name, update.effective_user.id))
    await update.message.reply_text(f"✅ Risiti zako sasa zitaandikwa: {name}")


# ---------------- wateja ----------------
def _wa_link(phone, text):
    return f"https://wa.me/{phone}?text=" + urllib.parse.quote(text)


@require_active
async def mteja(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    try:
        name = context.args[0][:40]
        phone = normalize_phone(context.args[1])
        assert phone
    except (IndexError, AssertionError):
        await update.message.reply_text("Tumia: /mteja <jina> <namba ya simu> [maelezo]\nMfano: /mteja Juma 0712345678 anapenda sukari")
        return
    note = " ".join(context.args[2:])[:120]
    with closing(db()) as conn, conn:
        cid = conn.execute("INSERT INTO customers(user_id,name,phone,note,ts) VALUES(?,?,?,?,?)", (uid, name, phone, note, now())).lastrowid
    await update.message.reply_text(f"👥 Mteja #{cid} amehifadhiwa: {name} (+{phone}).\nTuma ofa kwa wateja wote: /ofa <ujumbe>")


@require_active
async def wateja(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    with closing(db()) as conn:
        rows = conn.execute(
            "SELECT c.*, COALESCE((SELECT SUM(d.amount-d.paid) FROM debts d WHERE d.user_id=c.user_id "
            "AND lower(d.customer)=lower(c.name) AND d.amount-d.paid>0.009),0) due "
            "FROM customers c WHERE c.user_id=? ORDER BY c.name LIMIT 60", (uid,)
        ).fetchall()
    if not rows:
        await update.message.reply_text("👥 Huna wateja bado.\nHifadhi: /mteja Juma 0712345678")
        return
    out = [f"👥 WATEJA WAKO ({len(rows)})"]
    for r in rows:
        out.append(f"#{r['id']} {r['name']} | +{r['phone']}" + (f" | deni {money(r['due'])}" if r["due"] else "") + (f" | {r['note']}" if r["note"] else ""))
    out.append("\nOfa kwa wote: /ofa <ujumbe>   Kufuta: /futa_mteja <id>")
    text = "\n".join(out)
    for i in range(0, len(text), 3800):
        await update.message.reply_text(text[i:i + 3800])


@require_active
async def futa_mteja(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        cid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("Tumia: /futa_mteja <id>")
        return
    with closing(db()) as conn, conn:
        cur = conn.execute("DELETE FROM customers WHERE id=? AND user_id=?", (cid, update.effective_user.id))
    await update.message.reply_text("🗑️ Mteja amefutwa." if cur.rowcount else "❌ Mteja hapatikani.")


@require_active
async def ofa(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    msg = " ".join(context.args).strip()
    if not msg:
        await update.message.reply_text("Tumia: /ofa <ujumbe>\nMfano: /ofa Punguzo la 10% kwa bidhaa zote leo tu!")
        return
    with closing(db()) as conn:
        rows = conn.execute("SELECT name, phone FROM customers WHERE user_id=? ORDER BY name LIMIT 100", (uid,)).fetchall()
    if not rows:
        await update.message.reply_text("Huna wateja. Hifadhi kwa /mteja Juma 0712345678")
        return
    await update.message.reply_text(f"💬 Bonyeza jina la mteja kumtumia ofa kupitia WhatsApp ({len(rows)} wateja):")
    for i in range(0, len(rows), 20):
        kb = Kb([[Btn(f"💬 {r['name']}", url=_wa_link(r["phone"], f"Habari {r['name']}! {msg}"))] for r in rows[i:i + 20]])
        await update.message.reply_text(f"Wateja {i + 1}–{min(i + 20, len(rows))}", reply_markup=kb)


# ---------------- wasaidizi ----------------
def staff_owner(uid):
    with closing(db()) as conn:
        r = conn.execute("SELECT owner_id FROM staff WHERE staff_id=? AND status='active' LIMIT 1", (uid,)).fetchone()
    return r["owner_id"] if r else None


def eff_uid(uid):
    """Msaidizi anafanya kazi kwa jina la bosi wake; wengine ni wao wenyewe."""
    return staff_owner(uid) or uid


@require_active
async def ongeza_msaidizi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    owner = update.effective_user
    if not is_registered(owner.id):
        await update.message.reply_text(NOT_REG_MSG)
        return
    if not context.args:
        await update.message.reply_text(
            "Tumia: /ongeza_msaidizi <namba ya simu au Telegram ID>\n"
            "Msaidizi lazima awe ameanza bot (/start). Anaweza kurekodi mauzo ya bidhaa zako tu, na haoni faida wala gharama."
        )
        return
    arg = context.args[0]
    phone = normalize_phone(arg)
    with closing(db()) as conn:
        if phone:
            t = conn.execute("SELECT user_id, name FROM users WHERE phone=?", (phone,)).fetchone()
        else:
            try:
                t = conn.execute("SELECT user_id, name FROM users WHERE user_id=?", (int(arg),)).fetchone()
            except ValueError:
                t = None
        n = conn.execute("SELECT COUNT(*) n FROM staff WHERE owner_id=?", (owner.id,)).fetchone()["n"]
    if not t:
        await update.message.reply_text("❌ Mtu huyo hajaanza bot. Mwambie atume /start kwa bot kwanza, kisha ujaribu tena.")
        return
    if t["user_id"] == owner.id:
        await update.message.reply_text("❌ Huwezi kujiongeza mwenyewe.")
        return
    if n >= MAX_STAFF:
        await update.message.reply_text(f"❌ Umefikia kikomo cha wasaidizi {MAX_STAFF}. Ondoa mmoja kwa /wasaidizi.")
        return
    with closing(db()) as conn, conn:
        conn.execute("INSERT OR REPLACE INTO staff(owner_id,staff_id,status,ts) VALUES(?,?,'pending',?)", (owner.id, t["user_id"], now()))
    await update.message.reply_text(f"⏳ Ombi limetumwa kwa {t['name']}. Utaarifiwa akikubali.")
    kb = Kb([[Btn("✅ Kubali", callback_data=f"sf_ok_{owner.id}"), Btn("❌ Kataa", callback_data=f"sf_no_{owner.id}")]])
    try:
        await context.bot.send_message(
            t["user_id"],
            f"👷 {owner.full_name} anakuomba uwe msaidizi wake wa mauzo.\n"
            "Utarekodi mauzo ya bidhaa zake tu; hutaona faida wala gharama zake.",
            reply_markup=kb,
        )
    except Exception:
        await update.message.reply_text("⚠️ Sikuweza kumfikia mtu huyo. Hakikisha hajazuia bot.")


async def staff_invite_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    _, action, owner = q.data.split("_")
    owner = int(owner)
    me = q.from_user
    with closing(db()) as conn, conn:
        r = conn.execute("SELECT status FROM staff WHERE owner_id=? AND staff_id=?", (owner, me.id)).fetchone()
        if not r or r["status"] != "pending":
            await q.answer("Ombi hili halipo tena.", show_alert=True)
            return
        if action == "ok":
            other = conn.execute("SELECT 1 FROM staff WHERE staff_id=? AND status='active'", (me.id,)).fetchone()
            if other:
                await q.answer("Tayari unafanya kazi kwa mtu mwingine. Tumia /acha_kazi kwanza.", show_alert=True)
                return
            conn.execute("UPDATE staff SET status='active' WHERE owner_id=? AND staff_id=?", (owner, me.id))
        else:
            conn.execute("DELETE FROM staff WHERE owner_id=? AND staff_id=?", (owner, me.id))
    await q.answer()
    if action == "ok":
        await q.edit_message_text("✅ Wewe sasa ni msaidizi. Bonyeza 🛒 Uza kurekodi mauzo. Kuacha kazi: /acha_kazi")
        await q.message.reply_text("🛒 Uza", reply_markup=menu_for(me.id))
        note = f"✅ {me.full_name} amekubali kuwa msaidizi wako."
    else:
        await q.edit_message_text("Umekataa ombi.")
        note = f"❌ {me.full_name} amekataa ombi la kuwa msaidizi."
    try:
        await context.bot.send_message(owner, note)
    except Exception:
        pass


def _staff_view(owner):
    with closing(db()) as conn:
        rows = conn.execute(
            "SELECT s.staff_id, s.status, u.name FROM staff s LEFT JOIN users u ON u.user_id=s.staff_id WHERE s.owner_id=?", (owner,)
        ).fetchall()
    if not rows:
        return "👷 Huna wasaidizi.\nOngeza: /ongeza_msaidizi <simu au id>", None
    out = ["👷 WASAIDIZI WAKO"] + [f"{r['name']} ({r['staff_id']}) | {'hai ✅' if r['status'] == 'active' else 'anasubiriwa ⏳'}" for r in rows]
    kb = Kb([[Btn(f"🗑️ Ondoa {r['name']}", callback_data=f"sd_{r['staff_id']}")] for r in rows])
    return "\n".join(out), kb


@require_active
async def wasaidizi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text, kb = _staff_view(update.effective_user.id)
    await update.message.reply_text(text, reply_markup=kb)


async def staff_remove_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    sid = int(q.data.split("_")[1])
    with closing(db()) as conn, conn:
        cur = conn.execute("DELETE FROM staff WHERE owner_id=? AND staff_id=?", (q.from_user.id, sid))
    await q.answer("🗑️ Ameondolewa" if cur.rowcount else "Hayupo.")
    text, kb = _staff_view(q.from_user.id)
    try:
        await q.edit_message_text(text, reply_markup=kb)
    except Exception:
        pass
    if cur.rowcount:
        try:
            await context.bot.send_message(sid, "ℹ️ Umeondolewa kwenye kazi ya usaidizi wa mauzo.")
        except Exception:
            pass


async def acha_kazi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    me = update.effective_user
    owner = staff_owner(me.id)
    if not owner:
        await update.message.reply_text("Wewe si msaidizi wa mtu yeyote.")
        return
    with closing(db()) as conn, conn:
        conn.execute("DELETE FROM staff WHERE staff_id=?", (me.id,))
    await update.message.reply_text("✅ Umeacha kazi ya usaidizi.")
    try:
        await context.bot.send_message(owner, f"ℹ️ {me.full_name} ameacha kazi ya usaidizi.")
    except Exception:
        pass


# ---------------- maagizo ya Soko ----------------
OR_TEXT = 70


def _contact_line(uid):
    with closing(db()) as conn:
        u = conn.execute("SELECT name, username, phone FROM users WHERE user_id=?", (uid,)).fetchone()
    if not u:
        return f"ID {uid}"
    if u["username"] and re.fullmatch(r"[A-Za-z0-9_]{4,32}", u["username"]):
        return f"{u['name']} (https://t.me/{u['username']})"
    if u["phone"]:
        return f"{u['name']} (simu +{u['phone']})"
    return f"{u['name']} (ID {uid})"


async def order_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    pid = int(q.data.split("_")[1])
    p = _post_row(pid)
    if not p or not p["active"]:
        await q.answer("Tangazo halipatikani tena.", show_alert=True)
        return ConversationHandler.END
    if p["user_id"] == q.from_user.id:
        await q.answer("Hili ni tangazo lako.", show_alert=True)
        return ConversationHandler.END
    ensure_user(q.from_user)
    with closing(db()) as conn:
        n = conn.execute("SELECT COUNT(*) n FROM orders WHERE buyer_id=? AND ts>=?", (q.from_user.id, add_days(now(), -1))).fetchone()["n"]
    if n >= ORDERS_PER_DAY:
        await q.answer(f"Umefikia kikomo cha maagizo {ORDERS_PER_DAY} kwa siku.", show_alert=True)
        return ConversationHandler.END
    context.user_data["order_pid"] = pid
    await q.answer()
    await q.message.reply_text(
        f"🛍️ Agiza: {p['caption'][:70]}\n\nAndika idadi na maelezo (mfano: 2, nipelekee Soko Kuu).\n"
        "Muuzaji atapata jina lako na username/namba ili awasiliane nawe.\nKughairi: /ghairi"
    )
    return OR_TEXT


async def order_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = update.message.text.strip()
    if text in MENU_TEXTS:
        return await ghairi(update, context)
    if len(text) < 2:
        await update.message.reply_text("❌ Andika angalau idadi au maelezo mafupi.")
        return OR_TEXT
    pid = context.user_data.pop("order_pid", None)
    p = _post_row(pid) if pid else None
    if not p:
        await update.message.reply_text("Tangazo halipatikani tena.")
        return ConversationHandler.END
    buyer = update.effective_user
    with closing(db()) as conn, conn:
        oid = conn.execute(
            "INSERT INTO orders(post_id,buyer_id,seller_id,text,ts) VALUES(?,?,?,?,?)", (pid, buyer.id, p["user_id"], text[:300], now())
        ).lastrowid
    await update.message.reply_text(f"✅ Ombi #{oid} limetumwa kwa {p['seller_name']}. Utaarifiwa akikubali au akikataa.", reply_markup=menu_for(buyer.id))
    kb = Kb([[Btn("✅ Kubali", callback_data=f"od_ok_{oid}"), Btn("❌ Kataa", callback_data=f"od_no_{oid}")]])
    try:
        await context.bot.send_message(
            p["user_id"],
            f"🛍️ AGIZO JIPYA #{oid}\nBidhaa: {p['caption'][:80]}\nMnunuzi: {buyer.full_name} (@{buyer.username or '-'})\n\n“{text[:300]}”",
            reply_markup=kb,
        )
    except Exception:
        pass
    return ConversationHandler.END


async def order_buttons(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    _, action, oid = q.data.split("_")
    oid = int(oid)
    with closing(db()) as conn, conn:
        o = conn.execute("SELECT * FROM orders WHERE id=?", (oid,)).fetchone()
        if not o or o["seller_id"] != q.from_user.id:
            await q.answer("Huna ruhusa.", show_alert=True)
            return
        if o["status"] != "pending":
            await q.answer("Agizo hili limeshashughulikiwa.", show_alert=True)
            return
        conn.execute("UPDATE orders SET status=? WHERE id=?", ("accepted" if action == "ok" else "declined", oid))
    await q.answer()
    if action == "ok":
        await q.edit_message_text(f"✅ Umekubali agizo #{oid}.\nWasiliana na mnunuzi: {_contact_line(o['buyer_id'])}")
        try:
            await context.bot.send_message(
                o["buyer_id"], f"🎉 Agizo lako #{oid} limekubaliwa!\nWasiliana na muuzaji: {_contact_line(o['seller_id'])}"
            )
        except Exception:
            pass
    else:
        await q.edit_message_text(f"❌ Umekataa agizo #{oid}.")
        try:
            await context.bot.send_message(o["buyer_id"], f"😔 Agizo lako #{oid} halikukubaliwa. Tazama bidhaa nyingine: /soko")
        except Exception:
            pass


async def maagizo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    ensure_user(update.effective_user)
    with closing(db()) as conn:
        recv = conn.execute(
            "SELECT o.*, u.name bname FROM orders o LEFT JOIN users u ON u.user_id=o.buyer_id "
            "WHERE o.seller_id=? AND o.status='pending' ORDER BY o.id DESC LIMIT 10", (uid,)
        ).fetchall()
        sent = conn.execute(
            "SELECT o.*, u.name sname FROM orders o LEFT JOIN users u ON u.user_id=o.seller_id "
            "WHERE o.buyer_id=? ORDER BY o.id DESC LIMIT 5", (uid,)
        ).fetchall()
    if not recv and not sent:
        await update.message.reply_text("🛍️ Hakuna maagizo bado. Tazama bidhaa kwenye 🎬 Soko na ubonyeze 🛍️ Agiza.")
        return
    icon = {"pending": "⏳ inasubiri", "accepted": "✅ amekubali", "declined": "❌ amekataa"}
    for o in recv:
        await update.message.reply_text(
            f"🛍️ AGIZO #{o['id']} (unasubiriwa)\nMnunuzi: {o['bname']}\n“{o['text']}”",
            reply_markup=Kb([[Btn("✅ Kubali", callback_data=f"od_ok_{o['id']}"), Btn("❌ Kataa", callback_data=f"od_no_{o['id']}")]]),
        )
    if sent:
        await update.message.reply_text(
            "📤 MAAGIZO ULIYOTUMA\n" + "\n".join(f"#{o['id']} | {o['sname']} | {icon.get(o['status'], o['status'])} | {o['text'][:40]}" for o in sent)
        )


# ---------------- kutafuta bidhaa Sokoni ----------------
async def tafuta(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    words = [w.lower() for w in (context.args or []) if len(w) >= 2][:5]
    if not words:
        await update.message.reply_text("🔍 Tumia: /tafuta <neno>\nMfano: /tafuta kanga  au  /tafuta juice mbeya")
        return
    cond = " AND ".join("(lower(p.caption) LIKE ? OR lower(u.name) LIKE ?)" for _ in words)
    params = [x for w in words for x in (f"%{w}%", f"%{w}%")]
    with closing(db()) as conn:
        rows = conn.execute(
            f"SELECT p.id, p.caption, u.name FROM posts p JOIN users u ON u.user_id=p.user_id "
            f"WHERE p.active=1 AND {cond} ORDER BY p.likes DESC, p.id DESC LIMIT 8", params
        ).fetchall()
    if not rows:
        await update.message.reply_text("🔍 Hakuna matangazo yaliyopatikana. Jaribu neno lingine, au tazama /soko")
        return
    kb = Kb([[Btn(f"{r['caption'][:32]} · {r['name'][:14]}", callback_data=f"fv_{r['id']}")] for r in rows])
    await update.message.reply_text(f"🔍 Matokeo ({len(rows)}):", reply_markup=kb)


async def feed_view(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    await _send_post(q.message, int(q.data.split("_")[1]), q.from_user.id, context.user_data)


# ---------------- takwimu za admin ----------------
async def takwimu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    d7, d30 = add_days(now(), -7), add_days(now(), -30)
    with closing(db()) as conn:
        users = conn.execute("SELECT * FROM users").fetchall()
        total = len(users)
        new7 = sum(1 for u in users if (u["joined"] or "") >= d7)
        new30 = sum(1 for u in users if (u["joined"] or "") >= d30)
        reg = [u for u in users if u["password_hash"] and not is_admin(u["user_id"])]
        cnt = {"paid": 0, "trial": 0, "locked": 0, "churn": 0}
        for u in reg:
            act, _, kind = sub_state(u)
            if act:
                cnt["paid" if kind == "paid" else "trial"] += 1
            else:
                cnt["locked"] += 1
                if u["paid_until"]:
                    cnt["churn"] += 1
        pay = conn.execute(
            "SELECT COUNT(DISTINCT user_id) n FROM payments WHERE status='approved'"
        ).fetchone()["n"]
        rev7 = conn.execute("SELECT COALESCE(SUM(amount),0) a, COUNT(*) n FROM payments WHERE status='approved' AND decided_ts>=?", (d7,)).fetchone()
        rev30 = conn.execute("SELECT COALESCE(SUM(amount),0) a, COUNT(*) n FROM payments WHERE status='approved' AND decided_ts>=?", (d30,)).fetchone()
        sellers7 = conn.execute("SELECT COUNT(DISTINCT seller_id) n FROM sales WHERE ts>=?", (d7,)).fetchone()["n"]
        feed = conn.execute("SELECT COUNT(*) n, COALESCE(SUM(views),0) v, COALESCE(SUM(likes),0) l FROM posts WHERE active=1").fetchone()
        orders30 = conn.execute("SELECT COUNT(*) n, COALESCE(SUM(status='accepted'),0) a FROM orders WHERE ts>=?", (d30,)).fetchone()
        tickets = conn.execute("SELECT COUNT(*) n FROM tickets WHERE status='open'").fetchone()["n"]
        weeks = []
        for i in range(4):
            a, b = add_days(now(), -7 * (i + 1)), add_days(now(), -7 * i)
            weeks.append(sum(1 for u in users if a <= (u["joined"] or "") < b))
    conv = f"{pay / len(reg) * 100:.0f}%" if reg else "0%"
    await update.message.reply_text(
        "📈 TAKWIMU ZA UKUAJI\n"
        f"Watumiaji wote: {total} | Waliosajiliwa: {len(reg)}\n"
        f"Wapya: siku 7 = {new7} | siku 30 = {new30}\n"
        f"Wiki 4 zilizopita (wapya kila wiki, mpya→zamani): {', '.join(map(str, weeks))}\n\n"
        f"🟢 Waliolipa sasa: {cnt['paid']} | 🎁 Ofa: {cnt['trial']} | 🔒 Waliofungwa: {cnt['locked']}\n"
        f"Walioondoka (walilipa kabla, sasa wamefungwa): {cnt['churn']}\n"
        f"Wamewahi kulipa: {pay} ({conv} ya waliosajiliwa)\n"
        f"Wauzaji hai (wiki hii): {sellers7}\n\n"
        f"💰 Mapato: siku 7 = {money(rev7['a'])} ({rev7['n']}) | siku 30 = {money(rev30['a'])} ({rev30['n']})\n\n"
        f"🎬 Soko: matangazo {feed['n']} | views {feed['v']} | likes {feed['l']}\n"
        f"🛍️ Maagizo (siku 30): {orders30['n']} | yaliyokubaliwa {orders30['a']}\n"
        f"🎫 Tiketi zinazosubiri: {tickets}"
    )


# ---------------- usajili wa handlers ----------------
def register_v2(app: Application):
    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("badili_password", bp_start)],
        states={
            PW_OLD: [MessageHandler(filters.TEXT & ~filters.COMMAND, bp_old)],
            PW_NEW: [MessageHandler(filters.TEXT & ~filters.COMMAND, bp_new)],
            PW_NEW2: [MessageHandler(filters.TEXT & ~filters.COMMAND, bp_new2)],
        },
        fallbacks=[CommandHandler("ghairi", ghairi)],
    ))
    app.add_handler(ConversationHandler(
        entry_points=[
            MessageHandler(filters.Regex(f"^{re.escape(BTN_SUPPORT)}$"), sp_start),
            CommandHandler("wasiliana", sp_start),
        ],
        states={SP_TEXT: [MessageHandler(filters.TEXT & ~filters.COMMAND, sp_text)]},
        fallbacks=[CommandHandler("ghairi", ghairi)],
    ))
    app.add_handler(ConversationHandler(
        entry_points=[CallbackQueryHandler(tk_reply_start, pattern=r"^tk_\d+$")],
        states={TK_REPLY: [MessageHandler(filters.TEXT & ~filters.COMMAND, tk_reply_text)]},
        fallbacks=[CommandHandler("ghairi", ghairi)],
    ))
    app.add_handler(ConversationHandler(
        entry_points=[CallbackQueryHandler(order_start, pattern=r"^fo_\d+$")],
        states={OR_TEXT: [MessageHandler(filters.TEXT & ~filters.COMMAND, order_text)]},
        fallbacks=[CommandHandler("ghairi", ghairi)],
    ))
    for pattern, fn in [
        (r"^pt_redeem$", points_redeem), (r"^rc_\d+$", receipt_button),
        (r"^sf_(ok|no)_\d+$", staff_invite_button), (r"^sd_\d+$", staff_remove_button),
        (r"^od_(ok|no)_\d+$", order_buttons), (r"^fv_\d+$", feed_view),
        (r"^fa_(ok_\d+|no)$", futa_akaunti_button),
    ]:
        app.add_handler(CallbackQueryHandler(fn, pattern=pattern))
    for name, fn in [
        ("masharti", masharti), ("pointi", pointi), ("risiti", risiti), ("jina_la_duka", jina_la_duka),
        ("mteja", mteja), ("wateja", wateja), ("futa_mteja", futa_mteja), ("ofa", ofa),
        ("ongeza_msaidizi", ongeza_msaidizi), ("wasaidizi", wasaidizi), ("acha_kazi", acha_kazi),
        ("maagizo", maagizo), ("tafuta", tafuta),
        ("takwimu", takwimu), ("tiketi", tiketi), ("jibu", jibu), ("futa_akaunti", futa_akaunti),
    ]:
        app.add_handler(CommandHandler(name, fn))
    for text, fn in [
        (BTN_CUSTOMERS, wateja), (BTN_POINTS, pointi), (BTN_ORDERS, maagizo),
        (BTN_STATS, takwimu), (BTN_TICKETS, tiketi),
    ]:
        app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(text)}$"), fn))


# ====== KUWASHA BOT ======
def main():
    builder = (
        Application.builder()
        .token(os.environ["BOT_TOKEN"])
        .concurrent_updates(True)       # watumiaji wengi wanahudumiwa kwa wakati mmoja
        .connection_pool_size(32)       # miunganisho zaidi kwa Telegram
        .post_init(setup_commands)
    )
    proxy = os.environ.get("PROXY_URL")  # akaunti ya bure ya PythonAnywhere: http://proxy.server:3128
    if proxy:
        for names in (("proxy", "get_updates_proxy"), ("proxy_url", "get_updates_proxy_url")):
            if hasattr(builder, names[0]):
                getattr(builder, names[0])(proxy)
                getattr(builder, names[1])(proxy)
                break
    app = builder.build()
    init_db()
    register(app)
    app.run_polling()


if __name__ == "__main__":
    main()
