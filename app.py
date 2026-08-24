"""
Smart Queue Management System v4.0
====================================
FEATURES:
  - Student / Staff / Admin role-based access control
  - Priority-based queue scheduling (Normal / High / Urgent)
  - Real-time ticket tracking and queue position
  - In-app notification system
  - Email notifications via SMTP (Gmail)
  - Appointment booking and management
  - Post-service star ratings and feedback
  - Staff dashboard: call next, done, no-show, pause/resume
  - Admin: user management, system settings, announcements,
           audit log, analytics, peak-hours heatmap, CSV/PDF export
  - Public display board
  - Dark mode
"""

from flask import (Flask, render_template, request, jsonify,
                   redirect, url_for, session, send_file, flash)
import os, csv, io, hashlib, secrets, smtplib

# Database backend — PostgreSQL (Supabase) when DATABASE_URL is set, else SQLite
DATABASE_URL = os.environ.get("DATABASE_URL", "")
USE_PG = bool(DATABASE_URL)

if USE_PG:
    import pg8000
    import pg8000.native
else:
    import sqlite3
from datetime import datetime, timedelta
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from functools import wraps
import random, string

app = Flask(__name__)
import os
app.secret_key = os.environ.get('SECRET_KEY', secrets.token_hex(32))
_data_dir = os.environ.get("DATA_DIR", os.path.dirname(os.path.abspath(__file__)))
DB_PATH = os.path.join(_data_dir, "queue.db")

# ─────────────────────────────────────────────────────────
DEFAULT_SERVICES = {
    "admission":  {"name": "Admissions & Enrollment",  "avg_minutes": 15},
    "financial":  {"name": "Financial Aid & Bursary",  "avg_minutes": 20},
    "academic":   {"name": "Academic Records",         "avg_minutes": 10},
    "counseling": {"name": "Student Counseling",       "avg_minutes": 30},
    "library":    {"name": "Library & Resources",      "avg_minutes":  8},
    "it_support": {"name": "IT Support",               "avg_minutes": 12},
}

def get_services():
    """Return merged dict of built-in + admin-added custom services."""
    services = dict(DEFAULT_SERVICES)
    try:
        with get_db() as conn:
            rows = conn.execute(
                "SELECT key, name, avg_minutes FROM custom_services WHERE is_active=1"
            ).fetchall()
        for r in rows:
            services[r["key"]] = {
                "name": r["name"],
                "avg_minutes": r["avg_minutes"],
                "custom": True
            }
    except Exception:
        pass
    return services

class _ServiceProxy(dict):
    """Behaves like a dict but always reflects the latest services from DB."""
    def __getitem__(self, k):  return get_services()[k]
    def __contains__(self, k): return k in get_services()
    def __iter__(self):        return iter(get_services())
    def __len__(self):         return len(get_services())
    def keys(self):            return get_services().keys()
    def values(self):          return get_services().values()
    def items(self):           return get_services().items()
    def get(self, k, d=None):  return get_services().get(k, d)

SERVICES = _ServiceProxy()
PRIORITY_LABELS = {1: "Normal", 2: "High", 3: "Urgent"}

# ─────────────────────────────────────────────────────────
# DATABASE
# ─────────────────────────────────────────────────────────
class _PgRow(dict):
    """Make pg8000 rows behave like sqlite3.Row (access by column name)."""
    def __getitem__(self, key):
        if isinstance(key, int):
            return list(self.values())[key]
        return super().__getitem__(key)

def get_db():
    if USE_PG:
        # Parse DATABASE_URL for pg8000
        import urllib.parse
        url = urllib.parse.urlparse(DATABASE_URL)
        conn = pg8000.connect(
            host=url.hostname,
            port=url.port or 5432,
            database=url.path.lstrip('/'),
            user=url.username,
            password=url.password,
            ssl_context=True  # Supabase requires SSL
        )
        conn.autocommit = False
        return _PgConn(conn)
    else:
        conn = sqlite3.connect(DB_PATH)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL")
        return conn

class _PgConn:
    """Thin wrapper making psycopg2 work like sqlite3 context manager."""
    def __init__(self, conn):
        self._conn = conn

    def execute(self, sql, params=()):
        if USE_PG:
            # Convert SQLite syntax to PostgreSQL
            sql = sql.replace("?", "%s")
            # INSERT OR IGNORE → INSERT ... ON CONFLICT DO NOTHING
            if "INSERT OR IGNORE" in sql.upper():
                sql = sql.upper().replace("INSERT OR IGNORE INTO", "INSERT INTO")
                # restore original case for table/column names by using regex
                import re as _re
                sql = _re.sub(r"(?i)INSERT OR IGNORE INTO", "INSERT INTO", sql.replace("?","%s"))
                sql = sql.rstrip()
                # Add ON CONFLICT DO NOTHING before any trailing semicolon
                if not sql.upper().endswith("ON CONFLICT DO NOTHING"):
                    sql = sql + " ON CONFLICT DO NOTHING"
            # INSERT OR REPLACE → INSERT ... ON CONFLICT ... DO UPDATE SET
            elif "INSERT OR REPLACE" in sql.upper():
                import re as _re
                sql = _re.sub(r"(?i)INSERT OR REPLACE INTO", "INSERT INTO", sql)
                # For settings table: on conflict update the value
                if "ON CONFLICT" not in sql.upper():
                    sql = sql + " ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value"
            # Apply DDL fixes
            if sql.strip().upper().startswith("CREATE"):
                sql = _to_pg_ddl(sql)
        cur = self._conn.cursor()
        try:
            if params:
                cur.execute(sql, list(params))
            else:
                cur.execute(sql)
        except Exception as e:
            self._conn.rollback()
            raise
        return _PgCursor(cur)

    def executemany(self, sql, seq):
        sql = _to_pg(sql)
        cur = self._conn.cursor()
        for row in seq:
            cur.execute(sql, list(row) if row else [])

    def executescript(self, sql):
        """Run multiple statements separated by semicolons."""
        for stmt in sql.split(";"):
            stmt = stmt.strip()
            if stmt:
                stmt = _to_pg_ddl(stmt)
                cur = self._conn.cursor()
                try:
                    cur.execute(stmt)
                except Exception:
                    self._conn.rollback()
                    raise
        self._conn.commit()

    def commit(self):
        self._conn.commit()

    def rollback(self):
        self._conn.rollback()

    def close(self):
        self._conn.close()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, *_):
        if exc_type:
            self._conn.rollback()
        else:
            self._conn.commit()
        self._conn.close()

class _PgCursor:
    """Wraps pg8000 cursor to return dict-like rows."""
    def __init__(self, cur):
        self._cur = cur

    def _to_row(self, raw):
        if raw is None:
            return None
        if self._cur.description:
            cols = [d[0] for d in self._cur.description]
            return _PgRow(zip(cols, raw))
        return _PgRow()

    def fetchone(self):
        return self._to_row(self._cur.fetchone())

    def fetchall(self):
        rows = self._cur.fetchall() or []
        return [self._to_row(r) for r in rows]

    @property
    def rowcount(self):
        return self._cur.rowcount

def _to_pg(sql):
    """Convert SQLite SQL to PostgreSQL SQL."""
    if not USE_PG:
        return sql
    # Replace ? placeholders with %s
    sql = sql.replace("?", "%s")
    return sql

def _pg_sql(sql):
    """Full SQLite→PostgreSQL conversion including INSERT OR IGNORE etc."""
    if not USE_PG:
        return sql
    sql = _to_pg(sql)
    # INSERT OR IGNORE → INSERT ... ON CONFLICT DO NOTHING
    if "INSERT OR IGNORE" in sql.upper():
        sql = sql.replace("INSERT OR IGNORE INTO", "INSERT INTO", 1)
        sql = sql.rstrip().rstrip(")") 
        sql = sql + ") ON CONFLICT DO NOTHING" if not sql.endswith("ON CONFLICT DO NOTHING") else sql
    # INSERT OR REPLACE → INSERT ... ON CONFLICT DO UPDATE
    if "INSERT OR REPLACE" in sql.upper():
        sql = sql.replace("INSERT OR REPLACE INTO", "INSERT INTO", 1)
    return sql

def _to_pg_ddl(sql):
    """Convert SQLite DDL to PostgreSQL DDL."""
    if not USE_PG:
        return sql
    sql = sql.replace("INTEGER PRIMARY KEY AUTOINCREMENT", "SERIAL PRIMARY KEY")
    sql = sql.replace("INTEGER PRIMARY KEY", "SERIAL PRIMARY KEY")
    # SQLite INTEGER → PostgreSQL INTEGER (keep)
    # SQLite TEXT → PostgreSQL TEXT (keep)
    # SQLite REAL → PostgreSQL REAL (keep)
    return sql
    sql = sql.replace("INTEGER PRIMARY KEY AUTOINCREMENT", "SERIAL PRIMARY KEY")
    sql = sql.replace("INTEGER PRIMARY KEY", "SERIAL PRIMARY KEY")
    sql = sql.replace("IF NOT EXISTS", "IF NOT EXISTS")
    return sql

def now_str():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")

def hash_pw(pw):
    return hashlib.sha256(pw.encode()).hexdigest()

def init_db():
    with get_db() as c:
        c.execute("""CREATE TABLE IF NOT EXISTS users (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id       TEXT NOT NULL UNIQUE,
            full_name     TEXT NOT NULL,
            email         TEXT,
            phone         TEXT,
            password      TEXT NOT NULL,
            role          TEXT NOT NULL DEFAULT 'student',
            is_active     INTEGER NOT NULL DEFAULT 1,
            failed_logins INTEGER DEFAULT 0,
            locked_until  TEXT,
            reset_token   TEXT,
            reset_expires TEXT,
            created_at    TEXT NOT NULL,
            last_login    TEXT
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS tickets (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            ticket_no     TEXT NOT NULL UNIQUE,
            student_id    TEXT NOT NULL,
            student_name  TEXT NOT NULL,
            service       TEXT NOT NULL,
            priority      INTEGER NOT NULL DEFAULT 1,
            status        TEXT NOT NULL DEFAULT 'waiting',
            created_at    TEXT NOT NULL,
            called_at     TEXT,
            completed_at  TEXT,
            counter       INTEGER,
            notes         TEXT,
            requeue_count INTEGER DEFAULT 0
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS counters (
            id             INTEGER PRIMARY KEY AUTOINCREMENT,
            counter_no     INTEGER NOT NULL UNIQUE,
            service        TEXT NOT NULL,
            is_active      INTEGER NOT NULL DEFAULT 1,
            current_ticket TEXT,
            staff_id       TEXT
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS appointments (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            student_id   TEXT NOT NULL,
            student_name TEXT NOT NULL,
            service      TEXT NOT NULL,
            appt_date    TEXT NOT NULL,
            appt_time    TEXT NOT NULL,
            status       TEXT NOT NULL DEFAULT 'booked',
            notes        TEXT,
            created_at   TEXT NOT NULL
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS feedback (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            ticket_no  TEXT NOT NULL,
            student_id TEXT NOT NULL,
            service    TEXT NOT NULL,
            rating     INTEGER NOT NULL,
            comment    TEXT,
            created_at TEXT NOT NULL
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS notifications (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            student_id TEXT NOT NULL,
            message    TEXT NOT NULL,
            is_read    INTEGER DEFAULT 0,
            created_at TEXT NOT NULL
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS announcements (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            title      TEXT NOT NULL,
            body       TEXT NOT NULL,
            type       TEXT NOT NULL DEFAULT 'info',
            is_active  INTEGER DEFAULT 1,
            created_by TEXT NOT NULL,
            created_at TEXT NOT NULL,
            expires_at TEXT
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS audit_log (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            actor_id   TEXT NOT NULL,
            action     TEXT NOT NULL,
            target     TEXT,
            detail     TEXT,
            ip         TEXT,
            created_at TEXT NOT NULL
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS settings (
            key   TEXT PRIMARY KEY,
            value TEXT NOT NULL
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS service_config (
            service      TEXT PRIMARY KEY,
            open_time    TEXT DEFAULT '08:00',
            close_time   TEXT DEFAULT '17:00',
            max_queue    INTEGER DEFAULT 100,
            is_paused    INTEGER DEFAULT 0,
            pause_reason TEXT
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS hourly_stats (
            id      INTEGER PRIMARY KEY AUTOINCREMENT,
            date    TEXT NOT NULL,
            hour    INTEGER NOT NULL,
            service TEXT NOT NULL,
            count   INTEGER DEFAULT 0
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS custom_services (
            key         TEXT PRIMARY KEY,
            name        TEXT NOT NULL,
            avg_minutes INTEGER NOT NULL DEFAULT 10,
            is_active   INTEGER NOT NULL DEFAULT 1,
            created_at  TEXT NOT NULL
        )""")

        # Seed counters
        if c.execute("SELECT COUNT(*) FROM counters").fetchone()[0] == 0:
            c.executemany("INSERT INTO counters (counter_no, service) VALUES (?,?)", [
                (1,"admission"),(2,"financial"),(3,"academic"),
                (4,"counseling"),(5,"library"),(6,"it_support"),
            ])

        # Seed service config
        for svc in SERVICES:
            c.execute("INSERT INTO service_config (service) VALUES (?) ON CONFLICT DO NOTHING", (svc,))

        # Seed default settings (email only)
        defaults = [
            ("email_enabled",   "0"),
            ("smtp_host",       "smtp.gmail.com"),
            ("smtp_port",       "587"),
            ("smtp_user",       ""),
            ("smtp_password",   ""),
            ("smtp_from_name",  "Smart Queue System"),
            ("university_name", "Federal University"),
        ]
        for k, v in defaults:
            c.execute("INSERT INTO settings (key, value) VALUES (?,?) ON CONFLICT DO NOTHING", (k, v))

        # Default admin account
        if c.execute("SELECT COUNT(*) FROM users WHERE role='admin'").fetchone()[0] == 0:
            c.execute(
                "INSERT INTO users (user_id,full_name,email,password,role,created_at) VALUES (?,?,?,?,?,?)",
                ("admin","System Administrator","admin@university.edu",
                 hash_pw("Admin@123"),"admin",now_str())
            )
        # Demo staff account
        if c.execute("SELECT COUNT(*) FROM users WHERE user_id='staff01'").fetchone()[0] == 0:
            c.execute(
                "INSERT INTO users (user_id,full_name,email,password,role,created_at) VALUES (?,?,?,?,?,?)",
                ("staff01","Demo Staff","staff@university.edu",
                 hash_pw("Staff@123"),"staff",now_str())
            )

# ─────────────────────────────────────────────────────────
# SETTINGS HELPERS
# ─────────────────────────────────────────────────────────
def get_setting(key, default=""):
    with get_db() as c:
        row = c.execute("SELECT value FROM settings WHERE key=?", (key,)).fetchone()
    return row["value"] if row else default

def set_setting(key, value):
    with get_db() as c:
        c.execute("INSERT INTO settings (key, value) VALUES (%s, %s) ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value", (key, str(value)))

def get_all_settings():
    with get_db() as c:
        rows = c.execute("SELECT key, value FROM settings").fetchall()
    return {r["key"]: r["value"] for r in rows}

# ─────────────────────────────────────────────────────────
# AUDIT LOG
# ─────────────────────────────────────────────────────────
def audit(actor_id, action, target=None, detail=None):
    with get_db() as c:
        c.execute(
            "INSERT INTO audit_log (actor_id,action,target,detail,ip,created_at) VALUES (?,?,?,?,?,?)",
            (actor_id, action, target, detail, request.remote_addr, now_str())
        )

# ─────────────────────────────────────────────────────────
# AUTH DECORATORS
# ─────────────────────────────────────────────────────────
def login_required(f):
    @wraps(f)
    def wrapped(*args, **kwargs):
        if not session.get("user_id"):
            return redirect(url_for("login", next=request.path))
        return f(*args, **kwargs)
    return wrapped

def role_required(*roles):
    def decorator(f):
        @wraps(f)
        def wrapped(*args, **kwargs):
            if not session.get("user_id"):
                return redirect(url_for("login", next=request.path))
            if session.get("role") not in roles:
                return render_template("forbidden.html"), 403
            return f(*args, **kwargs)
        return wrapped
    return decorator

def current_user():
    return session.get("user_id")

def current_role():
    return session.get("role", "student")

# ─────────────────────────────────────────────────────────
# NOTIFICATIONS  (in-app + email only)
# ─────────────────────────────────────────────────────────
def push_notification(user_id, message):
    """Store an in-app notification for the user."""
    with get_db() as c:
        c.execute(
            "INSERT INTO notifications (student_id,message,created_at) VALUES (?,?,?)",
            (user_id, message, now_str())
        )

def send_email(to_email, subject, body_html):
    """Send an email via SMTP. Returns True on success, False on failure."""
    if not to_email or get_setting("email_enabled") != "1":
        return False
    try:
        smtp_host = get_setting("smtp_host", "smtp.gmail.com")
        smtp_port = int(get_setting("smtp_port", "587"))
        smtp_user = get_setting("smtp_user")
        smtp_pass = get_setting("smtp_password")
        from_name = get_setting("smtp_from_name", "Smart Queue System")
        if not smtp_user or not smtp_pass:
            return False
        msg = MIMEMultipart("alternative")
        msg["Subject"] = subject
        msg["From"]    = f"{from_name} <{smtp_user}>"
        msg["To"]      = to_email
        msg.attach(MIMEText(body_html, "html"))
        with smtplib.SMTP(smtp_host, smtp_port, timeout=10) as server:
            server.starttls()
            server.login(smtp_user, smtp_pass)
            server.sendmail(smtp_user, to_email, msg.as_string())
        return True
    except Exception as e:
        print(f"[Email Error] {e}")
        return False

def notify(user_id, message, subject=None):
    """Push in-app notification and send email if enabled."""
    push_notification(user_id, message)
    with get_db() as c:
        u = c.execute("SELECT email FROM users WHERE user_id=?", (user_id,)).fetchone()
    if u and u["email"]:
        html = (f"<p style='font-family:Arial,sans-serif;font-size:15px'>{message}</p>"
                f"<p style='color:#718096;font-size:12px;margin-top:16px'>"
                f"Smart Queue Management System — {get_setting('university_name','')}</p>")
        send_email(u["email"], subject or "Smart Queue Notification", html)

def notify_by_ticket(ticket_no, message, subject=None):
    """Convenience: notify the student who owns ticket_no."""
    with get_db() as c:
        t = c.execute("SELECT student_id FROM tickets WHERE ticket_no=?", (ticket_no,)).fetchone()
    if t:
        notify(t["student_id"], message, subject)

# ─────────────────────────────────────────────────────────
# QUEUE HELPERS
# ─────────────────────────────────────────────────────────
def gen_ticket_no(service):
    prefix = service[:2].upper()
    suffix = "".join(random.choices(string.digits, k=4))
    return f"{prefix}-{suffix}"

def calc_estimated_wait(service, priority):
    with get_db() as c:
        waiting = c.execute(
            "SELECT COUNT(*) FROM tickets WHERE service=? AND status='waiting'", (service,)
        ).fetchone()[0]
        active = c.execute(
            "SELECT COUNT(*) FROM counters WHERE service=? AND is_active=1", (service,)
        ).fetchone()[0] or 1
    discount = {1: 1.0, 2: 0.6, 3: 0.3}[priority]
    return max(int((waiting / active) * SERVICES[service]["avg_minutes"] * discount), 1)

# ─────────────────────────────────────────────────────────
# AUTH ROUTES
# ─────────────────────────────────────────────────────────
@app.route("/login", methods=["GET", "POST"])
def login():
    error = None
    if request.method == "POST":
        uid = request.form["user_id"].strip()
        pw  = request.form["password"]
        with get_db() as c:
            u = c.execute("SELECT * FROM users WHERE user_id=?", (uid,)).fetchone()
        if not u:
            error = "Invalid ID or password."
        elif not u["is_active"]:
            error = "This account has been deactivated. Contact the administrator."
        elif u["locked_until"] and datetime.now() < datetime.fromisoformat(u["locked_until"]):
            mins = int((datetime.fromisoformat(u["locked_until"]) - datetime.now()).seconds / 60) + 1
            error = f"Account locked. Try again in {mins} minute(s)."
        elif u["password"] != hash_pw(pw):
            fails  = (u["failed_logins"] or 0) + 1
            locked = (datetime.now() + timedelta(minutes=15)).isoformat() if fails >= 5 else None
            with get_db() as c:
                c.execute("UPDATE users SET failed_logins=?, locked_until=? WHERE user_id=?",
                          (fails, locked, uid))
            error = ("Account locked for 15 minutes." if locked
                     else f"Invalid ID or password. {5 - fails} attempt(s) remaining.")
        else:
            with get_db() as c:
                c.execute("UPDATE users SET failed_logins=0, locked_until=NULL, last_login=? WHERE user_id=?",
                          (now_str(), uid))
            session.update({"user_id": u["user_id"], "full_name": u["full_name"],
                            "role": u["role"], "email": u["email"] or ""})
            audit(uid, "LOGIN")
            return redirect(url_for("staff_dashboard") if u["role"] in ("admin","staff")
                            else request.args.get("next") or url_for("index"))
    return render_template("login.html", error=error)

@app.route("/register", methods=["GET", "POST"])
def register():
    error = None
    if request.method == "POST":
        uid   = request.form["user_id"].strip()
        name  = request.form["full_name"].strip()
        email = request.form["email"].strip()
        phone = request.form["phone"].strip()
        pw    = request.form["password"]
        if not all([uid, name, pw]):
            error = "Student ID, full name and password are required."
        elif len(pw) < 8:
            error = "Password must be at least 8 characters."
        else:
            try:
                with get_db() as c:
                    c.execute(
                        "INSERT INTO users (user_id,full_name,email,phone,password,role,created_at) VALUES (?,?,?,?,?,?,?)",
                        (uid, name, email, phone, hash_pw(pw), "student", now_str())
                    )
                session.update({"user_id": uid, "full_name": name, "role": "student", "email": email})
                audit(uid, "REGISTER")
                return redirect(url_for("index"))
            except Exception as _ie:
                if 'unique' not in str(_ie).lower() and 'duplicate' not in str(_ie).lower():
                    raise
                    raise
                error = "That Student ID is already registered."
    return render_template("register.html", error=error)

@app.route("/logout")
def logout():
    if session.get("user_id"):
        audit(session["user_id"], "LOGOUT")
    session.clear()
    return redirect(url_for("login"))

@app.route("/forgot-password", methods=["GET", "POST"])
def forgot_password():
    msg = None
    if request.method == "POST":
        email = request.form["email"].strip()
        with get_db() as c:
            u = c.execute("SELECT * FROM users WHERE email=?", (email,)).fetchone()
        if u:
            token   = secrets.token_urlsafe(32)
            expires = (datetime.now() + timedelta(hours=1)).isoformat()
            with get_db() as c:
                c.execute("UPDATE users SET reset_token=?, reset_expires=? WHERE email=?",
                          (token, expires, email))
            reset_url = url_for("reset_password", token=token, _external=True)
            send_email(email, "Password Reset — Smart Queue",
                       f"<p>Click the link below to reset your password (valid for 1 hour):</p>"
                       f"<p><a href='{reset_url}'>{reset_url}</a></p>")
        msg = "If that email is registered, a reset link has been sent."
    return render_template("forgot_password.html", msg=msg)

@app.route("/reset-password/<token>", methods=["GET", "POST"])
def reset_password(token):
    with get_db() as c:
        u = c.execute(
            "SELECT * FROM users WHERE reset_token=? AND reset_expires > ?",
            (token, now_str())
        ).fetchone()
    if not u:
        return render_template("reset_password.html", error="Invalid or expired reset link.", token=token)
    error = None
    if request.method == "POST":
        pw  = request.form["password"]
        pw2 = request.form["password2"]
        if len(pw) < 8:
            error = "Password must be at least 8 characters."
        elif pw != pw2:
            error = "Passwords do not match."
        else:
            with get_db() as c:
                c.execute("UPDATE users SET password=?, reset_token=NULL, reset_expires=NULL WHERE id=?",
                          (hash_pw(pw), u["id"]))
            return redirect(url_for("login"))
    return render_template("reset_password.html", error=error, token=token)

# ─────────────────────────────────────────────────────────
# STUDENT PORTAL
# ─────────────────────────────────────────────────────────
@app.route("/")
@role_required("student")
def index():
    sid = current_user()
    with get_db() as c:
        queues, svc_cfg = {}, {}
        for k, v in SERVICES.items():
            cnt = c.execute(
                "SELECT COUNT(*) FROM tickets WHERE service=? AND status='waiting'", (k,)
            ).fetchone()[0]
            cfg = c.execute("SELECT * FROM service_config WHERE service=?", (k,)).fetchone()
            svc_cfg[k] = dict(cfg) if cfg else {}
            queues[k]  = {**v, "waiting": cnt,
                          "est_wait":  calc_estimated_wait(k, 1),
                          "is_paused": svc_cfg[k].get("is_paused", 0),
                          "max_queue": svc_cfg[k].get("max_queue", 100)}

        unread = c.execute(
            "SELECT COUNT(*) FROM notifications WHERE student_id=? AND is_read=0", (sid,)
        ).fetchone()[0]
        active_ticket = c.execute(
            "SELECT * FROM tickets WHERE student_id=? AND status IN ('waiting','serving') LIMIT 1", (sid,)
        ).fetchone()
        announcements = c.execute(
            "SELECT * FROM announcements WHERE is_active=1 ORDER BY created_at DESC LIMIT 5"
        ).fetchall()
        my_history = c.execute(
            "SELECT * FROM tickets WHERE student_id=? ORDER BY created_at DESC LIMIT 10", (sid,)
        ).fetchall()

    return render_template("index.html", queues=queues, unread=unread,
                           active_ticket=active_ticket, announcements=announcements,
                           my_history=my_history,
                           student_name=session.get("full_name", ""))

@app.route("/join", methods=["POST"])
@role_required("student")
def join_queue():
    data     = request.get_json()
    sid      = current_user()
    sname    = session.get("full_name", "")
    service  = data.get("service", "")
    priority = int(data.get("priority", 1))
    notes    = data.get("notes", "").strip()

    if service not in SERVICES:
        return jsonify({"success": False, "error": "Invalid service."}), 400

    with get_db() as c:
        cfg = c.execute("SELECT * FROM service_config WHERE service=?", (service,)).fetchone()
        if cfg and cfg["is_paused"]:
            return jsonify({"success": False,
                            "error": f"This service is currently paused. {cfg['pause_reason'] or ''} Please try later or book an appointment."}), 400
        q_count = c.execute(
            "SELECT COUNT(*) FROM tickets WHERE service=? AND status='waiting'", (service,)
        ).fetchone()[0]
        max_q = cfg["max_queue"] if cfg else 100
        if q_count >= max_q:
            return jsonify({"success": False,
                            "error": f"Queue is full ({max_q} maximum). Please try later or book an appointment."}), 400
        existing = c.execute(
            "SELECT ticket_no FROM tickets WHERE student_id=? AND status IN ('waiting','serving')", (sid,)
        ).fetchone()
        if existing:
            return jsonify({"success": False,
                            "error": f"You already have an active ticket ({existing['ticket_no']}). Please wait for it to complete."}), 409

        ticket_no = gen_ticket_no(service)
        c.execute(
            "INSERT INTO tickets (ticket_no,student_id,student_name,service,priority,status,created_at,notes) VALUES (?,?,?,?,?,?,?,?)",
            (ticket_no, sid, sname, service, priority, "waiting", now_str(), notes)
        )
        # Hourly stats
        hour  = datetime.now().hour
        today = datetime.now().strftime("%Y-%m-%d")
        c.execute("INSERT INTO hourly_stats (date,hour,service,count) VALUES (?,?,?,0) ON CONFLICT DO NOTHING",
                  (today, hour, service))
        c.execute("UPDATE hourly_stats SET count=count+1 WHERE date=? AND hour=? AND service=?",
                  (today, hour, service))

    est = calc_estimated_wait(service, priority)
    notify(sid,
           f"Queue joined: {SERVICES[service]['name']}. "
           f"Ticket: {ticket_no}. Estimated wait: ~{est} min.",
           "Queue Ticket Issued")
    audit(sid, "JOIN_QUEUE", ticket_no, f"service={service} priority={priority}")
    return jsonify({"success": True, "ticket_no": ticket_no,
                    "service": SERVICES[service]["name"],
                    "priority": PRIORITY_LABELS[priority], "est_wait": est})

@app.route("/requeue/<ticket_no>", methods=["POST"])
@role_required("student")
def requeue(ticket_no):
    sid = current_user()
    with get_db() as c:
        t = c.execute(
            "SELECT * FROM tickets WHERE ticket_no=? AND student_id=?", (ticket_no, sid)
        ).fetchone()
        if not t or t["status"] != "no_show":
            return jsonify({"success": False, "error": "Can only re-queue a no-show ticket."}), 400
        new_no  = gen_ticket_no(t["service"])
        recount = (t["requeue_count"] or 0) + 1
        c.execute(
            "INSERT INTO tickets (ticket_no,student_id,student_name,service,priority,status,created_at,notes,requeue_count) VALUES (?,?,?,?,?,?,?,?,?)",
            (new_no, sid, t["student_name"], t["service"], t["priority"],
             "waiting", now_str(), t["notes"], recount)
        )
    push_notification(sid, f"Re-queued successfully. New ticket: {new_no}")
    return jsonify({"success": True, "ticket_no": new_no})

@app.route("/status/<ticket_no>")
@login_required
def ticket_status(ticket_no):
    with get_db() as c:
        t = c.execute("SELECT * FROM tickets WHERE ticket_no=?", (ticket_no,)).fetchone()
        if not t:
            return jsonify({"error": "Ticket not found"}), 404
        position = None
        if t["status"] == "waiting":
            position = c.execute(
                """SELECT COUNT(*) FROM tickets
                   WHERE service=? AND status='waiting'
                   AND (priority > ? OR (priority=? AND created_at <= ?))""",
                (t["service"], t["priority"], t["priority"], t["created_at"])
            ).fetchone()[0]
        rated = c.execute(
            "SELECT id FROM feedback WHERE ticket_no=?", (ticket_no,)
        ).fetchone() is not None
    r = dict(t)
    r.update({"position": position,
               "service_name": SERVICES.get(t["service"], {}).get("name", ""),
               "priority_label": PRIORITY_LABELS.get(t["priority"], "Normal"),
               "already_rated": rated})
    return jsonify(r)

@app.route("/feedback", methods=["POST"])
@role_required("student")
def submit_feedback():
    data    = request.get_json()
    sid     = current_user()
    tn      = data.get("ticket_no", "")
    rating  = int(data.get("rating", 0))
    comment = data.get("comment", "").strip()
    if not tn or not (1 <= rating <= 5):
        return jsonify({"success": False, "error": "Invalid feedback."}), 400
    with get_db() as c:
        t = c.execute(
            "SELECT * FROM tickets WHERE ticket_no=? AND student_id=?", (tn, sid)
        ).fetchone()
        if not t:
            return jsonify({"success": False, "error": "Ticket not found."}), 404
        if c.execute("SELECT id FROM feedback WHERE ticket_no=?", (tn,)).fetchone():
            return jsonify({"success": False, "error": "You have already rated this ticket."}), 409
        c.execute(
            "INSERT INTO feedback (ticket_no,student_id,service,rating,comment,created_at) VALUES (?,?,?,?,?,?)",
            (tn, sid, t["service"], rating, comment, now_str())
        )
    return jsonify({"success": True})

@app.route("/notifications")
@login_required
def notifications_page():
    sid = current_user()
    with get_db() as c:
        notes = c.execute(
            "SELECT * FROM notifications WHERE student_id=? ORDER BY created_at DESC LIMIT 50", (sid,)
        ).fetchall()
        c.execute("UPDATE notifications SET is_read=1 WHERE student_id=?", (sid,))
    return render_template("notifications.html", notifications=notes,
                           student_name=session.get("full_name", ""), unread=0)

@app.route("/api/unread_count")
@login_required
def unread_count():
    sid = current_user()
    with get_db() as c:
        cnt = c.execute(
            "SELECT COUNT(*) FROM notifications WHERE student_id=? AND is_read=0", (sid,)
        ).fetchone()[0]
    return jsonify({"count": cnt})

@app.route("/appointments")
@role_required("student")
def appointments():
    sid = current_user()
    with get_db() as c:
        my_appts = c.execute(
            "SELECT * FROM appointments WHERE student_id=? ORDER BY appt_date, appt_time", (sid,)
        ).fetchall()
    slots = []
    for d in range(1, 8):
        day = datetime.now() + timedelta(days=d)
        if day.weekday() < 5:
            for h in range(9, 16):
                slots.append({"date": day.strftime("%Y-%m-%d"),
                              "label": day.strftime("%a, %d %b"),
                              "time": f"{h:02d}:00"})
    return render_template("appointments.html", services=SERVICES, appointments=my_appts,
                           slots=slots, student_name=session.get("full_name", ""), unread=0)

@app.route("/appointments/book", methods=["POST"])
@role_required("student")
def book_appointment():
    data  = request.get_json()
    sid   = current_user()
    sname = session.get("full_name", "")
    svc   = data.get("service", "")
    date  = data.get("date", "")
    time  = data.get("time", "")
    notes = data.get("notes", "").strip()
    if svc not in SERVICES or not date or not time:
        return jsonify({"success": False, "error": "Invalid booking details."}), 400
    with get_db() as c:
        clash = c.execute(
            "SELECT id FROM appointments WHERE student_id=? AND appt_date=? AND status='booked'",
            (sid, date)
        ).fetchone()
        if clash:
            return jsonify({"success": False, "error": "You already have a booking on that date."}), 409
        c.execute(
            "INSERT INTO appointments (student_id,student_name,service,appt_date,appt_time,notes,created_at) VALUES (?,?,?,?,?,?,?)",
            (sid, sname, svc, date, time, notes, now_str())
        )
    notify(sid,
           f"Appointment confirmed: {SERVICES[svc]['name']} on {date} at {time}. Please arrive on time.",
           "Appointment Confirmed")
    return jsonify({"success": True})

@app.route("/appointments/cancel/<int:appt_id>", methods=["POST"])
@role_required("student")
def cancel_appointment(appt_id):
    sid = current_user()
    with get_db() as c:
        c.execute("UPDATE appointments SET status='cancelled' WHERE id=? AND student_id=?", (appt_id, sid))
    return jsonify({"success": True})

# ─────────────────────────────────────────────────────────
# STAFF PORTAL
# ─────────────────────────────────────────────────────────
@app.route("/staff")
@role_required("staff", "admin")
def staff_dashboard():
    with get_db() as c:
        counters     = c.execute("SELECT * FROM counters ORDER BY counter_no").fetchall()
        waiting      = c.execute(
            "SELECT * FROM tickets WHERE status='waiting' ORDER BY priority DESC, created_at"
        ).fetchall()
        serving      = c.execute(
            "SELECT * FROM tickets WHERE status='serving' ORDER BY called_at"
        ).fetchall()
        todays_appts = c.execute(
            "SELECT * FROM appointments WHERE appt_date=? AND status='booked' ORDER BY appt_time",
            (datetime.now().strftime("%Y-%m-%d"),)
        ).fetchall()
        fb_avg = c.execute(
            "SELECT service, ROUND(AVG(rating),1) as avg_r, COUNT(*) as cnt FROM feedback GROUP BY service"
        ).fetchall()
        svc_cfg = {r["service"]: dict(r)
                   for r in c.execute("SELECT * FROM service_config").fetchall()}
    return render_template("staff.html",
                           counters=counters, waiting=waiting, serving=serving,
                           services=SERVICES, priority_labels=PRIORITY_LABELS,
                           todays_appts=todays_appts,
                           fb_avg={r["service"]: r for r in fb_avg},
                           svc_cfg=svc_cfg, role=current_role())

@app.route("/staff/call_next", methods=["POST"])
@role_required("staff", "admin")
def call_next():
    data       = request.get_json()
    counter_no = int(data["counter_no"])
    service    = data["service"]
    with get_db() as c:
        ticket = c.execute(
            "SELECT * FROM tickets WHERE service=? AND status='waiting' ORDER BY priority DESC, created_at LIMIT 1",
            (service,)
        ).fetchone()
        if not ticket:
            return jsonify({"success": False, "message": "No waiting tickets for this service."}), 200
        c.execute(
            "UPDATE tickets SET status='serving', called_at=?, counter=? WHERE id=?",
            (now_str(), counter_no, ticket["id"])
        )
        c.execute(
            "UPDATE counters SET current_ticket=?, staff_id=? WHERE counter_no=?",
            (ticket["ticket_no"], current_user(), counter_no)
        )
    notify(ticket["student_id"],
           f"Your ticket {ticket['ticket_no']} is being called. Please proceed to Counter {counter_no} now.",
           "Your Turn — Please Proceed")
    audit(current_user(), "CALL_NEXT", ticket["ticket_no"], f"counter={counter_no}")
    return jsonify({"success": True,
                    "ticket_no": ticket["ticket_no"],
                    "student_name": ticket["student_name"]})

@app.route("/staff/complete", methods=["POST"])
@role_required("staff", "admin")
def complete_ticket():
    data = request.get_json()
    with get_db() as c:
        c.execute("UPDATE tickets SET status='completed', completed_at=? WHERE ticket_no=?",
                  (now_str(), data["ticket_no"]))
        c.execute("UPDATE counters SET current_ticket=NULL WHERE counter_no=?", (data["counter_no"],))
    notify_by_ticket(data["ticket_no"],
                     "Your service is complete. Thank you for visiting! "
                     "Please take a moment to rate your experience.",
                     "Service Complete")
    audit(current_user(), "COMPLETE", data["ticket_no"])
    return jsonify({"success": True})

@app.route("/staff/no_show", methods=["POST"])
@role_required("staff", "admin")
def no_show():
    data = request.get_json()
    with get_db() as c:
        c.execute("UPDATE tickets SET status='no_show', completed_at=? WHERE ticket_no=?",
                  (now_str(), data["ticket_no"]))
        c.execute("UPDATE counters SET current_ticket=NULL WHERE counter_no=?", (data["counter_no"],))
    notify_by_ticket(data["ticket_no"],
                     f"Ticket {data['ticket_no']} was marked as no-show. "
                     "You may re-queue from the student portal.",
                     "No-Show Recorded")
    audit(current_user(), "NO_SHOW", data["ticket_no"])
    return jsonify({"success": True})

@app.route("/staff/toggle_counter", methods=["POST"])
@role_required("staff", "admin")
def toggle_counter():
    data = request.get_json()
    with get_db() as c:
        cur = c.execute(
            "SELECT is_active FROM counters WHERE counter_no=?", (data["counter_no"],)
        ).fetchone()["is_active"]
        c.execute("UPDATE counters SET is_active=? WHERE counter_no=?",
                  (0 if cur else 1, data["counter_no"]))
    audit(current_user(), "TOGGLE_COUNTER", str(data["counter_no"]),
          "closed" if cur else "opened")
    return jsonify({"success": True})

@app.route("/staff/toggle_pause", methods=["POST"])
@role_required("staff", "admin")
def toggle_pause():
    data    = request.get_json()
    service = data.get("service")
    reason  = data.get("reason", "")
    with get_db() as c:
        cur = c.execute(
            "SELECT is_paused FROM service_config WHERE service=?", (service,)
        ).fetchone()["is_paused"]
        c.execute("UPDATE service_config SET is_paused=?, pause_reason=? WHERE service=?",
                  (0 if cur else 1, reason, service))
    audit(current_user(),
          "RESUME_SERVICE" if cur else "PAUSE_SERVICE", service)
    return jsonify({"success": True, "paused": not cur})

# ─────────────────────────────────────────────────────────
# ADMIN ROUTES
# ─────────────────────────────────────────────────────────
@app.route("/admin/users")
@role_required("admin")
def admin_users():
    with get_db() as c:
        users = c.execute("SELECT * FROM users ORDER BY role, created_at").fetchall()
    return render_template("admin_users.html", users=users, role=current_role())

@app.route("/admin/users/create", methods=["POST"])
@role_required("admin")
def create_user():
    data  = request.get_json()
    uid   = data.get("user_id", "").strip()
    name  = data.get("full_name", "").strip()
    email = data.get("email", "").strip()
    phone = data.get("phone", "").strip()
    role  = data.get("role", "student")
    pw    = data.get("password", "").strip()
    if not all([uid, name, pw]) or role not in ("student", "staff", "admin"):
        return jsonify({"success": False, "error": "Invalid input."}), 400
    try:
        with get_db() as c:
            c.execute(
                "INSERT INTO users (user_id,full_name,email,phone,password,role,created_at) VALUES (?,?,?,?,?,?,?)",
                (uid, name, email, phone, hash_pw(pw), role, now_str())
            )
        audit(current_user(), "CREATE_USER", uid, f"role={role}")
        return jsonify({"success": True})
    except Exception as _ie:
        if 'unique' not in str(_ie).lower() and 'duplicate' not in str(_ie).lower():
            raise
        return jsonify({"success": False, "error": "That User ID already exists."}), 409

@app.route("/admin/users/toggle", methods=["POST"])
@role_required("admin")
def toggle_user():
    data = request.get_json()
    uid  = data.get("uid", "").strip()
    if not uid:
        return jsonify({"success": False, "error": "No user ID provided."}), 400
    if uid == current_user():
        return jsonify({"success": False, "error": "You cannot deactivate your own account."}), 400
    with get_db() as conn:
        row = conn.execute("SELECT is_active FROM users WHERE user_id=?", (uid,)).fetchone()
        if not row:
            return jsonify({"success": False, "error": "User not found."}), 404
        cur = row["is_active"]
        conn.execute("UPDATE users SET is_active=? WHERE user_id=?", (0 if cur else 1, uid))
    audit(current_user(), "TOGGLE_USER", uid, "deactivated" if cur else "activated")
    return jsonify({"success": True})

@app.route("/admin/users/reset_password", methods=["POST"])
@role_required("admin")
def admin_reset_password():
    data = request.get_json()
    uid  = data.get("uid", "").strip()
    pw   = data.get("password", "").strip()
    if not uid:
        return jsonify({"success": False, "error": "No user ID provided."}), 400
    if len(pw) < 8:
        return jsonify({"success": False, "error": "Password must be at least 8 characters."}), 400
    with get_db() as conn:
        conn.execute(
            "UPDATE users SET password=?, failed_logins=0, locked_until=NULL WHERE user_id=?",
            (hash_pw(pw), uid)
        )
    audit(current_user(), "RESET_PASSWORD", uid)
    return jsonify({"success": True})

@app.route("/admin/settings", methods=["GET", "POST"])
@role_required("admin")
def admin_settings():
    if request.method == "POST":
        for k in ["email_enabled", "smtp_host", "smtp_port",
                  "smtp_user", "smtp_password", "smtp_from_name", "university_name"]:
            if k in request.form:
                set_setting(k, request.form[k])
        for svc in SERVICES:
            with get_db() as c:
                c.execute(
                    "UPDATE service_config SET open_time=?, close_time=?, max_queue=? WHERE service=?",
                    (request.form.get(f"open_{svc}", "08:00"),
                     request.form.get(f"close_{svc}", "17:00"),
                     int(request.form.get(f"max_{svc}", 100)),
                     svc)
                )
        audit(current_user(), "UPDATE_SETTINGS")
        flash("Settings saved successfully.", "success")
        return redirect(url_for("admin_settings"))
    settings = get_all_settings()
    with get_db() as c:
        svc_cfg = {r["service"]: dict(r)
                   for r in c.execute("SELECT * FROM service_config").fetchall()}
    return render_template("admin_settings.html", settings=settings,
                           services=SERVICES, svc_cfg=svc_cfg, role=current_role())



# ─────────────────────────────────────────────────────────
# ── SERVICE MANAGEMENT (admin only) ──────────────────────
# ─────────────────────────────────────────────────────────
@app.route("/admin/services/add", methods=["POST"])
@role_required("admin")
def add_service():
    data        = request.get_json()
    name        = data.get("name", "").strip()
    avg_minutes = int(data.get("avg_minutes", 10))
    if not name:
        return jsonify({"success": False, "error": "Service name is required."}), 400
    if avg_minutes < 1 or avg_minutes > 120:
        return jsonify({"success": False,
                        "error": "Average duration must be between 1 and 120 minutes."}), 400
    # Generate a safe key from the name
    import re
    key = re.sub(r"[^a-z0-9]+", "_", name.lower()).strip("_")[:30]
    if not key:
        return jsonify({"success": False, "error": "Invalid service name."}), 400
    # Ensure key is unique
    all_svcs = get_services()
    original_key = key
    counter = 1
    while key in all_svcs:
        key = f"{original_key}_{counter}"
        counter += 1
    try:
        with get_db() as conn:
            conn.execute(
                "INSERT INTO custom_services (key,name,avg_minutes,is_active,created_at) VALUES (?,?,?,1,?)",
                (key, name, avg_minutes, now_str())
            )
            # Auto-create service_config entry for it
            conn.execute(
                "INSERT INTO service_config (service) VALUES (?) ON CONFLICT DO NOTHING", (key,)
            )
    except Exception as e:
        return jsonify({"success": False, "error": str(e)}), 500
    audit(current_user(), "ADD_SERVICE", key, f"name={name} avg={avg_minutes}min")
    return jsonify({"success": True, "key": key, "name": name})


@app.route("/admin/services/edit/<svc_key>", methods=["POST"])
@role_required("admin")
def edit_service(svc_key):
    # Only custom services can be edited
    with get_db() as conn:
        existing = conn.execute(
            "SELECT * FROM custom_services WHERE key=?", (svc_key,)
        ).fetchone()
    if not existing:
        return jsonify({"success": False,
                        "error": "Built-in services cannot be renamed."}), 400
    data        = request.get_json()
    name        = data.get("name", "").strip()
    avg_minutes = int(data.get("avg_minutes", 10))
    if not name:
        return jsonify({"success": False, "error": "Service name is required."}), 400
    with get_db() as conn:
        conn.execute(
            "UPDATE custom_services SET name=?, avg_minutes=? WHERE key=?",
            (name, avg_minutes, svc_key)
        )
    audit(current_user(), "EDIT_SERVICE", svc_key, f"name={name} avg={avg_minutes}min")
    return jsonify({"success": True})


@app.route("/admin/services/delete/<svc_key>", methods=["POST"])
@role_required("admin")
def delete_service(svc_key):
    # Only custom services can be deleted
    if svc_key in DEFAULT_SERVICES:
        return jsonify({"success": False,
                        "error": "Built-in services cannot be deleted."}), 400
    # Check no active tickets or counters
    with get_db() as conn:
        active_tickets = conn.execute(
            "SELECT COUNT(*) FROM tickets WHERE service=? AND status IN ('waiting','serving')",
            (svc_key,)
        ).fetchone()[0]
        if active_tickets > 0:
            return jsonify({"success": False,
                            "error": f"There are {active_tickets} active ticket(s) for this service. "
                                     "Clear them first."}), 400
        conn.execute("UPDATE custom_services SET is_active=0 WHERE key=?", (svc_key,))
        # Close any counters assigned to this service
        conn.execute(
            "UPDATE counters SET is_active=0 WHERE service=?", (svc_key,)
        )
    audit(current_user(), "DELETE_SERVICE", svc_key)
    return jsonify({"success": True})

# ─────────────────────────────────────────────────────────
# ── COUNTER MANAGEMENT (admin only) ──────────────────────
# ─────────────────────────────────────────────────────────
@app.route("/admin/counters")
@role_required("admin")
def admin_counters():
    with get_db() as conn:
        counters = conn.execute(
            "SELECT * FROM counters ORDER BY counter_no"
        ).fetchall()
        custom_svcs = conn.execute(
            "SELECT * FROM custom_services WHERE is_active=1 ORDER BY created_at"
        ).fetchall()
    return render_template("admin_counters.html",
                           counters=counters,
                           services=get_services(),
                           custom_services=custom_svcs,
                           role=current_role())

@app.route("/admin/counters/add", methods=["POST"])
@role_required("admin")
def add_counter():
    data    = request.get_json()
    service = data.get("service", "")
    if service not in SERVICES:
        return jsonify({"success": False, "error": "Invalid service."}), 400
    with get_db() as conn:
        row = conn.execute("SELECT MAX(counter_no) as m FROM counters").fetchone()
        next_no = (row["m"] or 0) + 1
        conn.execute(
            "INSERT INTO counters (counter_no, service, is_active) VALUES (?,?,1)",
            (next_no, service)
        )
    audit(current_user(), "ADD_COUNTER", str(next_no), f"service={service}")
    return jsonify({"success": True, "counter_no": next_no,
                    "service_name": SERVICES[service]["name"]})

@app.route("/admin/counters/delete/<int:counter_no>", methods=["POST"])
@role_required("admin")
def delete_counter(counter_no):
    with get_db() as conn:
        active = conn.execute(
            "SELECT current_ticket FROM counters WHERE counter_no=?",
            (counter_no,)
        ).fetchone()
        if active and active["current_ticket"]:
            return jsonify({"success": False,
                            "error": f"Counter {counter_no} is currently serving a ticket. "
                                     "Mark it complete or no-show first."}), 400
        conn.execute("DELETE FROM counters WHERE counter_no=?", (counter_no,))
    audit(current_user(), "DELETE_COUNTER", str(counter_no))
    return jsonify({"success": True})

@app.route("/admin/counters/edit/<int:counter_no>", methods=["POST"])
@role_required("admin")
def edit_counter(counter_no):
    data    = request.get_json()
    service = data.get("service", "")
    if service not in SERVICES:
        return jsonify({"success": False, "error": "Invalid service."}), 400
    with get_db() as conn:
        conn.execute(
            "UPDATE counters SET service=? WHERE counter_no=?",
            (service, counter_no)
        )
    audit(current_user(), "EDIT_COUNTER", str(counter_no), f"service={service}")
    return jsonify({"success": True})

@app.route("/admin/test_notification", methods=["POST"])
@role_required("admin")
def test_notification():
    data    = request.get_json()
    channel = data.get("channel", "all")
    sid     = current_user()
    with get_db() as c:
        u = c.execute("SELECT * FROM users WHERE user_id=?", (sid,)).fetchone()
    results = {}
    msg     = ("This is a test notification from the Smart Queue Management System. "
               "Your notification settings are working correctly.")
    if channel in ("inapp", "all"):
        push_notification(sid, "[TEST] " + msg)
        results["inapp"] = "sent"
    if channel in ("email", "all"):
        ok = send_email(u["email"] if u else "", "SmartQueue — Test Notification",
                        f"<p style='font-family:Arial'>{msg}</p>")
        results["email"] = "sent" if ok else "failed — check SMTP settings and ensure email is enabled"
    audit(sid, "TEST_NOTIFICATION", channel, str(results))
    return jsonify({"success": True, "results": results})

@app.route("/admin/announcements", methods=["GET", "POST"])
@role_required("admin")
def admin_announcements():
    if request.method == "POST":
        data = request.get_json()
        with get_db() as c:
            c.execute(
                "INSERT INTO announcements (title,body,type,is_active,created_by,created_at,expires_at) VALUES (?,?,?,?,?,?,?)",
                (data["title"], data["body"], data.get("type", "info"), 1,
                 current_user(), now_str(), data.get("expires_at") or None)
            )
        audit(current_user(), "CREATE_ANNOUNCEMENT", data["title"])
        return jsonify({"success": True})
    with get_db() as c:
        anns = c.execute("SELECT * FROM announcements ORDER BY created_at DESC").fetchall()
    return render_template("admin_announcements.html", announcements=anns, role=current_role())

@app.route("/admin/announcements/toggle/<int:ann_id>", methods=["POST"])
@role_required("admin")
def toggle_announcement(ann_id):
    with get_db() as c:
        cur = c.execute("SELECT is_active FROM announcements WHERE id=?", (ann_id,)).fetchone()["is_active"]
        c.execute("UPDATE announcements SET is_active=? WHERE id=?", (0 if cur else 1, ann_id))
    return jsonify({"success": True})

@app.route("/admin/announcements/delete/<int:ann_id>", methods=["POST"])
@role_required("admin")
def delete_announcement(ann_id):
    with get_db() as c:
        c.execute("DELETE FROM announcements WHERE id=?", (ann_id,))
    audit(current_user(), "DELETE_ANNOUNCEMENT", str(ann_id))
    return jsonify({"success": True})

@app.route("/admin/audit")
@role_required("admin")
def audit_log_page():
    with get_db() as c:
        logs = c.execute(
            "SELECT * FROM audit_log ORDER BY created_at DESC LIMIT 200"
        ).fetchall()
    return render_template("admin_audit.html", logs=logs, role=current_role())

@app.route("/admin/bulk_reset", methods=["POST"])
@role_required("admin")
def bulk_reset():
    data    = request.get_json()
    service = data.get("service", "all")
    with get_db() as c:
        if service == "all":
            c.execute("UPDATE tickets SET status='cancelled', completed_at=? WHERE status='waiting'",
                      (now_str(),))
            c.execute("UPDATE counters SET current_ticket=NULL")
        else:
            c.execute(
                "UPDATE tickets SET status='cancelled', completed_at=? WHERE service=? AND status='waiting'",
                (now_str(), service)
            )
            c.execute("UPDATE counters SET current_ticket=NULL WHERE service=?", (service,))
    audit(current_user(), "BULK_RESET", service)
    return jsonify({"success": True})

# ─────────────────────────────────────────────────────────
# ANALYTICS & EXPORTS
# ─────────────────────────────────────────────────────────
@app.route("/analytics")
@role_required("staff", "admin")
def analytics():
    today = datetime.now().strftime("%Y-%m-%d")
    with get_db() as c:
        stats = {}
        for k, v in SERVICES.items():
            served = c.execute(
                "SELECT COUNT(*) FROM tickets WHERE service=? AND status='completed' AND DATE(created_at)=?",
                (k, today)
            ).fetchone()[0]
            avg_wait = c.execute(
                "SELECT AVG((julianday(called_at)-julianday(created_at))*1440) FROM tickets WHERE service=? AND called_at IS NOT NULL AND DATE(created_at)=?",
                (k, today)
            ).fetchone()[0] or 0
            avg_serve = c.execute(
                "SELECT AVG((julianday(completed_at)-julianday(called_at))*1440) FROM tickets WHERE service=? AND status='completed' AND called_at IS NOT NULL AND DATE(created_at)=?",
                (k, today)
            ).fetchone()[0] or 0
            waiting_now = c.execute(
                "SELECT COUNT(*) FROM tickets WHERE service=? AND status='waiting'", (k,)
            ).fetchone()[0]
            avg_rating = c.execute(
                "SELECT ROUND(AVG(rating),1) FROM feedback WHERE service=?", (k,)
            ).fetchone()[0] or 0
            stats[k] = {"name": v["name"], "served_today": served,
                        "avg_wait_min": round(avg_wait, 1),
                        "avg_serve_min": round(avg_serve, 1),
                        "waiting_now": waiting_now, "avg_rating": avg_rating}

        total_today = c.execute(
            "SELECT COUNT(*) FROM tickets WHERE status='completed' AND DATE(created_at)=?", (today,)
        ).fetchone()[0]
        no_shows    = c.execute(
            "SELECT COUNT(*) FROM tickets WHERE status='no_show' AND DATE(created_at)=?", (today,)
        ).fetchone()[0]
        total_fb    = c.execute("SELECT COUNT(*) FROM feedback").fetchone()[0]
        overall_r   = c.execute("SELECT ROUND(AVG(rating),1) FROM feedback").fetchone()[0] or 0

        hourly_data = {h: {k: 0 for k in SERVICES} for h in range(8, 18)}
        for row in c.execute("SELECT hour, service, count FROM hourly_stats WHERE date=?", (today,)):
            if row["hour"] in hourly_data:
                hourly_data[row["hour"]][row["service"]] = row["count"]

    return render_template("analytics.html", stats=stats, total_today=total_today,
                           no_shows=no_shows, total_feedback=total_fb, overall_rating=overall_r,
                           today=today, hourly_data=hourly_data, services=SERVICES,
                           role=current_role())

@app.route("/admin/export/csv")
@role_required("staff", "admin")
def export_csv():
    date_filter = request.args.get("date", datetime.now().strftime("%Y-%m-%d"))
    with get_db() as c:
        rows = c.execute(
            "SELECT * FROM tickets WHERE DATE(created_at)=? ORDER BY created_at", (date_filter,)
        ).fetchall()
    out = io.StringIO()
    w   = csv.writer(out)
    w.writerow(["Ticket No","Student ID","Name","Service","Priority","Status",
                "Created","Called","Completed","Counter","Notes","Re-queued"])
    for r in rows:
        w.writerow([r["ticket_no"], r["student_id"], r["student_name"],
                    SERVICES.get(r["service"], {}).get("name", ""),
                    PRIORITY_LABELS.get(r["priority"], "Normal"), r["status"],
                    r["created_at"], r["called_at"] or "", r["completed_at"] or "",
                    r["counter"] or "", r["notes"] or "", r["requeue_count"] or 0])
    out.seek(0)
    return send_file(io.BytesIO(out.getvalue().encode()), mimetype="text/csv",
                     as_attachment=True, download_name=f"queue_{date_filter}.csv")

@app.route("/admin/export/feedback_csv")
@role_required("staff", "admin")
def export_feedback_csv():
    with get_db() as c:
        rows = c.execute("SELECT * FROM feedback ORDER BY created_at DESC").fetchall()
    out = io.StringIO()
    w   = csv.writer(out)
    w.writerow(["Ticket No","Student ID","Service","Rating","Comment","Date"])
    for r in rows:
        w.writerow([r["ticket_no"], r["student_id"],
                    SERVICES.get(r["service"], {}).get("name", ""),
                    r["rating"], r["comment"] or "", r["created_at"]])
    out.seek(0)
    return send_file(io.BytesIO(out.getvalue().encode()), mimetype="text/csv",
                     as_attachment=True, download_name="feedback.csv")

@app.route("/admin/export/pdf")
@role_required("staff", "admin")
def export_pdf():
    date_filter = request.args.get("date", datetime.now().strftime("%Y-%m-%d"))
    with get_db() as c:
        rows = c.execute(
            "SELECT * FROM tickets WHERE DATE(created_at)=? ORDER BY created_at", (date_filter,)
        ).fetchall()
        fb = c.execute(
            "SELECT service, ROUND(AVG(rating),1) as avg_r, COUNT(*) as cnt FROM feedback WHERE DATE(created_at)=? GROUP BY service",
            (date_filter,)
        ).fetchall()
    return render_template("export_pdf.html", rows=rows, date=date_filter,
                           services=SERVICES, priority_labels=PRIORITY_LABELS,
                           feedback={r["service"]: r for r in fb}, now=datetime.now)


@app.route("/api/live_queue_stats")
@role_required("staff", "admin")
def live_queue_stats():
    """Returns live per-service queue stats for the staff dashboard counter cards."""
    with get_db() as conn:
        stats = {}
        for svc_key in SERVICES:
            rows = conn.execute(
                """SELECT priority, COUNT(*) as cnt
                   FROM tickets WHERE service=? AND status='waiting'
                   GROUP BY priority""",
                (svc_key,)
            ).fetchall()

            by_priority = {1: 0, 2: 0, 3: 0}
            for r in rows:
                by_priority[r["priority"]] = r["cnt"]

            total_waiting = sum(by_priority.values())

            # Next ticket to be called
            next_ticket = conn.execute(
                """SELECT ticket_no, priority, student_name
                   FROM tickets WHERE service=? AND status='waiting'
                   ORDER BY priority DESC, created_at ASC LIMIT 1""",
                (svc_key,)
            ).fetchone()

            # Active counters for this service
            active_counters = conn.execute(
                "SELECT COUNT(*) FROM counters WHERE service=? AND is_active=1",
                (svc_key,)
            ).fetchone()[0] or 1

            # Estimated wait for next person
            avg_min = SERVICES[svc_key]["avg_minutes"]
            est_wait = max(int((total_waiting / active_counters) * avg_min * 1.0), 0)

            # Currently being served at this service
            serving = conn.execute(
                """SELECT ticket_no, counter FROM tickets
                   WHERE service=? AND status='serving'""",
                (svc_key,)
            ).fetchall()

            stats[svc_key] = {
                "total_waiting": total_waiting,
                "urgent":  by_priority[3],
                "high":    by_priority[2],
                "normal":  by_priority[1],
                "est_wait_min": est_wait,
                "next_ticket":  dict(next_ticket) if next_ticket else None,
                "serving_count": len(serving),
                "serving": [dict(r) for r in serving],
            }

        # Also return per-counter current ticket info
        counters_live = {}
        for row in conn.execute("SELECT * FROM counters ORDER BY counter_no").fetchall():
            counters_live[row["counter_no"]] = {
                "is_active":     row["is_active"],
                "current_ticket": row["current_ticket"],
                "service":        row["service"],
            }

    return jsonify({"stats": stats, "counters": counters_live, "timestamp": now_str()})

# ─────────────────────────────────────────────────────────
# DISPLAY BOARD
# ─────────────────────────────────────────────────────────
@app.route("/health")
def health():
    """Health check endpoint for Render."""
    try:
        with get_db() as conn:
            conn.execute("SELECT 1")
        return "OK", 200
    except Exception as e:
        return str(e), 500

@app.route("/setup")
def setup():
    """One-time setup: create all database tables. Visit once after first deploy."""
    try:
        init_db()
        return "Database tables created successfully. Default accounts ready.<br>Admin: admin / Admin@123<br>Staff: staff01 / Staff@123", 200
    except Exception as e:
        import traceback
        return f"Setup error: {e}<br><pre>{traceback.format_exc()}</pre>", 500

@app.route("/display")
def display():
    return render_template("display.html", services=SERVICES)

@app.route("/api/display_data")
def display_data():
    with get_db() as c:
        serving  = c.execute(
            "SELECT ticket_no,student_name,service,counter FROM tickets WHERE status='serving' ORDER BY called_at"
        ).fetchall()
        counters = c.execute(
            "SELECT * FROM counters WHERE is_active=1 ORDER BY counter_no"
        ).fetchall()
        anns = c.execute(
            "SELECT title,body,type FROM announcements WHERE is_active=1 ORDER BY created_at DESC LIMIT 3"
        ).fetchall()
    return jsonify({"serving": [dict(r) for r in serving],
                    "counters": [dict(r) for r in counters],
                    "announcements": [dict(r) for r in anns],
                    "timestamp": now_str()})

@app.route("/api/queue_data")
@login_required
def queue_data():
    with get_db() as c:
        data = {k: c.execute(
            "SELECT COUNT(*) FROM tickets WHERE service=? AND status='waiting'", (k,)
        ).fetchone()[0] for k in SERVICES}
    return jsonify(data)

# ─────────────────────────────────────────────────────────
# CONTEXT PROCESSOR
# ─────────────────────────────────────────────────────────
@app.context_processor
def inject_globals():
    return {"now": datetime.now,
            "current_role": current_role,
            "current_user_id": current_user}

# ─────────────────────────────────────────────────────────
# Auto-initialise database when loaded by Gunicorn
import sys as _sys
try:
    init_db()
    print("[SQMS] Database initialised OK", file=_sys.stderr)
except Exception as _init_err:
    print(f"[SQMS] DB init failed: {_init_err}", file=_sys.stderr)

if __name__ == "__main__":
    init_db()
    print("\n╔══════════════════════════════════════════════════════════╗")
    print("║  Smart Queue Management System v4.0                     ║")
    print("╠══════════════════════════════════════════════════════════╣")
    print("║  Student Portal  →  http://127.0.0.1:5000/              ║")
    print("║  Staff Dashboard →  http://127.0.0.1:5000/staff         ║")
    print("║  Analytics       →  http://127.0.0.1:5000/analytics     ║")
    print("║  Display Board   →  http://127.0.0.1:5000/display       ║")
    print("╠══════════════════════════════════════════════════════════╣")
    print("║  Logins:                                                 ║")
    print("║    Admin:  admin   / Admin@123                          ║")
    print("║    Staff:  staff01 / Staff@123                          ║")
    print("║    (Register a new student account via /register)       ║")
    print("╚══════════════════════════════════════════════════════════╝\n")
    app.run(debug=True, port=5000)
