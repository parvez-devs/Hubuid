from __future__ import annotations

import csv
import hashlib
import io
import json
import logging
import os
import re
import secrets
import shutil
import sqlite3
import threading
import time
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
from functools import wraps
from logging.handlers import RotatingFileHandler
from pathlib import Path

from flask import Flask, Response, g, jsonify, render_template, request, send_file, session
from werkzeug.security import check_password_hash, generate_password_hash

from scraper import FacebookScraper, ScraperError

BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = Path(os.environ.get("XEROXUID_DATA_DIR", BASE_DIR / "data"))
IMAGE_CACHE_DIR = DATA_DIR / "profile-images"
DB_PATH = Path(os.environ.get("XEROXUID_DB", DATA_DIR / "xeroxuid.db"))
BACKUP_DIR = Path(os.environ.get("XEROXUID_BACKUP_DIR", DB_PATH.parent / "backups"))
SECRET_PATH = DATA_DIR / ".session-secret"
APP_VERSION = "2.2.2"
MAX_IMPORT_LINES = 5000
UID_PATTERN = re.compile(r"^\d{1,30}$")
USERNAME_PATTERN = re.compile(r"^[A-Za-z0-9_.-]{3,32}$")
BOOTSTRAP_ADMIN_USERNAME = os.environ.get("XEROXUID_ADMIN_USERNAME", "xeroticadmin")
BOOTSTRAP_ADMIN_PASSWORD = os.environ.get("XEROXUID_ADMIN_PASSWORD", "adbc4231")
UNSAFE_METHODS = {"POST", "PUT", "PATCH", "DELETE"}
LOGIN_WINDOW_SECONDS = 300
LOGIN_MAX_FAILURES = 6
FETCH_LOCK_TTL_SECONDS = max(60, int(os.environ.get("XEROXUID_FETCH_LOCK_TTL", "120")))

RECORD_FIELDS = (
    "id",
    "owner_user_id",
    "uid",
    "finder_code",
    "name",
    "username",
    "profile_id",
    "canonical_url",
    "profile_pic",
    "description",
    "follower_count",
    "likes_count",
    "instagram_username",
    "instagram_url",
    "fetch_status",
    "error_code",
    "error_message",
    "created_at",
    "updated_at",
    "fetched_at",
    "is_saved",
    "is_visited",
)


def _load_secret_key() -> str:
    configured = os.environ.get("XEROXUID_SECRET_KEY")
    if configured:
        return configured
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    try:
        existing = SECRET_PATH.read_text(encoding="utf-8").strip()
        if len(existing) >= 32:
            return existing
    except FileNotFoundError:
        pass
    secret = secrets.token_urlsafe(48)
    SECRET_PATH.write_text(secret, encoding="utf-8")
    try:
        SECRET_PATH.chmod(0o600)
    except OSError:
        pass
    return secret


app = Flask(__name__)
app.secret_key = _load_secret_key()
app.config.update(
    MAX_CONTENT_LENGTH=10 * 1024 * 1024,
    SESSION_COOKIE_NAME="xeroxuid_session",
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Strict",
    SESSION_COOKIE_SECURE=os.environ.get("XEROXUID_SECURE_COOKIES", "0").lower() in {"1", "true", "yes"},
    PERMANENT_SESSION_LIFETIME=timedelta(hours=12),
)

scraper = FacebookScraper()
try:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    file_handler = RotatingFileHandler(
        DATA_DIR / "xeroxuid.log",
        maxBytes=512_000,
        backupCount=2,
        encoding="utf-8",
    )
    file_handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    file_handler.setLevel(logging.INFO)
    app.logger.addHandler(file_handler)
    app.logger.setLevel(logging.INFO)
except OSError:
    pass

_login_failures: dict[str, list[float]] = {}
_fetch_claims: set[tuple[int, int]] = set()
_fetch_claims_guard = threading.Lock()
_image_locks: dict[str, threading.Lock] = {}
_image_locks_guard = threading.Lock()


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


@contextmanager
def db_connection():
    DB_PATH.parent.mkdir(parents=True, exist_ok=True)
    connection = sqlite3.connect(DB_PATH, timeout=20)
    connection.row_factory = sqlite3.Row
    connection.execute("PRAGMA foreign_keys = ON")
    connection.execute("PRAGMA busy_timeout = 20000")
    try:
        yield connection
        connection.commit()
    except Exception:
        connection.rollback()
        raise
    finally:
        connection.close()


def _table_exists(db: sqlite3.Connection, table_name: str) -> bool:
    return db.execute(
        "SELECT 1 FROM sqlite_master WHERE type = 'table' AND name = ?",
        (table_name,),
    ).fetchone() is not None


def _create_users_table(db: sqlite3.Connection) -> None:
    db.execute(
        """
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT NOT NULL UNIQUE COLLATE NOCASE,
            password_hash TEXT NOT NULL,
            role TEXT NOT NULL DEFAULT 'user' CHECK(role IN ('admin', 'user')),
            is_active INTEGER NOT NULL DEFAULT 1,
            created_at TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            last_login_at TEXT,
            last_active_at TEXT,
            failed_login_count INTEGER NOT NULL DEFAULT 0
        )
        """
    )
    db.execute("CREATE INDEX IF NOT EXISTS idx_users_username ON users(username)")


def _ensure_bootstrap_admin(db: sqlite3.Connection) -> int:
    timestamp = now_iso()
    admin = db.execute(
        "SELECT id, role, is_active FROM users WHERE username = ? COLLATE NOCASE",
        (BOOTSTRAP_ADMIN_USERNAME,),
    ).fetchone()
    if admin is None:
        cursor = db.execute(
            """
            INSERT INTO users(username, password_hash, role, is_active, created_at, updated_at)
            VALUES (?, ?, 'admin', 1, ?, ?)
            """,
            (
                BOOTSTRAP_ADMIN_USERNAME,
                generate_password_hash(BOOTSTRAP_ADMIN_PASSWORD),
                timestamp,
                timestamp,
            ),
        )
        return int(cursor.lastrowid)
    if admin["role"] != "admin" or not admin["is_active"]:
        db.execute(
            "UPDATE users SET role = 'admin', is_active = 1, updated_at = ? WHERE id = ?",
            (timestamp, admin["id"]),
        )
    return int(admin["id"])


def _create_records_table(db: sqlite3.Connection, table_name: str = "records") -> None:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", table_name):
        raise ValueError("Unsafe table name")
    db.execute(
        f"""
        CREATE TABLE IF NOT EXISTS {table_name} (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            owner_user_id INTEGER NOT NULL,
            uid TEXT NOT NULL,
            finder_code TEXT NOT NULL DEFAULT '',
            name TEXT,
            username TEXT,
            profile_id TEXT,
            canonical_url TEXT,
            profile_pic TEXT,
            description TEXT,
            follower_count INTEGER,
            likes_count INTEGER,
            instagram_username TEXT,
            instagram_url TEXT,
            fetch_status TEXT NOT NULL DEFAULT 'pending',
            error_code TEXT,
            error_message TEXT,
            created_at TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            fetched_at TEXT,
            is_saved INTEGER NOT NULL DEFAULT 0,
            is_visited INTEGER NOT NULL DEFAULT 0,
            FOREIGN KEY(owner_user_id) REFERENCES users(id) ON DELETE CASCADE,
            UNIQUE(owner_user_id, uid)
        )
        """
    )


def _records_schema_is_tenant_scoped(db: sqlite3.Connection) -> bool:
    if not _table_exists(db, "records"):
        return False
    columns = {row["name"] for row in db.execute("PRAGMA table_info(records)").fetchall()}
    if "owner_user_id" not in columns:
        return False
    table_sql_row = db.execute(
        "SELECT sql FROM sqlite_master WHERE type = 'table' AND name = 'records'"
    ).fetchone()
    compact = re.sub(r"\s+", "", str(table_sql_row["sql"] or "").lower()) if table_sql_row else ""
    return "unique(owner_user_id,uid)" in compact


def _migrate_records_table(db: sqlite3.Connection, bootstrap_admin_id: int) -> None:
    if not _table_exists(db, "records"):
        _create_records_table(db)
        return
    if _records_schema_is_tenant_scoped(db):
        return

    old_columns = {row["name"] for row in db.execute("PRAGMA table_info(records)").fetchall()}
    old_rows = db.execute("SELECT * FROM records ORDER BY id").fetchall()
    db.execute("DROP TABLE IF EXISTS records_v150")
    _create_records_table(db, "records_v150")

    valid_users = {int(row["id"]) for row in db.execute("SELECT id FROM users").fetchall()}
    timestamp = now_iso()
    insert_sql = (
        "INSERT OR IGNORE INTO records_v150("
        + ", ".join(RECORD_FIELDS)
        + ") VALUES ("
        + ",".join("?" for _ in RECORD_FIELDS)
        + ")"
    )

    values_to_insert: list[tuple[object, ...]] = []
    for row in old_rows:
        owner = bootstrap_admin_id
        if "owner_user_id" in old_columns and row["owner_user_id"] is not None:
            candidate_owner = int(row["owner_user_id"])
            if candidate_owner in valid_users:
                owner = candidate_owner
        values_to_insert.append(
            (
                row["id"] if "id" in old_columns else None,
                owner,
                str(row["uid"]),
                str(row["finder_code"] or "") if "finder_code" in old_columns else "",
                row["name"] if "name" in old_columns else None,
                row["username"] if "username" in old_columns else None,
                row["profile_id"] if "profile_id" in old_columns else None,
                row["canonical_url"] if "canonical_url" in old_columns else None,
                row["profile_pic"] if "profile_pic" in old_columns else None,
                row["description"] if "description" in old_columns else None,
                row["follower_count"] if "follower_count" in old_columns else None,
                row["likes_count"] if "likes_count" in old_columns else None,
                row["instagram_username"] if "instagram_username" in old_columns else None,
                row["instagram_url"] if "instagram_url" in old_columns else None,
                str(row["fetch_status"] or "pending") if "fetch_status" in old_columns else "pending",
                row["error_code"] if "error_code" in old_columns else None,
                row["error_message"] if "error_message" in old_columns else None,
                str(row["created_at"] or timestamp) if "created_at" in old_columns else timestamp,
                str(row["updated_at"] or timestamp) if "updated_at" in old_columns else timestamp,
                row["fetched_at"] if "fetched_at" in old_columns else None,
                int(row["is_saved"] or 0) if "is_saved" in old_columns else 0,
                int(row["is_visited"] or 0) if "is_visited" in old_columns else 0,
            )
        )
    if values_to_insert:
        db.executemany(insert_sql, values_to_insert)

    db.execute("DROP TABLE records")
    db.execute("ALTER TABLE records_v150 RENAME TO records")



def _ensure_column(db: sqlite3.Connection, table: str, column: str, definition: str) -> None:
    columns = {row["name"] for row in db.execute(f"PRAGMA table_info({table})").fetchall()}
    if column not in columns:
        db.execute(f"ALTER TABLE {table} ADD COLUMN {column} {definition}")


def _ensure_user_columns(db: sqlite3.Connection) -> None:
    _ensure_column(db, "users", "last_active_at", "TEXT")
    _ensure_column(db, "users", "failed_login_count", "INTEGER NOT NULL DEFAULT 0")


def _ensure_record_columns(db: sqlite3.Connection) -> None:
    _ensure_column(db, "records", "is_saved", "INTEGER NOT NULL DEFAULT 0")
    _ensure_column(db, "records", "is_visited", "INTEGER NOT NULL DEFAULT 0")


def _create_audit_table(db: sqlite3.Connection) -> None:
    db.execute(
        """
        CREATE TABLE IF NOT EXISTS audit_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            actor_user_id INTEGER,
            target_user_id INTEGER,
            action TEXT NOT NULL,
            details TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL,
            FOREIGN KEY(actor_user_id) REFERENCES users(id) ON DELETE SET NULL,
            FOREIGN KEY(target_user_id) REFERENCES users(id) ON DELETE SET NULL
        )
        """
    )
    db.execute("CREATE INDEX IF NOT EXISTS idx_audit_created ON audit_log(created_at DESC)")
    db.execute("CREATE INDEX IF NOT EXISTS idx_audit_target ON audit_log(target_user_id, created_at DESC)")


def _create_fetch_locks_table(db: sqlite3.Connection) -> None:
    db.execute(
        """
        CREATE TABLE IF NOT EXISTS fetch_locks (
            owner_user_id INTEGER NOT NULL,
            record_id INTEGER NOT NULL,
            claimed_at INTEGER NOT NULL,
            PRIMARY KEY(owner_user_id, record_id),
            FOREIGN KEY(owner_user_id) REFERENCES users(id) ON DELETE CASCADE,
            FOREIGN KEY(record_id) REFERENCES records(id) ON DELETE CASCADE
        )
        """
    )
    db.execute("CREATE INDEX IF NOT EXISTS idx_fetch_locks_claimed ON fetch_locks(claimed_at)")


def _get_image_lock(cache_key: str) -> threading.Lock:
    with _image_locks_guard:
        lock = _image_locks.get(cache_key)
        if lock is None:
            if len(_image_locks) >= 256:
                _image_locks.pop(next(iter(_image_locks)), None)
            lock = threading.Lock()
            _image_locks[cache_key] = lock
        return lock


def audit_event(action: str, *, actor_user_id: int | None = None, target_user_id: int | None = None, details: str = "") -> None:
    safe_details = re.sub(r"(?i)(password|secret|token)=[^,; ]+", r"\1=[redacted]", str(details))[:500]
    try:
        with db_connection() as db:
            db.execute(
                "INSERT INTO audit_log(actor_user_id, target_user_id, action, details, created_at) VALUES (?, ?, ?, ?, ?)",
                (actor_user_id, target_user_id, action[:80], safe_details, now_iso()),
            )
    except sqlite3.Error:
        app.logger.exception("Audit write failed action=%s", action)


def create_database_backup(reason: str = "manual") -> Path | None:
    if not DB_PATH.exists() or DB_PATH.stat().st_size == 0:
        return None
    BACKUP_DIR.mkdir(parents=True, exist_ok=True)
    safe_reason = re.sub(r"[^A-Za-z0-9_-]+", "-", reason).strip("-") or "backup"
    stamp = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")
    target = BACKUP_DIR / f"xeroxuid-{stamp}-{safe_reason}.db"
    source = sqlite3.connect(DB_PATH, timeout=20)
    destination = sqlite3.connect(target)
    try:
        source.backup(destination)
        destination.commit()
    finally:
        destination.close()
        source.close()
    backups = sorted(BACKUP_DIR.glob("xeroxuid-*.db"), key=lambda item: item.stat().st_mtime, reverse=True)
    for obsolete in backups[12:]:
        try:
            obsolete.unlink()
        except OSError:
            pass
    return target


def init_db() -> None:
    try:
        rollback_backup = create_database_backup("startup")
    except (OSError, sqlite3.Error):
        rollback_backup = None
        app.logger.exception("Automatic startup backup failed")
    try:
        with db_connection() as db:
            db.execute("PRAGMA journal_mode = WAL")
            db.execute("PRAGMA synchronous = NORMAL")
            _create_users_table(db)
            _ensure_user_columns(db)
            bootstrap_admin_id = _ensure_bootstrap_admin(db)
            _migrate_records_table(db, bootstrap_admin_id)
            _ensure_record_columns(db)
            _create_audit_table(db)
            _create_fetch_locks_table(db)
            db.execute("DELETE FROM fetch_locks WHERE claimed_at < ?", (int(time.time()) - FETCH_LOCK_TTL_SECONDS,))
            db.execute("CREATE INDEX IF NOT EXISTS idx_records_owner_uid ON records(owner_user_id, uid)")
            db.execute("CREATE INDEX IF NOT EXISTS idx_records_owner_status ON records(owner_user_id, fetch_status)")
            db.execute("CREATE INDEX IF NOT EXISTS idx_records_owner_saved ON records(owner_user_id, is_saved, updated_at DESC)")
            db.execute("CREATE INDEX IF NOT EXISTS idx_records_owner_updated ON records(owner_user_id, updated_at DESC)")
    except Exception:
        if rollback_backup and rollback_backup.exists():
            try:
                shutil.copy2(rollback_backup, DB_PATH)
            except OSError:
                app.logger.exception("Migration rollback copy failed")
        raise


def record_to_dict(row: sqlite3.Row) -> dict:
    data = {key: row[key] for key in row.keys()}
    data.pop("owner_user_id", None)
    return data


def public_user(row: sqlite3.Row | dict) -> dict:
    keys = set(row.keys())
    payload = {
        "id": row["id"],
        "username": row["username"],
        "role": row["role"],
        "is_active": bool(row["is_active"]),
        "created_at": row["created_at"],
        "last_login_at": row["last_login_at"],
        "last_active_at": row["last_active_at"] if "last_active_at" in keys else None,
        "failed_login_count": int(row["failed_login_count"] or 0) if "failed_login_count" in keys else 0,
    }
    if "record_count" in keys:
        payload["record_count"] = int(row["record_count"] or 0)
    return payload


def current_user_row() -> sqlite3.Row | None:
    if hasattr(g, "current_user"):
        return g.current_user
    user_id = session.get("user_id")
    if not user_id:
        g.current_user = None
        return None
    with db_connection() as db:
        user = db.execute(
            "SELECT * FROM users WHERE id = ? AND is_active = 1",
            (user_id,),
        ).fetchone()
    g.current_user = user
    return user


def current_user_id() -> int:
    user = current_user_row()
    if user is None:
        raise RuntimeError("No authenticated user")
    return int(user["id"])


def login_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if current_user_row() is None:
            session.clear()
            return jsonify({"success": False, "error": {"code": "authentication_required", "message": "Please sign in."}}), 401
        return view(*args, **kwargs)

    return wrapped


def admin_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        user = current_user_row()
        if user is None:
            session.clear()
            return jsonify({"success": False, "error": {"code": "authentication_required", "message": "Please sign in."}}), 401
        if user["role"] != "admin":
            return jsonify({"success": False, "error": {"code": "admin_required", "message": "Administrator access is required."}}), 403
        return view(*args, **kwargs)

    return wrapped


def get_record(record_id: int, owner_user_id: int | None = None) -> sqlite3.Row | None:
    owner_user_id = current_user_id() if owner_user_id is None else owner_user_id
    with db_connection() as db:
        return db.execute(
            "SELECT * FROM records WHERE id = ? AND owner_user_id = ?",
            (record_id, owner_user_id),
        ).fetchone()


def parse_import_text(text: str) -> tuple[list[tuple[str, str]], list[dict]]:
    records: list[tuple[str, str]] = []
    invalid: list[dict] = []
    seen: set[str] = set()
    lines = text.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    if len(lines) > MAX_IMPORT_LINES:
        raise ValueError(f"Maximum {MAX_IMPORT_LINES} lines can be imported at once.")

    for line_number, raw_line in enumerate(lines, start=1):
        line = raw_line.strip()
        if not line:
            continue
        uid, separator, finder_code = line.partition("|")
        uid = uid.strip()
        finder_code = finder_code.strip() if separator else ""
        if not UID_PATTERN.fullmatch(uid):
            invalid.append({"line": line_number, "value": raw_line[:120], "reason": "Invalid numeric UID"})
            continue
        if len(finder_code) > 500:
            invalid.append({"line": line_number, "value": raw_line[:120], "reason": "Finder code is too long"})
            continue
        if uid in seen:
            continue
        seen.add(uid)
        records.append((uid, finder_code))
    return records, invalid


def _rate_key(username: str) -> str:
    return f"{request.remote_addr or 'local'}:{username.lower()}"


def _login_is_limited(key: str) -> bool:
    cutoff = time.monotonic() - LOGIN_WINDOW_SECONDS
    attempts = [stamp for stamp in _login_failures.get(key, []) if stamp >= cutoff]
    _login_failures[key] = attempts
    return len(attempts) >= LOGIN_MAX_FAILURES


def _record_login_failure(key: str) -> None:
    _login_failures.setdefault(key, []).append(time.monotonic())


def _clear_login_failures(key: str) -> None:
    _login_failures.pop(key, None)


def _claim_fetch(owner_user_id: int, record_id: int) -> bool:
    key = (owner_user_id, record_id)
    with _fetch_claims_guard:
        if key in _fetch_claims:
            return False
        _fetch_claims.add(key)
    try:
        with db_connection() as db:
            now_epoch = int(time.time())
            db.execute("DELETE FROM fetch_locks WHERE claimed_at < ?", (now_epoch - FETCH_LOCK_TTL_SECONDS,))
            try:
                db.execute(
                    "INSERT INTO fetch_locks(owner_user_id, record_id, claimed_at) VALUES (?, ?, ?)",
                    (owner_user_id, record_id, now_epoch),
                )
            except sqlite3.IntegrityError:
                with _fetch_claims_guard:
                    _fetch_claims.discard(key)
                return False
        return True
    except sqlite3.Error:
        # The in-process guard still prevents duplicate work if SQLite is
        # temporarily busy; do not turn a transient lock issue into data loss.
        app.logger.exception("Persistent fetch-lock claim failed owner=%s record=%s", owner_user_id, record_id)
        return True


def _release_fetch(owner_user_id: int, record_id: int) -> None:
    try:
        with db_connection() as db:
            db.execute(
                "DELETE FROM fetch_locks WHERE owner_user_id = ? AND record_id = ?",
                (owner_user_id, record_id),
            )
    except sqlite3.Error:
        app.logger.exception("Persistent fetch-lock release failed owner=%s record=%s", owner_user_id, record_id)
    finally:
        with _fetch_claims_guard:
            _fetch_claims.discard((owner_user_id, record_id))


@app.before_request
def protect_api_and_csrf():
    if not request.path.startswith("/api/"):
        return None
    if request.path in {"/api/auth/login", "/api/auth/me"}:
        return None
    user = current_user_row()
    if user is None:
        session.clear()
        return jsonify({"success": False, "error": {"code": "authentication_required", "message": "Please sign in."}}), 401
    last_touch = int(session.get("last_active_touch") or 0)
    now_epoch = int(time.time())
    if now_epoch - last_touch >= 60:
        with db_connection() as db:
            db.execute("UPDATE users SET last_active_at = ? WHERE id = ?", (now_iso(), user["id"]))
        session["last_active_touch"] = now_epoch
    if request.method in UNSAFE_METHODS:
        provided = request.headers.get("X-CSRF-Token", "")
        if not provided and request.path == "/api/records/mark-visited" and request.is_json:
            beacon_data = request.get_json(silent=True) or {}
            provided = str(beacon_data.get("csrf_token") or "")
        expected = session.get("csrf_token", "")
        if not expected or not secrets.compare_digest(provided, expected):
            return jsonify({"success": False, "error": {"code": "csrf_failed", "message": "Security token expired. Sign in again."}}), 403
    return None


@app.after_request
def add_security_headers(response):
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["X-Frame-Options"] = "DENY"
    response.headers["Referrer-Policy"] = "no-referrer"
    response.headers["Permissions-Policy"] = "camera=(), microphone=(), geolocation=()"
    if "Cache-Control" not in response.headers:
        response.headers["Cache-Control"] = "no-store"
    response.headers["Content-Security-Policy"] = (
        "default-src 'self'; img-src 'self' data:; "
        "style-src 'self' 'unsafe-inline'; script-src 'self'; "
        "connect-src 'self'; frame-ancestors 'none'; base-uri 'self'; form-action 'self'"
    )
    return response


@app.errorhandler(ScraperError)
def handle_scraper_error(error: ScraperError):
    return jsonify({"success": False, "error": {"code": error.code, "message": error.message}}), error.status_code


@app.errorhandler(413)
def request_too_large(_error):
    return jsonify({"success": False, "error": {"code": "request_too_large", "message": "Request body is too large."}}), 413


@app.errorhandler(404)
def not_found(_error):
    if request.path.startswith("/api/"):
        return jsonify({"success": False, "error": {"code": "not_found", "message": "API route not found."}}), 404
    return render_template("index.html"), 200


@app.errorhandler(500)
def internal_error(error):
    app.logger.exception("Unhandled application error: %s", error)
    if request.path.startswith("/api/"):
        return jsonify({"success": False, "error": {"code": "server_error", "message": "The server could not complete the request."}}), 500
    return render_template("index.html"), 500


@app.get("/")
def index():
    return render_template("index.html")


@app.get("/health")
def health():
    return jsonify({"success": True, "service": "xeroxuid", "version": APP_VERSION, "database": DB_PATH.name})


@app.get("/api/auth/me")
def auth_me():
    user = current_user_row()
    if user is None:
        return jsonify({"success": True, "authenticated": False})
    csrf_token = session.get("csrf_token") or secrets.token_urlsafe(32)
    session["csrf_token"] = csrf_token
    return jsonify({"success": True, "authenticated": True, "user": public_user(user), "csrf_token": csrf_token})


@app.post("/api/auth/login")
def auth_login():
    if not request.is_json:
        return jsonify({"success": False, "error": {"code": "invalid_content_type", "message": "JSON body required."}}), 415
    data = request.get_json(silent=True) or {}
    username = str(data.get("username") or "").strip()
    password = str(data.get("password") or "")
    key = _rate_key(username)
    if _login_is_limited(key):
        return jsonify({"success": False, "error": {"code": "login_limited", "message": "Too many failed attempts. Wait five minutes."}}), 429
    if not username or not password:
        return jsonify({"success": False, "error": {"code": "missing_credentials", "message": "Username and password are required."}}), 400

    with db_connection() as db:
        user = db.execute("SELECT * FROM users WHERE username = ? COLLATE NOCASE", (username,)).fetchone()
        if user is None or not user["is_active"] or not check_password_hash(user["password_hash"], password):
            _record_login_failure(key)
            if user is not None:
                db.execute("UPDATE users SET failed_login_count = failed_login_count + 1, updated_at = ? WHERE id = ?", (now_iso(), user["id"]))
            return jsonify({"success": False, "error": {"code": "invalid_credentials", "message": "Invalid username or password."}}), 401
        timestamp = now_iso()
        db.execute("UPDATE users SET last_login_at = ?, last_active_at = ?, failed_login_count = 0, updated_at = ? WHERE id = ?", (timestamp, timestamp, timestamp, user["id"]))
        user = db.execute("SELECT * FROM users WHERE id = ?", (user["id"],)).fetchone()

    _clear_login_failures(key)
    session.clear()
    session.permanent = True
    session["user_id"] = user["id"]
    session["csrf_token"] = secrets.token_urlsafe(32)
    session["last_active_touch"] = int(time.time())
    audit_event("login_success", actor_user_id=int(user["id"]), target_user_id=int(user["id"]))
    return jsonify({"success": True, "authenticated": True, "user": public_user(user), "csrf_token": session["csrf_token"]})


@app.post("/api/auth/logout")
@login_required
def auth_logout():
    actor_id = current_user_id()
    audit_event("logout", actor_user_id=actor_id, target_user_id=actor_id)
    session.clear()
    return jsonify({"success": True})


@app.post("/api/auth/change-password")
@login_required
def auth_change_password():
    data = request.get_json(silent=True) or {}
    current_password = str(data.get("current_password") or "")
    new_password = str(data.get("new_password") or "")
    if len(new_password) < 8 or len(new_password) > 128:
        return jsonify({"success": False, "error": {"code": "invalid_password", "message": "New password must be 8–128 characters."}}), 400
    user = current_user_row()
    if not check_password_hash(user["password_hash"], current_password):
        return jsonify({"success": False, "error": {"code": "invalid_current_password", "message": "Current password is incorrect."}}), 400
    with db_connection() as db:
        db.execute(
            "UPDATE users SET password_hash = ?, updated_at = ? WHERE id = ?",
            (generate_password_hash(new_password), now_iso(), user["id"]),
        )
    audit_event("password_changed", actor_user_id=int(user["id"]), target_user_id=int(user["id"]))
    return jsonify({"success": True})


@app.get("/api/admin/users")
@admin_required
def admin_list_users():
    with db_connection() as db:
        rows = db.execute(
            """
            SELECT u.id, u.username, u.role, u.is_active, u.created_at, u.last_login_at, u.last_active_at, u.failed_login_count,
                   COUNT(r.id) AS record_count
            FROM users AS u
            LEFT JOIN records AS r ON r.owner_user_id = u.id
            GROUP BY u.id
            ORDER BY CASE WHEN u.role = 'admin' THEN 0 ELSE 1 END, u.username COLLATE NOCASE
            """
        ).fetchall()
    return jsonify({"success": True, "data": [public_user(row) for row in rows]})


@app.post("/api/admin/users")
@admin_required
def admin_create_user():
    data = request.get_json(silent=True) or {}
    username = str(data.get("username") or "").strip()
    password = str(data.get("password") or "")
    role = str(data.get("role") or "user").strip().lower()
    if not USERNAME_PATTERN.fullmatch(username):
        return jsonify({"success": False, "error": {"code": "invalid_username", "message": "Username must be 3–32 letters, numbers, dot, dash or underscore."}}), 400
    if len(password) < 8 or len(password) > 128:
        return jsonify({"success": False, "error": {"code": "invalid_password", "message": "Password must be 8–128 characters."}}), 400
    if role not in {"user", "admin"}:
        return jsonify({"success": False, "error": {"code": "invalid_role", "message": "Role must be user or admin."}}), 400
    timestamp = now_iso()
    try:
        with db_connection() as db:
            cursor = db.execute(
                """
                INSERT INTO users(username, password_hash, role, is_active, created_at, updated_at)
                VALUES (?, ?, ?, 1, ?, ?)
                """,
                (username, generate_password_hash(password), role, timestamp, timestamp),
            )
            row = db.execute(
                """
                SELECT u.id, u.username, u.role, u.is_active, u.created_at, u.last_login_at, u.last_active_at, u.failed_login_count,
                       0 AS record_count
                FROM users AS u WHERE u.id = ?
                """,
                (cursor.lastrowid,),
            ).fetchone()
    except sqlite3.IntegrityError:
        return jsonify({"success": False, "error": {"code": "username_exists", "message": "That username already exists."}}), 409
    except sqlite3.Error as exc:
        app.logger.exception("Account creation failed username=%s", username)
        return jsonify({"success": False, "error": {"code": "account_create_failed", "message": f"Account could not be created: {type(exc).__name__}."}}), 500
    audit_event("user_created", actor_user_id=current_user_id(), target_user_id=int(row["id"]), details=f"username={username},role={role}")
    return jsonify({"success": True, "data": public_user(row)}), 201


@app.patch("/api/admin/users/<int:user_id>")
@admin_required
def admin_update_user(user_id: int):
    actor = current_user_row()
    data = request.get_json(silent=True) or {}
    with db_connection() as db:
        target = db.execute("SELECT * FROM users WHERE id = ?", (user_id,)).fetchone()
        if target is None:
            return jsonify({"success": False, "error": {"code": "user_not_found", "message": "User not found."}}), 404
        if target["username"].lower() == BOOTSTRAP_ADMIN_USERNAME.lower() and user_id != actor["id"]:
            return jsonify({"success": False, "error": {"code": "protected_admin", "message": "The primary administrator is protected."}}), 400

        updates: list[str] = []
        values: list[object] = []
        if "is_active" in data:
            active = 1 if bool(data["is_active"]) else 0
            if user_id == actor["id"] and not active:
                return jsonify({"success": False, "error": {"code": "self_disable", "message": "You cannot disable your own account."}}), 400
            updates.append("is_active = ?")
            values.append(active)
        if "role" in data:
            role = str(data["role"]).lower()
            if role not in {"admin", "user"}:
                return jsonify({"success": False, "error": {"code": "invalid_role", "message": "Role must be user or admin."}}), 400
            if user_id == actor["id"] and role != "admin":
                return jsonify({"success": False, "error": {"code": "self_demote", "message": "You cannot remove your own admin role."}}), 400
            updates.append("role = ?")
            values.append(role)
        if "password" in data:
            password = str(data.get("password") or "")
            if len(password) < 8 or len(password) > 128:
                return jsonify({"success": False, "error": {"code": "invalid_password", "message": "Password must be 8–128 characters."}}), 400
            updates.append("password_hash = ?")
            values.append(generate_password_hash(password))
        if not updates:
            return jsonify({"success": False, "error": {"code": "nothing_to_update", "message": "No valid changes supplied."}}), 400
        updates.append("updated_at = ?")
        values.append(now_iso())
        values.append(user_id)
        db.execute(f"UPDATE users SET {', '.join(updates)} WHERE id = ?", tuple(values))
        row = db.execute(
            """
            SELECT u.id, u.username, u.role, u.is_active, u.created_at, u.last_login_at, u.last_active_at, u.failed_login_count,
                   COUNT(r.id) AS record_count
            FROM users AS u LEFT JOIN records AS r ON r.owner_user_id = u.id
            WHERE u.id = ? GROUP BY u.id
            """,
            (user_id,),
        ).fetchone()
    audit_event("user_updated", actor_user_id=int(actor["id"]), target_user_id=user_id, details="fields=" + ",".join(sorted(data.keys())))
    return jsonify({"success": True, "data": public_user(row)})


@app.delete("/api/admin/users/<int:user_id>")
@admin_required
def admin_delete_user(user_id: int):
    actor = current_user_row()
    if user_id == actor["id"]:
        return jsonify({"success": False, "error": {"code": "self_delete", "message": "You cannot delete your own account."}}), 400
    with db_connection() as db:
        target = db.execute("SELECT username FROM users WHERE id = ?", (user_id,)).fetchone()
        if target is None:
            return jsonify({"success": False, "error": {"code": "user_not_found", "message": "User not found."}}), 404
        if target["username"].lower() == BOOTSTRAP_ADMIN_USERNAME.lower():
            return jsonify({"success": False, "error": {"code": "protected_admin", "message": "The primary administrator cannot be deleted."}}), 400
        target_username = str(target["username"])
        db.execute("DELETE FROM records WHERE owner_user_id = ?", (user_id,))
        db.execute("DELETE FROM users WHERE id = ?", (user_id,))
    audit_event("user_deleted", actor_user_id=int(actor["id"]), details=f"target_id={user_id},username={target_username}")
    return jsonify({"success": True})


@app.get("/api/records")
@login_required
def list_records():
    owner_user_id = current_user_id()
    query = (request.args.get("q") or "").strip()
    with db_connection() as db:
        if query:
            like = f"%{query}%"
            rows = db.execute(
                """
                SELECT * FROM records
                WHERE owner_user_id = ? AND (
                    uid LIKE ? OR finder_code LIKE ? OR COALESCE(name, '') LIKE ?
                    OR COALESCE(username, '') LIKE ? OR COALESCE(fetch_status, '') LIKE ?
                    OR COALESCE(instagram_username, '') LIKE ?
                )
                ORDER BY id DESC
                """,
                (owner_user_id, like, like, like, like, like, like),
            ).fetchall()
        else:
            rows = db.execute(
                "SELECT * FROM records WHERE owner_user_id = ? ORDER BY id DESC",
                (owner_user_id,),
            ).fetchall()
    return jsonify({"success": True, "data": [record_to_dict(row) for row in rows]})


@app.post("/api/import")
@login_required
def import_records():
    if not request.is_json:
        return jsonify({"success": False, "error": {"code": "invalid_content_type", "message": "JSON body required."}}), 415
    data = request.get_json(silent=True) or {}
    text = data.get("text")
    if not isinstance(text, str) or not text.strip():
        return jsonify({"success": False, "error": {"code": "missing_text", "message": "Import text is required."}}), 400
    try:
        records, invalid = parse_import_text(text)
    except ValueError as exc:
        return jsonify({"success": False, "error": {"code": "too_many_lines", "message": str(exc)}}), 400

    owner_user_id = current_user_id()
    timestamp = now_iso()
    new_rows: list[tuple[object, ...]] = []
    changed_rows: list[tuple[object, ...]] = []
    with db_connection() as db:
        existing_by_uid: dict[str, sqlite3.Row] = {}
        if records:
            all_uids = [uid for uid, _finder_code in records]
            for offset in range(0, len(all_uids), 850):
                chunk = all_uids[offset : offset + 850]
                placeholders = ",".join("?" for _ in chunk)
                found = db.execute(
                    f"SELECT id, uid, finder_code FROM records WHERE owner_user_id = ? AND uid IN ({placeholders})",
                    (owner_user_id, *chunk),
                ).fetchall()
                existing_by_uid.update({row["uid"]: row for row in found})

        for uid, finder_code in records:
            existing = existing_by_uid.get(uid)
            if existing is None:
                new_rows.append((owner_user_id, uid, finder_code, timestamp, timestamp))
            elif finder_code and finder_code != existing["finder_code"]:
                changed_rows.append((finder_code, timestamp, existing["id"], owner_user_id))
        if new_rows:
            db.executemany(
                "INSERT INTO records(owner_user_id, uid, finder_code, created_at, updated_at) VALUES (?, ?, ?, ?, ?)",
                new_rows,
            )
        if changed_rows:
            db.executemany(
                "UPDATE records SET finder_code = ?, updated_at = ? WHERE id = ? AND owner_user_id = ?",
                changed_rows,
            )

    return jsonify({
        "success": True,
        "data": {
            "inserted": len(new_rows),
            "updated": len(changed_rows),
            "valid": len(records),
            "invalid_count": len(invalid),
            "invalid": invalid[:50],
        },
    }), 201


@app.post("/api/records/mark-visited")
@login_required
def mark_records_visited():
    """Persist app-open history, including navigator.sendBeacon requests."""
    data = request.get_json(silent=True) or {}
    raw_ids = data.get("ids")
    if raw_ids is None and data.get("record_id") is not None:
        raw_ids = [data.get("record_id")]
    if not isinstance(raw_ids, list) or not raw_ids or len(raw_ids) > 5000:
        return jsonify({"success": False, "error": {"code": "invalid_ids", "message": "Provide 1–5,000 record IDs."}}), 400
    record_ids: list[int] = []
    seen_ids: set[int] = set()
    for value in raw_ids:
        if isinstance(value, bool):
            continue
        try:
            record_id = int(value)
        except (TypeError, ValueError):
            continue
        if record_id > 0 and record_id not in seen_ids:
            seen_ids.add(record_id)
            record_ids.append(record_id)
    if not record_ids:
        return jsonify({"success": False, "error": {"code": "invalid_ids", "message": "No valid record IDs were provided."}}), 400

    owner_user_id = current_user_id()
    updated = 0
    with db_connection() as db:
        for offset in range(0, len(record_ids), 850):
            chunk = record_ids[offset : offset + 850]
            placeholders = ",".join("?" for _ in chunk)
            cursor = db.execute(
                f"UPDATE records SET is_visited = 1 WHERE owner_user_id = ? AND id IN ({placeholders}) AND is_visited = 0",
                (owner_user_id, *chunk),
            )
            updated += max(0, int(cursor.rowcount or 0))
    return jsonify({"success": True, "updated": updated})


@app.get("/api/system/fetch-diagnostic")
@admin_required
def fetch_diagnostic():
    uid = str(request.args.get("uid") or "").strip()
    if uid and not UID_PATTERN.fullmatch(uid):
        return jsonify({"success": False, "error": {"code": "invalid_uid", "message": "Diagnostic UID must be numeric."}}), 400
    report = scraper.diagnose(uid or None)
    report["app_base"] = request.script_root or "/"
    report["proxy_mode"] = "direct_only"
    if not report.get("dns", {}).get("ok"):
        advice = "DNS resolution failed on the hosting account. Ask the provider to enable external DNS and outbound HTTPS."
    elif not report.get("outbound", {}).get("ok"):
        advice = "The server cannot reach Facebook over HTTPS. Ask the host to allow outbound TCP port 443 and check IPv6 routing."
    elif report.get("profile", {}).get("code") == "access_denied":
        advice = "Facebook returned a login/verification page for every supported public route. Test another known-public UID and pause repeated retries."
    elif report.get("profile", {}).get("code") in {"temporarily_blocked", "rate_limited", "facebook_http_400_all_routes"}:
        advice = "Facebook rejected the current public request. Pause batch fetching and retry later."
    elif report.get("profile", {}).get("ok"):
        advice = "Server fetch is working. Retry the record from the dashboard."
    else:
        advice = "Network access is available. Import one UID and run this test again for a profile-level result."
    report["advice"] = advice
    return jsonify({"success": True, "data": report})


@app.get("/api/records/<int:record_id>/image")
@login_required
def profile_image(record_id: int):
    owner_user_id = current_user_id()
    row = get_record(record_id, owner_user_id)
    if row is None:
        return Response(status=404)
    image_url = str(row["profile_pic"] or "").strip()
    if not image_url:
        return Response(status=404)

    cache_key = hashlib.sha256(image_url.encode("utf-8", errors="ignore")).hexdigest()
    cache_file = IMAGE_CACHE_DIR / f"{cache_key}.bin"
    type_file = IMAGE_CACHE_DIR / f"{cache_key}.type"

    def cached_response():
        try:
            if cache_file.is_file() and type_file.is_file():
                content_type = type_file.read_text(encoding="utf-8").strip() or "image/jpeg"
                response = send_file(cache_file, mimetype=content_type, conditional=True, max_age=21600)
                response.headers["Cache-Control"] = "private, max-age=21600, immutable"
                return response
        except OSError:
            return None
        return None

    cached = cached_response()
    if cached is not None:
        return cached

    # Only one request per image URL reaches Facebook at a time. Broken image
    # URLs return a fast 404 and use the client fallback; they never trigger a
    # second full profile scrape while the user is scrolling.
    image_lock = _get_image_lock(cache_key)
    with image_lock:
        cached = cached_response()
        if cached is not None:
            return cached
        try:
            payload, content_type = scraper.fetch_profile_image(image_url)
        except ScraperError as exc:
            app.logger.info(
                "Profile image fetch failed owner=%s record=%s code=%s",
                owner_user_id,
                record_id,
                exc.code,
            )
            return Response(status=404)

        try:
            IMAGE_CACHE_DIR.mkdir(parents=True, exist_ok=True)
            temporary = IMAGE_CACHE_DIR / f"{cache_key}.{threading.get_ident()}.tmp"
            temporary.write_bytes(payload)
            temporary.replace(cache_file)
            type_file.write_text(content_type, encoding="utf-8")
        except OSError:
            pass

    response = Response(payload, mimetype=content_type)
    response.headers["Cache-Control"] = "private, max-age=21600, immutable"
    response.headers["Content-Length"] = str(len(payload))
    return response


@app.post("/api/records/<int:record_id>/fetch")
@login_required
def fetch_record(record_id: int):
    owner_user_id = current_user_id()
    row = get_record(record_id, owner_user_id)
    if row is None:
        return jsonify({"success": False, "error": {"code": "record_not_found", "message": "Record not found."}}), 404
    if not _claim_fetch(owner_user_id, record_id):
        return jsonify({"success": False, "error": {"code": "already_fetching", "message": "This UID is already being fetched."}}), 409

    uid = str(row["uid"])
    profile_url = f"https://www.facebook.com/{uid}"
    timestamp = now_iso()
    try:
        try:
            result = scraper.extract_uid(uid)
        except ScraperError as exc:
            app.logger.warning("Facebook fetch failed owner=%s record=%s uid=%s code=%s", owner_user_id, record_id, uid, exc.code)
            with db_connection() as db:
                db.execute(
                    """
                    UPDATE records SET fetch_status = 'error', error_code = ?, error_message = ?,
                        updated_at = ?, fetched_at = ? WHERE id = ? AND owner_user_id = ?
                    """,
                    (exc.code, exc.message, timestamp, timestamp, record_id, owner_user_id),
                )
            return jsonify({"success": False, "error": {"code": exc.code, "message": exc.message}, "record_id": record_id}), exc.status_code

        with db_connection() as db:
            db.execute(
                """
                UPDATE records SET
                    name = COALESCE(?, name),
                    username = COALESCE(?, username),
                    profile_id = COALESCE(?, profile_id),
                    canonical_url = COALESCE(?, canonical_url),
                    profile_pic = COALESCE(?, profile_pic),
                    description = COALESCE(?, description),
                    follower_count = COALESCE(?, follower_count),
                    likes_count = COALESCE(?, likes_count),
                    instagram_username = COALESCE(?, instagram_username),
                    instagram_url = COALESCE(?, instagram_url),
                    fetch_status = 'success', error_code = NULL, error_message = NULL,
                    updated_at = ?, fetched_at = ?
                WHERE id = ? AND owner_user_id = ?
                """,
                (
                    result.get("name"), result.get("username"), result.get("profile_id") or uid,
                    result.get("canonical_url") or profile_url, result.get("profile_pic"),
                    result.get("description"), result.get("follower_count"), result.get("likes_count"),
                    result.get("instagram_username"), result.get("instagram_url"), timestamp, timestamp,
                    record_id, owner_user_id,
                ),
            )
            updated_row = db.execute(
                "SELECT * FROM records WHERE id = ? AND owner_user_id = ?",
                (record_id, owner_user_id),
            ).fetchone()
        return jsonify({"success": True, "data": record_to_dict(updated_row)})
    finally:
        _release_fetch(owner_user_id, record_id)


@app.patch("/api/records/<int:record_id>")
@login_required
def update_record(record_id: int):
    owner_user_id = current_user_id()
    if get_record(record_id, owner_user_id) is None:
        return jsonify({"success": False, "error": {"code": "record_not_found", "message": "Record not found."}}), 404
    data = request.get_json(silent=True) or {}
    updates: list[str] = []
    values: list[object] = []
    if "finder_code" in data:
        finder_code = data.get("finder_code")
        if not isinstance(finder_code, str) or len(finder_code) > 500:
            return jsonify({"success": False, "error": {"code": "invalid_finder_code", "message": "Finder code must be a string up to 500 characters."}}), 400
        updates.append("finder_code = ?")
        values.append(finder_code.strip())
    for json_key, column in (("is_saved", "is_saved"), ("is_visited", "is_visited")):
        if json_key in data:
            updates.append(f"{column} = ?")
            values.append(1 if bool(data[json_key]) else 0)
    if not updates:
        return jsonify({"success": False, "error": {"code": "nothing_to_update", "message": "No supported record changes supplied."}}), 400
    updates.append("updated_at = ?")
    values.append(now_iso())
    values.extend((record_id, owner_user_id))
    with db_connection() as db:
        db.execute(f"UPDATE records SET {', '.join(updates)} WHERE id = ? AND owner_user_id = ?", tuple(values))
        updated_row = db.execute(
            "SELECT * FROM records WHERE id = ? AND owner_user_id = ?",
            (record_id, owner_user_id),
        ).fetchone()
    return jsonify({"success": True, "data": record_to_dict(updated_row)})


@app.delete("/api/records/<int:record_id>")
@login_required
def delete_record(record_id: int):
    owner_user_id = current_user_id()
    with db_connection() as db:
        cursor = db.execute(
            "DELETE FROM records WHERE id = ? AND owner_user_id = ?",
            (record_id, owner_user_id),
        )
    if cursor.rowcount == 0:
        return jsonify({"success": False, "error": {"code": "record_not_found", "message": "Record not found."}}), 404
    return jsonify({"success": True})


@app.post("/api/records/bulk-delete")
@login_required
def bulk_delete_records():
    owner_user_id = current_user_id()
    data = request.get_json(silent=True) or {}
    ids = data.get("ids")
    if not isinstance(ids, list) or not ids or len(ids) > 5000:
        return jsonify({"success": False, "error": {"code": "invalid_ids", "message": "Supply 1–5,000 record IDs."}}), 400
    clean_ids = sorted({int(value) for value in ids if isinstance(value, int) or str(value).isdigit()})
    if not clean_ids:
        return jsonify({"success": False, "error": {"code": "invalid_ids", "message": "No valid record IDs supplied."}}), 400
    deleted = 0
    with db_connection() as db:
        for offset in range(0, len(clean_ids), 850):
            chunk = clean_ids[offset : offset + 850]
            placeholders = ",".join("?" for _ in chunk)
            cursor = db.execute(
                f"DELETE FROM records WHERE owner_user_id = ? AND id IN ({placeholders})",
                (owner_user_id, *chunk),
            )
            deleted += max(cursor.rowcount, 0)
    return jsonify({"success": True, "deleted": deleted})


@app.delete("/api/records")
@login_required
def delete_all_records():
    owner_user_id = current_user_id()
    with db_connection() as db:
        cursor = db.execute("DELETE FROM records WHERE owner_user_id = ?", (owner_user_id,))
    return jsonify({"success": True, "deleted": cursor.rowcount})


@app.post("/api/import-backup")
@login_required
def import_account_backup():
    data = request.get_json(silent=True) or {}
    source_records = data.get("records")
    if not isinstance(source_records, list) or not source_records:
        return jsonify({"success": False, "error": {"code": "invalid_backup", "message": "Backup JSON must contain a non-empty records array."}}), 400
    if len(source_records) > MAX_IMPORT_LINES:
        return jsonify({"success": False, "error": {"code": "too_many_records", "message": f"Maximum {MAX_IMPORT_LINES} records can be restored at once."}}), 400

    clean: list[dict] = []
    invalid: list[dict] = []
    allowed_statuses = {"pending", "success", "error"}
    for index, item in enumerate(source_records, start=1):
        if not isinstance(item, dict):
            invalid.append({"line": index, "reason": "Record is not an object"})
            continue
        uid = str(item.get("uid") or "").strip()
        finder_code = str(item.get("finder_code") or "").strip()
        if not UID_PATTERN.fullmatch(uid) or len(finder_code) > 500:
            invalid.append({"line": index, "reason": "Invalid UID or Finder Code"})
            continue
        status = str(item.get("fetch_status") or "pending").lower()
        if status not in allowed_statuses:
            status = "pending"
        def short_text(key: str, limit: int) -> str | None:
            value = item.get(key)
            if value is None:
                return None
            return str(value).strip()[:limit] or None
        def safe_int(key: str) -> int | None:
            value = item.get(key)
            try:
                return max(0, int(value)) if value not in {None, ""} else None
            except (TypeError, ValueError):
                return None
        clean.append({
            "uid": uid,
            "finder_code": finder_code,
            "name": short_text("name", 500),
            "username": short_text("username", 100),
            "profile_id": short_text("profile_id", 100),
            "canonical_url": short_text("canonical_url", 2000),
            "profile_pic": short_text("profile_pic", 4000),
            "description": short_text("description", 5000),
            "follower_count": safe_int("follower_count"),
            "likes_count": safe_int("likes_count"),
            "instagram_username": short_text("instagram_username", 100),
            "instagram_url": short_text("instagram_url", 2000),
            "fetch_status": status,
            "error_code": short_text("error_code", 100),
            "error_message": short_text("error_message", 1000),
            "is_saved": 1 if bool(item.get("is_saved")) else 0,
            "is_visited": 1 if bool(item.get("is_visited")) else 0,
        })
    if not clean:
        return jsonify({"success": False, "error": {"code": "invalid_backup", "message": "No valid records were found in the backup."}, "invalid": invalid[:50]}), 400

    owner_user_id = current_user_id()
    timestamp = now_iso()
    inserted = 0
    updated = 0
    with db_connection() as db:
        for item in clean:
            existing = db.execute(
                "SELECT id FROM records WHERE owner_user_id = ? AND uid = ?",
                (owner_user_id, item["uid"]),
            ).fetchone()
            values = (
                item["finder_code"], item["name"], item["username"], item["profile_id"],
                item["canonical_url"], item["profile_pic"], item["description"], item["follower_count"],
                item["likes_count"], item["instagram_username"], item["instagram_url"], item["fetch_status"],
                item["error_code"], item["error_message"], item["is_saved"], item["is_visited"], timestamp,
            )
            if existing is None:
                db.execute(
                    """
                    INSERT INTO records(
                        owner_user_id, uid, finder_code, name, username, profile_id, canonical_url,
                        profile_pic, description, follower_count, likes_count, instagram_username,
                        instagram_url, fetch_status, error_code, error_message, is_saved, is_visited,
                        created_at, updated_at, fetched_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    (owner_user_id, item["uid"], *values[:-1], timestamp, timestamp, timestamp if item["fetch_status"] != "pending" else None),
                )
                inserted += 1
            else:
                db.execute(
                    """
                    UPDATE records SET finder_code = ?, name = ?, username = ?, profile_id = ?,
                        canonical_url = ?, profile_pic = ?, description = ?, follower_count = ?, likes_count = ?,
                        instagram_username = ?, instagram_url = ?, fetch_status = ?, error_code = ?, error_message = ?,
                        is_saved = ?, is_visited = ?, updated_at = ?, fetched_at = CASE WHEN ? = 'pending' THEN fetched_at ELSE ? END
                    WHERE id = ? AND owner_user_id = ?
                    """,
                    (*values, item["fetch_status"], timestamp, existing["id"], owner_user_id),
                )
                updated += 1
    audit_event("account_backup_restored", actor_user_id=owner_user_id, target_user_id=owner_user_id, details=f"inserted={inserted},updated={updated},invalid={len(invalid)}")
    return jsonify({"success": True, "data": {"inserted": inserted, "updated": updated, "invalid_count": len(invalid), "invalid": invalid[:50]}}), 201


@app.get("/api/export")
@login_required
def export_account_data():
    owner_user_id = current_user_id()
    export_format = str(request.args.get("format") or "txt").lower()
    if export_format not in {"txt", "csv", "json"}:
        return jsonify({"success": False, "error": {"code": "invalid_export_format", "message": "Format must be txt, csv or json."}}), 400
    with db_connection() as db:
        rows = db.execute("SELECT * FROM records WHERE owner_user_id = ? ORDER BY id", (owner_user_id,)).fetchall()
    records = [record_to_dict(row) for row in rows]
    stamp = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")
    if export_format == "json":
        payload = json.dumps({"version": APP_VERSION, "exported_at": now_iso(), "records": records}, ensure_ascii=False, indent=2).encode("utf-8")
        mime = "application/json"
    elif export_format == "csv":
        output = io.StringIO(newline="")
        fields = ["uid", "finder_code", "name", "username", "follower_count", "likes_count", "instagram_username", "fetch_status", "is_saved", "is_visited"]
        writer = csv.DictWriter(output, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(records)
        payload = output.getvalue().encode("utf-8-sig")
        mime = "text/csv"
    else:
        payload = "\n".join(f"{row['uid']}|{row.get('finder_code') or ''}" for row in records).encode("utf-8")
        mime = "text/plain"
    return send_file(io.BytesIO(payload), mimetype=mime, as_attachment=True, download_name=f"xeroxuid-account-{stamp}.{export_format}")


@app.post("/api/system/backup")
@admin_required
def create_backup_api():
    path = create_database_backup("manual")
    if path is None:
        return jsonify({"success": False, "error": {"code": "backup_unavailable", "message": "Database is empty or unavailable."}}), 400
    audit_event("database_backup", actor_user_id=current_user_id(), details=f"file={path.name}")
    return jsonify({"success": True, "file": path.name, "created_at": now_iso()})


@app.post("/api/system/cache/clear")
@admin_required
def clear_image_cache():
    removed = 0
    if IMAGE_CACHE_DIR.exists():
        for path in IMAGE_CACHE_DIR.iterdir():
            if path.is_file() and path.suffix in {".bin", ".type", ".tmp"}:
                try:
                    path.unlink()
                    removed += 1
                except OSError:
                    pass
    audit_event("image_cache_cleared", actor_user_id=current_user_id(), details=f"files={removed}")
    return jsonify({"success": True, "removed": removed})


@app.get("/api/admin/audit")
@admin_required
def admin_audit_log():
    try:
        limit = min(max(int(request.args.get("limit") or 100), 1), 500)
    except (TypeError, ValueError):
        return jsonify({"success": False, "error": {"code": "invalid_limit", "message": "Audit limit must be a number."}}), 400
    with db_connection() as db:
        rows = db.execute(
            """
            SELECT a.id, a.action, a.details, a.created_at,
                   actor.username AS actor_username, target.username AS target_username
            FROM audit_log AS a
            LEFT JOIN users AS actor ON actor.id = a.actor_user_id
            LEFT JOIN users AS target ON target.id = a.target_user_id
            ORDER BY a.id DESC LIMIT ?
            """,
            (limit,),
        ).fetchall()
    return jsonify({"success": True, "data": [dict(row) for row in rows]})


init_db()

if __name__ == "__main__":
    port = int(os.environ.get("PORT", "5002"))
    host = os.environ.get("HOST", "127.0.0.1")
    app.run(host=host, port=port, debug=False, threaded=True)
