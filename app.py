#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════╗
║     RENTAL BOOKING & INVENTORY MANAGEMENT SYSTEM v3.0       ║
╠══════════════════════════════════════════════════════════════╣
║  • Accept/Deny workflow with Stripe payment integration      ║
║  • Invoice + contract emailed automatically on Accept        ║
║  • Stripe webhook auto-confirms booking on deposit payment   ║
║  • Real-time inventory — first-come-first-PAID               ║
║  • Admin panel with full booking management                  ║
╚══════════════════════════════════════════════════════════════╝
"""

import os, re, json, logging, smtplib, secrets, decimal
import urllib.parse
from datetime import datetime, timezone, date, timedelta
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from functools import wraps

import requests
import psycopg2
import psycopg2.extras
import stripe
from flask import (Flask, request, render_template_string,
                   redirect, url_for, jsonify, session, Response)
from dotenv import load_dotenv

load_dotenv()
logging.basicConfig(level=logging.INFO, format="%(asctime)s  %(levelname)s  %(message)s")
log = logging.getLogger(__name__)

app = Flask(__name__)
app.secret_key = os.getenv("SECRET_KEY", secrets.token_hex(32))


# ══════════════════════════════════════════════════════════════════════════════
#  RENTAL CATALOG  —  edit prices/quantities here anytime
# ══════════════════════════════════════════════════════════════════════════════

PRODUCTS = [
    {"id": "chairs",         "name": "White Folding Plastic Chairs",     "price": 2.75,  "total": 200},
    {"id": "tables_6ft",     "name": "6ft White Folding Plastic Tables", "price": 8.00,  "total": 30},
    {"id": "banquet_tables", "name": "8x30 Wood Banquet Tables",         "price": 15.00, "total": 10},
    {"id": "round_tables",   "name": "60in Wood Round Tables",           "price": 15.00, "total": 10},
    {"id": "cocktail_30",    "name": "30in Cocktail Tables",             "price": 15.00, "total": 10},
    {"id": "cocktail_cloth", "name": "Cocktail Table Cloths",            "price": 8.00,  "total": 10},
]

EXACT_TIME_FEE  = 175.00
DEPOSIT_PERCENT = 0.25   # 25% deposit required
CT_TAX_RATE     = 0.0635 # Connecticut sales tax 6.35%


# ══════════════════════════════════════════════════════════════════════════════
#  CONFIGURATION  (set in Render.com → Environment)
# ══════════════════════════════════════════════════════════════════════════════

def _float(key, default):
    try:
        return float(os.getenv(key, "") or default)
    except ValueError:
        return float(default)

# ── PWA Icons (base64-encoded PNGs) ──────────────────────────────────────────
import base64 as _b64
_ICON_192_B64 = "iVBORw0KGgoAAAANSUhEUgAAAMAAAADACAIAAADdvvtQAAAE8klEQVR4nO3dP05UURiG8YGQkBBjovb0bIFVuAO2QOEarCiIhbWtnYWdKzCxdyVi7CxOcnMzEOWe95zv331+vc7wncfvzDAGTi6vbw5Ar1PvJ4DcCAgSAoKEgCAhIEgICBICgoSAICEgSAgIEgKChIAgISBICAiSM+8nEML51V3Hn/rz893wZ5LOHgPqy+U5f88Ok9pFQKOK2fpAe+ipckBm3fz3CRQuqVpA7tE8af2sisVUJ6CY6TzWnmeZjNIHlKWbI2Vut8QBJU3nSPaFlDKgGums5c0oWUD10lnLmFGagGqns5Yroxyfhe2nnkWWLzn6BsoyxxlSrKK4Ae05nbXgGQW9wqjnSNiBRAwo7LB8xRxLrCss5oziCHidBdpA1PNMoQYVJaBQQ4kvzrj8r7A4s8glyHXmvIGoR+Q+QM+A3L/4GnzH6BYQ9QzkOEyfgKhnOK+ROgREPZO4DNY6IOqZyn68pgFRjwHjIdsFRD1mLEdtFBD1GDMbeJSPMpCURUCsHxc2Y58eEPU4Mhj+3ICox93sI+A1ECQTA2L9BDH1IGYFRD2hzDuOKQFRT0CTDoXXQJCMD4j1E9aMo2EDQTI4INZPcMMPaGRA1JPC2GPiCoNkWECsn0QGHhYbCJIxAbF+0hl1ZGwgSAYExPpJasjBsYEgUQNi/aSmHx8bCBICgkT6AVMx76+XFyc/PrzxfhbH3n/+9enbb+9n8YTzqzvlp1SxgSDpDyjm+kEH5SjZQJAQECQEBEnnu7BcL4Duvzx8/Ppg+YivXpx+v39t+Yii7vdibCBICAiSnoBy3V94pr5jZQNBQkCQEBAkBATJ5oB4BV1Yx+GygSAhIEgICBICgoSAINkWEG/Bytt6xGwgSAgIEgKChIAgISBICAgSAoKEgCAhIEgICBICgoSAICEgSAgIEgKChIAgISBItgWk/DhPpLD1iNlAkBAQJAQECQFBQkCQbA6IN2KFdRwuGwgSAoKEgCAhIEh6AuJ1dEn8qgM4ICBIOgPiFium+0DZQJAQECQEBEl/QLwMKoPfGw83UkAsoQLEQ2QDQUJAkKgBcYulph8fGwiSAQGxhJIacnBsIEjGBMQSSmfUkbGBIBkWEEsokYGHxQaCZGRALKEUxh7T4A1EQ8ENPyCuMEjGB8QSCmvG0bCBIJkSEEsooEmHMmsD0VAo845j4hVGQ0FMPQheA0EyNyCWkLvZRzB9A9GQI4PhW1xhNOTCZuxnBo/h7vbtxe3bC+9nUZPRi2iWkDGzgdu9C6MhM5ajNn0bT0MGjIds/X0gGprKfrwO30ikoUlcBntyeX1j/6iHw+H86s7lcavy+mfp9lEGe2ggx2F6fhZGQ0P4jtH5w1QaErkP0P870W0EvCTayj2dJsp/5wgyjizijCtKQIdIQwku1KD8r7A1rrN/C5VOE2gDLQKOKYKYY4kY0CHqsByFHUisK2yN66wJm04TN6BmzxkFT6cJeoUdSTHKsbJ8ydE30GI/qyhLOk2agJraGeVKp0kWUFMvo4zpNCkDampklDedJnFAzXIAuUrK3s0ifUCLLAupTDpNnYCa9fHEialYNGvVAlpzv90Kd7OoHNDi6CDn9bSHYo7sIqAjj4+5L6kd5vLYHgN6jBS65fgsDGERECQEBAkBQUJAkBAQJAQECQFBQkCQEBAkBAQJAUFCQJAQECR/AWuBXRYBgcQbAAAAAElFTkSuQmCC"
_ICON_512_B64 = "iVBORw0KGgoAAAANSUhEUgAAAgAAAAIACAIAAAB7GkOtAAAOd0lEQVR4nO3dMY5sVxWF4bJlZCECGIFT5AkQOCYnJUGehIkIEDEeBhNgGIzAImYCEFoQELT13O7XXV1169579t7r+wYADXXO+t+pfoZPvvjq6wsAeT5d/QMAsIYAAIQSAIBQAgAQSgAAQgkAQCgBAAglAAChBAAglAAAhBIAgFACABBKAABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEIJAEAoAQAIJQAAoQQAIJQAAIQSAIBQAgAQSgAAQgkAQCgBAAglAAChBAAglAAAhBIAgFACABBKAABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEIJAECoZQH4/rtvVv1bA9SxcAy9AABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEKtDIB/GBgIt3YGvQAAQgkAQCgBAAglAAChBAAglAAAhBIAgFCLA+AfBQBiLR9ALwCAUAIAEEoAAEIJAEAoAQAItT4Ay38PDnC+CtO3PgAALCEAAKEEACCUAACEKhGACr8MAThNkdErEQAAzicAAKEEACBUlQAU+UYM4Gh15q5KAAA4mQAAhBIAgFACABCqUADq/GIE4CClhq5QAAA4kwAAhKoVgFKPI4B9VZu4WgEA4DQCABBKAABClQtAte/IAHZRcNzKBQCAcwgAQKiKASj4UAJ4RM1ZqxgAAE4gAAChigag5nMJYIOyg1Y0AAAcTQAAQtUNQNlHE8DtKk9Z3QAAcCgBAAhVOgCVn04A7yo+YqUDAMBxBAAgVPUAFH9AAbyl/nxVDwAABxEAgFANAlD/GQXwQovhahAAAI7QIwAtWgrwpMtk9QgAALsIAMDhageg7EMNJO84Sf0CAMAuWgagY2mBwZqOUssAAPC4rgFo2ltgnr5z1DUAADyocQD6VhcYo/UQNQ4AAI/oHYDW7QW66z5BvQMAwGbtA9C9wEBTA8anfQAA2GZCAAZ0GOhlxuxMCAAAGwwJwIwaAy2MGZwhAbgM+kiAyiZNzZwAAHCXUQGYVGagoGEjMyoAANxuWgCG9RmoY968TAsAADcaGIB5lQaWGzksAwNwGfpRAatMnZSZAQDgXWMDMLXYwMkGj8nYAFxGf2zAOWbPyOQAAHDF8ADMrjdwqPEDMjwAl4CPEDhCwnTMDwAAr4oIQELJgR2FjEZEAC4xHyfwuJy5SAkAAC8EBSCn6sBmUUMRFIBL2EcL3CttIrICAMAHcQFIKzxwo8BxiAvAJfJjBq7LnIXEAFxSP2zgVbGDEBoAAHIDENt84LnkKcgNwCX7gwcu8SMQHYBL/McPyVz/9AAAxBIAfwqARC7+RQCeOAoQxZV/IgA/cCAghMv+gQD8yLGA8Vzz5wQAIJQA/IQ/HcBgLvgLAvCSIwIjudof+2z1D1DR99998/mX367+Keb4+59/tfpHIJ31f5UXwOscFxjDdX6LALzJoYEBXOQrBOAaRwdac4WvE4B3OEDQlMv7LgEACCUA7/PnCGjHtb2FANzEYYJGXNgbCcCtHClowVW9nQDcwcGC4lzSuwjAfRwvKMv1vJcA3M0hg4JczA0EYAtHDUpxJbcRgI0cOCjCZdxMALZz7GA51/ARn3zx1derf4be/A9HwyrW/0FeAI9yBGEJV+9xArADBxFO5tLtwv8j2D6ejqOvg+Bopn9HXgB7cjThUK7YvgRgZw4oHMTl2p0A7M8xhd25VkcQgEM4rLAjF+ogAnAURxZ24SodRwAO5ODCg1yiQ/lroMfy10NhG9N/Ai+AMzjKcBdX5hwCcBIHGm7kspxGAM7jWMO7XJMz+R3AqfxKAN5i+s/nBbCAgw4vuBRLCMAajjt84Dqs4iugZXwdBKZ/LS+AxVwAYjn8ywnAeq4BgRz7CnwFVIKvg8hh+uvwAijExWA8h7wUL4BaPAWYyvQX5AVQkavCMI50TV4ARXkKMIPpr8wLoDSXh9Yc4OK8AKrzFKAj09+CF0APrhONOK5deAG04SlAfaa/Fy+AZlwwynI42/EC6MdTgGpMf1MC0JUMUIHpb00AepMBVjH9A/gdwASuIidz5GbwAhjCU4BzmP5JBGAUGeA4pn8eARhIBtiX6Z9KAMaSAR5n+mcTgOFkgG1MfwIBiCAD3M705xCAIDLAdaY/jQDE+XDJlYAndj+WAOTyIMD0hxOAdDKQyfRzEQCe+F4ohN3nOQHgJzwIpjL9fEwAeIUHwRh2nysEgGuUoCm7zy0EgJsoQQt2n7sIAPdRgoLsPtsIABspwXJ2nwcJAI9SgpPZffYiAOzm+TCJwb6MPkcQAA7hWbALu8+hBIBjvZgwPbjO4nMmAeBUvib6mNFnFQFgmdjHgcWnCAGgio9ncUYSzD1lCQB1vTWdNcNg6GlHAOjn+tQelwcTzzACwDRmGm706eofAIA1BAAglAAAhBIAgFACABBKAABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEIJAEAoAQAIJQAAoQQAIJQAAIQSAIBQAgAQSgAAQgkAQCgBAAglAAChBAAglAAAhBIAgFACABBKAABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEIJAECo/wO4sn30VF69pwAAAABJRU5ErkJggg=="
_ICON_192 = _b64.b64decode(_ICON_192_B64)
_ICON_512 = _b64.b64decode(_ICON_512_B64)

def _row(row):
    """Convert a psycopg2 DictRow to a plain dict, converting Decimal→float."""
    if row is None:
        return None
    return {k: float(v) if isinstance(v, decimal.Decimal) else v for k, v in dict(row).items()}

def _fmt_date(d):
    """Format a date as MM/DD/YYYY. Accepts datetime.date, datetime, or YYYY-MM-DD string."""
    if not d:
        return ''
    if hasattr(d, 'strftime'):
        return d.strftime('%m/%d/%Y')
    s = str(d)[:10]
    if len(s) == 10 and s[4] == '-':
        return f"{s[5:7]}/{s[8:10]}/{s[0:4]}"
    return s

BUSINESS_NAME    = os.getenv("BUSINESS_NAME",    "Rent a Party, LLC")
BUSINESS_PHONE   = os.getenv("BUSINESS_PHONE",   "")
BUSINESS_EMAIL   = os.getenv("BUSINESS_EMAIL",   "")
BUSINESS_ADDRESS = os.getenv("BUSINESS_ADDRESS", "")

DELIVERY_THRESHOLD = _float("DELIVERY_THRESHOLD", "15")
DELIVERY_BASE_FEE  = _float("DELIVERY_BASE_FEE",  "55")
DELIVERY_RATE      = _float("DELIVERY_RATE",       "3.80")

GOOGLE_MAPS_KEY    = os.getenv("GOOGLE_MAPS_KEY",    "")
DATABASE_URL       = os.getenv("DATABASE_URL",       "")
OWNER_EMAIL        = os.getenv("OWNER_EMAIL",        "")
GMAIL_USER         = os.getenv("GMAIL_USER",         "")
GMAIL_APP_PASSWORD = os.getenv("GMAIL_APP_PASSWORD", "")
ADMIN_PASSWORD     = os.getenv("ADMIN_PASSWORD",     "admin123")

STRIPE_SECRET_KEY     = os.getenv("STRIPE_SECRET_KEY",     "")
STRIPE_WEBHOOK_SECRET = os.getenv("STRIPE_WEBHOOK_SECRET", "")
BASE_URL              = os.getenv("BASE_URL", "").rstrip("/")
CRON_SECRET           = os.getenv("CRON_SECRET", "")

if STRIPE_SECRET_KEY:
    stripe.api_key = STRIPE_SECRET_KEY


# ══════════════════════════════════════════════════════════════════════════════
#  DATABASE
# ══════════════════════════════════════════════════════════════════════════════

def get_db():
    if not DATABASE_URL:
        log.warning("DATABASE_URL not set")
        return None
    try:
        return psycopg2.connect(DATABASE_URL, sslmode="require")
    except Exception as e:
        log.error(f"DB connection failed: {e}")
        return None


def init_db():
    """Create tables and run column migrations on startup."""
    conn = get_db()
    if not conn:
        return
    try:
        cur = conn.cursor()

        # Create bookings table
        cur.execute("""
            CREATE TABLE IF NOT EXISTS bookings (
                id               SERIAL PRIMARY KEY,
                created_at       TIMESTAMPTZ DEFAULT NOW(),
                status           VARCHAR(20) DEFAULT 'pending',

                full_name        VARCHAR(255),
                company_name     VARCHAR(255),
                renter_street    VARCHAR(255),
                renter_city      VARCHAR(100),
                renter_state     VARCHAR(50),
                renter_zip       VARCHAR(20),
                phone            VARCHAR(50),
                email            VARCHAR(255),

                event_start_date DATE,
                event_end_date   DATE,
                event_start_time VARCHAR(20),
                event_end_time   VARCHAR(20),
                setup_time       VARCHAR(20),
                venue_type       VARCHAR(20),
                venue_latest_pickup VARCHAR(20),

                event_street     VARCHAR(255),
                event_city       VARCHAR(100),
                event_state      VARCHAR(50),
                event_zip        VARCHAR(20),

                exact_time_delivery BOOLEAN DEFAULT FALSE,
                delivery_location   TEXT,
                delivery_fee        DECIMAL(10,2) DEFAULT 0,
                distance_miles      DECIMAL(6,1),

                items_json       TEXT,
                items_subtotal   DECIMAL(10,2) DEFAULT 0,
                exact_time_fee   DECIMAL(10,2) DEFAULT 0,
                grand_total      DECIMAL(10,2) DEFAULT 0,
                notes            TEXT,

                stripe_payment_link TEXT,
                stripe_session_id   TEXT
            )
        """)

        # Payment links tracker table
        cur.execute("""
            CREATE TABLE IF NOT EXISTS payment_links (
                id             SERIAL PRIMARY KEY,
                booking_id     INTEGER REFERENCES bookings(id) ON DELETE CASCADE,
                label          TEXT,
                amount         DECIMAL(10,2),
                url            TEXT,
                stripe_link_id TEXT,
                status         VARCHAR(20) DEFAULT 'active',
                created_at     TIMESTAMPTZ DEFAULT NOW()
            )
        """)

        # Migrations: add new columns to existing tables (safe to run every time)
        migrations = [
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS stripe_payment_link TEXT",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS stripe_session_id TEXT",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS final_payment_link TEXT",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS final_reminder_sent BOOLEAN DEFAULT FALSE",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS auto_invoice_sent BOOLEAN DEFAULT FALSE",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS archived BOOLEAN DEFAULT FALSE",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS tax_rate DECIMAL(5,4) DEFAULT 0",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS tax_amount DECIMAL(10,2) DEFAULT 0",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS tax_exempt BOOLEAN DEFAULT FALSE",
            "ALTER TABLE customers ADD COLUMN IF NOT EXISTS tax_exempt BOOLEAN DEFAULT FALSE",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS delivery_status TEXT DEFAULT NULL",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS late_night_fee DECIMAL(10,2) DEFAULT 0",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS amount_paid DECIMAL(10,2) DEFAULT 0",
            # Clean up literal 'None' strings left by Booqable import
            "UPDATE bookings SET phone         = NULL WHERE phone         = 'None'",
            "UPDATE bookings SET renter_street = NULL WHERE renter_street = 'None'",
            "UPDATE bookings SET renter_city   = NULL WHERE renter_city   = 'None'",
            "UPDATE bookings SET renter_state  = NULL WHERE renter_state  = 'None'",
            "UPDATE bookings SET renter_zip    = NULL WHERE renter_zip    = 'None'",
            "UPDATE bookings SET company_name  = NULL WHERE company_name  = 'None'",
            # Set all Marquee Letter items to $85 (name = "Marquee A" through "Marquee Z")
            "UPDATE inventory SET price = 85 WHERE TRIM(name) SIMILAR TO 'Marquee [A-Za-z]'",
            # Admin-only private notes
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS admin_notes TEXT",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS view_token TEXT DEFAULT NULL",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS discount_type VARCHAR(10) DEFAULT NULL",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS discount_value DECIMAL(10,2) DEFAULT 0",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS discount_amount DECIMAL(10,2) DEFAULT 0",
        ]
        for m in migrations:
            try:
                cur.execute("SAVEPOINT mig")
                cur.execute(m)
                cur.execute("RELEASE SAVEPOINT mig")
            except Exception as me:
                cur.execute("ROLLBACK TO SAVEPOINT mig")
                log.warning(f"Migration warning: {me}")

        # Create customers table
        cur.execute("""
            CREATE TABLE IF NOT EXISTS customers (
                id           SERIAL PRIMARY KEY,
                created_at   TIMESTAMPTZ DEFAULT NOW(),
                full_name    VARCHAR(255) NOT NULL,
                company_name VARCHAR(255),
                email        VARCHAR(255),
                phone        VARCHAR(50),
                street       VARCHAR(255),
                city         VARCHAR(100),
                state        VARCHAR(50),
                zip          VARCHAR(20),
                notes        TEXT
            )
        """)
        # Unique index on email so ON CONFLICT works for upserts
        cur.execute("""
            CREATE UNIQUE INDEX IF NOT EXISTS customers_email_idx
            ON customers (email) WHERE email IS NOT NULL
        """)

        # Import all existing booking customers into customers table (safe to run every time)
        try:
            cur.execute("SAVEPOINT cust_import")
            cur.execute("""
                INSERT INTO customers (full_name, company_name, email, phone, street, city, state, zip)
                SELECT DISTINCT ON (email)
                    full_name, company_name, email, phone,
                    renter_street, renter_city, renter_state, renter_zip
                FROM bookings
                WHERE email IS NOT NULL
                ORDER BY email, created_at DESC
                ON CONFLICT (email) WHERE email IS NOT NULL DO UPDATE SET
                    full_name    = EXCLUDED.full_name,
                    company_name = EXCLUDED.company_name,
                    phone        = EXCLUDED.phone,
                    street       = EXCLUDED.street,
                    city         = EXCLUDED.city,
                    state        = EXCLUDED.state,
                    zip          = EXCLUDED.zip
            """)
            cur.execute("RELEASE SAVEPOINT cust_import")
            log.info("Existing booking customers synced to customers table")
        except Exception as ie:
            cur.execute("ROLLBACK TO SAVEPOINT cust_import")
            log.warning(f"Customer import warning: {ie}")

        # Create inventory table
        cur.execute("""
            CREATE TABLE IF NOT EXISTS inventory (
                id         VARCHAR(100) PRIMARY KEY,
                name       VARCHAR(255) NOT NULL,
                price      DECIMAL(10,2) NOT NULL DEFAULT 0,
                total      INT NOT NULL DEFAULT 0,
                sort_order INT NOT NULL DEFAULT 0
            )
        """)
        # Seed from PRODUCTS constant if inventory table is empty
        cur.execute("SELECT COUNT(*) FROM inventory")
        if cur.fetchone()[0] == 0:
            for i, p in enumerate(PRODUCTS):
                cur.execute(
                    "INSERT INTO inventory (id, name, price, total, sort_order) VALUES (%s, %s, %s, %s, %s)",
                    (p["id"], p["name"], p["price"], p["total"], i)
                )
            log.info("Inventory seeded from PRODUCTS default list")

        conn.commit()
        cur.close()
        conn.close()
        log.info("Database ready")
    except Exception as e:
        log.error(f"DB init error: {e}")


# ── Run on startup ─────────────────────────────────────────────────────────
with app.app_context():
    init_db()


# ══════════════════════════════════════════════════════════════════════════════
#  PRODUCT CATALOG — load from DB (falls back to hardcoded PRODUCTS)
# ══════════════════════════════════════════════════════════════════════════════

def get_products():
    """Load product catalog from inventory table; fall back to PRODUCTS constant."""
    conn = get_db()
    if not conn:
        return PRODUCTS
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("SELECT * FROM inventory ORDER BY sort_order, name")
        rows = cur.fetchall()
        cur.close()
        conn.close()
        if rows:
            products = []
            for r in rows:
                p = dict(r)
                p["price"] = float(p["price"])
                p["total"] = int(p["total"])
                products.append(p)
            return products
    except Exception as e:
        log.error(f"get_products error: {e}")
    return PRODUCTS


# ══════════════════════════════════════════════════════════════════════════════
#  INVENTORY CHECKING
# ══════════════════════════════════════════════════════════════════════════════

def get_available(start_date_str, end_date_str, exclude_id=None):
    """
    Returns {product_id: available_qty} for a date range.
    Locks inventory for both CONFIRMED (paid in full) and ACCEPTED (deposit paid / partially paid).
    Also matches items by name for Booqable-imported bookings that lack a product id.
    """
    products   = get_products()
    available  = {p["id"]: p["total"] for p in products}
    # Build name → id map so name-only items (e.g. Booqable imports) are matched
    name_to_id = {p["name"].lower(): p["id"] for p in products}
    conn = get_db()
    if not conn:
        return available
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        query = """
            SELECT items_json FROM bookings
            WHERE status IN ('confirmed', 'accepted')
              AND event_start_date <= %s
              AND event_end_date   >= %s
        """
        params = [end_date_str, start_date_str]
        if exclude_id:
            query += " AND id != %s"
            params.append(exclude_id)
        cur.execute(query, params)
        rows = cur.fetchall()
        cur.close()
        conn.close()
        for row in rows:
            try:
                items = json.loads(row["items_json"] or "[]")
                for item in items:
                    # Match by product id first, fall back to name lookup
                    pid = item.get("id") or name_to_id.get((item.get("name") or "").lower())
                    qty = int(item.get("qty") or 0)
                    if pid and pid in available and qty > 0:
                        available[pid] = max(0, available[pid] - qty)
            except Exception:
                pass
    except Exception as e:
        log.error(f"Inventory check error: {e}")
    return available


def get_inventory_conflicts():
    """
    Returns a list of conflicts where a confirmed/accepted booking needs more
    of an item than the inventory can supply given all other bookings on those dates.
    Each conflict: {booking_id, customer, event_date, item, needed, available, shortfall}
    """
    products   = get_products()
    prod_totals = {p["id"]: int(p["total"]) for p in products}
    name_to_pid = {p["name"].lower(): p["id"] for p in products}

    conn = get_db()
    if not conn:
        return []
    conflicts = []
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("""
            SELECT id, full_name, event_start_date, event_end_date, items_json
            FROM bookings
            WHERE status IN ('confirmed','accepted')
              AND event_start_date IS NOT NULL
              AND event_end_date   IS NOT NULL
        """)
        active = [_row(r) for r in cur.fetchall()]
        cur.close(); conn.close()

        for b in active:
            b_start = str(b.get("event_start_date",""))[:10]
            b_end   = str(b.get("event_end_date",""))[:10]

            # Sum qty reserved by every OTHER booking that overlaps these dates
            others_reserved = {}
            for o in active:
                if o["id"] == b["id"]:
                    continue
                o_start = str(o.get("event_start_date",""))[:10]
                o_end   = str(o.get("event_end_date",""))[:10]
                if o_start <= b_end and o_end >= b_start:  # date overlap
                    for item in json.loads(o.get("items_json") or "[]"):
                        pid = item.get("id") or name_to_pid.get((item.get("name") or "").lower())
                        qty = int(item.get("qty") or 0)
                        if pid and qty > 0:
                            others_reserved[pid] = others_reserved.get(pid, 0) + qty

            # Check this booking's items against what's left
            for item in json.loads(b.get("items_json") or "[]"):
                pid = item.get("id") or name_to_pid.get((item.get("name") or "").lower())
                qty = int(item.get("qty") or 0)
                if pid and qty > 0 and pid in prod_totals:
                    avail = max(0, prod_totals[pid] - others_reserved.get(pid, 0))
                    if qty > avail:
                        conflicts.append({
                            "booking_id": b["id"],
                            "customer":   b.get("full_name","Unknown"),
                            "event_date": b_start,
                            "item":       item.get("name",""),
                            "needed":     qty,
                            "available":  avail,
                            "shortfall":  qty - avail,
                        })
    except Exception as e:
        log.error(f"Conflict check error: {e}")
    return conflicts


def get_booking_inventory_check(booking_id):
    """
    For a specific booking (any status), check whether its items can be fulfilled
    given other confirmed/accepted bookings on the same dates.
    Returns list of {item, needed, available, shortfall}
    """
    products    = get_products()
    prod_totals = {p["id"]: int(p["total"]) for p in products}
    name_to_pid = {p["name"].lower(): p["id"] for p in products}

    conn = get_db()
    if not conn:
        return []
    issues = []
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("SELECT * FROM bookings WHERE id=%s", (booking_id,))
        row = cur.fetchone()
        if not row:
            cur.close(); conn.close()
            return []
        b       = _row(row)
        b_start = str(b.get("event_start_date", ""))[:10]
        b_end   = str(b.get("event_end_date",   ""))[:10]
        if not b_start or not b_end:
            cur.close(); conn.close()
            return []

        # All other confirmed/accepted bookings overlapping these dates
        cur.execute("""
            SELECT id, items_json, event_start_date, event_end_date
            FROM bookings
            WHERE status IN ('confirmed','accepted')
              AND id != %s
              AND event_start_date IS NOT NULL
              AND event_end_date   IS NOT NULL
              AND event_start_date <= %s
              AND event_end_date   >= %s
        """, (booking_id, b_end, b_start))
        others = [_row(r) for r in cur.fetchall()]
        cur.close(); conn.close()

        others_reserved = {}
        for o in others:
            for item in json.loads(o.get("items_json") or "[]"):
                pid = item.get("id") or name_to_pid.get((item.get("name") or "").lower())
                qty = int(item.get("qty") or 0)
                if pid and qty > 0:
                    others_reserved[pid] = others_reserved.get(pid, 0) + qty

        for item in json.loads(b.get("items_json") or "[]"):
            pid = item.get("id") or name_to_pid.get((item.get("name") or "").lower())
            qty = int(item.get("qty") or 0)
            if pid and qty > 0 and pid in prod_totals:
                avail = max(0, prod_totals[pid] - others_reserved.get(pid, 0))
                if qty > avail:
                    issues.append({
                        "item":      item.get("name", ""),
                        "needed":    qty,
                        "available": avail,
                        "shortfall": qty - avail,
                    })
    except Exception as e:
        log.error(f"Booking inventory check error: {e}")
    return issues


# ══════════════════════════════════════════════════════════════════════════════
#  DISTANCE & DELIVERY FEE
# ══════════════════════════════════════════════════════════════════════════════

def get_distance_miles(destination):
    if not GOOGLE_MAPS_KEY or not BUSINESS_ADDRESS or not destination:
        return None
    try:
        r = requests.get(
            "https://maps.googleapis.com/maps/api/distancematrix/json",
            params={"origins": BUSINESS_ADDRESS, "destinations": destination,
                    "units": "imperial", "key": GOOGLE_MAPS_KEY},
            timeout=10,
        )
        el = r.json()["rows"][0]["elements"][0]
        if el.get("status") != "OK":
            return None
        return round(el["distance"]["value"] / 1609.344, 1)
    except Exception as e:
        log.error(f"Distance error: {e}")
        return None


def calc_delivery_fee(miles):
    if miles is None:
        return DELIVERY_BASE_FEE, "flat fee (distance could not be verified)"
    if miles <= DELIVERY_THRESHOLD:
        return DELIVERY_BASE_FEE, f"{miles} mi — flat delivery fee"
    fee = round(miles * DELIVERY_RATE, 2)
    return fee, f"{miles} mi x ${DELIVERY_RATE:.2f}/mi"


# ══════════════════════════════════════════════════════════════════════════════
#  STRIPE
# ══════════════════════════════════════════════════════════════════════════════

def create_stripe_payment_link(booking_id, deposit_amount, customer_email, items_desc, product_name=None):
    """Create a Stripe Payment Link. Returns (url, stripe_link_id, error)."""
    if not STRIPE_SECRET_KEY:
        log.warning("STRIPE_SECRET_KEY not set — cannot create payment link")
        return None, None, "Stripe not configured"
    try:
        name = product_name or f"25% Deposit — Booking #{booking_id}"
        product = stripe.Product.create(
            name=name,
            description=(items_desc[:500] if items_desc else "Rental deposit"),
        )
        price = stripe.Price.create(
            unit_amount=int(round(deposit_amount * 100)),
            currency="usd",
            product=product.id,
        )
        kwargs = {
            "line_items": [{"price": price.id, "quantity": 1}],
            "metadata": {"booking_id": str(booking_id)},
        }
        if BASE_URL:
            kwargs["after_completion"] = {
                "type": "redirect",
                "redirect": {"url": f"{BASE_URL}/payment/success/{booking_id}"}
            }
        link = stripe.PaymentLink.create(**kwargs)
        log.info(f"Stripe Payment Link created for booking #{booking_id}: {link.url}")
        return link.url, link.id, None
    except Exception as e:
        log.error(f"Stripe Payment Link error: {e}")
        return None, None, str(e)


def save_payment_link(booking_id, label, amount, url, stripe_link_id):
    """Record a payment link in the payment_links table."""
    conn = get_db()
    if not conn:
        return
    try:
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO payment_links (booking_id, label, amount, url, stripe_link_id, status)
            VALUES (%s, %s, %s, %s, %s, 'active')
        """, (booking_id, label, amount, url, stripe_link_id))
        conn.commit()
        cur.close(); conn.close()
    except Exception as e:
        log.error(f"save_payment_link error: {e}")


def get_payment_links(booking_id):
    """Return all payment links for a booking, newest first."""
    conn = get_db()
    if not conn:
        return []
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("""
            SELECT id, label, amount, url, stripe_link_id, status, created_at
            FROM payment_links WHERE booking_id=%s ORDER BY created_at DESC
        """, (booking_id,))
        rows = [_row(r) for r in cur.fetchall()]
        cur.close(); conn.close()
        return rows
    except Exception as e:
        log.error(f"get_payment_links error: {e}")
        return []


# ══════════════════════════════════════════════════════════════════════════════
#  CONTRACT TEXT
# ══════════════════════════════════════════════════════════════════════════════

def build_contract_html(b, deposit_amount):
    """Build formatted HTML contract with booking details filled in."""
    customer_name = b.get('full_name', '')
    items = json.loads(b.get('items_json') or '[]')
    items_list = ', '.join(f"{i['qty']}x {i['name']}" for i in items)
    deposit_str = f"${deposit_amount:.2f}"
    event_date = str(b.get('event_start_date', ''))
    today_str = date.today().strftime("%B %d, %Y")

    return f"""
<div style="font-size:.84rem;color:#374151;line-height:1.75;font-family:-apple-system,sans-serif">

  <h3 style="font-size:1rem;font-weight:700;color:#1a365d;margin:0 0 1rem;border-bottom:2px solid #e2e8f0;padding-bottom:.5rem">
    NON-REFUNDABLE DEPOSIT AGREEMENT
  </h3>

  <p>This Non-Refundable Deposit Agreement is made and entered into by and between <strong>Rent a Party, LLC</strong>
  and <strong>{customer_name}</strong> ("Deposit Recipient") for the purpose of securing the date and time of
  <em>{items_list}</em> for event on <strong>{event_date}</strong>. The Deposit Provider agrees to provide a
  non-refundable deposit in the amount of <strong>{deposit_str}</strong> to secure the reservation.
  Throughout this agreement, <strong>{customer_name}</strong> shall also be referred to as "The Renter."</p>

  <p>Deposit Recipient acknowledges that the deposit is non-refundable and will be forfeited if any of the
  conditions outlined in this agreement occur. The conditions for forfeiture are as follows:</p>

  <ol style="margin:.75rem 0 .75rem 1.25rem;padding:0">
    <li style="margin-bottom:.4rem"><strong>DEPOSIT NEEDED IS TWENTY-FIVE PERCENT (25%) AND IS NOT REFUNDABLE UNDER ANY CIRCUMSTANCES.</strong></li>
    <li style="margin-bottom:.4rem">If canceled within 20 days of the scheduled event, 50% of all items will be charged.</li>
    <li style="margin-bottom:.4rem">If canceled within 10 days of the scheduled event, 75% of all items will be charged.</li>
    <li style="margin-bottom:.4rem">If canceled within 24 hours of the scheduled event, there will still be a 100% charge.</li>
    <li style="margin-bottom:.4rem">The scheduled event is not secured until deposit is paid in full. Full payment is required for bookings
    made within one week of the event. If Rent a Party, LLC is prevented or delayed in delivering or picking up equipment at the
    agreed-upon time and location due to the negligence of the Renter, the Renter shall be responsible for a fee of $75 per hour
    for any additional time required. The Renter agrees to pay the remaining balance 48 hours before the scheduled pick-up/drop-off.
    Failure to make payment 48 hours prior may result in the order being considered canceled. Renter agrees that a person 18 years
    or older must be present at time of delivery. Rent a Party, LLC does not offer refunds; postponed events due to inclement weather
    will receive store credits.</li>
  </ol>

  <p>Deposit Recipient agrees to the terms of this Agreement and acknowledges that they have read and understood all terms and
  conditions. This Agreement shall be governed by the laws of the State of Connecticut. <strong>By making the non-refundable payment,
  you agree to the terms and conditions stated in this agreement. No signature is required for this agreement to be legally binding.</strong></p>

  <h3 style="font-size:1rem;font-weight:700;color:#1a365d;margin:1.25rem 0 1rem;border-bottom:2px solid #e2e8f0;padding-bottom:.5rem">
    EQUIPMENT RENTAL TERMS
  </h3>

  <p>With the consensual agreement of the Owner leasing equipment(s) described above, the Renter agrees to the Terms and Conditions as follows:</p>

  <ol style="margin:.75rem 0 .75rem 1.25rem;padding:0">
    <li style="margin-bottom:.4rem">In the event any equipment upon its return is not in good repair, condition and working order (ordinary wear and tear excepted),
    the renter will be obligated to pay Owner for reasonable out-of-pocket expenses to restore such equipment.</li>
    <li style="margin-bottom:.4rem">If the Renter declines delivery service, the Renter agrees to return all equipment on or before the specified time.
    Late fees of $75 per hour will be charged for returns made after the specified time. The Renter assumes all responsibility for the equipment.</li>
    <li style="margin-bottom:.4rem">If Rent a Party, LLC is prevented or delayed in delivering or picking up equipment due to the negligence of the Renter,
    the Renter shall be responsible for a fee of $75 per hour for any additional time required.</li>
    <li style="margin-bottom:.4rem">The Renter has obtained authorization from the venue to use all equipment on their premises.</li>
    <li style="margin-bottom:.4rem">Renter may only use and operate any equipment for its intended purpose.</li>
    <li style="margin-bottom:.4rem">Renter shall install all equipment in a manner that allows for removal without damage.</li>
    <li style="margin-bottom:.4rem">Renter shall not make any additions, attachments, alterations or improvements to any equipment without prior written consent of Owner.</li>
    <li style="margin-bottom:.4rem">Renter agrees that all equipment received is in safe and proper order.</li>
    <li style="margin-bottom:.4rem">Renter may only use and operate all equipment for its intended purpose.</li>
    <li style="margin-bottom:.4rem">The Renter acknowledges that all equipment provided by Rent a Party, LLC is accurate and corresponds exactly to the equipment rental list.</li>
    <li style="margin-bottom:.4rem">Renter acknowledges that the quantity of equipment is accurate to what is stated in the equipment rental list.</li>
    <li style="margin-bottom:.4rem">Regarding deliveries without setup/breakdown package: all chairs must be stacked with the black circle facing up. If chairs are not stacked properly, a fee of $1 per rented chair may be charged.</li>
    <li style="margin-bottom:.4rem">Marquee items should not be exposed to moisture or rain, left outside overnight, or stood upon. Keep all marquee items dry at all times.</li>
    <li style="margin-bottom:.4rem">Items with electrical or battery-operated systems (speakers, microphones, etc.) should not be left outside overnight or exposed to moisture or rain.</li>
    <li style="margin-bottom:.4rem">Any water damage to rental products will result in the renter being responsible for the cost of repairing or replacing the damaged item(s).</li>
    <li style="margin-bottom:.4rem"><strong>OVERNIGHT RENTALS:</strong> Lessee understands that all equipment is to be locked up in a secure location overnight. The Renter is fully responsible for all equipment until it is returned or picked up by Rent a Party, LLC.</li>
  </ol>

  <p style="margin-top:1rem;font-style:italic;color:#6b7280;font-size:.8rem">
    Agreement date: {today_str} &nbsp;|&nbsp; Booking #{b.get('id')} &nbsp;|&nbsp; {customer_name}
  </p>
</div>
"""


# ══════════════════════════════════════════════════════════════════════════════
#  EMAIL
# ══════════════════════════════════════════════════════════════════════════════

def _send_email(to, subject, html, plain, reply_to=None):
    if not all([GMAIL_USER, GMAIL_APP_PASSWORD]):
        log.warning("Gmail not configured")
        return
    try:
        msg = MIMEMultipart("alternative")
        msg["From"]    = f"{BUSINESS_NAME} <{GMAIL_USER}>"
        msg["To"]      = to
        msg["Subject"] = subject
        if reply_to:
            msg["Reply-To"] = reply_to
        msg.attach(MIMEText(plain, "plain"))
        msg.attach(MIMEText(html,  "html"))
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as s:
            s.login(GMAIL_USER, GMAIL_APP_PASSWORD)
            s.send_message(msg)
        log.info(f"Email sent → {to}")
    except Exception as e:
        log.error(f"Email error: {e}")


def send_sms(body):
    """Send an SMS to the owner via Twilio REST API (no SDK required)."""
    account_sid = os.getenv("TWILIO_ACCOUNT_SID", "")
    auth_token  = os.getenv("TWILIO_AUTH_TOKEN",  "")
    from_number = os.getenv("TWILIO_FROM_NUMBER", "")
    to_number   = os.getenv("OWNER_PHONE",        "")
    if not all([account_sid, auth_token, from_number, to_number]):
        log.warning("SMS skipped — TWILIO_ACCOUNT_SID / TWILIO_AUTH_TOKEN / TWILIO_FROM_NUMBER / OWNER_PHONE not all set")
        return
    try:
        resp = requests.post(
            f"https://api.twilio.com/2010-04-01/Accounts/{account_sid}/Messages.json",
            auth=(account_sid, auth_token),
            data={"From": from_number, "To": to_number, "Body": body},
            timeout=10
        )
        if resp.status_code >= 400:
            log.warning(f"SMS send failed ({resp.status_code}): {resp.text[:200]}")
        else:
            log.info(f"Owner SMS sent → {to_number}")
    except Exception as e:
        log.error(f"SMS error: {e}")


def send_owner_email(b):
    """Send detailed booking notification to owner."""
    if not OWNER_EMAIL:
        return
    items = json.loads(b.get("items_json") or "[]")
    exact = b.get("exact_time_delivery", False)
    event_addr = f"{b.get('event_street','')}, {b.get('event_city','')}, {b.get('event_state','')} {b.get('event_zip','')}"
    renter_addr = f"{b.get('renter_street','')}, {b.get('renter_city','')}, {b.get('renter_state','')} {b.get('renter_zip','')}"
    item_rows = ""
    for it in items:
        item_rows += f"""
        <tr>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0">{it['name']}</td>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0;text-align:center">{it['qty']}</td>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0;text-align:right">${it['unit_price']:.2f}</td>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0;text-align:right;font-weight:600">${it['total']:.2f}</td>
        </tr>"""
    subject = f"New Booking #{b.get('id')} — {b.get('full_name')} | {_fmt_date(b.get('event_start_date'))}"
    html = f"""
<html><body style="font-family:-apple-system,sans-serif;background:#f0f4f8;padding:2rem 1rem">
<div style="max-width:640px;margin:0 auto">
  <div style="background:linear-gradient(135deg,#1a365d,#2b6cb0);border-radius:12px 12px 0 0;padding:1.5rem 2rem;color:white">
    <h2 style="margin:0">New Booking Request #{b.get('id')}</h2>
    <p style="margin:.4rem 0 0;opacity:.85">{BUSINESS_NAME} — Review in Admin Panel</p>
  </div>
  <div style="background:white;padding:2rem;border-radius:0 0 12px 12px;box-shadow:0 4px 16px rgba(0,0,0,.08)">
    <table style="width:100%;border-collapse:collapse;margin-bottom:1.5rem">
      <tr style="background:#ebf4ff"><td colspan="2" style="padding:10px 12px;font-weight:700;color:#2b6cb0;text-transform:uppercase;font-size:.85rem">Customer</td></tr>
      <tr><td style="padding:8px 12px;color:#718096;width:160px">Name</td><td style="padding:8px 12px;font-weight:600">{b.get('full_name')}</td></tr>
      <tr style="background:#f7fafc"><td style="padding:8px 12px;color:#718096">Address</td><td style="padding:8px 12px">{renter_addr}</td></tr>
      <tr><td style="padding:8px 12px;color:#718096">Phone</td><td style="padding:8px 12px">{b.get('phone')}</td></tr>
      <tr style="background:#f7fafc"><td style="padding:8px 12px;color:#718096">Email</td><td style="padding:8px 12px"><a href="mailto:{b.get('email')}">{b.get('email')}</a></td></tr>
    </table>
    <table style="width:100%;border-collapse:collapse;margin-bottom:1.5rem">
      <tr style="background:#ebf4ff"><td colspan="2" style="padding:10px 12px;font-weight:700;color:#2b6cb0;text-transform:uppercase;font-size:.85rem">Event</td></tr>
      <tr><td style="padding:8px 12px;color:#718096;width:160px">Dates</td><td style="padding:8px 12px;font-weight:600">{_fmt_date(b.get('event_start_date'))} to {_fmt_date(b.get('event_end_date'))}</td></tr>
      <tr style="background:#f7fafc"><td style="padding:8px 12px;color:#718096">Event Address</td><td style="padding:8px 12px">{event_addr}</td></tr>
    </table>
    <table style="width:100%;border-collapse:collapse;margin-bottom:1.5rem">
      <tr style="background:#ebf4ff">
        <th style="padding:10px 12px;text-align:left;color:#2b6cb0;font-size:.85rem">Item</th>
        <th style="padding:10px 12px;text-align:center;color:#2b6cb0;font-size:.85rem">Qty</th>
        <th style="padding:10px 12px;text-align:right;color:#2b6cb0;font-size:.85rem">Price</th>
        <th style="padding:10px 12px;text-align:right;color:#2b6cb0;font-size:.85rem">Total</th>
      </tr>
      {item_rows}
      {"<tr><td colspan='3' style='padding:8px 12px;border-bottom:1px solid #e2e8f0'>Exact Time Delivery</td><td style='padding:8px 12px;text-align:right;font-weight:600;border-bottom:1px solid #e2e8f0'>$175.00</td></tr>" if exact else ""}
      <tr style="background:#1a365d;color:white">
        <td colspan="3" style="padding:12px;font-weight:700">ESTIMATED TOTAL</td>
        <td style="padding:12px;text-align:right;font-weight:700;font-size:1.2rem">${b.get('grand_total',0):.2f}</td>
      </tr>
    </table>
    <div style="background:#ebf4ff;border-radius:8px;padding:1rem;text-align:center">
      <p style="margin:0;font-weight:700;color:#1a365d">Log in to Admin Panel to Accept or Deny</p>
    </div>
  </div>
</div></body></html>"""
    plain = f"NEW BOOKING #{b.get('id')}\n{b.get('full_name')} | {b.get('email')} | {b.get('phone')}\nEvent: {_fmt_date(b.get('event_start_date'))}\nTotal: ${b.get('grand_total',0):.2f}\n"
    _send_email(OWNER_EMAIL, subject, html, plain, reply_to=b.get("email"))


def send_customer_email(b):
    """Send initial confirmation to customer (booking received, pending review)."""
    email = b.get("email")
    first = b.get("full_name", "").split()[0]
    if not email:
        return
    token = b.get("view_token") or ""
    base_url = os.environ.get("APP_BASE_URL", "").rstrip("/")
    view_url = f"{base_url}/booking/view/{token}" if token and base_url else ""
    view_btn = f"""
    <div style="text-align:center;margin:1.25rem 0">
      <a href="{view_url}"
         style="display:inline-block;background:#2b6cb0;color:white;padding:.75rem 2rem;border-radius:8px;font-weight:700;font-size:.95rem;text-decoration:none">
        &#x1F4CB; View Your Order
      </a>
      <p style="margin:.5rem 0 0;font-size:.78rem;color:#718096">Bookmark this link to check your order anytime</p>
    </div>""" if view_url else ""

    # ── Build items table rows ──────────────────────────────────────────
    items = json.loads(b.get("items_json") or "[]")
    item_rows = ""
    for it in items:
        item_rows += (
            f"<tr>"
            f"<td style='padding:.45rem .6rem;border-bottom:1px solid #e2e8f0'>{it.get('name','')}</td>"
            f"<td style='padding:.45rem .6rem;border-bottom:1px solid #e2e8f0;text-align:center'>{it.get('qty',1)}</td>"
            f"<td style='padding:.45rem .6rem;border-bottom:1px solid #e2e8f0;text-align:right'>${float(it.get('total',0)):.2f}</td>"
            f"</tr>"
        )

    subtotal     = float(b.get("items_subtotal") or 0)
    delivery_fee = float(b.get("delivery_fee") or 0)
    exact_fee    = 175.0 if b.get("exact_time_delivery") else 0.0
    tax          = float(b.get("tax_amount") or 0)
    grand_total  = float(b.get("grand_total") or 0)

    delivery_row = (
        f"<tr><td colspan='2' style='padding:.4rem .6rem;color:#4a5568'>Delivery Fee</td>"
        f"<td style='padding:.4rem .6rem;text-align:right'>${delivery_fee:.2f}</td></tr>"
    ) if delivery_fee else ""
    exact_row = (
        f"<tr><td colspan='2' style='padding:.4rem .6rem;color:#4a5568'>Exact Time Delivery</td>"
        f"<td style='padding:.4rem .6rem;text-align:right'>${exact_fee:.2f}</td></tr>"
    ) if exact_fee else ""

    # ── Event details ───────────────────────────────────────────────────
    start_date   = b.get("event_start_date") or ""
    end_date     = b.get("event_end_date") or ""
    start_time   = b.get("event_start_time") or ""
    end_time     = b.get("event_end_time") or ""       # pickup time
    setup_time   = b.get("setup_time") or ""           # delivery time
    venue_type   = b.get("venue_type") or ""
    event_addr   = ", ".join(filter(None, [
        b.get("event_street",""), b.get("event_city",""),
        b.get("event_state",""), b.get("event_zip","")
    ]))
    delivery_addr = b.get("delivery_address") or ""

    date_display = f"{start_date} - {end_date}" if end_date and end_date != start_date else start_date

    time_rows_html = ""
    if start_time:
        time_rows_html += f"<tr><td style='padding:.3rem .5rem;color:#718096;font-size:.88rem'>Event Start</td><td style='padding:.3rem .5rem;font-size:.88rem'>{start_time}</td></tr>"
    if setup_time:
        time_rows_html += f"<tr><td style='padding:.3rem .5rem;color:#718096;font-size:.88rem'>Delivery Time</td><td style='padding:.3rem .5rem;font-size:.88rem'>{setup_time}</td></tr>"
    if end_time:
        time_rows_html += f"<tr><td style='padding:.3rem .5rem;color:#718096;font-size:.88rem'>Pickup Time</td><td style='padding:.3rem .5rem;font-size:.88rem'>{end_time}</td></tr>"

    venue_row   = f"<tr><td style='padding:.3rem .5rem;color:#718096;font-size:.88rem'>Venue Type</td><td style='padding:.3rem .5rem;font-size:.88rem'>{venue_type}</td></tr>" if venue_type else ""
    addr_row    = f"<tr><td style='padding:.3rem .5rem;color:#718096;font-size:.88rem'>Event Address</td><td style='padding:.3rem .5rem;font-size:.88rem'>{event_addr}</td></tr>" if event_addr else ""
    del_row     = f"<tr><td style='padding:.3rem .5rem;color:#718096;font-size:.88rem'>Delivery To</td><td style='padding:.3rem .5rem;font-size:.88rem'>{delivery_addr}</td></tr>" if delivery_addr and delivery_addr != event_addr else ""
    cust_addr   = b.get("customer_address") or ""
    cust_addr_row = f"<tr><td style='padding:.3rem .5rem;color:#718096;font-size:.88rem'>Your Address</td><td style='padding:.3rem .5rem;font-size:.88rem'>{cust_addr}</td></tr>" if cust_addr else ""

    subject = f"We received your rental request! - {BUSINESS_NAME}"
    html = f"""
<html><body style="font-family:-apple-system,sans-serif;background:#f0f4f8;padding:2rem 1rem">
<div style="max-width:580px;margin:0 auto;background:white;border-radius:12px;overflow:hidden;box-shadow:0 4px 16px rgba(0,0,0,.08)">
  <div style="background:linear-gradient(135deg,#1a365d,#2b6cb0);padding:2rem;color:white;text-align:center">
    <h2 style="margin:0">Request Received!</h2>
    <p style="margin:.5rem 0 0;opacity:.85">{BUSINESS_NAME}</p>
  </div>
  <div style="padding:2rem">
    <p>Hi <strong>{first}</strong>,</p>
    <p style="color:#4a5568;line-height:1.7;margin:.75rem 0">
      Thank you for your rental inquiry! We have received your request and will review it shortly.
      Below is a full summary of everything you submitted for your records.
    </p>

    <div style="background:#f0f4f8;border-radius:8px;padding:1rem;margin:1rem 0;text-align:center">
      <p style="margin:0;font-weight:600;color:#2d3748">Booking Reference</p>
      <p style="margin:.3rem 0 0;font-size:1.5rem;font-weight:700;color:#2b6cb0">#{b.get('id')}</p>
    </div>
    {view_btn}

    <h3 style="margin:1.5rem 0 .5rem;color:#1a365d;font-size:.9rem;text-transform:uppercase;letter-spacing:.06em;border-bottom:2px solid #e2e8f0;padding-bottom:.4rem">Contact Information</h3>
    <table style="width:100%;border-collapse:collapse">
      <tr><td style="padding:.3rem .5rem;color:#718096;font-size:.88rem;width:38%">Name</td><td style="padding:.3rem .5rem;font-size:.88rem">{b.get('full_name','')}</td></tr>
      <tr><td style="padding:.3rem .5rem;color:#718096;font-size:.88rem">Email</td><td style="padding:.3rem .5rem;font-size:.88rem">{b.get('email','')}</td></tr>
      <tr><td style="padding:.3rem .5rem;color:#718096;font-size:.88rem">Phone</td><td style="padding:.3rem .5rem;font-size:.88rem">{b.get('phone','')}</td></tr>
      {cust_addr_row}
    </table>

    <h3 style="margin:1.5rem 0 .5rem;color:#1a365d;font-size:.9rem;text-transform:uppercase;letter-spacing:.06em;border-bottom:2px solid #e2e8f0;padding-bottom:.4rem">Event Details</h3>
    <table style="width:100%;border-collapse:collapse">
      <tr><td style="padding:.3rem .5rem;color:#718096;font-size:.88rem;width:38%">Date(s)</td><td style="padding:.3rem .5rem;font-size:.88rem">{date_display}</td></tr>
      {time_rows_html}
      {venue_row}
      {addr_row}
      {del_row}
    </table>

    <h3 style="margin:1.5rem 0 .5rem;color:#1a365d;font-size:.9rem;text-transform:uppercase;letter-spacing:.06em;border-bottom:2px solid #e2e8f0;padding-bottom:.4rem">Items Ordered</h3>
    <table style="width:100%;border-collapse:collapse">
      <thead>
        <tr style="background:#f7fafc">
          <th style="padding:.45rem .6rem;text-align:left;color:#4a5568;font-size:.85rem">Item</th>
          <th style="padding:.45rem .6rem;text-align:center;color:#4a5568;font-size:.85rem">Qty</th>
          <th style="padding:.45rem .6rem;text-align:right;color:#4a5568;font-size:.85rem">Price</th>
        </tr>
      </thead>
      <tbody>{item_rows}</tbody>
    </table>
    <table style="width:100%;border-collapse:collapse;margin-top:.25rem">
      <tr><td colspan="2" style="padding:.4rem .6rem;color:#4a5568;font-size:.88rem">Items Subtotal</td>
          <td style="padding:.4rem .6rem;text-align:right;font-size:.88rem">${subtotal:.2f}</td></tr>
      {delivery_row}
      {exact_row}
      <tr><td colspan="2" style="padding:.4rem .6rem;color:#4a5568;font-size:.88rem">CT Sales Tax (6.35%)</td>
          <td style="padding:.4rem .6rem;text-align:right;font-size:.88rem">${tax:.2f}</td></tr>
      <tr style="background:#f0f4f8;font-weight:700">
        <td colspan="2" style="padding:.55rem .6rem;border-top:2px solid #cbd5e0;font-size:.9rem">Estimated Total</td>
        <td style="padding:.55rem .6rem;border-top:2px solid #cbd5e0;text-align:right;font-size:.9rem">${grand_total:.2f}</td>
      </tr>
    </table>

    <div style="background:#fffbeb;border:1px solid #fcd34d;border-radius:8px;padding:.85rem 1rem;margin:1.25rem 0">
      <p style="margin:0;font-size:.88rem;color:#78350f;line-height:1.6">
        <strong>Please note:</strong> This is an estimate based on your submission.
        The final invoice will be sent to you before any payment is required.
      </p>
    </div>
    <p style="color:#4a5568;line-height:1.7;font-size:.9rem">
      Keep your booking reference handy.{f' Questions? Call <strong>{BUSINESS_PHONE}</strong>.' if BUSINESS_PHONE else ''}
    </p>
    <p style="color:#2d3748;font-weight:600;margin-top:1.5rem">- The {BUSINESS_NAME} Team</p>
  </div>
</div></body></html>"""

    item_lines = "\n".join(
        f"  {it.get('name','')} x{it.get('qty',1)}  ${float(it.get('total',0)):.2f}"
        for it in items
    )
    plain = (
        f"Hi {first},\n\n"
        f"Thank you for your rental inquiry! Here is a summary of your submission.\n\n"
        f"BOOKING REFERENCE: #{b.get('id')}\n"
        + (f"View your order: {view_url}\n" if view_url else "") +
        f"\n--- CONTACT ---\n"
        f"Name:  {b.get('full_name','')}\n"
        f"Email: {b.get('email','')}\n"
        f"Phone: {b.get('phone','')}\n"
        + (f"Address: {cust_addr}\n" if cust_addr else "") +
        f"\n--- EVENT ---\n"
        f"Date(s): {date_display}\n"
        + (f"Event Start:   {start_time}\n" if start_time else "")
        + (f"Delivery Time: {setup_time}\n" if setup_time else "")
        + (f"Pickup Time:   {end_time}\n" if end_time else "")
        + (f"Venue: {venue_type}\n" if venue_type else "")
        + (f"Address: {event_addr}\n" if event_addr else "") +
        f"\n--- ITEMS ORDERED ---\n{item_lines}\n\n"
        f"Subtotal:    ${subtotal:.2f}\n"
        + (f"Delivery:    ${delivery_fee:.2f}\n" if delivery_fee else "")
        + (f"Exact Time:  ${exact_fee:.2f}\n" if exact_fee else "") +
        f"Tax (6.35%): ${tax:.2f}\n"
        f"Est. Total:  ${grand_total:.2f}\n\n"
        f"Please note: this is an estimate. The final invoice will be sent before any payment is required.\n\n"
        f"- {BUSINESS_NAME}"
    )
    _send_email(email, subject, html, plain)


def send_accepted_email(b, charge_amount, payment_type="deposit"):
    """
    Send invoice + contract + Stripe payment link to customer.
    payment_type: "deposit" (25% now, rest later) or "full" (100% required now).
    """
    email = b.get("email")
    first = b.get("full_name", "").split()[0]
    if not email:
        return

    payment_link = b.get("stripe_payment_link", "")
    items = json.loads(b.get("items_json") or "[]")
    exact = b.get("exact_time_delivery", False)
    grand_total = float(b.get("grand_total") or 0)
    remaining = round(grand_total - charge_amount, 2)
    event_addr = f"{b.get('event_street','')}, {b.get('event_city','')}, {b.get('event_state','')} {b.get('event_zip','')}"

    is_deposit = (payment_type == "deposit")

    # Labels based on payment type
    if is_deposit:
        due_label      = "25% Deposit Due Now"
        pay_btn_label  = f"Pay ${charge_amount:.2f} Deposit Now"
        header_sub     = "Pay your 25% deposit to secure your date"
        urgency_msg    = "Your booking is <strong>not secured</strong> until the deposit is paid. Pay now to lock in your date."
        balance_line   = f'<div style="border-top:1px solid #c6f6d5;margin-top:1rem;padding-top:1rem;font-size:.87rem;color:#4a5568"><p style="margin:0"><strong>Remaining balance:</strong> ${remaining:.2f} — due <strong>48 hours before</strong> your event on {b.get("event_start_date")}</p></div>'
        balance_plain  = f"Remaining balance: ${remaining:.2f} — due 48 hours before your event."
    else:
        due_label      = "Full Payment Required"
        pay_btn_label  = f"Pay Full Amount ${charge_amount:.2f}"
        header_sub     = "Full payment required — your event is within 7 days"
        urgency_msg    = "Because your event is <strong>within 7 days</strong>, full payment is required to secure your booking."
        balance_line   = ""
        balance_plain  = "Full payment required — no remaining balance."

    tax_amount_val  = float(b.get("tax_amount") or 0)
    tax_rate_val    = float(b.get("tax_rate") or 0)
    is_tax_exempt_b = bool(b.get("tax_exempt"))
    disc_amount     = float(b.get("discount_amount") or 0)
    disc_type       = b.get("discount_type") or ""
    disc_value      = float(b.get("discount_value") or 0)

    item_rows = ""
    for it in items:
        item_rows += f"""
        <tr>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0">{it['name']}</td>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0;text-align:center">{it['qty']}</td>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0;text-align:right">${it['unit_price']:.2f}</td>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0;text-align:right;font-weight:600">${it['total']:.2f}</td>
        </tr>"""

    if disc_amount > 0:
        disc_label = f"{disc_value:.1f}% Discount" if disc_type == "percent" else f"${disc_value:.2f} Discount"
        disc_row_html  = f'<tr style="background:#f0fdf4"><td colspan="3" style="padding:8px 12px;border-bottom:1px solid #e2e8f0;color:#166534;font-weight:600">🏷️ {disc_label}</td><td style="padding:8px 12px;text-align:right;font-weight:700;border-bottom:1px solid #e2e8f0;color:#16a34a">- ${disc_amount:.2f}</td></tr>'
        disc_row_plain = f"  {disc_label}:    -${disc_amount:.2f}\n"
    else:
        disc_row_html  = ""
        disc_row_plain = ""

    if is_tax_exempt_b:
        tax_row_html  = '<tr><td colspan="3" style="padding:8px 12px;border-bottom:1px solid #e2e8f0;color:#276749">CT Sales Tax <span style="font-size:.76rem;background:#c6f6d5;color:#276749;border-radius:4px;padding:.1rem .35rem;margin-left:.3rem">TAX EXEMPT</span></td><td style="padding:8px 12px;text-align:right;font-weight:600;border-bottom:1px solid #e2e8f0;color:#276749">$0.00</td></tr>'
        tax_row_plain = "  CT Sales Tax:       $0.00 (TAX EXEMPT)\n"
    elif tax_amount_val:
        tax_row_html  = f'<tr><td colspan="3" style="padding:8px 12px;border-bottom:1px solid #e2e8f0;color:#718096">CT Sales Tax ({tax_rate_val*100:.2f}%)</td><td style="padding:8px 12px;text-align:right;font-weight:600;border-bottom:1px solid #e2e8f0">${tax_amount_val:.2f}</td></tr>'
        tax_row_plain = f"  CT Sales Tax ({tax_rate_val*100:.2f}%): ${tax_amount_val:.2f}\n"
    else:
        tax_row_html  = ""
        tax_row_plain = ""

    payment_btn = f"""
    <div style="text-align:center;margin:1.5rem 0">
      <a href="{payment_link}"
         style="display:inline-block;background:linear-gradient(135deg,#276749,#38a169);color:white;padding:1.1rem 2.75rem;border-radius:10px;font-weight:700;font-size:1.15rem;text-decoration:none;letter-spacing:.3px;box-shadow:0 4px 12px rgba(39,103,73,.35)">
        {pay_btn_label}
      </a>
      <p style="margin:.6rem 0 0;font-size:.82rem;color:#718096">Secure payment powered by Stripe</p>
    </div>""" if payment_link else f"""
    <div style="background:#fffaf0;border:2px solid #ed8936;border-radius:10px;padding:1.25rem;text-align:center;margin:1.5rem 0">
      <p style="font-weight:700;color:#744210">Amount Due: ${charge_amount:.2f}</p>
      <p style="color:#744210;font-size:.9rem">We will send your payment link shortly.{f" Questions? Call {BUSINESS_PHONE}" if BUSINESS_PHONE else ""}</p>
    </div>"""

    contract_html = build_contract_html(b, charge_amount)

    subject_tag = "Deposit Required" if is_deposit else "Full Payment Required"
    subject = f"Booking Accepted — {subject_tag} | {BUSINESS_NAME}"

    html = f"""
<html><body style="font-family:-apple-system,sans-serif;background:#f0f4f8;padding:2rem 1rem">
<div style="max-width:640px;margin:0 auto">

  <div style="background:linear-gradient(135deg,#276749,#38a169);border-radius:12px 12px 0 0;padding:1.75rem 2rem;color:white;text-align:center">
    <div style="font-size:2.2rem;margin-bottom:.4rem">&#127881; Booking Accepted!</div>
    <h2 style="margin:0;font-weight:700;font-size:1.2rem">Booking #{b.get('id')} &mdash; {BUSINESS_NAME}</h2>
    <p style="margin:.5rem 0 0;opacity:.88;font-size:.95rem">{header_sub}</p>
  </div>

  <div style="background:white;padding:2rem;border-radius:0 0 12px 12px;box-shadow:0 4px 16px rgba(0,0,0,.08)">

    <p style="color:#2d3748;font-size:1.05rem;margin-bottom:.75rem">Hi <strong>{first}</strong>,</p>
    <p style="color:#4a5568;line-height:1.7;margin-bottom:1.25rem">
      Thank you for choosing Rent a Party, LLC. We are pleased to confirm that your rental request has been reviewed and we have availability for your event.
      Please carefully review your invoice below, read the rental agreement at the bottom of this email, and submit your payment at your earliest convenience to secure your reservation.
    </p>

    <!-- Event Summary box -->
    <div style="background:#f0fff4;border:1.5px solid #68d391;border-radius:10px;padding:1rem 1.25rem;margin-bottom:1.5rem;font-size:.9rem;color:#2d3748">
      <div style="margin-bottom:.3rem"><strong>Event Date:</strong> {_fmt_date(b.get('event_start_date'))} &rarr; {_fmt_date(b.get('event_end_date'))}</div>
      <div style="margin-bottom:.3rem"><strong>Location:</strong> {event_addr}</div>
      <div><strong>Deliver to:</strong> {b.get('delivery_location','')}</div>
    </div>

    <!-- Invoice table -->
    <h3 style="color:#1a365d;font-size:.95rem;font-weight:700;margin:0 0 .75rem;text-transform:uppercase;letter-spacing:.5px">Invoice</h3>
    <table style="width:100%;border-collapse:collapse;font-size:.9rem;margin-bottom:1.5rem">
      <thead>
        <tr style="background:#ebf4ff">
          <th style="padding:9px 12px;text-align:left;color:#2b6cb0;font-size:.78rem;text-transform:uppercase">Item</th>
          <th style="padding:9px 12px;text-align:center;color:#2b6cb0;font-size:.78rem;text-transform:uppercase">Qty</th>
          <th style="padding:9px 12px;text-align:right;color:#2b6cb0;font-size:.78rem;text-transform:uppercase">Unit Price</th>
          <th style="padding:9px 12px;text-align:right;color:#2b6cb0;font-size:.78rem;text-transform:uppercase">Total</th>
        </tr>
      </thead>
      <tbody>
        {item_rows}
        {"<tr><td colspan='3' style='padding:8px 12px;border-bottom:1px solid #e2e8f0'>Exact Time Delivery</td><td style='padding:8px 12px;text-align:right;font-weight:600;border-bottom:1px solid #e2e8f0'>$175.00</td></tr>" if exact else ""}
        <tr>
          <td colspan="3" style="padding:8px 12px;border-bottom:1px solid #e2e8f0;color:#718096">Delivery Fee ({b.get('distance_miles','?')} mi)</td>
          <td style="padding:8px 12px;text-align:right;font-weight:600;border-bottom:1px solid #e2e8f0">${b.get('delivery_fee',0):.2f}</td>
        </tr>
        {disc_row_html}
        {tax_row_html}
        <tr style="background:#1a365d;color:white">
          <td colspan="3" style="padding:11px 12px;font-weight:700;font-size:1rem">TOTAL</td>
          <td style="padding:11px 12px;text-align:right;font-weight:700;font-size:1.2rem">${grand_total:.2f}</td>
        </tr>
      </tbody>
    </table>

    <!-- Payment section -->
    <div style="background:#f0fff4;border:2px solid #38a169;border-radius:12px;padding:1.5rem;margin-bottom:1.5rem;text-align:center">
      <p style="font-size:.82rem;color:#276749;margin:0 0 .3rem;font-weight:700;text-transform:uppercase;letter-spacing:.6px">{due_label}</p>
      <p style="font-size:2.75rem;font-weight:800;color:#276749;margin:.2rem 0 .1rem;line-height:1">${charge_amount:.2f}</p>
      {f'<p style="font-size:.85rem;color:#718096;margin:.2rem 0 0">of ${grand_total:.2f} total</p>' if is_deposit else ""}
      {payment_btn}
      {balance_line}
    </div>

    <!-- Urgency note -->
    <div style="background:#fffaf0;border-left:4px solid #ed8936;padding:1rem 1.25rem;border-radius:0 8px 8px 0;margin-bottom:1.75rem;font-size:.88rem;color:#744210">
      <strong>Important:</strong> {urgency_msg}
      Inventory is first-come-first-paid &mdash; we cannot hold your reservation without payment.
    </div>

    <!-- Contract -->
    <div style="border-top:2px solid #e2e8f0;padding-top:1.5rem">
      <h3 style="color:#1a365d;font-size:.95rem;font-weight:700;margin:0 0 .4rem;text-transform:uppercase;letter-spacing:.5px">Rental Agreement</h3>
      <p style="font-size:.82rem;color:#718096;margin:0 0 1rem">
        Please read the following agreement carefully.
        By completing your payment above, you agree to all terms below. No additional signature is required.
      </p>
      <div style="background:#f7fafc;border:1px solid #e2e8f0;border-radius:8px;padding:1.25rem">
        {contract_html}
      </div>
    </div>

    <p style="color:#2d3748;font-weight:600;margin-top:1.75rem">&mdash; The {BUSINESS_NAME} Team</p>
    {f'<p style="font-size:.85rem;color:#718096">Questions? Call us at {BUSINESS_PHONE}</p>' if BUSINESS_PHONE else ""}
  </div>
</div></body></html>"""

    plain = f"""Hi {first},

GREAT NEWS — Your rental request (Booking #{b.get('id')}) has been ACCEPTED!

EVENT DETAILS
  Date:       {_fmt_date(b.get('event_start_date'))} - {_fmt_date(b.get('event_end_date'))}
  Location:   {event_addr}
  Deliver to: {b.get('delivery_location','')}

INVOICE
{"".join(f"  {i['qty']}x {i['name']} @ ${i['unit_price']:.2f} = ${i['total']:.2f}\n" for i in items)}{"  Exact Time Delivery: $175.00\n" if exact else ""}  Delivery Fee: ${b.get('delivery_fee',0):.2f}
{disc_row_plain}{tax_row_plain}  ─────────────────────────────
  TOTAL: ${grand_total:.2f}

PAYMENT REQUIRED
  {due_label}: ${charge_amount:.2f}
  {f"Pay here: {payment_link}" if payment_link else "We will send your payment link shortly."}
  {balance_plain}

IMPORTANT: Your booking is NOT secured until payment is received.
{f"Call us at {BUSINESS_PHONE} with any questions." if BUSINESS_PHONE else ""}

By completing payment you agree to the rental terms and contract.

— {BUSINESS_NAME}"""

    _send_email(email, subject, html, plain)


def send_receipt_email(b):
    """Send a detailed receipt to the customer after payment."""
    email = b.get("email")
    if not email:
        return
    first  = (b.get("full_name") or "").split()[0] or "Valued Customer"
    bid    = b.get("id")
    paid   = float(b.get("amount_paid") or 0)
    total  = float(b.get("grand_total") or 0)
    balance = max(round(total - paid, 2), 0)

    # Build items table rows
    items = b.get("items_json") or []
    if isinstance(items, str):
        try: items = json.loads(items)
        except Exception: items = []
    item_rows = ""
    for it in items:
        name  = it.get("name", "")
        qty   = it.get("qty", 1)
        up    = float(it.get("unit_price") or 0)
        tot   = float(it.get("total") or round(up * qty, 2))
        item_rows += f"""<tr>
          <td style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0">{name}</td>
          <td style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0;text-align:center">{qty}</td>
          <td style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0;text-align:right">${up:,.2f}</td>
          <td style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0;text-align:right">${tot:,.2f}</td>
        </tr>"""

    delivery_fee  = float(b.get("delivery_fee") or 0)
    late_fee      = float(b.get("late_night_fee") or 0)
    r_disc_amount = float(b.get("discount_amount") or 0)
    r_disc_type   = b.get("discount_type") or ""
    r_disc_value  = float(b.get("discount_value") or 0)
    if delivery_fee:
        item_rows += f"""<tr><td style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0" colspan="3">Delivery Fee</td>
          <td style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0;text-align:right">${delivery_fee:,.2f}</td></tr>"""
    if late_fee:
        item_rows += f"""<tr><td style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0" colspan="3">Late Night Fee</td>
          <td style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0;text-align:right">${late_fee:,.2f}</td></tr>"""
    if r_disc_amount > 0:
        r_disc_label = f"{r_disc_value:.1f}% Discount" if r_disc_type == "percent" else f"${r_disc_value:.2f} Discount"
        item_rows += f"""<tr style="background:#f0fdf4"><td style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0;color:#166534;font-weight:600" colspan="3">🏷️ {r_disc_label}</td>
          <td style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0;text-align:right;font-weight:700;color:#16a34a">- ${r_disc_amount:,.2f}</td></tr>"""

    balance_row = ""
    if balance > 0.01:
        balance_row = f"""<tr style="background:#fff5f5"><td colspan="3" style="padding:.5rem .75rem;font-weight:600;color:#991b1b">Balance Remaining</td>
          <td style="padding:.5rem .75rem;text-align:right;font-weight:700;color:#991b1b">${balance:,.2f}</td></tr>"""

    subject = f"Receipt for Order #{bid} — {BUSINESS_NAME}"
    html = f"""
<html><body style="font-family:-apple-system,sans-serif;background:#f0f4f8;padding:2rem 1rem">
<div style="max-width:560px;margin:0 auto;background:white;border-radius:12px;overflow:hidden;box-shadow:0 4px 16px rgba(0,0,0,.08)">
  <div style="background:linear-gradient(135deg,#1a365d,#2b6cb0);padding:2rem;color:white;text-align:center">
    <h2 style="margin:0">Payment Receipt</h2>
    <p style="margin:.4rem 0 0;opacity:.85">{BUSINESS_NAME}</p>
  </div>
  <div style="padding:2rem">
    <p>Hi <strong>{first}</strong>,</p>
    <p style="color:#4a5568;line-height:1.7">Thank you so much for your business! We truly appreciate you choosing {BUSINESS_NAME} and look forward to making your event a great one.</p>
    <div style="background:#f0f4f8;border-radius:8px;padding:1rem;margin:1.25rem 0;text-align:center">
      <p style="margin:0;font-size:.8rem;font-weight:600;color:#718096;text-transform:uppercase;letter-spacing:.05em">Order Number</p>
      <p style="margin:.25rem 0 0;font-size:1.6rem;font-weight:800;color:#2b6cb0">#{bid}</p>
      <p style="margin:.25rem 0 0;font-size:.85rem;color:#718096">{_fmt_date(b.get('event_start_date'))} — {_fmt_date(b.get('event_end_date'))}</p>
    </div>
    <table style="width:100%;border-collapse:collapse;font-size:.9rem;margin:1rem 0">
      <thead>
        <tr style="background:#f0f4f8">
          <th style="padding:.5rem .75rem;text-align:left;font-weight:600;color:#4a5568">Item</th>
          <th style="padding:.5rem .75rem;text-align:center;font-weight:600;color:#4a5568">Qty</th>
          <th style="padding:.5rem .75rem;text-align:right;font-weight:600;color:#4a5568">Unit Price</th>
          <th style="padding:.5rem .75rem;text-align:right;font-weight:600;color:#4a5568">Total</th>
        </tr>
      </thead>
      <tbody>{item_rows}</tbody>
      <tfoot>
        <tr style="background:#f0fdf4">
          <td colspan="3" style="padding:.6rem .75rem;font-weight:700;color:#166534">Grand Total</td>
          <td style="padding:.6rem .75rem;text-align:right;font-weight:800;color:#166534">${total:,.2f}</td>
        </tr>
        <tr style="background:#f0fdf4">
          <td colspan="3" style="padding:.5rem .75rem;color:#166534">✅ Amount Paid</td>
          <td style="padding:.5rem .75rem;text-align:right;font-weight:700;color:#166534">${paid:,.2f}</td>
        </tr>
        {balance_row}
      </tfoot>
    </table>
    <p style="color:#4a5568;line-height:1.7;font-size:.9rem">Please keep this receipt for your records. Order #{bid} is your reference for any questions or changes.</p>
    {f'<p style="color:#4a5568;font-size:.9rem">Questions? Call <strong>{BUSINESS_PHONE}</strong> or reply to this email.</p>' if BUSINESS_PHONE else ''}
    <p style="color:#2d3748;font-weight:600;margin-top:1.5rem">With gratitude,<br>— The {BUSINESS_NAME} Team</p>
  </div>
</div></body></html>"""
    plain = (f"RECEIPT — Order #{bid}\n{BUSINESS_NAME}\n\n"
             f"Hi {first},\n\nThank you for your business! We appreciate you choosing {BUSINESS_NAME}.\n\n"
             f"Event: {_fmt_date(b.get('event_start_date'))} — {_fmt_date(b.get('event_end_date'))}\n"
             f"Grand Total: ${total:,.2f}\nAmount Paid: ${paid:,.2f}\n"
             + (f"Balance Due: ${balance:,.2f}\n" if balance > 0.01 else "Paid in Full\n") +
             f"\nOrder Reference: #{bid}\n\n— {BUSINESS_NAME}")
    _send_email(email, subject, html, plain)


def send_denied_email(b):
    """Send polite denial email to customer."""
    email = b.get("email")
    first = b.get("full_name", "").split()[0]
    if not email:
        return
    subject = f"Regarding Your Rental Request — {BUSINESS_NAME}"
    html = f"""
<html><body style="font-family:-apple-system,sans-serif;background:#f0f4f8;padding:2rem 1rem">
<div style="max-width:500px;margin:0 auto;background:white;border-radius:12px;overflow:hidden;box-shadow:0 4px 16px rgba(0,0,0,.08)">
  <div style="background:linear-gradient(135deg,#1a365d,#2b6cb0);padding:1.75rem 2rem;color:white;text-align:center">
    <h2 style="margin:0">{BUSINESS_NAME}</h2>
  </div>
  <div style="padding:2rem">
    <p>Hi <strong>{first}</strong>,</p>
    <p style="color:#4a5568;line-height:1.7;margin:.75rem 0">
      Thank you for thinking of us for your event on <strong>{_fmt_date(b.get('event_start_date'))}</strong>.
      Unfortunately, we are unable to accommodate your rental request at this time.
      This may be due to availability, date conflicts, or other circumstances.
    </p>
    <p style="color:#4a5568;line-height:1.7;margin:.75rem 0">
      We're sorry for any inconvenience and hope to have the opportunity to serve you in the future.
      Please don't hesitate to reach out if you have a different date in mind or would like to discuss other options.
    </p>
    {f'<p style="color:#4a5568;margin:.75rem 0">You can reach us at <strong>{BUSINESS_PHONE}</strong>.</p>' if BUSINESS_PHONE else ""}
    <p style="color:#2d3748;font-weight:600;margin-top:1.5rem">— The {BUSINESS_NAME} Team</p>
  </div>
</div></body></html>"""
    plain = f"Hi {first},\n\nThank you for your interest in {BUSINESS_NAME}. Unfortunately, we are unable to accommodate your rental request for {_fmt_date(b.get('event_start_date'))} at this time.\n\nWe hope to serve you in the future.{f' Please call {BUSINESS_PHONE} if you have questions.' if BUSINESS_PHONE else ''}\n\n— {BUSINESS_NAME}"
    _send_email(email, subject, html, plain)


def send_final_payment_email(b, remaining_amount, payment_link):
    """Send final payment reminder 48 hours before event with Stripe link for remaining balance."""
    email = b.get("email")
    first = b.get("full_name", "").split()[0]
    if not email:
        return

    items = json.loads(b.get("items_json") or "[]")
    exact = b.get("exact_time_delivery", False)
    grand_total    = float(b.get("grand_total") or 0)
    deposit_paid   = round(grand_total - remaining_amount, 2)
    event_addr     = f"{b.get('event_street','')}, {b.get('event_city','')}, {b.get('event_state','')} {b.get('event_zip','')}"
    event_date     = str(b.get("event_start_date", ""))
    event_time     = str(b.get("event_start_time", ""))
    setup_time     = str(b.get("setup_time", ""))

    item_rows = ""
    for it in items:
        item_rows += f"""
        <tr>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0">{it['name']}</td>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0;text-align:center">{it['qty']}</td>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0;text-align:right">${it['unit_price']:.2f}</td>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0;text-align:right;font-weight:600">${it['total']:.2f}</td>
        </tr>"""

    contract_html = build_contract_html(b, remaining_amount)

    f_tax_amount   = float(b.get("tax_amount") or 0)
    f_tax_rate     = float(b.get("tax_rate") or 0)
    f_tax_exempt   = bool(b.get("tax_exempt"))
    if f_tax_exempt:
        f_tax_row_html  = '<tr><td colspan="3" style="padding:8px 12px;border-bottom:1px solid #e2e8f0;color:#276749">CT Sales Tax <span style="font-size:.76rem;background:#c6f6d5;color:#276749;border-radius:4px;padding:.1rem .35rem;margin-left:.3rem">TAX EXEMPT</span></td><td style="padding:8px 12px;text-align:right;color:#276749;font-weight:600;border-bottom:1px solid #e2e8f0">$0.00</td></tr>'
        f_tax_row_plain = "  CT Sales Tax:       $0.00 (TAX EXEMPT)\n"
    elif f_tax_amount:
        f_tax_row_html  = f'<tr><td colspan="3" style="padding:8px 12px;border-bottom:1px solid #e2e8f0;color:#718096">CT Sales Tax ({f_tax_rate*100:.2f}%)</td><td style="padding:8px 12px;text-align:right;font-weight:600;border-bottom:1px solid #e2e8f0">${f_tax_amount:.2f}</td></tr>'
        f_tax_row_plain = f"  CT Sales Tax ({f_tax_rate*100:.2f}%): ${f_tax_amount:.2f}\n"
    else:
        f_tax_row_html  = ""
        f_tax_row_plain = ""

    pay_btn = f"""
      <a href="{payment_link}"
         style="display:inline-block;background:linear-gradient(135deg,#c05621,#dd6b20);color:white;padding:1.1rem 2.75rem;border-radius:10px;font-weight:700;font-size:1.15rem;text-decoration:none;letter-spacing:.3px;box-shadow:0 4px 12px rgba(192,86,33,.35)">
        Pay Remaining Balance ${remaining_amount:.2f}
      </a>
      <p style="margin:.6rem 0 0;font-size:.82rem;color:#718096">Secure payment powered by Stripe</p>""" if payment_link else f"""
      <p style="font-weight:700;color:#c05621">Remaining Balance Due: ${remaining_amount:.2f}</p>
      <p style="color:#744210;font-size:.9rem">Please contact us to complete your payment.{f" Call {BUSINESS_PHONE}" if BUSINESS_PHONE else ""}</p>"""

    subject = f"Final Payment Due — Your Event is in 2 Days! | {BUSINESS_NAME}"
    html = f"""
<html><body style="font-family:-apple-system,sans-serif;background:#f0f4f8;padding:2rem 1rem">
<div style="max-width:640px;margin:0 auto">

  <div style="background:linear-gradient(135deg,#c05621,#dd6b20);border-radius:12px 12px 0 0;padding:1.75rem 2rem;color:white;text-align:center">
    <div style="font-size:2rem;margin-bottom:.4rem">&#8987; Your Event is in 2 Days!</div>
    <h2 style="margin:0;font-weight:700;font-size:1.2rem">Final Payment Due — {BUSINESS_NAME}</h2>
    <p style="margin:.5rem 0 0;opacity:.88;font-size:.95rem">Booking #{b.get('id')} &bull; {event_date}</p>
  </div>

  <div style="background:white;padding:2rem;border-radius:0 0 12px 12px;box-shadow:0 4px 16px rgba(0,0,0,.08)">

    <p style="color:#2d3748;font-size:1.05rem;margin-bottom:.75rem">Hi <strong>{first}</strong>,</p>
    <p style="color:#4a5568;line-height:1.7;margin-bottom:1.25rem">
      This is your final payment reminder. Your event is <strong>2 days away</strong> and your remaining balance
      is due now to ensure everything is ready for delivery.
    </p>

    <!-- Event Summary -->
    <div style="background:#fff8f3;border:1.5px solid #fbd38d;border-radius:10px;padding:1rem 1.25rem;margin-bottom:1.5rem;font-size:.9rem;color:#2d3748">
      <div style="margin-bottom:.3rem"><strong>&#128197; Event Date:</strong> {event_date}</div>
      <div style="margin-bottom:.3rem"><strong>&#8986; Event Start Time:</strong> {event_time}</div>
      <div style="margin-bottom:.3rem"><strong>&#128337; Setup Time:</strong> {setup_time}</div>
      <div style="margin-bottom:.3rem"><strong>&#128205; Location:</strong> {event_addr}</div>
      <div><strong>&#128666; Deliver to:</strong> {b.get('delivery_location','')}</div>
    </div>

    <!-- Invoice summary -->
    <h3 style="color:#1a365d;font-size:.95rem;font-weight:700;margin:0 0 .75rem;text-transform:uppercase;letter-spacing:.5px">Your Order</h3>
    <table style="width:100%;border-collapse:collapse;font-size:.9rem;margin-bottom:1.5rem">
      <thead>
        <tr style="background:#ebf4ff">
          <th style="padding:9px 12px;text-align:left;color:#2b6cb0;font-size:.78rem;text-transform:uppercase">Item</th>
          <th style="padding:9px 12px;text-align:center;color:#2b6cb0;font-size:.78rem;text-transform:uppercase">Qty</th>
          <th style="padding:9px 12px;text-align:right;color:#2b6cb0;font-size:.78rem;text-transform:uppercase">Unit</th>
          <th style="padding:9px 12px;text-align:right;color:#2b6cb0;font-size:.78rem;text-transform:uppercase">Total</th>
        </tr>
      </thead>
      <tbody>
        {item_rows}
        {"<tr><td colspan='3' style='padding:8px 12px;border-bottom:1px solid #e2e8f0'>Exact Time Delivery</td><td style='padding:8px 12px;text-align:right;font-weight:600;border-bottom:1px solid #e2e8f0'>$175.00</td></tr>" if exact else ""}
        <tr>
          <td colspan="3" style="padding:8px 12px;border-bottom:1px solid #e2e8f0;color:#718096">Delivery Fee</td>
          <td style="padding:8px 12px;text-align:right;font-weight:600;border-bottom:1px solid #e2e8f0">${b.get('delivery_fee',0):.2f}</td>
        </tr>
        {f_tax_row_html}
        <tr style="background:#f7fafc">
          <td colspan="3" style="padding:9px 12px;border-bottom:1px solid #e2e8f0;color:#718096">Total Invoice</td>
          <td style="padding:9px 12px;text-align:right;border-bottom:1px solid #e2e8f0">${grand_total:.2f}</td>
        </tr>
        <tr style="background:#f7fafc">
          <td colspan="3" style="padding:9px 12px;border-bottom:1px solid #e2e8f0;color:#718096">Deposit Paid</td>
          <td style="padding:9px 12px;text-align:right;color:#276749;font-weight:600;border-bottom:1px solid #e2e8f0">- ${deposit_paid:.2f}</td>
        </tr>
        <tr style="background:#1a365d;color:white">
          <td colspan="3" style="padding:11px 12px;font-weight:700;font-size:1rem">REMAINING BALANCE DUE</td>
          <td style="padding:11px 12px;text-align:right;font-weight:700;font-size:1.2rem">${remaining_amount:.2f}</td>
        </tr>
      </tbody>
    </table>

    <!-- Payment section -->
    <div style="background:#fff8f3;border:2px solid #dd6b20;border-radius:12px;padding:1.5rem;margin-bottom:1.5rem;text-align:center">
      <p style="font-size:.82rem;color:#c05621;margin:0 0 .3rem;font-weight:700;text-transform:uppercase;letter-spacing:.6px">Final Payment Due Now</p>
      <p style="font-size:2.75rem;font-weight:800;color:#c05621;margin:.2rem 0 .8rem;line-height:1">${remaining_amount:.2f}</p>
      {pay_btn}
    </div>

    <!-- Urgency note -->
    <div style="background:#fff5f5;border-left:4px solid #e53e3e;padding:1rem 1.25rem;border-radius:0 8px 8px 0;margin-bottom:1.5rem;font-size:.88rem;color:#742a2a">
      <strong>Important:</strong> Failure to make final payment may result in your order being considered canceled.
      Please complete payment as soon as possible to guarantee your delivery.
    </div>

    <p style="color:#4a5568;line-height:1.7;font-size:.9rem">
      If you have any questions or need assistance, please don't hesitate to reach out.
      {f"You can call us at <strong>{BUSINESS_PHONE}</strong>." if BUSINESS_PHONE else ""}
      We look forward to making your event a success!
    </p>

    <!-- Rental Agreement -->
    <div style="border-top:2px solid #e2e8f0;padding-top:1.5rem;margin-top:1.5rem">
      <h3 style="color:#1a365d;font-size:.95rem;font-weight:700;margin:0 0 .4rem;text-transform:uppercase;letter-spacing:.5px">Rental Agreement</h3>
      <p style="font-size:.82rem;color:#718096;margin:0 0 1rem">
        As a reminder, your rental is subject to the following terms and conditions.
        By completing your final payment above, you confirm your agreement to all terms below.
        No additional signature is required.
      </p>
      <div style="background:#f7fafc;border:1px solid #e2e8f0;border-radius:8px;padding:1.25rem">
        {contract_html}
      </div>
    </div>

    <p style="color:#2d3748;font-weight:600;margin-top:1.75rem">&mdash; The {BUSINESS_NAME} Team</p>
  </div>
</div></body></html>"""

    plain = f"""Hi {first},

YOUR EVENT IS IN 2 DAYS — FINAL PAYMENT REQUIRED

Booking #{b.get('id')} | {event_date}
Location: {event_addr}
Event Time: {event_time} | Setup Time: {setup_time}

PAYMENT SUMMARY
  Total Invoice:    ${grand_total:.2f}
  Deposit Paid:   - ${deposit_paid:.2f}
{f_tax_row_plain}  ──────────────────────────
  REMAINING DUE:   ${remaining_amount:.2f}

PAY NOW: {payment_link if payment_link else 'Contact us to complete payment.'}

Failure to make final payment may result in your order being canceled.
{f"Questions? Call {BUSINESS_PHONE}" if BUSINESS_PHONE else ""}

────────────────────────────────────────────────────────
RENTAL AGREEMENT — TERMS & CONDITIONS
────────────────────────────────────────────────────────

NON-REFUNDABLE DEPOSIT AGREEMENT
Deposit is 25% and is NOT REFUNDABLE under any circumstances.
- Canceled within 20 days of event: 50% of all items charged.
- Canceled within 10 days of event: 75% of all items charged.
- Canceled within 24 hours of event: 100% charge applies.
- $75/hr fee if Rent a Party LLC is delayed due to Renter negligence.
- Remaining balance due 48 hours before event; failure to pay may result in cancellation.
- Person 18+ must be present at time of delivery.
- No refunds; inclement weather postponements receive store credit.

EQUIPMENT RENTAL TERMS
1. Equipment returned damaged (beyond normal wear) — Renter pays repair/replacement costs.
2. Late returns charged at $75/hour after specified return time.
3. Renter must have venue authorization to use equipment on premises.
4. Equipment may only be used for its intended purpose.
5. No additions, attachments, or alterations without prior written consent.
6. All equipment must be installed to allow removal without damage.
7. Chairs must be stacked with the black circle facing up; improper stacking = $1/chair fee.
8. Marquee items: keep dry, do not leave outside overnight, do not stand on them.
9. Electrical/battery items (speakers, microphones, etc.) must not be left outside overnight or exposed to moisture.
10. Water damage to any rental item = Renter responsible for full repair/replacement cost.
11. OVERNIGHT RENTALS: All equipment must be secured in a locked location overnight.
    Renter is fully responsible for all equipment until returned/picked up by Rent a Party, LLC.

By making final payment you confirm your agreement to all terms above.
No signature required — payment constitutes acceptance of this agreement.

— {BUSINESS_NAME}"""

    _send_email(email, subject, html, plain)


# ══════════════════════════════════════════════════════════════════════════════
#  ADMIN AUTHENTICATION
# ══════════════════════════════════════════════════════════════════════════════

def admin_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not session.get("admin_logged_in"):
            return redirect(url_for("admin_login"))
        return f(*args, **kwargs)
    return decorated


# ══════════════════════════════════════════════════════════════════════════════
#  HTML TEMPLATES
# ══════════════════════════════════════════════════════════════════════════════

FORM_HTML = r"""
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <link rel="manifest" href="/manifest.json">
  <meta name="theme-color" content="#2563eb">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="default">
  <meta name="apple-mobile-web-app-title" content="Rent a Party">
  <link rel="apple-touch-icon" href="/icon-192.png">
  <script>if("serviceWorker"in navigator)navigator.serviceWorker.register("/sw.js");</script>
  <title>Book a Rental — {{ business_name }}</title>
  <style>
    *,*::before,*::after{box-sizing:border-box;margin:0;padding:0}
    body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif;background:#f0f4f8;color:#1a202c;min-height:100vh}
    header{background:linear-gradient(135deg,#1a365d 0%,#2b6cb0 100%);color:white;padding:2.5rem 1.5rem;text-align:center}
    header h1{font-size:2rem;font-weight:700}
    header p{margin-top:.5rem;opacity:.85;font-size:1.05rem}
    .container{max-width:720px;margin:0 auto;padding:2rem 1rem 4rem}
    .card{background:white;border-radius:12px;box-shadow:0 2px 12px rgba(0,0,0,.08);padding:1.75rem;margin-bottom:1.5rem}
    .card h2{font-size:1rem;font-weight:700;color:#2b6cb0;border-bottom:2px solid #ebf4ff;padding-bottom:.6rem;margin-bottom:1.25rem;text-transform:uppercase;letter-spacing:.5px}
    .field{margin-bottom:1rem}
    .field label{display:block;font-size:.85rem;font-weight:600;color:#4a5568;margin-bottom:.3rem}
    .field input,.field select,.field textarea{width:100%;padding:.65rem .85rem;border:1.5px solid #cbd5e0;border-radius:8px;font-size:.97rem;color:#1a202c;background:#fff;transition:border-color .15s}
    .field input:focus,.field select:focus,.field textarea:focus{outline:none;border-color:#2b6cb0;box-shadow:0 0 0 3px rgba(43,108,176,.12)}
    .field textarea{resize:vertical;min-height:80px}
    .row{display:grid;gap:1rem;grid-template-columns:1fr 1fr}
    .row3{display:grid;gap:1rem;grid-template-columns:2fr 1fr 1fr}
    @media(max-width:560px){.row,.row3{grid-template-columns:1fr}}
    .required{color:#e53e3e}
    .section-note{font-size:.82rem;color:#718096;margin-bottom:1rem;font-style:italic}
    .type-toggle{display:flex;gap:.75rem;margin-bottom:1rem}
    .type-btn{flex:1;padding:.65rem;border:2px solid #cbd5e0;border-radius:8px;background:white;font-size:.9rem;font-weight:600;color:#718096;cursor:pointer;text-align:center;transition:all .15s}
    .type-btn.active{border-color:#2b6cb0;background:#ebf4ff;color:#2b6cb0}
    .exact-toggle{display:flex;align-items:center;gap:.75rem;padding:1rem;background:#fffaf0;border:2px solid #ed8936;border-radius:10px;cursor:pointer;margin-bottom:.75rem}
    .exact-toggle input[type=checkbox]{width:20px;height:20px;cursor:pointer;accent-color:#2b6cb0}
    .exact-label{flex:1}
    .exact-label strong{display:block;font-size:.97rem;color:#1a202c}
    .exact-label span{font-size:.82rem;color:#718096}
    .exact-badge{background:#ed8936;color:white;padding:.2rem .6rem;border-radius:20px;font-size:.8rem;font-weight:700}
    .product-row{display:grid;grid-template-columns:1fr auto auto;align-items:center;gap:.75rem;padding:.85rem 0;border-bottom:1px solid #f0f4f8}
    .product-row:last-child{border-bottom:none}
    .product-name{font-weight:600;font-size:.95rem}
    .product-meta{display:flex;gap:1rem;font-size:.8rem;margin-top:.15rem}
    .product-price{color:#718096}
    .avail-badge{font-weight:600}
    .avail-badge.ok{color:#38a169}
    .avail-badge.low{color:#d69e2e}
    .avail-badge.out{color:#e53e3e}
    .qty-control{display:flex;align-items:center;border:1.5px solid #cbd5e0;border-radius:8px;overflow:hidden}
    .qty-btn{background:#f7fafc;border:none;width:34px;height:36px;font-size:1.1rem;color:#2b6cb0;cursor:pointer;transition:background .12s}
    .qty-btn:hover{background:#ebf4ff}
    .qty-input{width:52px;border:none;border-left:1.5px solid #cbd5e0;border-right:1.5px solid #cbd5e0;text-align:center;font-size:.95rem;font-weight:600;padding:.4rem .2rem;outline:none}
    .product-sub{text-align:right;min-width:70px;font-weight:600;color:#718096;font-size:.95rem}
    .product-sub.has-val{color:#2b6cb0}
    .total-bar{background:linear-gradient(135deg,#1a365d,#2b6cb0);border-radius:12px;padding:1.25rem 1.75rem;color:white;margin-bottom:1.5rem}
    .total-row{display:flex;justify-content:space-between;padding:.2rem 0;font-size:.95rem;opacity:.85}
    .total-row.grand{font-size:1.35rem;font-weight:700;opacity:1;border-top:1px solid rgba(255,255,255,.25);margin-top:.5rem;padding-top:.6rem}
    .total-note{font-size:.78rem;opacity:.7;margin-top:.5rem;font-style:italic}
    .alert{background:#fff5f5;border:1px solid #feb2b2;color:#c53030;padding:.85rem 1rem;border-radius:8px;margin-bottom:1rem;font-size:.9rem}
    .submit-btn{width:100%;padding:1rem;background:linear-gradient(135deg,#1a365d,#2b6cb0);color:white;border:none;border-radius:10px;font-size:1.1rem;font-weight:700;cursor:pointer;transition:opacity .15s}
    .submit-btn:hover{opacity:.92}
    .submit-btn:disabled{opacity:.6;cursor:not-allowed}
  </style>
</head>
<body>
<header>
  <h1>{{ business_name }}</h1>
  <p>Request a rental quote — we'll respond quickly!</p>
</header>
<div class="container">
{% if error %}<div class="alert">{{ error }}</div>{% endif %}
<form method="POST" action="/submit" id="bookingForm">
  <div class="card">
    <h2>Your Information</h2>
    <div class="row">
      <div class="field"><label>Full Name <span class="required">*</span></label><input name="full_name" required placeholder="Jane Smith" value="{{ form.full_name or '' }}"></div>
      <div class="field"><label>Company Name <span style="color:#718096;font-weight:400">(if applicable)</span></label><input name="company_name" placeholder="ABC Events LLC" value="{{ form.company_name or '' }}"></div>
    </div>
    <div class="field"><label>Street Address <span class="required">*</span></label><input name="renter_street" required placeholder="123 Main Street" value="{{ form.renter_street or '' }}"></div>
    <div class="row3">
      <div class="field"><label>City <span class="required">*</span></label><input name="renter_city" required placeholder="Hartford" value="{{ form.renter_city or '' }}"></div>
      <div class="field"><label>State <span class="required">*</span></label><input name="renter_state" required placeholder="CT" maxlength="2" value="{{ form.renter_state or '' }}"></div>
      <div class="field"><label>Zip <span class="required">*</span></label><input name="renter_zip" required placeholder="06101" value="{{ form.renter_zip or '' }}"></div>
    </div>
    <div class="row">
      <div class="field"><label>Phone <span class="required">*</span></label><input name="phone" type="tel" required placeholder="(555) 000-0000" value="{{ form.phone or '' }}"></div>
      <div class="field"><label>Email <span class="required">*</span></label><input name="email" type="email" required placeholder="jane@email.com" value="{{ form.email or '' }}"></div>
    </div>
    <div style="margin-top:1rem;padding:.75rem 1rem;background:#f0fdf4;border:1.5px solid #86efac;border-radius:8px;display:flex;align-items:flex-start;gap:.75rem">
      <input type="checkbox" name="tax_exempt_request" id="tax_exempt_request" value="1" onchange="updateTotals()" style="width:18px;height:18px;margin-top:.15rem;accent-color:#16a34a;cursor:pointer;flex-shrink:0">
      <label for="tax_exempt_request" style="cursor:pointer;font-size:.9rem;color:#166534;font-weight:600;line-height:1.4">
        I have a Connecticut Tax-Exempt Certificate
        <span style="display:block;font-weight:400;font-size:.8rem;color:#4b7c5a;margin-top:.1rem">Check this if your organization is tax-exempt. You will need to provide your certificate number to the rental office.</span>
      </label>
    </div>
  </div>

  <div class="card">
    <h2>Event Details</h2>
    <div class="row">
      <div class="field"><label>Event Start Date <span class="required">*</span></label><input id="event_start_date" name="event_start_date" type="date" required onchange="onDateChange()" value="{{ form.event_start_date or '' }}"></div>
      <div class="field"><label>Event End Date <span class="required">*</span></label><input id="event_end_date" name="event_end_date" type="date" required onchange="onDateChange()" value="{{ form.event_end_date or '' }}"></div>
    </div>
    <div class="row">
      <div class="field"><label>Event Start Time <span class="required">*</span></label><input name="event_start_time" type="time" required value="{{ form.event_start_time or '' }}"></div>
      <div class="field"><label>Pickup / End Time <span class="required">*</span></label><input name="event_end_time" type="time" required value="{{ form.event_end_time or '' }}"></div>
    </div>
    <div class="row"><div class="field"><label>Setup / Delivery Time <span class="required">*</span></label><input name="setup_time" type="time" required value="{{ form.setup_time or '' }}"></div></div>
    <div class="field">
      <label>Venue Type <span class="required">*</span></label>
      <div class="type-toggle">
        <div class="type-btn active" id="btn_venue" onclick="setVenue('venue')">Venue</div>
        <div class="type-btn" id="btn_residential" onclick="setVenue('residential')">Residential</div>
      </div>
      <input type="hidden" name="venue_type" id="venue_type_input" value="venue">
    </div>
    <div id="venue_pickup_row" class="field"><label>Latest Pickup Time at Venue <span class="required">*</span></label><input id="venue_latest_pickup" name="venue_latest_pickup" type="time" value="{{ form.venue_latest_pickup or '' }}"></div>
  </div>

  <div class="card">
    <h2>Event Address</h2>
    <p class="section-note">Where will we deliver your rental items?</p>
    <div class="field"><label>Street Address <span class="required">*</span></label><input id="event_street" name="event_street" required placeholder="456 Venue Blvd" value="{{ form.event_street or '' }}" oninput="scheduleDistanceCalc()"></div>
    <div class="row3">
      <div class="field"><label>City <span class="required">*</span></label><input id="event_city" name="event_city" required placeholder="Hartford" value="{{ form.event_city or '' }}" oninput="scheduleDistanceCalc()"></div>
      <div class="field"><label>State <span class="required">*</span></label><input id="event_state" name="event_state" required placeholder="CT" maxlength="2" value="{{ form.event_state or '' }}" oninput="scheduleDistanceCalc()"></div>
      <div class="field"><label>Zip <span class="required">*</span></label><input id="event_zip" name="event_zip" required placeholder="06101" value="{{ form.event_zip or '' }}" oninput="scheduleDistanceCalc()"></div>
    </div>
  </div>

  <div class="card">
    <h2>Delivery Options</h2>
    <label class="exact-toggle">
      <input type="checkbox" id="exact_time_cb" name="exact_time_delivery" value="yes" onchange="updateTotals()">
      <div class="exact-label"><strong>Exact Time Delivery</strong><span>Guaranteed delivery at your specified setup time</span></div>
      <span class="exact-badge">+$175</span>
    </label>
    <div class="field"><label>Where on the premises will items be delivered? <span class="required">*</span></label><textarea name="delivery_location" required placeholder="e.g. Through the main entrance, set up in the ballroom on the left side...">{{ form.delivery_location or '' }}</textarea></div>
  </div>

  <!-- Hidden qty inputs — submitted with form -->
  {% for p in products %}
  <input type="hidden" class="qty-input" id="qty_{{ p.id }}" name="qty_{{ p.id }}" value="0" data-price="{{ p.price }}" data-max="{{ p.total }}">
  {% endfor %}

  <!-- Product data for JS -->
  <script>
  const ALL_PRODUCTS = [
    {% for p in products %}
    { id:"{{ p.id }}", name:{{ p.name | tojson }}, price:{{ p.price }}, max:{{ p.total }} },
    {% endfor %}
  ];
  </script>

  <div class="card">
    <h2>Select Your Items</h2>
    <p style="color:#6b7280;font-size:.88rem;margin-bottom:1.25rem">Click a category below to browse items. Select an item to add it to your order.</p>

    <!-- Category accordion dropdowns -->
    <div id="category-dropdowns"></div>

    <!-- Selected items list -->
    <div id="selected-items-wrap" style="display:none;margin-top:1.25rem;border-top:2px solid #e5e7eb;padding-top:1rem">
      <div style="font-weight:700;font-size:.95rem;color:#1a202c;margin-bottom:.75rem">🛒 Your Items</div>
      <div id="marquee-tier-notice" style="display:none;background:#eff6ff;border:1px solid #bfdbfe;border-radius:8px;padding:.6rem .9rem;margin-bottom:.75rem;font-size:.88rem;color:#1e40af"></div>
      <div id="selected-items-list"></div>
    </div>
  </div>

  <!-- Stackable Marquee Option — shown only when marquee items are in cart -->
  <div id="stackable-section" style="display:none;margin:.75rem 0;padding:1.1rem 1.25rem;background:#faf5ff;border:1.5px solid #d8b4fe;border-radius:10px">
    <div style="font-weight:700;font-size:.95rem;color:#6b21a8;margin-bottom:.5rem">🔡 Stackable Marquee</div>
    <p style="font-size:.88rem;color:#4c1d95;margin-bottom:.85rem;line-height:1.6">
      Would you like your marquee letters/numbers to be <strong>stackable</strong> (stacked on top of each other)?
      <span style="background:#ede9fe;color:#7c3aed;border-radius:4px;padding:.1rem .45rem;font-size:.8rem;font-weight:700;margin-left:.3rem">+$75 fee</span>
    </p>
    <div style="display:flex;gap:1rem;margin-bottom:.85rem">
      <label style="display:flex;align-items:center;gap:.4rem;cursor:pointer;font-weight:600;color:#1a202c">
        <input type="radio" name="stackable_choice" value="yes" onchange="onStackableChange()"
          style="accent-color:#7c3aed;width:16px;height:16px"> Yes, I want stackable (+$75)
      </label>
      <label style="display:flex;align-items:center;gap:.4rem;cursor:pointer;font-weight:600;color:#1a202c">
        <input type="radio" name="stackable_choice" value="no" onchange="onStackableChange()" checked
          style="accent-color:#7c3aed;width:16px;height:16px"> No thanks
      </label>
    </div>
    <div id="stackable-top-wrap" style="display:none">
      <label style="font-size:.88rem;font-weight:600;color:#1a202c;display:block;margin-bottom:.35rem">
        Which letters or numbers go on top? <span style="color:#dc2626">*</span>
      </label>
      <input type="text" id="stackable_top_display" placeholder="e.g. A, E, O — or 2, 5"
        oninput="document.getElementById('stackable_top_input').value=this.value"
        style="width:100%;border:1.5px solid #c4b5fd;border-radius:8px;padding:.5rem .75rem;font-size:.9rem;box-sizing:border-box">
    </div>
  </div>
  <input type="hidden" name="stackable" id="stackable_input" value="no">
  <input type="hidden" name="stackable_top" id="stackable_top_input" value="">

  <input type="hidden" name="late_night_fee" id="late_night_fee_input" value="0">
  <div id="late_night_notice" style="display:none;margin:.75rem 0;padding:.75rem 1rem;background:#fef3c7;border:1.5px solid #fcd34d;border-radius:8px;font-size:.88rem;color:#92400e">
    <strong>⏰ Late Night / Early Morning Fee: $125.00</strong><br>
    Your pickup or dropoff time falls between 11:30 PM – 7:00 AM. A $125 fee applies for pickups or deliveries outside of standard hours.
  </div>
  <div class="total-bar">
    <div class="total-row"><span>Items Subtotal</span><span id="t_items">$0.00</span></div>
    <div class="total-row"><span>Exact Time Delivery</span><span id="t_exact">-</span></div>
    <div class="total-row" id="t_stackable_row" style="display:none"><span>Stackable Marquee</span><span id="t_stackable">$75.00</span></div>
    <div class="total-row" id="t_latenight_row" style="display:none"><span>Late Night / Early Morning Fee</span><span id="t_latenight">$125.00</span></div>
    <div class="total-row"><span>Delivery Fee</span><span id="t_delivery">Calculated after review</span></div>
    <div class="total-row"><span>CT Sales Tax (6.35%)</span><span id="t_tax">$0.00</span></div>
    <div class="total-row grand"><span>Estimated Total</span><span id="t_grand">$0.00</span></div>
    <p class="total-note">Final delivery fee and tax confirmed after we review your address. This is a quote request, not a charge.</p>
  </div>

  <div style="background:#fffbeb;border:1px solid #fcd34d;border-radius:10px;padding:1rem 1.25rem;margin-bottom:1.25rem">
    <p style="margin:0;font-size:.9rem;color:#78350f;line-height:1.7">
      <strong>📋 Please note:</strong> This is a quote request, not a charge. The initial quote may not reflect the exact final price — pricing may vary based on your event details.
      Any differences will be clearly explained in the invoice we send you before any payment is required.
    </p>
  </div>

  <button type="submit" class="submit-btn" id="submitBtn">Send Quote Request</button>
</form>
</div>
<script>
const EXACT_FEE = {{ exact_time_fee }};
const LATE_NIGHT_FEE = 125;
const CT_TAX_RATE = 0.0635;
function isLateNight(timeStr){
  if(!timeStr) return false;
  const [h,m]=timeStr.split(':').map(Number);
  const mins=h*60+m;
  return mins>=1410||mins<420;
}
function checkLateNightFee(){
  const endTime=document.querySelector('[name="event_end_time"]').value;
  const late=isLateNight(endTime);
  document.getElementById('late_night_notice').style.display=late?'block':'none';
  document.getElementById('t_latenight_row').style.display=late?'flex':'none';
  document.getElementById('late_night_fee_input').value=late?LATE_NIGHT_FEE:0;
  return late?LATE_NIGHT_FEE:0;
}

// ── Marquee Tier Pricing ──────────────────────────────────────────
const MARQUEE_NUMBER_TIERS = [
  { count:1, total:80 },
  { count:2, total:150 },
  { count:3, total:215 },
  { count:4, total:275 },
];
function getMarqueeNumberTotal(n){
  if(n<=0) return 0;
  const t=MARQUEE_NUMBER_TIERS.find(x=>x.count===n);
  if(t) return t.total;
  return 275+(n-4)*55;
}
const MARQUEE_LETTER_TIERS = [
  { count:1, total:85 },
  { count:2, total:160 },
  { count:3, total:225 },
  { count:4, total:285 },
];
function getMarqueeLetterTotal(n){
  if(n<=0) return 0;
  const t=MARQUEE_LETTER_TIERS.find(x=>x.count===n);
  if(t) return t.total;
  return 285+(n-4)*55;
}
function isMarqueeNumber(name){ return /^marquee\s+#?\d/i.test(name); }
function isMarqueeLetter(name){ return /^marquee\s+[a-z]$/i.test(name); }

// ── Item Categories ───────────────────────────────────────────────
const ITEM_CATEGORIES = [
  { label:"🪑 Chairs",           keywords:["chair","stool","bench","seat","chiavari"] },
  { label:"🪣 Tables",           keywords:["table","tablecloth","linen","cloth","runner","overlay","skirt"] },
  { label:"🔢 Marquee Numbers",  keywords:["marquee number"] },
  { label:"🔤 Marquee Letters",  keywords:["marquee letter"] },
  { label:"💡 Lighting",         keywords:["light","lamp","led","glow","neon","bulb","lantern","fairy","chandelier","uplighting"] },
  { label:"🎭 Backdrops & Décor",keywords:["backdrop","banner","balloon","arch","flower","floral","decor","sign","drape","curtain","pillar","column","centerpiece","vase","frame","wall"] },
  { label:"🎪 Entertainment",    keywords:["bounce","slide","game","popcorn","cotton candy","machine","photo booth","casino","carnival","inflatable"] },
  { label:"⛺ Tents & Canopies", keywords:["tent","canopy","pergola","gazebo","umbrella"] },
];
function getCat(name){
  const n=name.trim();
  // Marquee Letter: "Marquee A", "Marquee B", etc. — marquee followed by a single letter
  if(/^marquee\s+[a-zA-Z]$/i.test(n) || /marquee\s+[a-zA-Z]\s*$/i.test(n)) return "🔤 Marquee Letters";
  // Marquee Number: "Marquee #5", "Marquee 3", etc. — marquee followed by # or digit
  if(/marquee\s+#?\d/i.test(n)) return "🔢 Marquee Numbers";
  const nl=n.toLowerCase();
  for(const c of ITEM_CATEGORIES){ if(c.keywords.some(k=>nl.includes(k))) return c.label; }
  return "📦 Other";
}

// ── Build Category Accordion Dropdowns ───────────────────────────
function buildDropdowns(){
  // Group products by category
  const groups={};
  ALL_PRODUCTS.forEach(p=>{
    const cat=getCat(p.name);
    if(!groups[cat]) groups[cat]=[];
    groups[cat].push(p);
  });
  const wrap=document.getElementById('category-dropdowns');
  wrap.innerHTML='';
  const CAT_ORDER=['🪑 Chairs','🪣 Tables','🔤 Marquee Letters','🔢 Marquee Numbers'];
  const sorted=Object.entries(groups).sort(([a],[b])=>{
    if(a==='📦 Other') return 1;
    if(b==='📦 Other') return -1;
    const ai=CAT_ORDER.indexOf(a), bi=CAT_ORDER.indexOf(b);
    if(ai>=0&&bi>=0) return ai-bi;
    if(ai>=0) return -1;
    if(bi>=0) return 1;
    return a.localeCompare(b);
  });
  sorted.forEach(([cat,items])=>{
    const sec=document.createElement('div');
    sec.style.cssText='border:1px solid #e5e7eb;border-radius:8px;margin-bottom:.5rem;overflow:hidden';
    sec.innerHTML=`
      <button type="button" onclick="toggleCat(this)"
        style="width:100%;text-align:left;background:#f9fafb;border:none;padding:.75rem 1rem;font-size:.95rem;font-weight:700;color:#1a202c;cursor:pointer;display:flex;justify-content:space-between;align-items:center">
        <span>${cat} <span style="font-size:.8rem;font-weight:400;color:#9ca3af">(${items.length} item${items.length!==1?'s':''})</span></span>
        <span class="chev" style="transition:transform .2s;font-size:.8rem">▼</span>
      </button>
      <div class="cat-body" style="display:none;padding:.75rem 1rem;background:white">
        ${cat==='🔢 Marquee Numbers'?`<div style="background:#fefce8;border:1px solid #fde047;border-radius:8px;padding:.6rem .9rem;margin-bottom:.75rem;font-size:.83rem;color:#713f12">
          <strong>📋 Tier Pricing:</strong> 1 for $80 &nbsp;·&nbsp; 2 for $150 &nbsp;·&nbsp; 3 for $215 &nbsp;·&nbsp; 4 for $275 &nbsp;·&nbsp; 5+ = $275 + $55 each additional
        </div>`:''}
        ${cat==='🔤 Marquee Letters'?`<div style="background:#fefce8;border:1px solid #fde047;border-radius:8px;padding:.6rem .9rem;margin-bottom:.75rem;font-size:.83rem;color:#713f12">
          <strong>📋 Tier Pricing:</strong> 1 for $85 &nbsp;·&nbsp; 2 for $160 &nbsp;·&nbsp; 3 for $225 &nbsp;·&nbsp; 4 for $285 &nbsp;·&nbsp; 5+ = $285 + $55 each additional
        </div>`:''}
        <div style="display:flex;flex-wrap:wrap;gap:.5rem">
          ${items.map(p=>`
            <button type="button" onclick="addToCart('${p.id}')"
              data-id="${p.id}"
              style="background:#eff6ff;color:#1d4ed8;border:1.5px solid #bfdbfe;border-radius:20px;padding:.35rem .9rem;font-size:.85rem;font-weight:600;cursor:pointer;transition:background .15s"
              onmouseover="this.style.background='#dbeafe'" onmouseout="this.style.background='#eff6ff'">
              ${p.name} — $${p.price.toFixed(2)}
            </button>`).join('')}
        </div>
      </div>`;
    wrap.appendChild(sec);
  });
}
function toggleCat(btn){
  const body=btn.nextElementSibling;
  const open=body.style.display==='block';
  body.style.display=open?'none':'block';
  btn.querySelector('.chev').style.transform=open?'':'rotate(180deg)';
  btn.style.background=open?'#f9fafb':'#eff6ff';
}

// ── Cart ──────────────────────────────────────────────────────────
const cart={};  // id -> qty
function addToCart(id){
  const p=ALL_PRODUCTS.find(x=>x.id===id);
  if(!p) return;
  if(cart[id]){ setQty(id, cart[id]+1); }
  else { cart[id]=1; renderCart(); }
  setHiddenQty(id, cart[id]);
  updateTotals();
  // Highlight the button
  const btn=document.querySelector(`button[data-id="${id}"]`);
  if(btn){ btn.style.background='#bbf7d0'; btn.style.borderColor='#4ade80'; btn.style.color='#166534';
    setTimeout(()=>{ btn.style.background='#eff6ff'; btn.style.borderColor='#bfdbfe'; btn.style.color='#1d4ed8'; },600); }
}
function setQty(id, val){
  const p=ALL_PRODUCTS.find(x=>x.id===id);
  if(!p) return;
  const v=Math.max(0, val);
  if(v===0){ delete cart[id]; }
  else { cart[id]=v; }
  const inp=document.getElementById('cart-qty-'+id);
  if(inp) inp.value=v===0?'':v;
  setHiddenQty(id, v);
  renderCart();
  updateTotals();
}
function setHiddenQty(id, val){
  const h=document.getElementById('qty_'+id);
  if(h) h.value=val;
}
function removeFromCart(id){
  delete cart[id];
  setHiddenQty(id,0);
  renderCart();
  updateTotals();
}
const STACKABLE_FEE = 75;
function hasMarqueeInCart(){
  return Object.keys(cart).some(id=>{
    const p=ALL_PRODUCTS.find(x=>x.id===id);
    return p && (isMarqueeLetter(p.name)||isMarqueeNumber(p.name));
  });
}
function onStackableChange(){
  const sel=document.querySelector('input[name="stackable_choice"]:checked');
  const yes=sel&&sel.value==='yes';
  document.getElementById('stackable_input').value=yes?'yes':'no';
  document.getElementById('stackable-top-wrap').style.display=yes?'block':'none';
  if(!yes){ document.getElementById('stackable_top_input').value=''; const d=document.getElementById('stackable_top_display'); if(d) d.value=''; }
  updateTotals();
}
function renderCart(){
  const list=document.getElementById('selected-items-list');
  const wrap=document.getElementById('selected-items-wrap');
  const ids=Object.keys(cart);
  if(ids.length===0){
    wrap.style.display='none'; list.innerHTML='';
    // Hide stackable section and reset when cart is empty
    const ss=document.getElementById('stackable-section');
    if(ss) ss.style.display='none';
    document.getElementById('stackable_input').value='no';
    const noRadio=document.querySelector('input[name="stackable_choice"][value="no"]');
    if(noRadio){ noRadio.checked=true; }
    document.getElementById('stackable-top-wrap').style.display='none';
    return;
  }
  wrap.style.display='block';
  // Show stackable section only when marquee items are in cart
  const ss=document.getElementById('stackable-section');
  if(ss) ss.style.display=hasMarqueeInCart()?'block':'none';
  if(!hasMarqueeInCart()){
    document.getElementById('stackable_input').value='no';
    const noRadio=document.querySelector('input[name="stackable_choice"][value="no"]');
    if(noRadio){ noRadio.checked=true; }
    document.getElementById('stackable-top-wrap').style.display='none';
  }
  // Calculate total marquee numbers for proration
  let mnCount=0, mlCount=0;
  ids.forEach(id=>{ const p=ALL_PRODUCTS.find(x=>x.id===id); if(!p) return;
    if(isMarqueeNumber(p.name)) mnCount+=cart[id]||0;
    else if(isMarqueeLetter(p.name)) mlCount+=cart[id]||0;
  });
  const mnTierTotal=getMarqueeNumberTotal(mnCount);
  const mlTierTotal=getMarqueeLetterTotal(mlCount);
  const mnUnitPrice=mnCount>0?(mnTierTotal/mnCount):0;
  const mlUnitPrice=mlCount>0?(mlTierTotal/mlCount):0;
  list.innerHTML=ids.map(id=>{
    const p=ALL_PRODUCTS.find(x=>x.id===id);
    const q=cart[id]||1;
    const isMN=isMarqueeNumber(p.name);
    const isML=isMarqueeLetter(p.name);
    const unitPrice=isMN?mnUnitPrice:isML?mlUnitPrice:p.price;
    const lineTotal=(unitPrice*q).toFixed(2);
    const tierTag=(isMN||isML)?` <span style="font-size:.75rem;color:#2563eb;font-weight:600">(tier)</span>`:'';
    const unitLabel=`$${unitPrice.toFixed(2)} ea${tierTag}`;
    return `<div style="display:flex;align-items:center;gap:.75rem;padding:.6rem .5rem;border-bottom:1px solid #f3f4f6">
      <span style="flex:1;font-size:.92rem;font-weight:600;color:#1a202c">${p.name}</span>
      <span style="font-size:.82rem;color:#6b7280;white-space:nowrap">${unitLabel}</span>
      <div style="display:flex;align-items:center;gap:.3rem">
        <button type="button" onclick="setQty('${id}',${q-1})"
          style="width:28px;height:28px;border:1px solid #d1d5db;border-radius:6px;background:white;font-size:1rem;cursor:pointer;line-height:1">−</button>
        <input id="cart-qty-${id}" type="number" value="${q}" min="1" max="9999"
          onchange="setQty('${id}',parseInt(this.value)||1)"
          style="width:44px;text-align:center;border:1px solid #d1d5db;border-radius:6px;padding:.2rem;font-size:.9rem;font-weight:700">
        <button type="button" onclick="setQty('${id}',${q+1})"
          style="width:28px;height:28px;border:1px solid #d1d5db;border-radius:6px;background:white;font-size:1rem;cursor:pointer;line-height:1">+</button>
      </div>
      <span style="font-size:.9rem;font-weight:700;color:#2563eb;min-width:52px;text-align:right">$${lineTotal}</span>
      <button type="button" onclick="removeFromCart('${id}')"
        style="background:none;border:none;color:#9ca3af;font-size:1.1rem;cursor:pointer;padding:.1rem .3rem" title="Remove">✕</button>
    </div>`;
  }).join('');
}
function updateTotals(){
  let regularSub=0, mnCount=0, mlCount=0;
  ALL_PRODUCTS.forEach(p=>{
    const qty=cart[p.id]||0;
    if(!qty) return;
    if(isMarqueeNumber(p.name)) mnCount+=qty;
    else if(isMarqueeLetter(p.name)) mlCount+=qty;
    else regularSub+=qty*p.price;
  });
  const mnSub=getMarqueeNumberTotal(mnCount);
  const mlSub=getMarqueeLetterTotal(mlCount);
  const sub=regularSub+mnSub+mlSub;
  // Update tier notices in cart
  const tierEl=document.getElementById('marquee-tier-notice');
  if(tierEl){
    let html='';
    if(mnCount>0){
      const nextN=MARQUEE_NUMBER_TIERS.find(t=>t.count===mnCount+1);
      const savN=nextN?` <span style="color:#16a34a;font-size:.82rem">· Add 1 more for $${nextN.total} total</span>`:'';
      html+=`🔢 <strong>${mnCount} Marquee Number${mnCount!==1?'s':''}</strong> — Tier Price: <strong>$${mnSub.toFixed(2)}</strong>${savN}<br>`;
    }
    if(mlCount>0){
      const nextL=MARQUEE_LETTER_TIERS.find(t=>t.count===mlCount+1);
      const savL=nextL?` <span style="color:#16a34a;font-size:.82rem">· Add 1 more for $${nextL.total} total</span>`:'';
      html+=`🔤 <strong>${mlCount} Marquee Letter${mlCount!==1?'s':''}</strong> — Tier Price: <strong>$${mlSub.toFixed(2)}</strong>${savL}`;
    }
    tierEl.innerHTML=html;
    tierEl.style.display=(mnCount>0||mlCount>0)?'block':'none';
  }
  const exactCb=document.getElementById('exact_time_cb');
  const ef=exactCb&&exactCb.checked?EXACT_FEE:0;
  const lf=checkLateNightFee();
  const stackableSel=document.querySelector('input[name="stackable_choice"]:checked');
  const sf=(stackableSel&&stackableSel.value==='yes'&&hasMarqueeInCart())?STACKABLE_FEE:0;
  const stackRow=document.getElementById('t_stackable_row');
  if(stackRow) stackRow.style.display=sf>0?'flex':'none';
  const exemptCb=document.getElementById('tax_exempt_request');
  const exempt=exemptCb&&exemptCb.checked;
  const tax=exempt?0:(sub+ef+sf+lf)*CT_TAX_RATE;
  const taxEl=document.getElementById('t_tax');
  if(taxEl){ taxEl.textContent='$'+tax.toFixed(2); taxEl.style.color=exempt?'#16a34a':'';
    const lbl=taxEl.previousElementSibling; if(lbl) lbl.textContent=exempt?'CT Sales Tax (EXEMPT)':'CT Sales Tax (6.35%)'; }
  document.getElementById('t_items').textContent='$'+sub.toFixed(2);
  document.getElementById('t_exact').textContent=ef>0?'$'+ef.toFixed(2):'-';
  document.getElementById('t_grand').textContent='$'+(sub+ef+sf+lf+tax).toFixed(2)+'+';
}
document.addEventListener('DOMContentLoaded', buildDropdowns);
function setVenue(type){document.getElementById('venue_type_input').value=type;document.getElementById('btn_venue').classList.toggle('active',type==='venue');document.getElementById('btn_residential').classList.toggle('active',type==='residential');const row=document.getElementById('venue_pickup_row');const inp=document.getElementById('venue_latest_pickup');row.style.display=type==='venue'?'block':'none';inp.required=type==='venue';}
setVenue('venue');
function onDateChange(){const start=document.getElementById('event_start_date').value;const end=document.getElementById('event_end_date').value;if(!start||!end||end<start)return;fetch('/availability?start='+start+'&end='+end).then(r=>r.json()).then(data=>{ALL_PRODUCTS.forEach(p=>{if(data[p.id]!==undefined){p.max=data[p.id];}});updateTotals();}).catch(()=>{});}
let distTimer;
function scheduleDistanceCalc(){clearTimeout(distTimer);distTimer=setTimeout(()=>{const street=document.getElementById('event_street').value;const city=document.getElementById('event_city').value;const state=document.getElementById('event_state').value;const zip=document.getElementById('event_zip').value;if(street&&city&&state&&zip){const addr=street+', '+city+', '+state+' '+zip;fetch('/delivery_fee?address='+encodeURIComponent(addr)).then(r=>r.json()).then(d=>{document.getElementById('t_delivery').textContent='$'+d.fee.toFixed(2)+' ('+d.note+')';}).catch(()=>{});}},800);}
// ── Date validation ───────────────────────────────────────────────────────
const today=new Date().toISOString().split('T')[0];
const startDateEl = document.getElementById('event_start_date');
const endDateEl   = document.getElementById('event_end_date');
const startTimeEl = document.querySelector('[name="event_start_time"]');
const endTimeEl   = document.querySelector('[name="event_end_time"]');
const setupTimeEl = document.querySelector('[name="setup_time"]');

startDateEl.min = today;
endDateEl.min   = today;

// When start date changes, end date must be >= start date
startDateEl.addEventListener('change', function() {
  endDateEl.min = this.value;
  if (endDateEl.value && endDateEl.value < this.value) {
    endDateEl.value = this.value;
  }
  onDateChange();
});

endDateEl.addEventListener('change', function() {
  if (this.value < startDateEl.value) {
    this.value = startDateEl.value;
    showTimeError('End date cannot be before start date.');
  }
  onDateChange();
});

// When start time changes, end time must be after it; setup time must be before it
startTimeEl.addEventListener('change', function() {
  if (endTimeEl.value && endTimeEl.value <= this.value) {
    endTimeEl.value = '';
    showTimeError('Event end time must be after start time.');
  }
  if (setupTimeEl.value && setupTimeEl.value >= this.value) {
    setupTimeEl.value = '';
    showTimeError('Setup time must be before event start time.');
  }
});

endTimeEl.addEventListener('change', function() {
  if (startTimeEl.value && this.value <= startTimeEl.value) {
    this.value = '';
    showTimeError('Event end time must be after the start time.');
  }
  updateTotals();
});

setupTimeEl.addEventListener('change', function() {
  if (startTimeEl.value && this.value >= startTimeEl.value) {
    this.value = '';
    showTimeError('Setup time must be before the event start time.');
  }
});

function showTimeError(msg) {
  let el = document.getElementById('time_error');
  if (!el) {
    el = document.createElement('div');
    el.id = 'time_error';
    el.style.cssText = 'background:#fff5f5;border:1px solid #feb2b2;color:#c53030;padding:.75rem 1rem;border-radius:8px;margin-bottom:1rem;font-size:.9rem';
    document.getElementById('submitBtn').before(el);
  }
  el.textContent = msg;
  setTimeout(() => { if (el) el.textContent = ''; }, 4000);
}

// ── Form submit validation ────────────────────────────────────────────────
document.getElementById('bookingForm').addEventListener('submit', function(e) {
  const errors = [];
  const sd = startDateEl.value, ed = endDateEl.value;
  const st = startTimeEl.value, et = endTimeEl.value, sut = setupTimeEl.value;

  if (sd && ed && ed < sd)   errors.push('End date cannot be before start date.');
  if (st && et && et <= st)  errors.push('Event end time must be after the start time.');
  if (sut && st && sut >= st) errors.push('Setup time must be before the event start time.');

  if (errors.length) {
    e.preventDefault();
    showTimeError(errors.join(' '));
    return;
  }
  const btn = document.getElementById('submitBtn');
  btn.disabled = true;
  btn.textContent = 'Submitting...';
});
</script>
</body></html>
"""


SUCCESS_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <link rel="manifest" href="/manifest.json">
  <meta name="theme-color" content="#2563eb">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="default">
  <meta name="apple-mobile-web-app-title" content="Rent a Party">
  <link rel="apple-touch-icon" href="/icon-192.png">
  <script>if("serviceWorker"in navigator)navigator.serviceWorker.register("/sw.js");</script>
  <title>Request Received — {{ business_name }}</title>
  <style>
    body{font-family:-apple-system,sans-serif;background:#f0f4f8;display:flex;align-items:center;justify-content:center;min-height:100vh;margin:0}
    .box{background:white;border-radius:16px;padding:3rem 2.5rem;text-align:center;max-width:480px;width:90%;box-shadow:0 4px 24px rgba(0,0,0,.1)}
    .icon{font-size:3.5rem;margin-bottom:1rem}
    h1{color:#1a365d;font-size:1.6rem;margin-bottom:.75rem}
    p{color:#4a5568;line-height:1.6;margin-bottom:.75rem}
    .ref{background:#ebf4ff;border-radius:8px;padding:.75rem 1.25rem;display:inline-block;margin:.5rem 0;color:#1a365d;font-weight:700;font-size:1.3rem;letter-spacing:1px}
    a{display:inline-block;margin-top:1.5rem;padding:.7rem 1.5rem;background:#2b6cb0;color:white;border-radius:8px;text-decoration:none;font-weight:600}
  </style>
</head>
<body>
  <div class="box">
    <div class="icon">&#10003;</div>
    <h1>Request Received!</h1>
    <p>Thanks, <strong>{{ name }}</strong>! Your rental request is in.</p>
    <p>Your booking reference:</p>
    <div class="ref">#{{ booking_id }}</div>
    <p>We'll review your request and send a quote to <strong>{{ email }}</strong> shortly.</p>
    {% if business_phone %}<p>Questions? Call <strong>{{ business_phone }}</strong></p>{% endif %}
    <a href="/">Submit Another Request</a>
  </div>
</body></html>
"""


PAYMENT_SUCCESS_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <link rel="manifest" href="/manifest.json">
  <meta name="theme-color" content="#2563eb">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="default">
  <meta name="apple-mobile-web-app-title" content="Rent a Party">
  <link rel="apple-touch-icon" href="/icon-192.png">
  <script>if("serviceWorker"in navigator)navigator.serviceWorker.register("/sw.js");</script>
  <title>Payment Received — {{ business_name }}</title>
  <style>
    body{font-family:-apple-system,sans-serif;background:#f0f4f8;display:flex;align-items:center;justify-content:center;min-height:100vh;margin:0}
    .box{background:white;border-radius:16px;padding:3rem 2.5rem;text-align:center;max-width:480px;width:90%;box-shadow:0 4px 24px rgba(0,0,0,.1)}
    .icon{font-size:3.5rem;margin-bottom:1rem}
    h1{color:#276749;font-size:1.6rem;margin-bottom:.75rem}
    p{color:#4a5568;line-height:1.6;margin-bottom:.75rem}
  </style>
</head>
<body>
  <div class="box">
    <div class="icon">&#127881;</div>
    <h1>Payment Received!</h1>
    <p>Thank you! Your deposit for <strong>Booking #{{ booking_id }}</strong> has been received.</p>
    <p>Your reservation is now <strong>confirmed</strong>. We look forward to serving you!</p>
    <p style="font-weight:600;color:#2d3748">&#8212; {{ business_name }}</p>
    {% if business_phone %}<p style="font-size:.9rem;color:#718096">Questions? Call {{ business_phone }}</p>{% endif %}
  </div>
</body></html>
"""


ADMIN_LOGIN_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <link rel="manifest" href="/manifest.json">
  <meta name="theme-color" content="#2563eb">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="default">
  <meta name="apple-mobile-web-app-title" content="Rent a Party">
  <link rel="apple-touch-icon" href="/icon-192.png">
  <script>if("serviceWorker"in navigator)navigator.serviceWorker.register("/sw.js");</script>
  <title>Admin Login — {{ business_name }}</title>
  <style>
    body{font-family:-apple-system,sans-serif;background:#f0f4f8;display:flex;align-items:center;justify-content:center;min-height:100vh;margin:0}
    .box{background:white;border-radius:12px;padding:2.5rem;max-width:360px;width:90%;box-shadow:0 4px 24px rgba(0,0,0,.1)}
    h1{color:#1a365d;font-size:1.4rem;margin-bottom:1.5rem;text-align:center}
    label{display:block;font-size:.85rem;font-weight:600;color:#4a5568;margin-bottom:.3rem}
    input{width:100%;padding:.65rem .85rem;border:1.5px solid #cbd5e0;border-radius:8px;font-size:.97rem;margin-bottom:1rem}
    input:focus{outline:none;border-color:#2b6cb0}
    button{width:100%;padding:.85rem;background:linear-gradient(135deg,#1a365d,#2b6cb0);color:white;border:none;border-radius:8px;font-size:1rem;font-weight:700;cursor:pointer}
    .err{background:#fff5f5;border:1px solid #feb2b2;color:#c53030;padding:.7rem;border-radius:8px;margin-bottom:1rem;font-size:.9rem;text-align:center}
  </style>
</head>
<body>
  <div class="box">
    <h1>Admin Login</h1>
    {% if error %}<div class="err">{{ error }}</div>{% endif %}
    <form method="POST">
      <label>Password</label>
      <input type="password" name="password" autofocus required>
      <button type="submit">Sign In</button>
    </form>
  </div>
</body></html>
"""


ADMIN_DASH_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <link rel="manifest" href="/manifest.json">
  <meta name="theme-color" content="#2563eb">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="default">
  <meta name="apple-mobile-web-app-title" content="Rent a Party">
  <link rel="apple-touch-icon" href="/icon-192.png">
  <script>if("serviceWorker"in navigator)navigator.serviceWorker.register("/sw.js");</script>
  <title>Admin — {{ business_name }}</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Helvetica,sans-serif;background:#f5f6fa;color:#111827;min-height:100vh}

    /* Top bar */
    .topbar{background:white;border-bottom:1px solid #e5e7eb;padding:.9rem 1.75rem;display:flex;justify-content:space-between;align-items:center;position:sticky;top:0;z-index:50}
    .topbar-brand{font-size:1rem;font-weight:700;color:#111827;display:flex;align-items:center;gap:.5rem}
    .topbar-brand span{font-size:1.25rem}
    .logout-btn{background:white;border:1px solid #d1d5db;color:#6b7280;padding:.38rem .85rem;border-radius:6px;cursor:pointer;font-size:.82rem;font-weight:500;text-decoration:none;transition:all .15s}
    .logout-btn:hover{border-color:#9ca3af;color:#374151}

    /* Layout */
    .main{max-width:1280px;margin:0 auto;padding:1.75rem 1.75rem}
    .page-title{font-size:1.4rem;font-weight:700;color:#111827;margin-bottom:1.25rem}

    /* Metric cards */
    .metrics{display:grid;grid-template-columns:repeat(4,1fr);gap:1rem;margin-bottom:1.75rem}
    .metric{background:white;border:1px solid #e5e7eb;border-radius:10px;padding:1.25rem 1.5rem}
    .metric-label{font-size:.72rem;color:#9ca3af;text-transform:uppercase;letter-spacing:.6px;margin-bottom:.35rem;font-weight:600}
    .metric-value{font-size:1.9rem;font-weight:700;color:#111827;line-height:1}

    /* Inventory grid */
    .section-title{font-size:.95rem;font-weight:700;color:#374151;margin:0 0 .75rem;text-transform:uppercase;letter-spacing:.4px}
    .inv-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(240px,1fr));gap:.75rem;margin-bottom:1.75rem}
    .inv-card{background:white;border:1px solid #e5e7eb;border-radius:10px;padding:1rem 1.1rem}
    .inv-name{font-size:.85rem;font-weight:600;color:#111827;margin-bottom:.55rem;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
    .inv-meta{display:flex;justify-content:space-between;align-items:center;font-size:.75rem;margin-bottom:.45rem}
    .inv-reserved{color:#6b7280}
    .inv-avail-ok{color:#059669;font-weight:700}
    .inv-avail-low{color:#d97706;font-weight:700}
    .inv-avail-zero{color:#dc2626;font-weight:700}
    .inv-bar{height:5px;border-radius:3px;background:#e5e7eb;overflow:hidden}
    .inv-fill{height:100%;border-radius:3px}

    /* Tabs + table card */
    .tabs{display:flex;background:white;border:1px solid #e5e7eb;border-bottom:none;border-radius:10px 10px 0 0;overflow-x:auto}
    .tab{padding:.7rem 1.1rem;font-size:.82rem;font-weight:500;color:#6b7280;text-decoration:none;border-bottom:2px solid transparent;white-space:nowrap;flex-shrink:0;transition:all .12s}
    .tab:hover{color:#111827;background:#f9fafb}
    .tab.active{color:#2563eb;border-bottom-color:#2563eb;font-weight:600}
    .table-card{background:white;border:1px solid #e5e7eb;border-radius:0 0 10px 10px;overflow:hidden}
    .table-scroll{overflow-x:auto;-webkit-overflow-scrolling:touch}
    .table-scroll table{min-width:900px}

    /* Table */
    table{width:100%;border-collapse:collapse}
    thead tr{background:#f9fafb}
    th{padding:.7rem 1rem;text-align:left;font-size:.72rem;font-weight:600;color:#9ca3af;text-transform:uppercase;letter-spacing:.5px;border-bottom:1px solid #e5e7eb;white-space:nowrap}
    td{padding:.85rem 1rem;border-bottom:1px solid #f3f4f6;vertical-align:middle;font-size:.86rem;color:#374151}
    tr:last-child td{border-bottom:none}
    tbody tr:hover td{background:#fafafa}

    /* Avatar */
    .client-cell{display:flex;align-items:center;gap:.6rem}
    .avatar{width:32px;height:32px;border-radius:50%;display:flex;align-items:center;justify-content:center;font-size:.78rem;font-weight:700;color:white;flex-shrink:0}
    .client-name{font-weight:600;color:#111827;font-size:.86rem}
    .client-email{font-size:.75rem;color:#9ca3af;margin-top:.05rem}

    /* Booking status badges */
    .badge{display:inline-flex;align-items:center;padding:.22rem .65rem;border-radius:20px;font-size:.74rem;font-weight:600;white-space:nowrap}
    .badge-pending{background:#fef9c3;color:#854d0e}
    .badge-accepted{background:#dbeafe;color:#1e40af}
    .badge-confirmed{background:#dcfce7;color:#166534}
    .badge-denied{background:#fee2e2;color:#991b1b}
    .badge-cancelled{background:#f3f4f6;color:#6b7280}

    /* Payment status badges */
    .pay-badge{display:inline-flex;align-items:center;padding:.22rem .65rem;border-radius:20px;font-size:.74rem;font-weight:600;white-space:nowrap}
    .pay-paid{background:#dcfce7;color:#166534}
    .pay-due{background:#fef9c3;color:#854d0e}
    .pay-partial{background:#dbeafe;color:#1e40af}
    .pay-none{color:#9ca3af;font-size:.78rem}

    /* Date range */
    .date-range{display:flex;align-items:center;gap:.35rem;font-size:.83rem;white-space:nowrap}
    .date-arrow{color:#d1d5db;font-size:.7rem}

    /* Action buttons */
    .action-btns{display:flex;gap:.35rem;flex-wrap:nowrap;align-items:center}
    .btn{display:inline-block;padding:.3rem .65rem;border-radius:6px;font-size:.76rem;font-weight:600;cursor:pointer;border:1px solid transparent;text-decoration:none;line-height:1.5;white-space:nowrap;transition:all .12s}
    .btn-view{background:#eff6ff;color:#2563eb;border-color:#bfdbfe}
    .btn-view:hover{background:#dbeafe}
    .btn-accept{background:#f0fdf4;color:#166534;border-color:#bbf7d0}
    .btn-accept:hover{background:#dcfce7}
    .btn-deny{background:#fef2f2;color:#991b1b;border-color:#fecaca}
    .btn-deny:hover{background:#fee2e2}
    .btn-confirm{background:#eff6ff;color:#1e40af;border-color:#bfdbfe}
    .btn-confirm:hover{background:#dbeafe}
    .btn-cancel{background:#f9fafb;color:#6b7280;border-color:#d1d5db}

    .empty-state{padding:3rem;text-align:center;color:#9ca3af;font-size:.95rem}

    @media(max-width:900px){
      .metrics{grid-template-columns:1fr 1fr}
      .main{padding:1rem}
    }
    @media(max-width:540px){
      .metrics{grid-template-columns:1fr}
      th,td{padding:.6rem .75rem}
    }
  </style>
</head>
<body>

<div class="topbar">
  <div class="topbar-brand"><span>🎉</span> {{ business_name }}</div>
  <div style="display:flex;align-items:center;gap:.5rem">
    <a href="/admin/dashboard" style="color:#2563eb;font-size:.85rem;font-weight:600;text-decoration:none;padding:.38rem .75rem;border-radius:6px;background:#eff6ff">Dashboard</a>
    <a href="/admin/inventory" style="color:#6b7280;font-size:.85rem;font-weight:500;text-decoration:none;padding:.38rem .75rem;border-radius:6px;transition:all .12s" onmouseover="this.style.background='#f3f4f6'" onmouseout="this.style.background=''">Inventory</a>
    <a href="/admin/customers" style="color:#6b7280;font-size:.85rem;font-weight:500;text-decoration:none;padding:.38rem .75rem;border-radius:6px;transition:all .12s" onmouseover="this.style.background='#f3f4f6'" onmouseout="this.style.background=''">Customers</a>
    <a href="/admin/calendar" class="nav-link">📅 Calendar</a>
    <a href="/admin/route" class="nav-link">🗺 Route</a>
    <a href="/admin/booking/new" style="background:#16a34a;color:white;font-size:.85rem;font-weight:600;text-decoration:none;padding:.38rem .85rem;border-radius:6px">+ New Booking</a>
    <a href="/admin/logout" class="logout-btn">Sign Out</a>
  </div>
</div>

<div class="main">
  <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:1.25rem;flex-wrap:wrap;gap:.75rem">
    <div class="page-title" style="margin-bottom:0">Dashboard</div>
    <div style="position:relative">
      <input type="text" id="dash-search" placeholder="🔍 Search bookings…" oninput="filterDash(this.value)"
        style="border:1px solid #d1d5db;border-radius:8px;padding:.45rem 1rem;font-size:.88rem;width:260px;outline:none;transition:border .12s;background:white"
        onfocus="this.style.borderColor='#2563eb'" onblur="this.style.borderColor='#d1d5db'">
      <span id="dash-count" style="position:absolute;right:.6rem;top:50%;transform:translateY(-50%);font-size:.75rem;color:#9ca3af"></span>
    </div>
  </div>

  <!-- ── Inventory Conflict Alert ── -->
  {% if inv_conflicts %}
  <div style="background:#fef2f2;border:2px solid #f87171;border-radius:10px;padding:1rem 1.25rem;margin-bottom:1.5rem">
    <div style="display:flex;align-items:center;gap:.6rem;margin-bottom:.6rem">
      <span style="font-size:1.2rem">🚨</span>
      <span style="font-weight:700;color:#991b1b;font-size:.95rem">Inventory Conflict — {{ inv_conflicts|length }} item{{ 's' if inv_conflicts|length != 1 else '' }} over-committed</span>
    </div>
    <div style="display:flex;flex-direction:column;gap:.35rem">
      {% for c in inv_conflicts %}
      <div style="background:white;border:1px solid #fecaca;border-radius:7px;padding:.5rem .85rem;display:flex;flex-wrap:wrap;align-items:center;justify-content:space-between;gap:.5rem;font-size:.86rem">
        <div>
          <a href="/admin/booking/{{ c.booking_id }}" style="font-weight:700;color:#dc2626;text-decoration:none">Booking #{{ c.booking_id }}</a>
          <span style="color:#374151"> — {{ c.customer }}</span>
          <span style="color:#9ca3af;font-size:.78rem"> ({{ c.event_date }})</span>
        </div>
        <div style="color:#7f1d1d;font-size:.83rem">
          <strong>{{ c.item }}</strong>: needs <strong>{{ c.needed }}</strong>, only <strong>{{ c.available }}</strong> available
          <span style="background:#dc2626;color:white;border-radius:4px;padding:.1rem .45rem;font-size:.75rem;font-weight:700;margin-left:.3rem">-{{ c.shortfall }} short</span>
        </div>
      </div>
      {% endfor %}
    </div>
  </div>
  {% endif %}

  <!-- ── Metric Cards ── -->
  <div class="metrics">
    <div class="metric">
      <div class="metric-label">Bookings</div>
      <div class="metric-value">{{ stats.total }}</div>
    </div>
    <div class="metric">
      <div class="metric-label">Pending Review</div>
      <div class="metric-value" style="color:#d97706">{{ stats.pending }}</div>
    </div>
    <div class="metric">
      <div class="metric-label">Revenue</div>
      <div class="metric-value" style="color:#059669">${{ "{:,.2f}".format(stats.revenue) }}</div>
    </div>
    <div class="metric">
      <div class="metric-label">Amount Due</div>
      <div class="metric-value" style="color:#dc2626">${{ "{:,.2f}".format(stats.amount_due) }}</div>
    </div>
  </div>


  <!-- ── Bookings ── -->
  {% set df = ('&date_from=' ~ date_from) if date_from else '' %}
  {% set dt = ('&date_to=' ~ date_to) if date_to else '' %}
  {% set pf = ('&pay_filter=' ~ pay_filter) if pay_filter else '' %}
  {% set sf = ('&sort=' ~ sort_by) if (sort_by and sort_by != 'date') else '' %}
  <div class="tabs">
    <a href="/admin/dashboard?status=pending&sort=created_asc" class="tab {% if status_filter=='pending' and not past_filter %}active{% endif %}" style="{% if status_filter=='pending' and not past_filter %}color:#d97706;border-bottom-color:#d97706;{% endif %}">🆕&nbsp;New{% if stats.pending > 0 %}&nbsp;<span style="background:#d97706;color:white;border-radius:99px;padding:.05rem .45rem;font-size:.72rem;font-weight:700;margin-left:.2rem">{{ stats.pending }}</span>{% endif %}</a>
    <a href="/admin/dashboard?upcoming=1" class="tab {% if upcoming_filter %}active{% endif %}" style="{% if upcoming_filter %}color:#f97316;border-bottom-color:#f97316;{% endif %}">🔔&nbsp;Upcoming&nbsp;{% if stats.upcoming > 0 %}<span style="background:#f97316;color:white;border-radius:99px;padding:.05rem .45rem;font-size:.72rem;font-weight:700;margin-left:.2rem">{{ stats.upcoming }}</span>{% endif %}</a>
    <a href="/admin/dashboard?status=accepted{{ df }}{{ dt }}{{ pf }}{{ sf }}"  class="tab {% if status_filter=='accepted'  and not past_filter %}active{% endif %}">Accepted&nbsp;({{ stats.accepted }})</a>
    <a href="/admin/dashboard?status=confirmed{{ df }}{{ dt }}{{ pf }}{{ sf }}" class="tab {% if status_filter=='confirmed' and not past_filter %}active{% endif %}">Confirmed&nbsp;({{ stats.confirmed }})</a>
    <a href="/admin/dashboard?status=denied{{ df }}{{ dt }}{{ pf }}{{ sf }}"    class="tab {% if status_filter=='denied'    and not past_filter %}active{% endif %}">Denied</a>
    <a href="/admin/dashboard?status=cancelled{{ df }}{{ dt }}{{ pf }}{{ sf }}" class="tab {% if status_filter=='cancelled' and not past_filter %}active{% endif %}">Cancelled</a>
    <a href="/admin/dashboard?past=1" class="tab {% if past_filter %}active{% endif %}" style="{% if past_filter %}color:#6366f1;border-bottom-color:#6366f1;{% endif %}">🕓&nbsp;Past&nbsp;({{ stats.past }})</a>
    <a href="/admin/dashboard" class="tab {% if not status_filter and not upcoming_filter and not archived_filter and not past_filter %}active{% endif %}">All&nbsp;({{ stats.total }})</a>
    <a href="/admin/dashboard?archived=1" class="tab {% if archived_filter %}active{% endif %}" style="{% if archived_filter %}color:#9ca3af;border-bottom-color:#9ca3af;{% endif %}">📦&nbsp;Archived</a>
  </div>

  <!-- ── Date Range + Payment Filter + Sort ── -->
  <form method="GET" action="/admin/dashboard" style="background:white;border:1px solid #e5e7eb;border-bottom:none;padding:.65rem 1rem;display:flex;flex-wrap:wrap;gap:.6rem;align-items:center">
    <input type="hidden" name="status" value="{{ status_filter }}">
    <label style="font-size:.78rem;font-weight:600;color:#6b7280;margin-right:.1rem">Event Date:</label>
    <input type="date" name="date_from" value="{{ date_from }}" style="border:1px solid #d1d5db;border-radius:6px;padding:.3rem .55rem;font-size:.82rem;color:#374151">
    <span style="font-size:.82rem;color:#9ca3af">to</span>
    <input type="date" name="date_to" value="{{ date_to }}" style="border:1px solid #d1d5db;border-radius:6px;padding:.3rem .55rem;font-size:.82rem;color:#374151">
    <label style="font-size:.78rem;font-weight:600;color:#6b7280;margin-left:.5rem">Payment:</label>
    <select name="pay_filter" style="border:1px solid #d1d5db;border-radius:6px;padding:.3rem .55rem;font-size:.82rem;color:#374151">
      <option value="" {% if not pay_filter %}selected{% endif %}>All</option>
      <option value="paid"    {% if pay_filter=='paid'    %}selected{% endif %}>Paid In Full</option>
      <option value="partial" {% if pay_filter=='partial' %}selected{% endif %}>Partially Paid</option>
      <option value="due"     {% if pay_filter=='due'     %}selected{% endif %}>Payment Due</option>
    </select>
    <label style="font-size:.78rem;font-weight:600;color:#6b7280;margin-left:.5rem">Sort:</label>
    <select name="sort" style="border:1px solid #d1d5db;border-radius:6px;padding:.3rem .55rem;font-size:.82rem;color:#374151">
      <option value="date"      {% if sort_by=='date'      %}selected{% endif %}>Event Date ↑</option>
      <option value="date_desc" {% if sort_by=='date_desc' %}selected{% endif %}>Event Date ↓</option>
      <option value="name"      {% if sort_by=='name'      %}selected{% endif %}>Client A→Z</option>
      <option value="name_desc" {% if sort_by=='name_desc' %}selected{% endif %}>Client Z→A</option>
      <option value="id"        {% if sort_by=='id'        %}selected{% endif %}>Booking # ↓</option>
      <option value="id_asc"    {% if sort_by=='id_asc'    %}selected{% endif %}>Booking # ↑</option>
      <option value="total"     {% if sort_by=='total'     %}selected{% endif %}>Total ↓</option>
      <option value="created"   {% if sort_by=='created'   %}selected{% endif %}>Date Added ↓</option>
    </select>
    <button type="submit" style="background:#2563eb;color:white;border:none;border-radius:6px;padding:.35rem .85rem;font-size:.82rem;font-weight:600;cursor:pointer">Apply</button>
    {% if date_from or date_to or pay_filter %}<a href="/admin/dashboard?status={{ status_filter }}" style="font-size:.78rem;color:#6b7280;text-decoration:none">✕ Clear</a>{% endif %}
  </form>

  <!-- Bulk action bar (hidden until checkboxes selected) -->
  <div id="bulkBar" style="display:none;background:#1e3a5f;color:white;padding:.6rem 1rem;display:flex;gap:.75rem;align-items:center;border-radius:8px;margin-bottom:.5rem">
    <span id="bulkCount" style="font-size:.85rem;font-weight:600"></span>
    <form method="POST" action="/admin/bookings/bulk-archive" id="bulkArchiveForm">
      <input type="hidden" name="ids" id="bulkArchiveIds">
      <button type="button" onclick="bulkAction('archive')" style="background:#f97316;color:white;border:none;border-radius:6px;padding:.3rem .8rem;font-size:.82rem;font-weight:600;cursor:pointer">📦 Archive Selected</button>
    </form>
    <form method="POST" action="/admin/bookings/bulk-delete" id="bulkDeleteForm">
      <input type="hidden" name="ids" id="bulkDeleteIds">
      <button type="button" onclick="bulkAction('delete')" style="background:#ef4444;color:white;border:none;border-radius:6px;padding:.3rem .8rem;font-size:.82rem;font-weight:600;cursor:pointer">🗑 Delete Selected</button>
    </form>
    <button type="button" onclick="clearAll()" style="background:transparent;color:#9ca3af;border:1px solid #4b5563;border-radius:6px;padding:.3rem .8rem;font-size:.82rem;cursor:pointer">✕ Clear</button>
  </div>

  <div class="table-card">
    {% if bookings %}
    <div class="table-scroll">
    <table>
      <thead>
        <tr>
          <th style="width:36px;padding-left:.75rem"><input type="checkbox" id="selectAll" onchange="toggleAll(this)" style="cursor:pointer;width:15px;height:15px;accent-color:#2563eb"></th>
          <th>#</th>
          <th>Client</th>
          <th>Status</th>
          <th>Event Dates</th>
          <th>Items</th>
          <th>Total</th>
          <th>Payment</th>
          <th>Actions</th>
        </tr>
      </thead>
      <tbody>
        {% for b in bookings %}
        <tr id="row-{{ b.id }}" data-search="{{ (b.full_name or '') | lower }} {{ (b.email or '') | lower }} {{ (b.phone or '') | lower }} {{ (b.event_start_date or '') }} {{ (b.items_summary or '') | lower }}">
          <td style="padding-left:.75rem"><input type="checkbox" class="row-cb" value="{{ b.id }}" onchange="updateBulkBar()" style="cursor:pointer;width:15px;height:15px;accent-color:#2563eb"></td>
          <td style="font-weight:700;color:#2563eb;font-size:.83rem">#{{ b.id }}</td>
          <td>
            <div class="client-cell">
              <div class="avatar" style="background:{{ b.avatar_color }}">{{ b.avatar_initials }}</div>
              <div>
                <div class="client-name">{{ b.full_name }}</div>
                <div class="client-email">{{ b.email }}</div>
                {% if b.phone %}<div style="font-size:.75rem;color:#6b7280;margin-top:.1rem"><a href="tel:{{ b.phone }}" style="color:#6b7280;text-decoration:none">📞 {{ b.phone }}</a></div>{% endif %}
              </div>
            </div>
          </td>
          <td><span class="badge badge-{{ b.status }}">{{ b.status | capitalize }}</span></td>
          <td>
            <div class="date-range">
              <span>{{ b.event_start_date.strftime('%m/%d/%Y') if b.event_start_date else '' }}</span>
              <span class="date-arrow">→</span>
              <span>{{ b.event_end_date.strftime('%m/%d/%Y') if b.event_end_date else '' }}</span>
            </div>
            {% if b.maps_url %}
            <a href="{{ b.maps_url }}" target="_blank" rel="noopener noreferrer"
               style="display:inline-flex;align-items:center;gap:.18rem;margin-top:.25rem;font-size:.73rem;color:#2563eb;text-decoration:none;font-weight:500;opacity:.85"
               title="{{ b.event_street }}, {{ b.event_city }}, {{ b.event_state }} {{ b.event_zip }}">
              📍 Map
            </a>
            {% endif %}
          </td>
          <td style="max-width:170px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;color:#6b7280;font-size:.8rem">{{ b.items_summary }}</td>
          <td style="font-weight:700;white-space:nowrap">${{ "%.2f"|format(b.grand_total or 0) }}</td>
          <td>
            {% if b.pay_label != '—' %}
            <span class="pay-badge {{ b.pay_class }}">{{ b.pay_label }}</span>
            {% else %}
            <span class="pay-none">—</span>
            {% endif %}
          </td>
          <td>
            <div class="action-btns">
              <a href="/admin/booking/{{ b.id }}" class="btn btn-view">View</a>
              {% if b.status == 'pending' %}
              <form method="POST" action="/admin/booking/{{ b.id }}/accept" style="display:inline">
                <button class="btn btn-accept" onclick="return confirm('Accept #{{ b.id }}? This emails {{ b.email }} their invoice + Stripe payment link.')">Accept</button>
              </form>
              <form method="POST" action="/admin/booking/{{ b.id }}/deny" style="display:inline">
                <button class="btn btn-deny" onclick="return confirm('Deny booking #{{ b.id }}?')">Deny</button>
              </form>
              {% endif %}
              {% if b.status == 'accepted' %}
              <form method="POST" action="/admin/booking/{{ b.id }}/confirm" style="display:inline">
                <button class="btn btn-confirm" onclick="return confirm('Manually mark #{{ b.id }} as paid?')">Mark Paid</button>
              </form>
              {% endif %}
              {% if b.status not in ('denied', 'cancelled') %}
              <form method="POST" action="/admin/booking/{{ b.id }}/cancel" style="display:inline">
                <button class="btn btn-cancel" onclick="return confirm('Cancel booking #{{ b.id }}?')">Cancel</button>
              </form>
              {% endif %}
              {% if b.delivery_status != 'picked_up' %}
              <form method="POST" action="/admin/booking/{{ b.id }}/delivery-status" style="display:inline">
                {% if not b.delivery_status %}
                <button class="btn" style="background:#fffbeb;color:#92400e;border:1px solid #fcd34d;font-size:.75rem"
                  onclick="return confirm('Mark booking #{{ b.id }} as DELIVERED?')">🚚 Delivered</button>
                {% elif b.delivery_status == 'delivered' %}
                <button class="btn" style="background:#eff6ff;color:#1e40af;border:1px solid #93c5fd;font-size:.75rem"
                  onclick="return confirm('Mark booking #{{ b.id }} as PICKED UP?')">✅ Picked Up</button>
                {% endif %}
              </form>
              {% else %}
              <span style="font-size:.75rem;color:#16a34a;font-weight:600;padding:.28rem .5rem;background:#f0fdf4;border:1px solid #86efac;border-radius:6px">✔ Picked Up</span>
              {% endif %}
              <!-- Archive / Delete / Unarchive dropdown -->
              <form method="POST" id="mgmt-form-{{ b.id }}" action="" style="display:inline">
                <select onchange="submitMgmt({{ b.id }}, this)" style="border:1px solid #d1d5db;border-radius:6px;padding:.28rem .5rem;font-size:.78rem;color:#374151;cursor:pointer;margin-left:.25rem">
                  <option value="">⚙ More</option>
                  {% if b.archived %}
                  <option value="/admin/booking/{{ b.id }}/unarchive">↩ Unarchive</option>
                  {% else %}
                  <option value="/admin/booking/{{ b.id }}/archive">📦 Archive</option>
                  {% endif %}
                  <option value="/admin/booking/{{ b.id }}/delete" data-confirm="Permanently delete booking #{{ b.id }}? This cannot be undone.">🗑 Delete</option>
                </select>
              </form>
            </div>
          </td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
    </div>
    {% else %}
    <div class="empty-state">No bookings found.</div>
    {% endif %}
  </div>

</div>
<script>
function submitMgmt(id, sel){
  var url = sel.value;
  if(!url){ return; }
  var opt = sel.options[sel.selectedIndex];
  var msg = opt.getAttribute('data-confirm') || ('Are you sure?');
  if(!confirm(msg)){ sel.selectedIndex=0; return; }
  var f = document.getElementById('mgmt-form-'+id);
  f.action = url;
  f.submit();
}

function getChecked(){
  return Array.from(document.querySelectorAll('.row-cb:checked')).map(c=>c.value);
}

function updateBulkBar(){
  var ids = getChecked();
  var bar = document.getElementById('bulkBar');
  if(ids.length > 0){
    bar.style.display = 'flex';
    document.getElementById('bulkCount').textContent = ids.length + ' selected';
  } else {
    bar.style.display = 'none';
  }
  var all = document.querySelectorAll('.row-cb');
  document.getElementById('selectAll').indeterminate = ids.length > 0 && ids.length < all.length;
  document.getElementById('selectAll').checked = ids.length === all.length && all.length > 0;
}

function toggleAll(cb){
  document.querySelectorAll('.row-cb').forEach(c => c.checked = cb.checked);
  updateBulkBar();
}

function clearAll(){
  document.querySelectorAll('.row-cb').forEach(c => c.checked = false);
  document.getElementById('selectAll').checked = false;
  document.getElementById('bulkBar').style.display = 'none';
}

function filterDash(q){
  const term = q.toLowerCase().trim();
  const rows = document.querySelectorAll('tbody tr[data-search]');
  let shown = 0;
  rows.forEach(row => {
    const match = !term || row.dataset.search.includes(term);
    row.style.display = match ? '' : 'none';
    if(match) shown++;
  });
  const cnt = document.getElementById('dash-count');
  if(cnt) cnt.textContent = term ? shown + ' found' : '';
}

function bulkAction(type){
  var ids = getChecked();
  if(ids.length === 0) return;
  var msg = type === 'delete'
    ? 'Permanently delete ' + ids.length + ' booking(s)? This cannot be undone.'
    : 'Archive ' + ids.length + ' booking(s)?';
  if(!confirm(msg)) return;
  var idStr = ids.join(',');
  if(type === 'delete'){
    document.getElementById('bulkDeleteIds').value = idStr;
    document.getElementById('bulkDeleteForm').submit();
  } else {
    document.getElementById('bulkArchiveIds').value = idStr;
    document.getElementById('bulkArchiveForm').submit();
  }
}
</script>
</body></html>
"""


ADMIN_BOOKING_EDIT_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <title>Edit Booking #{{ b.id }} — {{ business_name }}</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:-apple-system,sans-serif;background:#f0f4f8;color:#1a202c;min-height:100vh}
    header{background:linear-gradient(135deg,#1a365d,#2b6cb0);color:white;padding:1.25rem 2rem;display:flex;justify-content:space-between;align-items:center}
    header h1{font-size:1.2rem}
    .container{max-width:800px;margin:0 auto;padding:1.5rem 1rem}
    .card{background:white;border-radius:12px;box-shadow:0 2px 12px rgba(0,0,0,.08);padding:1.5rem;margin-bottom:1.5rem}
    .card h2{font-size:.95rem;font-weight:700;color:#2b6cb0;border-bottom:2px solid #ebf4ff;padding-bottom:.5rem;margin-bottom:1rem;text-transform:uppercase;letter-spacing:.4px}
    .field-grid{display:grid;grid-template-columns:1fr 1fr;gap:.75rem 1rem}
    .field-grid.single{grid-template-columns:1fr}
    .field-grid.triple{grid-template-columns:1fr 1fr 1fr}
    label{display:block;font-size:.78rem;font-weight:600;color:#6b7280;margin-bottom:.25rem;text-transform:uppercase;letter-spacing:.3px}
    input,select,textarea{width:100%;border:1px solid #d1d5db;border-radius:7px;padding:.5rem .75rem;font-size:.92rem;color:#1a202c;background:white}
    input:focus,select:focus,textarea:focus{outline:none;border-color:#2563eb;box-shadow:0 0 0 3px rgba(37,99,235,.1)}
    textarea{resize:vertical;min-height:80px}
    .actions{display:flex;gap:.75rem;flex-wrap:wrap;margin-top:1.5rem}
    .btn{padding:.65rem 1.4rem;border-radius:8px;font-size:.9rem;font-weight:600;cursor:pointer;border:none;text-decoration:none;display:inline-block}
    .btn-save{background:#16a34a;color:white}
    .btn-cancel{background:#f0f4f8;color:#4a5568;text-decoration:none}
    a{color:#2b6cb0}
  </style>
</head>
<body>
<header>
  <h1>✏️ Edit Booking #{{ b.id }} — {{ b.full_name }}</h1>
  <a href="/admin/booking/{{ b.id }}" style="color:white;text-decoration:none;font-size:.9rem">← Cancel</a>
</header>
<div class="container">
<form method="POST" action="/admin/booking/{{ b.id }}/edit">

  <div class="card">
    <h2>Customer</h2>
    <div class="field-grid">
      <div><label>Full Name</label><input name="full_name" value="{{ b.full_name or '' }}"></div>
      <div><label>Company</label><input name="company_name" value="{{ b.company_name or '' }}"></div>
      <div><label>Email</label><input name="email" type="email" value="{{ b.email or '' }}"></div>
      <div><label>Phone</label><input name="phone" value="{{ b.phone or '' }}"></div>
      <div><label>Street</label><input name="renter_street" value="{{ b.renter_street or '' }}"></div>
      <div><label>City</label><input name="renter_city" value="{{ b.renter_city or '' }}"></div>
      <div><label>State</label><input name="renter_state" value="{{ b.renter_state or '' }}"></div>
      <div><label>ZIP</label><input name="renter_zip" value="{{ b.renter_zip or '' }}"></div>
    </div>
  </div>

  <div class="card">
    <h2>Event</h2>
    <div class="field-grid">
      <div><label>Start Date</label><input name="event_start_date" type="date" value="{{ b.event_start_date or '' }}"></div>
      <div><label>End Date</label><input name="event_end_date" type="date" value="{{ b.event_end_date or '' }}"></div>
      <div><label>Event Start Time</label><input name="event_start_time" type="time" value="{{ b.event_start_time or '' }}"></div>
      <div><label>Pickup Time</label><input name="event_end_time" type="time" value="{{ b.event_end_time or '' }}"></div>
      <div><label>Delivery Time</label><input name="setup_time" type="time" value="{{ b.setup_time or '' }}"></div>
      <div><label>Venue Type</label>
        <select name="venue_type">
          <option value="venue" {% if b.venue_type=='venue' %}selected{% endif %}>Venue</option>
          <option value="backyard" {% if b.venue_type=='backyard' %}selected{% endif %}>Backyard</option>
          <option value="park" {% if b.venue_type=='park' %}selected{% endif %}>Park</option>
          <option value="other" {% if b.venue_type=='other' %}selected{% endif %}>Other</option>
        </select>
      </div>
    </div>
    <div class="field-grid" style="margin-top:.75rem">
      <div><label>Event Street</label><input name="event_street" value="{{ b.event_street or '' }}"></div>
      <div><label>Event City</label><input name="event_city" value="{{ b.event_city or '' }}"></div>
      <div><label>Event State</label><input name="event_state" value="{{ b.event_state or '' }}"></div>
      <div><label>Event ZIP</label><input name="event_zip" value="{{ b.event_zip or '' }}"></div>
      <div class="single" style="grid-column:1/-1"><label>Delivery Location / Notes on Venue</label><input name="delivery_location" value="{{ b.delivery_location or '' }}"></div>
    </div>
  </div>

  <div class="card">
    <h2>Financials & Status</h2>
    <div class="field-grid">
      <div><label>Status</label>
        <select name="status">
          <option value="pending"   {% if b.status=='pending'   %}selected{% endif %}>Pending</option>
          <option value="accepted"  {% if b.status=='accepted'  %}selected{% endif %}>Accepted (Awaiting Payment)</option>
          <option value="confirmed" {% if b.status=='confirmed' %}selected{% endif %}>Confirmed (Paid)</option>
          <option value="denied"    {% if b.status=='denied'    %}selected{% endif %}>Denied</option>
          <option value="cancelled" {% if b.status=='cancelled' %}selected{% endif %}>Cancelled</option>
        </select>
      </div>
      <div><label>Grand Total ($)</label><input name="grand_total" type="number" step="0.01" value="{{ b.grand_total or 0 }}"></div>
      <div><label>Amount Paid ($)</label><input name="amount_paid" type="number" step="0.01" value="{{ b.amount_paid or 0 }}"></div>
      <div><label>Delivery Fee ($)</label><input name="delivery_fee" type="number" step="0.01" value="{{ b.delivery_fee or 0 }}"></div>
      <div><label>Late Night Fee ($)</label><input name="late_night_fee" type="number" step="0.01" value="{{ b.late_night_fee or 0 }}"></div>
      <div><label>Distance (miles)</label><input name="distance_miles" type="number" step="0.1" value="{{ b.distance_miles or '' }}"></div>
    </div>
  </div>

  <div class="card">
    <h2>Notes</h2>
    <div class="field-grid single">
      <div><textarea name="notes">{{ b.notes or '' }}</textarea></div>
    </div>
  </div>

  <div class="actions">
    <button type="submit" class="btn btn-save">💾 Save Changes</button>
    <a href="/admin/booking/{{ b.id }}" class="btn btn-cancel">Cancel</a>
  </div>
</form>
</div>
</body></html>
"""


ADMIN_NEW_BOOKING_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <title>New Booking — {{ business_name }}</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:-apple-system,sans-serif;background:#f0f4f8;color:#1a202c;min-height:100vh}
    header{background:linear-gradient(135deg,#1a365d,#2b6cb0);color:white;padding:1.25rem 2rem;display:flex;justify-content:space-between;align-items:center}
    header h1{font-size:1.2rem}
    .container{max-width:860px;margin:0 auto;padding:1.5rem 1rem}
    .card{background:white;border-radius:12px;box-shadow:0 2px 12px rgba(0,0,0,.08);padding:1.5rem;margin-bottom:1.5rem}
    .card h2{font-size:.95rem;font-weight:700;color:#2b6cb0;border-bottom:2px solid #ebf4ff;padding-bottom:.5rem;margin-bottom:1rem;text-transform:uppercase;letter-spacing:.4px}
    .fg{display:grid;grid-template-columns:1fr 1fr;gap:.75rem 1rem}
    .fg.one{grid-template-columns:1fr}
    .fg.three{grid-template-columns:1fr 1fr 1fr}
    label{display:block;font-size:.78rem;font-weight:600;color:#6b7280;margin-bottom:.25rem;text-transform:uppercase;letter-spacing:.3px}
    input,select,textarea{width:100%;border:1px solid #d1d5db;border-radius:7px;padding:.5rem .75rem;font-size:.92rem;color:#1a202c;background:white}
    input:focus,select:focus,textarea:focus{outline:none;border-color:#2563eb;box-shadow:0 0 0 3px rgba(37,99,235,.1)}
    textarea{resize:vertical;min-height:70px}
    .item-row{display:grid;grid-template-columns:1fr 80px 110px 90px 36px;gap:.4rem;align-items:center;margin-bottom:.4rem}
    .item-row input{font-size:.88rem}
    .item-total{font-size:.88rem;font-weight:600;color:#2563eb;text-align:right;padding-right:.25rem}
    .add-btn{background:#eff6ff;color:#2563eb;border:1px solid #bfdbfe;border-radius:7px;padding:.4rem .85rem;font-size:.82rem;font-weight:600;cursor:pointer;margin-top:.35rem}
    .del-btn{background:#fef2f2;color:#dc2626;border:1px solid #fecaca;border-radius:6px;width:32px;height:32px;font-size:1rem;cursor:pointer;display:flex;align-items:center;justify-content:center;flex-shrink:0}
    .subtotal-bar{display:flex;justify-content:flex-end;gap:1.5rem;font-size:.88rem;padding:.6rem .25rem;border-top:1px solid #e5e7eb;margin-top:.35rem}
    .subtotal-bar span{font-weight:700;color:#1a202c}
    .actions{display:flex;gap:.75rem;flex-wrap:wrap;margin-top:1.5rem}
    .btn{padding:.65rem 1.4rem;border-radius:8px;font-size:.9rem;font-weight:600;cursor:pointer;border:none;text-decoration:none;display:inline-block}
    .btn-save{background:#16a34a;color:white}
    .btn-cancel{background:#f0f4f8;color:#4a5568}
    .col-hdr{font-size:.72rem;font-weight:600;color:#9ca3af;text-transform:uppercase;letter-spacing:.3px;padding:.1rem .1rem .4rem}
  </style>
</head>
<body>
<header>
  <h1>➕ New Manual Booking</h1>
  <a href="/admin/dashboard" style="color:white;text-decoration:none;font-size:.9rem">← Dashboard</a>
</header>
<div class="container">
<form method="POST" action="/admin/booking/new" id="nbform">

  <div class="card">
    <h2>Customer</h2>
    <div class="fg">
      <div><label>Full Name *</label><input name="full_name" required placeholder="Jane Smith"></div>
      <div><label>Email</label><input name="email" type="email" placeholder="jane@email.com"></div>
      <div><label>Phone</label><input name="phone" placeholder="(555) 000-0000"></div>
      <div><label>Company</label><input name="company_name" placeholder="Optional"></div>
    </div>
  </div>

  <div class="card">
    <h2>Event</h2>
    <div class="fg">
      <div><label>Delivery Date *</label><input name="event_start_date" type="date" required></div>
      <div><label>Pickup Date *</label><input name="event_end_date" type="date" required></div>
      <div><label>Delivery Time</label><input name="event_start_time" type="time" value="16:00"></div>
      <div><label>Pickup Time</label><input name="event_end_time" type="time" value="10:00"></div>
      <div><label>Venue Type</label>
        <select name="venue_type">
          <option value="residential">Residential</option>
          <option value="venue">Venue</option>
          <option value="backyard">Backyard</option>
          <option value="park">Park</option>
          <option value="other">Other</option>
        </select>
      </div>
      <div><label>Status</label>
        <select name="status">
          <option value="confirmed">Confirmed (Paid/Partial)</option>
          <option value="accepted">Accepted (Awaiting Payment)</option>
          <option value="pending">Pending Review</option>
        </select>
      </div>
    </div>
    <div class="fg" style="margin-top:.75rem">
      <div><label>Event Street</label><input name="event_street" placeholder="456 Venue Blvd"></div>
      <div><label>Event City</label><input name="event_city" placeholder="Hartford"></div>
      <div><label>State</label><input name="event_state" placeholder="CT" style="width:80px"></div>
      <div><label>ZIP</label><input name="event_zip" placeholder="06101" style="width:100px"></div>
    </div>
  </div>

  <div class="card">
    <h2>Items</h2>
    <datalist id="inv-list">
      {% for p in products %}<option value="{{ p.name }}">{% endfor %}
    </datalist>
    <script>
    const INV_PRICES = { {% for p in products %}"{{ p.name }}": {{ p.price }},{% endfor %} };
    </script>
    <div style="display:grid;grid-template-columns:1fr 80px 110px 90px 36px;gap:.4rem;padding-bottom:.25rem">
      <div class="col-hdr">Item Name</div>
      <div class="col-hdr" style="text-align:center">Qty</div>
      <div class="col-hdr" style="text-align:center">Unit Price</div>
      <div class="col-hdr" style="text-align:right">Total</div>
      <div></div>
    </div>
    <div id="items-wrap"></div>
    <button type="button" class="add-btn" onclick="addRow()">+ Add Item</button>
    <div class="subtotal-bar">
      Items Subtotal: <span id="items-sub">$0.00</span>
    </div>
    <input type="hidden" name="items_json" id="items_json_field">
    <input type="hidden" name="items_subtotal" id="items_subtotal_field">
  </div>

  <div class="card">
    <h2>Financials</h2>
    <div class="fg three">
      <div><label>Delivery Fee ($)</label><input name="delivery_fee" type="number" step="0.01" value="0" id="del_fee" oninput="recalc()"></div>
      <div><label>CT Sales Tax (6.35%)</label><input name="tax_amount" type="number" step="0.01" id="tax_amt" readonly style="background:#f9fafb"></div>
      <div><label>Grand Total ($)</label><input name="grand_total" type="number" step="0.01" id="grand_total" style="font-weight:700;background:#f0fff4" readonly></div>
      <div><label>Amount Paid ($)</label><input name="amount_paid" type="number" step="0.01" value="0" id="amt_paid" oninput="recalc()"></div>
      <div><label>Balance Due</label><input type="text" id="bal_due" readonly style="background:#fff5f5;font-weight:700;color:#dc2626"></div>
      <div><label>Tax Exempt?</label>
        <select name="tax_exempt" onchange="recalc()">
          <option value="0">No — Apply 6.35% CT Tax</option>
          <option value="1">Yes — Tax Exempt</option>
        </select>
      </div>
    </div>
    <input type="hidden" name="tax_rate" value="0.0635">
  </div>

  <div class="card">
    <h2>Notes</h2>
    <div class="fg one"><textarea name="notes" placeholder="Source, special instructions, Booqable reference #, etc."></textarea></div>
  </div>

  <div class="actions">
    <button type="submit" class="btn btn-save" onclick="prepSubmit()">💾 Create Booking</button>
    <a href="/admin/dashboard" class="btn btn-cancel">Cancel</a>
  </div>
</form>
</div>

<script>
let rowCount = 0;

function addRow(name='', qty=1, price=0) {
  rowCount++;
  const wrap = document.getElementById('items-wrap');
  const div = document.createElement('div');
  div.className = 'item-row';
  div.id = 'row' + rowCount;
  const rc = rowCount;
  div.innerHTML = `
    <input type="text" list="inv-list" placeholder="Type item name…" id="rn${rc}" value="${name}" oninput="onNameChange(${rc})">
    <input type="number" min="1" value="${qty}" id="rq${rc}" oninput="onQtyChange(${rc})" style="text-align:center">
    <input type="number" step="0.01" value="${price.toFixed(2)}" id="rp${rc}" oninput="recalc()">
    <div class="item-total" id="rt${rc}">$0.00</div>
    <button type="button" class="del-btn" onclick="delRow(${rc})">×</button>
  `;
  wrap.appendChild(div);
  recalc();
}

function onNameChange(rc) {
  const name = document.getElementById('rn'+rc).value;
  if (INV_PRICES[name] !== undefined) {
    document.getElementById('rp'+rc).value = INV_PRICES[name].toFixed(2);
  }
  recalc();
}

function onQtyChange(rc) { recalc(); }

function delRow(rc) {
  const el = document.getElementById('row'+rc);
  if (el) el.remove();
  recalc();
}

function recalc() {
  let sub = 0;
  document.querySelectorAll('.item-row').forEach(row => {
    const rc = row.id.replace('row','');
    const qty = parseFloat(document.getElementById('rq'+rc)?.value || 0);
    const price = parseFloat(document.getElementById('rp'+rc)?.value || 0);
    const tot = qty * price;
    sub += tot;
    const totEl = document.getElementById('rt'+rc);
    if (totEl) totEl.textContent = '$' + tot.toFixed(2);
  });
  document.getElementById('items-sub').textContent = '$' + sub.toFixed(2);
  document.getElementById('items_subtotal_field').value = sub.toFixed(2);
  const delFee = parseFloat(document.getElementById('del_fee').value || 0);
  const taxExempt = document.querySelector('[name=tax_exempt]').value === '1';
  const taxable = sub + delFee;
  const tax = taxExempt ? 0 : Math.round(taxable * 0.0635 * 100) / 100;
  document.getElementById('tax_amt').value = tax.toFixed(2);
  const grand = taxable + tax;
  document.getElementById('grand_total').value = grand.toFixed(2);
  const paid = parseFloat(document.getElementById('amt_paid').value || 0);
  const bal = Math.max(0, grand - paid);
  document.getElementById('bal_due').value = '$' + bal.toFixed(2);
}

function prepSubmit() {
  const items = [];
  document.querySelectorAll('.item-row').forEach(row => {
    const rc = row.id.replace('row','');
    const name = (document.getElementById('rn'+rc)?.value || '').trim();
    const qty = parseInt(document.getElementById('rq'+rc)?.value || 0);
    const price = parseFloat(document.getElementById('rp'+rc)?.value || 0);
    if (name && qty > 0) items.push({name, qty, unit_price: price, total: Math.round(qty*price*100)/100});
  });
  document.getElementById('items_json_field').value = JSON.stringify(items);
  // un-readonly grand_total and tax so they submit
  document.getElementById('grand_total').removeAttribute('readonly');
  document.getElementById('tax_amt').removeAttribute('readonly');
}

// Start with two blank rows
addRow(); addRow();
</script>
</body></html>
"""


ADMIN_BOOKING_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <link rel="manifest" href="/manifest.json">
  <meta name="theme-color" content="#2563eb">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="default">
  <meta name="apple-mobile-web-app-title" content="Rent a Party">
  <link rel="apple-touch-icon" href="/icon-192.png">
  <script>if("serviceWorker"in navigator)navigator.serviceWorker.register("/sw.js");</script>
  <title>Booking #{{ b.id }} — {{ business_name }}</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:-apple-system,sans-serif;background:#f0f4f8;color:#1a202c;min-height:100vh}
    header{background:linear-gradient(135deg,#1a365d,#2b6cb0);color:white;padding:1.25rem 2rem;display:flex;justify-content:space-between;align-items:center}
    header h1{font-size:1.2rem}
    .container{max-width:800px;margin:0 auto;padding:1.5rem 1rem}
    .card{background:white;border-radius:12px;box-shadow:0 2px 12px rgba(0,0,0,.08);padding:1.5rem;margin-bottom:1.5rem}
    .card h2{font-size:.95rem;font-weight:700;color:#2b6cb0;border-bottom:2px solid #ebf4ff;padding-bottom:.5rem;margin-bottom:1rem;text-transform:uppercase;letter-spacing:.4px}
    .row{display:grid;grid-template-columns:160px 1fr;gap:.5rem .75rem;font-size:.92rem}
    .row .k{color:#718096;font-size:.85rem}
    .row .v{font-weight:500}
    .badge{display:inline-block;padding:.3rem .8rem;border-radius:20px;font-size:.82rem;font-weight:700;text-transform:uppercase;margin-bottom:1rem}
    .badge-pending{background:#fefcbf;color:#975a16}
    .badge-accepted{background:#bee3f8;color:#2c5282}
    .badge-confirmed{background:#c6f6d5;color:#276749}
    .badge-denied{background:#fbd38d;color:#744210}
    .badge-cancelled{background:#fed7d7;color:#9b2c2c}
    table{width:100%;border-collapse:collapse;font-size:.9rem}
    th{padding:8px 10px;text-align:left;color:#718096;font-size:.78rem;text-transform:uppercase;border-bottom:1px solid #e2e8f0}
    td{padding:8px 10px;border-bottom:1px solid #f0f4f8}
    .total-row{font-weight:700;background:#1a365d;color:white}
    .total-row td{padding:10px}
    .actions{display:flex;gap:.75rem;flex-wrap:wrap;margin-top:1.5rem}
    .btn{padding:.65rem 1.25rem;border-radius:8px;font-size:.9rem;font-weight:600;cursor:pointer;border:none;text-decoration:none;display:inline-block}
    .btn-back{background:#f0f4f8;color:#4a5568}
    .btn-accept{background:#38a169;color:white}
    .btn-deny{background:#e53e3e;color:white}
    .btn-confirm{background:#3182ce;color:white}
    .btn-cancel{background:#718096;color:white}
    .btn-reminder{background:linear-gradient(135deg,#c05621,#dd6b20);color:white}
    .payment-link-box{background:#f0fff4;border:2px solid #38a169;border-radius:10px;padding:1.1rem 1.25rem;margin-bottom:1rem}
    .alert{background:#fffaf0;border-left:4px solid #ed8936;padding:.85rem 1rem;border-radius:0 8px 8px 0;font-size:.9rem;margin-bottom:1rem}
    a{color:#2b6cb0}
  </style>
</head>
<body>
<header>
  <h1>Booking #{{ b.id }}</h1>
  <div style="display:flex;gap:.75rem;align-items:center">
    <a href="/admin/booking/{{ b.id }}/edit" style="background:rgba(255,255,255,.15);color:white;text-decoration:none;font-size:.85rem;font-weight:600;padding:.4rem .9rem;border-radius:7px;border:1px solid rgba(255,255,255,.3)">✏️ Edit Booking</a>
    <a href="/admin/dashboard" style="color:white;text-decoration:none;font-size:.9rem">Back to Dashboard</a>
  </div>
</header>
<div class="container">

  <span class="badge badge-{{ b.status }}">{{ b.status|upper }}</span>
  <div style="font-size:.8rem;color:#718096;margin-bottom:1rem">Received: {{ b.created_at }}</div>

  {% if b.status == 'accepted' %}
  <div class="payment-link-box">
    <div style="font-weight:700;color:#276749;margin-bottom:.4rem">Awaiting Deposit Payment</div>
    {% if b.stripe_payment_link %}
    <p style="font-size:.9rem;color:#4a5568;margin-bottom:.5rem">Payment link sent to {{ b.email }}:</p>
    <a href="{{ b.stripe_payment_link }}" target="_blank" style="word-break:break-all;font-size:.85rem">{{ b.stripe_payment_link }}</a>
    {% else %}
    <p style="font-size:.9rem;color:#744210">No payment link generated. Use the Mark as Paid button below once payment is received.</p>
    {% endif %}
  </div>
  {% endif %}

  {% if booking_inv_issues %}
  <div style="background:#fef2f2;border:2px solid #f87171;border-radius:10px;padding:1rem 1.25rem;margin-bottom:1rem">
    <div style="font-weight:700;color:#dc2626;font-size:1rem;margin-bottom:.5rem">⚠️ Inventory Shortage — Review Before Accepting</div>
    {% for c in booking_inv_issues %}
    <div style="font-size:.9rem;color:#7f1d1d;margin-bottom:.3rem">
      <strong>{{ c.item }}</strong>: customer needs <strong>{{ c.needed }}</strong>, only <strong>{{ c.available }}</strong> available after other bookings
      <span style="background:#fee2e2;color:#b91c1c;border-radius:4px;padding:.1rem .45rem;font-size:.78rem;font-weight:700;margin-left:.4rem">{{ c.shortfall }} short</span>
    </div>
    {% endfor %}
    <div style="font-size:.82rem;color:#991b1b;margin-top:.6rem">Other confirmed bookings on these dates are using the remaining inventory. You may need to source more or contact the customer.</div>
  </div>
  {% endif %}

  {% if b.status == 'pending' %}
  <div class="alert">
    This booking is waiting for your review. Click Accept to send the customer their invoice, contract, and Stripe payment link.
    Click Deny to send a polite rejection.
  </div>
  {% endif %}

  {% if matched_customer %}
  {% set mc = matched_customer %}
  <div style="background:#eff6ff;border:1px solid #93c5fd;border-radius:10px;padding:1rem 1.25rem;margin-bottom:1rem">
    <div style="font-weight:700;color:#1e40af;margin-bottom:.4rem">🔗 Existing Customer Profile Found</div>
    <div style="font-size:.88rem;color:#1e3a8a;margin-bottom:.75rem">
      A customer profile matches this booking's name: <strong>{{ mc.full_name }}</strong><br>
      Profile email: {{ mc.email or '—' }} &nbsp;|&nbsp; Profile phone: {{ mc.phone or '—' }}
    </div>
    <div style="display:flex;flex-wrap:wrap;gap:.5rem">
      {% if mc.email != b.email or mc.phone != b.phone %}
      <form method="POST" action="/admin/booking/{{ b.id }}/sync-customer-profile">
        <input type="hidden" name="action" value="update_profile">
        <button style="background:#2563eb;color:white;border:none;border-radius:6px;padding:.35rem .85rem;font-size:.82rem;font-weight:700;cursor:pointer">
          ↑ Update Profile with Booking Info
        </button>
      </form>
      <form method="POST" action="/admin/booking/{{ b.id }}/sync-customer-profile">
        <input type="hidden" name="action" value="update_booking">
        <button style="background:#f0fdf4;color:#166534;border:1px solid #86efac;border-radius:6px;padding:.35rem .85rem;font-size:.82rem;font-weight:700;cursor:pointer">
          ↓ Fill Booking from Profile
        </button>
      </form>
      {% else %}
      <span style="font-size:.85rem;color:#166534;font-weight:600">✅ Profile info matches — no update needed</span>
      {% endif %}
      <a href="/admin/customers/{{ mc.id }}" style="background:white;color:#374151;border:1px solid #d1d5db;border-radius:6px;padding:.35rem .85rem;font-size:.82rem;font-weight:600;text-decoration:none">
        View Profile →
      </a>
    </div>
  </div>
  {% endif %}

  <div class="card">
    <h2>Customer</h2>
    <div class="row">
      <span class="k">Name</span><span class="v">{{ b.full_name or '—' }}</span>
      {% if b.company_name and b.company_name != 'None' %}<span class="k">Company</span><span class="v">{{ b.company_name }}</span>{% endif %}
      <span class="k">Address</span>
      <span class="v">
        <form method="POST" action="/admin/booking/{{ b.id }}/update-address" style="display:flex;flex-wrap:wrap;gap:.4rem;align-items:center;margin:0">
          <input name="renter_street" value="{{ b.renter_street if (b.renter_street and b.renter_street != 'None') else '' }}" placeholder="Street"
                 style="border:1px solid #d1d5db;border-radius:5px;padding:.25rem .5rem;font-size:.88rem;width:180px">
          <input name="renter_city" value="{{ b.renter_city if (b.renter_city and b.renter_city != 'None') else '' }}" placeholder="City"
                 style="border:1px solid #d1d5db;border-radius:5px;padding:.25rem .5rem;font-size:.88rem;width:120px">
          <input name="renter_state" value="{{ b.renter_state if (b.renter_state and b.renter_state != 'None') else '' }}" placeholder="ST"
                 style="border:1px solid #d1d5db;border-radius:5px;padding:.25rem .5rem;font-size:.88rem;width:50px">
          <input name="renter_zip" value="{{ b.renter_zip if (b.renter_zip and b.renter_zip != 'None') else '' }}" placeholder="ZIP"
                 style="border:1px solid #d1d5db;border-radius:5px;padding:.25rem .5rem;font-size:.88rem;width:75px">
          <button type="submit" style="background:#2563eb;color:white;border:none;border-radius:5px;padding:.25rem .6rem;font-size:.8rem;font-weight:600;cursor:pointer">Save</button>
        </form>
      </span>
      {% set _phone = b.phone if (b.phone and b.phone != 'None') else '' %}
      <span class="k">Phone</span>
      <span class="v">
        <form method="POST" action="/admin/booking/{{ b.id }}/update-phone" style="display:inline-flex;align-items:center;gap:.4rem;margin:0">
          <input type="tel" name="phone" value="{{ _phone }}" placeholder="(555) 000-0000"
                 style="border:1px solid #d1d5db;border-radius:5px;padding:.25rem .5rem;font-size:.88rem;width:160px">
          <button type="submit" style="background:#2563eb;color:white;border:none;border-radius:5px;padding:.25rem .6rem;font-size:.8rem;font-weight:600;cursor:pointer">Save</button>
        </form>
      </span>
      <span class="k">Email</span><span class="v">{% if b.email %}<a href="mailto:{{ b.email }}">{{ b.email }}</a>{% else %}—{% endif %}</span>
    </div>
  </div>

  <div class="card">
    <h2>Event</h2>
    {% if weekend_residential %}
    <div style="background:#fef3c7;border:1px solid #f59e0b;border-radius:8px;padding:.85rem 1rem;margin-bottom:1rem;display:flex;flex-wrap:wrap;align-items:center;gap:.75rem">
      <div style="flex:1;min-width:200px">
        <div style="font-weight:700;color:#92400e;margin-bottom:.2rem">🏠 Weekend Residential Event</div>
        <div style="font-size:.85rem;color:#78350f">
          {{ weekend_residential.day_label }} event detected. Apply standard weekend schedule:<br>
          <strong>Delivery:</strong> {{ weekend_residential.delivery_label }} &nbsp;|&nbsp; <strong>Pickup:</strong> {{ weekend_residential.pickup_label }}
        </div>
      </div>
      <form method="POST" action="/admin/booking/{{ b.id }}/apply-weekend-schedule" style="margin:0">
        <button type="submit" style="background:#d97706;color:white;border:none;border-radius:7px;padding:.55rem 1.1rem;font-size:.88rem;font-weight:700;cursor:pointer;white-space:nowrap">
          📅 Apply Weekend Schedule
        </button>
      </form>
    </div>
    {% endif %}
    <div class="row">
      <span class="k">Dates</span><span class="v">{{ b.event_start_date.strftime('%m/%d/%Y') if b.event_start_date else '' }} - {{ b.event_end_date.strftime('%m/%d/%Y') if b.event_end_date else '' }}</span>
      <span class="k">Event Start Time</span><span class="v">{{ b.event_start_time }}</span>
      <span class="k">Pickup Time</span><span class="v">{{ b.event_end_time }}</span>
      <span class="k">Delivery Time</span><span class="v">{{ b.setup_time }}</span>
      <span class="k">Venue Type</span><span class="v" style="text-transform:capitalize">{{ b.venue_type }}</span>
      {% if b.venue_latest_pickup %}<span class="k">Latest Pickup</span><span class="v">{{ b.venue_latest_pickup }}</span>{% endif %}
      <span class="k">Event Address</span><span class="v">{{ b.event_street }}, {{ b.event_city }}, {{ b.event_state }} {{ b.event_zip }}</span>
      <span class="k">Deliver To</span><span class="v">{{ b.delivery_location }}</span>
    </div>
    <div style="background:#f0f9ff;border-left:3px solid #38bdf8;padding:.6rem .9rem;margin-top:.9rem;border-radius:0 6px 6px 0;font-size:.82rem;color:#0c4a6e">
      ℹ️ <strong>Delivery times are approximate</strong> unless the customer has opted for exact-time delivery/pickup.
    </div>

    <!-- Booking Calendar -->
    <div style="margin-top:1.25rem">
      <div style="font-size:.72rem;font-weight:700;text-transform:uppercase;letter-spacing:.07em;color:#6b7280;margin-bottom:.75rem">📅 Confirmed Bookings Calendar</div>
      <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:.5rem">
        <button onclick="calPrev()" style="background:none;border:1px solid #d1d5db;border-radius:6px;padding:.25rem .65rem;cursor:pointer;font-size:.9rem;color:#374151">‹</button>
        <span id="cal-title" style="font-weight:700;font-size:.9rem;color:#1a202c"></span>
        <button onclick="calNext()" style="background:none;border:1px solid #d1d5db;border-radius:6px;padding:.25rem .65rem;cursor:pointer;font-size:.9rem;color:#374151">›</button>
      </div>
      <div id="cal-grid" style="display:grid;grid-template-columns:repeat(7,1fr);gap:2px;font-size:.78rem"></div>
      <div style="display:flex;flex-wrap:wrap;gap:.6rem;margin-top:.75rem;font-size:.75rem">
        <span style="display:flex;align-items:center;gap:.3rem"><span style="width:12px;height:12px;border-radius:3px;background:#fef3c7;border:1px solid #f59e0b;display:inline-block"></span>This booking</span>
        <span style="display:flex;align-items:center;gap:.3rem"><span style="width:12px;height:12px;border-radius:3px;background:#dcfce7;border:1px solid #86efac;display:inline-block"></span>Confirmed</span>
        <span style="display:flex;align-items:center;gap:.3rem"><span style="width:12px;height:12px;border-radius:3px;background:#dbeafe;border:1px solid #93c5fd;display:inline-block"></span>Accepted</span>
      </div>
    </div>

    <script>
    (function(){
      const CAL_BOOKINGS = {{ cal_bookings | tojson }};
      const THIS_START   = "{{ b.event_start_date or '' }}".slice(0,10);
      const THIS_END     = "{{ b.event_end_date or '' }}".slice(0,10);
      const THIS_ID      = {{ b.id }};

      // Start calendar at this booking's month
      let calYear, calMonth;
      if(THIS_START){
        const d=new Date(THIS_START+'T00:00:00');
        calYear=d.getFullYear(); calMonth=d.getMonth();
      } else {
        const now=new Date();
        calYear=now.getFullYear(); calMonth=now.getMonth();
      }

      const MONTHS=['January','February','March','April','May','June',
                    'July','August','September','October','November','December'];
      const DAYS=['Su','Mo','Tu','We','Th','Fr','Sa'];

      function dateStr(y,m,d){ return y+'-'+(String(m+1).padStart(2,'0'))+'-'+(String(d).padStart(2,'0')); }
      function inRange(ds, start, end){ return ds>=start && ds<=end; }

      function render(){
        document.getElementById('cal-title').textContent=MONTHS[calMonth]+' '+calYear;
        const grid=document.getElementById('cal-grid');
        grid.innerHTML='';
        // Day headers
        DAYS.forEach(d=>{
          const h=document.createElement('div');
          h.textContent=d;
          h.style.cssText='text-align:center;font-weight:700;color:#9ca3af;padding:4px 2px;font-size:.7rem';
          grid.appendChild(h);
        });
        const firstDay=new Date(calYear,calMonth,1).getDay();
        const daysInMonth=new Date(calYear,calMonth+1,0).getDate();
        // Empty cells before first day
        for(let i=0;i<firstDay;i++){
          const e=document.createElement('div'); grid.appendChild(e);
        }
        for(let d=1;d<=daysInMonth;d++){
          const ds=dateStr(calYear,calMonth,d);
          const cell=document.createElement('div');
          cell.textContent=d;
          let bg='transparent', border='transparent', color='#374151', fw='400';

          // Check if this day falls in THIS booking's range
          const isThis=THIS_START&&THIS_END&&inRange(ds,THIS_START,THIS_END);
          if(isThis){ bg='#fef3c7'; border='#f59e0b'; fw='700'; }

          // Check confirmed/accepted bookings (others)
          let tip='';
          CAL_BOOKINGS.forEach(bk=>{
            if(bk.id===THIS_ID) return;
            if(bk.start&&bk.end&&inRange(ds,bk.start,bk.end)){
              if(!isThis){
                bg=bk.status==='confirmed'?'#dcfce7':'#dbeafe';
                border=bk.status==='confirmed'?'#86efac':'#93c5fd';
              } else {
                // Overlap — show red ring
                border='#f87171';
              }
              fw='700';
              tip+=(tip?', ':'')+bk.name+' #'+bk.id;
            }
          });

          cell.style.cssText=`text-align:center;padding:5px 2px;border-radius:5px;cursor:default;font-weight:${fw};color:${color};background:${bg};border:1.5px solid ${border};font-size:.78rem;line-height:1.4;min-height:24px`;
          if(tip) cell.title=tip;
          grid.appendChild(cell);
        }
      }

      window.calPrev=function(){ calMonth--; if(calMonth<0){calMonth=11;calYear--;} render(); };
      window.calNext=function(){ calMonth++; if(calMonth>11){calMonth=0;calYear++;} render(); };
      render();
    })();
    </script>
  </div>

  <div class="card">
    <h2>Items & Totals</h2>
    <table>
      <thead><tr><th>Item</th><th style="text-align:center">Qty</th><th style="text-align:right">Unit</th><th style="text-align:right">Total</th></tr></thead>
      <tbody>
        {% for item in items %}
        <tr><td>{{ item.name }}</td><td style="text-align:center">{{ item.qty }}</td><td style="text-align:right">${{ "%.2f"|format((item.unit_price or 0)|float) }}</td><td style="text-align:right;font-weight:600">${{ "%.2f"|format((item.total or 0)|float) }}</td></tr>
        {% endfor %}
        {% if b.exact_time_delivery %}
        <tr><td colspan="3">Exact Time Delivery</td><td style="text-align:right;font-weight:600">$175.00</td></tr>
        {% endif %}
        <tr><td colspan="3">Delivery Fee ({{ b.distance_miles or '?' }} mi)</td><td style="text-align:right;font-weight:600">${{ "%.2f"|format(b.delivery_fee or 0) }}</td></tr>
        {% if (b.discount_amount or 0)|float > 0 %}
        <tr style="background:#f0fdf4">
          <td colspan="3" style="color:#16a34a;font-weight:600">
            🏷️ Discount
            {% if b.discount_type == 'percent' %}({{ b.discount_value|float|round(1) }}% off)
            {% else %}(${{ "%.2f"|format(b.discount_value|float) }} off){% endif %}
          </td>
          <td style="text-align:right;font-weight:600;color:#16a34a">- ${{ "%.2f"|format(b.discount_amount|float) }}</td>
        </tr>
        {% endif %}
        {% if b.tax_exempt %}
        <tr style="background:#f0fff4"><td colspan="3" style="color:#276749">CT Sales Tax <span style="font-size:.78rem;background:#c6f6d5;color:#276749;border-radius:4px;padding:.1rem .4rem;margin-left:.4rem">TAX EXEMPT</span></td><td style="text-align:right;color:#276749">$0.00</td></tr>
        {% elif b.tax_amount %}
        <tr><td colspan="3" style="color:#718096">CT Sales Tax ({{ "%.2f"|format((b.tax_rate or 0)*100) }}%)</td><td style="text-align:right;font-weight:600">${{ "%.2f"|format(b.tax_amount or 0) }}</td></tr>
        {% endif %}
        <tr class="total-row"><td colspan="3">GRAND TOTAL</td><td style="text-align:right">${{ "%.2f"|format(b.grand_total or 0) }}</td></tr>
        {% set paid = (b.amount_paid or 0)|float %}
        {% set total = (b.grand_total or 0)|float %}
        {% set balance = [total - paid, 0]|max %}
        {% if paid > 0 %}
        <tr style="background:#f0fff4">
          <td colspan="3" style="color:#276749;font-weight:700">✅ Amount Paid</td>
          <td style="text-align:right;font-weight:700;color:#276749">- ${{ "%.2f"|format(paid) }}</td>
        </tr>
        {% if balance > 0.01 %}
        <tr style="background:#fff5f5">
          <td colspan="3" style="color:#c53030;font-weight:700">⚠️ Balance Due</td>
          <td style="text-align:right;font-weight:700;color:#c53030">${{ "%.2f"|format(balance) }}</td>
        </tr>
        {% else %}
        <tr style="background:#f0fff4">
          <td colspan="4" style="color:#276749;font-weight:700;text-align:center">✅ Paid In Full</td>
        </tr>
        {% endif %}
        {% elif b.status == 'confirmed' %}
        <tr style="background:#f0fff4">
          <td colspan="4" style="color:#276749;font-weight:700;text-align:center">✅ Paid In Full</td>
        </tr>
        {% elif b.status == 'accepted' %}
        <tr style="background:#fffbeb">
          <td colspan="3" style="color:#92400e;font-weight:700">⏳ Balance Due</td>
          <td style="text-align:right;font-weight:700;color:#92400e">${{ "%.2f"|format(total) }}</td>
        </tr>
        {% endif %}
      </tbody>
    </table>
  </div>

  <!-- ── Edit Items ── -->
  <datalist id="inv-list">
    {% for p in products %}<option value="{{ p.name }}">{% endfor %}
  </datalist>
  <div class="card">
    <h2>Edit Items</h2>
    <form method="POST" action="/admin/booking/{{ b.id }}/update-items">
      <!-- Header labels -->
      <div style="display:flex;gap:.5rem;margin-bottom:.25rem;font-size:.75rem;font-weight:700;color:#6b7280;text-transform:uppercase;letter-spacing:.04em">
        <span style="flex:1;padding-left:.65rem">Item Name</span>
        <span style="width:62px;text-align:center">Qty</span>
        <span style="width:90px;text-align:center">Unit Price</span>
        <span style="width:30px"></span>
      </div>
      <div id="items-editor" style="display:flex;flex-direction:column;gap:.5rem;margin-bottom:.75rem">
        {% for item in items %}
        <div class="item-row" style="display:flex;gap:.5rem;align-items:center">
          <input type="text" name="item_name" value="{{ item.name }}" list="inv-list"
                 placeholder="Type to search inventory…"
                 style="flex:1;border:1px solid #d1d5db;border-radius:6px;padding:.4rem .65rem;font-size:.9rem">
          <input type="number" name="item_qty" value="{{ item.qty }}" min="1"
                 style="width:62px;border:1px solid #d1d5db;border-radius:6px;padding:.4rem .5rem;font-size:.9rem;text-align:center" title="Qty">
          <input type="number" name="item_price" value="{{ item.unit_price or 0 }}" min="0" step="0.01"
                 style="width:90px;border:1px solid #d1d5db;border-radius:6px;padding:.4rem .5rem;font-size:.9rem;text-align:center" placeholder="Price" title="Unit Price">
          <button type="button" onclick="this.closest('.item-row').remove()"
                  style="background:#fee2e2;color:#dc2626;border:none;border-radius:6px;padding:.4rem .65rem;font-size:.85rem;cursor:pointer;font-weight:700">✕</button>
        </div>
        {% endfor %}
      </div>

      <!-- Exact Time Delivery & Delivery Fee row -->
      <div style="display:flex;gap:1.25rem;flex-wrap:wrap;align-items:center;background:#f8fafc;border:1px solid #e2e8f0;border-radius:8px;padding:.65rem 1rem;margin-bottom:.75rem">
        <label style="display:flex;align-items:center;gap:.45rem;font-size:.88rem;font-weight:600;color:#374151;cursor:pointer">
          <input type="checkbox" name="exact_time_delivery" value="1"
                 {% if b.exact_time_delivery %}checked{% endif %}
                 style="width:16px;height:16px;accent-color:#2563eb">
          Exact Time Delivery <span style="color:#6b7280;font-weight:400">(+$175.00)</span>
        </label>
        <label style="display:flex;align-items:center;gap:.45rem;font-size:.88rem;font-weight:600;color:#374151">
          Delivery Fee ($)
          <input type="number" name="delivery_fee" value="{{ b.delivery_fee or 0 }}" min="0" step="0.01"
                 style="width:90px;border:1px solid #d1d5db;border-radius:6px;padding:.35rem .5rem;font-size:.9rem;text-align:center">
        </label>
      </div>

      <div style="display:flex;gap:.5rem;flex-wrap:wrap">
        <button type="button" id="add-item-btn"
                style="background:#eff6ff;color:#2563eb;border:1px solid #bfdbfe;border-radius:6px;padding:.45rem 1rem;font-size:.85rem;font-weight:600;cursor:pointer">+ Add Item</button>
        <button type="submit"
                style="background:#16a34a;color:white;border:none;border-radius:6px;padding:.45rem 1.1rem;font-size:.85rem;font-weight:600;cursor:pointer">💾 Save &amp; Recalculate</button>
      </div>
      <p style="font-size:.78rem;color:#6b7280;margin-top:.5rem;margin-bottom:0">Totals, tax, and grand total are automatically recalculated on save.</p>
    </form>
  </div>
  <script>
  // Price lookup map from inventory
  var _invPrices = {};
  {% for p in products %}_invPrices[{{ p.name|tojson }}] = {{ p.price|float }};{% endfor %}

  function makePriceInput(val) {
    var p = document.createElement('input');
    p.type = 'number'; p.name = 'item_price'; p.min = '0'; p.step = '0.01';
    p.value = val || '0'; p.placeholder = 'Price'; p.title = 'Unit Price';
    p.style.cssText = 'width:80px;border:1px solid #d1d5db;border-radius:6px;padding:.4rem .5rem;font-size:.9rem;text-align:center';
    return p;
  }

  document.getElementById('items-editor').addEventListener('change', function(e) {
    if (e.target.name === 'item_name') {
      var row = e.target.closest('.item-row');
      if (!row) return;
      var priceInput = row.querySelector('input[name="item_price"]');
      var price = _invPrices[e.target.value];
      if (priceInput && price !== undefined && parseFloat(priceInput.value) === 0) {
        priceInput.value = price.toFixed(2);
      }
    }
  });

  document.getElementById('add-item-btn').addEventListener('click', function() {
    var editor = document.getElementById('items-editor');
    var row = document.createElement('div');
    row.className = 'item-row';
    row.style.cssText = 'display:flex;gap:.5rem;align-items:center';
    var nameInput = document.createElement('input');
    nameInput.type = 'text'; nameInput.name = 'item_name';
    nameInput.setAttribute('list', 'inv-list');
    nameInput.placeholder = 'Type to search inventory…';
    nameInput.style.cssText = 'flex:1;border:1px solid #d1d5db;border-radius:6px;padding:.4rem .65rem;font-size:.9rem';
    var qtyInput = document.createElement('input');
    qtyInput.type = 'number'; qtyInput.name = 'item_qty'; qtyInput.value = '1'; qtyInput.min = '1';
    qtyInput.style.cssText = 'width:62px;border:1px solid #d1d5db;border-radius:6px;padding:.4rem .5rem;font-size:.9rem;text-align:center';
    qtyInput.title = 'Qty';
    var priceInput = makePriceInput(0);
    nameInput.addEventListener('change', function() {
      var price = _invPrices[nameInput.value];
      if (price !== undefined && parseFloat(priceInput.value) === 0) {
        priceInput.value = price.toFixed(2);
      }
    });
    var removeBtn = document.createElement('button');
    removeBtn.type = 'button'; removeBtn.textContent = '✕';
    removeBtn.style.cssText = 'background:#fee2e2;color:#dc2626;border:none;border-radius:6px;padding:.4rem .65rem;font-size:.85rem;cursor:pointer;font-weight:700';
    removeBtn.addEventListener('click', function() { row.remove(); });
    row.appendChild(nameInput); row.appendChild(qtyInput); row.appendChild(priceInput); row.appendChild(removeBtn);
    editor.appendChild(row);
    nameInput.focus();
  });
  </script>

  {% if b.notes %}
  <div class="card"><h2>Notes</h2><p style="color:#4a5568;line-height:1.6">{{ b.notes }}</p></div>
  {% endif %}

  <!-- ── Discount ── -->
  <div class="card" style="border:2px solid #bbf7d0;background:#f0fdf4">
    <h2 style="color:#166534">🏷️ Discount</h2>
    {% set disc_amt    = (b.discount_amount or 0)|float %}
    {% set subtotal    = (b.items_subtotal or 0)|float %}
    {% set del_fee     = (b.delivery_fee or 0)|float %}
    {% set exact_fee   = 175.0 if b.exact_time_delivery else 0.0 %}
    {% set tax_amt     = (b.tax_amount or 0)|float %}
    {% set grand_total = (b.grand_total or 0)|float %}
    {% set pre_disc    = subtotal + del_fee + exact_fee %}
    {% if disc_amt > 0 %}
    <div style="background:#dcfce7;border:1px solid #86efac;border-radius:8px;padding:.65rem 1rem;margin-bottom:.75rem;font-size:.92rem;color:#166534;font-weight:600">
      ✅ Discount applied:
      {% if b.discount_type == 'percent' %}
        {{ b.discount_value|float|round(1) }}% off
      {% else %}
        ${{ "%.2f"|format(b.discount_value|float) }} off
      {% endif %}
      — saves customer <strong>${{ "%.2f"|format(disc_amt) }}</strong>
    </div>
    {% endif %}
    <!-- Totals summary -->
    <div style="background:white;border:1px solid #d1fae5;border-radius:8px;padding:.65rem 1rem;margin-bottom:.85rem;font-size:.88rem">
      <table style="width:100%;border-collapse:collapse">
        <tr>
          <td style="padding:.25rem .4rem;color:#4b5563">Items Subtotal</td>
          <td style="padding:.25rem .4rem;text-align:right;color:#4b5563">${{ "%.2f"|format(subtotal) }}</td>
        </tr>
        {% if del_fee > 0 %}
        <tr>
          <td style="padding:.25rem .4rem;color:#4b5563">Delivery Fee</td>
          <td style="padding:.25rem .4rem;text-align:right;color:#4b5563">${{ "%.2f"|format(del_fee) }}</td>
        </tr>
        {% endif %}
        {% if b.exact_time_delivery %}
        <tr>
          <td style="padding:.25rem .4rem;color:#4b5563">Exact Time Delivery</td>
          <td style="padding:.25rem .4rem;text-align:right;color:#4b5563">$175.00</td>
        </tr>
        {% endif %}
        {% if disc_amt > 0 %}
        <tr style="border-top:1px dashed #d1d5db">
          <td style="padding:.35rem .4rem;color:#374151;font-weight:600">Total Before Discount</td>
          <td style="padding:.35rem .4rem;text-align:right;color:#374151;font-weight:600">${{ "%.2f"|format(subtotal + del_fee + exact_fee) }}</td>
        </tr>
        <tr>
          <td style="padding:.25rem .4rem;color:#16a34a;font-weight:600">Discount</td>
          <td style="padding:.25rem .4rem;text-align:right;color:#16a34a;font-weight:600">- ${{ "%.2f"|format(disc_amt) }}</td>
        </tr>
        <tr>
          <td style="padding:.25rem .4rem;color:#374151;font-weight:600">Total After Discount</td>
          <td style="padding:.25rem .4rem;text-align:right;color:#374151;font-weight:600">${{ "%.2f"|format(subtotal + del_fee + exact_fee - disc_amt) }}</td>
        </tr>
        {% endif %}
        <tr>
          <td style="padding:.25rem .4rem;color:#4b5563">CT Sales Tax (6.35%)</td>
          <td style="padding:.25rem .4rem;text-align:right;color:#4b5563">${{ "%.2f"|format(tax_amt) }}</td>
        </tr>
        <tr style="border-top:2px solid #86efac">
          <td style="padding:.4rem .4rem 0;font-weight:800;font-size:1rem;color:#166534">Grand Total</td>
          <td style="padding:.4rem .4rem 0;text-align:right;font-weight:800;font-size:1rem;color:#166534">${{ "%.2f"|format(grand_total) }}</td>
        </tr>
      </table>
    </div>
    <form method="POST" action="/admin/booking/{{ b.id }}/apply-discount">
      <div style="display:flex;flex-wrap:wrap;gap:.75rem;align-items:flex-end">
        <div>
          <label style="font-size:.82rem;font-weight:600;color:#374151;display:block;margin-bottom:.3rem">Discount Type</label>
          <select name="discount_type" style="border:1px solid #d1d5db;border-radius:7px;padding:.45rem .7rem;font-size:.9rem;background:white">
            <option value="amount" {% if b.discount_type == 'amount' %}selected{% endif %}>$ Fixed Amount</option>
            <option value="percent" {% if b.discount_type == 'percent' %}selected{% endif %}>% Percentage</option>
          </select>
        </div>
        <div>
          <label style="font-size:.82rem;font-weight:600;color:#374151;display:block;margin-bottom:.3rem">Value</label>
          <input type="number" name="discount_value" min="0" step="0.01"
            value="{{ b.discount_value|float if b.discount_value else '' }}"
            placeholder="e.g. 25"
            style="border:1px solid #d1d5db;border-radius:7px;padding:.45rem .7rem;font-size:.9rem;width:110px">
        </div>
        <button type="submit" style="background:#16a34a;color:white;border:none;border-radius:7px;padding:.5rem 1.2rem;font-size:.88rem;font-weight:700;cursor:pointer">Apply Discount</button>
        {% if disc_amt > 0 %}
        <a href="/admin/booking/{{ b.id }}/remove-discount" style="background:#fee2e2;color:#dc2626;border:1px solid #fca5a5;border-radius:7px;padding:.5rem 1rem;font-size:.88rem;font-weight:600;text-decoration:none">Remove</a>
        {% endif %}
      </div>
      <p style="font-size:.78rem;color:#6b7280;margin-top:.6rem;margin-bottom:0">Discount is applied to the full pre-tax total (items + delivery fees). Grand total is recalculated automatically.</p>
    </form>
  </div>

  <!-- ── Admin Private Notes ── -->
  <div class="card" style="border:2px solid #fde68a;background:#fffbeb">
    <h2 style="color:#92400e">🔒 Private Admin Notes</h2>
    <p style="font-size:.8rem;color:#a16207;margin-bottom:.75rem">Only visible to you — never shown to customers.</p>
    <form method="POST" action="/admin/booking/{{ b.id }}/admin-notes">
      <textarea name="admin_notes" rows="5" placeholder="Add your private notes here… follow-up reminders, customer preferences, payment history, anything…" style="width:100%;border:1px solid #fcd34d;border-radius:8px;padding:.65rem .85rem;font-size:.9rem;color:#1a202c;background:white;resize:vertical;line-height:1.6">{{ b.admin_notes or '' }}</textarea>
      <div style="display:flex;justify-content:flex-end;margin-top:.5rem">
        <button type="submit" style="background:#d97706;color:white;border:none;border-radius:7px;padding:.5rem 1.25rem;font-size:.88rem;font-weight:700;cursor:pointer">💾 Save Notes</button>
      </div>
    </form>
  </div>

  <!-- ── Payment Links History ── -->
  {% if payment_links %}
  <div class="card">
    <h2>Payment Links Sent</h2>
    <table style="width:100%;border-collapse:collapse;font-size:.88rem">
      <thead>
        <tr style="background:#f8fafc;text-align:left">
          <th style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0;color:#6b7280;font-weight:600">Label</th>
          <th style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0;color:#6b7280;font-weight:600">Amount</th>
          <th style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0;color:#6b7280;font-weight:600">Sent</th>
          <th style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0;color:#6b7280;font-weight:600">Status</th>
          <th style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0;color:#6b7280;font-weight:600">Link</th>
          <th style="padding:.5rem .75rem;border-bottom:1px solid #e2e8f0"></th>
        </tr>
      </thead>
      <tbody>
        {% for pl in payment_links %}
        <tr style="border-bottom:1px solid #f1f5f9">
          <td style="padding:.55rem .75rem;color:#1a202c;font-weight:500">{{ pl.label or '—' }}</td>
          <td style="padding:.55rem .75rem;font-weight:700;color:#1a202c">${{ "%.2f"|format(pl.amount or 0) }}</td>
          <td style="padding:.55rem .75rem;color:#6b7280;font-size:.82rem">{{ (pl.created_at or '')|string|truncate(16, True, '') }}</td>
          <td style="padding:.55rem .75rem">
            {% if pl.status == 'active' %}
            <span style="background:#dcfce7;color:#166534;font-size:.78rem;font-weight:700;padding:.2rem .55rem;border-radius:20px">Active</span>
            {% else %}
            <span style="background:#fee2e2;color:#991b1b;font-size:.78rem;font-weight:700;padding:.2rem .55rem;border-radius:20px">Cancelled</span>
            {% endif %}
          </td>
          <td style="padding:.55rem .75rem">
            {% if pl.url and pl.status == 'active' %}
            <a href="{{ pl.url }}" target="_blank" style="color:#2563eb;font-size:.82rem;word-break:break-all">Open ↗</a>
            {% else %}
            <span style="color:#9ca3af;font-size:.82rem">—</span>
            {% endif %}
          </td>
          <td style="padding:.55rem .75rem">
            {% if pl.status == 'active' %}
            <form method="POST" action="/admin/payment-link/{{ pl.id }}/cancel" style="margin:0">
              <button type="submit"
                      onclick="return confirm('Cancel this payment link? The customer will no longer be able to pay using it.')"
                      style="background:#fee2e2;color:#dc2626;border:none;border-radius:6px;padding:.3rem .75rem;font-size:.8rem;font-weight:600;cursor:pointer;white-space:nowrap">
                🚫 Cancel Link
              </button>
            </form>
            {% endif %}
          </td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
  {% endif %}

  <!-- ── Custom Stripe Payment Link ── -->
  {% if request.args.get('custom_link') %}
  <div style="background:#f0fdf4;border:2px solid #86efac;border-radius:10px;padding:1rem 1.25rem;margin-bottom:1rem">
    <div style="font-weight:700;color:#15803d;margin-bottom:.35rem">✅ Payment link created &amp; emailed to {{ b.email }}</div>
    <div style="font-size:.82rem;color:#6b7280;margin-bottom:.4rem">Copy this link to share it another way:</div>
    <div style="display:flex;gap:.5rem;align-items:center">
      <input id="custom-link-val" type="text" value="{{ request.args.get('custom_link') }}" readonly
             style="flex:1;border:1px solid #d1d5db;border-radius:6px;padding:.4rem .65rem;font-size:.82rem;background:#f9fafb;color:#374151">
      <button type="button" onclick="var i=document.getElementById('custom-link-val');i.select();document.execCommand('copy');this.textContent='Copied!';setTimeout(()=>this.textContent='Copy',1500)"
              style="background:#2563eb;color:white;border:none;border-radius:6px;padding:.4rem .9rem;font-size:.82rem;cursor:pointer;font-weight:600;white-space:nowrap">Copy</button>
    </div>
  </div>
  {% endif %}
  <div class="card">
    <h2>Send Custom Payment Link</h2>
    <p style="color:#6b7280;font-size:.88rem;margin-bottom:1rem">Create a Stripe payment link for any amount and email it directly to the customer.</p>
    <form method="POST" action="/admin/booking/{{ b.id }}/custom-stripe-link" style="display:flex;gap:.6rem;align-items:flex-end;flex-wrap:wrap">
      <div>
        <label style="display:block;font-size:.8rem;font-weight:600;color:#374151;margin-bottom:.3rem">Amount ($)</label>
        <input type="number" name="amount" min="0.50" step="0.01" placeholder="0.00" required
               style="width:130px;border:1px solid #d1d5db;border-radius:6px;padding:.45rem .65rem;font-size:1rem;font-weight:600">
      </div>
      <div>
        <label style="display:block;font-size:.8rem;font-weight:600;color:#374151;margin-bottom:.3rem">Label (optional)</label>
        <input type="text" name="label" placeholder="e.g. Deposit, Balance…"
               style="width:220px;border:1px solid #d1d5db;border-radius:6px;padding:.45rem .65rem;font-size:.9rem">
      </div>
      <button type="submit" style="background:#2563eb;color:white;border:none;border-radius:6px;padding:.5rem 1.25rem;font-size:.9rem;font-weight:700;cursor:pointer;height:38px">
        💳 Create &amp; Send Link
      </button>
    </form>
  </div>

  <div class="actions">
    <a href="/admin/dashboard" class="btn btn-back">Back to Dashboard</a>
    {% if b.status == 'pending' %}
    <form id="accept-form" method="POST" action="/admin/booking/{{ b.id }}/accept">
      <input type="hidden" name="custom_amount" id="accept-amount-input">
      <button type="button" class="btn btn-accept" id="accept-btn">
        Accept — Send Invoice & Payment Link
      </button>
    </form>
    <form method="POST" action="/admin/booking/{{ b.id }}/deny">
      <button class="btn btn-deny" onclick="return confirm('Deny this booking? This will send {{ b.email }} a rejection email.')">
        Deny — Send Rejection Email
      </button>
    </form>
    {% endif %}
    {% if b.status == 'accepted' %}
    <form method="POST" action="/admin/booking/{{ b.id }}/confirm">
      <button class="btn btn-confirm" onclick="return confirm('Manually mark this booking as paid/confirmed? Only do this if you have confirmed payment outside of Stripe.')">
        Mark as Paid (Manual)
      </button>
    </form>
    {% endif %}
    {% if b.status not in ('denied', 'cancelled') %}
    <form method="POST" action="/admin/booking/{{ b.id }}/cancel">
      <button class="btn btn-cancel" onclick="return confirm('Cancel booking #{{ b.id }}?')">Cancel Booking</button>
    </form>
    {% endif %}
    {% if b.status == 'confirmed' %}
    <form id="final-form" method="POST" action="/admin/booking/{{ b.id }}/send-final-reminder">
      <input type="hidden" name="custom_amount" id="final-amount-input">
      <button type="button" class="btn btn-reminder" id="final-btn">
        Send Final Payment Reminder
      </button>
    </form>
    {% endif %}
    {% if b.status in ('confirmed', 'accepted') %}
    <form method="POST" action="/admin/booking/{{ b.id }}/send-receipt"
          onsubmit="return confirm('Send a payment receipt to {{ b.email }}?')">
      <button class="btn" style="background:#f0fdf4;color:#166534;border:1px solid #86efac;font-weight:700">
        📄 Send Receipt to Customer
      </button>
    </form>
    {% endif %}
    {% if b.delivery_status != 'picked_up' %}
    <form method="POST" action="/admin/booking/{{ b.id }}/delivery-status">
      {% if not b.delivery_status %}
      <button class="btn" style="background:#fffbeb;color:#92400e;border:1px solid #fcd34d"
        onclick="return confirm('Mark this booking as DELIVERED?')">🚚 Mark as Delivered</button>
      {% elif b.delivery_status == 'delivered' %}
      <button class="btn" style="background:#eff6ff;color:#1e40af;border:1px solid #93c5fd"
        onclick="return confirm('Mark this booking as PICKED UP?')">✅ Mark as Picked Up</button>
      {% endif %}
    </form>
    {% else %}
    <span style="padding:.5rem 1rem;background:#f0fdf4;color:#16a34a;border:1px solid #86efac;border-radius:8px;font-weight:600">✔ Picked Up</span>
    {% endif %}
    <form method="POST" action="/admin/booking/{{ b.id }}/delete" style="margin-left:auto">
      <button class="btn" style="background:#1f2937;color:white" onclick="return confirm('Permanently DELETE booking #{{ b.id }}? This cannot be undone. Customer info will be kept.')">
        Delete Booking
      </button>
    </form>
  </div>

  {% if b.final_payment_link %}
  <div style="background:#fff8f3;border:2px solid #dd6b20;border-radius:10px;padding:1.1rem 1.25rem;margin-top:1rem">
    <div style="font-weight:700;color:#c05621;margin-bottom:.4rem">Final Payment Link Sent</div>
    <a href="{{ b.final_payment_link }}" target="_blank" style="font-size:.85rem;word-break:break-all">{{ b.final_payment_link }}</a>
  </div>
  {% endif %}
</div>

<!-- ── Payment Amount Modal ── -->
<div id="payment-modal" style="display:none;position:fixed;inset:0;background:rgba(0,0,0,.55);z-index:9999;align-items:center;justify-content:center">
  <div style="background:white;border-radius:14px;padding:2rem;width:min(420px,92vw);box-shadow:0 20px 60px rgba(0,0,0,.3)">
    <h2 id="modal-title" style="margin:0 0 .35rem;font-size:1.2rem;color:#1a202c">Send Stripe Payment Link</h2>
    <p id="modal-subtitle" style="margin:0 0 1.25rem;font-size:.9rem;color:#718096"></p>
    <label style="display:block;font-size:.85rem;font-weight:600;color:#374151;margin-bottom:.4rem">Amount to charge ($)</label>
    <input id="modal-amount" type="number" min="0.01" step="0.01"
           style="width:100%;box-sizing:border-box;border:2px solid #d1d5db;border-radius:8px;padding:.6rem .85rem;font-size:1.25rem;font-weight:700;color:#1a202c;margin-bottom:.3rem">
    <p style="font-size:.78rem;color:#9ca3af;margin:0 0 1.5rem">You can change this to any amount — the customer will be charged exactly what you enter.</p>
    <div style="display:flex;gap:.75rem">
      <button id="modal-confirm" style="flex:1;background:#16a34a;color:white;border:none;border-radius:8px;padding:.7rem;font-size:.95rem;font-weight:700;cursor:pointer">
        ✓ Send Payment Link
      </button>
      <button onclick="document.getElementById('payment-modal').style.display='none'"
              style="background:#f3f4f6;color:#374151;border:none;border-radius:8px;padding:.7rem 1.25rem;font-size:.95rem;cursor:pointer">
        Cancel
      </button>
    </div>
  </div>
</div>

<script>
(function() {
  var grandTotal = parseFloat('{{ b.grand_total or 0 }}') || 0;
  var eventDate  = '{{ b.event_start_date or "" }}';
  var modal      = document.getElementById('payment-modal');
  var amountIn   = document.getElementById('modal-amount');
  var confirmBtn = document.getElementById('modal-confirm');
  var activeForm = null;
  var activeHidden = null;

  function daysUntil(dateStr) {
    if (!dateStr) return 999;
    var d = new Date(dateStr + 'T00:00:00');
    var today = new Date(); today.setHours(0,0,0,0);
    return Math.round((d - today) / 86400000);
  }

  function openModal(title, subtitle, suggestedAmount, form, hiddenInput) {
    document.getElementById('modal-title').textContent = title;
    document.getElementById('modal-subtitle').textContent = subtitle;
    amountIn.value = suggestedAmount.toFixed(2);
    activeForm = form;
    activeHidden = hiddenInput;
    modal.style.display = 'flex';
    amountIn.focus();
    amountIn.select();
  }

  // Accept button
  var acceptBtn = document.getElementById('accept-btn');
  if (acceptBtn) {
    acceptBtn.addEventListener('click', function() {
      var days = daysUntil(eventDate);
      var suggested = days <= 7 ? grandTotal : Math.round(grandTotal * 0.25 * 100) / 100;
      var label = days <= 7 ? 'Full payment (event within 7 days)' : '25% deposit suggested';
      openModal(
        'Accept Booking — Set Payment Amount',
        'Grand total: $' + grandTotal.toFixed(2) + ' | ' + label,
        suggested,
        document.getElementById('accept-form'),
        document.getElementById('accept-amount-input')
      );
    });
  }

  // Final payment button
  var finalBtn = document.getElementById('final-btn');
  if (finalBtn) {
    finalBtn.addEventListener('click', function() {
      var suggested = Math.round(grandTotal * 0.75 * 100) / 100;
      openModal(
        'Send Final Payment Reminder',
        'Grand total: $' + grandTotal.toFixed(2) + ' | Remaining 75% suggested',
        suggested,
        document.getElementById('final-form'),
        document.getElementById('final-amount-input')
      );
    });
  }

  // Confirm button submits the active form
  confirmBtn.addEventListener('click', function() {
    var amt = parseFloat(amountIn.value);
    if (!amt || amt <= 0) { amountIn.style.borderColor='#ef4444'; return; }
    activeHidden.value = amt.toFixed(2);
    modal.style.display = 'none';
    activeForm.submit();
  });

  // Close on backdrop click
  modal.addEventListener('click', function(e) {
    if (e.target === modal) modal.style.display = 'none';
  });

  // Enter key confirms
  amountIn.addEventListener('keydown', function(e) {
    if (e.key === 'Enter') confirmBtn.click();
  });
})();
</script>

</body></html>
"""


# ══════════════════════════════════════════════════════════════════════════════
#  ROUTES — BOOKING FORM
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/", methods=["GET"])
def index():
    return render_template_string(FORM_HTML,
        business_name=BUSINESS_NAME,
        products=get_products(),
        exact_time_fee=EXACT_TIME_FEE,
        error=None,
        form={},
    )


@app.route("/availability")
def availability():
    start = request.args.get("start", "")
    end   = request.args.get("end",   "")
    if not start or not end:
        return jsonify({p["id"]: p["total"] for p in get_products()})
    avail = get_available(start, end)
    return jsonify(avail)


@app.route("/delivery_fee")
def delivery_fee_check():
    address = request.args.get("address", "")
    miles   = get_distance_miles(address) if address else None
    fee, note = calc_delivery_fee(miles)
    return jsonify({"fee": fee, "note": note, "miles": miles})


@app.route("/submit", methods=["POST"])
def submit():
    f = request.form

    full_name        = f.get("full_name",        "").strip()
    company_name     = f.get("company_name",     "").strip()
    renter_street    = f.get("renter_street",    "").strip()
    renter_city      = f.get("renter_city",      "").strip()
    renter_state     = f.get("renter_state",     "").strip()
    renter_zip       = f.get("renter_zip",       "").strip()
    phone            = f.get("phone",            "").strip()
    email            = f.get("email",            "").strip()
    event_start_date = f.get("event_start_date", "").strip()
    event_end_date   = f.get("event_end_date",   "").strip()
    event_start_time = f.get("event_start_time", "").strip()
    event_end_time   = f.get("event_end_time",   "").strip()
    setup_time       = f.get("setup_time",       "").strip()
    venue_type       = f.get("venue_type",       "venue").strip()
    venue_latest     = f.get("venue_latest_pickup","").strip()
    event_street     = f.get("event_street",     "").strip()
    event_city       = f.get("event_city",       "").strip()
    event_state      = f.get("event_state",      "").strip()
    event_zip        = f.get("event_zip",        "").strip()
    exact_delivery   = f.get("exact_time_delivery","") == "yes"
    delivery_location= f.get("delivery_location","").strip()
    notes            = f.get("notes",            "").strip()

    _products = get_products()
    if not email or not full_name:
        return render_template_string(FORM_HTML, business_name=BUSINESS_NAME,
            products=_products, exact_time_fee=EXACT_TIME_FEE,
            error="Name and email are required.", form=f), 400

    # Accept any quantity — admin is alerted of conflicts on the dashboard
    # Collect items first so we can apply marquee tier pricing
    _raw_items = []
    for p in _products:
        qty = int(f.get(f"qty_{p['id']}", 0) or 0)
        qty = max(0, qty)
        if qty > 0:
            _raw_items.append({"id": p["id"], "name": p["name"], "qty": qty, "base_price": float(p["price"])})

    # Marquee tier pricing (must match JS logic exactly)
    def _is_ml(name): return bool(re.match(r'^marquee\s+[a-z]$', name.strip(), re.IGNORECASE))
    def _is_mn(name): return bool(re.match(r'^marquee\s+#?\d', name.strip(), re.IGNORECASE))
    _ML_TIERS = [(1,85),(2,160),(3,225),(4,285)]
    _MN_TIERS = [(1,80),(2,150),(3,215),(4,275)]
    def _ml_total(n):
        for c,t in _ML_TIERS:
            if c==n: return float(t)
        return 285.0+(n-4)*55.0
    def _mn_total(n):
        for c,t in _MN_TIERS:
            if c==n: return float(t)
        return 275.0+(n-4)*55.0
    ml_count = sum(i["qty"] for i in _raw_items if _is_ml(i["name"]))
    mn_count = sum(i["qty"] for i in _raw_items if _is_mn(i["name"]))
    ml_unit = (_ml_total(ml_count)/ml_count) if ml_count>0 else 0.0
    mn_unit = (_mn_total(mn_count)/mn_count) if mn_count>0 else 0.0

    order_items, subtotal = [], 0.0
    for item in _raw_items:
        name = item["name"]
        qty  = item["qty"]
        if _is_ml(name):
            unit_price = ml_unit
        elif _is_mn(name):
            unit_price = mn_unit
        else:
            unit_price = item["base_price"]
        line = round(qty * unit_price, 2)
        subtotal += line
        order_items.append({"id": item["id"], "name": name, "qty": qty,
                             "unit_price": round(unit_price, 2), "total": line})

    # Stackable marquee fee
    stackable     = f.get("stackable", "no").strip().lower() == "yes"
    stackable_top = f.get("stackable_top", "").strip()
    has_marquee   = any(_is_ml(i["name"]) or _is_mn(i["name"]) for i in order_items)
    if stackable and has_marquee:
        subtotal += 75.0
        stack_label = f"Stackable Marquee (top: {stackable_top})" if stackable_top else "Stackable Marquee"
        order_items.append({"name": stack_label, "qty": 1, "unit_price": 75.0, "total": 75.0})

    # Delivery
    event_address = f"{event_street}, {event_city}, {event_state} {event_zip}"
    miles = get_distance_miles(event_address)
    delivery_fee, delivery_note = calc_delivery_fee(miles)

    exact_fee   = EXACT_TIME_FEE if exact_delivery else 0.0
    late_night_fee = float(f.get("late_night_fee") or 0)
    # Validate server-side: check end time actually falls in late night window
    def _is_late_night(t):
        if not t: return False
        try:
            h, m = map(int, t.strip().split(':')[:2])
            mins = h * 60 + m
            return mins >= 23*60+30 or mins < 7*60
        except: return False
    if late_night_fee and not _is_late_night(event_end_time):
        late_night_fee = 0.0
    if _is_late_night(event_end_time):
        late_night_fee = 125.0
    pre_tax_total = round(subtotal + exact_fee + late_night_fee + delivery_fee, 2)

    # Check if customer is tax exempt (either from DB record or self-reported on form)
    is_tax_exempt = f.get("tax_exempt_request") == "1"
    if not is_tax_exempt:
        tax_check_conn = get_db()
        if tax_check_conn and email:
            try:
                tc = tax_check_conn.cursor()
                tc.execute("SELECT tax_exempt FROM customers WHERE email=%s", (email,))
                row = tc.fetchone()
                if row and row[0]:
                    is_tax_exempt = True
                tc.close()
                tax_check_conn.close()
            except Exception:
                pass

    applied_tax_rate = 0.0 if is_tax_exempt else CT_TAX_RATE
    tax_amount  = round(pre_tax_total * applied_tax_rate, 2)
    grand_total = round(pre_tax_total + tax_amount, 2)

    # Save to DB
    booking_id = None
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute("""
                INSERT INTO bookings (
                    full_name, company_name,
                    renter_street, renter_city, renter_state, renter_zip,
                    phone, email,
                    event_start_date, event_end_date,
                    event_start_time, event_end_time, setup_time,
                    venue_type, venue_latest_pickup,
                    event_street, event_city, event_state, event_zip,
                    exact_time_delivery, delivery_location,
                    delivery_fee, distance_miles,
                    items_json, items_subtotal, exact_time_fee, late_night_fee, tax_rate, tax_amount, tax_exempt, grand_total,
                    notes
                ) VALUES (
                    %s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,
                    %s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s
                ) RETURNING id
            """, (
                full_name, company_name,
                renter_street, renter_city, renter_state, renter_zip,
                phone, email,
                event_start_date or None, event_end_date or None,
                event_start_time, event_end_time, setup_time,
                venue_type, venue_latest or None,
                event_street, event_city, event_state, event_zip,
                exact_delivery, delivery_location,
                delivery_fee, miles,
                json.dumps(order_items), subtotal, exact_fee, late_night_fee, applied_tax_rate, tax_amount, is_tax_exempt, grand_total,
                notes,
            ))
            booking_id = cur.fetchone()[0]
            view_token = secrets.token_urlsafe(24)
            cur.execute("UPDATE bookings SET view_token=%s WHERE id=%s", (view_token, booking_id))
            conn.commit()
            cur.close()
            conn.close()
            log.info(f"Booking #{booking_id} saved for {full_name}")
        except Exception as e:
            log.error(f"DB insert error: {e}")

    booking_data = {
        "id": booking_id, "view_token": view_token if booking_id else None,
        "full_name": full_name, "company_name": company_name,
        "renter_street": renter_street, "renter_city": renter_city,
        "renter_state": renter_state, "renter_zip": renter_zip,
        "phone": phone, "email": email,
        "event_start_date": event_start_date, "event_end_date": event_end_date,
        "event_start_time": event_start_time, "event_end_time": event_end_time,
        "setup_time": setup_time, "venue_type": venue_type,
        "venue_latest_pickup": venue_latest,
        "event_street": event_street, "event_city": event_city,
        "event_state": event_state, "event_zip": event_zip,
        "exact_time_delivery": exact_delivery,
        "delivery_location": delivery_location,
        "delivery_fee": delivery_fee, "delivery_fee_note": delivery_note,
        "distance_miles": miles,
        "items_json": json.dumps(order_items),
        "items_subtotal": subtotal, "exact_time_fee": exact_fee,
        "tax_rate": applied_tax_rate, "tax_amount": tax_amount, "tax_exempt": is_tax_exempt,
        "grand_total": grand_total, "notes": notes,
    }
    send_owner_email(booking_data)
    send_customer_email(booking_data)

    # ── Text alert to owner ──────────────────────────────────────────────────
    _base = os.environ.get("APP_BASE_URL", "").rstrip("/")
    _admin_link = f"{_base}/admin/booking/{booking_id}" if _base else f"/admin/booking/{booking_id}"
    send_sms(
        f"New Booking #{booking_id}\n"
        f"{full_name} | {_fmt_date(event_start_date)}\n"
        f"Total: ${grand_total:.2f}\n"
        f"View & Respond: {_admin_link}"
    )

    # Upsert customer record — if email already exists update their info, else insert
    cust_conn = get_db()
    if cust_conn and email:
        try:
            cust_cur = cust_conn.cursor()
            cust_cur.execute("""
                INSERT INTO customers (full_name, company_name, email, phone, street, city, state, zip)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                ON CONFLICT (email) WHERE email IS NOT NULL DO UPDATE SET
                    full_name    = EXCLUDED.full_name,
                    company_name = EXCLUDED.company_name,
                    phone        = EXCLUDED.phone,
                    street       = EXCLUDED.street,
                    city         = EXCLUDED.city,
                    state        = EXCLUDED.state,
                    zip          = EXCLUDED.zip
            """, (
                full_name,
                company_name or None,
                email,
                phone or None,
                renter_street or None,
                renter_city or None,
                renter_state or None,
                renter_zip or None,
            ))
            cust_conn.commit()
            cust_cur.close()
            cust_conn.close()
            log.info(f"Customer record upserted for {email}")
        except Exception as e:
            log.error(f"Customer upsert error: {e}")

    return render_template_string(SUCCESS_HTML,
        business_name=BUSINESS_NAME,
        business_phone=BUSINESS_PHONE,
        name=full_name.split()[0],
        email=email,
        booking_id=booking_id,
    )


ADMIN_INVENTORY_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <link rel="manifest" href="/manifest.json">
  <meta name="theme-color" content="#2563eb">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="default">
  <meta name="apple-mobile-web-app-title" content="Rent a Party">
  <link rel="apple-touch-icon" href="/icon-192.png">
  <script>if("serviceWorker"in navigator)navigator.serviceWorker.register("/sw.js");</script>
  <title>Inventory — {{ business_name }}</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Helvetica,sans-serif;background:#f5f6fa;color:#111827;min-height:100vh}
    .topbar{background:white;border-bottom:1px solid #e5e7eb;padding:.9rem 1.75rem;display:flex;justify-content:space-between;align-items:center;position:sticky;top:0;z-index:50}
    .topbar-brand{font-size:1rem;font-weight:700;color:#111827}
    .topbar-nav{display:flex;gap:.5rem;align-items:center}
    .nav-link{color:#6b7280;text-decoration:none;font-size:.85rem;font-weight:500;padding:.38rem .75rem;border-radius:6px;transition:all .12s}
    .nav-link:hover{background:#f3f4f6;color:#111827}
    .nav-link.active{background:#eff6ff;color:#2563eb;font-weight:600}
    .logout-btn{background:white;border:1px solid #d1d5db;color:#6b7280;padding:.38rem .85rem;border-radius:6px;cursor:pointer;font-size:.82rem;font-weight:500;text-decoration:none}
    .main{max-width:900px;margin:0 auto;padding:1.75rem}
    .page-title{font-size:1.4rem;font-weight:700;color:#111827;margin-bottom:.35rem}
    .page-sub{font-size:.88rem;color:#6b7280;margin-bottom:1.5rem}
    .flash{padding:.75rem 1rem;border-radius:8px;margin-bottom:1.25rem;font-size:.9rem;font-weight:500}
    .flash-ok{background:#dcfce7;color:#166534;border:1px solid #bbf7d0}
    .flash-err{background:#fee2e2;color:#991b1b;border:1px solid #fecaca}
    .card{background:white;border:1px solid #e5e7eb;border-radius:10px;overflow:hidden;margin-bottom:1.5rem}
    .card-header{padding:.85rem 1.25rem;background:#f9fafb;border-bottom:1px solid #e5e7eb;font-weight:700;font-size:.88rem;color:#374151;display:flex;justify-content:space-between;align-items:center}
    table{width:100%;border-collapse:collapse}
    th{padding:.65rem 1rem;text-align:left;font-size:.72rem;font-weight:600;color:#9ca3af;text-transform:uppercase;letter-spacing:.5px;border-bottom:1px solid #e5e7eb;background:#f9fafb}
    td{padding:.6rem 1rem;border-bottom:1px solid #f3f4f6;vertical-align:middle}
    tr:last-child td{border-bottom:none}
    tbody tr:hover td{background:#fafafa}
    input[type=text],input[type=number]{width:100%;padding:.4rem .6rem;border:1px solid #d1d5db;border-radius:6px;font-size:.86rem;color:#111827;background:white;transition:border .12s}
    input[type=text]:focus,input[type=number]:focus{outline:none;border-color:#2563eb;box-shadow:0 0 0 2px rgba(37,99,235,.1)}
    input[type=number]{max-width:90px}
    .btn{display:inline-block;padding:.4rem .85rem;border-radius:6px;font-size:.82rem;font-weight:600;cursor:pointer;border:none;text-decoration:none;transition:all .12s;line-height:1.5}
    .btn-primary{background:#2563eb;color:white}
    .btn-primary:hover{background:#1d4ed8}
    .btn-danger{background:#fee2e2;color:#991b1b;border:1px solid #fecaca}
    .btn-danger:hover{background:#fecaca}
    .btn-outline{background:white;color:#374151;border:1px solid #d1d5db}
    .btn-outline:hover{background:#f3f4f6}
    .add-form{display:grid;grid-template-columns:1fr auto auto auto;gap:.6rem;align-items:center;padding:1rem 1.25rem;background:#f9fafb;border-top:1px solid #e5e7eb}
    .add-form input{width:100%}
    .save-bar{display:flex;justify-content:flex-end;gap:.75rem;padding:1rem 1.25rem;border-top:1px solid #e5e7eb;background:#f9fafb}
    .item-id{font-size:.75rem;color:#9ca3af;font-family:monospace}
    @media(max-width:600px){
      .add-form{grid-template-columns:1fr;gap:.5rem}
      .main{padding:1rem}
    }
  </style>
</head>
<body>
<div class="topbar">
  <div class="topbar-brand">🎉 {{ business_name }}</div>
  <div class="topbar-nav">
    <a href="/admin/dashboard" class="nav-link">Dashboard</a>
    <a href="/admin/inventory" class="nav-link active">Inventory</a>
    <a href="/admin/customers" class="nav-link">Customers</a>
    <a href="/admin/calendar" class="nav-link">📅 Calendar</a>
    <a href="/admin/route" class="nav-link">🗺 Route</a>
    <a href="/admin/logout" class="logout-btn">Sign Out</a>
  </div>
</div>
<div class="main">
  <div class="page-title">Inventory</div>
  <div class="page-sub">Edit item names, rental prices, and total quantities. Changes take effect immediately on the booking form.</div>

  {% if flash_ok %}<div class="flash flash-ok">✓ {{ flash_ok }}</div>{% endif %}
  {% if flash_err %}<div class="flash flash-err">⚠ {{ flash_err }}</div>{% endif %}

  <!-- ── Availability Checker ── -->
  <div class="card" style="margin-bottom:1.5rem">
    <div class="card-header">📅 Check Availability</div>
    <div style="padding:1.1rem 1.25rem">
      <div style="display:flex;gap:.75rem;margin-bottom:.9rem">
        <button type="button" id="btn_single" onclick="setMode('single')"
          style="padding:.35rem .9rem;border-radius:6px;font-size:.83rem;font-weight:600;cursor:pointer;border:1.5px solid #2563eb;background:#2563eb;color:white">Single Day</button>
        <button type="button" id="btn_range" onclick="setMode('range')"
          style="padding:.35rem .9rem;border-radius:6px;font-size:.83rem;font-weight:600;cursor:pointer;border:1.5px solid #d1d5db;background:white;color:#374151">Date Range</button>
      </div>
      <form method="GET" action="/admin/inventory" style="display:flex;flex-wrap:wrap;gap:.65rem;align-items:flex-end">
        <div>
          <label style="display:block;font-size:.75rem;font-weight:600;color:#6b7280;margin-bottom:.25rem">Date</label>
          <input type="date" name="check_from" id="check_from" value="{{ check_from }}"
            style="border:1px solid #d1d5db;border-radius:6px;padding:.38rem .6rem;font-size:.86rem">
        </div>
        <div id="to_wrapper" style="display:none">
          <label style="display:block;font-size:.75rem;font-weight:600;color:#6b7280;margin-bottom:.25rem">To</label>
          <input type="date" name="check_to" id="check_to" value="{{ check_to }}"
            style="border:1px solid #d1d5db;border-radius:6px;padding:.38rem .6rem;font-size:.86rem">
        </div>
        <button type="submit" style="background:#2563eb;color:white;border:none;border-radius:6px;padding:.42rem 1rem;font-size:.85rem;font-weight:600;cursor:pointer;align-self:flex-end">Check</button>
        {% if check_from %}<a href="/admin/inventory" style="align-self:flex-end;font-size:.82rem;color:#6b7280;text-decoration:none;padding:.42rem .5rem">✕ Clear</a>{% endif %}
      </form>
    </div>
    {% if avail_data %}
    <div style="border-top:1px solid #e5e7eb;padding:.75rem 1.25rem .5rem">
      <div style="font-size:.8rem;font-weight:600;color:#374151;margin-bottom:.6rem">
        Availability for {{ check_from }}{% if check_to and check_to != check_from %} → {{ check_to }}{% endif %}
      </div>
      <div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(200px,1fr));gap:.6rem">
        {% for item in avail_data %}
        {% set pct = ((item.reserved / item.total * 100)|int) if item.total > 0 else 0 %}
        <div style="border:1px solid #e5e7eb;border-radius:8px;padding:.65rem .85rem;background:{% if item.available == 0 %}#fef2f2{% elif item.available <= 2 %}#fffbeb{% else %}#f0fdf4{% endif %}">
          <div style="font-size:.84rem;font-weight:600;color:#111827;margin-bottom:.3rem">{{ item.name }}</div>
          <div style="display:flex;justify-content:space-between;align-items:center">
            <span style="font-size:.78rem;color:#6b7280">{{ item.reserved }} reserved</span>
            <span style="font-size:.88rem;font-weight:700;color:{% if item.available == 0 %}#dc2626{% elif item.available <= 2 %}#d97706{% else %}#16a34a{% endif %}">
              {{ item.available }}/{{ item.total }} avail{% if item.available == 0 %} — SOLD OUT{% endif %}
            </span>
          </div>
          <div style="height:4px;background:#e5e7eb;border-radius:2px;margin-top:.4rem">
            <div style="height:4px;border-radius:2px;width:{{ pct }}%;background:{% if pct>=100 %}#ef4444{% elif pct>=70 %}#f59e0b{% else %}#10b981{% endif %}"></div>
          </div>
        </div>
        {% endfor %}
      </div>
    </div>
    {% endif %}
  </div>

  <div class="card">
    <div class="card-header">
      <span>Rental Items ({{ products|length }})</span>
      <input type="text" id="inv-search" placeholder="🔍 Search items…" oninput="filterInv(this.value)"
        style="border:1px solid #d1d5db;border-radius:7px;padding:.35rem .75rem;font-size:.85rem;width:220px;outline:none;transition:border .12s"
        onfocus="this.style.borderColor='#2563eb'" onblur="this.style.borderColor='#d1d5db'">
    </div>
    <form method="POST" action="/admin/inventory/save">
      <table>
        <thead>
          <tr>
            <th>Item Name</th>
            <th>Price / Unit</th>
            <th>Total Qty</th>
            <th>Remove</th>
          </tr>
        </thead>
        <tbody>
          {% for p in products %}
          <tr>
            <td>
              <input type="hidden" name="id_{{ loop.index0 }}" value="{{ p.id }}">
              <input type="text" name="name_{{ loop.index0 }}" value="{{ p.name }}" required>
            </td>
            <td>
              <div style="display:flex;align-items:center;gap:.3rem">
                <span style="color:#9ca3af;font-size:.9rem">$</span>
                <input type="number" name="price_{{ loop.index0 }}" value="{{ '%.2f'|format(p.price|float) }}" min="0" step="0.01" required>
              </div>
            </td>
            <td>
              <input type="number" name="total_{{ loop.index0 }}" value="{{ p.total }}" min="0" step="1" required>
            </td>
            <td>
              <button type="submit" form="del_{{ p.id }}" class="btn btn-danger" onclick="return confirm('Remove {{ p.name }} from inventory?')">Remove</button>
            </td>
          </tr>
          {% endfor %}
        </tbody>
      </table>
      <input type="hidden" name="count" value="{{ products|length }}">
      <div class="save-bar">
        <a href="/admin/dashboard" class="btn btn-outline">Cancel</a>
        <button type="submit" class="btn btn-primary">Save Changes</button>
      </div>
    </form>

    <!-- Delete forms (one per item, outside main form) -->
    {% for p in products %}
    <form id="del_{{ p.id }}" method="POST" action="/admin/inventory/delete/{{ p.id }}" style="display:none"></form>
    {% endfor %}

    <!-- Add new item -->
    <form method="POST" action="/admin/inventory/add">
      <div class="add-form">
        <input type="text" name="name" placeholder="New item name (e.g. Tents 20x20)" required>
        <div style="display:flex;align-items:center;gap:.3rem">
          <span style="color:#9ca3af">$</span>
          <input type="number" name="price" placeholder="Price" min="0" step="0.01" style="max-width:90px" required>
        </div>
        <input type="number" name="total" placeholder="Qty" min="1" step="1" style="max-width:70px" required>
        <button type="submit" class="btn btn-primary">+ Add Item</button>
      </div>
    </form>
  </div>
</div>
<script>
function filterInv(q){
  const term=q.toLowerCase();
  document.querySelectorAll('tbody tr').forEach(row=>{
    const name=(row.querySelector('input[type=text]')?.value||'').toLowerCase();
    row.style.display=name.includes(term)?'':'none';
  });
}
function setMode(m){
  const isRange=m==='range';
  document.getElementById('to_wrapper').style.display=isRange?'block':'none';
  const bs=document.getElementById('btn_single').style;
  const br=document.getElementById('btn_range').style;
  bs.background=isRange?'white':'#2563eb'; bs.color=isRange?'#374151':'white'; bs.borderColor=isRange?'#d1d5db':'#2563eb';
  br.background=isRange?'#2563eb':'white'; br.color=isRange?'white':'#374151'; br.borderColor=isRange?'#2563eb':'#d1d5db';
  if(!isRange) document.getElementById('check_to').value='';
}
{% if check_to and check_to != check_from %}setMode('range');{% else %}setMode('single');{% endif %}
</script>
</body></html>
"""


# ══════════════════════════════════════════════════════════════════════════════
#  ROUTES — CUSTOMER ORDER VIEW (read-only, token-gated)
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/booking/view/<token>")
def customer_booking_view(token):
    if not token:
        return "Invalid link.", 404
    conn = get_db()
    if not conn:
        return "Unable to load booking. Please try again later.", 503
    b, items = None, []
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("SELECT * FROM bookings WHERE view_token=%s", (token,))
        row = cur.fetchone()
        if row:
            b = _row(row)
            try: items = json.loads(b.get("items_json") or "[]")
            except Exception: items = []
        cur.close(); conn.close()
    except Exception as e:
        log.error(f"Customer view error: {e}")
    if not b:
        return "Booking not found or link has expired.", 404

    STATUS_LABELS = {
        "pending":   ("🕐 Under Review",  "#92400e", "#fef3c7"),
        "accepted":  ("✅ Accepted",       "#1e40af", "#dbeafe"),
        "confirmed": ("✅ Confirmed",      "#166534", "#dcfce7"),
        "denied":    ("❌ Denied",         "#991b1b", "#fee2e2"),
        "cancelled": ("🚫 Cancelled",      "#6b7280", "#f3f4f6"),
    }
    status_key = (b.get("status") or "pending").lower()
    status_label, status_color, status_bg = STATUS_LABELS.get(status_key, ("Unknown", "#6b7280", "#f3f4f6"))

    disc_amount = float(b.get("discount_amount") or 0)
    disc_type   = b.get("discount_type") or ""
    disc_value  = float(b.get("discount_value") or 0)

    items_html = ""
    for it in items:
        up  = float(it.get("unit_price") or 0)
        tot = float(it.get("total") or round(up * int(it.get("qty",1)), 2))
        items_html += f"""
        <tr>
          <td style="padding:10px 14px;border-bottom:1px solid #e5e7eb">{it.get('name','')}</td>
          <td style="padding:10px 14px;border-bottom:1px solid #e5e7eb;text-align:center">{it.get('qty','')}</td>
          <td style="padding:10px 14px;border-bottom:1px solid #e5e7eb;text-align:right">${up:.2f}</td>
          <td style="padding:10px 14px;border-bottom:1px solid #e5e7eb;text-align:right;font-weight:600">${tot:.2f}</td>
        </tr>"""

    exact_fee = float(b.get("exact_time_fee") or 0)
    late_fee  = float(b.get("late_night_fee") or 0)
    if exact_fee:
        items_html += f'<tr><td colspan="3" style="padding:10px 14px;border-bottom:1px solid #e5e7eb;color:#6b7280">Exact Time Delivery</td><td style="padding:10px 14px;border-bottom:1px solid #e5e7eb;text-align:right;font-weight:600">${exact_fee:.2f}</td></tr>'
    if late_fee:
        items_html += f'<tr><td colspan="3" style="padding:10px 14px;border-bottom:1px solid #e5e7eb;color:#6b7280">Late Night Fee</td><td style="padding:10px 14px;border-bottom:1px solid #e5e7eb;text-align:right;font-weight:600">${late_fee:.2f}</td></tr>'
    delivery_fee = float(b.get("delivery_fee") or 0)
    if delivery_fee:
        miles_str = f"{b.get('distance_miles','?')} mi" if b.get("distance_miles") else ""
        items_html += f'<tr><td colspan="3" style="padding:10px 14px;border-bottom:1px solid #e5e7eb;color:#6b7280">Delivery Fee {miles_str}</td><td style="padding:10px 14px;border-bottom:1px solid #e5e7eb;text-align:right;font-weight:600">${delivery_fee:.2f}</td></tr>'
    if disc_amount > 0:
        disc_lbl = f"{disc_value:.1f}% Discount" if disc_type == "percent" else f"${disc_value:.2f} Discount"
        items_html += f'<tr style="background:#f0fdf4"><td colspan="3" style="padding:10px 14px;border-bottom:1px solid #e5e7eb;color:#166534;font-weight:600">🏷️ {disc_lbl}</td><td style="padding:10px 14px;border-bottom:1px solid #e5e7eb;text-align:right;font-weight:700;color:#16a34a">- ${disc_amount:.2f}</td></tr>'
    tax_amount = float(b.get("tax_amount") or 0)
    tax_rate   = float(b.get("tax_rate") or 0)
    if b.get("tax_exempt"):
        items_html += '<tr><td colspan="3" style="padding:10px 14px;border-bottom:1px solid #e5e7eb;color:#6b7280">CT Sales Tax <span style="font-size:.75rem;background:#dcfce7;color:#166534;border-radius:4px;padding:.1rem .35rem;margin-left:.3rem">TAX EXEMPT</span></td><td style="padding:10px 14px;border-bottom:1px solid #e5e7eb;text-align:right;color:#166534">$0.00</td></tr>'
    elif tax_amount:
        items_html += f'<tr><td colspan="3" style="padding:10px 14px;border-bottom:1px solid #e5e7eb;color:#6b7280">CT Sales Tax ({tax_rate*100:.2f}%)</td><td style="padding:10px 14px;border-bottom:1px solid #e5e7eb;text-align:right;font-weight:600">${tax_amount:.2f}</td></tr>'

    grand_total = float(b.get("grand_total") or 0)
    amount_paid = float(b.get("amount_paid") or 0)
    balance_due = max(round(grand_total - amount_paid, 2), 0)

    venue_map = {"venue": "Event Venue", "backyard": "Backyard", "residential": "Residential", "park": "Park", "other": "Other"}

    html = f"""<!DOCTYPE html>
<html lang="en"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Your Order — {BUSINESS_NAME}</title>
<style>
  *{{box-sizing:border-box;margin:0;padding:0}}
  body{{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;background:#f0f4f8;color:#1a202c;padding:1.5rem 1rem}}
  .wrap{{max-width:680px;margin:0 auto}}
  .card{{background:white;border-radius:12px;box-shadow:0 2px 12px rgba(0,0,0,.07);padding:1.5rem;margin-bottom:1.25rem}}
  .section-title{{font-size:.72rem;font-weight:700;text-transform:uppercase;letter-spacing:.08em;color:#6b7280;margin-bottom:.9rem}}
  .row{{display:grid;grid-template-columns:1fr 1fr;gap:.5rem 1.5rem}}
  .field label{{font-size:.75rem;color:#6b7280;font-weight:600;display:block;margin-bottom:.2rem}}
  .field span{{font-size:.95rem;color:#1a202c}}
  table{{width:100%;border-collapse:collapse;font-size:.9rem}}
  th{{padding:9px 14px;background:#f8fafc;color:#6b7280;font-size:.72rem;text-transform:uppercase;letter-spacing:.05em;text-align:left}}
  th:last-child{{text-align:right}}
  .grand-row td{{padding:13px 14px;background:#1a365d;color:white;font-weight:700;font-size:1rem}}
  .grand-row td:last-child{{text-align:right;font-size:1.15rem}}
  @media(max-width:500px){{.row{{grid-template-columns:1fr}}}}
</style>
</head><body>
<div class="wrap">

  <div style="text-align:center;margin-bottom:1.5rem">
    <div style="font-size:1.5rem;font-weight:800;color:#1a365d">{BUSINESS_NAME}</div>
    <div style="font-size:.88rem;color:#6b7280;margin-top:.25rem">Order Confirmation</div>
  </div>

  <!-- Status banner -->
  <div style="background:{status_bg};border-radius:10px;padding:.85rem 1.25rem;margin-bottom:1.25rem;display:flex;align-items:center;justify-content:space-between">
    <span style="font-weight:700;color:{status_color};font-size:.95rem">{status_label}</span>
    <span style="font-size:.8rem;color:{status_color};opacity:.75">Booking #{b.get('id')}</span>
  </div>

  <!-- Your Information -->
  <div class="card">
    <div class="section-title">Your Information</div>
    <div class="row">
      <div class="field"><label>Name</label><span>{b.get('full_name') or '—'}</span></div>
      <div class="field"><label>Email</label><span>{b.get('email') or '—'}</span></div>
      <div class="field"><label>Phone</label><span>{b.get('phone') or '—'}</span></div>
      {'<div class="field"><label>Company</label><span>' + str(b.get('company_name')) + '</span></div>' if b.get('company_name') else ''}
      <div class="field" style="grid-column:1/-1"><label>Address</label>
        <span>{b.get('renter_street') or ''}{', ' + str(b.get('renter_city')) if b.get('renter_city') else ''}{', ' + str(b.get('renter_state')) if b.get('renter_state') else ''} {b.get('renter_zip') or ''}</span>
      </div>
    </div>
  </div>

  <!-- Event Details -->
  <div class="card">
    <div class="section-title">Event Details</div>
    <div class="row">
      <div class="field"><label>Delivery Date</label><span>{_fmt_date(b.get('event_start_date')) or '—'}</span></div>
      <div class="field"><label>Pickup Date</label><span>{_fmt_date(b.get('event_end_date')) or '—'}</span></div>
      <div class="field"><label>Delivery / Setup Time</label><span>{b.get('setup_time') or '—'}</span></div>
      <div class="field"><label>Pickup Time</label><span>{b.get('event_end_time') or '—'}</span></div>
      <div class="field"><label>Venue Type</label><span>{venue_map.get(b.get('venue_type',''), b.get('venue_type','') or '—')}</span></div>
      <div class="field" style="grid-column:1/-1"><label>Event Address</label>
        <span>{b.get('event_street') or ''}{', ' + str(b.get('event_city')) if b.get('event_city') else ''}{', ' + str(b.get('event_state')) if b.get('event_state') else ''} {b.get('event_zip') or ''}</span>
      </div>
      <div class="field" style="grid-column:1/-1"><label>Deliver Items To</label><span>{b.get('delivery_location') or '—'}</span></div>
      {'<div class="field" style="grid-column:1/-1"><label>Notes</label><span>' + str(b.get('notes')) + '</span></div>' if b.get('notes') else ''}
    </div>
  </div>

  <!-- Items & Totals -->
  <div class="card">
    <div class="section-title">Items &amp; Totals</div>
    <table>
      <thead><tr>
        <th>Item</th><th style="text-align:center">Qty</th><th style="text-align:right">Unit</th><th style="text-align:right">Total</th>
      </tr></thead>
      <tbody>
        {items_html}
        <tr class="grand-row"><td colspan="3">Grand Total</td><td>${grand_total:.2f}</td></tr>
      </tbody>
    </table>
    {f'<div style="margin-top:.85rem;padding:.75rem 1rem;background:#f0fdf4;border-radius:8px;display:flex;justify-content:space-between;font-size:.9rem"><span style="color:#166534;font-weight:600">✅ Amount Paid</span><span style="color:#166534;font-weight:700">${amount_paid:.2f}</span></div>' if amount_paid > 0 else ''}
    {f'<div style="margin-top:.5rem;padding:.75rem 1rem;background:#fff5f5;border-radius:8px;display:flex;justify-content:space-between;font-size:.9rem"><span style="color:#991b1b;font-weight:600">⚠️ Balance Due</span><span style="color:#991b1b;font-weight:700">${balance_due:.2f}</span></div>' if balance_due > 0.01 else ''}
  </div>

  <div style="text-align:center;color:#9ca3af;font-size:.8rem;padding:.5rem 0 1.5rem">
    {f'Questions? Call <strong style="color:#374151">{BUSINESS_PHONE}</strong> or reply to your confirmation email.' if BUSINESS_PHONE else 'Reply to your confirmation email with any questions.'}
    <br>This page is view-only. To make changes, please contact us directly.
  </div>

</div></body></html>"""
    return html


# ══════════════════════════════════════════════════════════════════════════════
#  ROUTES — ADMIN
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/admin", methods=["GET", "POST"])
def admin_login():
    if session.get("admin_logged_in"):
        return redirect(url_for("admin_dashboard"))
    error = None
    if request.method == "POST":
        if request.form.get("password") == ADMIN_PASSWORD:
            session["admin_logged_in"] = True
            return redirect(url_for("admin_dashboard"))
        error = "Incorrect password."
    return render_template_string(ADMIN_LOGIN_HTML,
                                  business_name=BUSINESS_NAME, error=error)


@app.route("/admin/logout")
def admin_logout():
    session.clear()
    return redirect(url_for("admin_login"))


@app.route("/admin/dashboard")
@admin_required
def admin_dashboard():
    status_filter   = request.args.get("status", "")
    date_from       = request.args.get("date_from", "")
    date_to         = request.args.get("date_to", "")
    pay_filter      = request.args.get("pay_filter", "")   # paid | partial | due | ""
    upcoming_filter = bool(request.args.get("upcoming", ""))
    archived_filter = bool(request.args.get("archived", ""))
    past_filter     = bool(request.args.get("past", ""))
    sort_by         = request.args.get("sort", "created")   # date | name | id | created
    conn = get_db()
    bookings = []
    stats = {"total": 0, "pending": 0, "accepted": 0, "confirmed": 0, "revenue": 0, "amount_due": 0, "upcoming": 0, "past": 0}
    inventory_status = []

    if conn:
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur.execute("SELECT COUNT(*) FROM bookings"); stats["total"] = cur.fetchone()[0]
            cur.execute("SELECT COUNT(*) FROM bookings WHERE status='pending'"); stats["pending"] = cur.fetchone()[0]
            cur.execute("SELECT COUNT(*) FROM bookings WHERE status='accepted'"); stats["accepted"] = cur.fetchone()[0]
            cur.execute("SELECT COUNT(*) FROM bookings WHERE status='confirmed'"); stats["confirmed"] = cur.fetchone()[0]
            cur.execute("SELECT COALESCE(SUM(grand_total),0) FROM bookings WHERE status='confirmed'")
            stats["revenue"] = float(cur.fetchone()[0])
            cur.execute("SELECT COALESCE(SUM(grand_total),0) FROM bookings WHERE status='accepted'")
            stats["amount_due"] = float(cur.fetchone()[0])
            # Count upcoming (next 8 days, non-cancelled/denied)
            today_dt = date.today()
            seven_days_ago = (today_dt - timedelta(days=7)).isoformat()
            in_8_days = (today_dt + timedelta(days=8)).isoformat()
            cur.execute("""
                SELECT COUNT(*) FROM bookings
                WHERE event_start_date >= %s AND event_start_date <= %s
                  AND status NOT IN ('cancelled','denied')
            """, (today_dt.isoformat(), in_8_days))
            stats["upcoming"] = cur.fetchone()[0]
            # Count past (older than 7 days ago)
            cur.execute("""
                SELECT COUNT(*) FROM bookings
                WHERE (event_start_date < %s OR event_start_date IS NULL)
                  AND (archived IS NULL OR archived = FALSE)
            """, (seven_days_ago,))
            stats["past"] = cur.fetchone()[0]

            # Build filtered query — filter on event_start_date (the date orders go out)
            wheres = []
            params = []
            if upcoming_filter:
                wheres.append("event_start_date >= %s"); params.append(today_dt.isoformat())
                wheres.append("event_start_date <= %s"); params.append(in_8_days)
                wheres.append("status NOT IN ('cancelled','denied')")
                wheres.append("(archived IS NULL OR archived = FALSE)")
            elif past_filter:
                wheres.append("(event_start_date < %s OR event_start_date IS NULL)")
                params.append(seven_days_ago)
                wheres.append("(archived IS NULL OR archived = FALSE)")
                if status_filter:
                    wheres.append("status=%s"); params.append(status_filter)
            elif archived_filter:
                wheres.append("archived = TRUE")
            else:
                wheres.append("(archived IS NULL OR archived = FALSE)")
                if status_filter:
                    # Status tab: show ALL bookings with that status, no date restriction
                    wheres.append("status=%s"); params.append(status_filter)
                else:
                    # Default "All" view: recent (past 7 days) + future only
                    wheres.append("(event_start_date >= %s OR event_start_date IS NULL)"); params.append(seven_days_ago)
                if date_from:
                    wheres.append("event_start_date >= %s"); params.append(date_from)
                if date_to:
                    wheres.append("event_start_date <= %s"); params.append(date_to)
            q = "SELECT * FROM bookings"
            if wheres:
                q += " WHERE " + " AND ".join(wheres)
            # Sort order
            sort_map = {
                "date":        "event_start_date ASC NULLS LAST, created_at DESC",
                "date_desc":   "event_start_date DESC NULLS LAST, created_at DESC",
                "name":        "full_name ASC",
                "name_desc":   "full_name DESC",
                "id":          "id DESC",
                "id_asc":      "id ASC",
                "total":       "grand_total DESC NULLS LAST",
                "created":     "created_at DESC",
                "created_asc": "created_at ASC",
            }
            q += " ORDER BY " + sort_map.get(sort_by, "event_start_date ASC NULLS LAST, created_at DESC")
            q += " LIMIT 1000"
            cur.execute(q, params)
            rows = cur.fetchall()
            _avatar_colors = ['#ef4444','#f97316','#eab308','#22c55e','#14b8a6',
                               '#3b82f6','#8b5cf6','#ec4899','#06b6d4','#84cc16']
            for row in rows:
                b = _row(row)
                items = json.loads(b.get("items_json") or "[]")
                b["items_summary"] = ", ".join(f"{i['qty']}x {i['name']}" for i in items[:2])
                if len(items) > 2:
                    b["items_summary"] += f" +{len(items)-2} more"
                # Payment label + class
                paid    = float(b.get("amount_paid") or 0)
                total   = float(b.get("grand_total") or 0)
                notes   = (b.get("notes") or "")

                # Try to pull paid amount from Booqable notes when amount_paid not set
                # Notes format: "Paid: $75.11 of $300.44"
                if paid == 0 and "Paid: $" in notes:
                    import re as _re
                    _m = _re.search(r'Paid: \$([0-9]+\.?[0-9]*)', notes)
                    if _m:
                        try:
                            paid = float(_m.group(1))
                        except Exception:
                            pass

                owed = round(total - paid, 2) if total > 0 else 0

                if b["status"] == "confirmed":
                    if "Payment: payment_due" in notes:
                        b["pay_label"], b["pay_class"] = "Payment Due", "pay-due"
                    elif paid > 0 and owed > 0.01:
                        b["pay_label"] = f"Partial — ${owed:,.2f} owed"
                        b["pay_class"] = "pay-partial"
                    elif paid > 0 or b.get("final_payment_link") is None:
                        b["pay_label"], b["pay_class"] = "Paid In Full", "pay-paid"
                    else:
                        # final_payment_link set but no amount_paid → estimate 75% remaining
                        est_owed = round(total * 0.75, 2)
                        b["pay_label"] = f"Partial — ${est_owed:,.2f} owed"
                        b["pay_class"] = "pay-partial"
                elif b["status"] == "accepted":
                    if paid > 0 and owed > 0.01:
                        b["pay_label"] = f"Partial — ${owed:,.2f} owed"
                        b["pay_class"] = "pay-partial"
                    else:
                        b["pay_label"], b["pay_class"] = "Payment Due", "pay-due"
                else:
                    b["pay_label"], b["pay_class"] = "—", "pay-none"
                # Apply pay_filter AFTER labelling
                if pay_filter:
                    if pay_filter == "paid" and b["pay_class"] != "pay-paid": continue
                    if pay_filter == "partial" and b["pay_class"] != "pay-partial": continue
                    if pay_filter == "due" and b["pay_class"] != "pay-due": continue
                # Google Maps URL for delivery address
                addr_parts = [p for p in [
                    (b.get("event_street") or "").strip(),
                    (b.get("event_city") or "").strip(),
                    (b.get("event_state") or "").strip(),
                    (b.get("event_zip") or "").strip()
                ] if p]
                if addr_parts:
                    b["maps_url"] = "https://www.google.com/maps/search/?api=1&query=" + urllib.parse.quote_plus(", ".join(addr_parts))
                else:
                    b["maps_url"] = ""
                # Avatar
                name = b.get("full_name") or "?"
                b["avatar_color"]    = _avatar_colors[ord(name[0].lower()) % len(_avatar_colors)]
                b["avatar_initials"] = name[0].upper()
                bookings.append(b)

            today_str = date.today().isoformat()
            avail = get_available(today_str, "2099-12-31")
            for p2 in get_products():
                reserved = p2["total"] - avail.get(p2["id"], p2["total"])
                inventory_status.append({
                    "name": p2["name"], "total": p2["total"],
                    "reserved": reserved, "available": avail.get(p2["id"], p2["total"])
                })

            cur.close()
            conn.close()
        except Exception as e:
            log.error(f"Admin dashboard error: {e}")

    inv_conflicts = get_inventory_conflicts()

    return render_template_string(ADMIN_DASH_HTML,
        business_name=BUSINESS_NAME,
        bookings=bookings,
        stats=stats,
        inventory=inventory_status,
        status_filter=status_filter,
        date_from=date_from,
        date_to=date_to,
        pay_filter=pay_filter,
        upcoming_filter=upcoming_filter,
        archived_filter=archived_filter,
        past_filter=past_filter,
        sort_by=sort_by,
        inv_conflicts=inv_conflicts,
    )


@app.route("/admin/booking/<int:booking_id>")
@admin_required
def admin_booking(booking_id):
    conn = get_db()
    b, items = None, []
    if conn:
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur.execute("SELECT * FROM bookings WHERE id=%s", (booking_id,))
            row = cur.fetchone()
            if row:
                b = _row(row)
                try:
                    items_raw = json.loads(b.get("items_json") or "[]")
                    items = items_raw if isinstance(items_raw, list) else []
                except Exception:
                    items = []
                # Auto-fill prices from inventory for items missing unit_price
                _prod_map = {p["name"].lower(): float(p.get("price") or 0) for p in get_products()}
                for item in items:
                    if not item.get("unit_price"):
                        price = _prod_map.get((item.get("name") or "").lower(), 0)
                        item["unit_price"] = price
                        item["total"] = round(price * int(item.get("qty") or 1), 2)
            cur.close()
            conn.close()
        except Exception as e:
            log.error(f"Booking fetch error: {e}")

    if not b:
        return "Booking not found", 404

    # Calculate days until event for payment label logic
    days_until = 999
    try:
        event_dt = datetime.strptime(str(b.get("event_start_date", ""))[:10], "%Y-%m-%d").date()
        days_until = (event_dt - date.today()).days
    except Exception:
        pass

    # Check for matching customer profile by name
    matched_customer = None
    try:
        conn2 = get_db()
        if conn2:
            cur2 = conn2.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur2.execute("""
                SELECT * FROM customers
                WHERE LOWER(TRIM(full_name)) = LOWER(TRIM(%s))
                LIMIT 1
            """, (b.get("full_name") or "",))
            crow = cur2.fetchone()
            cur2.close(); conn2.close()
            if crow:
                matched_customer = _row(crow)
    except Exception as e:
        log.error(f"Customer match lookup error: {e}")

    # Weekend residential schedule detection
    weekend_residential = None
    try:
        if (b.get("venue_type") or "").lower() == "residential":
            esd = str(b.get("event_start_date", ""))[:10]
            event_date = datetime.strptime(esd, "%Y-%m-%d").date()
            weekday = event_date.weekday()  # 5=Saturday, 6=Sunday
            if weekday == 5:  # Saturday
                friday = event_date - timedelta(days=1)
                sunday = event_date + timedelta(days=1)
                weekend_residential = {
                    "day_label": "Saturday",
                    "delivery_date": friday,
                    "delivery_label": f"Friday {friday.strftime('%b %-d')} at 4:00 PM",
                    "pickup_date": sunday,
                    "pickup_label": f"Sunday {sunday.strftime('%b %-d')} at 10:00 AM",
                    "pickup_weekday": "sunday",
                }
            elif weekday == 6:  # Sunday
                friday = event_date - timedelta(days=2)
                monday = event_date + timedelta(days=1)
                weekend_residential = {
                    "day_label": "Sunday",
                    "delivery_date": friday,
                    "delivery_label": f"Friday {friday.strftime('%b %-d')} at 4:00 PM",
                    "pickup_date": monday,
                    "pickup_label": f"Monday {monday.strftime('%b %-d')} at 10:00 AM",
                    "pickup_weekday": "monday",
                }
    except Exception:
        pass

    booking_inv_issues = get_booking_inventory_check(booking_id)

    # Fetch all confirmed/accepted booking date ranges for the calendar
    cal_bookings = []
    try:
        conn3 = get_db()
        if conn3:
            cur3 = conn3.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur3.execute("""
                SELECT id, full_name, event_start_date, event_end_date, status
                FROM bookings
                WHERE status IN ('confirmed','accepted')
                  AND event_start_date IS NOT NULL
                ORDER BY event_start_date
            """)
            for row in cur3.fetchall():
                r = _row(row)
                cal_bookings.append({
                    "id":    r["id"],
                    "name":  r.get("full_name",""),
                    "start": str(r.get("event_start_date",""))[:10],
                    "end":   str(r.get("event_end_date",""))[:10],
                    "status": r.get("status",""),
                })
            cur3.close(); conn3.close()
    except Exception as e:
        log.error(f"Calendar bookings fetch error: {e}")

    try:
        return render_template_string(ADMIN_BOOKING_HTML,
            business_name=BUSINESS_NAME, b=b, items=items, days_until=days_until,
            products=get_products(), payment_links=get_payment_links(booking_id),
            matched_customer=matched_customer, weekend_residential=weekend_residential,
            booking_inv_issues=booking_inv_issues,
            cal_bookings=cal_bookings)
    except Exception as e:
        log.error(f"Booking {booking_id} render error: {e}")
        return "Error rendering booking — please contact support.", 500


@app.route("/admin/booking/<int:booking_id>/accept", methods=["POST"])
@admin_required
def accept_booking(booking_id):
    """Accept booking: create Stripe payment link, email invoice + contract + link to customer."""
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_dashboard"))

    b = None
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("SELECT * FROM bookings WHERE id=%s", (booking_id,))
        row = cur.fetchone()
        cur.close()
        conn.close()
        if row:
            b = _row(row)
    except Exception as e:
        log.error(f"Accept fetch error: {e}")
        return redirect(url_for("admin_dashboard"))

    if not b:
        return "Booking not found", 404

    grand_total = float(b.get("grand_total") or 0)
    items = json.loads(b.get("items_json") or "[]")
    items_desc = ", ".join(f"{i['qty']}x {i['name']}" for i in items)

    # ── Determine payment type based on days until event ──────────────────
    event_date_raw = b.get("event_start_date")
    days_until = 999
    try:
        # Convert to string first — handles date objects, datetime objects, and strings
        event_dt = datetime.strptime(str(event_date_raw)[:10], "%Y-%m-%d").date()
        days_until = (event_dt - date.today()).days
        log.info(f"Booking #{booking_id}: event={event_dt}, today={date.today()}, days_until={days_until}")
    except Exception as e:
        log.error(f"Date calc error for booking #{booking_id}: {e} (raw={event_date_raw!r})")

    if days_until <= 7:
        # Event within 7 days — full payment required
        charge_amount  = round(grand_total, 2)
        payment_type   = "full"
        product_name   = f"Full Payment — Booking #{booking_id}"
        stripe_desc    = items_desc
        log.info(f"Booking #{booking_id}: {days_until} days away — requiring FULL payment ${charge_amount:.2f}")
    else:
        # More than 7 days away — 25% deposit
        charge_amount  = round(grand_total * DEPOSIT_PERCENT, 2)
        payment_type   = "deposit"
        product_name   = f"25% Deposit — Booking #{booking_id}"
        stripe_desc    = items_desc
        log.info(f"Booking #{booking_id}: {days_until} days away — requiring 25% deposit ${charge_amount:.2f}")

    # Override with admin-specified amount if provided
    try:
        custom = float(request.form.get("custom_amount") or 0)
        if custom > 0:
            charge_amount = round(custom, 2)
            product_name  = f"Payment — Booking #{booking_id}"
            log.info(f"Booking #{booking_id}: admin overrode charge to ${charge_amount:.2f}")
    except Exception:
        pass

    # Create Stripe Payment Link
    payment_link, plink_id, stripe_error = create_stripe_payment_link(
        booking_id, charge_amount, b.get("email"), stripe_desc, product_name
    )
    if stripe_error:
        log.warning(f"Stripe error for #{booking_id}: {stripe_error}")
    if payment_link:
        save_payment_link(booking_id, product_name, charge_amount, payment_link, plink_id)

    # Update DB: status -> accepted, store payment link
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute(
                "UPDATE bookings SET status='accepted', stripe_payment_link=%s WHERE id=%s",
                (payment_link, booking_id)
            )
            conn.commit()
            cur.close()
            conn.close()
            log.info(f"Booking #{booking_id} accepted ({payment_type})")
        except Exception as e:
            log.error(f"Accept DB update error: {e}")

    # Send acceptance email with invoice + contract + payment link
    b["stripe_payment_link"] = payment_link
    send_accepted_email(b, charge_amount, payment_type)

    return redirect(url_for("admin_booking", booking_id=booking_id))


@app.route("/admin/booking/<int:booking_id>/deny", methods=["POST"])
@admin_required
def deny_booking(booking_id):
    """Deny booking: send polite rejection email."""
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_dashboard"))
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("SELECT * FROM bookings WHERE id=%s", (booking_id,))
        row = cur.fetchone()
        if row:
            b = _row(row)
            cur2 = conn.cursor()
            cur2.execute("UPDATE bookings SET status='denied' WHERE id=%s", (booking_id,))
            conn.commit()
            cur2.close()
            send_denied_email(b)
            log.info(f"Booking #{booking_id} denied")
        cur.close()
        conn.close()
    except Exception as e:
        log.error(f"Deny error: {e}")
    return redirect(url_for("admin_dashboard"))


@app.route("/admin/booking/<int:booking_id>/confirm", methods=["POST"])
@admin_required
def confirm_booking(booking_id):
    """Manually confirm a booking (mark as paid) — locks inventory."""
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute("UPDATE bookings SET status='confirmed' WHERE id=%s", (booking_id,))
            conn.commit()
            cur2 = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur2.execute("SELECT * FROM bookings WHERE id=%s", (booking_id,))
            row = cur2.fetchone()
            cur2.close(); cur.close(); conn.close()
            if row:
                send_receipt_email(_row(row))
            log.info(f"Booking #{booking_id} manually confirmed")
        except Exception as e:
            log.error(f"Confirm error: {e}")
    return redirect(url_for("admin_dashboard"))


@app.route("/admin/booking/<int:booking_id>/cancel", methods=["POST"])
@admin_required
def cancel_booking(booking_id):
    """Cancel a booking — releases inventory."""
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute("UPDATE bookings SET status='cancelled' WHERE id=%s", (booking_id,))
            conn.commit()
            cur.close()
            conn.close()
            log.info(f"Booking #{booking_id} cancelled")
        except Exception as e:
            log.error(f"Cancel error: {e}")
    return redirect(url_for("admin_dashboard"))


@app.route("/admin/booking/<int:booking_id>/edit", methods=["GET", "POST"])
@admin_required
def edit_booking(booking_id):
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_dashboard"))
    if request.method == "GET":
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur.execute("SELECT * FROM bookings WHERE id=%s", (booking_id,))
            row = cur.fetchone()
            cur.close(); conn.close()
            if not row:
                return "Booking not found", 404
            b = _row(row)
        except Exception as e:
            log.error(f"Edit booking fetch: {e}")
            return redirect(url_for("admin_dashboard"))
        return render_template_string(ADMIN_BOOKING_EDIT_HTML, business_name=BUSINESS_NAME, b=b)
    # POST — save changes
    f = request.form
    fields = {
        "full_name":        f.get("full_name","").strip(),
        "company_name":     f.get("company_name","").strip(),
        "email":            f.get("email","").strip(),
        "phone":            f.get("phone","").strip(),
        "renter_street":    f.get("renter_street","").strip(),
        "renter_city":      f.get("renter_city","").strip(),
        "renter_state":     f.get("renter_state","").strip(),
        "renter_zip":       f.get("renter_zip","").strip(),
        "event_start_date": f.get("event_start_date","").strip() or None,
        "event_end_date":   f.get("event_end_date","").strip() or None,
        "event_start_time": f.get("event_start_time","").strip(),
        "event_end_time":   f.get("event_end_time","").strip(),
        "setup_time":       f.get("setup_time","").strip(),
        "venue_type":       f.get("venue_type","venue"),
        "event_street":     f.get("event_street","").strip(),
        "event_city":       f.get("event_city","").strip(),
        "event_state":      f.get("event_state","").strip(),
        "event_zip":        f.get("event_zip","").strip(),
        "delivery_location":f.get("delivery_location","").strip(),
        "status":           f.get("status","pending"),
        "grand_total":      float(f.get("grand_total") or 0),
        "amount_paid":      float(f.get("amount_paid") or 0),
        "delivery_fee":     float(f.get("delivery_fee") or 0),
        "late_night_fee":   float(f.get("late_night_fee") or 0),
        "distance_miles":   float(f.get("distance_miles") or 0) or None,
        "notes":            f.get("notes","").strip(),
    }
    try:
        cur = conn.cursor()
        cur.execute("""
            UPDATE bookings SET
              full_name=%(full_name)s, company_name=%(company_name)s,
              email=%(email)s, phone=%(phone)s,
              renter_street=%(renter_street)s, renter_city=%(renter_city)s,
              renter_state=%(renter_state)s, renter_zip=%(renter_zip)s,
              event_start_date=%(event_start_date)s, event_end_date=%(event_end_date)s,
              event_start_time=%(event_start_time)s, event_end_time=%(event_end_time)s,
              setup_time=%(setup_time)s, venue_type=%(venue_type)s,
              event_street=%(event_street)s, event_city=%(event_city)s,
              event_state=%(event_state)s, event_zip=%(event_zip)s,
              delivery_location=%(delivery_location)s,
              status=%(status)s, grand_total=%(grand_total)s,
              amount_paid=%(amount_paid)s, delivery_fee=%(delivery_fee)s,
              late_night_fee=%(late_night_fee)s, distance_miles=%(distance_miles)s,
              notes=%(notes)s
            WHERE id=%(id)s
        """, {**fields, "id": booking_id})
        conn.commit()
        cur.close(); conn.close()
    except Exception as e:
        log.error(f"Edit booking save: {e}")
    return redirect(url_for("admin_booking", booking_id=booking_id))


@app.route("/admin/booking/new", methods=["GET", "POST"])
@admin_required
def new_booking():
    if request.method == "GET":
        return render_template_string(ADMIN_NEW_BOOKING_HTML,
            business_name=BUSINESS_NAME, products=get_products())
    # POST — create booking
    f = request.form
    try:
        items_json_raw = f.get("items_json", "[]")
        try:
            items = json.loads(items_json_raw)
        except Exception:
            items = []
        items_subtotal = float(f.get("items_subtotal") or 0)
        delivery_fee   = float(f.get("delivery_fee") or 0)
        tax_exempt     = f.get("tax_exempt", "0") == "1"
        tax_rate       = 0.0 if tax_exempt else 0.0635
        taxable        = items_subtotal + delivery_fee
        tax_amount     = 0.0 if tax_exempt else round(taxable * tax_rate, 2)
        grand_total    = float(f.get("grand_total") or round(taxable + tax_amount, 2))
        amount_paid    = float(f.get("amount_paid") or 0)
        conn = get_db()
        if not conn:
            return "Database unavailable", 500
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO bookings (
                full_name, company_name, email, phone,
                event_start_date, event_end_date, event_start_time, event_end_time,
                venue_type, event_street, event_city, event_state, event_zip,
                delivery_location, status,
                items_json, items_subtotal, delivery_fee,
                tax_rate, tax_amount, tax_exempt,
                grand_total, amount_paid, notes,
                created_at
            ) VALUES (
                %s,%s,%s,%s, %s,%s,%s,%s, %s,%s,%s,%s,%s, %s,%s,
                %s,%s,%s, %s,%s,%s, %s,%s,%s, NOW()
            ) RETURNING id
        """, (
            f.get("full_name","").strip(),
            f.get("company_name","").strip() or None,
            f.get("email","").strip() or None,
            f.get("phone","").strip() or None,
            f.get("event_start_date","").strip() or None,
            f.get("event_end_date","").strip() or None,
            f.get("event_start_time","").strip() or None,
            f.get("event_end_time","").strip() or None,
            f.get("venue_type","other"),
            f.get("event_street","").strip() or None,
            f.get("event_city","").strip() or None,
            f.get("event_state","").strip() or None,
            f.get("event_zip","").strip() or None,
            f.get("delivery_location","").strip() or None,
            f.get("status","confirmed"),
            json.dumps(items), items_subtotal, delivery_fee,
            tax_rate, tax_amount, tax_exempt,
            grand_total, amount_paid,
            f.get("notes","").strip() or None,
        ))
        new_id = cur.fetchone()[0]
        conn.commit()
        cur.close(); conn.close()
        return redirect(url_for("admin_booking", booking_id=new_id))
    except Exception as e:
        log.error(f"New booking create error: {e}")
        return f"Error creating booking: {e}", 500


@app.route("/admin/booking/<int:booking_id>/update-items", methods=["POST"])
@admin_required
def update_booking_items(booking_id):
    names  = request.form.getlist("item_name")
    qtys   = request.form.getlist("item_qty")
    prices = request.form.getlist("item_price")
    while len(prices) < len(names):
        prices.append("0")

    # Build product price map as fallback
    _prod_map = {p["name"].lower(): float(p.get("price") or 0) for p in get_products()}
    items = []
    for name, qty, price in zip(names, qtys, prices):
        name = name.strip()
        if name:
            try:
                q = max(1, int(qty or 1))
            except Exception:
                q = 1
            try:
                up = float(price or 0)
            except Exception:
                up = 0
            if up == 0:
                up = _prod_map.get(name.lower(), 0)
            items.append({"name": name, "qty": q, "unit_price": up, "total": round(up * q, 2)})

    # Exact time delivery & delivery fee
    exact_time = bool(request.form.get("exact_time_delivery"))
    try:
        delivery_fee = round(float(request.form.get("delivery_fee") or 0), 2)
    except Exception:
        delivery_fee = 0.0

    # Recalculate all totals
    items_subtotal = round(sum(i["total"] for i in items), 2)
    exact_fee      = 175.0 if exact_time else 0.0
    pre_tax        = round(items_subtotal + delivery_fee + exact_fee, 2)

    conn = get_db()
    if conn:
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            # Fetch current discount info so we can reapply it
            cur.execute("SELECT discount_type, discount_value, tax_rate FROM bookings WHERE id=%s", (booking_id,))
            row = cur.fetchone()
            disc_type  = row["discount_type"]  if row else None
            disc_value = float(row["discount_value"] or 0) if row else 0.0
            tax_rate   = float(row["tax_rate"]  or 0.0635) if row else 0.0635

            # Reapply discount to full pre-tax total (items + fees)
            disc_amount = 0.0
            if disc_type == "percent" and disc_value > 0:
                disc_amount = round(pre_tax * disc_value / 100.0, 2)
            elif disc_type == "amount" and disc_value > 0:
                disc_amount = round(min(disc_value, pre_tax), 2)

            taxable    = round(pre_tax - disc_amount, 2)
            tax_amount = round(taxable * tax_rate, 2)
            grand_total = round(taxable + tax_amount, 2)

            cur2 = conn.cursor()
            cur2.execute("""
                UPDATE bookings SET
                    items_json=%s,
                    items_subtotal=%s,
                    exact_time_delivery=%s,
                    delivery_fee=%s,
                    discount_amount=%s,
                    tax_amount=%s,
                    grand_total=%s
                WHERE id=%s
            """, (json.dumps(items), items_subtotal, exact_time, delivery_fee,
                  disc_amount, tax_amount, grand_total, booking_id))
            conn.commit()
            cur.close(); cur2.close(); conn.close()
            log.info(f"Booking #{booking_id} items updated — subtotal ${items_subtotal}, total ${grand_total}")
        except Exception as e:
            log.error(f"Update items error: {e}")
    return redirect(url_for("admin_booking", booking_id=booking_id))


@app.route("/admin/booking/<int:booking_id>/sync-customer-profile", methods=["POST"])
@admin_required
def sync_customer_profile(booking_id):
    """Sync between booking info and matching customer profile."""
    action = request.form.get("action", "")
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_booking", booking_id=booking_id))
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("SELECT * FROM bookings WHERE id=%s", (booking_id,))
        brow = cur.fetchone()
        if not brow:
            cur.close(); conn.close()
            return redirect(url_for("admin_booking", booking_id=booking_id))
        b = _row(brow)
        cur.execute("SELECT * FROM customers WHERE LOWER(TRIM(full_name))=LOWER(TRIM(%s)) LIMIT 1",
                    (b.get("full_name") or "",))
        crow = cur.fetchone()
        if crow:
            mc = _row(crow)
            if action == "update_profile":
                # Push booking phone/email → customer profile
                cur2 = conn.cursor()
                cur2.execute("""
                    UPDATE customers SET
                      email = COALESCE(NULLIF(%s,''), email),
                      phone = COALESCE(NULLIF(%s,''), phone)
                    WHERE id=%s
                """, (b.get("email") or "", b.get("phone") or "", mc["id"]))
                conn.commit(); cur2.close()
                log.info(f"Customer profile {mc['id']} updated from booking #{booking_id}")
            elif action == "update_booking":
                # Pull customer profile phone/email → booking
                cur2 = conn.cursor()
                cur2.execute("""
                    UPDATE bookings SET
                      email = COALESCE(NULLIF(%s,''), email),
                      phone = COALESCE(NULLIF(%s,''), phone)
                    WHERE id=%s
                """, (mc.get("email") or "", mc.get("phone") or "", booking_id))
                conn.commit(); cur2.close()
                log.info(f"Booking #{booking_id} updated from customer profile {mc['id']}")
        cur.close(); conn.close()
    except Exception as e:
        log.error(f"Sync customer profile error: {e}")
    return redirect(url_for("admin_booking", booking_id=booking_id))


@app.route("/admin/booking/<int:booking_id>/send-receipt", methods=["POST"])
@admin_required
def admin_send_receipt(booking_id):
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur.execute("SELECT * FROM bookings WHERE id=%s", (booking_id,))
            row = cur.fetchone()
            cur.close(); conn.close()
            if row:
                send_receipt_email(_row(row))
                log.info(f"Manual receipt sent for #{booking_id}")
        except Exception as e:
            log.error(f"Send receipt error: {e}")
    return redirect(url_for("admin_booking", booking_id=booking_id))


@app.route("/admin/booking/<int:booking_id>/update-address", methods=["POST"])
@admin_required
def update_booking_address(booking_id):
    f = request.form
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute("""
                UPDATE bookings SET
                  renter_street=%s, renter_city=%s, renter_state=%s, renter_zip=%s
                WHERE id=%s
            """, (
                f.get("renter_street","").strip() or None,
                f.get("renter_city","").strip() or None,
                f.get("renter_state","").strip() or None,
                f.get("renter_zip","").strip() or None,
                booking_id
            ))
            conn.commit()
            cur.close(); conn.close()
        except Exception as e:
            log.error(f"Update address error: {e}")
    return redirect(url_for("admin_booking", booking_id=booking_id))


@app.route("/admin/booking/<int:booking_id>/admin-notes", methods=["POST"])
@admin_required
def update_admin_notes(booking_id):
    notes = (request.form.get("admin_notes") or "").strip()
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute("UPDATE bookings SET admin_notes=%s WHERE id=%s", (notes or None, booking_id))
            conn.commit()
            cur.close(); conn.close()
        except Exception as e:
            log.error(f"Admin notes update error: {e}")
    return redirect(url_for("admin_booking", booking_id=booking_id))


@app.route("/admin/booking/<int:booking_id>/apply-discount", methods=["POST"])
@admin_required
def apply_discount(booking_id):
    disc_type  = request.form.get("discount_type", "amount").strip()
    disc_value = float(request.form.get("discount_value") or 0)
    if disc_type not in ("amount", "percent") or disc_value <= 0:
        return redirect(url_for("admin_booking", booking_id=booking_id))

    conn = get_db()
    if not conn:
        return redirect(url_for("admin_booking", booking_id=booking_id))
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("SELECT * FROM bookings WHERE id=%s", (booking_id,))
        row = cur.fetchone()
        if not row:
            cur.close(); conn.close()
            return redirect(url_for("admin_booking", booking_id=booking_id))
        b = _row(row)

        items_subtotal = float(b.get("items_subtotal") or 0)
        delivery_fee   = float(b.get("delivery_fee")   or 0)
        exact_fee      = 175.0 if b.get("exact_time_delivery") else 0.0
        tax_rate       = float(b.get("tax_rate")       or 0.0635)
        tax_exempt     = bool(b.get("tax_exempt"))

        # Discount applies to full pre-tax total (items + fees)
        pre_tax_full = round(items_subtotal + delivery_fee + exact_fee, 2)
        if disc_type == "percent":
            disc_amount = round(pre_tax_full * (disc_value / 100.0), 2)
        else:
            disc_amount = round(min(disc_value, pre_tax_full), 2)

        taxable     = round(pre_tax_full - disc_amount, 2)
        tax_amount  = 0.0 if tax_exempt else round(taxable * tax_rate, 2)
        grand_total = round(taxable + tax_amount, 2)

        cur.execute("""
            UPDATE bookings
            SET discount_type=%s, discount_value=%s, discount_amount=%s,
                tax_amount=%s, grand_total=%s
            WHERE id=%s
        """, (disc_type, disc_value, disc_amount, tax_amount, grand_total, booking_id))
        conn.commit()
        cur.close(); conn.close()
    except Exception as e:
        log.error(f"Apply discount error: {e}")
    return redirect(url_for("admin_booking", booking_id=booking_id))


@app.route("/admin/booking/<int:booking_id>/remove-discount")
@admin_required
def remove_discount(booking_id):
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_booking", booking_id=booking_id))
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("SELECT * FROM bookings WHERE id=%s", (booking_id,))
        row = cur.fetchone()
        if not row:
            cur.close(); conn.close()
            return redirect(url_for("admin_booking", booking_id=booking_id))
        b = _row(row)

        # Restore grand total without discount
        items_subtotal = float(b.get("items_subtotal") or 0)
        delivery_fee   = float(b.get("delivery_fee")   or 0)
        exact_fee      = float(b.get("exact_time_fee") or 0)
        late_night_fee = float(b.get("late_night_fee") or 0)
        tax_rate       = float(b.get("tax_rate")       or 0.0635)
        tax_exempt     = bool(b.get("tax_exempt"))

        pre_tax    = round(items_subtotal + delivery_fee + exact_fee + late_night_fee, 2)
        tax_amount = 0.0 if tax_exempt else round(pre_tax * tax_rate, 2)
        grand_total = round(pre_tax + tax_amount, 2)

        cur.execute("""
            UPDATE bookings
            SET discount_type=NULL, discount_value=0, discount_amount=0,
                tax_amount=%s, grand_total=%s
            WHERE id=%s
        """, (tax_amount, grand_total, booking_id))
        conn.commit()
        cur.close(); conn.close()
    except Exception as e:
        log.error(f"Remove discount error: {e}")
    return redirect(url_for("admin_booking", booking_id=booking_id))


@app.route("/admin/booking/<int:booking_id>/apply-weekend-schedule", methods=["POST"])
@admin_required
def apply_weekend_schedule(booking_id):
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur.execute("SELECT event_start_date, event_start_time, event_end_date, event_end_time, venue_type, notes FROM bookings WHERE id=%s", (booking_id,))
            row = cur.fetchone()
            if row:
                venue_type = (row["venue_type"] or "").lower()
                event_date = row["event_start_date"]
                if not hasattr(event_date, "strftime"):
                    event_date = datetime.strptime(str(event_date)[:10], "%Y-%m-%d").date()
                weekday = event_date.weekday()
                if venue_type == "residential" and weekday in (5, 6):
                    friday = event_date - timedelta(days=1 if weekday == 5 else 2)
                    pickup_date = event_date + timedelta(days=1)  # Sunday or Monday
                    # Preserve original submitted dates in notes
                    orig_start = event_date.strftime("%A, %B %-d %Y")
                    orig_start_time = row["event_start_time"] or ""
                    orig_end = row["event_end_date"]
                    orig_end_str = ""
                    if orig_end:
                        if not hasattr(orig_end, "strftime"):
                            orig_end = datetime.strptime(str(orig_end)[:10], "%Y-%m-%d").date()
                        orig_end_str = f" – {orig_end.strftime('%A, %B %-d %Y')}"
                        if row["event_end_time"]:
                            orig_end_str += f" at {row['event_end_time']}"
                    schedule_note = (
                        f"[Original event date: {orig_start}"
                        + (f" at {orig_start_time}" if orig_start_time else "")
                        + orig_end_str + "]"
                    )
                    existing_notes = (row["notes"] or "").strip()
                    new_notes = (schedule_note + "\n" + existing_notes).strip()
                    cur.execute("""
                        UPDATE bookings SET
                          event_start_date=%s, event_start_time=%s,
                          event_end_date=%s, event_end_time=%s,
                          notes=%s
                        WHERE id=%s
                    """, (friday, "16:00", pickup_date, "10:00", new_notes, booking_id))
                    conn.commit()
            cur.close(); conn.close()
        except Exception as e:
            log.error(f"Apply weekend schedule error: {e}")
    return redirect(url_for("admin_booking", booking_id=booking_id))


@app.route("/admin/booking/<int:booking_id>/update-phone", methods=["POST"])
@admin_required
def update_booking_phone(booking_id):
    phone = (request.form.get("phone") or "").strip()
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute("UPDATE bookings SET phone=%s WHERE id=%s", (phone or None, booking_id))
            conn.commit()
            cur.close(); conn.close()
        except Exception as e:
            log.error(f"Update phone error: {e}")
    return redirect(url_for("admin_booking", booking_id=booking_id))


@app.route("/admin/booking/<int:booking_id>/custom-stripe-link", methods=["POST"])
@admin_required
def custom_stripe_link(booking_id):
    """Create a Stripe payment link for a custom amount and email it to the customer."""
    try:
        amount = float(request.form.get("amount") or 0)
    except Exception:
        amount = 0
    if amount <= 0:
        return redirect(url_for("admin_booking", booking_id=booking_id))

    label = (request.form.get("label") or "").strip() or f"Payment — Booking #{booking_id}"

    # Fetch booking for customer email / name
    b = None
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur.execute("SELECT * FROM bookings WHERE id=%s", (booking_id,))
            row = cur.fetchone()
            cur.close(); conn.close()
            if row:
                b = _row(row)
        except Exception as e:
            log.error(f"Custom link fetch error: {e}")

    if not b:
        return redirect(url_for("admin_booking", booking_id=booking_id))

    items_desc = ", ".join(f"{i['qty']}x {i['name']}" for i in json.loads(b.get("items_json") or "[]"))
    payment_link, plink_id, err = create_stripe_payment_link(booking_id, amount, b.get("email"), items_desc, label)

    if err:
        log.warning(f"Custom Stripe link error for #{booking_id}: {err}")
    if payment_link:
        save_payment_link(booking_id, label, amount, payment_link, plink_id)

    # Email the link to the customer
    if payment_link and b.get("email"):
        first = (b.get("full_name") or "").split()[0] or "there"
        subject = f"Payment Link — {label} | {BUSINESS_NAME}"
        html = f"""
<html><body style="font-family:-apple-system,sans-serif;background:#f0f4f8;padding:2rem 1rem">
<div style="max-width:560px;margin:0 auto;background:white;border-radius:12px;overflow:hidden;box-shadow:0 4px 20px rgba(0,0,0,.1)">
  <div style="background:linear-gradient(135deg,#1e40af,#2563eb);padding:1.5rem 2rem;color:white;text-align:center">
    <h2 style="margin:0;font-size:1.2rem">{BUSINESS_NAME}</h2>
    <p style="margin:.4rem 0 0;opacity:.88;font-size:.95rem">Payment Request</p>
  </div>
  <div style="padding:1.75rem 2rem">
    <p style="color:#2d3748;font-size:1.05rem;margin-bottom:.75rem">Hi <strong>{first}</strong>,</p>
    <p style="color:#4a5568;line-height:1.7;margin-bottom:1.5rem">
      A payment link has been created for your booking. Please use the button below to complete your payment.
    </p>
    <div style="background:#eff6ff;border:2px solid #bfdbfe;border-radius:12px;padding:1.5rem;text-align:center;margin-bottom:1.5rem">
      <p style="font-size:.85rem;color:#1d4ed8;font-weight:700;text-transform:uppercase;letter-spacing:.5px;margin:0 0 .3rem">{label}</p>
      <p style="font-size:2.75rem;font-weight:800;color:#1e40af;margin:.2rem 0 1rem;line-height:1">${amount:.2f}</p>
      <a href="{payment_link}"
         style="display:inline-block;background:linear-gradient(135deg,#1e40af,#2563eb);color:white;padding:1rem 2.5rem;border-radius:10px;font-weight:700;font-size:1.1rem;text-decoration:none">
        Pay ${amount:.2f} Now
      </a>
      <p style="margin:.6rem 0 0;font-size:.8rem;color:#6b7280">Secure payment powered by Stripe</p>
    </div>
    <p style="font-size:.85rem;color:#718096">Booking #{booking_id} &bull; {BUSINESS_NAME}</p>
  </div>
</div>
</body></html>"""
        plain = f"Hi {first},\n\nPayment of ${amount:.2f} is due for your booking.\n\nPay here: {payment_link}\n\n— {BUSINESS_NAME}"
        _send_email(b.get("email"), subject, html, plain)
        log.info(f"Custom payment link sent for #{booking_id}: ${amount:.2f}")

    link_param = urllib.parse.quote(payment_link or "", safe="")
    return redirect(url_for("admin_booking", booking_id=booking_id) + f"?custom_link={link_param}")


@app.route("/admin/payment-link/<int:link_id>/cancel", methods=["POST"])
@admin_required
def cancel_payment_link(link_id):
    """Deactivate a Stripe Payment Link and mark it cancelled in DB."""
    # Fetch the link record so we know booking_id and stripe_link_id
    conn = get_db()
    booking_id = None
    stripe_link_id = None
    if conn:
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur.execute("SELECT booking_id, stripe_link_id FROM payment_links WHERE id=%s", (link_id,))
            row = cur.fetchone()
            cur.close(); conn.close()
            if row:
                booking_id     = row["booking_id"]
                stripe_link_id = row["stripe_link_id"]
        except Exception as e:
            log.error(f"Cancel link fetch error: {e}")

    # Deactivate in Stripe
    if stripe_link_id and STRIPE_SECRET_KEY:
        try:
            stripe.PaymentLink.modify(stripe_link_id, active=False)
            log.info(f"Stripe link {stripe_link_id} deactivated")
        except Exception as e:
            log.warning(f"Stripe deactivate error for {stripe_link_id}: {e}")

    # Mark cancelled in DB
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute("UPDATE payment_links SET status='cancelled' WHERE id=%s", (link_id,))
            conn.commit()
            cur.close(); conn.close()
        except Exception as e:
            log.error(f"Cancel link DB error: {e}")

    if booking_id:
        return redirect(url_for("admin_booking", booking_id=booking_id))
    return redirect(url_for("admin_dashboard"))


@app.route("/admin/booking/<int:booking_id>/delete", methods=["POST"])
@admin_required
def delete_booking(booking_id):
    """Permanently delete a booking. Customer record in customers table is untouched."""
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute("DELETE FROM bookings WHERE id=%s", (booking_id,))
            conn.commit()
            cur.close()
            conn.close()
            log.info(f"Booking #{booking_id} permanently deleted")
        except Exception as e:
            log.error(f"Delete booking error: {e}")
    return redirect(url_for("admin_dashboard"))


@app.route("/admin/bookings/bulk-archive", methods=["POST"])
@admin_required
def bulk_archive_bookings():
    ids_raw = request.form.get("ids", "")
    ids = [int(i) for i in ids_raw.split(",") if i.strip().isdigit()]
    if ids:
        conn = get_db()
        if conn:
            try:
                cur = conn.cursor()
                cur.execute("UPDATE bookings SET archived=TRUE WHERE id = ANY(%s)", (ids,))
                conn.commit(); cur.close(); conn.close()
            except Exception as e:
                log.error(f"Bulk archive error: {e}")
    return redirect(url_for("admin_dashboard"))


@app.route("/admin/bookings/bulk-delete", methods=["POST"])
@admin_required
def bulk_delete_bookings():
    ids_raw = request.form.get("ids", "")
    ids = [int(i) for i in ids_raw.split(",") if i.strip().isdigit()]
    if ids:
        conn = get_db()
        if conn:
            try:
                cur = conn.cursor()
                cur.execute("DELETE FROM bookings WHERE id = ANY(%s)", (ids,))
                conn.commit(); cur.close(); conn.close()
            except Exception as e:
                log.error(f"Bulk delete error: {e}")
    return redirect(url_for("admin_dashboard"))


@app.route("/admin/booking/<int:booking_id>/archive", methods=["POST"])
@admin_required
def archive_booking(booking_id):
    """Hide a booking from the main list (soft delete). Can be viewed in Archived tab."""
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute("UPDATE bookings SET archived=TRUE WHERE id=%s", (booking_id,))
            conn.commit()
            cur.close()
            conn.close()
            log.info(f"Booking #{booking_id} archived")
        except Exception as e:
            log.error(f"Archive booking error: {e}")
    return redirect(url_for("admin_dashboard"))


@app.route("/admin/booking/<int:booking_id>/unarchive", methods=["POST"])
@admin_required
def unarchive_booking(booking_id):
    """Restore an archived booking back to the main list."""
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute("UPDATE bookings SET archived=FALSE WHERE id=%s", (booking_id,))
            conn.commit()
            cur.close()
            conn.close()
        except Exception as e:
            log.error(f"Unarchive booking error: {e}")
    return redirect(url_for("admin_dashboard", archived=1))


@app.route("/admin/booking/<int:booking_id>/delivery-status", methods=["POST"])
@admin_required
def booking_delivery_status(booking_id):
    """Advance delivery_status: None → delivered → picked_up."""
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute("SELECT delivery_status FROM bookings WHERE id=%s", (booking_id,))
            row = cur.fetchone()
            current = row[0] if row else None
            if current is None:
                new_status = "delivered"
            elif current == "delivered":
                new_status = "picked_up"
            else:
                new_status = current  # already picked_up, no change
            cur.execute("UPDATE bookings SET delivery_status=%s WHERE id=%s", (new_status, booking_id))
            conn.commit()
            cur.close()
            conn.close()
        except Exception as e:
            log.error(f"Delivery status error: {e}")
    # Return to wherever admin came from
    ref = request.referrer or url_for("admin_dashboard")
    return redirect(ref)


# ══════════════════════════════════════════════════════════════════════════════
#  ROUTES — STRIPE WEBHOOK
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/stripe/webhook", methods=["POST"])
def stripe_webhook():
    """
    Stripe sends this webhook when a payment is completed.
    Auto-confirms the booking so inventory gets locked.
    """
    payload    = request.get_data(as_text=False)
    sig_header = request.headers.get("Stripe-Signature", "")

    if STRIPE_WEBHOOK_SECRET:
        try:
            event = stripe.Webhook.construct_event(payload, sig_header, STRIPE_WEBHOOK_SECRET)
        except ValueError:
            log.error("Invalid Stripe webhook payload")
            return jsonify({"error": "Invalid payload"}), 400
        except stripe.error.SignatureVerificationError:
            log.error("Invalid Stripe webhook signature")
            return jsonify({"error": "Invalid signature"}), 400
    else:
        try:
            event = json.loads(payload)
        except Exception:
            return jsonify({"error": "Invalid JSON"}), 400

    if event.get("type") == "checkout.session.completed":
        sess = event["data"]["object"]
        if sess.get("payment_status") == "paid":
            booking_id = sess.get("metadata", {}).get("booking_id")
            if booking_id:
                conn = get_db()
                if conn:
                    try:
                        cur = conn.cursor()
                        cur.execute(
                            "UPDATE bookings SET status='confirmed', stripe_session_id=%s WHERE id=%s AND status='accepted'",
                            (sess.get("id"), int(booking_id))
                        )
                        conn.commit()
                        # Fetch booking for receipt
                        cur2 = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
                        cur2.execute("SELECT * FROM bookings WHERE id=%s", (int(booking_id),))
                        row = cur2.fetchone()
                        cur2.close()
                        cur.close()
                        conn.close()
                        if row:
                            send_receipt_email(_row(row))
                        log.info(f"Booking #{booking_id} auto-confirmed via Stripe webhook")
                    except Exception as e:
                        log.error(f"Webhook DB error: {e}")

    return jsonify({"status": "received"}), 200


# ══════════════════════════════════════════════════════════════════════════════
#  ROUTES — FINAL PAYMENT REMINDER
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/admin/booking/<int:booking_id>/send-final-reminder", methods=["POST"])
@admin_required
def send_final_reminder(booking_id):
    """Manually send final payment reminder from the admin panel."""
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_booking", booking_id=booking_id))

    b = None
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("SELECT * FROM bookings WHERE id=%s", (booking_id,))
        row = cur.fetchone()
        cur.close()
        conn.close()
        if row:
            b = _row(row)
    except Exception as e:
        log.error(f"Final reminder fetch error: {e}")
        return redirect(url_for("admin_booking", booking_id=booking_id))

    if not b:
        return "Booking not found", 404

    grand_total     = float(b.get("grand_total") or 0)
    remaining       = round(grand_total * 0.75, 2)
    # Override with admin-specified amount if provided
    try:
        custom = float(request.form.get("custom_amount") or 0)
        if custom > 0:
            remaining = round(custom, 2)
            log.info(f"Booking #{booking_id}: admin overrode final payment to ${remaining:.2f}")
    except Exception:
        pass
    items_list      = ", ".join(f"{i['qty']}x {i['name']}" for i in json.loads(b.get("items_json") or "[]"))
    product_name    = f"Final Payment — Booking #{booking_id}"

    payment_link, plink_id, err = create_stripe_payment_link(
        booking_id, remaining, b.get("email"), items_list, product_name
    )
    if err:
        log.warning(f"Stripe error for final payment #{booking_id}: {err}")
    if payment_link:
        save_payment_link(booking_id, product_name, remaining, payment_link, plink_id)

    # Save final payment link to DB
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute(
                "UPDATE bookings SET final_payment_link=%s, final_reminder_sent=TRUE WHERE id=%s",
                (payment_link, booking_id)
            )
            conn.commit()
            cur.close()
            conn.close()
        except Exception as e:
            log.error(f"Final reminder DB error: {e}")

    b["final_payment_link"] = payment_link
    send_final_payment_email(b, remaining, payment_link)
    log.info(f"Final payment reminder sent for booking #{booking_id}")
    return redirect(url_for("admin_booking", booking_id=booking_id))


ADMIN_CUSTOMERS_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <link rel="manifest" href="/manifest.json">
  <meta name="theme-color" content="#2563eb">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="default">
  <meta name="apple-mobile-web-app-title" content="Rent a Party">
  <link rel="apple-touch-icon" href="/icon-192.png">
  <script>if("serviceWorker"in navigator)navigator.serviceWorker.register("/sw.js");</script>
  <title>Customers — {{ business_name }}</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;background:#f5f6fa;color:#111827;min-height:100vh}
    .topbar{background:white;border-bottom:1px solid #e5e7eb;padding:.9rem 1.75rem;display:flex;justify-content:space-between;align-items:center;position:sticky;top:0;z-index:50}
    .topbar-brand{font-size:1rem;font-weight:700;color:#111827}
    .topbar-nav{display:flex;gap:.5rem;align-items:center}
    .nav-link{color:#6b7280;font-size:.85rem;font-weight:500;text-decoration:none;padding:.38rem .75rem;border-radius:6px;transition:all .12s}
    .nav-link:hover{background:#f3f4f6;color:#111827}
    .nav-link.active{background:#eff6ff;color:#2563eb;font-weight:600}
    .logout-btn{background:white;border:1px solid #d1d5db;color:#6b7280;padding:.38rem .85rem;border-radius:6px;font-size:.82rem;font-weight:500;text-decoration:none}
    .main{max-width:1100px;margin:0 auto;padding:1.75rem}
    .top-row{display:flex;justify-content:space-between;align-items:center;margin-bottom:1.25rem}
    .page-title{font-size:1.4rem;font-weight:700;color:#111827}
    .flash{padding:.75rem 1rem;border-radius:8px;margin-bottom:1.25rem;font-size:.9rem;font-weight:500}
    .flash-ok{background:#dcfce7;color:#166534;border:1px solid #bbf7d0}
    .flash-err{background:#fee2e2;color:#991b1b;border:1px solid #fecaca}

    /* Add form panel */
    .add-panel{background:white;border:1px solid #e5e7eb;border-radius:10px;padding:1.25rem 1.5rem;margin-bottom:1.5rem;display:none}
    .add-panel.open{display:block}
    .add-panel h3{font-size:.95rem;font-weight:700;color:#374151;margin-bottom:1rem}
    .form-grid{display:grid;grid-template-columns:1fr 1fr;gap:.75rem}
    .form-grid.three{grid-template-columns:1fr 1fr 1fr}
    .form-group{display:flex;flex-direction:column;gap:.3rem}
    .form-group label{font-size:.75rem;font-weight:600;color:#6b7280;text-transform:uppercase;letter-spacing:.4px}
    .form-group input,.form-group textarea{padding:.45rem .65rem;border:1px solid #d1d5db;border-radius:6px;font-size:.86rem;color:#111827;font-family:inherit}
    .form-group input:focus,.form-group textarea:focus{outline:none;border-color:#2563eb;box-shadow:0 0 0 2px rgba(37,99,235,.1)}
    .form-group textarea{resize:vertical;min-height:60px}
    .form-actions{display:flex;gap:.6rem;justify-content:flex-end;margin-top:.75rem}

    /* Table */
    .card{background:white;border:1px solid #e5e7eb;border-radius:10px;overflow:hidden}
    .card-header{padding:.85rem 1.25rem;background:#f9fafb;border-bottom:1px solid #e5e7eb;display:flex;justify-content:space-between;align-items:center}
    .card-title{font-weight:700;font-size:.88rem;color:#374151}
    table{width:100%;border-collapse:collapse}
    thead tr{background:#f9fafb}
    th{padding:.65rem 1rem;text-align:left;font-size:.72rem;font-weight:600;color:#9ca3af;text-transform:uppercase;letter-spacing:.5px;border-bottom:1px solid #e5e7eb}
    td{padding:.85rem 1rem;border-bottom:1px solid #f3f4f6;vertical-align:middle;font-size:.86rem}
    tr:last-child td{border-bottom:none}
    tbody tr:hover td{background:#fafafa}
    .avatar{width:34px;height:34px;border-radius:50%;display:inline-flex;align-items:center;justify-content:center;font-size:.8rem;font-weight:700;color:white;flex-shrink:0}
    .client-cell{display:flex;align-items:center;gap:.65rem}
    .client-name{font-weight:600;color:#111827}
    .client-company{font-size:.78rem;color:#9ca3af}
    .btn{display:inline-block;padding:.32rem .7rem;border-radius:6px;font-size:.78rem;font-weight:600;cursor:pointer;border:1px solid transparent;text-decoration:none;line-height:1.5;transition:all .12s}
    .btn-primary{background:#2563eb;color:white;border:none}
    .btn-primary:hover{background:#1d4ed8}
    .btn-outline{background:white;color:#374151;border-color:#d1d5db}
    .btn-outline:hover{background:#f3f4f6}
    .btn-edit{background:#eff6ff;color:#2563eb;border-color:#bfdbfe}
    .btn-edit:hover{background:#dbeafe}
    .btn-danger{background:#fef2f2;color:#991b1b;border-color:#fecaca}
    .btn-danger:hover{background:#fee2e2}
    .action-btns{display:flex;gap:.4rem}
    .empty-state{padding:3rem;text-align:center;color:#9ca3af}
    .search-box{padding:.45rem .75rem;border:1px solid #d1d5db;border-radius:7px;font-size:.86rem;width:220px}
    .search-box:focus{outline:none;border-color:#2563eb}
    @media(max-width:700px){.form-grid,.form-grid.three{grid-template-columns:1fr}.main{padding:1rem}}
  </style>
</head>
<body>
<div class="topbar">
  <div class="topbar-brand">🎉 {{ business_name }}</div>
  <div class="topbar-nav">
    <a href="/admin/dashboard" class="nav-link">Dashboard</a>
    <a href="/admin/inventory" class="nav-link">Inventory</a>
    <a href="/admin/customers" class="nav-link active">Customers</a>
    <a href="/admin/calendar" class="nav-link">📅 Calendar</a>
    <a href="/admin/route" class="nav-link">🗺 Route</a>
    <a href="/admin/logout" class="logout-btn">Sign Out</a>
  </div>
</div>
<div class="main">
  <div class="top-row">
    <div class="page-title">Customers</div>
    <div style="display:flex;gap:.6rem;align-items:center">
      <a href="/admin/customers/import" class="btn btn-outline">⬆ Import CSV</a>
      <button class="btn btn-primary" onclick="toggleAdd()">+ Add Customer</button>
    </div>
  </div>

  {% if flash_ok %}<div class="flash flash-ok">✓ {{ flash_ok }}</div>{% endif %}
  {% if flash_err %}<div class="flash flash-err">⚠ {{ flash_err }}</div>{% endif %}

  <!-- Add Customer Panel -->
  <div class="add-panel" id="addPanel">
    <h3>New Customer</h3>
    <form method="POST" action="/admin/customers/add">
      <div class="form-grid">
        <div class="form-group">
          <label>Full Name *</label>
          <input type="text" name="full_name" required>
        </div>
        <div class="form-group">
          <label>Company Name</label>
          <input type="text" name="company_name">
        </div>
        <div class="form-group">
          <label>Email</label>
          <input type="email" name="email">
        </div>
        <div class="form-group">
          <label>Phone</label>
          <input type="tel" name="phone">
        </div>
      </div>
      <div class="form-grid" style="margin-top:.75rem">
        <div class="form-group" style="grid-column:1/-1">
          <label>Street Address</label>
          <input type="text" name="street">
        </div>
        <div class="form-group">
          <label>City</label>
          <input type="text" name="city">
        </div>
        <div class="form-group three">
          <label>State</label>
          <input type="text" name="state" maxlength="2">
        </div>
        <div class="form-group three">
          <label>Zip</label>
          <input type="text" name="zip" maxlength="10">
        </div>
      </div>
      <div class="form-group" style="margin-top:.75rem">
        <label>Notes</label>
        <textarea name="notes" placeholder="Any notes about this customer..."></textarea>
      </div>
      <div style="margin-top:.75rem;padding:.75rem 1rem;background:#f0fdf4;border:1.5px solid #86efac;border-radius:8px">
        <label style="display:flex;align-items:center;gap:.6rem;cursor:pointer;font-weight:600;color:#166534;font-size:.95rem;text-transform:none;letter-spacing:0">
          <input type="checkbox" name="tax_exempt" value="1"
                 style="width:18px;height:18px;accent-color:#16a34a;cursor:pointer">
          Tax Exempt
        </label>
        <p style="margin:.3rem 0 0;font-size:.8rem;color:#4b7c5a">
          Check if this customer has a valid CT tax-exempt certificate. Tax (6.35%) will be removed from all their bookings.
        </p>
      </div>
      <div class="form-actions">
        <button type="button" class="btn btn-outline" onclick="toggleAdd()">Cancel</button>
        <button type="submit" class="btn btn-primary">Save Customer</button>
      </div>
    </form>
  </div>

  <!-- Customer List -->
  <div class="card">
    <div class="card-header">
      <span class="card-title">All Customers ({{ customers|length }})</span>
      <input class="search-box" type="text" id="searchBox" placeholder="Search name or email..." onkeyup="filterCustomers()">
    </div>
    {% if customers %}
    <table id="customerTable">
      <thead>
        <tr>
          <th>Customer</th>
          <th>Email</th>
          <th>Phone</th>
          <th>Location</th>
          <th>Orders</th>
          <th>Actions</th>
        </tr>
      </thead>
      <tbody>
        {% set avatar_colors = ['#ef4444','#f97316','#eab308','#22c55e','#14b8a6','#3b82f6','#8b5cf6','#ec4899','#06b6d4','#84cc16'] %}
        {% for c in customers %}
        {% set color = avatar_colors[loop.index0 % 10] %}
        <tr class="cust-row">
          <td>
            <div class="client-cell">
              <div class="avatar" style="background:{{ color }}">{{ (c.full_name or '?')[0]|upper }}</div>
              <div>
                <div class="client-name cust-name">{{ c.full_name }}</div>
                {% if c.company_name %}<div class="client-company">{{ c.company_name }}</div>{% endif %}
              </div>
            </div>
          </td>
          <td class="cust-email">
            <a href="mailto:{{ c.email }}" style="color:#2563eb;text-decoration:none">{{ c.email or '—' }}</a>
            {% if c.tax_exempt %}<span style="display:inline-block;margin-left:.4rem;font-size:.7rem;background:#dcfce7;color:#166534;border-radius:4px;padding:.1rem .4rem;font-weight:600">TAX EXEMPT</span>{% endif %}
          </td>
          <td><a href="tel:{{ c.phone }}" style="color:#374151;text-decoration:none">{{ c.phone or '—' }}</a></td>
          <td style="color:#6b7280;font-size:.82rem">
            {% if c.city %}{{ c.city }}{% if c.state %}, {{ c.state }}{% endif %}{% else %}—{% endif %}
          </td>
          <td>
            {% if c.bookings %}
            <div style="display:flex;flex-wrap:wrap;gap:.3rem">
              {% for b in c.bookings %}
              <a href="/admin/booking/{{ b.id }}"
                 style="display:inline-flex;align-items:center;gap:.25rem;padding:.2rem .5rem;border-radius:5px;font-size:.75rem;font-weight:600;text-decoration:none;
                        background:{% if b.status=='confirmed' %}#dcfce7;color:#166534{% elif b.status=='pending' %}#fef9c3;color:#854d0e{% elif b.status=='accepted' %}#dbeafe;color:#1e40af{% else %}#f3f4f6;color:#6b7280{% endif %}">
                #{{ b.id }}
              </a>
              {% endfor %}
            </div>
            {% else %}
            <span style="color:#9ca3af;font-size:.8rem">No orders</span>
            {% endif %}
          </td>
          <td>
            <div class="action-btns">
              <a href="/admin/customers/{{ c.id }}/edit" class="btn btn-edit">Edit</a>
              <form method="POST" action="/admin/customers/{{ c.id }}/delete" style="display:inline">
                <button class="btn btn-danger" onclick="return confirm('Remove {{ c.full_name }}?')">Remove</button>
              </form>
            </div>
          </td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
    {% else %}
    <div class="empty-state">No customers yet. Click "+ Add Customer" to get started.</div>
    {% endif %}
  </div>
</div>
<script>
function toggleAdd(){
  var p=document.getElementById('addPanel');
  p.classList.toggle('open');
  if(p.classList.contains('open')) p.querySelector('input').focus();
}
function filterCustomers(){
  var q=document.getElementById('searchBox').value.toLowerCase();
  document.querySelectorAll('.cust-row').forEach(function(row){
    var name=row.querySelector('.cust-name').textContent.toLowerCase();
    var email=row.querySelector('.cust-email').textContent.toLowerCase();
    row.style.display=(name.includes(q)||email.includes(q))?'':'none';
  });
}
</script>
</body></html>
"""

ADMIN_CUSTOMER_IMPORT_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <link rel="manifest" href="/manifest.json">
  <meta name="theme-color" content="#2563eb">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="default">
  <meta name="apple-mobile-web-app-title" content="Rent a Party">
  <link rel="apple-touch-icon" href="/icon-192.png">
  <script>if("serviceWorker"in navigator)navigator.serviceWorker.register("/sw.js");</script>
  <title>Import Customers — {{ business_name }}</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;background:#f5f6fa;color:#111827;min-height:100vh}
    .topbar{background:white;border-bottom:1px solid #e5e7eb;padding:.9rem 1.75rem;display:flex;justify-content:space-between;align-items:center;position:sticky;top:0;z-index:50}
    .topbar-brand{font-size:1rem;font-weight:700}
    .topbar-nav{display:flex;gap:.5rem;align-items:center}
    .nav-link{color:#6b7280;font-size:.85rem;font-weight:500;text-decoration:none;padding:.38rem .75rem;border-radius:6px}
    .nav-link:hover{background:#f3f4f6;color:#111827}
    .nav-link.active{background:#eff6ff;color:#2563eb;font-weight:600}
    .logout-btn{background:white;border:1px solid #d1d5db;color:#6b7280;padding:.38rem .85rem;border-radius:6px;font-size:.82rem;font-weight:500;text-decoration:none}
    .main{max-width:750px;margin:0 auto;padding:1.75rem}
    .breadcrumb{font-size:.82rem;color:#9ca3af;margin-bottom:1rem}
    .breadcrumb a{color:#2563eb;text-decoration:none}
    .page-title{font-size:1.3rem;font-weight:700;margin-bottom:.35rem}
    .page-sub{font-size:.88rem;color:#6b7280;margin-bottom:1.5rem}
    .flash{padding:.75rem 1rem;border-radius:8px;margin-bottom:1.25rem;font-size:.9rem;font-weight:500}
    .flash-ok{background:#dcfce7;color:#166534;border:1px solid #bbf7d0}
    .flash-err{background:#fee2e2;color:#991b1b;border:1px solid #fecaca}
    .card{background:white;border:1px solid #e5e7eb;border-radius:10px;padding:1.5rem;margin-bottom:1.25rem}
    .card h3{font-size:.9rem;font-weight:700;color:#374151;text-transform:uppercase;letter-spacing:.4px;margin-bottom:1rem;padding-bottom:.5rem;border-bottom:1px solid #f3f4f6}
    .step{display:flex;gap:1rem;margin-bottom:1rem;align-items:flex-start}
    .step-num{width:28px;height:28px;border-radius:50%;background:#2563eb;color:white;font-size:.82rem;font-weight:700;display:flex;align-items:center;justify-content:center;flex-shrink:0;margin-top:.1rem}
    .step-body{flex:1}
    .step-title{font-weight:600;font-size:.9rem;color:#111827;margin-bottom:.25rem}
    .step-desc{font-size:.84rem;color:#6b7280;line-height:1.5}
    code{background:#f3f4f6;padding:.15rem .4rem;border-radius:4px;font-size:.82rem;font-family:monospace}
    .template-box{background:#f8fafc;border:1px solid #e5e7eb;border-radius:7px;padding:.75rem 1rem;font-family:monospace;font-size:.78rem;color:#374151;overflow-x:auto;white-space:nowrap;margin:.5rem 0}
    .upload-area{border:2px dashed #d1d5db;border-radius:10px;padding:2rem;text-align:center;cursor:pointer;transition:all .15s;background:#fafafa}
    .upload-area:hover,.upload-area.drag{border-color:#2563eb;background:#eff6ff}
    .upload-icon{font-size:2rem;margin-bottom:.5rem}
    .upload-label{font-size:.9rem;font-weight:600;color:#374151;margin-bottom:.25rem}
    .upload-sub{font-size:.8rem;color:#9ca3af}
    input[type=file]{display:none}
    .btn{display:inline-block;padding:.5rem 1.1rem;border-radius:7px;font-size:.86rem;font-weight:600;cursor:pointer;border:none;text-decoration:none;transition:all .12s}
    .btn-primary{background:#2563eb;color:white}
    .btn-primary:hover{background:#1d4ed8}
    .btn-outline{background:white;color:#374151;border:1px solid #d1d5db}
    .btn-outline:hover{background:#f3f4f6}
    .btn-sm{padding:.3rem .7rem;font-size:.78rem}
    .actions{display:flex;gap:.75rem;margin-top:1.25rem;align-items:center}
    table{width:100%;border-collapse:collapse;font-size:.83rem;margin-top:.75rem}
    th{padding:.5rem .75rem;text-align:left;font-size:.72rem;font-weight:600;color:#9ca3af;text-transform:uppercase;border-bottom:1px solid #e5e7eb;background:#f9fafb}
    td{padding:.5rem .75rem;border-bottom:1px solid #f3f4f6;color:#374151}
  </style>
</head>
<body>
<div class="topbar">
  <div class="topbar-brand">🎉 {{ business_name }}</div>
  <div class="topbar-nav">
    <a href="/admin/dashboard" class="nav-link">Dashboard</a>
    <a href="/admin/inventory" class="nav-link">Inventory</a>
    <a href="/admin/customers" class="nav-link active">Customers</a>
    <a href="/admin/calendar" class="nav-link">📅 Calendar</a>
    <a href="/admin/route" class="nav-link">🗺 Route</a>
    <a href="/admin/logout" class="logout-btn">Sign Out</a>
  </div>
</div>
<div class="main">
  <div class="breadcrumb"><a href="/admin/customers">Customers</a> › Import</div>
  <div class="page-title">Import Customers from CSV</div>
  <div class="page-sub">Upload a spreadsheet of customers exported from Booqable or filled in manually.</div>

  {% if flash_ok %}<div class="flash flash-ok">✓ {{ flash_ok }}</div>{% endif %}
  {% if flash_err %}<div class="flash flash-err">⚠ {{ flash_err }}</div>{% endif %}
  {% if results %}
  <div class="flash flash-ok">
    ✓ Import complete — {{ results.added }} added, {{ results.updated }} updated, {{ results.skipped }} skipped.
  </div>
  {% endif %}

  <div class="card">
    <h3>How to Import</h3>
    <div class="step">
      <div class="step-num">1</div>
      <div class="step-body">
        <div class="step-title">Download the template</div>
        <div class="step-desc">
          Click below to download a CSV template with the correct column headers.
          <br><br>
          <a href="/admin/customers/import/template" class="btn btn-outline btn-sm">⬇ Download Template</a>
        </div>
      </div>
    </div>
    <div class="step">
      <div class="step-num">2</div>
      <div class="step-body">
        <div class="step-title">Fill it in</div>
        <div class="step-desc">
          Open the template in Google Sheets or Excel. Paste your Booqable customer names, emails, and phone numbers into the matching columns. The required columns are:
          <div class="template-box">full_name, email, phone, company_name, street, city, state, zip, notes</div>
          Only <code>full_name</code> is required. Everything else is optional.
        </div>
      </div>
    </div>
    <div class="step">
      <div class="step-num">3</div>
      <div class="step-body">
        <div class="step-title">Save as CSV and upload</div>
        <div class="step-desc">In Google Sheets: File → Download → CSV. In Excel: Save As → CSV. Then upload below.</div>
      </div>
    </div>
  </div>

  <div class="card">
    <h3>Upload CSV File</h3>
    <form method="POST" action="/admin/customers/import" enctype="multipart/form-data">
      <div class="upload-area" id="dropZone" onclick="document.getElementById('csvFile').click()"
           ondragover="event.preventDefault();this.classList.add('drag')"
           ondragleave="this.classList.remove('drag')"
           ondrop="event.preventDefault();this.classList.remove('drag');handleDrop(event)">
        <div class="upload-icon">📂</div>
        <div class="upload-label" id="uploadLabel">Click to choose a CSV file</div>
        <div class="upload-sub">or drag and drop here</div>
      </div>
      <input type="file" id="csvFile" name="csvfile" accept=".csv,text/csv" onchange="showFileName(this)">
      <div class="actions">
        <a href="/admin/customers" class="btn btn-outline">Cancel</a>
        <button type="submit" class="btn btn-primary">Import Customers</button>
      </div>
    </form>
  </div>

  {% if preview %}
  <div class="card">
    <h3>Preview (first 5 rows)</h3>
    <table>
      <thead><tr><th>Name</th><th>Email</th><th>Phone</th><th>City</th></tr></thead>
      <tbody>
        {% for r in preview %}
        <tr><td>{{ r.full_name }}</td><td>{{ r.email or '—' }}</td><td>{{ r.phone or '—' }}</td><td>{{ r.city or '—' }}</td></tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
  {% endif %}
</div>
<script>
function showFileName(input){
  if(input.files&&input.files[0]){
    document.getElementById('uploadLabel').textContent='Selected: '+input.files[0].name;
  }
}
function handleDrop(e){
  const file=e.dataTransfer.files[0];
  if(file){
    const dt=new DataTransfer();dt.items.add(file);
    const inp=document.getElementById('csvFile');
    inp.files=dt.files;
    showFileName(inp);
  }
}
</script>
</body></html>
"""

ADMIN_CUSTOMER_EDIT_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <link rel="manifest" href="/manifest.json">
  <meta name="theme-color" content="#2563eb">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="default">
  <meta name="apple-mobile-web-app-title" content="Rent a Party">
  <link rel="apple-touch-icon" href="/icon-192.png">
  <script>if("serviceWorker"in navigator)navigator.serviceWorker.register("/sw.js");</script>
  <title>Edit Customer — {{ business_name }}</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;background:#f5f6fa;color:#111827;min-height:100vh}
    .topbar{background:white;border-bottom:1px solid #e5e7eb;padding:.9rem 1.75rem;display:flex;justify-content:space-between;align-items:center;position:sticky;top:0;z-index:50}
    .topbar-brand{font-size:1rem;font-weight:700;color:#111827}
    .topbar-nav{display:flex;gap:.5rem;align-items:center}
    .nav-link{color:#6b7280;font-size:.85rem;font-weight:500;text-decoration:none;padding:.38rem .75rem;border-radius:6px}
    .nav-link:hover{background:#f3f4f6;color:#111827}
    .nav-link.active{background:#eff6ff;color:#2563eb;font-weight:600}
    .logout-btn{background:white;border:1px solid #d1d5db;color:#6b7280;padding:.38rem .85rem;border-radius:6px;font-size:.82rem;font-weight:500;text-decoration:none}
    .main{max-width:700px;margin:0 auto;padding:1.75rem}
    .breadcrumb{font-size:.82rem;color:#9ca3af;margin-bottom:1rem}
    .breadcrumb a{color:#2563eb;text-decoration:none}
    .page-title{font-size:1.3rem;font-weight:700;color:#111827;margin-bottom:1.5rem}
    .card{background:white;border:1px solid #e5e7eb;border-radius:10px;padding:1.5rem;margin-bottom:1.25rem}
    .card h3{font-size:.88rem;font-weight:700;color:#374151;text-transform:uppercase;letter-spacing:.4px;margin-bottom:1rem;padding-bottom:.5rem;border-bottom:1px solid #f3f4f6}
    .form-grid{display:grid;grid-template-columns:1fr 1fr;gap:.75rem}
    .form-group{display:flex;flex-direction:column;gap:.3rem}
    .form-group label{font-size:.75rem;font-weight:600;color:#6b7280;text-transform:uppercase;letter-spacing:.4px}
    .form-group input,.form-group textarea{padding:.45rem .65rem;border:1px solid #d1d5db;border-radius:6px;font-size:.86rem;color:#111827;font-family:inherit}
    .form-group input:focus,.form-group textarea:focus{outline:none;border-color:#2563eb;box-shadow:0 0 0 2px rgba(37,99,235,.1)}
    .form-group textarea{resize:vertical;min-height:70px}
    .form-actions{display:flex;gap:.75rem;margin-top:1.25rem}
    .btn{display:inline-block;padding:.5rem 1.1rem;border-radius:7px;font-size:.86rem;font-weight:600;cursor:pointer;border:none;text-decoration:none;transition:all .12s}
    .btn-primary{background:#2563eb;color:white}
    .btn-primary:hover{background:#1d4ed8}
    .btn-outline{background:white;color:#374151;border:1px solid #d1d5db}
    .btn-outline:hover{background:#f3f4f6}
    .btn-danger{background:#fee2e2;color:#991b1b;border:1px solid #fecaca}
    .span2{grid-column:1/-1}
    /* Recent bookings mini-table */
    .bookings-mini{width:100%;border-collapse:collapse;font-size:.84rem}
    .bookings-mini th{padding:.5rem .75rem;text-align:left;color:#9ca3af;font-size:.72rem;font-weight:600;text-transform:uppercase;border-bottom:1px solid #e5e7eb}
    .bookings-mini td{padding:.6rem .75rem;border-bottom:1px solid #f3f4f6;color:#374151}
    .bookings-mini tr:last-child td{border-bottom:none}
    .badge{display:inline-flex;padding:.2rem .55rem;border-radius:20px;font-size:.72rem;font-weight:600}
    .badge-pending{background:#fef9c3;color:#854d0e}
    .badge-accepted{background:#dbeafe;color:#1e40af}
    .badge-confirmed{background:#dcfce7;color:#166534}
    .badge-denied{background:#fee2e2;color:#991b1b}
    .badge-cancelled{background:#f3f4f6;color:#6b7280}
    @media(max-width:600px){.form-grid{grid-template-columns:1fr}.main{padding:1rem}}
  </style>
</head>
<body>
<div class="topbar">
  <div class="topbar-brand">🎉 {{ business_name }}</div>
  <div class="topbar-nav">
    <a href="/admin/dashboard" class="nav-link">Dashboard</a>
    <a href="/admin/inventory" class="nav-link">Inventory</a>
    <a href="/admin/customers" class="nav-link active">Customers</a>
    <a href="/admin/calendar" class="nav-link">📅 Calendar</a>
    <a href="/admin/route" class="nav-link">🗺 Route</a>
    <a href="/admin/logout" class="logout-btn">Sign Out</a>
  </div>
</div>
<div class="main">
  <div class="breadcrumb"><a href="/admin/customers">Customers</a> › Edit</div>
  <div class="page-title">{{ c.full_name }}</div>

  <div class="card">
    <h3>Contact Information</h3>
    <form method="POST" action="/admin/customers/{{ c.id }}/save">
      <div class="form-grid">
        <div class="form-group">
          <label>Full Name *</label>
          <input type="text" name="full_name" value="{{ c.full_name or '' }}" required>
        </div>
        <div class="form-group">
          <label>Company Name</label>
          <input type="text" name="company_name" value="{{ c.company_name or '' }}">
        </div>
        <div class="form-group">
          <label>Email</label>
          <input type="email" name="email" value="{{ c.email or '' }}">
        </div>
        <div class="form-group">
          <label>Phone</label>
          <input type="tel" name="phone" value="{{ c.phone or '' }}">
        </div>
        <div class="form-group span2">
          <label>Street Address</label>
          <input type="text" name="street" value="{{ c.street or '' }}">
        </div>
        <div class="form-group">
          <label>City</label>
          <input type="text" name="city" value="{{ c.city or '' }}">
        </div>
        <div class="form-group">
          <label>State</label>
          <input type="text" name="state" value="{{ c.state or '' }}" maxlength="2">
        </div>
        <div class="form-group">
          <label>Zip</label>
          <input type="text" name="zip" value="{{ c.zip or '' }}" maxlength="10">
        </div>
        <div class="form-group span2">
          <label>Notes</label>
          <textarea name="notes">{{ c.notes or '' }}</textarea>
        </div>
        <div class="form-group span2" style="padding:.75rem 1rem;background:#f0fdf4;border:1.5px solid #86efac;border-radius:8px">
          <label style="display:flex;align-items:center;gap:.6rem;cursor:pointer;font-weight:600;color:#166534;font-size:.95rem;text-transform:none;letter-spacing:0">
            <input type="checkbox" name="tax_exempt" value="1" {% if c.tax_exempt %}checked{% endif %}
                   style="width:18px;height:18px;accent-color:#16a34a;cursor:pointer">
            Tax Exempt
          </label>
          <p style="margin:.3rem 0 0;font-size:.8rem;color:#4b7c5a">
            Check if this customer has a valid CT tax-exempt certificate. Tax (6.35%) will be removed from all their bookings.
          </p>
        </div>
      </div>
      <div class="form-actions">
        <a href="/admin/customers" class="btn btn-outline">Cancel</a>
        <button type="submit" class="btn btn-primary">Save Changes</button>
        <form method="POST" action="/admin/customers/{{ c.id }}/delete" style="display:inline;margin:0">
          <button class="btn btn-danger" onclick="return confirm('Permanently remove {{ c.full_name }}?')">Remove Customer</button>
        </form>
      </div>
    </form>
  </div>

  {% if bookings %}
  <div class="card">
    <h3>Booking History ({{ bookings|length }})</h3>
    <table class="bookings-mini">
      <thead><tr><th>#</th><th>Event Date</th><th>Total</th><th>Status</th></tr></thead>
      <tbody>
        {% for b in bookings %}
        <tr>
          <td><a href="/admin/booking/{{ b.id }}" style="color:#2563eb;font-weight:600">#{{ b.id }}</a></td>
          <td>{{ b.event_start_date.strftime('%m/%d/%Y') if b.event_start_date else '' }}</td>
          <td>${{ "%.2f"|format(b.grand_total or 0) }}</td>
          <td><span class="badge badge-{{ b.status }}">{{ b.status|capitalize }}</span></td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
  {% endif %}
</div>
</body></html>
"""


# ══════════════════════════════════════════════════════════════════════════════
#  ROUTES — INVENTORY MANAGEMENT
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/admin/inventory")
@admin_required
def admin_inventory():
    products  = get_products()
    flash_ok  = request.args.get("ok",  "")
    flash_err = request.args.get("err", "")
    check_from = request.args.get("check_from", "")
    check_to   = request.args.get("check_to",   "")
    avail_data = []
    if check_from:
        end = check_to if check_to else check_from
        avail = get_available(check_from, end)
        for p in products:
            avail_qty = avail.get(p["id"], p["total"])
            avail_data.append({
                "name":      p["name"],
                "total":     p["total"],
                "available": avail_qty,
                "reserved":  p["total"] - avail_qty,
            })
    return render_template_string(ADMIN_INVENTORY_HTML,
        business_name=BUSINESS_NAME, products=products,
        flash_ok=flash_ok, flash_err=flash_err,
        check_from=check_from, check_to=check_to,
        avail_data=avail_data)


@app.route("/admin/inventory/save", methods=["POST"])
@admin_required
def admin_inventory_save():
    """Save all inventory edits submitted from the table form."""
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_inventory", err="Database unavailable"))
    try:
        count = int(request.form.get("count", 0))
        cur = conn.cursor()
        for i in range(count):
            pid   = request.form.get(f"id_{i}",    "").strip()
            name  = request.form.get(f"name_{i}",  "").strip()
            price = request.form.get(f"price_{i}", "0").strip()
            total = request.form.get(f"total_{i}", "0").strip()
            if not pid or not name:
                continue
            cur.execute(
                "UPDATE inventory SET name=%s, price=%s, total=%s WHERE id=%s",
                (name, float(price), int(total), pid)
            )
        conn.commit()
        cur.close()
        conn.close()
        log.info("Inventory updated via admin")
        return redirect(url_for("admin_inventory", ok="Inventory saved successfully!"))
    except Exception as e:
        log.error(f"Inventory save error: {e}")
        return redirect(url_for("admin_inventory", err=f"Save failed: {e}"))


@app.route("/admin/inventory/add", methods=["POST"])
@admin_required
def admin_inventory_add():
    """Add a new item to inventory."""
    name  = request.form.get("name",  "").strip()
    price = request.form.get("price", "0").strip()
    total = request.form.get("total", "0").strip()
    if not name:
        return redirect(url_for("admin_inventory", err="Item name is required"))
    # Generate a slug ID from the name
    import re
    slug = re.sub(r"[^a-z0-9]+", "_", name.lower()).strip("_")[:60]
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_inventory", err="Database unavailable"))
    try:
        cur = conn.cursor()
        # Get next sort_order
        cur.execute("SELECT COALESCE(MAX(sort_order),0)+1 FROM inventory")
        next_order = cur.fetchone()[0]
        # Ensure unique id
        base_slug = slug
        suffix = 1
        while True:
            cur.execute("SELECT 1 FROM inventory WHERE id=%s", (slug,))
            if not cur.fetchone():
                break
            slug = f"{base_slug}_{suffix}"
            suffix += 1
        cur.execute(
            "INSERT INTO inventory (id, name, price, total, sort_order) VALUES (%s, %s, %s, %s, %s)",
            (slug, name, float(price), int(total), next_order)
        )
        conn.commit()
        cur.close()
        conn.close()
        log.info(f"New inventory item added: {name} (id={slug})")
        return redirect(url_for("admin_inventory", ok=f'"{name}" added to inventory!'))
    except Exception as e:
        log.error(f"Inventory add error: {e}")
        return redirect(url_for("admin_inventory", err=f"Add failed: {e}"))


@app.route("/admin/inventory/delete/<item_id>", methods=["POST"])
@admin_required
def admin_inventory_delete(item_id):
    """Remove an item from inventory."""
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_inventory", err="Database unavailable"))
    try:
        cur = conn.cursor()
        cur.execute("SELECT name FROM inventory WHERE id=%s", (item_id,))
        row = cur.fetchone()
        name = row[0] if row else item_id
        cur.execute("DELETE FROM inventory WHERE id=%s", (item_id,))
        conn.commit()
        cur.close()
        conn.close()
        log.info(f"Inventory item deleted: {item_id}")
        return redirect(url_for("admin_inventory", ok=f'"{name}" removed from inventory.'))
    except Exception as e:
        log.error(f"Inventory delete error: {e}")
        return redirect(url_for("admin_inventory", err=f"Delete failed: {e}"))


# ══════════════════════════════════════════════════════════════════════════════
#  ROUTES — CUSTOMER MANAGEMENT
# ══════════════════════════════════════════════════════════════════════════════

_CUST_AVATAR_COLORS = ['#ef4444','#f97316','#eab308','#22c55e','#14b8a6',
                       '#3b82f6','#8b5cf6','#ec4899','#06b6d4','#84cc16']

@app.route("/admin/customers")
@admin_required
def admin_customers():
    customers = []
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur.execute("SELECT * FROM customers ORDER BY full_name")
            customers = [dict(r) for r in cur.fetchall()]
            # Attach bookings to each customer matched by email
            for c in customers:
                if c.get("email"):
                    cur.execute("""
                        SELECT id, event_start_date, grand_total, status
                        FROM bookings WHERE email=%s ORDER BY created_at DESC
                    """, (c["email"],))
                    c["bookings"] = [dict(r) for r in cur.fetchall()]
                else:
                    c["bookings"] = []
            cur.close()
            conn.close()
        except Exception as e:
            log.error(f"Customers list error: {e}")
    return render_template_string(ADMIN_CUSTOMERS_HTML,
        business_name=BUSINESS_NAME, customers=customers,
        flash_ok=request.args.get("ok", ""),
        flash_err=request.args.get("err", ""))


@app.route("/admin/customers/add", methods=["POST"])
@admin_required
def admin_customers_add():
    f = request.form
    full_name = f.get("full_name", "").strip()
    if not full_name:
        return redirect(url_for("admin_customers", err="Full name is required"))
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_customers", err="Database unavailable"))
    try:
        cur = conn.cursor()
        tax_exempt_val = f.get("tax_exempt") == "1"
        cur.execute("""
            INSERT INTO customers (full_name, company_name, email, phone, street, city, state, zip, notes, tax_exempt)
            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
        """, (
            full_name,
            f.get("company_name", "").strip() or None,
            f.get("email", "").strip() or None,
            f.get("phone", "").strip() or None,
            f.get("street", "").strip() or None,
            f.get("city", "").strip() or None,
            f.get("state", "").strip() or None,
            f.get("zip", "").strip() or None,
            f.get("notes", "").strip() or None,
            tax_exempt_val,
        ))
        conn.commit()
        cur.close()
        conn.close()
        log.info(f"Customer added: {full_name}")
        return redirect(url_for("admin_customers", ok=f'"{full_name}" added!'))
    except Exception as e:
        log.error(f"Customer add error: {e}")
        return redirect(url_for("admin_customers", err=f"Add failed: {e}"))


@app.route("/admin/customers/<int:customer_id>/edit")
@admin_required
def admin_customer_edit(customer_id):
    conn = get_db()
    c, bookings = None, []
    if conn:
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur.execute("SELECT * FROM customers WHERE id=%s", (customer_id,))
            row = cur.fetchone()
            if row:
                c = _row(row)
                # Load bookings by matching email
                if c.get("email"):
                    cur.execute(
                        "SELECT id, event_start_date, grand_total, status FROM bookings WHERE email=%s ORDER BY event_start_date DESC",
                        (c["email"],)
                    )
                    bookings = [dict(r) for r in cur.fetchall()]
            cur.close()
            conn.close()
        except Exception as e:
            log.error(f"Customer edit fetch error: {e}")
    if not c:
        return redirect(url_for("admin_customers", err="Customer not found"))
    return render_template_string(ADMIN_CUSTOMER_EDIT_HTML,
        business_name=BUSINESS_NAME, c=c, bookings=bookings)


@app.route("/admin/customers/<int:customer_id>/save", methods=["POST"])
@admin_required
def admin_customer_save(customer_id):
    f = request.form
    full_name = f.get("full_name", "").strip()
    if not full_name:
        return redirect(url_for("admin_customer_edit", customer_id=customer_id))
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_customers", err="Database unavailable"))
    try:
        cur = conn.cursor()
        tax_exempt_val = f.get("tax_exempt") == "1"
        cur.execute("""
            UPDATE customers SET full_name=%s, company_name=%s, email=%s, phone=%s,
                street=%s, city=%s, state=%s, zip=%s, notes=%s, tax_exempt=%s
            WHERE id=%s
        """, (
            full_name,
            f.get("company_name", "").strip() or None,
            f.get("email", "").strip() or None,
            f.get("phone", "").strip() or None,
            f.get("street", "").strip() or None,
            f.get("city", "").strip() or None,
            f.get("state", "").strip() or None,
            f.get("zip", "").strip() or None,
            f.get("notes", "").strip() or None,
            tax_exempt_val,
            customer_id,
        ))
        conn.commit()
        cur.close()
        conn.close()
        log.info(f"Customer #{customer_id} updated")
        return redirect(url_for("admin_customers", ok=f'"{full_name}" updated!'))
    except Exception as e:
        log.error(f"Customer save error: {e}")
        return redirect(url_for("admin_customers", err=f"Save failed: {e}"))


@app.route("/admin/customers/<int:customer_id>/delete", methods=["POST"])
@admin_required
def admin_customer_delete(customer_id):
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_customers", err="Database unavailable"))
    try:
        cur = conn.cursor()
        cur.execute("SELECT full_name FROM customers WHERE id=%s", (customer_id,))
        row = cur.fetchone()
        name = row[0] if row else "Customer"
        cur.execute("DELETE FROM customers WHERE id=%s", (customer_id,))
        conn.commit()
        cur.close()
        conn.close()
        log.info(f"Customer #{customer_id} deleted")
        return redirect(url_for("admin_customers", ok=f'"{name}" removed.'))
    except Exception as e:
        log.error(f"Customer delete error: {e}")
        return redirect(url_for("admin_customers", err=f"Delete failed: {e}"))


ADMIN_CALENDAR_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <link rel="manifest" href="/manifest.json">
  <meta name="theme-color" content="#2563eb">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="default">
  <meta name="apple-mobile-web-app-title" content="Rent a Party">
  <link rel="apple-touch-icon" href="/icon-192.png">
  <script>if("serviceWorker"in navigator)navigator.serviceWorker.register("/sw.js");</script>
  <title>Calendar — {{ business_name }}</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;background:#f5f6fa;color:#111827;min-height:100vh}
    .topbar{background:white;border-bottom:1px solid #e5e7eb;padding:.9rem 1.75rem;display:flex;justify-content:space-between;align-items:center;position:sticky;top:0;z-index:50}
    .topbar-brand{font-size:1rem;font-weight:700}
    .topbar-nav{display:flex;gap:.5rem;align-items:center}
    .nav-link{color:#6b7280;font-size:.85rem;font-weight:500;text-decoration:none;padding:.38rem .75rem;border-radius:6px}
    .nav-link:hover{background:#f3f4f6;color:#111827}
    .nav-link.active{background:#eff6ff;color:#2563eb;font-weight:600}
    .logout-btn{background:white;border:1px solid #d1d5db;color:#6b7280;padding:.38rem .85rem;border-radius:6px;font-size:.82rem;font-weight:500;text-decoration:none}
    .main{max-width:1100px;margin:0 auto;padding:1.5rem 1.25rem}
    .page-header{display:flex;justify-content:space-between;align-items:center;margin-bottom:1.25rem;flex-wrap:wrap;gap:.75rem}
    .page-title{font-size:1.3rem;font-weight:700}
    .cal-nav{display:flex;align-items:center;gap:.75rem}
    .cal-nav button{background:white;border:1px solid #d1d5db;color:#374151;padding:.35rem .75rem;border-radius:7px;font-size:.9rem;cursor:pointer;font-weight:600}
    .cal-nav button:hover{background:#f3f4f6}
    .cal-month{font-size:1.1rem;font-weight:700;color:#111827;min-width:160px;text-align:center}
    /* Legend */
    .legend{display:flex;gap:1rem;flex-wrap:wrap;margin-bottom:1rem}
    .leg-item{display:flex;align-items:center;gap:.4rem;font-size:.8rem;color:#374151;font-weight:500}
    .leg-dot{width:12px;height:12px;border-radius:3px;flex-shrink:0}
    /* Google Calendar sync box */
    .sync-box{background:white;border:1px solid #e5e7eb;border-radius:10px;padding:1rem 1.25rem;margin-bottom:1.25rem;display:flex;align-items:center;gap:1rem;flex-wrap:wrap}
    .sync-box img{width:24px;height:24px;flex-shrink:0}
    .sync-text{flex:1;min-width:200px}
    .sync-title{font-size:.88rem;font-weight:700;color:#111827;margin-bottom:.15rem}
    .sync-sub{font-size:.78rem;color:#6b7280}
    .sync-url{font-family:monospace;font-size:.75rem;background:#f3f4f6;padding:.3rem .6rem;border-radius:5px;color:#374151;word-break:break-all;flex:2;min-width:200px}
    .btn{display:inline-block;padding:.4rem .9rem;border-radius:7px;font-size:.82rem;font-weight:600;cursor:pointer;border:none;text-decoration:none;transition:all .12s}
    .btn-primary{background:#2563eb;color:white}
    .btn-primary:hover{background:#1d4ed8}
    .btn-outline{background:white;color:#374151;border:1px solid #d1d5db}
    .btn-outline:hover{background:#f3f4f6}
    /* Calendar grid */
    .cal-grid{background:white;border:1px solid #e5e7eb;border-radius:12px;overflow:hidden}
    .cal-days-header{display:grid;grid-template-columns:repeat(7,1fr);background:#f9fafb;border-bottom:1px solid #e5e7eb}
    .cal-day-name{padding:.55rem .5rem;text-align:center;font-size:.72rem;font-weight:700;color:#9ca3af;text-transform:uppercase;letter-spacing:.4px}
    .cal-cells{display:grid;grid-template-columns:repeat(7,1fr)}
    .cal-cell{border-right:1px solid #f3f4f6;border-bottom:1px solid #f3f4f6;min-height:110px;padding:.45rem .4rem;position:relative;cursor:default}
    .cal-cell:nth-child(7n){border-right:none}
    .cal-cell.other-month .cell-num{color:#d1d5db}
    .cal-cell.today{background:#eff6ff}
    .cal-cell.today .cell-num{background:#2563eb;color:white;border-radius:50%;width:24px;height:24px;display:flex;align-items:center;justify-content:center;font-weight:700}
    .cell-num{font-size:.8rem;font-weight:600;color:#374151;margin-bottom:.3rem;width:24px;height:24px;display:flex;align-items:center;justify-content:center}
    .event-chip{font-size:.68rem;font-weight:600;padding:.18rem .4rem;border-radius:4px;margin-bottom:.18rem;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;cursor:pointer;line-height:1.35;display:block}
    .event-chip:hover{opacity:.85;transform:translateY(-1px)}
    .chip-paid{background:#dcfce7;color:#166534}
    .chip-partial{background:#fef9c3;color:#854d0e}
    .chip-due{background:#fee2e2;color:#991b1b}
    .chip-pending{background:#dbeafe;color:#1e40af}
    .chip-cancelled{background:#f3f4f6;color:#6b7280}
    /* Modal */
    .modal-overlay{display:none;position:fixed;inset:0;background:rgba(0,0,0,.45);z-index:100;align-items:center;justify-content:center}
    .modal-overlay.open{display:flex}
    .modal{background:white;border-radius:12px;padding:1.5rem;max-width:420px;width:92%;box-shadow:0 20px 60px rgba(0,0,0,.18)}
    .modal-title{font-size:1rem;font-weight:700;margin-bottom:1rem;color:#111827}
    .modal-row{display:flex;justify-content:space-between;margin-bottom:.55rem;font-size:.86rem}
    .modal-label{color:#6b7280;font-weight:500}
    .modal-val{color:#111827;font-weight:600;text-align:right}
    .modal-close{margin-top:1rem;width:100%}
    @media(max-width:600px){.cal-cell{min-height:70px;padding:.3rem .2rem}.event-chip{font-size:.6rem}.sync-box{flex-direction:column;align-items:flex-start}}
  </style>
</head>
<body>
<div class="topbar">
  <div class="topbar-brand">🎉 {{ business_name }}</div>
  <div class="topbar-nav">
    <a href="/admin/dashboard" class="nav-link">Dashboard</a>
    <a href="/admin/inventory" class="nav-link">Inventory</a>
    <a href="/admin/customers" class="nav-link">Customers</a>
    <a href="/admin/calendar" class="nav-link active">📅 Calendar</a>
    <a href="/admin/route" class="nav-link">🗺 Route</a>
    <a href="/admin/logout" class="logout-btn">Sign Out</a>
  </div>
</div>

<div class="main">
  <div class="page-header">
    <div class="page-title">📅 Booking Calendar</div>
    <div class="cal-nav">
      <button onclick="changeMonth(-1)">‹</button>
      <div class="cal-month" id="calMonthLabel"></div>
      <button onclick="changeMonth(1)">›</button>
      <button onclick="goToday()" style="font-size:.78rem">Today</button>
    </div>
  </div>

  <!-- Google Calendar sync -->
  <div class="sync-box">
    <div style="font-size:1.3rem">📆</div>
    <div class="sync-text">
      <div class="sync-title">Sync with Google Calendar</div>
      <div class="sync-sub">Subscribe to this URL in Google Calendar to see all bookings automatically.</div>
    </div>
    <span class="sync-url" id="icsUrl">{{ ics_url }}</span>
    <button class="btn btn-outline" onclick="copyIcs()" style="white-space:nowrap" id="copyBtn">Copy URL</button>
    <a href="https://calendar.google.com/calendar/r/settings/addbyurl" target="_blank" class="btn btn-primary" style="white-space:nowrap">Open Google Calendar</a>
  </div>

  <!-- Filter toggles (click to show/hide each type) -->
  <div class="legend" style="margin-bottom:1rem">
    <span style="font-size:.75rem;font-weight:600;color:#9ca3af;text-transform:uppercase;letter-spacing:.4px;margin-right:.25rem">Show:</span>
    <div class="leg-item filter-btn active" data-filter="paid"      onclick="toggleFilter('paid')"      style="cursor:pointer;border:2px solid #22c55e;border-radius:20px;padding:.25rem .65rem;background:#dcfce7">
      <div class="leg-dot" style="background:#22c55e"></div>Paid In Full
    </div>
    <div class="leg-item filter-btn active" data-filter="partial"   onclick="toggleFilter('partial')"   style="cursor:pointer;border:2px solid #eab308;border-radius:20px;padding:.25rem .65rem;background:#fef9c3">
      <div class="leg-dot" style="background:#eab308"></div>Partially Paid
    </div>
    <div class="leg-item filter-btn active" data-filter="due"       onclick="toggleFilter('due')"       style="cursor:pointer;border:2px solid #ef4444;border-radius:20px;padding:.25rem .65rem;background:#fee2e2">
      <div class="leg-dot" style="background:#ef4444"></div>Payment Due
    </div>
    <div class="leg-item filter-btn active" data-filter="pending"   onclick="toggleFilter('pending')"   style="cursor:pointer;border:2px solid #3b82f6;border-radius:20px;padding:.25rem .65rem;background:#dbeafe">
      <div class="leg-dot" style="background:#3b82f6"></div>Pending
    </div>
    <div class="leg-item filter-btn active" data-filter="cancelled" onclick="toggleFilter('cancelled')" style="cursor:pointer;border:2px solid #d1d5db;border-radius:20px;padding:.25rem .65rem;background:#f3f4f6">
      <div class="leg-dot" style="background:#d1d5db"></div>Cancelled
    </div>
  </div>

  <!-- Calendar grid -->
  <div class="cal-grid">
    <div class="cal-days-header">
      <div class="cal-day-name">Sun</div><div class="cal-day-name">Mon</div>
      <div class="cal-day-name">Tue</div><div class="cal-day-name">Wed</div>
      <div class="cal-day-name">Thu</div><div class="cal-day-name">Fri</div>
      <div class="cal-day-name">Sat</div>
    </div>
    <div class="cal-cells" id="calCells"></div>
  </div>
</div>

<!-- Event detail modal -->
<div class="modal-overlay" id="modal" onclick="if(event.target===this)closeModal()">
  <div class="modal">
    <div class="modal-title" id="modalTitle"></div>
    <div id="modalBody"></div>
    <button class="btn btn-outline modal-close" onclick="closeModal()">Close</button>
  </div>
</div>

<script>
var bookings = {{ bookings_json | safe }};
var today = new Date();
var curYear = today.getFullYear();
var curMonth = today.getMonth();

var MONTHS = ["January","February","March","April","May","June","July","August","September","October","November","December"];

// Active filters — all on by default
var activeFilters = {paid:true, partial:true, due:true, pending:true, cancelled:true};

function payType(b){
  if(b.status==='confirmed') return b.final_payment_link ? 'partial' : 'paid';
  if(b.status==='accepted') return 'due';
  if(b.status==='pending') return 'pending';
  return 'cancelled';
}
function payClass(b){
  var t = payType(b);
  if(t==='paid')     return 'chip-paid';
  if(t==='partial')  return 'chip-partial';
  if(t==='due')      return 'chip-due';
  if(t==='pending')  return 'chip-pending';
  return 'chip-cancelled';
}
function payLabel(b){
  var t = payType(b);
  if(t==='paid')    return '✅ Paid';
  if(t==='partial') return '⚡ Partial';
  if(t==='due')     return '💰 Due';
  if(t==='pending') return '⏳ Pending';
  return b.status;
}

function toggleFilter(key){
  activeFilters[key] = !activeFilters[key];
  var btn = document.querySelector('[data-filter="'+key+'"]');
  if(activeFilters[key]){
    btn.classList.add('active');
    btn.style.opacity = '1';
  } else {
    btn.classList.remove('active');
    btn.style.opacity = '0.35';
  }
  renderCalendar();
}

function renderCalendar(){
  document.getElementById('calMonthLabel').textContent = MONTHS[curMonth] + ' ' + curYear;
  var cells = document.getElementById('calCells');
  cells.innerHTML = '';

  var firstDay = new Date(curYear, curMonth, 1).getDay();
  var daysInMonth = new Date(curYear, curMonth+1, 0).getDate();
  var prevDays = new Date(curYear, curMonth, 0).getDate();

  // Build a map: "YYYY-MM-DD" -> [bookings] — respect active filters
  var map = {};
  bookings.forEach(function(b){
    if(!activeFilters[payType(b)]) return;   // skip if filtered out
    var s = new Date(b.event_start_date + 'T00:00:00');
    var e = new Date((b.event_end_date || b.event_start_date) + 'T00:00:00');
    for(var d = new Date(s); d <= e; d.setDate(d.getDate()+1)){
      var key = d.toISOString().slice(0,10);
      if(!map[key]) map[key] = [];
      map[key].push(b);
    }
  });

  var totalCells = Math.ceil((firstDay + daysInMonth) / 7) * 7;
  for(var i = 0; i < totalCells; i++){
    var cell = document.createElement('div');
    cell.className = 'cal-cell';
    var day, month, year, isOther = false;
    if(i < firstDay){
      day = prevDays - firstDay + i + 1;
      month = curMonth - 1; year = curYear;
      if(month < 0){month=11;year--;}
      isOther = true;
    } else if(i >= firstDay + daysInMonth){
      day = i - firstDay - daysInMonth + 1;
      month = curMonth + 1; year = curYear;
      if(month > 11){month=0;year++;}
      isOther = true;
    } else {
      day = i - firstDay + 1;
      month = curMonth; year = curYear;
    }
    if(isOther) cell.classList.add('other-month');
    var isToday = !isOther && day===today.getDate() && curMonth===today.getMonth() && curYear===today.getFullYear();
    if(isToday) cell.classList.add('today');

    var numEl = document.createElement('div');
    numEl.className = 'cell-num';
    numEl.textContent = day;
    cell.appendChild(numEl);

    var dateKey = year+'-'+String(month+1).padStart(2,'0')+'-'+String(day).padStart(2,'0');
    var dayBookings = map[dateKey] || [];
    var shown = dayBookings.slice(0,3);
    shown.forEach(function(b){
      var chip = document.createElement('span');
      chip.className = 'event-chip ' + payClass(b);
      chip.textContent = payLabel(b) + ' ' + b.full_name.split(' ')[0];
      chip.title = b.full_name;
      chip.onclick = function(){ showModal(b); };
      cell.appendChild(chip);
    });
    if(dayBookings.length > 3){
      var more = document.createElement('span');
      more.style.cssText = 'font-size:.65rem;color:#9ca3af;padding:.1rem .3rem;display:block';
      more.textContent = '+' + (dayBookings.length-3) + ' more';
      cell.appendChild(more);
    }
    cells.appendChild(cell);
  }
}

function changeMonth(delta){
  curMonth += delta;
  if(curMonth > 11){curMonth=0;curYear++;}
  if(curMonth < 0){curMonth=11;curYear--;}
  renderCalendar();
}
function goToday(){curYear=today.getFullYear();curMonth=today.getMonth();renderCalendar();}

function fmtD(s){if(!s)return '';var p=s.split('-');return p.length===3?p[1]+'/'+p[2]+'/'+p[0]:s;}

function showModal(b){
  document.getElementById('modalTitle').textContent = '#'+b.id+' — '+b.full_name;
  var rows = [
    ['Dates', fmtD(b.event_start_date) + (b.event_end_date&&b.event_end_date!==b.event_start_date?' → '+fmtD(b.event_end_date):'')],
    ['Status', b.status.charAt(0).toUpperCase()+b.status.slice(1)],
    ['Payment', b.status==='confirmed'?(b.amount_paid>0&&b.amount_paid<b.grand_total-0.01?'Partial — $'+(b.grand_total-b.amount_paid).toFixed(2)+' owed':(b.final_payment_link?'Partially Paid':'Paid In Full')):(b.status==='accepted'?'Payment Due':'—')],
    ['Total', '$'+parseFloat(b.grand_total||0).toFixed(2)],
    ['Email', b.email||'—'],
    ['Phone', b.phone||'—'],
  ];
  var html = rows.map(function(r){
    return '<div class="modal-row"><span class="modal-label">'+r[0]+'</span><span class="modal-val">'+r[1]+'</span></div>';
  }).join('');
  html += '<div style="margin-top:.75rem"><a href="/admin/booking/'+b.id+'" class="btn btn-primary" style="display:block;text-align:center">View Full Booking →</a></div>';
  document.getElementById('modalBody').innerHTML = html;
  document.getElementById('modal').classList.add('open');
}
function closeModal(){ document.getElementById('modal').classList.remove('open'); }

function copyIcs(){
  var url = document.getElementById('icsUrl').textContent.trim();
  navigator.clipboard.writeText(url).then(function(){
    var btn = document.getElementById('copyBtn');
    btn.textContent = '✓ Copied!';
    btn.style.background = '#dcfce7';
    btn.style.color = '#166534';
    setTimeout(function(){btn.textContent='Copy URL';btn.style.background='';btn.style.color='';},2000);
  });
}

renderCalendar();
</script>
</body></html>
"""

@app.route("/admin/customers/import", methods=["GET"])
@admin_required
def admin_customers_import():
    return render_template_string(ADMIN_CUSTOMER_IMPORT_HTML,
        business_name=BUSINESS_NAME,
        flash_ok=request.args.get("ok"),
        flash_err=request.args.get("err"),
        results=None, preview=None)


@app.route("/admin/customers/import", methods=["POST"])
@admin_required
def admin_customers_import_post():
    import io, csv as csv_module
    f = request.files.get("csvfile")
    if not f or f.filename == "":
        return redirect(url_for("admin_customers_import", err="No file selected."))

    try:
        stream = io.StringIO(f.stream.read().decode("utf-8-sig"), newline=None)
        reader = csv_module.DictReader(stream)
    except Exception as e:
        return redirect(url_for("admin_customers_import", err=f"Could not read file: {e}"))

    # Normalise header names (strip whitespace, lowercase)
    FIELD_MAP = {
        "full_name": ["full_name", "name", "customer name", "fullname", "full name"],
        "company_name": ["company_name", "company", "business", "company name"],
        "email": ["email", "email address", "e-mail"],
        "phone": ["phone", "phone number", "mobile", "cell"],
        "street": ["street", "address", "street address", "addr"],
        "city": ["city"],
        "state": ["state", "province"],
        "zip": ["zip", "postal code", "postcode", "zip code"],
        "notes": ["notes", "note", "comments", "comment"],
    }

    def find_col(headers, candidates):
        h_lower = {h.strip().lower(): h for h in headers}
        for c in candidates:
            if c in h_lower:
                return h_lower[c]
        return None

    rows_parsed = []
    errors_out = []
    conn = get_db()
    if not conn:
        return redirect(url_for("admin_customers_import", err="Database unavailable."))

    headers = reader.fieldnames or []
    name_col    = find_col(headers, FIELD_MAP["full_name"])
    company_col = find_col(headers, FIELD_MAP["company_name"])
    email_col   = find_col(headers, FIELD_MAP["email"])
    phone_col   = find_col(headers, FIELD_MAP["phone"])
    street_col  = find_col(headers, FIELD_MAP["street"])
    city_col    = find_col(headers, FIELD_MAP["city"])
    state_col   = find_col(headers, FIELD_MAP["state"])
    zip_col     = find_col(headers, FIELD_MAP["zip"])
    notes_col   = find_col(headers, FIELD_MAP["notes"])

    if not name_col:
        return redirect(url_for("admin_customers_import",
                                err="Could not find a 'name' column in your CSV."))

    for i, row in enumerate(reader, start=2):
        full_name = row.get(name_col, "").strip()
        if not full_name:
            continue
        rows_parsed.append({
            "full_name":    full_name,
            "company_name": row.get(company_col, "").strip() if company_col else None,
            "email":        row.get(email_col, "").strip() if email_col else None,
            "phone":        row.get(phone_col, "").strip() if phone_col else None,
            "street":       row.get(street_col, "").strip() if street_col else None,
            "city":         row.get(city_col, "").strip() if city_col else None,
            "state":        row.get(state_col, "").strip() if state_col else None,
            "zip":          row.get(zip_col, "").strip() if zip_col else None,
            "notes":        row.get(notes_col, "").strip() if notes_col else None,
        })

    if not rows_parsed:
        return redirect(url_for("admin_customers_import", err="No valid rows found in CSV."))

    try:
        cur = conn.cursor()
        upserted = 0
        for r in rows_parsed:
            cur.execute("""
                INSERT INTO customers (full_name, company_name, email, phone, street, city, state, zip, notes)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                ON CONFLICT (email) WHERE email IS NOT NULL DO UPDATE SET
                    full_name    = EXCLUDED.full_name,
                    company_name = EXCLUDED.company_name,
                    phone        = EXCLUDED.phone,
                    street       = EXCLUDED.street,
                    city         = EXCLUDED.city,
                    state        = EXCLUDED.state,
                    zip          = EXCLUDED.zip,
                    notes        = EXCLUDED.notes
            """, (r.get("full_name"), r.get("company_name") or None,
                  r.get("email") or None, r.get("phone") or None,
                  r.get("street") or None, r.get("city") or None,
                  r.get("state") or None, r.get("zip") or None,
                  r.get("notes") or None))
            upserted += 1
        conn.commit()
        cur.close()
        conn.close()
        return redirect(url_for("admin_customers", ok=f"{upserted} customer(s) imported successfully!"))
    except Exception as e:
        log.error(f"CSV import DB error: {e}")
        return redirect(url_for("admin_customers_import", err=f"Database error: {e}"))


@app.route("/admin/customers/import/template")
@admin_required
def admin_customers_import_template():
    from flask import Response as _R
    csv_bytes = b"full_name,company_name,email,phone,street,city,state,zip,notes\n"
    return _R(csv_bytes, mimetype="text/csv",
              headers={"Content-Disposition": "attachment; filename=customers_template.csv"})


# ── Booqable Phone Sync ───────────────────────────────────────

@app.route("/admin/booqable-sync", methods=["GET", "POST"])
@admin_required
def booqable_sync():
    """Pull phone numbers from Booqable API and update matching bookings/customers."""
    result = None
    last_token  = ""
    last_tenant = "eminent-rental"
    if request.method == "POST":
        token    = (request.form.get("token") or "").strip()
        tenant   = (request.form.get("tenant") or "eminent-rental").strip()
        last_token  = token
        last_tenant = tenant
        # Strip full domain if user pasted the whole URL or domain
        tenant = tenant.replace("https://", "").replace("http://", "")
        tenant = tenant.split(".booqable.com")[0].split("/")[0]
        if not token:
            result = {"error": "Bearer token is required."}
        else:
            updated = 0
            errors  = []
            debug_info = []
            try:
                headers = {"Authorization": f"Bearer {token}",
                           "Content-Type": "application/json"}
                base = f"https://{tenant}.booqable.com/api/boomerang"
                # Use orders?include=customer — orders endpoint works with this token
                page = 1
                email_phone = {}  # email -> phone
                while True:
                    r = requests.get(f"{base}/orders",
                                     headers=headers,
                                     params={"page[number]": page, "page[per]": 100,
                                             "include": "customer"},
                                     timeout=15)
                    debug_info.append(f"Page {page}: HTTP {r.status_code}")
                    if r.status_code != 200:
                        errors.append(f"Orders API error {r.status_code}: {r.text[:400]}")
                        break
                    try:
                        rjson = r.json()
                    except Exception:
                        errors.append(f"Bad JSON: {r.text[:200]}")
                        break
                    orders = rjson.get("data", [])
                    included = rjson.get("included", [])
                    debug_info.append(f"  → {len(orders)} orders, {len(included)} included records")
                    # Extract customer phone from included records
                    for inc in included:
                        if inc.get("type") == "customers":
                            attrs = inc.get("attributes", {})
                            email = (attrs.get("email") or "").strip().lower()
                            phone = (attrs.get("phone") or attrs.get("mobile_phone") or "").strip()
                            if email and phone:
                                email_phone[email] = phone
                    if len(orders) < 100:
                        break
                    page += 1

                debug_info.append(f"Unique emails with phone: {len(email_phone)}")

                # Update bookings + customers tables
                conn = get_db()
                if conn and email_phone:
                    cur = conn.cursor()
                    for email, phone in email_phone.items():
                        cur.execute("""
                            UPDATE bookings SET phone=%s
                            WHERE LOWER(email)=%s AND (phone IS NULL OR phone = '' OR phone = 'None')
                        """, (phone, email))
                        updated += cur.rowcount
                        cur.execute("""
                            UPDATE customers SET phone=%s
                            WHERE LOWER(email)=%s AND (phone IS NULL OR phone = '' OR phone = 'None')
                        """, (phone, email))
                    conn.commit()
                    cur.close(); conn.close()
                result = {"ok": True, "customers_fetched": len(email_phone), "records_updated": updated, "errors": errors, "debug": debug_info}
            except Exception as e:
                result = {"error": str(e), "debug": debug_info}

    # Simple page
    nav = '<a href="/admin/dashboard" style="color:#2563eb;font-size:.85rem">← Back to Dashboard</a>'
    form_html = f"""<!DOCTYPE html>
<html><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Booqable Phone Sync</title>
<style>*{{box-sizing:border-box;margin:0;padding:0}}body{{font-family:-apple-system,sans-serif;background:#f5f6fa;padding:2rem}}
.card{{background:white;border:1px solid #e5e7eb;border-radius:10px;padding:1.5rem;max-width:540px;margin:0 auto}}
h1{{font-size:1.2rem;font-weight:700;margin-bottom:.25rem}}p{{color:#6b7280;font-size:.88rem;margin-bottom:1.25rem}}
label{{display:block;font-size:.8rem;font-weight:600;color:#374151;margin-bottom:.3rem}}
input{{width:100%;border:1px solid #d1d5db;border-radius:6px;padding:.5rem .75rem;font-size:.9rem;margin-bottom:.85rem}}
button{{background:#2563eb;color:white;border:none;border-radius:6px;padding:.6rem 1.5rem;font-size:.9rem;font-weight:700;cursor:pointer}}
.ok{{background:#dcfce7;color:#166534;border:1px solid #bbf7d0;border-radius:8px;padding:.85rem 1rem;margin-bottom:1rem;font-size:.88rem}}
.err{{background:#fee2e2;color:#991b1b;border:1px solid #fecaca;border-radius:8px;padding:.85rem 1rem;margin-bottom:1rem;font-size:.88rem}}
</style></head><body>
<div class="card">
  <div style="margin-bottom:1rem">{nav}</div>
  <h1>Booqable Phone Sync</h1>
  <p>Fetches phone numbers from your Booqable orders and fills them in for matching bookings. Get a fresh Bearer token from Booqable → open browser DevTools (F12) → Network tab → filter "boomerang" → click any request → copy the Authorization header value (everything after "Bearer ").</p>
  {'<div class="ok">✅ Found ' + str(result.get("customers_fetched",0)) + ' customers with phones, updated ' + str(result.get("records_updated",0)) + ' booking records.</div>' if result and result.get("ok") else ''}
  {'<div class="err">⚠ ' + result.get("error","") + '</div>' if result and result.get("error") else ''}
  {'<pre style=\'background:#f1f5f9;border:1px solid #e2e8f0;border-radius:6px;padding:.75rem;font-size:.75rem;overflow-x:auto;margin-bottom:1rem;white-space:pre-wrap\'>' + chr(10).join(result.get("debug",[])) + '</pre>' if result and result.get("debug") else ''}
  <form method="POST">
    <label>Booqable Subdomain (just the part before .booqable.com)</label>
    <input name="tenant" value="{last_tenant}" required>
    <label>Bearer Token (paste fresh token each time)</label>
    <input name="token" value="{last_token}" placeholder="Paste token here…" required autocomplete="off">
    <button type="submit">🔄 Sync Phone Numbers</button>
  </form>
</div>
</body></html>"""
    return form_html


# ── Route Planner ─────────────────────────────────────────────────────────────

DEPOT_ADDRESS = "799 New Haven Rd, Naugatuck, CT 06770"

ADMIN_ROUTE_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Route Planner | {{ business_name }}</title>
<style>
  *{box-sizing:border-box;margin:0;padding:0}
  body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;background:#f0f4f8;color:#1a202c}
  .topbar{background:white;border-bottom:1px solid #e2e8f0;padding:.75rem 1.5rem;display:flex;align-items:center;justify-content:space-between;position:sticky;top:0;z-index:100;box-shadow:0 1px 3px rgba(0,0,0,.08)}
  .topbar-brand{font-weight:800;font-size:1.1rem;color:#1a365d}
  .topbar-nav{display:flex;align-items:center;gap:.25rem}
  .nav-link{color:#6b7280;font-size:.85rem;font-weight:500;text-decoration:none;padding:.38rem .75rem;border-radius:6px;transition:all .12s}
  .nav-link:hover{background:#f3f4f6;color:#374151}
  .nav-link.active{background:#eff6ff;color:#2563eb;font-weight:600}
  .logout-btn{color:#e53e3e;font-size:.85rem;font-weight:500;text-decoration:none;padding:.38rem .75rem;border-radius:6px;margin-left:.5rem}
  .logout-btn:hover{background:#fff5f5}
  .main{max-width:820px;margin:0 auto;padding:2rem 1.5rem}
  .page-title{font-size:1.5rem;font-weight:800;color:#1a365d;margin-bottom:1.5rem}
  .card{background:white;border-radius:12px;padding:1.5rem;box-shadow:0 1px 4px rgba(0,0,0,.07);margin-bottom:1.25rem}
  .date-bar{display:flex;align-items:center;gap:1rem;flex-wrap:wrap}
  .date-bar label{font-weight:600;color:#374151;font-size:.95rem}
  .date-bar input[type=date]{border:1.5px solid #cbd5e0;border-radius:8px;padding:.55rem .9rem;font-size:.95rem;color:#1a202c;cursor:pointer;outline:none}
  .date-bar input[type=date]:focus{border-color:#2563eb}
  .btn-plan{background:linear-gradient(135deg,#1a365d,#2563eb);color:white;border:none;padding:.6rem 1.4rem;border-radius:8px;font-size:.9rem;font-weight:600;cursor:pointer;transition:opacity .15s}
  .btn-plan:hover{opacity:.9}
  .btn-maps{display:inline-flex;align-items:center;gap:.4rem;background:#ea4335;color:white;text-decoration:none;padding:.65rem 1.3rem;border-radius:8px;font-size:.9rem;font-weight:600;margin-top:1rem;transition:opacity .15s}
  .btn-maps:hover{opacity:.9}
  #loading{display:none;text-align:center;padding:3rem;color:#6b7280}
  #loading .spinner{width:36px;height:36px;border:3px solid #e2e8f0;border-top-color:#2563eb;border-radius:50%;animation:spin .7s linear infinite;margin:0 auto 1rem}
  @keyframes spin{to{transform:rotate(360deg)}}
  #route-output{display:none}
  .depot-card{background:linear-gradient(135deg,#1a365d,#2b6cb0);color:white;border-radius:12px;padding:1.25rem 1.5rem}
  .depot-label{font-size:.72rem;text-transform:uppercase;letter-spacing:.8px;opacity:.75;font-weight:600}
  .depot-addr{font-size:1rem;font-weight:700;margin-top:.2rem}
  .leg{display:flex;align-items:center;gap:.65rem;padding:.5rem 0 .5rem 1.5rem}
  .leg-line{width:2px;height:26px;background:#cbd5e0;flex-shrink:0}
  .leg-info{font-size:.8rem;color:#374151;font-weight:600;background:#f0f4f8;border-radius:6px;padding:.22rem .7rem;border:1px solid #e2e8f0;white-space:nowrap}
  .stop-card{border:1.5px solid #e2e8f0;border-radius:12px;padding:1.25rem 1.5rem;background:white}
  .stop-num{display:inline-flex;align-items:center;justify-content:center;width:28px;height:28px;background:#2563eb;color:white;border-radius:50%;font-size:.78rem;font-weight:700;margin-bottom:.55rem}
  .stop-name{font-size:1.05rem;font-weight:700;color:#1a365d}
  .stop-addr{font-size:.85rem;color:#4a5568;margin:.15rem 0 .55rem}
  .chips{display:flex;flex-wrap:wrap;gap:.35rem;margin-bottom:.55rem}
  .chip{font-size:.74rem;background:#f0f4f8;color:#4a5568;border-radius:5px;padding:.18rem .55rem;border:1px solid #e2e8f0}
  .chip.time{background:#eff6ff;color:#1e40af;border-color:#bfdbfe}
  .items-line{font-size:.8rem;color:#6b7280;margin-top:.3rem}
  .stop-links{margin-top:.65rem;display:flex;gap:.75rem;flex-wrap:wrap}
  .stop-link{font-size:.78rem;font-weight:500;text-decoration:none}
  .stop-link.maps{color:#ea4335}
  .stop-link.booking{color:#6b7280}
  .stop-link:hover{text-decoration:underline}
  .summary-row{display:flex;gap:1.5rem;flex-wrap:wrap;background:#f0fff4;border:1.5px solid #68d391;border-radius:12px;padding:1.25rem 1.5rem;margin-top:1.25rem}
  .summary-stat .val{font-size:1.7rem;font-weight:800;color:#276749;line-height:1}
  .summary-stat .lbl{font-size:.72rem;text-transform:uppercase;letter-spacing:.5px;color:#4a5568;margin-top:.2rem}
  .error-msg{background:#fff5f5;border:1px solid #feb2b2;color:#c53030;border-radius:8px;padding:1rem 1.25rem;font-size:.9rem}
  .no-deliveries{text-align:center;padding:2.5rem;color:#718096}
</style>
</head>
<body>
<div class="topbar">
  <div class="topbar-brand">&#127881; {{ business_name }}</div>
  <div class="topbar-nav">
    <a href="/admin/dashboard" class="nav-link">Dashboard</a>
    <a href="/admin/inventory" class="nav-link">Inventory</a>
    <a href="/admin/customers" class="nav-link">Customers</a>
    <a href="/admin/calendar" class="nav-link">&#128197; Calendar</a>
    <a href="/admin/route" class="nav-link active">&#128506; Route</a>
    <a href="/admin/logout" class="logout-btn">Sign Out</a>
  </div>
</div>
<div class="main">
  <div class="page-title">&#128506; Route Planner</div>

  <div class="card">
    <div class="date-bar">
      <label for="rdate">Delivery Date</label>
      <input type="date" id="rdate" value="{{ today }}">
      <button class="btn-plan" onclick="planRoute()">Plan Route</button>
    </div>
    <div style="margin-top:.9rem;display:flex;flex-wrap:wrap;align-items:center;gap:.6rem">
      <label for="depot-select" style="font-size:.85rem;color:#6b7280;font-weight:600;white-space:nowrap">Starting Point:</label>
      <select id="depot-select" onchange="onDepotChange()" style="flex:1;min-width:220px;padding:.45rem .65rem;border:1.5px solid #d1d5db;border-radius:8px;font-size:.9rem;background:#fff;cursor:pointer">
        <option value="799 New Haven Rd, Naugatuck, CT 06770">799 New Haven Rd, Naugatuck, CT 06770</option>
        <option value="40 Graham St, Stratford, CT 06615">40 Graham St, Stratford, CT 06615</option>
        <option value="__custom__">Custom address&hellip;</option>
      </select>
    </div>
    <div id="custom-depot-row" style="display:none;margin-top:.6rem">
      <input id="custom-depot-input" type="text" placeholder="Enter full address, e.g. 123 Main St, City, CT 00000"
             style="width:100%;box-sizing:border-box;padding:.5rem .75rem;border:1.5px solid #93c5fd;border-radius:8px;font-size:.9rem">
    </div>
  </div>

  <div id="loading"><div class="spinner"></div><p>Calculating optimal route&hellip;</p></div>
  <div id="no-stops" style="display:none" class="card"><div class="no-deliveries">
    <div style="font-size:2rem;margin-bottom:.6rem">&#128235;</div>
    <strong>No deliveries on this date</strong>
    <p style="font-size:.85rem;margin-top:.3rem">Active (pending, accepted, confirmed) bookings for this date will appear here.</p>
  </div></div>
  <div id="route-error" style="display:none" class="card"><div class="error-msg" id="route-err-msg"></div></div>

  <div id="route-output">
    <div class="depot-card">
      <div class="depot-label">&#127968; Starting Point</div>
      <div class="depot-addr" id="depot-display">{{ depot }}</div>
    </div>
    <div id="stops-list"></div>
    <div class="summary-row" id="summary-row">
      <div class="summary-stat"><div class="val" id="s-stops">-</div><div class="lbl">Stops</div></div>
      <div class="summary-stat"><div class="val" id="s-miles">-</div><div class="lbl">Total Miles</div></div>
      <div class="summary-stat"><div class="val" id="s-time">-</div><div class="lbl">Est. Drive Time</div></div>
    </div>
    <a id="gmaps-btn" href="#" target="_blank" rel="noopener" class="btn-maps" style="display:none">
      &#128205; Open Full Route in Google Maps
    </a>
  </div>
</div>
<script>
function esc(t){return String(t||'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');}
function fmt(m){if(!m&&m!==0)return '?';if(m<60)return m+'m';return Math.floor(m/60)+'h '+(m%60)+'m';}

function onDepotChange(){
  var sel=document.getElementById('depot-select');
  var row=document.getElementById('custom-depot-row');
  row.style.display=sel.value==='__custom__'?'block':'none';
  if(sel.value!=='__custom__') document.getElementById('custom-depot-input').value='';
}
function getDepot(){
  var sel=document.getElementById('depot-select');
  if(sel.value==='__custom__'){
    var v=document.getElementById('custom-depot-input').value.trim();
    if(!v){alert('Please enter a custom starting address.');return null;}
    return v;
  }
  return sel.value;
}
function planRoute(){
  var d=document.getElementById('rdate').value;
  if(!d){alert('Select a date first.');return;}
  var depot=getDepot();
  if(!depot)return;
  ['route-output','no-stops','route-error'].forEach(function(id){document.getElementById(id).style.display='none';});
  document.getElementById('loading').style.display='block';
  fetch('/admin/route/optimize?date='+d+'&depot='+encodeURIComponent(depot))
    .then(function(r){return r.json();})
    .then(function(data){
      document.getElementById('loading').style.display='none';
      if(data.error){
        document.getElementById('route-err-msg').textContent=data.error;
        document.getElementById('route-error').style.display='block';
        return;
      }
      if(!data.stops||data.stops.length===0){
        document.getElementById('no-stops').style.display='block';
        return;
      }
      renderRoute(data);
    })
    .catch(function(e){
      document.getElementById('loading').style.display='none';
      document.getElementById('route-err-msg').textContent='Error: '+e.message;
      document.getElementById('route-error').style.display='block';
    });
}

function renderRoute(data){
  var depotEl=document.getElementById('depot-display');
  if(depotEl&&data.depot)depotEl.textContent=data.depot;
  var list=document.getElementById('stops-list');
  list.innerHTML='';
  data.stops.forEach(function(s,i){
    var leg=document.createElement('div');
    leg.className='leg';
    var legText=(s.leg_miles!==null&&s.leg_miles!==undefined)
      ? s.leg_miles+' mi &nbsp;&middot;&nbsp; ~'+fmt(s.leg_minutes)
      : 'Distance N/A';
    leg.innerHTML='<div class="leg-line"></div><div class="leg-info">'+legText+'</div>';
    list.appendChild(leg);

    var card=document.createElement('div');
    card.className='stop-card';
    var chips='';
    if(s.setup_time) chips+='<span class="chip time">&#9201; Setup '+esc(s.setup_time)+'</span>';
    if(s.event_start_time) chips+='<span class="chip time">&#127881; Start '+esc(s.event_start_time)+'</span>';
    if(s.phone) chips+='<span class="chip">&#128222; '+esc(s.phone)+'</span>';
    if(s.email) chips+='<span class="chip">&#9993; '+esc(s.email)+'</span>';
    var items=s.items&&s.items.length?s.items.map(function(it){return it.qty+'x '+it.name;}).join(', '):'';
    var mapsUrl='https://www.google.com/maps/search/?api=1&query='+encodeURIComponent(s.address);
    card.innerHTML=
      '<div class="stop-num">'+(i+1)+'</div>'+
      '<div class="stop-name">'+esc(s.name)+'</div>'+
      '<div class="stop-addr">'+esc(s.address)+'</div>'+
      (chips?'<div class="chips">'+chips+'</div>':'')+
      (items?'<div class="items-line">&#128230; '+esc(items)+'</div>':'')+
      (s.delivery_location?'<div class="items-line">&#128682; '+esc(s.delivery_location)+'</div>':'')+
      '<div class="stop-links">'+
        '<a href="'+mapsUrl+'" target="_blank" rel="noopener" class="stop-link maps">&#128205; Open in Maps</a>'+
        '<a href="/admin/booking/'+s.booking_id+'" class="stop-link booking">View Booking #'+s.booking_id+'</a>'+
      '</div>';
    list.appendChild(card);
  });
  document.getElementById('s-stops').textContent=data.stops.length;
  document.getElementById('s-miles').textContent=data.total_miles!==null?data.total_miles+' mi':'?';
  document.getElementById('s-time').textContent=fmt(data.total_minutes);
  var btn=document.getElementById('gmaps-btn');
  if(data.google_maps_url){btn.href=data.google_maps_url;btn.style.display='inline-flex';}
  else{btn.style.display='none';}
  document.getElementById('route-output').style.display='block';
}
document.addEventListener('DOMContentLoaded',function(){planRoute();});
</script>
</body></html>
"""


@app.route("/admin/route")
@admin_required
def admin_route():
    from datetime import date as _date
    return render_template_string(ADMIN_ROUTE_HTML,
        business_name=BUSINESS_NAME,
        depot=DEPOT_ADDRESS,
        today=_date.today().isoformat(),
    )


@app.route("/admin/route/optimize")
@admin_required
def admin_route_optimize():
    date_str = request.args.get("date", "")
    if not date_str:
        return jsonify({"error": "No date provided"}), 400
    depot_addr = request.args.get("depot", DEPOT_ADDRESS).strip() or DEPOT_ADDRESS

    conn = get_db()
    if not conn:
        return jsonify({"error": "Database unavailable"}), 500

    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("""
            SELECT id, full_name, phone, email,
                   event_street, event_city, event_state, event_zip,
                   delivery_location, items_json,
                   setup_time, event_start_time
            FROM bookings
            WHERE event_start_date = %s
              AND status NOT IN ('cancelled', 'denied')
              AND (archived IS NULL OR archived = FALSE)
            ORDER BY id
        """, (date_str,))
        rows = [dict(r) for r in cur.fetchall()]
        cur.close()
        conn.close()
    except Exception as e:
        return jsonify({"error": str(e)}), 500

    if not rows:
        return jsonify({"stops": [], "total_miles": 0, "total_minutes": 0,
                        "date": date_str, "depot": depot_addr})

    addresses = []
    for b in rows:
        parts = [b.get("event_street",""), b.get("event_city",""),
                 b.get("event_state",""), b.get("event_zip","")]
        addresses.append(", ".join(p for p in parts if p).strip(", "))

    all_locs = [depot_addr] + addresses
    n = len(all_locs)
    route_order = list(range(1, n))
    dur_matrix = None
    dist_matrix = None
    optimized = False

    if GOOGLE_MAPS_KEY and n > 1:
        try:
            rsp = requests.get(
                "https://maps.googleapis.com/maps/api/distancematrix/json",
                params={"origins": "|".join(all_locs),
                        "destinations": "|".join(all_locs),
                        "units": "imperial",
                        "key": GOOGLE_MAPS_KEY},
                timeout=15,
            )
            dm = rsp.json()
            dur_m, dist_m = [], []
            for row_data in dm.get("rows", []):
                dr, distrow = [], []
                for el in row_data.get("elements", []):
                    if el.get("status") == "OK":
                        dr.append(el["duration"]["value"])
                        distrow.append(el["distance"]["value"])
                    else:
                        dr.append(999999)
                        distrow.append(999999)
                dur_m.append(dr)
                dist_m.append(distrow)
            dur_matrix  = dur_m
            dist_matrix = dist_m

            unvisited = set(range(1, n))
            route_order = []
            current = 0
            while unvisited:
                nearest = min(unvisited, key=lambda x: dur_matrix[current][x])
                route_order.append(nearest)
                unvisited.remove(nearest)
                current = nearest
            optimized = True
        except Exception as e:
            log.error(f"Route optimize error: {e}")

    result_stops = []
    total_miles   = 0.0
    total_minutes = 0
    prev_idx = 0

    for step, idx in enumerate(route_order):
        b = rows[idx - 1]
        leg_miles = leg_mins = None
        if dur_matrix and dist_matrix:
            d_sec = dur_matrix[prev_idx][idx]
            d_met = dist_matrix[prev_idx][idx]
            if d_sec < 999999:
                leg_miles = round(d_met / 1609.344, 1)
                leg_mins  = max(1, round(d_sec / 60))
                total_miles   += leg_miles
                total_minutes += leg_mins
        result_stops.append({
            "order":             step + 1,
            "booking_id":        b["id"],
            "name":              b.get("full_name", ""),
            "phone":             str(b.get("phone") or ""),
            "email":             str(b.get("email") or ""),
            "address":           addresses[idx - 1],
            "delivery_location": str(b.get("delivery_location") or ""),
            "items":             json.loads(b.get("items_json") or "[]"),
            "setup_time":        str(b.get("setup_time") or ""),
            "event_start_time":  str(b.get("event_start_time") or ""),
            "leg_miles":         leg_miles,
            "leg_minutes":       leg_mins,
        })
        prev_idx = idx

    waypoints = [urllib.parse.quote_plus(depot_addr)]
    for s in result_stops[:9]:
        waypoints.append(urllib.parse.quote_plus(s["address"]))
    maps_url = "https://www.google.com/maps/dir/" + "/".join(waypoints)

    return jsonify({
        "stops":           result_stops,
        "total_miles":     round(total_miles, 1),
        "total_minutes":   total_minutes,
        "date":            date_str,
        "optimized":       optimized,
        "depot":           depot_addr,
        "google_maps_url": maps_url,
    })


# ── Calendar Routes ───────────────────────────────────────────────────────────

CALENDAR_KEY = os.getenv("CALENDAR_KEY", "")

@app.route("/admin/calendar")
@admin_required
def admin_calendar():
    conn = get_db()
    bookings = []
    if conn:
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur.execute("""
                SELECT id, full_name, email, phone,
                       event_start_date, event_end_date,
                       status, grand_total, final_payment_link,
                       items_json, delivery_location
                FROM bookings
                WHERE status NOT IN ('denied')
                  AND (archived IS NULL OR archived = FALSE)
                ORDER BY event_start_date
            """)
            for row in cur.fetchall():
                b = _row(row)
                b["grand_total"] = float(b.get("grand_total") or 0)
                b["event_start_date"] = str(b.get("event_start_date") or "")
                b["event_end_date"]   = str(b.get("event_end_date") or "")
                bookings.append(b)
            cur.close()
            conn.close()
        except Exception as e:
            log.error(f"Calendar fetch error: {e}")

    ics_url = request.host_url.rstrip("/") + "/calendar.ics"
    if CALENDAR_KEY:
        ics_url += f"?key={CALENDAR_KEY}"

    return render_template_string(ADMIN_CALENDAR_HTML,
        business_name=BUSINESS_NAME,
        bookings_json=json.dumps(bookings),
        ics_url=ics_url,
    )


@app.route("/calendar.ics")
def calendar_ics():
    key = request.args.get("key", "")
    if CALENDAR_KEY and key != CALENDAR_KEY:
        return "Unauthorized", 401

    conn = get_db()
    bookings = []
    if conn:
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
            cur.execute("""
                SELECT id, full_name, event_start_date, event_end_date,
                       status, grand_total, final_payment_link
                FROM bookings
                WHERE status NOT IN ('denied')
                  AND (archived IS NULL OR archived = FALSE)
                ORDER BY event_start_date
            """)
            bookings = [dict(r) for r in cur.fetchall()]
            cur.close()
            conn.close()
        except Exception as e:
            log.error(f"ICS feed error: {e}")

    now_utc = datetime.utcnow().strftime("%Y%m%dT%H%M%SZ")
    lines = [
        "BEGIN:VCALENDAR", "VERSION:2.0",
        f"PRODID:-//Rent a Party LLC//Booking Calendar//EN",
        f"X-WR-CALNAME:{BUSINESS_NAME} Bookings",
        "X-WR-TIMEZONE:America/New_York",
        "CALSCALE:GREGORIAN", "METHOD:PUBLISH",
    ]
    for b in bookings:
        status = b.get("status", "")
        paid   = float(b.get("amount_paid") or 0)
        total  = float(b.get("grand_total") or 0)
        fp     = b.get("final_payment_link")
        if status == "confirmed":
            if paid > 0 and paid < total - 0.01:
                label = f"Partial — ${total - paid:,.2f} owed"
            elif fp:
                label = "Partially Paid"
            else:
                label = "Paid In Full"
        elif status == "accepted":
            label = "Payment Due"
        elif status == "pending":
            label = "Pending"
        else:
            label = status.capitalize()
        try:
            start_str = str(b["event_start_date"])[:10].replace("-", "")
            end_dt    = datetime.strptime(str(b["event_end_date"])[:10], "%Y-%m-%d") + timedelta(days=1)
            end_str   = end_dt.strftime("%Y%m%d")
        except Exception:
            start_str = end_str = now_utc[:8]
        uid     = f"booking-{b['id']}@rentaparty"
        summary = f"{label} - {b['full_name']} (#{b['id']})"
        total   = float(b.get("grand_total") or 0)
        desc    = f"Booking #{b['id']} | Total: ${total:.2f} | Status: {status}"
        lines += [
            "BEGIN:VEVENT", f"UID:{uid}", f"DTSTAMP:{now_utc}",
            f"DTSTART;VALUE=DATE:{start_str}", f"DTEND;VALUE=DATE:{end_str}",
            f"SUMMARY:{summary}", f"DESCRIPTION:{desc}", "END:VEVENT",
        ]
    lines.append("END:VCALENDAR")
    ics_content = "\r\n".join(lines) + "\r\n"
    return Response(ics_content, mimetype="text/calendar",
                    headers={"Content-Disposition": "inline; filename=bookings.ics"})


# ── PWA Routes ────────────────────────────────────────────────────────────────

@app.route("/manifest.json")
def pwa_manifest():
    manifest = {
        "name": BUSINESS_NAME,
        "short_name": "Rent a Party",
        "description": "Party rental booking and admin",
        "start_url": "/",
        "display": "standalone",
        "background_color": "#f5f6fa",
        "theme_color": "#2563eb",
        "orientation": "portrait-primary",
        "icons": [
            {"src": "/icon-192.png", "sizes": "192x192", "type": "image/png", "purpose": "any maskable"},
            {"src": "/icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "any maskable"},
        ],
    }
    return Response(json.dumps(manifest), mimetype="application/manifest+json")


@app.route("/sw.js")
def pwa_sw():
    sw = """self.addEventListener('install',e=>self.skipWaiting());
self.addEventListener('activate',e=>clients.claim());
self.addEventListener('fetch',e=>{});
"""
    return Response(sw, mimetype="application/javascript")


@app.route("/icon-192.png")
def pwa_icon_192():
    return Response(_ICON_192, mimetype="image/png")


@app.route("/icon-512.png")
def pwa_icon_512():
    return Response(_ICON_512, mimetype="image/png")


# ── SMS Test ──────────────────────────────────────────────────────────────────

@app.route("/admin/test-sms")
@admin_required
def test_sms():
    """Send a test SMS to verify Twilio config is working."""
    account_sid = os.getenv("TWILIO_ACCOUNT_SID", "")
    auth_token  = os.getenv("TWILIO_AUTH_TOKEN",  "")
    from_number = os.getenv("TWILIO_FROM_NUMBER", "")
    to_number   = os.getenv("OWNER_PHONE",        "")

    missing = [k for k, v in [
        ("TWILIO_ACCOUNT_SID", account_sid),
        ("TWILIO_AUTH_TOKEN",  auth_token),
        ("TWILIO_FROM_NUMBER", from_number),
        ("OWNER_PHONE",        to_number),
    ] if not v]

    if missing:
        return f"<pre>Missing env vars: {', '.join(missing)}\n\nSet them on Render and redeploy.</pre>", 400

    try:
        resp = requests.post(
            f"https://api.twilio.com/2010-04-01/Accounts/{account_sid}/Messages.json",
            auth=(account_sid, auth_token),
            data={"From": from_number, "To": to_number,
                  "Body": "Test from Rent a Party app — SMS alerts are working!"},
            timeout=10
        )
        if resp.status_code >= 400:
            return f"<pre>Twilio error {resp.status_code}:\n{resp.text}</pre>", 400
        return f"<pre>SMS sent successfully to {to_number}!\n\nTwilio response: {resp.json().get('sid')}</pre>"
    except Exception as e:
        return f"<pre>Error: {e}</pre>", 500


# ── Cron / Auto-reminders ─────────────────────────────────────────────────────

@app.route("/cron/send-reminders")
def cron_send_reminders():
    """Called by Render cron job (or external scheduler) once daily.

    Two passes:
    1. confirmed bookings (deposit paid) → send remaining balance 2 days before event
    2. accepted bookings (full amount due) → send full invoice 5 days before event
    """
    secret = request.args.get("secret", "")
    cron_secret = os.getenv("CRON_SECRET", "")
    if cron_secret and secret != cron_secret:
        return "Unauthorized", 401

    conn = get_db()
    if not conn:
        return "DB unavailable", 500

    sent = []

    # ── Pass 1: confirmed bookings, 2 days out (remaining 75%) ───────────────
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        target_2day = (date.today() + timedelta(days=2)).isoformat()
        cur.execute("""
            SELECT * FROM bookings
            WHERE status = 'confirmed'
              AND event_start_date = %s
              AND (final_reminder_sent IS NULL OR final_reminder_sent = FALSE)
        """, (target_2day,))
        bookings_2day = [dict(r) for r in cur.fetchall()]
        cur.close()
    except Exception as e:
        conn.close()
        return f"DB error (pass 1): {e}", 500

    for b in bookings_2day:
        try:
            grand_total  = float(b.get("grand_total") or 0)
            amount_paid  = float(b.get("amount_paid") or 0)
            remaining    = round(max(grand_total - amount_paid, grand_total * 0.75), 2)
            items_list   = ", ".join(
                f"{i['qty']}x {i['name']}"
                for i in json.loads(b.get("items_json") or "[]")
            )
            product_name = f"Final Payment — Booking #{b['id']}"
            payment_link, plink_id, err = create_stripe_payment_link(
                b["id"], remaining, b.get("email"), items_list, product_name
            )
            if err:
                log.warning(f"Cron Stripe error #{b['id']}: {err}")
            if payment_link:
                save_payment_link(b["id"], product_name, remaining, payment_link, plink_id)

            conn2 = get_db()
            if conn2:
                cur2 = conn2.cursor()
                cur2.execute(
                    "UPDATE bookings SET final_payment_link=%s, final_reminder_sent=TRUE WHERE id=%s",
                    (payment_link, b["id"])
                )
                conn2.commit(); cur2.close(); conn2.close()

            b["final_payment_link"] = payment_link
            send_final_payment_email(b, remaining, payment_link)
            sent.append(b["id"])
            log.info(f"Cron: 2-day final reminder sent for booking #{b['id']}")
        except Exception as e:
            log.error(f"Cron pass-1 error for booking #{b.get('id')}: {e}")

    # ── Pass 2: accepted bookings, 5 days out (full amount due) ──────────────
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        target_5day = (date.today() + timedelta(days=5)).isoformat()
        cur.execute("""
            SELECT * FROM bookings
            WHERE status = 'accepted'
              AND event_start_date = %s
              AND (auto_invoice_sent IS NULL OR auto_invoice_sent = FALSE)
        """, (target_5day,))
        bookings_5day = [dict(r) for r in cur.fetchall()]
        cur.close()
        conn.close()
    except Exception as e:
        return f"DB error (pass 2): {e}", 500

    for b in bookings_5day:
        try:
            grand_total  = float(b.get("grand_total") or 0)
            if grand_total <= 0:
                continue
            items_list   = ", ".join(
                f"{i['qty']}x {i['name']}"
                for i in json.loads(b.get("items_json") or "[]")
            )
            product_name = f"Full Invoice — Booking #{b['id']}"
            payment_link, plink_id, err = create_stripe_payment_link(
                b["id"], grand_total, b.get("email"), items_list, product_name
            )
            if err:
                log.warning(f"Cron 5-day Stripe error #{b['id']}: {err}")
            if payment_link:
                save_payment_link(b["id"], product_name, grand_total, payment_link, plink_id)

            conn3 = get_db()
            if conn3:
                cur3 = conn3.cursor()
                cur3.execute(
                    "UPDATE bookings SET final_payment_link=%s, auto_invoice_sent=TRUE WHERE id=%s",
                    (payment_link, b["id"])
                )
                conn3.commit(); cur3.close(); conn3.close()

            b["final_payment_link"] = payment_link
            send_final_payment_email(b, grand_total, payment_link)
            sent.append(b["id"])
            log.info(f"Cron: 5-day full invoice sent for booking #{b['id']}")
        except Exception as e:
            log.error(f"Cron pass-2 error for booking #{b.get('id')}: {e}")

    return jsonify({"sent": sent, "count": len(sent)})


# ── Run ───────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    app.run(debug=False, host="0.0.0.0", port=int(os.getenv("PORT", 5000)))
