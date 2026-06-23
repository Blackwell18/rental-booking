#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════╗
║        RENTAL BOOKING & INVENTORY MANAGEMENT SYSTEM         ║
╠══════════════════════════════════════════════════════════════╣
║  • Professional booking form with all required fields        ║
║  • Real-time inventory availability by date range            ║
║  • First-come-first-PAID: confirmed bookings lock inventory  ║
║  • Admin panel to view bookings & confirm payments           ║
║  • Automatic delivery fee calculation                        ║
║  • Email notifications for owner and customer               ║
║  • PostgreSQL database via Supabase (free)                   ║
╚══════════════════════════════════════════════════════════════╝
"""

import os, json, logging, smtplib, secrets
from datetime import datetime, timezone, date
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from functools import wraps

import requests
import psycopg2
import psycopg2.extras
from flask import (Flask, request, render_template_string,
                   redirect, url_for, jsonify, session)
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
    {"id": "banquet_tables", "name": "8×30 Wood Banquet Tables",         "price": 15.00, "total": 10},
    {"id": "round_tables",   "name": "60\" Wood Round Tables",           "price": 15.00, "total": 10},
    {"id": "cocktail_30",    "name": "30\" Cocktail Tables",             "price": 15.00, "total": 10},
    {"id": "cocktail_cloth", "name": "Cocktail Table Cloths",            "price": 8.00,  "total": 10},
]

EXACT_TIME_FEE = 175.00   # fee for exact-time delivery


# ══════════════════════════════════════════════════════════════════════════════
#  CONFIGURATION  (set in Render.com → Environment)
# ══════════════════════════════════════════════════════════════════════════════

def _float(key, default):
    try:
        return float(os.getenv(key, "") or default)
    except ValueError:
        return float(default)

BUSINESS_NAME    = os.getenv("BUSINESS_NAME",    "Premier Event Rentals")
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
ADMIN_PASSWORD     = os.getenv("ADMIN_PASSWORD",     "admin123")  # CHANGE THIS


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
    """Create tables on startup if they don't exist."""
    conn = get_db()
    if not conn:
        return
    try:
        cur = conn.cursor()
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
                notes            TEXT
            )
        """)
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
#  INVENTORY CHECKING
# ══════════════════════════════════════════════════════════════════════════════

def get_available(start_date_str, end_date_str, exclude_id=None):
    """
    Returns dict of {product_id: available_qty} for a given date range.
    Available = total inventory minus quantities in CONFIRMED bookings
    that overlap with the requested dates.

    Pending bookings do NOT block inventory — only paid/confirmed ones do.
    """
    available = {p["id"]: p["total"] for p in PRODUCTS}

    conn = get_db()
    if not conn:
        return available

    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)

        # Find confirmed bookings that overlap with the requested date range
        # Overlap condition: booking starts before end AND booking ends after start
        query = """
            SELECT items_json FROM bookings
            WHERE status = 'confirmed'
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

        # Subtract booked quantities from available
        for row in rows:
            try:
                items = json.loads(row["items_json"] or "[]")
                for item in items:
                    pid = item.get("id")
                    qty = item.get("qty", 0)
                    if pid in available:
                        available[pid] = max(0, available[pid] - qty)
            except Exception:
                pass

    except Exception as e:
        log.error(f"Inventory check error: {e}")

    return available


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
    return fee, f"{miles} mi × ${DELIVERY_RATE:.2f}/mi"


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

    subject = f"📋 New Booking #{b.get('id')} — {b.get('full_name')} | {b.get('event_start_date')}"

    html = f"""
<html><body style="font-family:-apple-system,sans-serif;background:#f0f4f8;padding:2rem 1rem">
<div style="max-width:640px;margin:0 auto">
  <div style="background:linear-gradient(135deg,#1a365d,#2b6cb0);border-radius:12px 12px 0 0;padding:1.5rem 2rem;color:white">
    <h2 style="margin:0">📋 New Booking Request #{b.get('id')}</h2>
    <p style="margin:.4rem 0 0;opacity:.85">{BUSINESS_NAME}</p>
  </div>
  <div style="background:white;padding:2rem;border-radius:0 0 12px 12px;box-shadow:0 4px 16px rgba(0,0,0,.08)">

    <table style="width:100%;border-collapse:collapse;margin-bottom:1.5rem">
      <tr style="background:#ebf4ff"><td colspan="2" style="padding:10px 12px;font-weight:700;color:#2b6cb0;text-transform:uppercase;font-size:.85rem">Customer</td></tr>
      <tr><td style="padding:8px 12px;color:#718096;width:160px">Name</td><td style="padding:8px 12px;font-weight:600">{b.get('full_name')}</td></tr>
      {"<tr style='background:#f7fafc'><td style='padding:8px 12px;color:#718096'>Company</td><td style='padding:8px 12px'>" + b.get('company_name','') + "</td></tr>" if b.get('company_name') else ""}
      <tr style="background:#f7fafc"><td style="padding:8px 12px;color:#718096">Address</td><td style="padding:8px 12px">{renter_addr}</td></tr>
      <tr><td style="padding:8px 12px;color:#718096">Phone</td><td style="padding:8px 12px">{b.get('phone')}</td></tr>
      <tr style="background:#f7fafc"><td style="padding:8px 12px;color:#718096">Email</td><td style="padding:8px 12px"><a href="mailto:{b.get('email')}" style="color:#2b6cb0">{b.get('email')}</a></td></tr>
    </table>

    <table style="width:100%;border-collapse:collapse;margin-bottom:1.5rem">
      <tr style="background:#ebf4ff"><td colspan="2" style="padding:10px 12px;font-weight:700;color:#2b6cb0;text-transform:uppercase;font-size:.85rem">Event</td></tr>
      <tr><td style="padding:8px 12px;color:#718096;width:160px">Dates</td><td style="padding:8px 12px;font-weight:600">{b.get('event_start_date')} → {b.get('event_end_date')}</td></tr>
      <tr style="background:#f7fafc"><td style="padding:8px 12px;color:#718096">Start Time</td><td style="padding:8px 12px">{b.get('event_start_time','')}</td></tr>
      <tr><td style="padding:8px 12px;color:#718096">End Time</td><td style="padding:8px 12px">{b.get('event_end_time','')}</td></tr>
      <tr style="background:#f7fafc"><td style="padding:8px 12px;color:#718096">Setup Time</td><td style="padding:8px 12px">{b.get('setup_time','')}</td></tr>
      <tr><td style="padding:8px 12px;color:#718096">Venue Type</td><td style="padding:8px 12px;text-transform:capitalize">{b.get('venue_type','')}</td></tr>
      {"<tr style='background:#f7fafc'><td style='padding:8px 12px;color:#718096'>Latest Pickup</td><td style='padding:8px 12px'>" + str(b.get('venue_latest_pickup','')) + "</td></tr>" if b.get('venue_latest_pickup') else ""}
      <tr style="background:#f7fafc"><td style="padding:8px 12px;color:#718096">Event Address</td><td style="padding:8px 12px">{event_addr}</td></tr>
      <tr><td style="padding:8px 12px;color:#718096">Delivery To</td><td style="padding:8px 12px">{b.get('delivery_location','')}</td></tr>
    </table>

    <table style="width:100%;border-collapse:collapse;margin-bottom:1.5rem">
      <tr style="background:#ebf4ff">
        <th style="padding:10px 12px;text-align:left;color:#2b6cb0;font-size:.85rem;text-transform:uppercase">Item</th>
        <th style="padding:10px 12px;text-align:center;color:#2b6cb0;font-size:.85rem;text-transform:uppercase">Qty</th>
        <th style="padding:10px 12px;text-align:right;color:#2b6cb0;font-size:.85rem;text-transform:uppercase">Price</th>
        <th style="padding:10px 12px;text-align:right;color:#2b6cb0;font-size:.85rem;text-transform:uppercase">Total</th>
      </tr>
      {item_rows}
      {"<tr style='background:#fffaf0'><td colspan='3' style='padding:8px 12px;border-bottom:1px solid #e2e8f0'>Exact Time Delivery</td><td style='padding:8px 12px;text-align:right;font-weight:600;border-bottom:1px solid #e2e8f0'>$175.00</td></tr>" if exact else ""}
      <tr style="background:#fffaf0">
        <td colspan="3" style="padding:8px 12px;border-bottom:1px solid #e2e8f0">
          Delivery Fee <span style="color:#718096;font-size:.85em">({b.get('distance_miles','?')} mi — {b.get('delivery_fee_note','calculated')})</span>
        </td>
        <td style="padding:8px 12px;text-align:right;font-weight:600;border-bottom:1px solid #e2e8f0">${b.get('delivery_fee',0):.2f}</td>
      </tr>
      <tr style="background:#1a365d;color:white">
        <td colspan="3" style="padding:12px;font-weight:700;font-size:1.05rem">ESTIMATED TOTAL</td>
        <td style="padding:12px;text-align:right;font-weight:700;font-size:1.2rem">${b.get('grand_total',0):.2f}</td>
      </tr>
    </table>

    {"<div style='background:#fffaf0;border-left:4px solid #ed8936;padding:1rem;border-radius:0 8px 8px 0;margin-bottom:1.5rem'><strong>Notes:</strong><br>" + str(b.get('notes','')) + "</div>" if b.get('notes') else ""}

    <div style="background:#f0f4f8;border-radius:10px;padding:1.25rem;text-align:center">
      <p style="margin:0 0 .5rem;font-weight:600;color:#2d3748">Hit Reply to contact {b.get('full_name','').split()[0]}</p>
      <p style="margin:0;font-size:.85rem;color:#718096">Reply goes directly to {b.get('email')}</p>
    </div>
  </div>
</div></body></html>"""

    plain = f"""NEW BOOKING #{b.get('id')} — {BUSINESS_NAME}

CUSTOMER
  {b.get('full_name')}  |  {b.get('phone')}  |  {b.get('email')}
  {renter_addr}

EVENT
  Dates:  {b.get('event_start_date')} → {b.get('event_end_date')}
  Start:  {b.get('event_start_time')}  |  End: {b.get('event_end_time')}
  Setup:  {b.get('setup_time')}  |  Venue: {b.get('venue_type')}
  Address: {event_addr}
  Deliver to: {b.get('delivery_location')}

ITEMS
{"".join(f"  {i['qty']}x {i['name']} @ ${i['unit_price']:.2f} = ${i['total']:.2f}\n" for i in items)}
{"  Exact Time Delivery: $175.00\n" if exact else ""}  Delivery: ${b.get('delivery_fee',0):.2f}
  TOTAL: ${b.get('grand_total',0):.2f}
"""
    _send_email(OWNER_EMAIL, subject, html, plain, reply_to=b.get("email"))


def send_customer_email(b):
    """Send confirmation to customer."""
    email = b.get("email")
    first = b.get("full_name", "").split()[0]
    if not email:
        return

    subject = f"We received your rental request! — {BUSINESS_NAME}"
    html = f"""
<html><body style="font-family:-apple-system,sans-serif;background:#f0f4f8;padding:2rem 1rem">
<div style="max-width:500px;margin:0 auto;background:white;border-radius:12px;overflow:hidden;box-shadow:0 4px 16px rgba(0,0,0,.08)">
  <div style="background:linear-gradient(135deg,#1a365d,#2b6cb0);padding:2rem;color:white;text-align:center">
    <h2 style="margin:0">Request Received ✅</h2>
    <p style="margin:.5rem 0 0;opacity:.85">{BUSINESS_NAME}</p>
  </div>
  <div style="padding:2rem">
    <p style="color:#2d3748;font-size:1.05rem">Hi <strong>{first}</strong>,</p>
    <p style="color:#4a5568;line-height:1.7">
      Thank you for your rental inquiry! We've received your request for
      <strong>{b.get('event_start_date')}</strong> and will review your booking and
      send you a detailed quote shortly.
    </p>
    <div style="background:#f0f4f8;border-radius:8px;padding:1rem;margin:1rem 0">
      <p style="margin:0;font-weight:600;color:#2d3748">Your Booking Reference</p>
      <p style="margin:.3rem 0 0;font-size:1.4rem;font-weight:700;color:#2b6cb0">#{b.get('id')}</p>
    </div>
    <p style="color:#4a5568;line-height:1.7">
      Please save this reference number. {f"Questions? Call us at <strong>{BUSINESS_PHONE}</strong>." if BUSINESS_PHONE else ""}
    </p>
    <p style="color:#2d3748;font-weight:600;margin-top:1.5rem">— The {BUSINESS_NAME} Team</p>
  </div>
</div></body></html>"""

    plain = f"""Hi {first},

Thank you for your rental request! We received your booking for {b.get('event_start_date')}.

Your booking reference number is: #{b.get('id')}

We'll review your request and send you a quote soon.

{f"Questions? Call {BUSINESS_PHONE}" if BUSINESS_PHONE else ""}

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

    /* Venue/Residential toggle */
    .type-toggle{display:flex;gap:.75rem;margin-bottom:1rem}
    .type-btn{flex:1;padding:.65rem;border:2px solid #cbd5e0;border-radius:8px;background:white;font-size:.9rem;font-weight:600;color:#718096;cursor:pointer;text-align:center;transition:all .15s}
    .type-btn.active{border-color:#2b6cb0;background:#ebf4ff;color:#2b6cb0}

    /* Exact time delivery toggle */
    .exact-toggle{display:flex;align-items:center;gap:.75rem;padding:1rem;background:#fffaf0;border:2px solid #ed8936;border-radius:10px;cursor:pointer;margin-bottom:.75rem}
    .exact-toggle input[type=checkbox]{width:20px;height:20px;cursor:pointer;accent-color:#2b6cb0}
    .exact-label{flex:1}
    .exact-label strong{display:block;font-size:.97rem;color:#1a202c}
    .exact-label span{font-size:.82rem;color:#718096}
    .exact-badge{background:#ed8936;color:white;padding:.2rem .6rem;border-radius:20px;font-size:.8rem;font-weight:700}

    /* Product rows */
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

    /* Total bar */
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
{% if error %}
<div class="alert">⚠️ {{ error }}</div>
{% endif %}

<form method="POST" action="/submit" id="bookingForm">

  <!-- ── 1. YOUR INFORMATION ── -->
  <div class="card">
    <h2>👤 Your Information</h2>
    <div class="row">
      <div class="field">
        <label>Full Name <span class="required">*</span></label>
        <input name="full_name" required placeholder="Jane Smith" value="{{ form.full_name or '' }}">
      </div>
      <div class="field">
        <label>Company Name <span style="color:#718096;font-weight:400">(if applicable)</span></label>
        <input name="company_name" placeholder="ABC Events LLC" value="{{ form.company_name or '' }}">
      </div>
    </div>
    <div class="field">
      <label>Street Address <span class="required">*</span></label>
      <input name="renter_street" required placeholder="123 Main Street" value="{{ form.renter_street or '' }}">
    </div>
    <div class="row3">
      <div class="field">
        <label>City <span class="required">*</span></label>
        <input name="renter_city" required placeholder="Orlando" value="{{ form.renter_city or '' }}">
      </div>
      <div class="field">
        <label>State <span class="required">*</span></label>
        <input name="renter_state" required placeholder="FL" maxlength="2" value="{{ form.renter_state or '' }}">
      </div>
      <div class="field">
        <label>Zip Code <span class="required">*</span></label>
        <input name="renter_zip" required placeholder="32801" value="{{ form.renter_zip or '' }}">
      </div>
    </div>
    <div class="row">
      <div class="field">
        <label>Phone Number <span class="required">*</span></label>
        <input name="phone" type="tel" required placeholder="(555) 000-0000" value="{{ form.phone or '' }}">
      </div>
      <div class="field">
        <label>Email Address <span class="required">*</span></label>
        <input name="email" type="email" required placeholder="jane@email.com" value="{{ form.email or '' }}">
      </div>
    </div>
  </div>

  <!-- ── 2. EVENT DETAILS ── -->
  <div class="card">
    <h2>📅 Event Details</h2>
    <div class="row">
      <div class="field">
        <label>Event Start Date <span class="required">*</span></label>
        <input id="event_start_date" name="event_start_date" type="date" required
               onchange="onDateChange()" value="{{ form.event_start_date or '' }}">
      </div>
      <div class="field">
        <label>Event End Date <span class="required">*</span></label>
        <input id="event_end_date" name="event_end_date" type="date" required
               onchange="onDateChange()" value="{{ form.event_end_date or '' }}">
      </div>
    </div>
    <div class="row">
      <div class="field">
        <label>Event Start Time <span class="required">*</span></label>
        <input name="event_start_time" type="time" required value="{{ form.event_start_time or '' }}">
      </div>
      <div class="field">
        <label>Event End Time <span class="required">*</span></label>
        <input name="event_end_time" type="time" required value="{{ form.event_end_time or '' }}">
      </div>
    </div>
    <div class="row">
      <div class="field">
        <label>Setup Time <span class="required">*</span></label>
        <input name="setup_time" type="time" required value="{{ form.setup_time or '' }}">
      </div>
    </div>

    <div class="field">
      <label>Venue Type <span class="required">*</span></label>
      <div class="type-toggle">
        <div class="type-btn active" id="btn_venue"       onclick="setVenue('venue')">🏛️ Venue</div>
        <div class="type-btn"       id="btn_residential" onclick="setVenue('residential')">🏠 Residential</div>
      </div>
      <input type="hidden" name="venue_type" id="venue_type_input" value="venue">
    </div>
    <div id="venue_pickup_row" class="field">
      <label>Latest Pickup Time at Venue <span class="required">*</span></label>
      <input id="venue_latest_pickup" name="venue_latest_pickup" type="time" value="{{ form.venue_latest_pickup or '' }}">
    </div>
  </div>

  <!-- ── 3. EVENT ADDRESS ── -->
  <div class="card">
    <h2>📍 Event Address</h2>
    <p class="section-note">Where will we deliver your rental items?</p>
    <div class="field">
      <label>Street Address <span class="required">*</span></label>
      <input id="event_street" name="event_street" required placeholder="456 Venue Blvd" value="{{ form.event_street or '' }}" oninput="scheduleDistanceCalc()">
    </div>
    <div class="row3">
      <div class="field">
        <label>City <span class="required">*</span></label>
        <input id="event_city" name="event_city" required placeholder="Orlando" value="{{ form.event_city or '' }}" oninput="scheduleDistanceCalc()">
      </div>
      <div class="field">
        <label>State <span class="required">*</span></label>
        <input id="event_state" name="event_state" required placeholder="FL" maxlength="2" value="{{ form.event_state or '' }}" oninput="scheduleDistanceCalc()">
      </div>
      <div class="field">
        <label>Zip Code <span class="required">*</span></label>
        <input id="event_zip" name="event_zip" required placeholder="32801" value="{{ form.event_zip or '' }}" oninput="scheduleDistanceCalc()">
      </div>
    </div>
  </div>

  <!-- ── 4. DELIVERY ── -->
  <div class="card">
    <h2>🚚 Delivery Options</h2>
    <label class="exact-toggle">
      <input type="checkbox" id="exact_time_cb" name="exact_time_delivery" value="yes"
             onchange="updateTotals()">
      <div class="exact-label">
        <strong>Exact Time Delivery</strong>
        <span>Guaranteed delivery at your specified setup time</span>
      </div>
      <span class="exact-badge">+$175</span>
    </label>
    <div class="field">
      <label>Where on the premises will items be delivered? <span class="required">*</span></label>
      <textarea name="delivery_location" required
                placeholder="e.g. Through the main entrance, set up in the ballroom on the left side…">{{ form.delivery_location or '' }}</textarea>
    </div>
  </div>

  <!-- ── 5. SELECT ITEMS ── -->
  <div class="card">
    <h2>🪑 Select Your Items</h2>
    <p class="section-note" id="avail_note">Select your event dates above to see real-time availability.</p>
    {% for p in products %}
    <div class="product-row">
      <div>
        <div class="product-name">{{ p.name }}</div>
        <div class="product-meta">
          <span class="product-price">${{ "%.2f"|format(p.price) }} each</span>
          <span class="avail-badge ok" id="avail_{{ p.id }}">{{ p.total }} available</span>
        </div>
      </div>
      <div class="qty-control">
        <button type="button" class="qty-btn" onclick="changeQty('{{ p.id }}',-1)">−</button>
        <input class="qty-input" type="number" id="qty_{{ p.id }}" name="qty_{{ p.id }}"
               value="0" min="0" max="{{ p.total }}"
               data-price="{{ p.price }}" data-max="{{ p.total }}"
               oninput="updateTotals()">
        <button type="button" class="qty-btn" onclick="changeQty('{{ p.id }}',1)">+</button>
      </div>
      <div class="product-sub" id="sub_{{ p.id }}">—</div>
    </div>
    {% endfor %}
  </div>

  <!-- ── ORDER SUMMARY ── -->
  <div class="total-bar">
    <div class="total-row"><span>Items Subtotal</span><span id="t_items">$0.00</span></div>
    <div class="total-row"><span>Exact Time Delivery</span><span id="t_exact">—</span></div>
    <div class="total-row"><span>Delivery Fee</span><span id="t_delivery">Calculated after review</span></div>
    <div class="total-row grand"><span>Estimated Total</span><span id="t_grand">$0.00</span></div>
    <p class="total-note">Final delivery fee confirmed after we verify your address. This is a quote request, not a charge.</p>
  </div>

  <button type="submit" class="submit-btn" id="submitBtn">Send Quote Request →</button>
</form>
</div>

<script>
const EXACT_FEE = {{ exact_time_fee }};

// ── Live price calculator ────────────────────────────────────────────────
function changeQty(id, delta) {
  const input = document.getElementById('qty_' + id);
  const max   = parseInt(input.dataset.max);
  let v = Math.max(0, Math.min(max, parseInt(input.value || 0) + delta));
  input.value = v;
  updateTotals();
}

function updateTotals() {
  let sub = 0;
  document.querySelectorAll('.qty-input').forEach(input => {
    const qty = parseInt(input.value) || 0;
    const price = parseFloat(input.dataset.price);
    const id = input.id.replace('qty_','');
    const line = qty * price;
    sub += line;
    const el = document.getElementById('sub_' + id);
    el.textContent = qty > 0 ? '$' + line.toFixed(2) : '—';
    el.classList.toggle('has-val', qty > 0);
  });
  const exact = document.getElementById('exact_time_cb').checked;
  const exactFee = exact ? EXACT_FEE : 0;
  document.getElementById('t_items').textContent = '$' + sub.toFixed(2);
  document.getElementById('t_exact').textContent = exact ? '$' + EXACT_FEE.toFixed(2) : '—';
  document.getElementById('t_grand').textContent = '$' + (sub + exactFee).toFixed(2) + '+';
}

// ── Venue toggle ─────────────────────────────────────────────────────────
function setVenue(type) {
  document.getElementById('venue_type_input').value = type;
  document.getElementById('btn_venue').classList.toggle('active', type === 'venue');
  document.getElementById('btn_residential').classList.toggle('active', type === 'residential');
  const row = document.getElementById('venue_pickup_row');
  const inp = document.getElementById('venue_latest_pickup');
  row.style.display = type === 'venue' ? 'block' : 'none';
  inp.required = type === 'venue';
}
setVenue('venue');

// ── Availability check (called when dates change) ─────────────────────────
function onDateChange() {
  const start = document.getElementById('event_start_date').value;
  const end   = document.getElementById('event_end_date').value;
  if (!start || !end || end < start) return;
  document.getElementById('avail_note').textContent = 'Checking availability…';
  fetch(`/availability?start=${start}&end=${end}`)
    .then(r => r.json())
    .then(data => {
      document.getElementById('avail_note').textContent = '✅ Availability updated for your dates.';
      Object.entries(data).forEach(([id, avail]) => {
        const input = document.getElementById('qty_' + id);
        const badge = document.getElementById('avail_' + id);
        if (!input) return;
        input.dataset.max = avail;
        input.max = avail;
        if (avail === 0) {
          badge.textContent = 'SOLD OUT for these dates';
          badge.className = 'avail-badge out';
          input.value = 0;
        } else if (avail <= 3) {
          badge.textContent = avail + ' left!';
          badge.className = 'avail-badge low';
        } else {
          badge.textContent = avail + ' available';
          badge.className = 'avail-badge ok';
        }
        if (parseInt(input.value) > avail) { input.value = avail; }
      });
      updateTotals();
    })
    .catch(() => {
      document.getElementById('avail_note').textContent = 'Could not check availability — please proceed.';
    });
}

// ── Distance calc (debounced, runs when address fields change) ────────────
let distTimer;
function scheduleDistanceCalc() {
  clearTimeout(distTimer);
  distTimer = setTimeout(() => {
    const street = document.getElementById('event_street').value;
    const city   = document.getElementById('event_city').value;
    const state  = document.getElementById('event_state').value;
    const zip    = document.getElementById('event_zip').value;
    if (street && city && state && zip) {
      const addr = `${street}, ${city}, ${state} ${zip}`;
      fetch(`/delivery_fee?address=${encodeURIComponent(addr)}`)
        .then(r => r.json())
        .then(d => {
          document.getElementById('t_delivery').textContent = '$' + d.fee.toFixed(2) + ' (' + d.note + ')';
        })
        .catch(() => {});
    }
  }, 800);
}

// ── Prevent double submit ─────────────────────────────────────────────────
document.getElementById('bookingForm').addEventListener('submit', function() {
  const btn = document.getElementById('submitBtn');
  btn.disabled = true; btn.textContent = 'Submitting…';
});

// Set min date to today
const today = new Date().toISOString().split('T')[0];
document.getElementById('event_start_date').min = today;
document.getElementById('event_end_date').min   = today;
</script>
</body></html>
"""


SUCCESS_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
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
    <div class="icon">✅</div>
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


ADMIN_LOGIN_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
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
    <h1>🔐 Admin Login</h1>
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
  <title>Admin — {{ business_name }}</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:-apple-system,sans-serif;background:#f0f4f8;color:#1a202c;min-height:100vh}
    header{background:linear-gradient(135deg,#1a365d,#2b6cb0);color:white;padding:1.25rem 2rem;display:flex;justify-content:space-between;align-items:center}
    header h1{font-size:1.3rem}
    .logout{background:rgba(255,255,255,.2);color:white;border:1px solid rgba(255,255,255,.4);padding:.4rem .9rem;border-radius:6px;cursor:pointer;font-size:.85rem;text-decoration:none}
    .container{max-width:1100px;margin:0 auto;padding:1.5rem 1rem}
    .stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:1rem;margin-bottom:1.5rem}
    .stat{background:white;border-radius:10px;padding:1.25rem;box-shadow:0 2px 8px rgba(0,0,0,.07);text-align:center}
    .stat-num{font-size:2rem;font-weight:700;color:#2b6cb0}
    .stat-label{font-size:.8rem;color:#718096;text-transform:uppercase;letter-spacing:.5px;margin-top:.25rem}
    .card{background:white;border-radius:12px;box-shadow:0 2px 12px rgba(0,0,0,.08);margin-bottom:1.5rem;overflow:hidden}
    .card-header{padding:1rem 1.5rem;background:#ebf4ff;font-weight:700;color:#2b6cb0;font-size:.95rem;text-transform:uppercase;letter-spacing:.5px}
    table{width:100%;border-collapse:collapse}
    th{padding:10px 12px;text-align:left;font-size:.8rem;color:#718096;text-transform:uppercase;letter-spacing:.4px;border-bottom:1px solid #e2e8f0}
    td{padding:10px 12px;border-bottom:1px solid #f0f4f8;font-size:.9rem;vertical-align:middle}
    tr:last-child td{border-bottom:none}
    tr:hover td{background:#f7fafc}
    .badge{display:inline-block;padding:.2rem .6rem;border-radius:20px;font-size:.75rem;font-weight:700;text-transform:uppercase}
    .badge-pending{background:#fefcbf;color:#975a16}
    .badge-confirmed{background:#c6f6d5;color:#276749}
    .badge-cancelled{background:#fed7d7;color:#9b2c2c}
    .btn{display:inline-block;padding:.3rem .8rem;border-radius:6px;font-size:.8rem;font-weight:600;cursor:pointer;border:none;text-decoration:none}
    .btn-view{background:#ebf4ff;color:#2b6cb0}
    .btn-confirm{background:#c6f6d5;color:#276749}
    .btn-cancel{background:#fed7d7;color:#9b2c2c}
    .inv-row{display:grid;grid-template-columns:2fr 1fr 1fr 1fr;padding:.75rem 1.5rem;border-bottom:1px solid #f0f4f8;align-items:center;font-size:.9rem}
    .inv-row:last-child{border-bottom:none}
    .inv-header{background:#ebf4ff;font-weight:700;font-size:.8rem;color:#2b6cb0;text-transform:uppercase}
    .filter-bar{padding:.75rem 1.5rem;background:#f7fafc;border-bottom:1px solid #e2e8f0;display:flex;gap:.5rem;flex-wrap:wrap}
    .filter-btn{padding:.3rem .8rem;border-radius:6px;font-size:.82rem;font-weight:600;cursor:pointer;border:1.5px solid #cbd5e0;background:white;color:#4a5568;text-decoration:none}
    .filter-btn.active{border-color:#2b6cb0;background:#ebf4ff;color:#2b6cb0}
    .empty{padding:2rem;text-align:center;color:#a0aec0;font-size:.95rem}
    @media(max-width:600px){.stats{grid-template-columns:1fr 1fr}td,th{padding:8px}}
  </style>
</head>
<body>
<header>
  <h1>📊 {{ business_name }} — Admin</h1>
  <a href="/admin/logout" class="logout">Sign Out</a>
</header>

<div class="container">

  <!-- Stats -->
  <div class="stats">
    <div class="stat"><div class="stat-num">{{ stats.total }}</div><div class="stat-label">Total Bookings</div></div>
    <div class="stat"><div class="stat-num" style="color:#975a16">{{ stats.pending }}</div><div class="stat-label">Pending</div></div>
    <div class="stat"><div class="stat-num" style="color:#276749">{{ stats.confirmed }}</div><div class="stat-label">Confirmed</div></div>
    <div class="stat"><div class="stat-num">${{ "%.0f"|format(stats.revenue) }}</div><div class="stat-label">Confirmed Revenue</div></div>
  </div>

  <!-- Inventory Snapshot -->
  <div class="card">
    <div class="card-header">📦 Inventory — Available Today</div>
    <div class="inv-row inv-header">
      <div>Item</div><div>Total Stock</div><div>Reserved</div><div>Available</div>
    </div>
    {% for item in inventory %}
    <div class="inv-row">
      <div>{{ item.name }}</div>
      <div>{{ item.total }}</div>
      <div style="color:#e53e3e">{{ item.reserved }}</div>
      <div style="font-weight:700;color:{% if item.available == 0 %}#e53e3e{% elif item.available <= 3 %}#d69e2e{% else %}#38a169{% endif %}">
        {{ item.available }}{% if item.available == 0 %} SOLD OUT{% endif %}
      </div>
    </div>
    {% endfor %}
  </div>

  <!-- Bookings -->
  <div class="card">
    <div class="card-header">📋 Bookings</div>
    <div class="filter-bar">
      <a href="/admin/dashboard" class="filter-btn {% if not status_filter %}active{% endif %}">All ({{ stats.total }})</a>
      <a href="/admin/dashboard?status=pending"   class="filter-btn {% if status_filter=='pending' %}active{% endif %}">Pending ({{ stats.pending }})</a>
      <a href="/admin/dashboard?status=confirmed" class="filter-btn {% if status_filter=='confirmed' %}active{% endif %}">Confirmed ({{ stats.confirmed }})</a>
      <a href="/admin/dashboard?status=cancelled" class="filter-btn {% if status_filter=='cancelled' %}active{% endif %}">Cancelled</a>
    </div>
    {% if bookings %}
    <table>
      <thead>
        <tr>
          <th>#</th><th>Customer</th><th>Event Dates</th><th>Items</th><th>Total</th><th>Status</th><th>Actions</th>
        </tr>
      </thead>
      <tbody>
        {% for b in bookings %}
        <tr>
          <td style="font-weight:700;color:#2b6cb0">#{{ b.id }}</td>
          <td>
            <div style="font-weight:600">{{ b.full_name }}</div>
            <div style="font-size:.8rem;color:#718096">{{ b.email }}</div>
          </td>
          <td>
            <div>{{ b.event_start_date }}</div>
            {% if b.event_end_date != b.event_start_date %}
            <div style="font-size:.8rem;color:#718096">→ {{ b.event_end_date }}</div>
            {% endif %}
          </td>
          <td style="font-size:.82rem;max-width:200px">{{ b.items_summary }}</td>
          <td style="font-weight:700">${{ "%.2f"|format(b.grand_total or 0) }}</td>
          <td><span class="badge badge-{{ b.status }}">{{ b.status }}</span></td>
          <td>
            <a href="/admin/booking/{{ b.id }}" class="btn btn-view">View</a>
            {% if b.status == 'pending' %}
            <form method="POST" action="/admin/booking/{{ b.id }}/confirm" style="display:inline">
              <button class="btn btn-confirm" onclick="return confirm('Confirm payment received for #{{ b.id }}?')">✓ Paid</button>
            </form>
            {% endif %}
            {% if b.status != 'cancelled' %}
            <form method="POST" action="/admin/booking/{{ b.id }}/cancel" style="display:inline">
              <button class="btn btn-cancel" onclick="return confirm('Cancel booking #{{ b.id }}?')">✕</button>
            </form>
            {% endif %}
          </td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
    {% else %}
    <div class="empty">No bookings found.</div>
    {% endif %}
  </div>

</div>
</body></html>
"""


ADMIN_BOOKING_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
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
    .badge-confirmed{background:#c6f6d5;color:#276749}
    .badge-cancelled{background:#fed7d7;color:#9b2c2c}
    table{width:100%;border-collapse:collapse;font-size:.9rem}
    th{padding:8px 10px;text-align:left;color:#718096;font-size:.78rem;text-transform:uppercase;border-bottom:1px solid #e2e8f0}
    td{padding:8px 10px;border-bottom:1px solid #f0f4f8}
    .total-row{font-weight:700;background:#1a365d;color:white}
    .total-row td{padding:10px}
    .actions{display:flex;gap:.75rem;flex-wrap:wrap}
    .btn{padding:.6rem 1.2rem;border-radius:8px;font-size:.9rem;font-weight:600;cursor:pointer;border:none;text-decoration:none;display:inline-block}
    .btn-back{background:#f0f4f8;color:#4a5568}
    .btn-confirm{background:#38a169;color:white}
    .btn-cancel{background:#e53e3e;color:white}
    a{color:#2b6cb0}
  </style>
</head>
<body>
<header>
  <h1>Booking #{{ b.id }}</h1>
  <a href="/admin/dashboard" style="color:white;text-decoration:none;font-size:.9rem">← Back to Dashboard</a>
</header>
<div class="container">

  <span class="badge badge-{{ b.status }}">{{ b.status|upper }}</span>
  <div style="font-size:.8rem;color:#718096;margin-bottom:1rem">Received: {{ b.created_at }}</div>

  <div class="card">
    <h2>👤 Customer</h2>
    <div class="row">
      <span class="k">Name</span><span class="v">{{ b.full_name }}</span>
      {% if b.company_name %}<span class="k">Company</span><span class="v">{{ b.company_name }}</span>{% endif %}
      <span class="k">Address</span><span class="v">{{ b.renter_street }}, {{ b.renter_city }}, {{ b.renter_state }} {{ b.renter_zip }}</span>
      <span class="k">Phone</span><span class="v"><a href="tel:{{ b.phone }}">{{ b.phone }}</a></span>
      <span class="k">Email</span><span class="v"><a href="mailto:{{ b.email }}">{{ b.email }}</a></span>
    </div>
  </div>

  <div class="card">
    <h2>📅 Event</h2>
    <div class="row">
      <span class="k">Dates</span><span class="v">{{ b.event_start_date }} → {{ b.event_end_date }}</span>
      <span class="k">Start Time</span><span class="v">{{ b.event_start_time }}</span>
      <span class="k">End Time</span><span class="v">{{ b.event_end_time }}</span>
      <span class="k">Setup Time</span><span class="v">{{ b.setup_time }}</span>
      <span class="k">Venue Type</span><span class="v" style="text-transform:capitalize">{{ b.venue_type }}</span>
      {% if b.venue_latest_pickup %}<span class="k">Latest Pickup</span><span class="v">{{ b.venue_latest_pickup }}</span>{% endif %}
      <span class="k">Event Address</span><span class="v">{{ b.event_street }}, {{ b.event_city }}, {{ b.event_state }} {{ b.event_zip }}</span>
      <span class="k">Deliver To</span><span class="v">{{ b.delivery_location }}</span>
    </div>
  </div>

  <div class="card">
    <h2>🪑 Items & Totals</h2>
    <table>
      <thead><tr><th>Item</th><th style="text-align:center">Qty</th><th style="text-align:right">Unit</th><th style="text-align:right">Total</th></tr></thead>
      <tbody>
        {% for item in items %}
        <tr>
          <td>{{ item.name }}</td>
          <td style="text-align:center">{{ item.qty }}</td>
          <td style="text-align:right">${{ "%.2f"|format(item.unit_price) }}</td>
          <td style="text-align:right;font-weight:600">${{ "%.2f"|format(item.total) }}</td>
        </tr>
        {% endfor %}
        {% if b.exact_time_delivery %}
        <tr><td colspan="3">Exact Time Delivery</td><td style="text-align:right;font-weight:600">$175.00</td></tr>
        {% endif %}
        <tr><td colspan="3">Delivery Fee ({{ b.distance_miles or '?' }} mi)</td><td style="text-align:right;font-weight:600">${{ "%.2f"|format(b.delivery_fee or 0) }}</td></tr>
        <tr class="total-row"><td colspan="3">TOTAL</td><td style="text-align:right">${{ "%.2f"|format(b.grand_total or 0) }}</td></tr>
      </tbody>
    </table>
  </div>

  {% if b.notes %}
  <div class="card">
    <h2>💬 Notes</h2>
    <p style="color:#4a5568;line-height:1.6">{{ b.notes }}</p>
  </div>
  {% endif %}

  <div class="actions">
    <a href="/admin/dashboard" class="btn btn-back">← Dashboard</a>
    {% if b.status == 'pending' %}
    <form method="POST" action="/admin/booking/{{ b.id }}/confirm">
      <button class="btn btn-confirm" onclick="return confirm('Confirm payment received?')">✓ Confirm Payment Received</button>
    </form>
    {% endif %}
    {% if b.status != 'cancelled' %}
    <form method="POST" action="/admin/booking/{{ b.id }}/cancel">
      <button class="btn btn-cancel" onclick="return confirm('Cancel this booking?')">✕ Cancel Booking</button>
    </form>
    {% endif %}
  </div>
</div>
</body></html>
"""


# ══════════════════════════════════════════════════════════════════════════════
#  ROUTES — BOOKING FORM
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/", methods=["GET"])
def index():
    return render_template_string(FORM_HTML,
        business_name=BUSINESS_NAME,
        products=PRODUCTS,
        exact_time_fee=EXACT_TIME_FEE,
        error=None,
        form={},
    )


@app.route("/availability")
def availability():
    """Returns available quantities for each product for a given date range."""
    start = request.args.get("start", "")
    end   = request.args.get("end",   "")
    if not start or not end:
        return jsonify({p["id"]: p["total"] for p in PRODUCTS})
    avail = get_available(start, end)
    return jsonify(avail)


@app.route("/delivery_fee")
def delivery_fee_check():
    """Returns delivery fee estimate for a given address (called by JS)."""
    address = request.args.get("address", "")
    miles   = get_distance_miles(address) if address else None
    fee, note = calc_delivery_fee(miles)
    return jsonify({"fee": fee, "note": note, "miles": miles})


@app.route("/submit", methods=["POST"])
def submit():
    f = request.form

    # ── Parse fields ─────────────────────────────────────────────────────
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

    if not email or not full_name:
        return render_template_string(FORM_HTML, business_name=BUSINESS_NAME,
            products=PRODUCTS, exact_time_fee=EXACT_TIME_FEE,
            error="Name and email are required.", form=f), 400

    # ── Check inventory availability for requested dates ──────────────────
    avail = get_available(event_start_date, event_end_date)
    order_items = []
    subtotal    = 0.0
    errors      = []

    for p in PRODUCTS:
        qty = int(f.get(f"qty_{p['id']}", 0) or 0)
        qty = max(0, qty)
        if qty == 0:
            continue
        max_avail = avail.get(p["id"], p["total"])
        if qty > max_avail:
            errors.append(f"Only {max_avail} {p['name']} available for those dates (you requested {qty}).")
            qty = max_avail  # cap it
        if qty > 0:
            line = round(qty * p["price"], 2)
            subtotal += line
            order_items.append({"id": p["id"], "name": p["name"],
                                 "qty": qty, "unit_price": p["price"], "total": line})

    if errors:
        return render_template_string(FORM_HTML, business_name=BUSINESS_NAME,
            products=PRODUCTS, exact_time_fee=EXACT_TIME_FEE,
            error=" | ".join(errors), form=f), 400

    # ── Calculate delivery fee ────────────────────────────────────────────
    event_address = f"{event_street}, {event_city}, {event_state} {event_zip}"
    miles = get_distance_miles(event_address)
    delivery_fee, delivery_note = calc_delivery_fee(miles)

    # ── Calculate total ───────────────────────────────────────────────────
    exact_fee   = EXACT_TIME_FEE if exact_delivery else 0.0
    grand_total = round(subtotal + exact_fee + delivery_fee, 2)

    # ── Save to database ──────────────────────────────────────────────────
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
                    items_json, items_subtotal, exact_time_fee, grand_total,
                    notes
                ) VALUES (
                    %s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,
                    %s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s
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
                json.dumps(order_items), subtotal, exact_fee, grand_total,
                notes,
            ))
            booking_id = cur.fetchone()[0]
            conn.commit()
            cur.close()
            conn.close()
            log.info(f"Booking #{booking_id} saved for {full_name}")
        except Exception as e:
            log.error(f"DB insert error: {e}")

    # ── Send emails ───────────────────────────────────────────────────────
    booking_data = {
        "id": booking_id, "full_name": full_name, "company_name": company_name,
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
        "grand_total": grand_total, "notes": notes,
    }
    send_owner_email(booking_data)
    send_customer_email(booking_data)

    return render_template_string(SUCCESS_HTML,
        business_name=BUSINESS_NAME,
        business_phone=BUSINESS_PHONE,
        name=full_name.split()[0],
        email=email,
        booking_id=booking_id,
    )


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
    status_filter = request.args.get("status", "")
    conn = get_db()
    bookings, stats = [], {"total": 0, "pending": 0, "confirmed": 0, "revenue": 0}
    inventory_status = []

    if conn:
        try:
            cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)

            # Stats
            cur.execute("SELECT COUNT(*) FROM bookings")
            stats["total"] = cur.fetchone()[0]
            cur.execute("SELECT COUNT(*) FROM bookings WHERE status='pending'")
            stats["pending"] = cur.fetchone()[0]
            cur.execute("SELECT COUNT(*) FROM bookings WHERE status='confirmed'")
            stats["confirmed"] = cur.fetchone()[0]
            cur.execute("SELECT COALESCE(SUM(grand_total),0) FROM bookings WHERE status='confirmed'")
            stats["revenue"] = float(cur.fetchone()[0])

            # Bookings list
            q = "SELECT * FROM bookings"
            p = []
            if status_filter:
                q += " WHERE status=%s"; p.append(status_filter)
            q += " ORDER BY created_at DESC LIMIT 100"
            cur.execute(q, p)
            rows = cur.fetchall()

            for row in rows:
                b = dict(row)
                items = json.loads(b.get("items_json") or "[]")
                b["items_summary"] = ", ".join(f"{i['qty']}× {i['name']}" for i in items[:2])
                if len(items) > 2:
                    b["items_summary"] += f" +{len(items)-2} more"
                bookings.append(b)

            # Inventory snapshot (reserved = sum of confirmed bookings for today onward)
            today_str = date.today().isoformat()
            avail = get_available(today_str, "2099-12-31")
            for p in PRODUCTS:
                reserved = p["total"] - avail.get(p["id"], p["total"])
                inventory_status.append({
                    "name": p["name"], "total": p["total"],
                    "reserved": reserved, "available": avail.get(p["id"], p["total"])
                })

            cur.close()
            conn.close()
        except Exception as e:
            log.error(f"Admin dashboard error: {e}")

    return render_template_string(ADMIN_DASH_HTML,
        business_name=BUSINESS_NAME,
        bookings=bookings,
        stats=stats,
        inventory=inventory_status,
        status_filter=status_filter,
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
                b = dict(row)
                items = json.loads(b.get("items_json") or "[]")
            cur.close()
            conn.close()
        except Exception as e:
            log.error(f"Booking fetch error: {e}")

    if not b:
        return "Booking not found", 404

    return render_template_string(ADMIN_BOOKING_HTML,
        business_name=BUSINESS_NAME, b=b, items=items)


@app.route("/admin/booking/<int:booking_id>/confirm", methods=["POST"])
@admin_required
def confirm_booking(booking_id):
    """Mark a booking as confirmed (payment received) — locks inventory."""
    conn = get_db()
    if conn:
        try:
            cur = conn.cursor()
            cur.execute("UPDATE bookings SET status='confirmed' WHERE id=%s", (booking_id,))
            conn.commit()
            cur.close()
            conn.close()
            log.info(f"Booking #{booking_id} confirmed")
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


# ══════════════════════════════════════════════════════════════════════════════
#  UTILITY ROUTES
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/health")
def health():
    return jsonify({"status": "running", "time": datetime.now(timezone.utc).isoformat()}), 200


@app.route("/test")
def test():
    cfg = {
        "BUSINESS_NAME":     bool(BUSINESS_NAME),
        "BUSINESS_ADDRESS":  bool(BUSINESS_ADDRESS),
        "DATABASE_URL":      bool(DATABASE_URL),
        "GOOGLE_MAPS_KEY":   bool(GOOGLE_MAPS_KEY),
        "OWNER_EMAIL":       bool(OWNER_EMAIL),
        "GMAIL_USER":        bool(GMAIL_USER),
        "GMAIL_APP_PASSWORD":bool(GMAIL_APP_PASSWORD),
        "ADMIN_PASSWORD":    bool(ADMIN_PASSWORD),
    }
    db_ok = False
    if DATABASE_URL:
        try:
            c = get_db(); c.close(); db_ok = True
        except Exception:
            pass
    return jsonify({
        "app":       "Rental Booking & Inventory System",
        "status":    "✅ All configured" if all(cfg.values()) else "⚠️ Some settings missing",
        "config":    cfg,
        "db_connected": db_ok,
        "products":  len(PRODUCTS),
    }), 200


if __name__ == "__main__":
    port = int(os.getenv("PORT", 5000))
    log.info(f"Starting {BUSINESS_NAME} on port {port}")
    app.run(host="0.0.0.0", port=port, debug=False)
