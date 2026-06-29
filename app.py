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

import os, json, logging, smtplib, secrets
from datetime import datetime, timezone, date
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from functools import wraps

import requests
import psycopg2
import psycopg2.extras
import stripe
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
    {"id": "banquet_tables", "name": "8x30 Wood Banquet Tables",         "price": 15.00, "total": 10},
    {"id": "round_tables",   "name": "60in Wood Round Tables",           "price": 15.00, "total": 10},
    {"id": "cocktail_30",    "name": "30in Cocktail Tables",             "price": 15.00, "total": 10},
    {"id": "cocktail_cloth", "name": "Cocktail Table Cloths",            "price": 8.00,  "total": 10},
]

EXACT_TIME_FEE  = 175.00
DEPOSIT_PERCENT = 0.25   # 25% deposit required


# ══════════════════════════════════════════════════════════════════════════════
#  CONFIGURATION  (set in Render.com → Environment)
# ══════════════════════════════════════════════════════════════════════════════

def _float(key, default):
    try:
        return float(os.getenv(key, "") or default)
    except ValueError:
        return float(default)

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

        # Migrations: add new columns to existing tables (safe to run every time)
        migrations = [
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS stripe_payment_link TEXT",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS stripe_session_id TEXT",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS final_payment_link TEXT",
            "ALTER TABLE bookings ADD COLUMN IF NOT EXISTS final_reminder_sent BOOLEAN DEFAULT FALSE",
            "CREATE UNIQUE INDEX IF NOT EXISTS customers_email_idx ON customers (email) WHERE email IS NOT NULL",
        ]
        for m in migrations:
            try:
                cur.execute(m)
            except Exception as me:
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
            return [dict(r) for r in rows]
    except Exception as e:
        log.error(f"get_products error: {e}")
    return PRODUCTS


# ══════════════════════════════════════════════════════════════════════════════
#  INVENTORY CHECKING
# ══════════════════════════════════════════════════════════════════════════════

def get_available(start_date_str, end_date_str, exclude_id=None):
    """
    Returns {product_id: available_qty} for a date range.
    Only CONFIRMED bookings lock inventory.
    """
    available = {p["id"]: p["total"] for p in get_products()}
    conn = get_db()
    if not conn:
        return available
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
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
    return fee, f"{miles} mi x ${DELIVERY_RATE:.2f}/mi"


# ══════════════════════════════════════════════════════════════════════════════
#  STRIPE
# ══════════════════════════════════════════════════════════════════════════════

def create_stripe_payment_link(booking_id, deposit_amount, customer_email, items_desc, product_name=None):
    """Create a Stripe Payment Link. Returns (url, error)."""
    if not STRIPE_SECRET_KEY:
        log.warning("STRIPE_SECRET_KEY not set — cannot create payment link")
        return None, "Stripe not configured"
    try:
        name = product_name or f"25% Deposit — Booking #{booking_id}"
        # Create a product for this booking
        product = stripe.Product.create(
            name=name,
            description=(items_desc[:500] if items_desc else "Rental deposit"),
        )
        # Create a one-time price
        price = stripe.Price.create(
            unit_amount=int(round(deposit_amount * 100)),  # cents
            currency="usd",
            product=product.id,
        )
        # Build payment link kwargs
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
        return link.url, None
    except Exception as e:
        log.error(f"Stripe Payment Link error: {e}")
        return None, str(e)


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
    subject = f"New Booking #{b.get('id')} — {b.get('full_name')} | {b.get('event_start_date')}"
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
      <tr><td style="padding:8px 12px;color:#718096;width:160px">Dates</td><td style="padding:8px 12px;font-weight:600">{b.get('event_start_date')} to {b.get('event_end_date')}</td></tr>
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
    plain = f"NEW BOOKING #{b.get('id')}\n{b.get('full_name')} | {b.get('email')} | {b.get('phone')}\nEvent: {b.get('event_start_date')}\nTotal: ${b.get('grand_total',0):.2f}\n"
    _send_email(OWNER_EMAIL, subject, html, plain, reply_to=b.get("email"))


def send_customer_email(b):
    """Send initial confirmation to customer (booking received, pending review)."""
    email = b.get("email")
    first = b.get("full_name", "").split()[0]
    if not email:
        return
    subject = f"We received your rental request! — {BUSINESS_NAME}"
    html = f"""
<html><body style="font-family:-apple-system,sans-serif;background:#f0f4f8;padding:2rem 1rem">
<div style="max-width:500px;margin:0 auto;background:white;border-radius:12px;overflow:hidden;box-shadow:0 4px 16px rgba(0,0,0,.08)">
  <div style="background:linear-gradient(135deg,#1a365d,#2b6cb0);padding:2rem;color:white;text-align:center">
    <h2 style="margin:0">Request Received!</h2>
    <p style="margin:.5rem 0 0;opacity:.85">{BUSINESS_NAME}</p>
  </div>
  <div style="padding:2rem">
    <p>Hi <strong>{first}</strong>,</p>
    <p style="color:#4a5568;line-height:1.7;margin:.75rem 0">Thank you for your rental inquiry! We've received your request for <strong>{b.get('event_start_date')}</strong>.
    We will review your booking and get back to you shortly with an invoice and next steps.</p>
    <div style="background:#f0f4f8;border-radius:8px;padding:1rem;margin:1rem 0;text-align:center">
      <p style="margin:0;font-weight:600;color:#2d3748">Booking Reference</p>
      <p style="margin:.3rem 0 0;font-size:1.5rem;font-weight:700;color:#2b6cb0">#{b.get('id')}</p>
    </div>
    <p style="color:#4a5568;line-height:1.7">Keep this reference number handy.{f" Questions? Call <strong>{BUSINESS_PHONE}</strong>." if BUSINESS_PHONE else ""}</p>
    <p style="color:#2d3748;font-weight:600;margin-top:1.5rem">— The {BUSINESS_NAME} Team</p>
  </div>
</div></body></html>"""
    plain = f"Hi {first},\n\nThank you! Your rental request for {b.get('event_start_date')} has been received.\n\nBooking Reference: #{b.get('id')}\n\nWe'll review and send you an invoice soon.\n\n— {BUSINESS_NAME}"
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

    item_rows = ""
    for it in items:
        item_rows += f"""
        <tr>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0">{it['name']}</td>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0;text-align:center">{it['qty']}</td>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0;text-align:right">${it['unit_price']:.2f}</td>
          <td style="padding:8px 12px;border-bottom:1px solid #e2e8f0;text-align:right;font-weight:600">${it['total']:.2f}</td>
        </tr>"""

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
      Great news &mdash; your rental request has been reviewed and we have availability for your event!
      Please review your invoice below, make your payment, and read the rental agreement at the bottom of this email.
    </p>

    <!-- Event Summary box -->
    <div style="background:#f0fff4;border:1.5px solid #68d391;border-radius:10px;padding:1rem 1.25rem;margin-bottom:1.5rem;font-size:.9rem;color:#2d3748">
      <div style="margin-bottom:.3rem"><strong>Event Date:</strong> {b.get('event_start_date')} &rarr; {b.get('event_end_date')}</div>
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
  Date:       {b.get('event_start_date')} - {b.get('event_end_date')}
  Location:   {event_addr}
  Deliver to: {b.get('delivery_location','')}

INVOICE
{"".join(f"  {i['qty']}x {i['name']} @ ${i['unit_price']:.2f} = ${i['total']:.2f}\n" for i in items)}{"  Exact Time Delivery: $175.00\n" if exact else ""}  Delivery Fee: ${b.get('delivery_fee',0):.2f}
  ─────────────────────────────
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
      Thank you for thinking of us for your event on <strong>{b.get('event_start_date')}</strong>.
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
    plain = f"Hi {first},\n\nThank you for your interest in {BUSINESS_NAME}. Unfortunately, we are unable to accommodate your rental request for {b.get('event_start_date')} at this time.\n\nWe hope to serve you in the future.{f' Please call {BUSINESS_PHONE} if you have questions.' if BUSINESS_PHONE else ''}\n\n— {BUSINESS_NAME}"
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

    <p style="color:#2d3748;font-weight:600;margin-top:1.5rem">&mdash; The {BUSINESS_NAME} Team</p>
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
  ──────────────────────────
  REMAINING DUE:   ${remaining_amount:.2f}

PAY NOW: {payment_link if payment_link else 'Contact us to complete payment.'}

Failure to make final payment may result in your order being canceled.
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
  </div>

  <div class="card">
    <h2>Event Details</h2>
    <div class="row">
      <div class="field"><label>Event Start Date <span class="required">*</span></label><input id="event_start_date" name="event_start_date" type="date" required onchange="onDateChange()" value="{{ form.event_start_date or '' }}"></div>
      <div class="field"><label>Event End Date <span class="required">*</span></label><input id="event_end_date" name="event_end_date" type="date" required onchange="onDateChange()" value="{{ form.event_end_date or '' }}"></div>
    </div>
    <div class="row">
      <div class="field"><label>Event Start Time <span class="required">*</span></label><input name="event_start_time" type="time" required value="{{ form.event_start_time or '' }}"></div>
      <div class="field"><label>Event End Time <span class="required">*</span></label><input name="event_end_time" type="time" required value="{{ form.event_end_time or '' }}"></div>
    </div>
    <div class="row"><div class="field"><label>Setup Time <span class="required">*</span></label><input name="setup_time" type="time" required value="{{ form.setup_time or '' }}"></div></div>
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

  <div class="card">
    <h2>Select Your Items</h2>
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
        <button type="button" class="qty-btn" onclick="changeQty('{{ p.id }}',-1)">-</button>
        <input class="qty-input" type="number" id="qty_{{ p.id }}" name="qty_{{ p.id }}" value="0" min="0" max="{{ p.total }}" data-price="{{ p.price }}" data-max="{{ p.total }}" oninput="updateTotals()">
        <button type="button" class="qty-btn" onclick="changeQty('{{ p.id }}',1)">+</button>
      </div>
      <div class="product-sub" id="sub_{{ p.id }}">-</div>
    </div>
    {% endfor %}
  </div>

  <div class="total-bar">
    <div class="total-row"><span>Items Subtotal</span><span id="t_items">$0.00</span></div>
    <div class="total-row"><span>Exact Time Delivery</span><span id="t_exact">-</span></div>
    <div class="total-row"><span>Delivery Fee</span><span id="t_delivery">Calculated after review</span></div>
    <div class="total-row grand"><span>Estimated Total</span><span id="t_grand">$0.00</span></div>
    <p class="total-note">Final delivery fee confirmed after we verify your address. This is a quote request, not a charge.</p>
  </div>

  <button type="submit" class="submit-btn" id="submitBtn">Send Quote Request</button>
</form>
</div>
<script>
const EXACT_FEE = {{ exact_time_fee }};
function changeQty(id,delta){const i=document.getElementById('qty_'+id);const m=parseInt(i.dataset.max);let v=Math.max(0,Math.min(m,parseInt(i.value||0)+delta));i.value=v;updateTotals();}
function updateTotals(){let sub=0;document.querySelectorAll('.qty-input').forEach(i=>{const qty=parseInt(i.value)||0;const price=parseFloat(i.dataset.price);const id=i.id.replace('qty_','');const line=qty*price;sub+=line;const el=document.getElementById('sub_'+id);el.textContent=qty>0?'$'+line.toFixed(2):'-';el.classList.toggle('has-val',qty>0);});const exact=document.getElementById('exact_time_cb').checked;const ef=exact?EXACT_FEE:0;document.getElementById('t_items').textContent='$'+sub.toFixed(2);document.getElementById('t_exact').textContent=exact?'$'+EXACT_FEE.toFixed(2):'-';document.getElementById('t_grand').textContent='$'+(sub+ef).toFixed(2)+'+';}
function setVenue(type){document.getElementById('venue_type_input').value=type;document.getElementById('btn_venue').classList.toggle('active',type==='venue');document.getElementById('btn_residential').classList.toggle('active',type==='residential');const row=document.getElementById('venue_pickup_row');const inp=document.getElementById('venue_latest_pickup');row.style.display=type==='venue'?'block':'none';inp.required=type==='venue';}
setVenue('venue');
function onDateChange(){const start=document.getElementById('event_start_date').value;const end=document.getElementById('event_end_date').value;if(!start||!end||end<start)return;document.getElementById('avail_note').textContent='Checking availability...';fetch('/availability?start='+start+'&end='+end).then(r=>r.json()).then(data=>{document.getElementById('avail_note').textContent='Availability updated for your dates.';Object.entries(data).forEach(([id,avail])=>{const input=document.getElementById('qty_'+id);const badge=document.getElementById('avail_'+id);if(!input)return;input.dataset.max=avail;input.max=avail;if(avail===0){badge.textContent='SOLD OUT for these dates';badge.className='avail-badge out';input.value=0;}else if(avail<=3){badge.textContent=avail+' left!';badge.className='avail-badge low';}else{badge.textContent=avail+' available';badge.className='avail-badge ok';}if(parseInt(input.value)>avail){input.value=avail;}});updateTotals();}).catch(()=>{document.getElementById('avail_note').textContent='Could not check availability - please proceed.';});}
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
    <a href="/admin/logout" class="logout-btn">Sign Out</a>
  </div>
</div>

<div class="main">
  <div class="page-title">Dashboard</div>

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

  <!-- ── Inventory ── -->
  <div class="section-title">Inventory</div>
  <div class="inv-grid">
    {% for item in inventory %}
    {% set pct = ((item.reserved / item.total * 100) | int) if item.total > 0 else 0 %}
    <div class="inv-card">
      <div class="inv-name" title="{{ item.name }}">{{ item.name }}</div>
      <div class="inv-meta">
        <span class="inv-reserved">{{ item.reserved }} reserved</span>
        <span class="{% if item.available == 0 %}inv-avail-zero{% elif item.available <= 3 %}inv-avail-low{% else %}inv-avail-ok{% endif %}">
          {{ item.available }}/{{ item.total }}{% if item.available == 0 %} SOLD OUT{% endif %}
        </span>
      </div>
      <div class="inv-bar">
        <div class="inv-fill" style="width:{{ pct }}%;background:{% if pct >= 100 %}#ef4444{% elif pct >= 70 %}#f59e0b{% else %}#10b981{% endif %}"></div>
      </div>
    </div>
    {% endfor %}
  </div>

  <!-- ── Bookings ── -->
  <div class="tabs">
    <a href="/admin/dashboard" class="tab {% if not status_filter %}active{% endif %}">All&nbsp;({{ stats.total }})</a>
    <a href="/admin/dashboard?status=pending"   class="tab {% if status_filter=='pending'   %}active{% endif %}">Pending&nbsp;({{ stats.pending }})</a>
    <a href="/admin/dashboard?status=accepted"  class="tab {% if status_filter=='accepted'  %}active{% endif %}">Awaiting Payment&nbsp;({{ stats.accepted }})</a>
    <a href="/admin/dashboard?status=confirmed" class="tab {% if status_filter=='confirmed' %}active{% endif %}">Confirmed&nbsp;({{ stats.confirmed }})</a>
    <a href="/admin/dashboard?status=denied"    class="tab {% if status_filter=='denied'    %}active{% endif %}">Denied</a>
    <a href="/admin/dashboard?status=cancelled" class="tab {% if status_filter=='cancelled' %}active{% endif %}">Cancelled</a>
  </div>
  <div class="table-card">
    {% if bookings %}
    <table>
      <thead>
        <tr>
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
        <tr>
          <td style="font-weight:700;color:#2563eb;font-size:.83rem">#{{ b.id }}</td>
          <td>
            <div class="client-cell">
              <div class="avatar" style="background:{{ b.avatar_color }}">{{ b.avatar_initials }}</div>
              <div>
                <div class="client-name">{{ b.full_name }}</div>
                <div class="client-email">{{ b.email }}</div>
              </div>
            </div>
          </td>
          <td><span class="badge badge-{{ b.status }}">{{ b.status | capitalize }}</span></td>
          <td>
            <div class="date-range">
              <span>{{ b.event_start_date }}</span>
              <span class="date-arrow">→</span>
              <span>{{ b.event_end_date }}</span>
            </div>
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
            </div>
          </td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
    {% else %}
    <div class="empty-state">No bookings found.</div>
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
  <a href="/admin/dashboard" style="color:white;text-decoration:none;font-size:.9rem">Back to Dashboard</a>
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

  {% if b.status == 'pending' %}
  <div class="alert">
    This booking is waiting for your review. Click Accept to send the customer their invoice, contract, and Stripe payment link.
    Click Deny to send a polite rejection.
  </div>
  {% endif %}

  <div class="card">
    <h2>Customer</h2>
    <div class="row">
      <span class="k">Name</span><span class="v">{{ b.full_name }}</span>
      {% if b.company_name %}<span class="k">Company</span><span class="v">{{ b.company_name }}</span>{% endif %}
      <span class="k">Address</span><span class="v">{{ b.renter_street }}, {{ b.renter_city }}, {{ b.renter_state }} {{ b.renter_zip }}</span>
      <span class="k">Phone</span><span class="v"><a href="tel:{{ b.phone }}">{{ b.phone }}</a></span>
      <span class="k">Email</span><span class="v"><a href="mailto:{{ b.email }}">{{ b.email }}</a></span>
    </div>
  </div>

  <div class="card">
    <h2>Event</h2>
    <div class="row">
      <span class="k">Dates</span><span class="v">{{ b.event_start_date }} - {{ b.event_end_date }}</span>
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
    <h2>Items & Totals</h2>
    <table>
      <thead><tr><th>Item</th><th style="text-align:center">Qty</th><th style="text-align:right">Unit</th><th style="text-align:right">Total</th></tr></thead>
      <tbody>
        {% for item in items %}
        <tr><td>{{ item.name }}</td><td style="text-align:center">{{ item.qty }}</td><td style="text-align:right">${{ "%.2f"|format(item.unit_price) }}</td><td style="text-align:right;font-weight:600">${{ "%.2f"|format(item.total) }}</td></tr>
        {% endfor %}
        {% if b.exact_time_delivery %}
        <tr><td colspan="3">Exact Time Delivery</td><td style="text-align:right;font-weight:600">$175.00</td></tr>
        {% endif %}
        <tr><td colspan="3">Delivery Fee ({{ b.distance_miles or '?' }} mi)</td><td style="text-align:right;font-weight:600">${{ "%.2f"|format(b.delivery_fee or 0) }}</td></tr>
        <tr class="total-row"><td colspan="3">TOTAL</td><td style="text-align:right">${{ "%.2f"|format(b.grand_total or 0) }}</td></tr>
        {% if days_until <= 7 %}
        <tr style="background:#fff5f5"><td colspan="3" style="color:#c53030;font-weight:700">Due Now (event within 7 days — full payment required)</td><td style="text-align:right;font-weight:700;color:#c53030">${{ "%.2f"|format(b.grand_total or 0) }}</td></tr>
        {% else %}
        <tr style="background:#f0fff4"><td colspan="3" style="color:#276749;font-weight:700">25% Deposit Due Now</td><td style="text-align:right;font-weight:700;color:#276749">${{ "%.2f"|format((b.grand_total or 0) * 0.25) }}</td></tr>
        <tr><td colspan="3" style="color:#718096">Remaining Balance (due 48 hrs before event)</td><td style="text-align:right;color:#718096">${{ "%.2f"|format((b.grand_total or 0) * 0.75) }}</td></tr>
        {% endif %}
      </tbody>
    </table>
  </div>

  {% if b.notes %}
  <div class="card"><h2>Notes</h2><p style="color:#4a5568;line-height:1.6">{{ b.notes }}</p></div>
  {% endif %}

  <div class="actions">
    <a href="/admin/dashboard" class="btn btn-back">Back to Dashboard</a>
    {% if b.status == 'pending' %}
    <form method="POST" action="/admin/booking/{{ b.id }}/accept">
      <button class="btn btn-accept" onclick="return confirm('Accept this booking? This will create a Stripe payment link and email {{ b.email }} with their invoice, contract, and payment instructions.')">
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
    <form method="POST" action="/admin/booking/{{ b.id }}/send-final-reminder">
      <button class="btn btn-reminder" onclick="return confirm('Send final payment reminder to {{ b.email }}? This will create a new Stripe link for the remaining 75% balance.')">
        Send Final Payment Reminder
      </button>
    </form>
    {% endif %}
  </div>

  {% if b.final_payment_link %}
  <div style="background:#fff8f3;border:2px solid #dd6b20;border-radius:10px;padding:1.1rem 1.25rem;margin-top:1rem">
    <div style="font-weight:700;color:#c05621;margin-bottom:.4rem">Final Payment Link Sent</div>
    <a href="{{ b.final_payment_link }}" target="_blank" style="font-size:.85rem;word-break:break-all">{{ b.final_payment_link }}</a>
  </div>
  {% endif %}
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

    # Check inventory
    avail = get_available(event_start_date, event_end_date)
    order_items, subtotal, errors = [], 0.0, []
    for p in _products:
        qty = int(f.get(f"qty_{p['id']}", 0) or 0)
        qty = max(0, qty)
        if qty == 0:
            continue
        max_avail = avail.get(p["id"], p["total"])
        if qty > max_avail:
            errors.append(f"Only {max_avail} {p['name']} available for those dates (requested {qty}).")
            qty = max_avail
        if qty > 0:
            line = round(qty * p["price"], 2)
            subtotal += line
            order_items.append({"id": p["id"], "name": p["name"],
                                 "qty": qty, "unit_price": p["price"], "total": line})
    if errors:
        return render_template_string(FORM_HTML, business_name=BUSINESS_NAME,
            products=_products, exact_time_fee=EXACT_TIME_FEE,
            error=" | ".join(errors), form=f), 400

    # Delivery
    event_address = f"{event_street}, {event_city}, {event_state} {event_zip}"
    miles = get_distance_miles(event_address)
    delivery_fee, delivery_note = calc_delivery_fee(miles)

    exact_fee   = EXACT_TIME_FEE if exact_delivery else 0.0
    grand_total = round(subtotal + exact_fee + delivery_fee, 2)

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

    # Upsert customer record — if email already exists update their info, else insert
    cust_conn = get_db()
    if cust_conn and email:
        try:
            cust_cur = cust_conn.cursor()
            cust_cur.execute("""
                INSERT INTO customers (full_name, company_name, email, phone, street, city, state, zip)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                ON CONFLICT (email) DO UPDATE SET
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
    <a href="/admin/logout" class="logout-btn">Sign Out</a>
  </div>
</div>
<div class="main">
  <div class="page-title">Inventory</div>
  <div class="page-sub">Edit item names, rental prices, and total quantities. Changes take effect immediately on the booking form.</div>

  {% if flash_ok %}<div class="flash flash-ok">✓ {{ flash_ok }}</div>{% endif %}
  {% if flash_err %}<div class="flash flash-err">⚠ {{ flash_err }}</div>{% endif %}

  <div class="card">
    <div class="card-header">
      <span>Rental Items ({{ products|length }})</span>
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
</body></html>
"""


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
    bookings = []
    stats = {"total": 0, "pending": 0, "accepted": 0, "confirmed": 0, "revenue": 0, "amount_due": 0}
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

            q = "SELECT * FROM bookings"
            p = []
            if status_filter:
                q += " WHERE status=%s"; p.append(status_filter)
            q += " ORDER BY created_at DESC LIMIT 100"
            cur.execute(q, p)
            rows = cur.fetchall()
            _avatar_colors = ['#ef4444','#f97316','#eab308','#22c55e','#14b8a6',
                               '#3b82f6','#8b5cf6','#ec4899','#06b6d4','#84cc16']
            for row in rows:
                b = dict(row)
                items = json.loads(b.get("items_json") or "[]")
                b["items_summary"] = ", ".join(f"{i['qty']}x {i['name']}" for i in items[:2])
                if len(items) > 2:
                    b["items_summary"] += f" +{len(items)-2} more"
                # Payment label + class
                if b["status"] == "confirmed":
                    if b.get("final_payment_link"):
                        b["pay_label"], b["pay_class"] = "Partially Paid", "pay-partial"
                    else:
                        b["pay_label"], b["pay_class"] = "Paid", "pay-paid"
                elif b["status"] == "accepted":
                    b["pay_label"], b["pay_class"] = "Payment Due", "pay-due"
                else:
                    b["pay_label"], b["pay_class"] = "—", "pay-none"
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

    # Calculate days until event for payment label logic
    days_until = 999
    try:
        event_dt = datetime.strptime(str(b.get("event_start_date", ""))[:10], "%Y-%m-%d").date()
        days_until = (event_dt - date.today()).days
    except Exception:
        pass

    return render_template_string(ADMIN_BOOKING_HTML,
        business_name=BUSINESS_NAME, b=b, items=items, days_until=days_until)


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
            b = dict(row)
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

    # Create Stripe Payment Link
    payment_link, stripe_error = create_stripe_payment_link(
        booking_id, charge_amount, b.get("email"), stripe_desc, product_name
    )
    if stripe_error:
        log.warning(f"Stripe error for #{booking_id}: {stripe_error}")

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
            b = dict(row)
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
            cur.close()
            conn.close()
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
                        cur.close()
                        conn.close()
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
            b = dict(row)
    except Exception as e:
        log.error(f"Final reminder fetch error: {e}")
        return redirect(url_for("admin_booking", booking_id=booking_id))

    if not b:
        return "Booking not found", 404

    grand_total     = float(b.get("grand_total") or 0)
    remaining       = round(grand_total * 0.75, 2)
    items_list      = ", ".join(f"{i['qty']}x {i['name']}" for i in json.loads(b.get("items_json") or "[]"))
    product_name    = f"Final Payment — Booking #{booking_id}"

    payment_link, err = create_stripe_payment_link(
        booking_id, remaining, b.get("email"), items_list, product_name
    )
    if err:
        log.warning(f"Stripe error for final payment #{booking_id}: {err}")

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
    <a href="/admin/logout" class="logout-btn">Sign Out</a>
  </div>
</div>
<div class="main">
  <div class="top-row">
    <div class="page-title">Customers</div>
    <button class="btn btn-primary" onclick="toggleAdd()">+ Add Customer</button>
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
          <td class="cust-email"><a href="mailto:{{ c.email }}" style="color:#2563eb;text-decoration:none">{{ c.email or '—' }}</a></td>
          <td><a href="tel:{{ c.phone }}" style="color:#374151;text-decoration:none">{{ c.phone or '—' }}</a></td>
          <td style="color:#6b7280;font-size:.82rem">
            {% if c.city %}{{ c.city }}{% if c.state %}, {{ c.state }}{% endif %}{% else %}—{% endif %}
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

ADMIN_CUSTOMER_EDIT_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
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
          <td>{{ b.event_start_date }}</td>
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
    products = get_products()
    flash_ok  = request.args.get("ok",  "")
    flash_err = request.args.get("err", "")
    return render_template_string(ADMIN_INVENTORY_HTML,
        business_name=BUSINESS_NAME, products=products,
        flash_ok=flash_ok, flash_err=flash_err)


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
        cur.execute("""
            INSERT INTO customers (full_name, company_name, email, phone, street, city, state, zip, notes)
            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
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
                c = dict(row)
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
        cur.execute("""
            UPDATE customers SET full_name=%s, company_name=%s, email=%s, phone=%s,
                street=%s, city=%s, state=%s, zip=%s, notes=%s
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


@app.route("/cron/final-reminders")
def cron_final_reminders():
    """
    Called daily by an external cron (e.g. cron-job.org).
    Finds all confirmed bookings whose event is exactly 2 days away
    and sends them a final payment reminder if not already sent.

    Secure with CRON_SECRET: call as /cron/final-reminders?secret=YOUR_SECRET
    """
    if CRON_SECRET and request.args.get("secret") != CRON_SECRET:
        return jsonify({"error": "Unauthorized"}), 401

    from datetime import timedelta
    target_date = (date.today() + timedelta(days=2)).isoformat()
    conn = get_db()
    if not conn:
        return jsonify({"error": "DB unavailable"}), 500

    sent = []
    errors = []
    try:
        cur = conn.cursor(cursor_factory=psycopg2.extras.DictCursor)
        cur.execute("""
            SELECT * FROM bookings
            WHERE status = 'confirmed'
              AND event_start_date = %s
              AND (final_reminder_sent IS NULL OR final_reminder_sent = FALSE)
        """, (target_date,))
        rows = cur.fetchall()
        cur.close()
        conn.close()

        for row in rows:
            b = dict(row)
            booking_id   = b["id"]
            grand_total  = float(b.get("grand_total") or 0)
            remaining    = round(grand_total * 0.75, 2)
            items_list   = ", ".join(f"{i['qty']}x {i['name']}" for i in json.loads(b.get("items_json") or "[]"))
            product_name = f"Final Payment — Booking #{booking_id}"

            payment_link, err = create_stripe_payment_link(
                booking_id, remaining, b.get("email"), items_list, product_name
            )

            # Save link + mark reminder sent
            conn2 = get_db()
            if conn2:
                try:
                    cur2 = conn2.cursor()
                    cur2.execute(
                        "UPDATE bookings SET final_payment_link=%s, final_reminder_sent=TRUE WHERE id=%s",
                        (payment_link, booking_id)
                    )
                    conn2.commit()
                    cur2.close()
                    conn2.close()
                except Exception as e:
                    log.error(f"Cron DB update error #{booking_id}: {e}")

            b["final_payment_link"] = payment_link
            send_final_payment_email(b, remaining, payment_link)
            sent.append(booking_id)
            log.info(f"Auto final reminder sent for booking #{booking_id}")

    except Exception as e:
        log.error(f"Cron error: {e}")
        errors.append(str(e))

    return jsonify({
        "date_checked": target_date,
        "reminders_sent": sent,
        "errors": errors,
    }), 200


# ══════════════════════════════════════════════════════════════════════════════
#  ROUTES — PAYMENT SUCCESS
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/payment/success/<int:booking_id>")
def payment_success(booking_id):
    return render_template_string(PAYMENT_SUCCESS_HTML,
        business_name=BUSINESS_NAME,
        business_phone=BUSINESS_PHONE,
        booking_id=booking_id,
    )


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
        "STRIPE_SECRET_KEY": bool(STRIPE_SECRET_KEY),
        "BASE_URL":          bool(BASE_URL),
    }
    db_ok = False
    if DATABASE_URL:
        try:
            c = get_db(); c.close(); db_ok = True
        except Exception:
            pass
    return jsonify({
        "app":          "Rental Booking & Inventory System v3.0",
        "status":       "All configured" if all(cfg.values()) else "Some settings missing",
        "config":       cfg,
        "db_connected": db_ok,
        "products":     len(PRODUCTS),
        "stripe_ready": bool(STRIPE_SECRET_KEY),
    }), 200


if __name__ == "__main__":
    port = int(os.getenv("PORT", 5000))
    log.info(f"Starting {BUSINESS_NAME} on port {port}")
    app.run(host="0.0.0.0", port=port, debug=False)
