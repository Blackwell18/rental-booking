#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════╗
║         RENTAL BUSINESS BOOKING SYSTEM                  ║
║  Free replacement for Formsite + Booqable                ║
╠══════════════════════════════════════════════════════════╣
║  • Hosts a professional booking form online              ║
║  • Live price calculator as customers pick items         ║
║  • Auto-calculates delivery fee ($3.80/mi over 15 mi)   ║
║  • Emails YOU every new inquiry with full breakdown      ║
║  • Emails customer a confirmation they'll hear from you  ║
╚══════════════════════════════════════════════════════════╝
  Setup: fill in .env file → deploy to Render.com → done.
  See SETUP_GUIDE.txt for step-by-step instructions.
"""

import os
import logging
import smtplib
from datetime import datetime, timezone
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart

import requests
from flask import Flask, request, render_template_string, redirect, url_for, jsonify
from dotenv import load_dotenv

load_dotenv()
logging.basicConfig(level=logging.INFO, format="%(asctime)s  %(levelname)s  %(message)s")
log = logging.getLogger(__name__)

app = Flask(__name__)


# ══════════════════════════════════════════════════════════════════════════════
#  YOUR RENTAL CATALOG
#  Edit prices or add/remove items here anytime.
# ══════════════════════════════════════════════════════════════════════════════

PRODUCTS = [
    {"id": "chairs",         "name": "White Folding Plastic Chairs",     "price": 2.75,  "max": 200},
    {"id": "tables_6ft",     "name": "6ft White Folding Plastic Tables", "price": 8.00,  "max": 30},
    {"id": "banquet_tables", "name": "8×30 Wood Banquet Tables",         "price": 15.00, "max": 10},
    {"id": "round_tables",   "name": "60\" Wood Round Tables",           "price": 15.00, "max": 10},
    {"id": "cocktail_30",    "name": "30\" Cocktail Tables",             "price": 15.00, "max": 10},
    {"id": "cocktail_cloth", "name": "Cocktail Table Cloths",            "price": 8.00,  "max": 10},
]


# ══════════════════════════════════════════════════════════════════════════════
#  CONFIGURATION  (set these in your .env file on Render.com)
# ══════════════════════════════════════════════════════════════════════════════

BUSINESS_NAME    = os.getenv("BUSINESS_NAME",    "Premier Event Rentals")
BUSINESS_PHONE   = os.getenv("BUSINESS_PHONE",   "")
BUSINESS_EMAIL   = os.getenv("BUSINESS_EMAIL",   "")
BUSINESS_ADDRESS = os.getenv("BUSINESS_ADDRESS", "")

DELIVERY_FREE_MILES = float(os.getenv("DELIVERY_FREE_MILES", "15"))
DELIVERY_RATE       = float(os.getenv("DELIVERY_RATE",       "3.80"))

GOOGLE_MAPS_KEY  = os.getenv("GOOGLE_MAPS_KEY",  "")
OWNER_EMAIL      = os.getenv("OWNER_EMAIL",      "")
GMAIL_USER       = os.getenv("GMAIL_USER",       "")
GMAIL_APP_PASSWORD = os.getenv("GMAIL_APP_PASSWORD", "")


# ══════════════════════════════════════════════════════════════════════════════
#  BOOKING FORM  (what customers see)
# ══════════════════════════════════════════════════════════════════════════════

FORM_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Book a Rental — {{ business_name }}</title>
  <style>
    *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }

    body {
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
      background: #f0f4f8;
      color: #1a202c;
      min-height: 100vh;
    }

    header {
      background: linear-gradient(135deg, #1a365d 0%, #2b6cb0 100%);
      color: white;
      padding: 2.5rem 1.5rem;
      text-align: center;
    }
    header h1 { font-size: 2rem; font-weight: 700; letter-spacing: -0.5px; }
    header p  { margin-top: .5rem; opacity: .85; font-size: 1.05rem; }

    .container { max-width: 700px; margin: 0 auto; padding: 2rem 1rem 4rem; }

    .card {
      background: white;
      border-radius: 12px;
      box-shadow: 0 2px 12px rgba(0,0,0,.08);
      padding: 1.75rem;
      margin-bottom: 1.5rem;
    }
    .card h2 {
      font-size: 1.1rem;
      font-weight: 700;
      color: #2b6cb0;
      border-bottom: 2px solid #ebf4ff;
      padding-bottom: .6rem;
      margin-bottom: 1.25rem;
      text-transform: uppercase;
      letter-spacing: .5px;
    }

    .field { margin-bottom: 1.1rem; }
    .field label {
      display: block;
      font-size: .85rem;
      font-weight: 600;
      color: #4a5568;
      margin-bottom: .35rem;
    }
    .field input, .field textarea, .field select {
      width: 100%;
      padding: .65rem .85rem;
      border: 1.5px solid #cbd5e0;
      border-radius: 8px;
      font-size: 1rem;
      color: #1a202c;
      transition: border-color .15s;
      background: #fff;
    }
    .field input:focus, .field textarea:focus, .field select:focus {
      outline: none;
      border-color: #2b6cb0;
      box-shadow: 0 0 0 3px rgba(43,108,176,.12);
    }
    .field textarea { resize: vertical; min-height: 80px; }

    .row { display: grid; grid-template-columns: 1fr 1fr; gap: 1rem; }
    @media (max-width: 520px) { .row { grid-template-columns: 1fr; } }

    /* ── Product rows ── */
    .product-row {
      display: grid;
      grid-template-columns: 1fr auto auto;
      align-items: center;
      gap: .75rem;
      padding: .85rem 0;
      border-bottom: 1px solid #f0f4f8;
    }
    .product-row:last-child { border-bottom: none; }

    .product-info .product-name  { font-weight: 600; font-size: .97rem; }
    .product-info .product-price { font-size: .82rem; color: #718096; margin-top: .1rem; }

    .qty-control {
      display: flex;
      align-items: center;
      gap: 0;
      border: 1.5px solid #cbd5e0;
      border-radius: 8px;
      overflow: hidden;
    }
    .qty-btn {
      background: #f7fafc;
      border: none;
      width: 34px;
      height: 36px;
      font-size: 1.2rem;
      color: #2b6cb0;
      cursor: pointer;
      line-height: 1;
      transition: background .12s;
    }
    .qty-btn:hover { background: #ebf4ff; }
    .qty-input {
      width: 52px !important;
      border: none !important;
      border-left: 1.5px solid #cbd5e0 !important;
      border-right: 1.5px solid #cbd5e0 !important;
      border-radius: 0 !important;
      text-align: center;
      font-size: .97rem;
      font-weight: 600;
      padding: .4rem .2rem !important;
      box-shadow: none !important;
    }
    .qty-input:focus { outline: none; border-color: #cbd5e0 !important; }

    .product-subtotal {
      text-align: right;
      min-width: 70px;
      font-weight: 600;
      color: #2d3748;
      font-size: .97rem;
    }
    .product-subtotal.has-value { color: #2b6cb0; }

    /* ── Delivery toggle ── */
    .delivery-toggle {
      display: flex;
      gap: 1rem;
      margin-bottom: 1.1rem;
    }
    .toggle-btn {
      flex: 1;
      padding: .7rem;
      border: 2px solid #cbd5e0;
      border-radius: 8px;
      background: white;
      font-size: .95rem;
      font-weight: 600;
      color: #718096;
      cursor: pointer;
      text-align: center;
      transition: all .15s;
    }
    .toggle-btn.active {
      border-color: #2b6cb0;
      background: #ebf4ff;
      color: #2b6cb0;
    }

    /* ── Total bar ── */
    .total-bar {
      background: linear-gradient(135deg, #1a365d 0%, #2b6cb0 100%);
      border-radius: 12px;
      padding: 1.25rem 1.75rem;
      color: white;
      margin-bottom: 1.5rem;
    }
    .total-row {
      display: flex;
      justify-content: space-between;
      align-items: center;
      padding: .25rem 0;
      font-size: .95rem;
      opacity: .85;
    }
    .total-row.grand {
      font-size: 1.35rem;
      font-weight: 700;
      opacity: 1;
      border-top: 1px solid rgba(255,255,255,.25);
      margin-top: .5rem;
      padding-top: .6rem;
    }
    .note {
      font-size: .8rem;
      color: #718096;
      margin-top: .4rem;
      font-style: italic;
    }

    /* ── Submit button ── */
    .submit-btn {
      width: 100%;
      padding: 1rem;
      background: linear-gradient(135deg, #1a365d, #2b6cb0);
      color: white;
      border: none;
      border-radius: 10px;
      font-size: 1.1rem;
      font-weight: 700;
      cursor: pointer;
      letter-spacing: .3px;
      transition: opacity .15s, transform .1s;
    }
    .submit-btn:hover   { opacity: .92; }
    .submit-btn:active  { transform: scale(.99); }
    .submit-btn:disabled { opacity: .6; cursor: not-allowed; }

    .required { color: #e53e3e; }
  </style>
</head>
<body>

<header>
  <h1>{{ business_name }}</h1>
  <p>Request a rental quote — we'll get back to you quickly!</p>
</header>

<div class="container">
<form method="POST" action="/submit" id="bookingForm">

  <!-- ── Contact Info ─────────────────────────────── -->
  <div class="card">
    <h2>📋 Your Information</h2>
    <div class="row">
      <div class="field">
        <label>First Name <span class="required">*</span></label>
        <input type="text" name="first_name" required placeholder="Jane">
      </div>
      <div class="field">
        <label>Last Name <span class="required">*</span></label>
        <input type="text" name="last_name" required placeholder="Smith">
      </div>
    </div>
    <div class="row">
      <div class="field">
        <label>Email Address <span class="required">*</span></label>
        <input type="email" name="email" required placeholder="jane@email.com">
      </div>
      <div class="field">
        <label>Phone Number</label>
        <input type="tel" name="phone" placeholder="(555) 000-0000">
      </div>
    </div>
  </div>

  <!-- ── Event Details ────────────────────────────── -->
  <div class="card">
    <h2>📅 Event Details</h2>
    <div class="row">
      <div class="field">
        <label>Event Date <span class="required">*</span></label>
        <input type="date" name="event_date" required>
      </div>
      <div class="field">
        <label>Event Type</label>
        <input type="text" name="event_type" placeholder="Wedding, Birthday, Corporate…">
      </div>
    </div>
    <div class="row">
      <div class="field">
        <label>Setup Time (when do we deliver?)</label>
        <input type="time" name="setup_time">
      </div>
      <div class="field">
        <label>Pickup Time (when do we collect?)</label>
        <input type="time" name="pickup_time">
      </div>
    </div>
  </div>

  <!-- ── Items ────────────────────────────────────── -->
  <div class="card">
    <h2>🪑 Select Your Items</h2>
    {% for p in products %}
    <div class="product-row">
      <div class="product-info">
        <div class="product-name">{{ p.name }}</div>
        <div class="product-price">${{ "%.2f"|format(p.price) }} each &nbsp;·&nbsp; up to {{ p.max }} available</div>
      </div>
      <div class="qty-control">
        <button type="button" class="qty-btn" onclick="changeQty('{{ p.id }}', -1)">−</button>
        <input class="qty-input" type="number" id="qty_{{ p.id }}" name="qty_{{ p.id }}"
               value="0" min="0" max="{{ p.max }}"
               data-price="{{ p.price }}" data-max="{{ p.max }}"
               oninput="updateTotals()">
        <button type="button" class="qty-btn" onclick="changeQty('{{ p.id }}', 1)">+</button>
      </div>
      <div class="product-subtotal" id="sub_{{ p.id }}">—</div>
    </div>
    {% endfor %}
  </div>

  <!-- ── Delivery ──────────────────────────────────── -->
  <div class="card">
    <h2>🚚 Delivery or Pickup?</h2>
    <div class="delivery-toggle">
      <div class="toggle-btn active" id="btn_delivery" onclick="setDelivery(true)">📦 Delivery</div>
      <div class="toggle-btn"       id="btn_pickup"   onclick="setDelivery(false)">🏠 I'll Pick Up</div>
    </div>
    <div id="delivery_fields">
      <div class="field">
        <label>Delivery Address <span class="required">*</span></label>
        <input type="text" id="delivery_address" name="delivery_address"
               placeholder="123 Main St, Orlando, FL 32801">
      </div>
      <p class="note">Delivery is free within {{ free_miles }} miles. Beyond that, we charge ${{ rate }}/mile.</p>
    </div>
    <input type="hidden" name="delivery_type" id="delivery_type_input" value="delivery">
  </div>

  <!-- ── Notes ────────────────────────────────────── -->
  <div class="card">
    <h2>💬 Anything Else?</h2>
    <div class="field">
      <label>Additional Notes or Special Requests</label>
      <textarea name="notes" placeholder="Tell us anything else about your event…"></textarea>
    </div>
  </div>

  <!-- ── Estimated Total ───────────────────────────── -->
  <div class="total-bar">
    <div class="total-row">
      <span>Items Subtotal</span>
      <span id="total_items">$0.00</span>
    </div>
    <div class="total-row">
      <span>Delivery Fee</span>
      <span id="total_delivery">Calculated at checkout</span>
    </div>
    <div class="total-row grand">
      <span>Estimated Total</span>
      <span id="total_grand">$0.00</span>
    </div>
  </div>
  <p class="note" style="text-align:center; margin-top:-1rem; margin-bottom:1.5rem;">
    ✉️ This is a quote request, not a charge. We'll confirm final pricing and availability by email.
  </p>

  <button type="submit" class="submit-btn" id="submitBtn">
    Send Quote Request →
  </button>

</form>
</div>

<script>
  // ── Live price calculator ──────────────────────────────────────────
  function changeQty(id, delta) {
    const input = document.getElementById('qty_' + id);
    const max   = parseInt(input.dataset.max);
    let val = parseInt(input.value || 0) + delta;
    val = Math.max(0, Math.min(max, val));
    input.value = val;
    updateTotals();
  }

  function updateTotals() {
    let subtotal = 0;
    document.querySelectorAll('.qty-input').forEach(input => {
      const qty   = parseInt(input.value) || 0;
      const price = parseFloat(input.dataset.price);
      const id    = input.id.replace('qty_', '');
      const sub   = qty * price;
      subtotal += sub;
      const el = document.getElementById('sub_' + id);
      if (qty > 0) {
        el.textContent = '$' + sub.toFixed(2);
        el.classList.add('has-value');
      } else {
        el.textContent = '—';
        el.classList.remove('has-value');
      }
    });
    document.getElementById('total_items').textContent = '$' + subtotal.toFixed(2);
    document.getElementById('total_grand').textContent = '$' + subtotal.toFixed(2) + '+';
  }

  // ── Delivery/pickup toggle ─────────────────────────────────────────
  function setDelivery(isDelivery) {
    document.getElementById('delivery_fields').style.display = isDelivery ? 'block' : 'none';
    document.getElementById('delivery_address').required = isDelivery;
    document.getElementById('delivery_type_input').value = isDelivery ? 'delivery' : 'pickup';
    document.getElementById('btn_delivery').classList.toggle('active', isDelivery);
    document.getElementById('btn_pickup').classList.toggle('active', !isDelivery);
  }

  // ── Prevent double-submit ──────────────────────────────────────────
  document.getElementById('bookingForm').addEventListener('submit', function() {
    const btn = document.getElementById('submitBtn');
    btn.disabled = true;
    btn.textContent = 'Sending…';
  });

  // Set min date to today
  document.querySelector('input[name="event_date"]').min =
    new Date().toISOString().split('T')[0];
</script>
</body>
</html>
"""


# ── Thank-you page (shown after successful submission) ──────────────────────
SUCCESS_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Request Received — {{ business_name }}</title>
  <style>
    body {
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
      background: #f0f4f8; display: flex; align-items: center;
      justify-content: center; min-height: 100vh; margin: 0;
    }
    .box {
      background: white; border-radius: 16px; padding: 3rem 2.5rem;
      text-align: center; max-width: 480px; width: 90%;
      box-shadow: 0 4px 24px rgba(0,0,0,.1);
    }
    .icon { font-size: 3.5rem; margin-bottom: 1rem; }
    h1 { color: #1a365d; font-size: 1.6rem; margin-bottom: .75rem; }
    p  { color: #4a5568; line-height: 1.6; margin-bottom: .75rem; }
    .back {
      display: inline-block; margin-top: 1.5rem;
      padding: .7rem 1.5rem; background: #2b6cb0; color: white;
      border-radius: 8px; text-decoration: none; font-weight: 600;
    }
  </style>
</head>
<body>
  <div class="box">
    <div class="icon">✅</div>
    <h1>Request Received!</h1>
    <p>Thanks, <strong>{{ name }}</strong>! We got your rental request and will send you a quote soon.</p>
    <p>Check your email at <strong>{{ email }}</strong> for a confirmation.</p>
    {% if business_phone %}
    <p>Questions? Call us at <strong>{{ business_phone }}</strong>.</p>
    {% endif %}
    <a href="/" class="back">← Submit Another Request</a>
  </div>
</body>
</html>
"""


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
        r.raise_for_status()
        el = r.json()["rows"][0]["elements"][0]
        if el.get("status") != "OK":
            return None
        return round(el["distance"]["value"] / 1609.344, 1)
    except Exception as e:
        log.error(f"Distance API error: {e}")
        return None


def calc_delivery_fee(miles):
    if miles is None:
        return 0.0, "Could not calculate (verify address)"
    if miles <= DELIVERY_FREE_MILES:
        return 0.0, f"{miles} mi — within {DELIVERY_FREE_MILES}-mile free zone ✓"
    billable = round(miles - DELIVERY_FREE_MILES, 1)
    fee      = round(billable * DELIVERY_RATE, 2)
    return fee, f"{miles} mi — {billable} billable miles × ${DELIVERY_RATE}/mi"


# ══════════════════════════════════════════════════════════════════════════════
#  ORDER PARSING
# ══════════════════════════════════════════════════════════════════════════════

def parse_order(form_data):
    """Extract selected products and quantities from the submitted form."""
    order_items = []
    subtotal    = 0.0

    for p in PRODUCTS:
        qty = int(form_data.get(f"qty_{p['id']}", 0) or 0)
        qty = max(0, min(qty, p["max"]))  # clamp to inventory limits
        if qty > 0:
            line_total = round(qty * p["price"], 2)
            subtotal  += line_total
            order_items.append({
                "name":       p["name"],
                "qty":        qty,
                "unit_price": p["price"],
                "total":      line_total,
            })

    return order_items, round(subtotal, 2)


# ══════════════════════════════════════════════════════════════════════════════
#  EMAILS
# ══════════════════════════════════════════════════════════════════════════════

def _send_email(to_addr, subject, html_body, plain_body, reply_to=None):
    if not all([GMAIL_USER, GMAIL_APP_PASSWORD]):
        log.warning("Gmail not configured — skipping email")
        return False
    try:
        msg = MIMEMultipart("alternative")
        msg["From"]    = f"{BUSINESS_NAME} <{GMAIL_USER}>"
        msg["To"]      = to_addr
        msg["Subject"] = subject
        if reply_to:
            msg["Reply-To"] = reply_to
        msg.attach(MIMEText(plain_body, "plain"))
        msg.attach(MIMEText(html_body,  "html"))
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as s:
            s.login(GMAIL_USER, GMAIL_APP_PASSWORD)
            s.send_message(msg)
        log.info(f"Email sent → {to_addr}")
        return True
    except Exception as e:
        log.error(f"Email error: {e}")
        return False


def send_owner_notification(customer, order_items, subtotal,
                            miles, delivery_fee, delivery_note,
                            delivery_type, event_date, event_type,
                            setup_time, pickup_time, notes):
    """
    Sends you a detailed HTML email for every new inquiry.
    Reply-To is set to the customer's email so you can just hit Reply.
    """
    if not OWNER_EMAIL:
        log.warning("OWNER_EMAIL not set")
        return

    first = customer["first_name"]
    last  = customer["last_name"]
    email = customer["email"]
    phone = customer.get("phone", "Not provided")
    grand = subtotal + delivery_fee

    subject = f"📋 New Quote Request — {first} {last}  |  {event_date}"

    # ── Build items table rows ─────────────────────────────────────────────
    item_rows_html  = ""
    item_rows_plain = ""
    for item in order_items:
        item_rows_html += f"""
        <tr>
          <td style="padding:8px 12px; border-bottom:1px solid #e2e8f0;">{item['name']}</td>
          <td style="padding:8px 12px; border-bottom:1px solid #e2e8f0; text-align:center;">{item['qty']}</td>
          <td style="padding:8px 12px; border-bottom:1px solid #e2e8f0; text-align:right;">${item['unit_price']:.2f}</td>
          <td style="padding:8px 12px; border-bottom:1px solid #e2e8f0; text-align:right; font-weight:600;">${item['total']:.2f}</td>
        </tr>"""
        item_rows_plain += f"  {item['qty']}x  {item['name']}  @ ${item['unit_price']:.2f}  =  ${item['total']:.2f}\n"

    if not order_items:
        item_rows_html  = '<tr><td colspan="4" style="padding:12px; color:#718096;">No specific items selected — customer left a note.</td></tr>'
        item_rows_plain = "  (No items selected — see notes)\n"

    delivery_row_html = f"""
        <tr style="background:#fffaf0;">
          <td colspan="3" style="padding:8px 12px; border-bottom:1px solid #e2e8f0;">
            Delivery Fee <span style="color:#718096; font-size:.85em;">({delivery_note})</span>
          </td>
          <td style="padding:8px 12px; border-bottom:1px solid #e2e8f0; text-align:right; font-weight:600;">
            {'FREE' if delivery_fee == 0 else f'${delivery_fee:.2f}'}
          </td>
        </tr>""" if delivery_type == "delivery" else ""

    delivery_plain = f"\n  Delivery Fee: {'FREE' if delivery_fee == 0 else f'${delivery_fee:.2f}'} ({delivery_note})" if delivery_type == "delivery" else "\n  Delivery: Customer will pick up"

    html = f"""
<html><body style="font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif; background:#f0f4f8; margin:0; padding:2rem 1rem;">
<div style="max-width:620px; margin:0 auto;">

  <!-- Header -->
  <div style="background:linear-gradient(135deg,#1a365d,#2b6cb0); border-radius:12px 12px 0 0; padding:1.5rem 2rem; color:white;">
    <h2 style="margin:0; font-size:1.4rem;">📋 New Quote Request</h2>
    <p style="margin:.4rem 0 0; opacity:.85;">{BUSINESS_NAME}</p>
  </div>

  <!-- Body -->
  <div style="background:white; padding:2rem; border-radius:0 0 12px 12px; box-shadow:0 4px 16px rgba(0,0,0,.08);">

    <!-- Customer info -->
    <table style="width:100%; border-collapse:collapse; margin-bottom:1.5rem;">
      <tr style="background:#ebf4ff;">
        <td colspan="2" style="padding:10px 12px; font-weight:700; color:#2b6cb0; font-size:.9rem; text-transform:uppercase; letter-spacing:.5px;">
          Customer
        </td>
      </tr>
      <tr>
        <td style="padding:8px 12px; width:140px; color:#718096;">Name</td>
        <td style="padding:8px 12px; font-weight:600;">{first} {last}</td>
      </tr>
      <tr style="background:#f7fafc;">
        <td style="padding:8px 12px; color:#718096;">Email</td>
        <td style="padding:8px 12px;"><a href="mailto:{email}" style="color:#2b6cb0;">{email}</a></td>
      </tr>
      <tr>
        <td style="padding:8px 12px; color:#718096;">Phone</td>
        <td style="padding:8px 12px;">{phone}</td>
      </tr>
    </table>

    <!-- Event info -->
    <table style="width:100%; border-collapse:collapse; margin-bottom:1.5rem;">
      <tr style="background:#ebf4ff;">
        <td colspan="2" style="padding:10px 12px; font-weight:700; color:#2b6cb0; font-size:.9rem; text-transform:uppercase; letter-spacing:.5px;">
          Event Details
        </td>
      </tr>
      <tr>
        <td style="padding:8px 12px; width:140px; color:#718096;">Date</td>
        <td style="padding:8px 12px; font-weight:600;">{event_date}</td>
      </tr>
      <tr style="background:#f7fafc;">
        <td style="padding:8px 12px; color:#718096;">Type</td>
        <td style="padding:8px 12px;">{event_type or 'Not specified'}</td>
      </tr>
      <tr>
        <td style="padding:8px 12px; color:#718096;">Setup Time</td>
        <td style="padding:8px 12px;">{setup_time or 'Not specified'}</td>
      </tr>
      <tr style="background:#f7fafc;">
        <td style="padding:8px 12px; color:#718096;">Pickup Time</td>
        <td style="padding:8px 12px;">{pickup_time or 'Not specified'}</td>
      </tr>
      <tr>
        <td style="padding:8px 12px; color:#718096;">Delivery To</td>
        <td style="padding:8px 12px;">{'🚚 ' + customer.get('delivery_address','') if delivery_type == 'delivery' else '🏠 Customer pickup'}</td>
      </tr>
    </table>

    <!-- Order items -->
    <table style="width:100%; border-collapse:collapse; margin-bottom:1.5rem;">
      <tr style="background:#ebf4ff;">
        <th style="padding:10px 12px; text-align:left; color:#2b6cb0; font-size:.9rem; text-transform:uppercase; letter-spacing:.5px;">Item</th>
        <th style="padding:10px 12px; text-align:center; color:#2b6cb0; font-size:.9rem; text-transform:uppercase; letter-spacing:.5px;">Qty</th>
        <th style="padding:10px 12px; text-align:right; color:#2b6cb0; font-size:.9rem; text-transform:uppercase; letter-spacing:.5px;">Price</th>
        <th style="padding:10px 12px; text-align:right; color:#2b6cb0; font-size:.9rem; text-transform:uppercase; letter-spacing:.5px;">Total</th>
      </tr>
      {item_rows_html}
      {delivery_row_html}
      <tr style="background:#1a365d; color:white;">
        <td colspan="3" style="padding:12px; font-weight:700; font-size:1.05rem;">ESTIMATED TOTAL</td>
        <td style="padding:12px; text-align:right; font-weight:700; font-size:1.2rem;">${grand:.2f}</td>
      </tr>
    </table>

    {'<div style="background:#fffaf0; border-left:4px solid #ed8936; padding:1rem; border-radius:0 8px 8px 0; margin-bottom:1.5rem;"><strong>Customer Notes:</strong><br>' + notes + '</div>' if notes else ''}

    <!-- CTA -->
    <div style="background:#f0f4f8; border-radius:10px; padding:1.25rem; text-align:center;">
      <p style="margin:0 0 .75rem; color:#4a5568;">
        <strong>Reply directly to this email</strong> to contact {first}.
      </p>
      <p style="margin:0; font-size:.85rem; color:#718096;">
        Hit Reply — it goes straight to {email}
      </p>
    </div>

  </div>
</div>
</body></html>"""

    plain = f"""NEW QUOTE REQUEST — {BUSINESS_NAME}

CUSTOMER
  Name:   {first} {last}
  Email:  {email}
  Phone:  {phone}

EVENT
  Date:       {event_date}
  Type:       {event_type or 'Not specified'}
  Setup:      {setup_time or 'Not specified'}
  Pickup:     {pickup_time or 'Not specified'}
  Delivery:   {'To ' + customer.get('delivery_address','') if delivery_type == 'delivery' else 'Customer pickup'}

ORDER
{item_rows_plain}{delivery_plain}
  ─────────────────────────────
  ESTIMATED TOTAL:  ${grand:.2f}

{'NOTES: ' + notes if notes else ''}

Reply to this email to contact {first} at {email}.
"""

    _send_email(OWNER_EMAIL, subject, html, plain, reply_to=email)


def send_customer_confirmation(first_name, customer_email, event_date, business_phone):
    """Sends a warm 'we got your request' email to the customer."""
    subject = f"We received your rental request! — {BUSINESS_NAME}"

    html = f"""
<html><body style="font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif; background:#f0f4f8; margin:0; padding:2rem 1rem;">
<div style="max-width:500px; margin:0 auto; background:white; border-radius:12px; box-shadow:0 4px 16px rgba(0,0,0,.08); overflow:hidden;">
  <div style="background:linear-gradient(135deg,#1a365d,#2b6cb0); padding:2rem; color:white; text-align:center;">
    <h2 style="margin:0; font-size:1.5rem;">Request Received! ✅</h2>
    <p style="margin:.5rem 0 0; opacity:.85;">{BUSINESS_NAME}</p>
  </div>
  <div style="padding:2rem;">
    <p style="color:#2d3748; font-size:1.05rem; line-height:1.6;">
      Hi <strong>{first_name}</strong>,
    </p>
    <p style="color:#4a5568; line-height:1.7;">
      Thank you for your interest! We've received your rental request for
      <strong>{event_date}</strong> and we'll review it and send you a
      detailed quote as soon as possible.
    </p>
    <p style="color:#4a5568; line-height:1.7;">
      If you have any questions in the meantime, just reply to this email
      {f'or give us a call at <strong>{business_phone}</strong>' if business_phone else ''}.
    </p>
    <p style="color:#4a5568; line-height:1.7;">
      We look forward to being part of your event! 🎉
    </p>
    <p style="color:#2d3748; margin-top:1.5rem; font-weight:600;">
      — The {BUSINESS_NAME} Team
    </p>
  </div>
</div>
</body></html>"""

    plain = f"""Hi {first_name},

Thank you for your interest in {BUSINESS_NAME}!

We've received your rental request for {event_date} and will send you a detailed quote shortly.

{f'Questions? Call us at {business_phone}.' if business_phone else ''}

We look forward to being part of your event!

— The {BUSINESS_NAME} Team
"""
    _send_email(customer_email, subject, html, plain)


# ══════════════════════════════════════════════════════════════════════════════
#  ROUTES
# ══════════════════════════════════════════════════════════════════════════════

@app.route("/", methods=["GET"])
def index():
    """Show the booking form."""
    return render_template_string(
        FORM_HTML,
        business_name=BUSINESS_NAME,
        products=PRODUCTS,
        free_miles=int(DELIVERY_FREE_MILES),
        rate=f"{DELIVERY_RATE:.2f}",
    )


@app.route("/submit", methods=["POST"])
def submit():
    """Process a booking form submission."""
    f = request.form

    # Customer details
    first_name       = f.get("first_name", "").strip()
    last_name        = f.get("last_name",  "").strip()
    email            = f.get("email",      "").strip()
    phone            = f.get("phone",      "").strip()
    event_date       = f.get("event_date", "").strip()
    event_type       = f.get("event_type", "").strip()
    setup_time       = f.get("setup_time", "").strip()
    pickup_time      = f.get("pickup_time","").strip()
    delivery_address = f.get("delivery_address", "").strip()
    delivery_type    = f.get("delivery_type_input", "delivery").strip()
    notes            = f.get("notes", "").strip()

    if not email or not first_name:
        return "Missing required fields", 400

    log.info(f"New submission: {first_name} {last_name} <{email}> — {event_date}")

    # Parse order
    order_items, subtotal = parse_order(f)

    # Delivery fee
    miles, delivery_fee, delivery_note = None, 0.0, "N/A"
    if delivery_type == "delivery" and delivery_address:
        miles = get_distance_miles(delivery_address)
        delivery_fee, delivery_note = calc_delivery_fee(miles)

    customer = {
        "first_name":       first_name,
        "last_name":        last_name,
        "email":            email,
        "phone":            phone,
        "delivery_address": delivery_address,
    }

    # Send emails
    send_owner_notification(
        customer, order_items, subtotal,
        miles, delivery_fee, delivery_note,
        delivery_type, event_date, event_type,
        setup_time, pickup_time, notes,
    )
    send_customer_confirmation(first_name, email, event_date, BUSINESS_PHONE)

    # Show thank-you page
    return render_template_string(
        SUCCESS_HTML,
        business_name=BUSINESS_NAME,
        business_phone=BUSINESS_PHONE,
        name=first_name,
        email=email,
    )


@app.route("/health", methods=["GET"])
def health():
    return jsonify({"status": "running", "time": datetime.now(timezone.utc).isoformat()}), 200


@app.route("/test", methods=["GET"])
def test():
    """Visit /test to verify your configuration is complete."""
    cfg = {
        "BUSINESS_NAME":     bool(BUSINESS_NAME),
        "BUSINESS_ADDRESS":  bool(BUSINESS_ADDRESS),
        "GOOGLE_MAPS_KEY":   bool(GOOGLE_MAPS_KEY),
        "OWNER_EMAIL":       bool(OWNER_EMAIL),
        "GMAIL_USER":        bool(GMAIL_USER),
        "GMAIL_APP_PASSWORD":bool(GMAIL_APP_PASSWORD),
    }
    return jsonify({
        "app":     "Rental Booking System",
        "status":  "✅ All configured" if all(cfg.values()) else "⚠️  Some settings missing",
        "config":  cfg,
        "products": len(PRODUCTS),
    }), 200


# ─────────────────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    port = int(os.getenv("PORT", 5000))
    log.info(f"Starting {BUSINESS_NAME} Booking System on port {port}")
    app.run(host="0.0.0.0", port=port, debug=False)
