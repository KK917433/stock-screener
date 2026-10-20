#!/usr/bin/env python3
"""
INDIA MOAT SCREENER v2
=======================
What it does
  1. Pulls candidates from Screener.in (growth + quality), then enforces YOUR rules in code:
       - all-time-high quarterly sales   - all-time-high quarterly profit
       - all-time-high annual sales      - all-time-high annual profit
       - profit BREAKOUT (qtr profit >= +25% YoY and above last 4 quarters)
  2. Adds live market data (Yahoo Finance): price vs 50/200 DMA, 52-wk high, volume vs 20-day avg.
  3. Adds news for every shortlisted stock (Google News RSS) with positive/negative scoring.
  4. Works out the cycle phase of each theme (precision, T&D, chemicals, semis, rail...).
  5. Scores every stock 0-100, says Bullish / Watch / Avoid and WHY, with stop-loss + max weight.
  5b. Finds stocks where the 50-DMA and 200-DMA are meeting (golden cross / squeeze) and checks that
      debtor days and inventory days are NOT rising (working-capital health).
  6. Builds a mobile-friendly dashboard (docs/index.html) and sends Telegram/email alerts.

Modes
  python auto_screener.py --mode full   # daily: screen + fundamentals + everything
  python auto_screener.py --mode live   # intraday: refresh price/volume/news on the shortlist
  python auto_screener.py --mode demo   # fake data, to preview the dashboard

Env vars: SCREENER_USER, SCREENER_PASS  (full mode)
          TELEGRAM_TOKEN, TELEGRAM_CHAT_ID  (optional alerts)
          EMAIL_USER, EMAIL_PASS, EMAIL_TO  (optional, Gmail app password)
Educational screening aid - NOT investment advice.
"""
import os, re, io, sys, json, time, hashlib, smtplib, argparse, random
import statistics as st
from datetime import datetime, timezone, timedelta
from email.message import EmailMessage
from email.utils import parsedate_to_datetime
import xml.etree.ElementTree as ET
import requests
from bs4 import BeautifulSoup

# ----------------------------------------------------------------------------
# CONFIG - edit freely
# ----------------------------------------------------------------------------
BASE = "https://www.screener.in"
OUT_DIR = os.getenv("OUT_DIR", "site_out")
DATA_DIR = f"{OUT_DIR}/data"
DATA_FILE = f"{DATA_DIR}/state.json"
UA = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/124 Safari/537.36"}
IST = timezone(timedelta(hours=5, minutes=30))

# Wide net on Screener; the strict ATH / breakout rules are enforced in Python below.
CANDIDATE_QUERY = """Market Capitalization > 1000 AND
Sales growth 3Years > 12 AND
Profit growth 3Years > 15 AND
Return on capital employed > 15 AND
Debt to equity < 1"""

MAX_PAGES = 40
BREAKOUT_PROFIT_YOY = 25      # % qtr profit growth YoY for "breakout"
NEAR_HIGH_PCT = 5             # within x% of 52-wk high = price breakout zone
MIN_TURNOVER_CR = 2           # avg daily traded value (Rs Cr) below this = illiquid
ALERT_MIN_SCORE = 65
LIVE_SHORTLIST_MAX = 60
ENRICH_MAX = 40               # how many top stocks get concall / order-book / credit-rating deep checks
MAX_CANDIDATES = 600          # safety cap on how many Screener results are analysed
# Symbols (as on Screener.in, e.g. POLYCAB) that are ALWAYS tracked and searchable, even if they fail your rules.
# You can also add symbols without editing code: Actions > Run workflow > "watch" box.
EXTRA_WATCHLIST = []
FILING_KW = ["receipt of order", "bagging", "bags order", "order worth", "letter of award", "purchase order", "work order",
             "new order", "supply order", "preferential", "warrant", "qip", "rights issue", "allotment", "fund rais", "capital rais", "open offer",
             "stake", "acquisition", "subscription", "buyback", "bulk deal", "block deal"]
ONLY_THEMES = False   # False = scan ALL sectors (your 5 priority themes are still labelled separately)

# keyword -> matched against Screener industry tags + company name
THEMES = {
    "Precision / Aerospace / Defence": ["aerospace", "defence", "defense", "precision", "forging", "casting", "bearing", "aviation"],
    "Transformers / T&D / Power equipment": ["transformer", "electrical equipment", "cable", "switchgear", "power equipment", "t&d", "transmission", "capital goods"],
    "Specialty / Water chemicals": ["specialty chem", "chemical", "water", "agrochem", "fluoro", "pharma chem"],
    "Semiconductor / Electronics": ["semiconductor", "electronic", "ems", "power electronics", "components"],
    "Rail / Automation / Industrial": ["railway", "rail", "automation", "industrial machinery", "industrial products"],
}

THEME_INFO = {
    "Precision / Aerospace / Defence": {
        "drivers": "Defence indigenisation + export push, global aerospace OEM supply-chain shift to India, long qualification cycles (high entry barrier).",
        "risks": "Lumpy orders, government payment cycles, premium valuations."},
    "Transformers / T&D / Power equipment": {
        "drivers": "Grid expansion, renewable evacuation, data-centre/industrial power demand, long order books; limited certified capacity.",
        "risks": "Copper/CRGO input costs, new capacity from many players, valuations pricing in perfection."},
    "Specialty / Water chemicals": {
        "drivers": "China+1 shift, regulatory approvals and sticky customers, water/industrial treatment demand.",
        "risks": "Chinese dumping, pricing cycles, destocking, environmental compliance."},
    "Semiconductor / Electronics": {
        "drivers": "ISM/PLI subsidies, EMS and component localisation, electronics export growth.",
        "risks": "Long gestation, thin margins in assembly, subsidy dependence, very high valuations."},
    "Rail / Automation / Industrial": {
        "drivers": "Rail capex, Kavach/modernisation, factory automation, manufacturing capex cycle.",
        "risks": "Government order timing, working-capital stretch, cyclicality."},
}

POS_WORDS = ["order win", "bags order", "wins order", "secures order", "order book", "bags contract", "wins contract",
             "record", "capacity expansion", "expansion", "upgrade", "target price", "buy rating", "approval",
             "partnership", "profit jumps", "profit rises", "profit surges", "surges", "strong demand",
             "acquisition", "commission", "beats", "raises guidance", "buyback", "bonus", "export order", "mou"]
NEG_WORDS = ["probe", "sebi", "fraud", "downgrade", "resign", "pledge", "loss widens", "net loss", "plunge",
             "penalty", "raid", "default", "cuts guidance", "misses", "delist", "show cause", "tax demand",
             "fire at", "shutdown", "promoter sells", "stake sale", "insolvency", "qualified opinion", "auditor"]

# ---- PLI / INCENTIVE SCHEMES (approximate outlays from public announcements; verify on ministry sites) ----
PLI_SCHEMES = [
    {"scheme": "Mobile phones and specified electronic components (PLI)", "outlay_cr": 40951, "kw": ["electronic", "telecom", "consumer electronics"],
     "why": "Turn India into a global phone/electronics export base and cut import dependence."},
    {"scheme": "Electronics Component Manufacturing Scheme (ECMS)", "outlay_cr": 22919, "kw": ["electronic", "component"],
     "why": "Build local PCBs, passive parts and sub-assemblies so assemblers stop importing them."},
    {"scheme": "India Semiconductor Mission (fabs, OSAT, display)", "outlay_cr": 76000, "kw": ["semiconductor", "electronic"],
     "why": "Strategic chip self-reliance; fiscal support of up to about half of project cost."},
    {"scheme": "IT hardware PLI 2.0 (laptops, servers)", "outlay_cr": 17000, "kw": ["computers", "hardware", "electronic"],
     "why": "Localise laptop, tablet and server production."},
    {"scheme": "Automobiles and auto components", "outlay_cr": 25938, "kw": ["auto"],
     "why": "Encourage advanced-technology vehicles (EV, hydrogen) and local component makers."},
    {"scheme": "Advanced Chemistry Cell (ACC) battery", "outlay_cr": 18100, "kw": ["battery", "electrical equipment", "auto"],
     "why": "Create 50 GWh of domestic battery cell capacity for EVs and grid storage."},
    {"scheme": "High-efficiency solar PV modules", "outlay_cr": 24000, "kw": ["solar", "renewable", "electrical equipment"],
     "why": "Integrated solar manufacturing (polysilicon to modules) to cut Chinese imports."},
    {"scheme": "Pharmaceuticals", "outlay_cr": 15000, "kw": ["pharma", "healthcare"],
     "why": "Boost high-value drug and formulation manufacturing and exports."},
    {"scheme": "Bulk drugs / APIs / key starting materials", "outlay_cr": 6940, "kw": ["pharma", "chemical"],
     "why": "Reduce dependence on China for drug raw materials."},
    {"scheme": "Medical devices", "outlay_cr": 3420, "kw": ["medical", "healthcare", "hospital"],
     "why": "Localise diagnostics, implants and equipment manufacturing."},
    {"scheme": "Telecom and networking products", "outlay_cr": 12195, "kw": ["telecom", "networking"],
     "why": "Build domestic 5G, routers and network equipment champions."},
    {"scheme": "White goods (AC and LED)", "outlay_cr": 6238, "kw": ["consumer durable", "air condition", "led"],
     "why": "Deepen local component supply for ACs and LED lighting."},
    {"scheme": "Food processing", "outlay_cr": 10900, "kw": ["food", "agro", "beverage", "consumer food"],
     "why": "Create Indian food brands and boost processed-food exports."},
    {"scheme": "Textiles (man-made fibre and technical)", "outlay_cr": 10683, "kw": ["textile", "apparel"],
     "why": "Scale up MMF and technical textiles for export competitiveness."},
    {"scheme": "Specialty steel", "outlay_cr": 6322, "kw": ["steel", "metal"],
     "why": "Make high-grade steel locally instead of importing it."},
    {"scheme": "Drones and drone components", "outlay_cr": 120, "kw": ["aerospace", "defence", "drone"],
     "why": "Seed an Indian drone industry for civil and defence use."},
    {"scheme": "National Green Hydrogen Mission (incl. SIGHT)", "outlay_cr": 19744, "kw": ["hydrogen", "renewable", "electrical equipment"],
     "why": "Electrolyser manufacturing and green hydrogen output to cut fossil imports."},
]
PLI_QUERIES = ["PLI scheme beneficiaries approved companies crore", "PLI scheme incentive disbursed company crore",
               "PLI scheme approval company investment crore"]
BROKER_POS = ["buy", "upgrade", "outperform", "overweight", "accumulate", "initiates coverage", "target price raised", "raises target"]
BROKER_NEG = ["sell", "downgrade", "underperform", "underweight", "reduce", "cuts target", "target price cut"]

# ---- GOVERNMENT / POLICY TRACKING (edit freely) ----
# Google News searches per theme (last 30 days). Add or change phrases to follow what you care about.
POLICY_QUERIES = {
    "Precision / Aerospace / Defence": ["Defence Acquisition Council approves", "Ministry of Defence indigenisation order India",
                                        "aerospace manufacturing India scheme"],
    "Transformers / T&D / Power equipment": ["transmission grid investment India approved", "Ministry of Power scheme transformers",
                                             "Cabinet approves power transmission India"],
    "Specialty / Water chemicals": ["PLI specialty chemicals India", "Jal Jeevan Mission water treatment", "anti-dumping duty chemicals India"],
    "Semiconductor / Electronics": ["India Semiconductor Mission approval", "PLI electronics components scheme",
                                    "Cabinet approves electronics manufacturing India"],
    "Rail / Automation / Industrial": ["Railways tender Kavach order", "Cabinet approves railway projects", "industrial automation India scheme"],
}
POLICY_KW = {  # used to tag PIB / newsletter items to a theme
    "Precision / Aerospace / Defence": ["defence", "defense", "aerospace", "drdo", "indigenis", "navy", "air force", "dac "],
    "Transformers / T&D / Power equipment": ["transmission", "grid", "transformer", "power sector", "renewable", "ministry of power", "discom"],
    "Specialty / Water chemicals": ["chemical", "water", "jal jeevan", "anti-dumping", "fertili"],
    "Semiconductor / Electronics": ["semiconductor", "electronics", "chip", "pli", "fab "],
    "Rail / Automation / Industrial": ["railway", "rail ", "kavach", "vande bharat", "automation", "manufacturing"],
}
POLICY_POS = ["approve", "cabinet", "outlay", "scheme", "mission", "incentive", "pli", "tender", "order", "sanction",
              "allocat", "budget", "subsidy", "indigenis", "boost", "anti-dumping", "investment"]
POLICY_NEG = ["scrap", "withdraw", "cancel", "delay", "curb", "ban on", "duty cut", "slash", "halt", "probe"]
PIB_FEED = "https://pib.gov.in/RssMain.aspx?ModId=6&Lang=1&Regid=3"   # official govt press releases (skipped if it fails)
NEWSLETTER_FEEDS = [
    # Paste RSS feed links of newsletters/blogs you follow, e.g. "https://yourname.substack.com/feed"
]

# ----------------------------------------------------------------------------
# small helpers
# ----------------------------------------------------------------------------
# ============================================================================
# v4: ALL-STOCK UNIVERSE, AREAS, CUSTOMERS, BROKERS  (these override older settings above)
# ============================================================================
UNIVERSE_QUERY = "Market Capitalization > 5"   # Rs Cr. This pulls EVERY company listed on Screener. Your rules are applied in Python.
CANDIDATE_QUERY = UNIVERSE_QUERY
# Companies whose latest quarter is growing fast are loaded FIRST, so the best candidates appear on the dashboard early.
PRIORITY_QUERY = ("Market Capitalization > 5 AND Net profit latest quarter > Net profit preceding year quarter * 1.25 "
                  "AND Sales latest quarter > Sales preceding year quarter")
MAX_PAGES = 300
MAX_CANDIDATES = 6000
BUDGET_MIN = 330            # time budget per full run (minutes). Unfinished work simply resumes on the next run.
FUND_REFRESH_DAYS = 6       # non-shortlisted stocks have their financials refreshed this often
ENRICH_PER_RUN = 250        # concall transcripts / credit reports read per run
FEATURED_MAX = 700          # stocks embedded in the dashboard page; every other stock loads on tap
POLICY_EXTRA_MAX = 20
ONLY_THEMES = False

# Each AREA lists: tags (matched to Screener industry names / company name), text (matched in the business
# description and concalls), what drives it, what can go wrong, and policy news searches.
AREAS = {
    "Mining & minerals": {
        "tags": ["mining", "mineral", "coal"],
        "text": ["mining", "mineral exploration", "iron ore", "beneficiation", "rare earth", "lithium", "bauxite", "manganese ore", "limestone"],
        "drivers": "Infrastructure and steel demand, critical-mineral push, auctions of new mines, import substitution.",
        "risks": "Commodity price swings, royalty and regulatory changes, environmental clearances.",
        "queries": ["Ministry of Mines critical minerals auction India", "Cabinet approves critical mineral mission India"]},
    "Precision engineering & components": {
        "tags": ["precision", "forging", "castings", "bearing"],
        "text": ["precision engineering", "precision component", "precision machining", "forgings", "castings", "machined components", "cnc machining",
                 "close tolerance", "investment casting", "turned components", "machined parts", "critical components"],
        "drivers": "Global supply chains adding India as a source, long qualification cycles with OEMs (high entry barrier), aerospace, energy and defence demand.",
        "risks": "Concentrated customers, lumpy orders, currency swings, premium valuations.",
        "queries": ["precision engineering exports India aerospace supply chain", "India manufacturing scheme precision components"]},
    "Electronics & EMS": {
        "tags": ["electronic"],
        "text": ["electronics manufacturing services", "pcb", "printed circuit", "electronic components", "box build", "mobile phone", "smartphone",
                 "mobile components", "enclosures", "camera module", "display module", "wearables", "charger"],
        "drivers": "PLI and component schemes, phone and consumer electronics localisation, export growth.",
        "risks": "Thin margins in assembly, subsidy dependence, customer concentration, working-capital strain.",
        "queries": ["PLI electronics components scheme approval", "Cabinet approves electronics manufacturing India"]},
    "Semiconductors": {
        "tags": ["semiconductor"],
        "text": ["semiconductor", "osat", "chip design", "wafer", "fabless", "vlsi", "semiconductor equipment", "cleanroom",
                 "ultra high purity", "test and assembly", "vacuum components"],
        "drivers": "India Semiconductor Mission incentives, fabs and OSAT plants being set up, design-linked incentives.",
        "risks": "Long gestation, very high capital needs, technology and subsidy dependence, rich valuations.",
        "queries": ["India Semiconductor Mission approval", "semiconductor fab OSAT India Cabinet approves"]},
    "Nuclear": {
        "tags": [],
        "name": ["nuclear"],
        "text": ["nuclear", "atomic energy", "npcil", "small modular reactor", "heavy water", "reactor components", "pressure tubes",
                 "nuclear fuel", "fuel handling", "steam generator", "bhavini", "department of atomic energy"],
        "drivers": "Government push to expand nuclear capacity, opening of the sector to private firms, small modular reactor plans, heavy-equipment and component orders.",
        "risks": "Very long project cycles, liability and approval uncertainty, state-utility customer concentration.",
        "queries": ["nuclear power India Cabinet approves", "small modular reactor India NPCIL private sector"]},
    "Ammunition & explosives": {
        "tags": ["explosives", "ammunition"],
        "name": ["ammunition", "explosive", "munition"],
        "text": ["ammunition", "artillery shell", "gun shell", "shells", "fuze", "propellant", "explosives", "detonator", "warhead",
                 "small arms", "munitions"],
        "drivers": "Self-reliance in ammunition, replenishing stockpiles, rising exports; long licensing and safety approvals keep entry hard.",
        "risks": "Lumpy government orders, safety incidents, working capital, export licence delays.",
        "queries": ["Ministry of Defence ammunition order India", "artillery shell contract Indian company", "India ammunition exports"]},
    "Transmission, transformers & T&D": {
        "tags": ["transformer", "electrical equipment", "cable", "power equipment", "transmission", "switchgear"],
        "text": ["transformer", "switchgear", "transmission line", "power cable", "conductor", "substation", "hvdc", "insulator"],
        "drivers": "Grid expansion, renewable evacuation, data-centre and industrial power demand, long order books, limited certified capacity.",
        "risks": "Copper and CRGO steel costs, new capacity from many players, valuations pricing in perfection.",
        "queries": ["transmission grid investment India approved", "Ministry of Power scheme transformers", "Cabinet approves power transmission India"]},
    "Defence": {
        "tags": ["defence", "defense"],
        "text": ["defence", "defense", "ammunition", "naval", "drdo", "armoured", "military"],
        "drivers": "Indigenisation lists, rising defence budgets, export push, long qualification cycles.",
        "risks": "Lumpy orders, government payment cycles, premium valuations.",
        "queries": ["Defence Acquisition Council approves", "Ministry of Defence indigenisation order India"]},
    "Aerospace": {
        "tags": ["aerospace"],
        "text": ["aerospace", "aero-engine", "aircraft component", "airframe", "turbine blade"],
        "drivers": "Global aircraft makers diversifying supply chains, engine-part outsourcing to India, strong order backlogs at Airbus and Boeing.",
        "risks": "Long certification cycles, customer concentration, cyclicality of aviation.",
        "queries": ["aerospace manufacturing India scheme", "Airbus Boeing Safran India supply chain order"]},
    "Space": {
        "tags": [],
        "text": ["isro", "launch vehicle", "space segment", "spacetech", "satellite component", "satellite manufactur"],
        "drivers": "Opening of the space sector to private firms, ISRO launch cadence, satellite constellations and defence space needs.",
        "risks": "Small order sizes, execution delays, dependence on ISRO and government budgets.",
        "queries": ["India space sector policy private satellite ISRO", "IN-SPACe approval private launch"]},
    "Data centers & cooling": {
        "tags": [],
        "text": ["data center", "data centre", "hyperscale", "liquid cooling", "precision cooling", "colocation"],
        "drivers": "Cloud and AI demand, data-localisation, hyperscaler build-outs in India; cooling, power and electrical suppliers benefit.",
        "risks": "Lumpy orders, a few global customers, fast technology change.",
        "queries": ["India data centre investment policy", "data center cooling power equipment India order"]},
    "Railways": {
        "tags": ["railway", "rail"],
        "text": ["indian railways", "railway wagons", "locomotive", "kavach", "metro rail", "rolling stock"],
        "drivers": "Rail capex, Kavach safety rollout, Vande Bharat and metro orders, freight corridors.",
        "risks": "Government order timing, working-capital stretch, tender competition.",
        "queries": ["Railways tender Kavach order", "Cabinet approves railway projects"]},
    "Specialty chemicals": {
        "tags": ["specialty chem", "chemical", "agrochem", "fluoro"],
        "text": ["specialty chemical", "fluorochemical", "agrochemical intermediates", "custom synthesis"],
        "drivers": "China+1 shift, regulatory approvals and sticky customers, import substitution.",
        "risks": "Chinese dumping, pricing cycles, destocking, environmental compliance.",
        "queries": ["PLI specialty chemicals India", "anti-dumping duty chemicals India"]},
    "Water & environment": {
        "tags": ["water"],
        "name": ["water"],
        "text": ["water treatment", "wastewater", "desalination", "water purification", "effluent treatment"],
        "drivers": "Jal Jeevan Mission, industrial water reuse rules, urban water and sewage projects.",
        "risks": "Government payment delays, order timing, intense tender competition.",
        "queries": ["Jal Jeevan Mission water treatment tender", "wastewater recycling policy India"]},
    "Solar & renewables": {
        "tags": ["solar", "renewable", "wind energy", "wind turbine"],
        "text": ["solar module", "solar cell", "wind turbine", "inverter", "green hydrogen", "electrolyser"],
        "drivers": "Renewable capacity targets, solar PLI, green hydrogen mission, domestic-content rules.",
        "risks": "Module price cycles, Chinese competition, policy and tariff changes.",
        "queries": ["solar PLI scheme India modules", "green hydrogen mission India electrolyser"]},
    "EV & batteries": {
        "tags": ["battery"],
        "text": ["electric vehicle", "lithium-ion", "battery pack", "ev charging", "cell manufacturing"],
        "drivers": "EV adoption incentives, ACC battery PLI, charging build-out, grid storage.",
        "risks": "Technology change, subsidy dependence, raw-material price swings.",
        "queries": ["ACC battery PLI India", "electric vehicle policy India subsidy"]},
    "Industrial automation & capital goods": {
        "tags": ["industrial machinery", "automation", "compressors"],
        "text": ["industrial automation", "robotics", "motion control", "plc "],
        "drivers": "Manufacturing capex cycle, factory automation, import substitution.",
        "risks": "Cyclical orders, working-capital strain, competition from imports.",
        "queries": ["industrial automation India scheme", "capital goods order inflow India capex"]},
    "Oil, gas & process equipment": {
        "tags": ["oilfield", "oil equipment", "oil & gas equipment"],
        "text": ["oil and gas equipment", "heat exchanger", "pressure vessel", "process equipment", "cryogenic"],
        "drivers": "Refinery and petrochemical expansion, LNG and gas-grid build-out, energy-security spending.",
        "risks": "Capex cycles, oil-price swings, government customer concentration.",
        "queries": ["refinery petrochemical expansion India approves", "city gas LNG infrastructure India investment"]},
    "Shipbuilding & marine": {
        "tags": ["shipbuilding"],
        "text": ["shipbuilding", "shipyard", "naval vessels", "offshore vessel"],
        "drivers": "Shipbuilding financial assistance, naval orders, coastal and port projects.",
        "risks": "Long delivery cycles, working capital, dependence on government orders.",
        "queries": ["India shipbuilding policy financial assistance", "Cabinet approves shipbuilding"]},
}
THEMES = {a: d["tags"] for a, d in AREAS.items()}
THEME_INFO = {a: {"drivers": d["drivers"], "risks": d["risks"]} for a, d in AREAS.items()}
POLICY_QUERIES = {a: d["queries"] for a, d in AREAS.items()}
POLICY_KW = {a: d["text"][:5] + d["tags"][:3] for a, d in AREAS.items()}

_CUST = {
    "Global": ["Safran", "Boeing", "Airbus", "GE Aerospace", "GE Vernova", "General Electric", "Rolls-Royce", "Pratt & Whitney",
               "Honeywell", "Collins Aerospace", "RTX", "Raytheon", "Lockheed Martin", "Northrop Grumman", "Thales", "Dassault",
               "Embraer", "Bombardier", "Spirit AeroSystems", "Leonardo", "BAE Systems", "Rafael", "Elbit", "Israel Aerospace",
               "Textron", "Bloom Energy", "Siemens Energy", "Siemens", "ABB", "Hitachi Energy", "Schneider Electric", "Eaton",
               "Mitsubishi", "Toshiba", "Westinghouse", "Vestas", "Tesla", "Cummins", "Caterpillar", "Baker Hughes",
               "Schlumberger", "Halliburton", "Vertiv", "Nvidia", "Apple", "Samsung", "Foxconn", "Dell", "Cisco", "Microsoft",
               "Amazon", "AWS", "Google", "Intel", "Micron", "TSMC", "Qualcomm", "Texas Instruments", "Infineon", "Alstom",
               "Wabtec", "Bosch", "Continental", "Hyundai", "Toyota", "Volkswagen", "Ford", "General Motors", "BYD",
               "Rio Tinto", "BHP", "SpaceX", "Kongsberg", "Rheinmetall", "Saab", "Hanwha", "Sandvik", "Atlas Copco",
               "Parker Hannifin", "Emerson", "Rockwell", "Johnson Controls", "Daikin", "Trane", "Legrand", "Hitachi",
               "Panasonic", "LG", "Xiaomi", "Danfoss", "Grundfos", "Xylem", "Pentair"],
    "India": ["NPCIL", "NTPC", "BHEL", "Larsen & Toubro", "L&T", "Tata Power", "Adani", "Power Grid", "PGCIL", "Reliance Industries",
              "ONGC", "Coal India", "NMDC", "Vedanta", "Hindalco", "Tata Steel", "JSW", "SAIL", "DRDO", "ISRO", "NSIL", "HAL",
              "Hindustan Aeronautics", "BEL", "Bharat Electronics", "BDL", "Bharat Dynamics", "Mazagon Dock", "Cochin Shipyard",
              "Indian Railways", "Indian Army", "Indian Navy", "Indian Air Force", "Tata Advanced Systems", "Tata Motors",
              "Mahindra", "Maruti", "Tata Electronics", "Bharat Forge", "Hindustan Copper", "GAIL", "IOCL", "Indian Oil", "BPCL",
              "HPCL", "Thermax", "Titagarh", "Jio", "Airtel", "BSNL", "Ministry of Defence", "Defence Ministry"],
}
_CUST["Global"] += ["ASML", "Applied Materials", "Lam Research", "KLA", "Tokyo Electron", "Analog Devices", "NXP", "Renesas", "Amkor",
                    "Pegatron", "Wistron", "Flex", "Jabil", "Oppo", "Vivo", "Motorola", "General Dynamics", "Nammo", "Nexter", "KNDS",
                    "Rosatom", "Holtec", "NuScale", "Framatome", "EDF", "AtkinsRealis", "GKN", "Magellan Aerospace", "Triumph Group",
                    "Howmet", "Precision Castparts", "Doosan", "Bechtel", "Fluor"]
_CUST["India"] += ["Munitions India", "Armoured Vehicles Nigam", "AVNL", "Gun and Shell Factory", "Yantra India", "Troop Comforts",
                   "Advanced Weapons and Equipment India", "BHAVINI", "Department of Atomic Energy", "DAE", "Nuclear Power Corporation",
                   "Solar Industries", "Data Patterns", "Dixon", "GRSE", "Garden Reach", "BEML", "MIDHANI", "Mishra Dhatu", "Hindustan Shipyard"]
CUSTOMERS = {n: reg for reg, names in _CUST.items() for n in names}
CUST_RE = re.compile(r"(?<![A-Za-z])(" + "|".join(re.escape(n) for n in sorted(CUSTOMERS, key=len, reverse=True)) + r")(?![A-Za-z])")
CUST_TRIG = re.compile(r"order|contract|supply|supplier|partner|agreement|mou|customer|client|qualif|vendor|approved|awarded|won |win |tie[- ]up|collaborat|joint venture|licen|share of wallet", re.I)
FOCUS_RE = re.compile(r"focus(?:ing|ed)? on|we are targeting|targeting|entering|enter the|new vertical|new segment|diversif|new customers?|new product|new market|adding capacity", re.I)

BROKERS = ["Kotak Institutional Equities", "Kotak", "ICICI Securities", "ICICI Direct", "Motilal Oswal", "Axis Securities", "Axis Capital",
           "Nuvama", "JM Financial", "HDFC Securities", "Jefferies", "Nomura", "Goldman Sachs", "Morgan Stanley", "CLSA", "Citi",
           "UBS", "Macquarie", "Emkay", "Anand Rathi", "Sharekhan", "Prabhudas Lilladher", "Systematix", "Antique", "Choice Equity",
           "Geojit", "SBI Securities", "Ambit", "Elara", "IIFL", "Investec", "Bernstein", "Barclays", "HSBC", "BNP Paribas",
           "Dolat", "Centrum", "Religare"]
BROKER_RE = re.compile(r"(?<![A-Za-z])(" + "|".join(re.escape(b) for b in sorted(BROKERS, key=len, reverse=True)) + r")(?![A-Za-z])")
TARGET_RE = re.compile(r"target(?: price)?(?: of| at)?\s*(?:Rs\.?|INR|\u20b9)?\s*([\d,]+)", re.I)

def num(x):
    try:
        return float(re.sub(r"[,%\u20b9\s]", "", x))
    except Exception:
        return None

def mean(v):
    v = [x for x in v if x is not None]
    return sum(v) / len(v) if v else None

def med(v):
    v = [x for x in v if x is not None]
    return st.median(v) if v else None

def pct_true(v):
    return 100.0 * sum(1 for x in v if x) / len(v) if v else 0.0

def now_ist():
    return datetime.now(IST)

def get(url, **kw):
    for i in range(3):
        try:
            r = requests.get(url, headers=UA, timeout=25, **kw)
            if r.status_code == 429:
                time.sleep(3 * (i + 1)); continue
            return r
        except requests.RequestException:
            time.sleep(2)
    return None

# ----------------------------------------------------------------------------
# Screener.in
# ----------------------------------------------------------------------------
S = requests.Session()
S.headers.update(UA)

def login():
    r = S.get(f"{BASE}/login/")
    tok = BeautifulSoup(r.text, "html.parser").find("input", {"name": "csrfmiddlewaretoken"})["value"]
    r = S.post(f"{BASE}/login/", data={
        "csrfmiddlewaretoken": tok,
        "username": os.environ["SCREENER_USER"],
        "password": os.environ["SCREENER_PASS"]}, headers={"Referer": f"{BASE}/login/"})
    if "/login" in r.url:
        sys.exit("Screener login failed - check SCREENER_USER / SCREENER_PASS secrets.")

def _total_results(text):
    """Screener says how many companies match, e.g. '5,382 results found'. Returns None if the wording is not found."""
    for pat in (r"([\d,]+)\s+results?\s+found", r"of\s+([\d,]+)\s+results?", r"([\d,]+)\s+companies\s+match"):
        m = re.search(pat, text, re.I)
        if m:
            try:
                return int(m.group(1).replace(",", ""))
            except ValueError:
                pass
    return None

def screen_rows(query, max_pages=None):
    """All companies for one Screener query. Stops when a page brings nothing new (does not rely on a 'Next' link)."""
    rows, seen, total, page = [], set(), None, 1
    while page <= (max_pages or MAX_PAGES):
        try:
            r = S.get(f"{BASE}/screen/raw/", params={"query": query, "page": page}, timeout=40)
        except requests.RequestException:
            time.sleep(5)
            break
        soup = BeautifulSoup(r.text, "html.parser")
        if page == 1:
            total = _total_results(soup.get_text(" "))
        table = soup.select_one("table.data-table")
        if not table:
            break
        new = 0
        for tr in table.select("tr[data-row-company-id]"):
            a = tr.find("a", href=re.compile(r"^/company/"))
            if a and a["href"] not in seen:
                seen.add(a["href"])
                rows.append({"name": a.get_text(strip=True), "url": BASE + a["href"]})
                new += 1
        if new == 0 or len(rows) >= MAX_CANDIDATES:
            break
        page += 1
        time.sleep(0.8)
    return rows, total

def split_screen(lo=5.0, hi=1_000_000.0):
    """Screener shows only a limited number of rows per query, so list the market in market-cap bands
    and split any band that is still cut short, until every band is complete."""
    out, seen, t0 = [], set(), time.time()
    def band(a, b, depth=0):
        rows, total = screen_rows(f"Market Capitalization > {a:.4f} AND Market Capitalization < {b:.4f}", 40)
        for r_ in rows:
            if r_["url"] not in seen:
                seen.add(r_["url"])
                out.append(r_)
        complete = (total is not None and len(rows) >= total * 0.99) or (total is None and len(rows) < 25)
        if not complete and b / a > 1.02 and depth < 16 and time.time() - t0 < 40 * 60:
            mid = (a * b) ** 0.5
            band(a, mid, depth + 1)
            band(mid, b, depth + 1)
    band(lo, hi)
    return out

def run_screen():
    rows, total = screen_rows(CANDIDATE_QUERY)
    print(f"Screener reports {total} matching companies; the single query returned {len(rows)}")
    if len(rows) >= 300 or (total and len(rows) >= total * 0.97):
        return rows
    print("One query is cut short by Screener - listing the whole market in market-cap bands instead")
    rows = split_screen()
    print(f"Band listing found {len(rows)} companies")
    return rows

def series(soup, section, labels):
    sec = soup.find("section", id=section)
    if not sec:
        return [], ""
    head = sec.select("thead th")
    period = head[-1].get_text(strip=True) if head else ""
    for tr in sec.select("tbody tr"):
        td = tr.find("td")
        if td and any(td.get_text(strip=True).lower().startswith(l.lower()) for l in labels):
            return [num(x.get_text()) for x in tr.find_all("td")[1:]], period
    return [], period

def is_ath(v):
    c = [x for x in v if x is not None]
    return len(c) >= 4 and v[-1] is not None and v[-1] > 0 and v[-1] >= max(c)

def not_rising(v):
    c = [x for x in v if x is not None]
    if len(c) < 2:
        return None
    ok = c[-1] <= c[-2] * 1.03 + 0.5
    if len(c) >= 4:
        ok = ok and c[-1] <= mean(c[-4:-1]) * 1.05 + 0.5
    return ok

def yoy(v):
    if len(v) >= 5 and v[-1] is not None and v[-5] not in (None, 0) and v[-5] > 0:
        return (v[-1] / v[-5] - 1) * 100
    return None

def theme_of(tags, name):
    hay = f"{tags} {name}".lower()
    for theme, kws in THEMES.items():
        if any(k in hay for k in kws):
            return theme
    return ""

def grab_table(soup, section, table_id=None):
    """Return (column headers, {normalised row label: values}) for a Screener table."""
    sec = soup.find("section", id=section)
    if not sec:
        return [], {}
    scope = sec.find(id=table_id) if table_id else None
    scope = scope if scope is not None else sec
    tbl = scope if scope.name == "table" else scope.find("table")
    if tbl is None:
        return [], {}
    hd = [th.get_text(strip=True) for th in tbl.select("thead th")][1:]
    rows = {}
    for tr in tbl.select("tbody tr"):
        tds = tr.find_all("td")
        if len(tds) < 2:
            continue
        label = re.sub(r"[\s+]+$", "", tds[0].get_text().replace("\u00a0", " ").strip()).lower()
        rows.setdefault(label, [num(td.get_text()) for td in tds[1:]])
    return hd, rows

def results_view(hd, rows):
    """Is the latest quarter excellent or not? Compared YoY and QoQ."""
    qs = rows.get("sales") or rows.get("revenue") or []
    qp = rows.get("net profit") or []
    om = rows.get("opm %") or []
    n = len(qs)
    if n < 2 or len(qp) < 2 or qs[-1] is None:
        return None
    def g(a, b):
        return (a / b - 1) * 100 if a is not None and b is not None and b > 0 else None
    r = {"period": hd[-1] if hd else "", "sales": qs[-1], "profit": qp[-1],
         "sales_yoy": g(qs[-1], qs[-5]) if n >= 5 else None, "sales_qoq": g(qs[-1], qs[-2]),
         "profit_yoy": g(qp[-1], qp[-5]) if len(qp) >= 5 else None, "profit_qoq": g(qp[-1], qp[-2]),
         "opm": om[-1] if om else None, "opm_yoy": om[-5] if len(om) >= 5 else None}
    pts = 0
    sy, py, sq, pq = r["sales_yoy"], r["profit_yoy"], r["sales_qoq"], r["profit_qoq"]
    if sy is not None:
        pts += 2 if sy >= 20 else 1 if sy >= 10 else -2 if sy < 0 else 0
    if py is not None:
        pts += 2 if py >= 25 else 1 if py >= 10 else -2 if py < 0 else 0
    if sq is not None:
        pts += 1 if sq > 0 else -1
    if pq is not None:
        pts += 1 if pq > 0 else -1
    if r["opm"] is not None and r["opm_yoy"] is not None:
        pts += 1 if r["opm"] > r["opm_yoy"] else -1
    if qp[-1] is not None and qp[-1] < 0:
        verdict = "Loss-making"
    else:
        verdict = "Excellent" if pts >= 5 else "Good" if pts >= 3 else "Mixed" if pts >= 1 else "Weak"
    trend = [g(qp[i], qp[i - 4]) for i in range(max(4, len(qp) - 4), len(qp))]
    tt = [x for x in trend if x is not None]
    r.update({"verdict": verdict, "pts": pts, "yoy_trend": [round(x) for x in tt],
              "accelerating": len(tt) >= 3 and tt[-1] > tt[-2] > tt[-3],
              "hist": [{"q": hd[i] if i < len(hd) else "", "s": qs[i], "p": qp[i] if i < len(qp) else None}
                       for i in range(max(0, n - 6), n)]})
    return r

def holding_view(hd, rows):
    """Who owns the company, and are institutions coming in or leaving?"""
    keys = ["promoters", "fiis", "diis", "government", "public"]
    ser = {k: rows.get(k) or [] for k in keys}
    if not ser["promoters"] and not ser["fiis"]:
        return None
    holders = rows.get("no. of shareholders") or []
    def chg(v, k):
        return v[-1] - v[-1 - k] if len(v) > k and v[-1] is not None and v[-1 - k] is not None else None
    ch = {k: {"now": ser[k][-1] if ser[k] else None, "q": chg(ser[k], 1), "y": chg(ser[k], 4)} for k in keys}
    sig = []
    fy, dy, py = ch["fiis"]["y"], ch["diis"]["y"], ch["promoters"]["y"]
    if fy is not None and fy >= 1:
        sig.append({"t": f"FIIs (foreign funds) raised holding by {fy:.1f} pts in a year", "tone": "g"})
    elif fy is not None and fy <= -1:
        sig.append({"t": f"FIIs (foreign funds) cut holding by {abs(fy):.1f} pts in a year", "tone": "r"})
    if dy is not None and dy >= 1:
        sig.append({"t": f"Domestic institutions (mutual funds, insurers) raised holding by {dy:.1f} pts in a year", "tone": "g"})
    elif dy is not None and dy <= -1:
        sig.append({"t": f"Domestic institutions (mutual funds, insurers) cut holding by {abs(dy):.1f} pts in a year", "tone": "r"})
    for k, lab in (("fiis", "FII"), ("diis", "mutual fund / DII")):
        v = ser[k]
        if len(v) >= 5 and v[-5] is not None and v[-1] is not None and v[-5] < 1 and v[-1] >= 2:
            sig.append({"t": f"New {lab} entry: {v[-5]:.1f}% to {v[-1]:.1f}% in a year", "tone": "g"})
    if py is not None and py <= -2:
        sig.append({"t": f"Promoter holding fell {abs(py):.1f} pts in a year", "tone": "r"})
    elif py is not None and py >= 1:
        sig.append({"t": f"Promoters raised their stake by {py:.1f} pts in a year", "tone": "g"})
    if len(holders) >= 5 and holders[-1] and holders[-5] and holders[-5] > 0:
        up = (holders[-1] / holders[-5] - 1) * 100
        if up >= 25:
            sig.append({"t": f"Shareholder count up {up:.0f}% in a year - retail crowding in", "tone": "a"})
    inst = (fy or 0) + (dy or 0)
    state = "Accumulating" if inst >= 1.5 else "Reducing" if inst <= -1.5 else "Stable"
    return {"labels": hd[-8:], "rows": {k: v[-8:] for k, v in ser.items() if v}, "holders": holders[-8:],
            "ch": ch, "signals": sig, "inst": state}

def insider_news(name):
    """Promoter / director / insider share purchases or sales (news about SEBI insider-trading disclosures)."""
    nm = clean_name(name)
    first = nm.split()[0].lower() if nm.split() else ""
    r = get("https://news.google.com/rss/search", params={
        "q": f'"{nm}" promoter OR director OR insider OR chairman "buys shares" OR "open market" OR "increases stake" OR '
             f'"raises stake" OR "acquires shares" OR "sells shares" OR offloads OR "pares stake" when:180d',
        "hl": "en-IN", "gl": "IN", "ceid": "IN:en"})
    out = []
    if r is None:
        return out
    buy = ("buys", "bought", "acquires", "picks up", "increases stake", "raises stake", "hikes stake", "open market", "adds stake", "purchase")
    sell = ("sells", "sold", "offloads", "pares stake", "reduces stake", "cuts stake", "stake sale", "dilutes")
    who = ("promoter", "director", "insider", "chairman", "managing director", "ceo", "founder")
    for it in feed_items(r.content, 10):
        low = it["title"].lower()
        if (len(first) >= 3 and first not in low) or not any(w in low for w in who):
            continue
        b, s_ = any(w in low for w in buy), any(w in low for w in sell)
        if b and not s_:
            it["kind"] = "Insider buying"
        elif s_ and not b:
            it["kind"] = "Insider selling"
        else:
            continue
        out.append(it)
    out.sort(key=lambda i: i["age_h"])
    return out[:6]

def investor_news(name):
    """Bulk/block deals, fund and FII stake news, preferential issues, QIPs, warrants (Google News)."""
    nm = clean_name(name)
    first = nm.split()[0].lower() if nm.split() else ""
    out, seen = [], set()
    queries = [(f'"{nm}" bulk deal OR block deal OR mutual fund OR FII OR stake', "90d"),
               (f'"{nm}" preferential issue OR preferential allotment OR warrants OR QIP OR rights issue OR fund raise', "180d")]
    for q, win in queries:
        r = get("https://news.google.com/rss/search", params={"q": f"{q} when:{win}", "hl": "en-IN", "gl": "IN", "ceid": "IN:en"})
        if r is None:
            continue
        for it in feed_items(r.content, 8):
            low, key = it["title"].lower(), it["title"].lower()[:70]
            if key in seen or (len(first) >= 3 and first not in low):
                continue
            if any(k in low for k in ("preferential", "warrant", "qip", "rights issue", "fund raise", "fundraise", "raises rs")):
                it["kind"] = "Preferential / fund raise"
            elif any(k in low for k in ("bulk deal", "block deal", "stake", "mutual fund", "fii", "fpi", "picks up", "acquires", "invests", "buys")):
                it["kind"] = "Big investor"
            else:
                continue
            seen.add(key); out.append(it)
        time.sleep(0.4)
    out.sort(key=lambda i: i["age_h"])
    return out[:8]

def margin_view(rows):
    """Cost quality: costs (COGS proxy) should fall as a share of sales, margin should expand, operating profit should grow."""
    qs = rows.get("sales") or rows.get("revenue") or []
    ex = rows.get("expenses") or []
    op = rows.get("operating profit") or []
    om = rows.get("opm %") or []
    if len(qs) < 5 or len(ex) < 5 or not qs[-1]:
        return None
    def cr(i):
        return ex[i] / qs[i] * 100 if qs[i] and ex[i] is not None and qs[i] > 0 else None
    def g(a, b):
        return (a / b - 1) * 100 if a is not None and b is not None and b > 0 else None
    c_now, c_yr, c_q = cr(-1), cr(-5), cr(-2)
    o_now = om[-1] if om else None
    o_yr = om[-5] if len(om) >= 5 else None
    o_q = om[-2] if len(om) >= 2 else None
    op_yoy = g(op[-1], op[-5]) if len(op) >= 5 else None
    op_qoq = g(op[-1], op[-2]) if len(op) >= 2 else None
    sy = g(qs[-1], qs[-5])
    cost_fall = c_now is not None and c_yr is not None and c_now < c_yr - 0.2
    opm_up = o_now is not None and o_yr is not None and o_now > o_yr + 0.2
    opm_up_q = o_now is not None and o_q is not None and o_now >= o_q
    op_grow = op_yoy is not None and op_yoy >= 10
    op_lev = op_yoy is not None and sy is not None and op_yoy >= sy
    op_rec = bool(op) and is_ath(op)
    pts = sum([cost_fall, opm_up, op_grow, op_lev, opm_up_q, op_rec])
    weak = (o_now is not None and o_yr is not None and o_now < o_yr - 0.5) or (op_yoy is not None and op_yoy < 0)
    verdict = "Excellent" if (cost_fall and opm_up and op_grow) else "Good" if ((opm_up and op_grow) or pts >= 4) else "Weak" if weak else "Mixed"
    return {"verdict": verdict, "cost_now": c_now, "cost_yr": c_yr, "cost_q": c_q, "opm": o_now, "opm_yr": o_yr, "opm_q": o_q,
            "op_yoy": op_yoy, "op_qoq": op_qoq, "op_record": op_rec, "cost_fall": cost_fall, "opm_up": opm_up, "pts": pts}

def fetch_cogs(html, url):
    """Material cost % (true COGS) from Screener's schedule data. Best effort: returns None if unavailable."""
    try:
        info = BeautifulSoup(html, "html.parser").find(id="company-info")
        wid = (info.get("data-warehouse-id") or info.get("data-company-id")) if info else None
        if not wid:
            return None
        params = {"parent": "Expenses", "section": "quarters"}
        if "/consolidated/" in url:
            params["consolidated"] = ""
        r = S.get(f"{BASE}/api/company/{wid}/schedules/", params=params, timeout=20)
        if r.status_code != 200:
            return None
        for k, v in r.json().items():
            if k.lower().startswith("material cost") and isinstance(v, dict):
                vals = [num(str(x)) for x in v.values()]
                if len(vals) >= 5 and vals[-1] is not None and vals[-5] is not None:
                    return {"now": vals[-1], "yr": vals[-5], "q": vals[-2]}
    except Exception:
        pass
    return None

def parse_company(html, row):
    soup = BeautifulSoup(html, "html.parser")
    ratios = {}
    for li in soup.select("#top-ratios li"):
        n = li.select_one(".name")
        vs = [num(v.get_text()) for v in li.select(".number")]
        if n and vs:
            ratios[n.get_text(strip=True)] = vs
    tag_list = [a.get_text(strip=True) for a in soup.select("#peers a[href^='/market/']")]
    tags = " | ".join(tag_list)
    sector = tag_list[0] if tag_list else "Other"
    qs, period = series(soup, "quarters", ["Sales", "Revenue"])
    qp, _ = series(soup, "quarters", ["Net Profit"])
    ys, _ = series(soup, "profit-loss", ["Sales", "Revenue"])
    yp, _ = series(soup, "profit-loss", ["Net Profit"])
    opm, _ = series(soup, "quarters", ["OPM"])
    pyoy, syoy = yoy(qp), yoy(qs)
    prior4 = [x for x in qp[-5:-1] if x is not None]
    breakout = bool(pyoy is not None and pyoy >= BREAKOUT_PROFIT_YOY and qp[-1] is not None
                    and prior4 and qp[-1] > max(prior4))
    f = {
        "period": period,
        "q_sales": qs[-1] if qs else None, "q_profit": qp[-1] if qp else None,
        "sales_yoy": syoy, "profit_yoy": pyoy,
        "opm_now": opm[-1] if opm else None, "opm_yr": opm[-5] if len(opm) >= 5 else None,
        "roce": (ratios.get("ROCE") or [None])[0], "pe": (ratios.get("Stock P/E") or [None])[0],
        "mcap": (ratios.get("Market Cap") or [None])[0],
        "ath_q_sales": is_ath(qs), "ath_q_profit": is_ath(qp),
        "ath_y_sales": is_ath(ys), "ath_y_profit": is_ath(yp),
        "profit_breakout": breakout, "y_sales": ys[-1] if ys else None,
    }
    dd, _ = series(soup, "ratios", ["Debtor Days"])
    iv, _ = series(soup, "ratios", ["Inventory Days"])
    oks = [x for x in (not_rising(dd), not_rising(iv)) if x is not None]
    f.update({"debtor_days": dd[-1] if dd else None, "debtor_prev": dd[-2] if len(dd) > 1 else None,
              "inv_days": iv[-1] if iv else None, "inv_prev": iv[-2] if len(iv) > 1 else None,
              "wc_ok": (all(oks) if oks else None)})
    def cagr_(v, n):
        if len(v) > n and v[-1] is not None and v[-1 - n] is not None and v[-1 - n] > 0 and v[-1] > 0:
            return ((v[-1] / v[-1 - n]) ** (1.0 / n) - 1) * 100
        return None
    f["cagr"] = {"sales3": cagr_(ys, 3), "sales5": cagr_(ys, 5), "profit3": cagr_(yp, 3), "profit5": cagr_(yp, 5)}
    qh, qrows = grab_table(soup, "quarters")
    f["results"] = results_view(qh, qrows)
    f["margin"] = margin_view(qrows)
    f["pledged"] = (ratios.get("Pledged percentage") or [None])[0]
    sh, srows = grab_table(soup, "shareholding", "quarterly-shp")
    holding = holding_view(sh, srows)
    docs = {"transcript": "", "ppt": "", "ratings": [], "filings": []}
    dsec = soup.find("section", id="documents")
    if dsec:
        for a in dsec.find_all("a", href=True):
            href = a["href"]
            href = BASE + href if href.startswith("/") else href
            if not href.startswith("https://"):
                continue
            txt, low = a.get_text(" ", strip=True), a.get_text(" ", strip=True).lower()
            if low == "transcript" and not docs["transcript"]:
                docs["transcript"] = href
            elif low == "ppt" and not docs["ppt"]:
                docs["ppt"] = href
            elif "rating" in low and len(docs["ratings"]) < 2:
                docs["ratings"].append({"text": txt, "href": href})
            elif any(k in low for k in FILING_KW) and len(docs["filings"]) < 8:
                docs["filings"].append({"text": txt[:140], "href": href})
    m = re.search(r"/company/([^/]+)/", row["url"])
    sym = m.group(1) if m else row["name"]
    h1 = soup.find("h1")
    nm = h1.get_text(strip=True) if ((row.get("watch") or row.get("guess")) and h1) else row["name"]
    ab = soup.select_one(".about") or soup.select_one(".company-profile")
    about = ab.get_text(" ", strip=True)[:1500] if ab else ""
    areas = areas_of(tags, nm, about)
    return {"sym": sym, "name": nm, "url": row["url"], "tags": tags, "sector": sector, "about": about, "areas": areas,
            "theme": areas[0] if areas else sector, "priority": bool(areas), "docs": docs, "f": f, "m": None, "news": [],
            "holding": holding, "watch": bool(row.get("watch"))}

# ----------------------------------------------------------------------------
# Yahoo Finance: price / volume
# ----------------------------------------------------------------------------
def fetch_chart(ysym, rng="1y"):
    r = get(f"https://query1.finance.yahoo.com/v8/finance/chart/{requests.utils.quote(ysym)}",
            params={"range": rng, "interval": "1d"})
    try:
        res = r.json()["chart"]["result"][0]
        q = res["indicators"]["quote"][0]
        rows = [(c, h, lo, v or 0) for c, h, lo, v in zip(q["close"], q["high"], q["low"], q["volume"])
                if c is not None and h is not None and lo is not None]
        return {"close": [x[0] for x in rows], "high": [x[1] for x in rows], "low": [x[2] for x in rows], "vol": [x[3] for x in rows]}
    except Exception:
        return None

def adx_calc(h, lo, c, n=14):
    """Wilder's Average Directional Index. Above 30 = very strong trend. Returns (ADX, +DI, -DI)."""
    if len(c) < 2 * n + 5:
        return None, None, None
    tr, pdm, mdm = [], [], []
    for i in range(1, len(c)):
        up, dn = h[i] - h[i - 1], lo[i - 1] - lo[i]
        pdm.append(up if up > dn and up > 0 else 0.0)
        mdm.append(dn if dn > up and dn > 0 else 0.0)
        tr.append(max(h[i] - lo[i], abs(h[i] - c[i - 1]), abs(lo[i] - c[i - 1])))
    def sm(x):
        s_ = sum(x[:n]); out = [s_]
        for v_ in x[n:]:
            s_ = s_ - s_ / n + v_
            out.append(s_)
        return out
    a_s, p_s, m_s = sm(tr), sm(pdm), sm(mdm)
    dx, pdi, mdi = [], None, None
    for a_, p_, m_ in zip(a_s, p_s, m_s):
        if a_ == 0:
            dx.append(0.0); continue
        pdi, mdi = 100 * p_ / a_, 100 * m_ / a_
        dx.append(100 * abs(pdi - mdi) / (pdi + mdi) if pdi + mdi else 0.0)
    if len(dx) < n:
        return None, None, None
    adx = sum(dx[:n]) / n
    for x_ in dx[n:]:
        adx = (adx * (n - 1) + x_) / n
    return round(adx, 1), round(pdi, 1), round(mdi, 1)

def atr_calc(h, lo, c, n=14):
    tr = [max(h[i] - lo[i], abs(h[i] - c[i - 1]), abs(lo[i] - c[i - 1])) for i in range(1, len(c))]
    return mean(tr[-n:]) if len(tr) >= n else None

_NIFTY = {}
def nifty_returns():
    """Nifty 50 returns, used to judge relative strength. Fetched once per run."""
    if not _NIFTY:
        d = fetch_chart("^NSEI", "2y")
        if d and len(d["close"]) > 130:
            c = d["close"]
            _NIFTY.update(r3=(c[-1] / c[-64] - 1) * 100, r6=(c[-1] / c[-127] - 1) * 100)
        else:
            _NIFTY["none"] = True
    return _NIFTY

def market_metrics(sym):
    d = None
    for suf in (".NS", ".BO"):
        d = fetch_chart(sym + suf, "2y")
        if d and len(d["close"]) >= 60:
            break
    else:
        return None
    c, h, v, lo_ = d["close"], d["high"], d["vol"], d["low"]
    price, prev = c[-1], c[-2]
    avg20 = mean(v[-21:-1])

    def sma(n, back=0):
        end = len(c) - back
        return mean(c[end - n:end]) if end - n >= 0 else None
    gap_now = state = cross_days = None
    s50, s200 = sma(50), sma(200)
    if s50 and s200:
        gap_now = (s50 / s200 - 1) * 100
        cur = s50 >= s200
        for back in range(1, 25):  # look back ~5 weeks for a crossover
            a, b = sma(50, back), sma(200, back)
            if a is None or b is None:
                break
            if (a >= b) != cur:
                cross_days = back
                break
        slope = s50 - (sma(50, 5) or s50)
        if cross_days is not None and cur:
            state = "golden_cross"
        elif cross_days is not None and not cur:
            state = "death_cross"
        elif abs(gap_now) <= 3 and slope > 0 and price > s50:
            state = "converging_up"
        elif abs(gap_now) <= 3:
            state = "squeeze"
    adx_v, pdi_v, mdi_v = adx_calc(h, lo_, c)
    def rt_(k):
        return (price / c[-1 - k] - 1) * 100 if len(c) > k else None
    rs_raw = None
    if len(c) > 250:
        rs_raw = 0.4 * rt_(63) + 0.2 * rt_(126) + 0.2 * rt_(189) + 0.2 * rt_(250)
    nf = nifty_returns()
    r6 = rt_(126)
    base20 = mean(v[-23:-3])
    return {
        "adx": adx_v, "pdi": pdi_v, "mdi": mdi_v, "atr": atr_calc(h, lo_, c), "rs_raw": rs_raw,
        "rs_nifty6m": (r6 - nf["r6"]) if (r6 is not None and nf.get("r6") is not None) else None,
        "ret2d": rt_(2), "ret5d": rt_(5), "ret6m": r6,
        "vol_max3": (max(v[-3:]) / base20) if base20 else None,
        "price": price, "day": (price / prev - 1) * 100,
        "dma50": mean(c[-50:]), "dma200": mean(c[-200:]) if len(c) >= 200 else None,
        "hi52": max(h[-252:]),
        "vol": v[-1], "avg20": avg20, "vol_ratio": (v[-1] / avg20) if avg20 else None,
        "turnover_cr": (price * avg20 / 1e7) if avg20 else None,
        "ret1m": (price / c[-22] - 1) * 100 if len(c) > 22 else None,
        "ret3m": (price / c[-64] - 1) * 100 if len(c) > 64 else None,
        "asof": now_ist().strftime("%d %b %H:%M"),
        "dma_gap": gap_now, "dma_state": state, "cross_days": cross_days,
    }

def market_overview():
    out = {}
    for key, sym in (("nifty", "^NSEI"), ("vix", "^INDIAVIX")):
        d = fetch_chart(sym)
        if d and len(d["close"]) > 60:
            c = d["close"]
            out[key] = {"price": c[-1], "dma50": mean(c[-50:]),
                        "dma200": mean(c[-200:]) if len(c) >= 200 else None,
                        "ret1m": (c[-1] / c[-22] - 1) * 100}
    n, vx = out.get("nifty"), out.get("vix")
    if n:
        weak = n["dma200"] and n["price"] < n["dma200"]
        vol = vx and vx["price"] > 20
        if weak:
            out["mood"] = "Weak - Nifty below 200-DMA. Keep positions small, favour only the strongest names."
            out["tone"] = "r"
        elif vol:
            out["mood"] = "Volatile - India VIX above 20. Stagger entries, expect sharp swings."
            out["tone"] = "a"
        elif n["ret1m"] > 0:
            out["mood"] = "Constructive - Nifty above 200-DMA and rising. Breakouts have better odds."
            out["tone"] = "g"
        else:
            out["mood"] = "Sideways - uptrend intact but momentum paused. Be selective."
            out["tone"] = "a"
    return out

# ----------------------------------------------------------------------------
# News (Google News RSS) with simple sentiment
# ----------------------------------------------------------------------------
def clean_name(n):
    return re.sub(r"\b(Ltd|Limited|Pvt|Private|India)\.?\b", "", n, flags=re.I).strip(" .")

def get_news(name, max_items=5, extra="stock", window="7d"):
    r = get("https://news.google.com/rss/search",
            params={"q": f'"{clean_name(name)}" {extra} when:{window}', "hl": "en-IN", "gl": "IN", "ceid": "IN:en"})
    items = []
    try:
        root = ET.fromstring(r.content)
        for it in root.iter("item"):
            title = (it.findtext("title") or "").strip()
            link = (it.findtext("link") or "").strip()
            if not link.startswith("http"):
                continue
            dt = parsedate_to_datetime(it.findtext("pubDate"))
            age_h = (datetime.now(timezone.utc) - dt).total_seconds() / 3600
            low = title.lower()
            pos = sum(w in low for w in POS_WORDS)
            neg = sum(w in low for w in NEG_WORDS)
            ago = f"{int(age_h)}h ago" if age_h < 48 else f"{int(age_h/24)}d ago"
            items.append({"title": title, "link": link, "src": (it.findtext("source") or "").strip(),
                          "ago": ago, "age_h": round(age_h, 1), "s": (pos > neg) - (neg > pos)})
            if len(items) >= max_items:
                break
    except Exception:
        pass
    return items

# ----------------------------------------------------------------------------
# Concall / order book / credit rating / brokerage / PLI per stock
# ----------------------------------------------------------------------------
AMT_RE = re.compile(r"(?:Rs\.?|INR|\u20b9)\s?([\d,]+(?:\.\d+)?)\s?(lakh crore|crore|cr\b|bn|billion|mn|million)?", re.I)
VAL_RE = re.compile(r"(?:Rs\.?|INR|\u20b9)\s?([\d,]+(?:\.\d+)?)\s?(lakh crore|crore|cr\b|bn|billion|mn|million)", re.I)
BOOK_RE = re.compile(r"order\s*(book|backlog)", re.I)
FLOW_RE = re.compile(r"order\s*(inflow|pipeline|intake)", re.I)
RATING_RE = re.compile(r"\b(AAA|AA\+|AA-|AA|A\+|A-|BBB\+|BBB-|BBB|BB\+|BB-|BB)(?![A-Za-z+\-])\s*(?:\(?(?:CE|SO)\)?)?\s*[/(,]?\s*(Stable|Positive|Negative|Watch\s\w+)")
POS_T = ["strong", "robust", "confident", "record", "healthy", "visibility", "momentum", "optimistic", "ahead of", "comfortable", "ramp"]
NEG_T = ["headwind", "challeng", "weak", "delay", "pressure", "slowdown", "uncertain", "cautious", "subdued", "decline", "soft demand"]

def find_amt(text):
    m = AMT_RE.search(text)
    return m.group(0).strip() if m and m.group(2) else ""

def to_cr(num_s, unit):
    try:
        v, u = float(num_s.replace(",", "")), unit.lower()
    except Exception:
        return None
    if u.startswith("lakh"):
        return v * 1e5
    if u.startswith("cr"):
        return v
    if u in ("bn", "billion"):
        return v * 100
    if u in ("mn", "million"):
        return v / 10
    return None

def pdf_text(url, max_pages=40):
    try:
        r = requests.get(url, headers={**UA, "Referer": "https://www.screener.in/"}, timeout=40)
        if r.status_code != 200 or len(r.content) > 15_000_000:
            return ""
        if r.content[:4] == b"%PDF":
            from pypdf import PdfReader
            rd = PdfReader(io.BytesIO(r.content))
            return " ".join((pg.extract_text() or "") for pg in rd.pages[:max_pages])
        return BeautifulSoup(r.text, "html.parser").get_text(" ")
    except Exception:
        return ""

CERT_KW = ["AS9100", "AS 9100", "NADCAP", "ASME", "N-stamp", "NQA-1", "IATF 16949", "CEMILAC", "DGAQA", "ISO 13485", "API 6A"]
QUAL_RE = re.compile(r"approved vendor|vendor approval|qualif(?:ied|ication)|first article|PPAP|sole[- ]source|single[- ]source|"
                     r"long[- ]term agreement|\bLTA\b|framework agreement|rate contract|repeat order|development order", re.I)
TOPCUST_RE = re.compile(r"(?:top|largest|biggest|single|one)\s+(?:\w+\s+){0,2}customers?[^.%]{0,60}?(\d{1,2})\s*%", re.I)

def analyse_transcript(text):
    text = re.sub(r"\s+", " ", text)
    sents = [x.strip() for x in re.split(r"(?<=[.?!])\s+", text) if 40 <= len(x) <= 320]
    cut = lambda x: x[:220]
    book = [x for x in sents if BOOK_RE.search(x) and re.search(r"\d", x)]
    flow = [x for x in sents if FLOW_RE.search(x) and re.search(r"\d", x)]
    ob_cr, ob_text = None, ""
    for x in book:
        m = VAL_RE.search(x)
        if m:
            v = to_cr(m.group(1), m.group(2))
            if v:
                ob_cr, ob_text = v, f"Order book about Rs {v:,.0f} Cr"
                break
    guid = [x for x in sents if re.search(r"guidance|we expect|outlook|aim to|confident|target", x, re.I) and re.search(r"\d", x)]
    capex = [x for x in sents if re.search(r"capex|capacity|expansion|commission", x, re.I) and re.search(r"\d", x)]
    risks = [x for x in sents if re.search(r"headwind|challeng|delay|pressure|slowdown|uncertain", x, re.I)]
    low = text.lower()
    pos, neg = sum(low.count(w) for w in POS_T), sum(low.count(w) for w in NEG_T)
    ratio = pos / (neg + 1)
    tone = "Positive" if ratio >= 3 else "Cautious" if ratio <= 1.2 else "Mixed"
    return {"tone": tone, "ob_cr": ob_cr, "ob_text": ob_text, "order_book": [cut(x) for x in (book[:2] + flow[:1])][:3],
            "guidance": [cut(x) for x in guid[:2]], "capex": [cut(x) for x in capex[:2]], "risks": [cut(x) for x in risks[:2]],
            "targets": target_areas(low), "focus": [cut(x) for x in sents if FOCUS_RE.search(x)][:3],
            "customers": customer_scan(sents),
            "certs": sorted({c for c in CERT_KW if re.search(r"(?<![A-Za-z0-9])" + re.escape(c) + r"(?![A-Za-z0-9])", text, re.I)}),
            "quals": [cut(x) for x in sents if QUAL_RE.search(x)][:3],
            "top_cust_pct": next((int(m_.group(1)) for m_ in (TOPCUST_RE.search(x) for x in sents) if m_), None), "v": 3}

def parse_rating(text, link_text):
    m = RATING_RE.search(text or "")
    ag = re.search(r"from\s+([\w .&-]+)$", link_text.strip())
    dt = re.search(r"(\d{1,2}\s+\w{3}\s+\d{4})", link_text)
    return {"rating": f"{m.group(1)}/{m.group(2)}" if m else "", "agency": ag.group(1).strip().upper() if ag else "",
            "date": dt.group(1) if dt else ""}

def enrich(s, prev):
    """Deep check: latest concall transcript + latest credit rating report. Cached by link."""
    d = s.get("docs") or {}
    tr = d.get("transcript")
    if tr:
        if (prev.get("concall") or {}).get("link") == tr and (prev.get("concall") or {}).get("v") == 3:
            s["concall"] = prev["concall"]
        else:
            txt = pdf_text(tr)
            if txt:
                c = analyse_transcript(txt)
                c["link"], c["ppt"] = tr, d.get("ppt", "")
                s["concall"] = c
            time.sleep(1)
    rl = (d.get("ratings") or [None])[0]
    if rl:
        if (prev.get("credit") or {}).get("link") == rl["href"]:
            s["credit"] = prev["credit"]
        else:
            c = parse_rating(pdf_text(rl["href"], max_pages=4), rl["text"])
            c["link"] = rl["href"]
            s["credit"] = c
            time.sleep(1)

def pli_stock(name):
    out = []
    for it in get_news(name, max_items=8, extra="PLI scheme incentive"):
        low = it["title"].lower()
        if "pli" in low or "production linked" in low or "production-linked" in low:
            it["amt"] = find_amt(it["title"])
            out.append(it)
    return out[:3]

def areas_of(tags, name, about):
    tg, nm, ab = tags.lower(), name.lower(), " " + (about or "").lower() + " "
    out = []
    for a, d in AREAS.items():
        if any(k in tg or k in nm for k in d["tags"] + d.get("name", [])) or any(k in ab for k in d["text"]):
            out.append(a)
    return out

def target_areas(low):
    low = " " + low + " "
    sc = {a: sum(low.count(k) for k in d["text"]) for a, d in AREAS.items()}
    top = sorted(((n, a) for a, n in sc.items() if n >= 3), reverse=True)[:4]
    return [{"area": a, "n": n} for n, a in top]

def customer_scan(sents, src="concall", link=""):
    found = {}
    for x in sents:
        if not CUST_TRIG.search(x):
            continue
        for nm_ in set(CUST_RE.findall(x)):
            d = found.setdefault(nm_, {"name": nm_, "region": CUSTOMERS[nm_], "n": 0, "ctx": "", "src": src, "link": link})
            d["n"] += 1
            if not d["ctx"]:
                d["ctx"] = x[:220]
    return sorted(found.values(), key=lambda d: -d["n"])[:8]

def amt_cr_of(text):
    m = VAL_RE.search(text or "")
    return to_cr(m.group(1), m.group(2)) if m else None

def orders_news(name):
    nm = clean_name(name)
    first = nm.split()[0].lower() if nm.split() else ""
    r = get("https://news.google.com/rss/search", params={
        "q": f'"{nm}" order OR contract OR partnership OR "supply agreement" OR MoU when:180d',
        "hl": "en-IN", "gl": "IN", "ceid": "IN:en"})
    out = []
    if r is None:
        return out
    for it in feed_items(r.content, 14):
        low = it["title"].lower()
        if len(first) >= 3 and first not in low:
            continue
        if not re.search(r"order|contract|partner|supply|agreement|mou|tie-up|collaborat|bags|secures|wins", low):
            continue
        it["cust"] = [d["name"] for d in customer_scan([it["title"]], "news", it["link"])]
        it["amt_cr"] = amt_cr_of(it["title"])
        out.append(it)
    return out[:8]

def broker_view(name):
    out, seen = [], set()
    for extra in ("target price brokerage rating", "Kotak OR ICICI OR Motilal OR Axis OR Nuvama OR Jefferies OR Nomura OR HDFC OR Emkay buy OR sell"):
        for it in get_news(name, max_items=8, extra=extra, window="60d"):
            key = it["title"].lower()[:70]
            if key in seen:
                continue
            seen.add(key)
            low = it["title"].lower()
            who = list(dict.fromkeys(BROKER_RE.findall(it["title"])))
            tg = TARGET_RE.search(it["title"])
            call = ("Buy" if re.search(r"\b(buy|outperform|overweight|accumulate|add)\b", low) else
                    "Sell" if re.search(r"\b(sell|underperform|underweight|reduce)\b", low) else
                    "Hold" if re.search(r"\b(hold|neutral|market perform)\b", low) else "")
            if not (who or tg or call):
                continue
            it.update(who=who, target=int(tg.group(1).replace(",", "")) if tg and tg.group(1).replace(",", "").isdigit() else None,
                      call=call, view={"Buy": 1, "Sell": -1}.get(call, 0))
            out.append(it)
    out.sort(key=lambda i: (not i["who"], i["age_h"]))
    return out[:5]

def prio_of(s):
    if s.get("watch"):
        return 3
    f = s.get("f") or {}
    fl = sum(bool(f.get(k)) for k in ("ath_q_sales", "ath_q_profit", "ath_y_sales", "ath_y_profit", "profit_breakout"))
    if fl >= 4:
        return 2
    if fl == 3 or (f.get("results") or {}).get("verdict") == "Excellent":
        return 1
    return 0

def pli_scan():
    out, seen = [], set()
    for q in PLI_QUERIES:
        r = get("https://news.google.com/rss/search", params={"q": q + " when:60d", "hl": "en-IN", "gl": "IN", "ceid": "IN:en"})
        if r is not None:
            for it in feed_items(r.content, 10):
                key = it["title"].lower()[:70]
                if key not in seen:
                    seen.add(key)
                    it["amt"] = find_amt(it["title"])
                    out.append(it)
        time.sleep(0.5)
    out.sort(key=lambda i: (not i["amt"], i["age_h"]))
    return out[:15]

# ----------------------------------------------------------------------------
# Government / policy tracking
# ----------------------------------------------------------------------------
def _ctext(it, name):
    for c in it:
        if c.tag.split("}")[-1] == name:
            return (c.text or "").strip(), c
    return "", None

def feed_items(content, limit=12):
    """Generic RSS/Atom parser."""
    out = []
    try:
        root = ET.fromstring(content)
    except Exception:
        return out
    for it in root.iter():
        if it.tag.split("}")[-1] not in ("item", "entry"):
            continue
        title, _ = _ctext(it, "title")
        link, lc = _ctext(it, "link")
        if not link and lc is not None:
            link = lc.get("href", "")
        ds = _ctext(it, "pubDate")[0] or _ctext(it, "published")[0] or _ctext(it, "updated")[0] or _ctext(it, "date")[0]
        try:
            dt = parsedate_to_datetime(ds)
        except Exception:
            try:
                dt = datetime.fromisoformat(ds.replace("Z", "+00:00"))
            except Exception:
                dt = datetime.now(timezone.utc)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        age_h = (datetime.now(timezone.utc) - dt).total_seconds() / 3600
        src = _ctext(it, "source")[0]
        if title and link.startswith("http"):
            out.append({"title": title, "link": link, "src": src, "age_h": round(age_h, 1),
                        "ago": f"{int(age_h)}h ago" if age_h < 48 else f"{int(age_h / 24)}d ago"})
        if len(out) >= limit:
            break
    return out

def policy_item_score(it):
    low = it["title"].lower()
    s = min(3, sum(w in low for w in POLICY_POS)) - sum(w in low for w in POLICY_NEG)
    it["s"] = (s > 0) - (s < 0)
    weight = 2 if it["age_h"] <= 24 * 7 else 1 if it["age_h"] <= 24 * 30 else 0
    return s * weight

def tag_theme(title):
    low = title.lower()
    return next((th for th, kws in POLICY_KW.items() if any(k in low for k in kws)), "")

def policy_scan(extra_sectors=()):
    queries = dict(POLICY_QUERIES)
    for sct in extra_sectors:
        queries[sct] = [f"{sct} India government scheme Cabinet approves"]
    themes = {th: {"items": []} for th in queries}
    seen = set()
    def add(th, it):
        key = it["title"].lower()[:70]
        if key not in seen and it["age_h"] <= 24 * 30:
            seen.add(key); themes[th]["items"].append(it)
    for th, qs in queries.items():
        for q in qs:
            r = get("https://news.google.com/rss/search",
                    params={"q": q + " when:30d", "hl": "en-IN", "gl": "IN", "ceid": "IN:en"})
            if r is not None:
                for it in feed_items(r.content, 8):
                    add(th, it)
            time.sleep(0.5)
    r = get(PIB_FEED)
    if r is not None:
        for it in feed_items(r.content, 60):
            th = tag_theme(it["title"])
            if th:
                it["src"] = it["src"] or "PIB"; add(th, it)
    letters = []
    for url in NEWSLETTER_FEEDS:
        r = get(url)
        if r is None:
            continue
        for it in feed_items(r.content, 10):
            it["src"] = it["src"] or re.sub(r"^https?://(www\.)?", "", url).split("/")[0]
            it["theme"] = tag_theme(it["title"]) or "General"
            policy_item_score(it); letters.append(it)
    for th, d in themes.items():
        score = sum(policy_item_score(it) for it in d["items"])
        d["items"].sort(key=lambda i: (-i["s"], i["age_h"]))
        d["items"] = d["items"][:6]
        d["score"] = score
        d["level"] = "High" if score >= 10 else "Medium" if score >= 4 else "Low"
    letters.sort(key=lambda i: i["age_h"])
    print("policy:", {k: v["level"] for k, v in themes.items()}, "newsletter items:", len(letters))
    return {"themes": themes, "newsletters": letters[:25], "at": now_ist().strftime("%d %b %H:%M")}

def policy_view(p):
    if not p:
        return {"themes": [], "newsletters": [], "at": ""}
    th = [{"theme": k, "level": v["level"], "score": v["score"], "items": v["items"]} for k, v in p["themes"].items()]
    th.sort(key=lambda x: -x["score"])
    return {"themes": th, "newsletters": p.get("newsletters", []), "at": p.get("at", "")}

# ----------------------------------------------------------------------------
# Sector cycle
# ----------------------------------------------------------------------------
def sector_cycle(stocks, policy=None):
    by = {}
    for s in stocks:
        for th in (s.get("areas") or ([s["theme"]] if s.get("theme") else [])):
            by.setdefault(th, []).append(s)
    out = []
    for theme, ss in by.items():
        fs = [s["f"] for s in ss]
        ms = [s["m"] for s in ss if s.get("m")]
        n = len(ss)
        earn = pct_true([f["ath_q_profit"] for f in fs])
        sales_ath = pct_true([f["ath_q_sales"] for f in fs])
        opm_up = pct_true([(f["opm_now"] or 0) > (f["opm_yr"] or 0) for f in fs if f["opm_now"] is not None and f["opm_yr"] is not None])
        a200 = pct_true([m["price"] > m["dma200"] for m in ms if m.get("dma200")])
        r1, r3 = med([m["ret1m"] for m in ms]), med([m["ret3m"] for m in ms])
        r3v, r1v = r3 or 0, r1 or 0
        if n < 3:
            phase, stance, tone, pts = "Too few stocks to judge", "WAIT", "a", 2
        elif earn >= 40 and r3v > 0 and a200 >= 60:
            if r1v > 15:
                phase, stance, tone, pts = "Hot - extended upcycle", "FOCUS (don't chase)", "a", 6
            else:
                phase, stance, tone, pts = "Upcycle - earnings and price both strong", "FOCUS", "g", 10
        elif earn >= 40:
            phase, stance, tone, pts = "Earnings at peak but price weakening (late-cycle risk)", "REDUCE / AVOID", "r", 2
        elif earn >= 20 and r3v > 0:
            phase, stance, tone, pts = "Early upcycle - earnings starting to build", "FOCUS (early)", "g", 8
        elif earn >= 20:
            phase, stance, tone, pts = "Earnings improving but price not confirming", "WAIT", "a", 4
        else:
            phase, stance, tone, pts = "Weak / out of favour", "AVOID", "r", 0
        pol = ((policy or {}).get("themes") or {}).get(theme, {})
        plevel = pol.get("level", "n/a")
        pts += {"High": 4, "Medium": 2}.get(plevel, 0)
        hay = (theme + " " + " ".join({s.get("tags", "") for s in ss})).lower()
        pli_s = [p for p in PLI_SCHEMES if any(k in hay for k in p["kw"])]
        info = THEME_INFO.get(theme, {})
        top = sorted(ss, key=lambda s: -(s.get("score") or 0))[:5]
        out.append({"theme": theme, "n": n, "phase": phase, "stance": stance, "tone": tone, "pts": pts,
                    "earn_ath_pct": round(earn), "sales_ath_pct": round(sales_ath), "opm_up_pct": round(opm_up),
                    "above200_pct": round(a200), "ret1m": r1, "ret3m": r3,
                    "drivers": info.get("drivers", ""), "risks": info.get("risks", ""),
                    "top": [s["sym"] for s in top],
                    "policy_level": plevel, "policy_top": (pol.get("items") or [{}])[0].get("title", ""),
                    "pli": [{"scheme": p["scheme"], "outlay_cr": p["outlay_cr"], "why": p["why"]} for p in pli_s[:3]]})
    out.sort(key=lambda x: -x["pts"])
    return out

# ----------------------------------------------------------------------------
# Scoring: Bullish / Watch / Avoid with reasons
# ----------------------------------------------------------------------------
def multibagger(s, f, m, rs, hv, mg, call, wc_ok, rk, adx_):
    """Early multibagger check: growing company + promoters/insiders buying + uptrend + sensible price + room to grow."""
    ins = s.get("insider") or []
    ibuy = any(i["kind"] == "Insider buying" and i["age_h"] <= 24 * 180 for i in ins)
    isell = any(i["kind"] == "Insider selling" and i["age_h"] <= 24 * 180 for i in ins)
    cg = f.get("cagr") or {}
    p3, s3 = cg.get("profit3"), cg.get("sales3")
    pch = ((hv or {}).get("ch") or {}).get("promoters") or {}
    py, ph = pch.get("y"), pch.get("now")
    pyoy, syoy = (rs or {}).get("profit_yoy"), (rs or {}).get("sales_yoy")
    verdict = (rs or {}).get("verdict")
    pe, mcap, pledged = f.get("pe"), f.get("mcap"), f.get("pledged") or 0
    price, d200 = m.get("price"), m.get("dma200")
    sc, why, risks = 0, [], []
    growing = bool(verdict in ("Excellent", "Good") and pyoy is not None and pyoy >= 20 and (syoy is None or syoy >= 10))
    if p3 is not None:
        sc += 12 if p3 >= 30 else 9 if p3 >= 20 else 6 if p3 >= 15 else 0
    if s3 is not None:
        sc += 6 if s3 >= 20 else 3 if s3 >= 12 else 0
    sc += 7 if verdict == "Excellent" else 4 if verdict == "Good" else 0
    sc += 8 if (mg or {}).get("verdict") == "Excellent" else 4 if (mg or {}).get("verdict") == "Good" else 0
    tier_pts = sum(bool(f.get(k)) for k in ("ath_q_sales", "ath_q_profit", "ath_y_sales", "ath_y_profit", "profit_breakout"))
    sc += {5: 7, 4: 5, 3: 2}.get(tier_pts, 0)
    if ph is not None:
        sc += 5 if ph >= 60 else 4 if ph >= 50 else 2 if ph >= 40 else 0
    prom_up = py is not None and py >= 0.3
    prom_sell = py is not None and py <= -1
    if py is not None:
        sc += 8 if py >= 1 else 5 if prom_up else -10 if py <= -2 else -4 if prom_sell else 0
    if ibuy:
        sc += 8
        why.append("Promoters / directors buying shares (insider buying headlines)")
    if isell:
        sc -= 10
        risks.append("Insider / promoter selling headlines")
    if pledged >= 10:
        sc -= 8
        risks.append(f"Promoters pledged {pledged:.0f}% of shares")
    if hv:
        inst = hv.get("inst")
        sc += 6 if inst == "Accumulating" else -4 if inst == "Reducing" else 0
        if any("New " in x["t"] for x in hv.get("signals", [])):
            sc += 3
    if rk is not None:
        sc += 6 if rk >= 80 else 3 if rk >= 60 else -3 if rk < 30 else 0
    uptrend = None if not (price and d200) else price > d200
    if uptrend:
        sc += 3
    if adx_ is not None and adx_ >= 25 and (m.get("pdi") or 0) > (m.get("mdi") or 0):
        sc += 3
    if s.get("m") and (m.get("vol_ratio") or 0) >= 1.5 and (m.get("ret5d") or 0) < 4 and verdict in ("Excellent", "Good"):
        sc += 4
    peg = (pe / p3) if (pe and p3 and p3 > 0) else None
    if peg is not None:
        sc += 5 if peg <= 1 else 3 if peg <= 1.5 else 1 if peg <= 2 else -5 if peg > 3 else 0
    if pe and pe > 80:
        sc -= 5
    if mcap:
        sc += 4 if mcap < 2000 else 3 if mcap < 10000 else 0 if mcap < 30000 else -5 if mcap >= 50000 else -2
    if f.get("roce"):
        sc += 5 if f["roce"] >= 25 else 3 if f["roce"] >= 18 else 0
    sc += 2 if wc_ok else -4 if wc_ok is False else 0
    sc = max(0, min(100, round(sc)))
    promoter_ok = bool(prom_up or ibuy)
    not_selling = not prom_sell and not isell and pledged < 10
    size_ok = None if not mcap else mcap <= 30000
    val_ok = None if not pe else (pe <= 60 or (peg is not None and peg <= 2))
    gates = [
        {"t": "Company is growing: latest quarter profit " + (f"{pyoy:+.0f}%" if pyoy is not None else "n/a") + " and sales " +
              (f"{syoy:+.0f}%" if syoy is not None else "n/a") + " year on year", "ok": growing if rs else None},
        {"t": "Long-run growth: profit " + (f"{p3:.0f}% a year over 3 years" if p3 is not None else "history not available"),
         "ok": None if p3 is None else p3 >= 15},
        {"t": "Promoters raising their stake or insiders buying" + (f" (promoter holding {ph:.1f}%, {py:+.1f} pts in a year)" if ph is not None and py is not None else ""),
         "ok": promoter_ok if (hv or s.get("insider")) else None},
        {"t": "Nobody selling: promoters not reducing, no pledged shares, no insider selling", "ok": not_selling if hv else None},
        {"t": "Price in an uptrend (above its 200-day average)", "ok": uptrend},
        {"t": "Valuation not stretched" + (f" (P/E {pe:.0f}" + (f", PEG {peg:.1f}" if peg is not None else "") + ")" if pe else ""), "ok": val_ok},
        {"t": "Room to grow" + (f": market cap Rs {mcap:,.0f} Cr" if mcap else ""), "ok": size_ok},
        {"t": "Working capital healthy (debtor and inventory days not rising)", "ok": wc_ok},
        {"t": "Tradable: not flagged AVOID", "ok": call != "AVOID"},
    ]
    must = [growing, promoter_ok, not_selling, uptrend is not False, size_ok is not False, val_ok is not False,
            call != "AVOID", wc_ok is not False]
    if sc >= 70 and all(must) and hv:
        mcall = "MULTIBAGGER BUY"
    elif sc >= 55 and growing and not_selling and call != "AVOID":
        mcall = "STRONG WATCH"
    else:
        mcall = ""
    for g in gates:
        if g["ok"] is True:
            why.append(g["t"])
    return {"score": sc, "call": mcall, "gates": gates, "why": why[:6], "risks": risks, "pu": py, "ph": ph, "p3": p3,
            "insider_buy": ibuy}

def build_view(s, cyc):
    f, m, news = s["f"], s.get("m") or {}, s.get("news", [])
    why, risks, score = [], [], 0
    aths = [("ath_q_sales", "quarterly sales"), ("ath_q_profit", "quarterly profit"),
            ("ath_y_sales", "annual sales"), ("ath_y_profit", "annual profit")]
    got = [l for k, l in aths if f.get(k)]
    miss = [l for k, l in aths if not f.get(k)]
    score += 8 * len(got)
    if len(got) == 4:
        why.append("All-time-high sales AND profit (quarterly + annual)")
    elif got:
        why.append("Record " + ", ".join(got))
    if miss:
        risks.append("Not at record: " + ", ".join(miss))
    flags = sum(bool(f.get(k)) for k, _ in aths) + bool(f.get("profit_breakout"))
    tier = "A" if flags == 5 else "B" if flags == 4 else "C" if flags == 3 else "-"
    if f.get("profit_breakout"):
        score += 8
        why.append(f"Profit breakout: +{f['profit_yoy']:.0f}% YoY and above the last 4 quarters")
    elif f.get("profit_yoy") is not None:
        risks.append(f"No profit breakout (qtr profit {f['profit_yoy']:+.0f}% YoY)")
    if f.get("sales_yoy") is not None and f["sales_yoy"] >= 15:
        why.append(f"Sales growing {f['sales_yoy']:.0f}% YoY")
    if f.get("opm_now") is not None and f.get("opm_yr") is not None:
        if f["opm_now"] > f["opm_yr"]:
            why.append(f"Margins expanding ({f['opm_yr']:.0f}% to {f['opm_now']:.0f}%)")
        else:
            risks.append(f"Margins shrinking ({f['opm_yr']:.0f}% to {f['opm_now']:.0f}%) - record profit may be near peak")
    if f.get("roce") and f["roce"] >= 20:
        score += 5
        why.append(f"ROCE {f['roce']:.0f}% - strong capital efficiency (moat proxy)")

    hard_avoid = False
    wc_ok = f.get("wc_ok")
    fm = lambda a, b: f"{a:.0f} to {b:.0f}" if a is not None and b is not None else "n/a"
    if wc_ok is True:
        why.append(f"Working capital healthy - debtor days {fm(f.get('debtor_prev'), f.get('debtor_days'))}, "
                   f"inventory days {fm(f.get('inv_prev'), f.get('inv_days'))} (not rising)")
    elif wc_ok is False:
        score -= 6
        risks.append(f"Working capital stretching - debtor days {fm(f.get('debtor_prev'), f.get('debtor_days'))}, "
                     f"inventory days {fm(f.get('inv_prev'), f.get('inv_days'))} (rising): check receivables / stock build-up")
    if m:
        price, d50, d200, hi = m["price"], m.get("dma50"), m.get("dma200"), m.get("hi52")
        gap = (hi - price) / hi * 100 if hi else None
        if d200 and price > d200:
            if gap is not None and gap <= NEAR_HIGH_PCT:
                score += 12
                why.append(f"Price {gap:.1f}% from 52-wk high, above 200-DMA - breakout zone")
            else:
                score += 6
                why.append("Above 200-DMA - uptrend intact")
            if d50 and price > d50:
                score += 4
            if price / d200 - 1 > 0.40:
                score -= 6
                risks.append(f"Extended: {100*(price/d200-1):.0f}% above 200-DMA - chasing risk")
        elif d200:
            if m.get("dma_state") in ("golden_cross", "converging_up", "squeeze") and price >= d200 * 0.97:
                risks.append("Just under 200-DMA - needs to close above it to confirm")
            else:
                hard_avoid = True
                risks.append("Below 200-DMA - trend not confirmed")
        st_ = m.get("dma_state")
        if st_ in ("golden_cross", "converging_up") and d200 and price >= d200 * 0.97:
            score += 6
            gp = m.get("dma_gap")
            why.append("50-DMA meeting 200-DMA" + (f" (gap {gp:+.1f}%)" if gp is not None else "")
                       + (f", golden cross {m['cross_days']} sessions ago" if st_ == "golden_cross" and m.get("cross_days") else "")
                       + " - classic trend-turn zone")
        elif st_ == "death_cross":
            score -= 5
            risks.append("50-DMA recently crossed below 200-DMA (death cross) - trend turning down")
        vr, day = m.get("vol_ratio"), m.get("day", 0)
        if vr and vr >= 1.5 and day > 0:
            score += 10
            why.append(f"Volume {vr:.1f}x the 20-day average with price up {day:.1f}% - buyers active")
        elif vr and vr >= 1.2 and day > 0:
            score += 5
            why.append(f"Volume {vr:.1f}x average on an up day")
        elif vr and vr >= 1.5 and day < -1:
            score -= 6
            risks.append(f"Heavy volume ({vr:.1f}x) on a {day:.1f}% fall - selling pressure")
        t = m.get("turnover_cr")
        if t is not None and t < MIN_TURNOVER_CR:
            score -= 5
            risks.append(f"Thin liquidity (~Rs {t:.1f} Cr/day) - hard to exit")
            if t < 1:
                hard_avoid = True
    else:
        risks.append("No live price data yet")
    pe = f.get("pe")
    if pe and pe > 70:
        score -= 5
        risks.append(f"Rich valuation (P/E {pe:.0f})")

    net = sum(n["s"] for n in news)
    score += max(-10, min(10, net * 4))
    pos = next((n for n in news if n["s"] > 0), None)
    neg = next((n for n in news if n["s"] < 0), None)
    if pos:
        why.append("News: " + pos["title"][:110])
    if neg:
        risks.append("News: " + neg["title"][:110])
    if net <= -2:
        hard_avoid = True

    cc, cr, bk, pl = s.get("concall") or {}, s.get("credit") or {}, s.get("broker") or [], s.get("pli") or []
    ob_text = cc.get("ob_text", "")
    if cc.get("ob_cr") and f.get("y_sales"):
        yrs = cc["ob_cr"] / f["y_sales"]
        ob_text = f"{ob_text} = {yrs:.1f}x annual sales"
        if yrs >= 1.5:
            score += 5
            why.append(f"Strong order book: {yrs:.1f}x annual sales (revenue visibility)")
        elif yrs < 0.5:
            risks.append(f"Thin order book: only {yrs:.1f}x annual sales")
    if cc.get("tone") == "Positive":
        score += 3
        why.append("Latest concall: management tone confident / positive")
    elif cc.get("tone") == "Cautious":
        score -= 4
        risks.append("Latest concall: management tone cautious (headwinds / delays mentioned)")
    if cc.get("guidance") and cc.get("tone") != "Cautious":
        why.append("Management outlook: " + cc["guidance"][0][:130])
    rt = cr.get("rating", "")
    if rt:
        if re.match(r"(AAA|AA)", rt) and "Negative" not in rt:
            score += 3
            why.append(f"Credit rating {rt} ({cr.get('agency', '')}) - strong balance sheet")
        elif "Negative" in rt or re.match(r"(BBB|BB)", rt):
            score -= 4
            risks.append(f"Credit rating {rt} ({cr.get('agency', '')}) - weaker credit quality")
    bnet = sum(b.get("view", 0) for b in bk)
    if bnet > 0:
        score += 2
        why.append("Brokerage view positive: " + bk[0]["title"][:100])
    elif bnet < 0:
        score -= 3
        risks.append("Brokerage view negative: " + bk[0]["title"][:100])
    if pl:
        score += 2
        why.append("PLI link: " + pl[0]["title"][:100])

    rs, hv, inv = f.get("results"), s.get("holding"), s.get("invest") or []
    if rs:
        bits = [f"{lab} {rs[k]:+.0f}% YoY" for lab, k in (("sales", "sales_yoy"), ("profit", "profit_yoy")) if rs.get(k) is not None]
        rtxt = f"{rs.get('period', '')}: {rs['verdict']}" + (" (" + ", ".join(bits) + ")" if bits else "")
        if rs["verdict"] == "Excellent":
            score += 3
            why.append("Latest quarter " + rtxt)
        elif rs["verdict"] == "Good":
            score += 1
            why.append("Latest quarter " + rtxt)
        elif rs["verdict"] in ("Weak", "Loss-making"):
            score -= 5
            risks.append("Latest quarter " + rtxt)
    if hv:
        score += 3 if hv["inst"] == "Accumulating" else -3 if hv["inst"] == "Reducing" else 0
        for sg_ in hv["signals"]:
            (why if sg_["tone"] == "g" else risks).append(sg_["t"])
    if (f.get("pledged") or 0) >= 10:
        score -= 4
        risks.append(f"Promoters have pledged {f['pledged']:.0f}% of their shares")
    for it in inv:
        if it["kind"].startswith("Preferential") and it["age_h"] <= 24 * 120:
            risks.append("Fund-raise headline - check who subscribed and at what price: " + it["title"][:100])
            break
    for it in inv:
        if it["kind"] == "Big investor" and it["age_h"] <= 24 * 60:
            why.append("Big-investor headline: " + it["title"][:100])
            break

    mg, cg = f.get("margin"), f.get("cogs")
    if mg:
        txt = ""
        if cg and cg.get("now") is not None and cg.get("yr") is not None:
            txt = f" (COGS {cg['yr']:.0f}% to {cg['now']:.0f}% of sales)"
        elif mg.get("cost_now") is not None and mg.get("cost_yr") is not None:
            txt = f" (costs {mg['cost_yr']:.0f}% to {mg['cost_now']:.0f}% of sales)"
        if mg["verdict"] == "Excellent":
            score += 5
            why.append("Cost quality excellent: costs falling, margin expanding, operating profit growing" + txt)
        elif mg["verdict"] == "Good":
            score += 2
            why.append("Margins improving and operating profit growing" + txt)
        elif mg["verdict"] == "Weak":
            score -= 5
            risks.append("Cost quality weak: margin shrinking or operating profit falling" + txt)
    adx_, pdi_, mdi_ = m.get("adx"), m.get("pdi"), m.get("mdi")
    if adx_ is not None:
        if adx_ >= 30 and (pdi_ or 0) > (mdi_ or 0):
            score += 5
            why.append(f"ADX {adx_:.0f} (above 30 = excellent trend strength) with buyers in control")
        elif adx_ >= 30:
            score -= 5
            risks.append(f"ADX {adx_:.0f}: strong DOWN trend (sellers in control)")
        elif adx_ >= 20 and (pdi_ or 0) > (mdi_ or 0):
            score += 2
            why.append(f"ADX {adx_:.0f}: uptrend building")
        elif adx_ < 20:
            risks.append(f"ADX {adx_:.0f}: no clear trend yet")
    rk = m.get("rs_rank")
    if rk is not None:
        if rk >= 80:
            score += 5
            why.append(f"Relative strength rank {rk}/99: outperforming most stocks")
        elif rk >= 60:
            score += 2
        elif rk < 30:
            score -= 4
            risks.append(f"Weak relative strength (rank {rk}/99)")
    mc_ = f.get("mcap")
    if mc_ and mc_ < 500:
        risks.append(f"Micro cap (Rs {mc_:.0f} Cr): thin trading, higher risk - keep the position small")
    accum_info = None
    flat = [lab for lab, k_, lim in (("2 days", "ret2d", 2), ("1 week", "ret5d", 4), ("1 month", "ret1m", 8))
            if m.get(k_) is not None and m[k_] < lim]
    vsurge = max(m.get("vol_ratio") or 0, m.get("vol_max3") or 0)
    if rs and rs["verdict"] in ("Excellent", "Good") and flat and vsurge >= 1.5 and m.get("price") and \
            (not m.get("dma200") or m["price"] >= m["dma200"] * 0.97):
        score += 8
        accum_info = {"flat": flat, "vol": vsurge}
        why.append(f"Quiet accumulation: {rs['verdict']} results, price flat over {', '.join(flat)}, "
                   f"volume {vsurge:.1f}x its 20-day average - big institutions may be buying")

    ords = [i for i in (s.get("orders") or []) if i.get("age_h", 0) <= 24 * 180]
    flt = [x for x in ((s.get("docs") or {}).get("filings") or []) if re.search(r"order|contract|award|\bLoA\b", x["text"], re.I)]
    cr_news = sum({round(i["amt_cr"], 1) for i in ords if i.get("amt_cr")})
    cr_file = sum({round(amt_cr_of(x["text"]), 1) for x in flt if amt_cr_of(x["text"])})
    ocr = max(cr_news, cr_file)
    ysales = f.get("y_sales")
    opct = (ocr / ysales * 100) if (ocr and ysales and ysales > 0) else None
    ordd = {"n": len(ords) + len(flt), "cr": ocr or None, "pct": opct, "files": flt[:3],
            "cust": list(dict.fromkeys(n_ for i in ords for n_ in (i.get("cust") or [])))[:4]}
    if opct is not None:
        if opct >= 25:
            score += 4
            why.append(f"Big order wins: about Rs {ocr:,.0f} Cr announced in 6 months = {opct:.0f}% of annual sales"
                       + (f" (customers: {', '.join(ordd['cust'])})" if ordd["cust"] else ""))
        elif opct >= 10:
            score += 2
            why.append(f"Order wins of about Rs {ocr:,.0f} Cr in 6 months = {opct:.0f}% of annual sales")
    if cc.get("certs"):
        score += 2
        why.append("Quality approvals mentioned on the concall: " + ", ".join(cc["certs"][:3]))
    if cc.get("quals"):
        score += 2
        why.append("Vendor-qualification / long-term-agreement language on the concall")
    if (cc.get("top_cust_pct") or 0) >= 40:
        risks.append(f"Customer concentration: top customers are about {cc['top_cust_pct']}% of sales")

    cy = next((c for c in cyc if c["theme"] == s["theme"]), None)
    if cy:
        score += cy["pts"]
        (why if cy["tone"] == "g" else risks if cy["tone"] == "r" else why).append(f"Sector cycle: {cy['phase']}")
        if cy.get("policy_level") == "High":
            why.append("Policy tailwind: " + (cy.get("policy_top") or "strong government focus")[:100])

    score = max(0, min(100, round(score)))
    if hard_avoid or score < 45 or (tier == "-" and score < 55):
        verdict = "Avoid"
    elif score >= 70 and tier in ("A", "B") and m and wc_ok is not False:
        verdict = "Bullish"
    else:
        verdict = "Watch"
    pr_, d50_, d200_ = m.get("price"), m.get("dma50"), m.get("dma200")
    ext = bool(pr_ and ((d50_ and pr_ > d50_ * 1.10) or (d200_ and pr_ / d200_ - 1 > 0.40)))
    if verdict == "Avoid":
        call = "AVOID"
    elif verdict == "Bullish":
        call = "HOLD" if ext else "BUY"
    else:
        call = "HOLD" if (tier in ("A", "B") and score >= 60 and ext) else "WAIT"

    plan = {"stop": None, "maxw": 0, "entry": ""}
    if m and verdict != "Avoid":
        d50 = m.get("dma50") or m["price"] * 0.92
        if m.get("atr"):
            plan["stop"] = round(max(m["price"] - 2 * m["atr"], m["price"] * 0.85), 1)
        else:
            plan["stop"] = round(max(d50 * 0.98, m["price"] * 0.88), 1)
        risk_ = m["price"] - plan["stop"]
        plan["t1"], plan["t2"] = round(m["price"] + 2 * risk_, 1), round(m["price"] + 3 * risk_, 1)
        plan["risk_pct"] = round(100 * risk_ / m["price"], 1)
        plan["maxw"] = (5 if tier == "A" else 4) if verdict == "Bullish" else 2
        if (f.get("mcap") or 1e9) < 1000:
            plan["maxw"] = min(plan["maxw"], 3)
        if m["price"] > d50 * 1.08:
            plan["entry"] = f"Extended above 50-DMA - wait for a dip toward Rs {d50*1.03:.0f} or start only 1/3 now."
        elif verdict == "Bullish":
            plan["entry"] = "Start 1/3 position now, add 1/3 on a volume-backed new high, last 1/3 on a dip to the 50-DMA."
        else:
            plan["entry"] = "On the watchlist. Wait for volume above 1.5x average with a close near the 52-wk high."
        if call == "HOLD":
            plan["entry"] = f"Strong but extended: keep what you own, do not add. Add only on a dip toward Rs {d50 * 1.03:.0f}."
    custs = {c["name"]: dict(c) for c in cc.get("customers", [])}
    for it in s.get("orders") or []:
        for nm_ in it.get("cust", []):
            if nm_ not in custs:
                custs[nm_] = {"name": nm_, "region": CUSTOMERS.get(nm_, ""), "n": 1, "ctx": it["title"][:220], "src": "news", "link": it["link"]}
    customers = sorted(custs.values(), key=lambda c: -c["n"])[:8]
    mb = multibagger(s, f, m, rs, hv, mg, call, wc_ok, rk, adx_)
    sym = s["sym"]
    return {
        "sym": sym, "name": s["name"], "theme": s["theme"], "tier": tier, "flags": flags, "score": score,
        "verdict": verdict, "price": m.get("price"), "day": m.get("day"), "vol_ratio": m.get("vol_ratio"),
        "turnover_cr": m.get("turnover_cr"), "asof": m.get("asof"), "pe": pe, "roce": f.get("roce"),
        "mcap": f.get("mcap"), "period": f.get("period"), "ret1m": m.get("ret1m"), "ret3m": m.get("ret3m"),
        "why": why, "risks": risks, "news": news, "plan": plan, "net_news": net,
        "concall": cc, "credit": cr, "broker": bk, "pli": pl, "ob_text": ob_text, "sector": s.get("sector", ""),
        "dma_gap": m.get("dma_gap"), "dma_state": m.get("dma_state"), "cross_days": m.get("cross_days"),
        "wc": {k: f.get(k) for k in ("debtor_days", "debtor_prev", "inv_days", "inv_prev", "wc_ok")},
        "results": rs, "holding": hv, "invest": inv, "filings": (s.get("docs") or {}).get("filings", []),
        "watch": bool(s.get("watch")), "pledged": f.get("pledged"),
        "adx": adx_, "pdi": pdi_, "mdi": mdi_, "rs_rank": rk, "rs_nifty6m": m.get("rs_nifty6m"),
        "margin": mg, "cogs": cg, "accum": accum_info, "ret2d": m.get("ret2d"), "ret5d": m.get("ret5d"),
        "call": call, "areas": s.get("areas", []), "mb": mb, "ord": ordd, "insider": s.get("insider") or [], "cagr": f.get("cagr"),
        "targets": [x["area"] for x in cc.get("targets", [])], "about": (s.get("about") or "")[:420],
        "customers": customers, "orders": s.get("orders", []),
        "links": {"screener": s["url"], "chart": f"https://in.tradingview.com/chart/?symbol=NSE%3A{sym}",
                  "news": "https://news.google.com/search?q=" + requests.utils.quote(clean_name(s['name']) + " stock")},
    }

# ----------------------------------------------------------------------------
# Alerts
# ----------------------------------------------------------------------------
def send_alert(text):
    tg, chat = os.getenv("TELEGRAM_TOKEN"), os.getenv("TELEGRAM_CHAT_ID")
    if tg and chat:
        try:
            requests.post(f"https://api.telegram.org/bot{tg}/sendMessage",
                          data={"chat_id": chat, "text": text[:4000], "disable_web_page_preview": True}, timeout=20)
        except requests.RequestException:
            pass
    eu, ep, eto = os.getenv("EMAIL_USER"), os.getenv("EMAIL_PASS"), os.getenv("EMAIL_TO")
    if eu and ep and eto:
        try:
            m = EmailMessage()
            m["Subject"], m["From"], m["To"] = "India Moat Screener alert", eu, eto
            m.set_content(text)
            with smtplib.SMTP_SSL("smtp.gmail.com", 465) as srv:
                srv.login(eu, ep); srv.send_message(m)
        except Exception as e:
            print("email failed:", e)

def do_alerts(views, data):
    done = set(data.get("alerted", []))
    msgs = []
    today = now_ist().strftime("%Y-%m-%d")
    for v in views:
        k = f"{v['sym']}|multibagger"
        if v["mb"]["call"] == "MULTIBAGGER BUY" and k not in done:
            msgs.append(f"MULTIBAGGER BUY: {v['name']} ({v['theme']})\nMulti-bagger score {v['mb']['score']}/100. "
                        + "; ".join(v["mb"]["why"][:3]) + f"\n{v['links']['screener']}")
            done.add(k)
        o_ = v.get("ord") or {}
        k = f"{v['sym']}|ord|{int(o_.get('cr') or 0)}"
        if o_.get("pct") and o_["pct"] >= 25 and (v.get("mcap") or 1e9) < 5000 and v["verdict"] != "Avoid" and k not in done:
            msgs.append(f"BIG ORDERS: {v['name']} announced about Rs {o_['cr']:,.0f} Cr of orders = {o_['pct']:.0f}% of annual sales"
                        + (f" (customers: {', '.join(o_['cust'])})" if o_.get("cust") else "") + f"\n{v['links']['screener']}")
            done.add(k)
        if v["verdict"] == "Avoid":
            continue
        k = f"{v['sym']}|tier{v['tier']}"
        if v["tier"] == "A" and k not in done and v["score"] >= ALERT_MIN_SCORE:
            msgs.append(f"NEW all-rule match: {v['name']} ({v['theme']})\nScore {v['score']}/100 - {v['verdict']}\n"
                        f"{v['why'][0] if v['why'] else ''}\n{v['links']['screener']}"); done.add(k)
        if v["score"] >= ALERT_MIN_SCORE or v["tier"] in ("A", "B"):
            for n in v["news"]:
                if n["s"] != 0 and n["age_h"] <= 24:
                    k = f"{v['sym']}|news|{hashlib.md5(n['title'].encode()).hexdigest()[:10]}"
                    if k not in done:
                        icon = "NEWS (+)" if n["s"] > 0 else "NEWS (-)"
                        msgs.append(f"{icon} {v['name']}: {n['title']}\n{n['link']}"); done.add(k)
            vr = v.get("vol_ratio")
            k = f"{v['sym']}|vol|{today}"
            if vr and vr >= 2 and (v.get("day") or 0) > 1 and k not in done:
                msgs.append(f"VOLUME SPIKE {v['name']}: {vr:.1f}x avg volume, price {v['day']:+.1f}% today\n{v['links']['chart']}")
                done.add(k)
    data["alerted"] = list(done)[-3000:]
    if msgs:
        send_alert("\n\n".join(msgs))
    print(f"alerts sent: {len(msgs)}")

# ----------------------------------------------------------------------------
# Pipelines
# ----------------------------------------------------------------------------
def load_data():
    try:
        return json.load(open(DATA_FILE))
    except Exception:
        return None

RAW_SHARDS = 16
KEEP_KEYS = ("m", "news", "concall", "credit", "broker", "pli", "invest", "insider", "orders", "deep_at", "enrich_key", "enrich_tries")

def safe_sym(sym):
    return re.sub(r"[^A-Za-z0-9_.-]", "_", sym)

def load_raw():
    raw = {}
    for i in range(RAW_SHARDS):
        try:
            raw.update(json.load(open(f"{DATA_DIR}/raw/{i:02d}.json")))
        except Exception:
            pass
    return raw

def save_raw(raw):
    os.makedirs(f"{DATA_DIR}/raw", exist_ok=True)
    shards = [{} for _ in range(RAW_SHARDS)]
    for sym, s in raw.items():
        shards[int(hashlib.md5(sym.encode()).hexdigest(), 16) % RAW_SHARDS][sym] = s
    for i, sh in enumerate(shards):
        json.dump(clean(sh), open(f"{DATA_DIR}/raw/{i:02d}.json", "w"), separators=(",", ":"))

def load_state():
    try:
        return json.load(open(DATA_FILE))
    except Exception:
        return {}

def save_state(state):
    os.makedirs(DATA_DIR, exist_ok=True)
    json.dump(clean(state), open(DATA_FILE, "w"), separators=(",", ":"))

def clean(o):
    # JSON cannot hold NaN / Infinity, so turn them into null
    if isinstance(o, float):
        return o if o == o and o not in (float("inf"), float("-inf")) else None
    if isinstance(o, dict):
        return {k: clean(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [clean(v) for v in o]
    return o

_PACE = {"delay": 1.0}

def fetch_company(url):
    """Returns the page html, "" if the page does not exist, None if Screener keeps refusing us.
    When Screener says 'too many requests' we wait, slow our pace, and try again."""
    for i in range(5):
        try:
            r = S.get(url, timeout=30)
        except requests.RequestException:
            time.sleep(5)
            continue
        if r.status_code in (429, 403) or r.status_code >= 500:
            try:
                ra = int(r.headers.get("Retry-After", 0))
            except ValueError:
                ra = 0
            wait = min(600, ra or 30 * (2 ** i))
            _PACE["delay"] = min(6.0, _PACE["delay"] * 1.5)
            print(f"Screener said HTTP {r.status_code}: waiting {wait}s and slowing to {_PACE['delay']:.1f}s per stock")
            time.sleep(wait)
            continue
        _PACE["delay"] = max(1.0, _PACE["delay"] * 0.97)
        return r.text if (r.status_code == 200 and "top-ratios" in r.text) else ""
    return None

def exchange_universe():
    """Fallback list of every NSE-listed company, used when Screener's own listing is cut short."""
    import csv
    rows = []
    try:
        r = requests.get("https://nsearchives.nseindia.com/content/equities/EQUITY_L.csv", headers=UA, timeout=40)
        if r.status_code == 200:
            for rec in list(csv.reader(r.text.splitlines()))[1:]:
                if len(rec) > 2 and rec[0].strip() and rec[2].strip() in ("EQ", "BE", "BZ", "SM", "ST"):
                    sym = rec[0].strip()
                    rows.append({"name": rec[1].strip() or sym, "url": f"{BASE}/company/{sym}/consolidated/", "guess": True})
    except Exception as e:
        print("NSE list failed:", e)
    return rows

def short_flags(s):
    f = s["f"]
    return sum(bool(f[k]) for k in ("ath_q_sales", "ath_q_profit", "ath_y_sales", "ath_y_profit", "profit_breakout"))

def full_scan():
    t0 = time.time()
    budget = float(os.getenv("BUDGET_MIN") or BUDGET_MIN) * 60
    dl = lambda frac: t0 + budget * frac
    scan_note = ""
    state, raw = load_state(), load_raw()
    login()
    rows = run_screen()
    print(f"Screener universe: {len(rows)} companies; {len(raw)} already saved")
    if len(rows) < 1500:
        have_u = {r_["url"] for r_ in rows}
        extra_rows = [x for x in exchange_universe() if x["url"] not in have_u]
        print(f"Screener's own listing is short - adding {len(extra_rows)} companies from the NSE list")
        rows = rows + extra_rows
    watch = sorted(set(EXTRA_WATCHLIST) | set(state.get("watch", [])) |
                   {x for x in re.split(r"[,\s]+", os.getenv("WATCH", "").upper()) if x})
    by_sym = {}
    for r_ in rows:
        mm = re.search(r"/company/([^/]+)/", r_["url"])
        if mm:
            by_sym.setdefault(mm.group(1), r_)
    have = {k.upper() for k in by_sym}
    for w in watch:
        if w not in have:
            by_sym[w] = {"name": w, "url": f"{BASE}/company/{w}/consolidated/", "watch": True}
    wset = set(watch)
    now = time.time()
    for sym in by_sym:
        if sym in raw:
            raw[sym]["seen_at"] = now
    for sym in list(raw):
        if sym not in by_sym and now - raw[sym].get("seen_at", now) > 30 * 86400:
            del raw[sym]

    # ---- phase 1: financials from Screener (new and stale stocks first) ----
    def due(sym):
        o = raw.get(sym)
        if not o:
            return True
        return now - o.get("fund_at", 0) > 86400 * (1 if prio_of(o) >= 1 else FUND_REFRESH_DAYS)
    try:
        pri_urls = {x["url"] for x in screen_rows(PRIORITY_QUERY, 30)[0]}
    except Exception:
        pri_urls = set()
    print(f"priority list (fast-growing companies, loaded first): {len(pri_urls)}")
    todo = sorted([sy for sy in by_sym if due(sy)],
                  key=lambda sy: (sy in raw, 0 if by_sym[sy]["url"] in pri_urls else 1,
                                  -prio_of(raw[sy]) if sy in raw else 0, raw.get(sy, {}).get("fund_at", 0)))
    print(f"phase 1: {len(todo)} stocks need fresh financials")
    done = blocked = 0
    for sym in todo:
        if time.time() > dl(0.62):
            print("phase 1: time slice used up, will continue next run")
            break
        r_ = by_sym[sym]
        html = fetch_company(r_["url"])
        if html is None:
            blocked += 1
            if blocked >= 2:
                scan_note = "Screener slowed us down; the rest loads on the next run"
                print("Screener keeps refusing requests - stopping page fetches for this run")
                break
            continue
        blocked = 0
        if not html and (r_.get("watch") or r_.get("guess")):
            html = fetch_company(r_["url"].replace("/consolidated/", "/")) or ""
        if not html:
            continue
        try:
            s = parse_company(html, r_)
        except Exception as e:
            print("parse failed", sym, e)
            continue
        if (r_.get("watch") or r_.get("guess")) and s["f"]["q_sales"] is None:
            if r_.get("watch"):
                print("watchlist symbol not found:", sym)
            continue
        if short_flags(s) >= 3 or s.get("watch"):
            s["f"]["cogs"] = fetch_cogs(html, r_["url"])
            time.sleep(0.6)
        o = raw.get(sym, {})
        for k in KEEP_KEYS:
            if k in o:
                s[k] = o[k]
        if sym.upper() in wset:
            s["watch"] = True
        s["fund_at"], s["seen_at"] = time.time(), now
        raw[sym] = s
        done += 1
        time.sleep(_PACE["delay"])
    print(f"phase 1 done: {done} stocks refreshed; {len(raw)} of {len(by_sym)} universe stocks now loaded")
    save_raw(raw)

    # ---- phase 2: price, volume, 50/200 DMA ----
    n2 = 0
    for s in sorted(raw.values(), key=lambda x: (-prio_of(x), (x.get("m") or {}).get("ts", 0))):
        if time.time() > dl(0.74):
            break
        if prio_of(s) < 2 and time.time() - (s.get("m") or {}).get("ts", 0) < 16 * 3600:
            continue
        m = market_metrics(s["sym"])
        if m:
            m["ts"] = time.time()
            s["m"] = m
        n2 += 1
        time.sleep(0.35)
    print(f"phase 2 done: market data for {n2} stocks")
    save_raw(raw)

    # ---- phase 3: news, PLI, big investors, orders, brokers (shortlisted stocks often, others in rotation) ----
    def deep_due(s):
        return time.time() - s.get("deep_at", 0) > {3: 0.5, 2: 1, 1: 3, 0: 10}[prio_of(s)] * 86400
    n3 = 0
    for s in sorted([x for x in raw.values() if deep_due(x)], key=lambda x: (-prio_of(x), x.get("deep_at", 0))):
        if time.time() > dl(0.88):
            break
        try:
            s["news"] = get_news(s["name"]); time.sleep(0.5)
            s["pli"] = pli_stock(s["name"]); time.sleep(0.4)
            s["invest"] = investor_news(s["name"])
            s["insider"] = insider_news(s["name"]); time.sleep(0.4)
            s["orders"] = orders_news(s["name"]); time.sleep(0.4)
            s["broker"] = broker_view(s["name"]); time.sleep(0.4)
            s["deep_at"] = time.time()
            n3 += 1
        except Exception as e:
            print("deep scan failed", s["name"], e)
    print(f"phase 3 done: news/investor/orders/brokers for {n3} stocks")
    save_raw(raw)

    # ---- phase 4: concall transcripts and credit ratings ----
    n4 = 0
    for s in sorted(raw.values(), key=lambda x: -prio_of(x)):
        if time.time() > dl(0.95) or n4 >= ENRICH_PER_RUN:
            break
        d = s.get("docs") or {}
        key = (d.get("transcript") or "") + "|" + ((d.get("ratings") or [{}])[0].get("href", ""))
        if key == "|" or s.get("enrich_key") == key:
            continue
        try:
            enrich(s, s)
            s["enrich_tries"] = s.get("enrich_tries", 0) + 1
            if s.get("concall") or s.get("credit") or s["enrich_tries"] >= 3:
                s["enrich_key"], s["enrich_tries"] = key, 0
            n4 += 1
        except Exception as e:
            print("enrich failed", s["name"], e)
    print(f"phase 4 done: concalls / ratings read for {n4} stocks")

    # ---- policy and PLI headlines ----
    extra = sorted({s["sector"] for s in raw.values() if not s.get("areas") and s.get("sector")})[:POLICY_EXTRA_MAX]
    state["policy"] = policy_scan(extra)
    state["pli_news"] = pli_scan()
    state["watch"] = watch
    state["universe_n"] = len(by_sym)
    state["scan_note"] = scan_note
    state["full_at"] = now_ist().strftime("%d %b %Y %H:%M IST")
    save_raw(raw)
    return raw, state

def live_refresh():
    raw, state = load_raw(), load_state()
    if not raw:
        print("No saved data yet - running a full scan first.")
        return full_scan()
    todo = sorted([s for s in raw.values() if prio_of(s) >= 1],
                  key=lambda s: (-prio_of(s), (s.get("m") or {}).get("ts", 0)))[:LIVE_SHORTLIST_MAX * 3]
    for s in todo:
        m = market_metrics(s["sym"])
        if m:
            m["ts"] = time.time()
            s["m"] = m
        s["news"] = get_news(s["name"]); time.sleep(0.5)
    save_raw(raw)
    return raw, state

def render(raw, state, alerts=True):
    stocks = list(raw.values())
    demo = bool(state.get("demo"))
    rs_list = sorted((s["m"]["rs_raw"], i) for i, s in enumerate(stocks) if s.get("m") and s["m"].get("rs_raw") is not None)
    for rank_, (_, i_) in enumerate(rs_list):
        stocks[i_]["m"]["rs_rank"] = max(1, min(99, round(99 * rank_ / max(1, len(rs_list) - 1))))
    state["market"] = state.get("market") if demo else market_overview()
    cyc = sector_cycle(stocks, state.get("policy"))
    views = [build_view(s, cyc) for s in stocks]
    for s, v in zip(stocks, views):
        s["score"] = v["score"]
    cyc = sector_cycle(stocks, state.get("policy"))
    views.sort(key=lambda v: (-{"Bullish": 2, "Watch": 1, "Avoid": 0}[v["verdict"]], -v["score"]))
    featured = [v for v in views if v["tier"] != "-" or v["watch"] or v["verdict"] != "Avoid"][:FEATURED_MAX]

    news = []
    for v in featured:
        for n in v["news"]:
            news.append({**n, "sym": v["sym"], "name": v["name"]})
    news.sort(key=lambda n: n["age_h"])

    cust = {}
    for v in views:
        for c in v["customers"]:
            e = cust.setdefault(c["name"], {"name": c["name"], "region": c["region"], "cos": []})
            e["cos"].append({"sym": v["sym"], "name": v["name"], "call": v["call"], "ctx": c["ctx"], "src": c["src"], "n": c["n"]})
    orders = sorted(cust.values(), key=lambda e: -len(e["cos"]))[:80]
    for e in orders:
        e["cos"] = sorted(e["cos"], key=lambda c: -c["n"])[:15]

    acc = [{"sym": v["sym"], "name": v["name"], "call": v["call"], "score": v["score"],
            "signals": [x["t"] for x in v["holding"]["signals"]][:4]}
           for v in views if (v.get("holding") or {}).get("inst") == "Accumulating"]
    acc = sorted(acc, key=lambda x: -x["score"])[:60]
    deals, prefs = [], []
    for v in views:
        for it in v["invest"]:
            row = {"sym": v["sym"], "name": v["name"], "title": it["title"], "link": it["link"], "src": it.get("src", ""),
                   "ago": it.get("ago", ""), "age_h": it.get("age_h", 0)}
            (prefs if it["kind"].startswith("Preferential") else deals).append(row)
        for fl in v["filings"]:
            if "preferential" in fl["text"].lower() or "warrant" in fl["text"].lower():
                prefs.append({"sym": v["sym"], "name": v["name"], "title": fl["text"], "link": fl["href"], "src": "Filing", "ago": "", "age_h": 9999})
    deals.sort(key=lambda x: x["age_h"]); prefs.sort(key=lambda x: x["age_h"])
    brokers = []
    for v in views:
        for b in v["broker"]:
            brokers.append({**b, "sym": v["sym"], "name": v["name"], "scall": v["call"]})
    brokers.sort(key=lambda b: (not b.get("who"), b.get("age_h", 0)))

    cnt_a, cnt_s = {}, {}
    for v in views:
        for a_ in v["areas"]:
            cnt_a[a_] = cnt_a.get(a_, 0) + 1
        if not v["areas"] and v["sector"]:
            cnt_s[v["sector"]] = cnt_s.get(v["sector"], 0) + 1
    areas = [{"area": a_, "n": cnt_a[a_], "kind": "area"} for a_ in AREAS if cnt_a.get(a_)]
    areas += [{"area": k, "n": n, "kind": "sector"} for k, n in sorted(cnt_s.items(), key=lambda kv: -kv[1])[:80]]

    summary = [{"s": v["sym"], "n": v["name"], "a": v["areas"], "t": v["sector"] or v["theme"], "c": v["mcap"], "p": v["price"],
                "d": v["day"], "v": v["call"], "sc": v["score"], "tr": v["tier"],
                "rv": (v["results"] or {}).get("verdict", ""), "tg": v["targets"][:3],
                "sy": (v["results"] or {}).get("sales_yoy"), "py": (v["results"] or {}).get("profit_yoy"),
                "mg": (v["margin"] or {}).get("verdict", ""), "ad": v["adx"], "rs": v["rs_rank"],
                "mb": v["mb"]["score"], "mbc": v["mb"]["call"], "pu": v["mb"]["pu"], "ph": v["mb"]["ph"],
                "ib": 1 if v["mb"]["insider_buy"] else 0, "pg": v["mb"]["p3"],
                "vr": round(v["vol_ratio"], 1) if v.get("vol_ratio") else None,
                "oc": v["ord"]["cr"], "op": v["ord"]["pct"], "on": v["ord"]["n"], "ou": v["ord"]["cust"][:3]} for v in views]

    quiet = sorted([{"sym": v["sym"], "name": v["name"], "call": v["call"], "score": v["score"],
                     "rv": (v["results"] or {}).get("verdict", ""), "flat": v["accum"]["flat"], "vol": v["accum"]["vol"],
                     "adx": v["adx"], "rs": v["rs_rank"]} for v in views if v.get("accum")], key=lambda x: -x["score"])[:80]
    out = {
        "updated": now_ist().strftime("%d %b %Y, %H:%M IST"), "full_at": state.get("full_at", ""),
        "market": state.get("market", {}), "policy": policy_view(state.get("policy")), "sectors": cyc,
        "pli": {"schemes": [{k: v_ for k, v_ in p_.items() if k != "kw"} for p_ in PLI_SCHEMES], "news": state.get("pli_news", []),
                "stocks": [{"name": v["name"], "sym": v["sym"], "theme": v["theme"], "verdict": v["verdict"], "items": v["pli"]}
                           for v in featured if v["pli"]]},
        "coverage": {"loaded": len(views), "universe": state.get("universe_n"), "note": state.get("scan_note", "")}, "stocks": featured, "accum": quiet, "news": news[:60], "areas": areas, "orders": orders,
        "big": {"acc": acc, "deals": deals[:60], "prefs": prefs[:60]}, "brokers": brokers[:80],
        "focus_themes": [c["theme"] for c in cyc if c["stance"].startswith("FOCUS")],
        "avoid_themes": [c["theme"] for c in cyc if c["stance"] in ("AVOID", "REDUCE / AVOID")],
        "counts": {"candidates": len(views), "A": sum(v["tier"] == "A" for v in views), "B": sum(v["tier"] == "B" for v in views),
                   "bullish": sum(v["verdict"] == "Bullish" for v in views)},
    }
    if demo:   # the offline demo page cannot fetch files, so embed everything
        out["univ"] = summary
        out["detail"] = {v["sym"]: v for v in views}

    os.makedirs(f"{DATA_DIR}/d", exist_ok=True)
    keep = set()
    for v in views:
        fn = safe_sym(v["sym"]) + ".json"
        keep.add(fn)
        json.dump(clean(v), open(f"{DATA_DIR}/d/{fn}", "w"), separators=(",", ":"))
    for fn in os.listdir(f"{DATA_DIR}/d"):
        if fn not in keep:
            os.remove(f"{DATA_DIR}/d/{fn}")
    json.dump(clean(summary), open(f"{DATA_DIR}/summary.json", "w"), separators=(",", ":"))
    if alerts and not demo:
        do_alerts(views, state)
    save_state(state)
    payload = json.dumps(clean(out), ensure_ascii=True).replace("</", "<\\/")
    open(f"{OUT_DIR}/index.html", "w", encoding="utf-8").write(HTML.replace("__DATA__", payload))
    open(f"{OUT_DIR}/.nojekyll", "w").write("")
    print(f"Dashboard written to {OUT_DIR}/ : {len(views)} stocks, {len(featured)} featured "
          f"(A={out['counts']['A']} B={out['counts']['B']} buy={out['counts']['bullish']})")

# ----------------------------------------------------------------------------
# Demo data (to preview the dashboard offline)
# ----------------------------------------------------------------------------
def demo_data():
    random.seed(7)
    names = [("Apex Precision Forge", 0), ("AeroDyn Components", 0), ("Voltgrid Transformers", 1), ("Kiran Switchgear", 1),
             ("Powerlink Cables", 1), ("AquaPure Chemicals", 2), ("FluoroSpec Industries", 2), ("ChipAssure Electronics", 3),
             ("Sensora EMS", 3), ("RailTrack Systems", 4), ("AutoMatic Controls", 4), ("MetalWorks Castings", 0),
             ("PowerTech Insulators", 1), ("PureFlow Water", 2), ("Microfab Semicon", 3)]
    themes = ["Precision engineering & components", "Transmission, transformers & T&D", "Specialty chemicals",
              "Electronics & EMS", "Railways"]
    stocks = []
    for i, (n, ti) in enumerate(names):
        strong = i % 3 != 2
        flags = [strong, strong, strong or i % 2 == 0, strong and i % 4 != 1, strong]
        price = random.uniform(300, 4000)
        d200 = price * random.uniform(0.7, 0.95) if strong else price * random.uniform(1.02, 1.2)
        f = {"period": "Jun 2026", "q_sales": 320.5, "q_profit": 48.2, "sales_yoy": random.uniform(8, 40),
             "profit_yoy": random.uniform(10, 70), "opm_now": 19, "opm_yr": 19 + random.choice([-2, 2.5]),
             "roce": random.uniform(14, 32), "pe": random.uniform(25, 90), "mcap": random.uniform(2000, 40000),
             "ath_q_sales": flags[0], "ath_q_profit": flags[1], "ath_y_sales": flags[2], "ath_y_profit": flags[3],
             "profit_breakout": flags[4], "y_sales": 1200,
             "debtor_days": 62, "debtor_prev": 60 if strong else 48, "inv_days": 80, "inv_prev": 84, "wc_ok": strong}
        m = {"price": price, "day": random.uniform(-2, 4), "dma50": price * random.uniform(0.9, 1.05), "dma200": d200,
             "hi52": price * random.uniform(1.0, 1.15), "vol": 1, "avg20": 1, "vol_ratio": random.uniform(0.6, 3),
             "turnover_cr": random.uniform(0.8, 40), "ret1m": random.uniform(-5, 18), "ret3m": random.uniform(-8, 35),
             "asof": "demo", "adx": random.uniform(14, 42), "pdi": 27, "mdi": 14, "atr": price * 0.03,
             "rs_raw": random.uniform(-10, 80), "ret2d": random.uniform(-1.5, 3), "ret5d": random.uniform(-2, 7),
             "vol_max3": random.uniform(0.7, 2.6), "rs_nifty6m": random.uniform(-8, 30), "dma_gap": random.uniform(-3, 4),
             "dma_state": random.choice(["golden_cross", "converging_up", "squeeze", None, "death_cross"]), "cross_days": 9}
        news = []
        if strong:
            news = [{"title": f"{n} bags Rs {random.randint(80, 900)} crore export order", "link": "https://news.google.com",
                     "src": "Demo Wire", "ago": f"{random.randint(1, 20)}h ago", "age_h": random.randint(1, 20), "s": 1}]
        elif i % 3 == 2:
            news = [{"title": f"{n} faces SEBI probe over disclosures", "link": "https://news.google.com", "src": "Demo Wire",
                     "ago": "5h ago", "age_h": 5, "s": -1}]
        stocks.append({"sym": n.split()[0].upper(), "name": n, "url": "https://www.screener.in", "tags": "",
                       "theme": themes[ti], "f": f, "m": m, "news": news})
    for i, s in enumerate(stocks):
        if i % 3 != 2:
            s["concall"] = {"tone": "Positive", "ob_cr": 2400, "ob_text": "Order book about Rs 2,400 Cr",
                            "order_book": ["Our order book stands at Rs 2,400 crore, up 35 percent year on year."],
                            "guidance": ["We expect around 25 percent revenue growth next year on new capacity."],
                            "capex": ["Phase 2 expansion of 40 percent more capacity will be commissioned by Q3."],
                            "risks": ["Raw material price volatility remains a watch item for us."], "link": "https://example.com", "ppt": ""}
            s["credit"] = {"rating": "AA/Stable", "agency": "CRISIL", "date": "22 Sep 2026", "link": "https://example.com"}
            s["broker"] = [{"title": "Brokerage initiates Buy with target of Rs 1,500", "link": "https://example.com", "src": "Demo",
                            "ago": "1d ago", "age_h": 24, "s": 1, "view": 1}]
            if i % 2 == 0:
                s["pli"] = [{"title": f"{s['name']} gets PLI approval, incentive of Rs 320 crore", "link": "https://example.com", "src": "Demo",
                             "ago": "2d ago", "age_h": 48, "s": 1, "amt": "Rs 320 crore"}]
    ql = ["Sep 2024", "Dec 2024", "Mar 2025", "Jun 2025", "Sep 2025", "Dec 2025", "Mar 2026", "Jun 2026"]
    for i, s in enumerate(stocks):
        base, gr = random.uniform(100, 400), random.uniform(-0.03, 0.12)
        sales = [round(base * (1 + gr) ** k, 1) for k in range(8)]
        prof = [round(x * random.uniform(0.08, 0.16), 1) for x in sales]
        s["f"]["results"] = results_view(ql, {"sales": sales, "net profit": prof,
                                              "opm %": [round(14 + k * random.uniform(-0.3, 0.6), 1) for k in range(8)]})
        ex = [round(x * (0.84 - (k * 0.01 if i % 3 != 2 else -k * 0.01)), 1) for k, x in enumerate(sales)]
        s["f"]["margin"] = margin_view({"sales": sales, "expenses": ex, "operating profit": [round(a - b, 1) for a, b in zip(sales, ex)],
                                        "opm %": [round(100 * (a - b) / a, 1) for a, b in zip(sales, ex)]})
        s["f"]["cogs"] = {"now": 52, "yr": 56, "q": 53} if i % 2 == 0 else None
        if i in (0, 3):
            s["f"]["results"]["verdict"] = "Excellent"
            s["f"]["results"].update(profit_yoy=45.0, sales_yoy=28.0)
            s["m"].update(ret2d=0.4, ret5d=1.1, ret1m=3.0, vol_ratio=1.9, vol_max3=2.2, dma200=s["m"]["price"] * 0.9)
        up = 1 if i % 3 != 2 else -1
        s["f"]["cagr"] = {"sales3": random.uniform(8, 35), "sales5": 15, "profit3": random.uniform(10, 45), "profit5": 20}
        if i % 3 == 0:
            s["insider"] = [{"title": f"Promoter buys 1.5 lakh shares of {s['name']} in open market", "link": "https://example.com",
                             "src": "Demo Wire", "ago": "9d ago", "age_h": 216, "s": 1, "kind": "Insider buying"}]
        s["holding"] = holding_view(ql, {
            "promoters": [round(55 + (0.15 if i % 2 == 0 else -0.1) * k, 1) for k in range(8)],
            "fiis": [round(4 + up * k * 0.4, 1) for k in range(8)],
            "diis": [round(0.5 + up * k * 0.5 + (3 if up > 0 else 6), 1) for k in range(8)],
            "government": [0.1] * 8, "public": [round(40 - up * k * 0.3, 1) for k in range(8)],
            "no. of shareholders": [20000 + k * (2500 if i % 4 == 0 else 200) for k in range(8)]})
        if i % 2 == 0:
            s["invest"] = [{"title": f"Mutual fund buys 1.2% stake in {s['name']} via block deal", "link": "https://example.com",
                            "src": "Demo Wire", "ago": "6d ago", "age_h": 144, "s": 1, "kind": "Big investor"}]
            if i % 4 == 0:
                s["invest"].append({"title": f"{s['name']} board approves preferential issue of warrants to investors", "link": "https://example.com",
                                    "src": "Demo Wire", "ago": "20d ago", "age_h": 480, "s": 1, "kind": "Preferential / fund raise"})
        s["docs"] = {"filings": [{"text": "Allotment of equity shares on preferential basis", "href": "https://example.com"}] if i % 4 == 0 else []}
    for i, s in enumerate(stocks):
        s["areas"] = [s["theme"]] + (["Nuclear"] if i % 5 == 0 else []) + (["Data centers & cooling"] if i % 4 == 0 else [])
        s["sector"] = "Capital Goods"
        s["about"] = "Demo company making precision components for aerospace, nuclear and data-centre customers."
        s["m"]["ts"] = time.time()
        if s.get("concall"):
            s["concall"]["targets"] = [{"area": "Aerospace", "n": 9}, {"area": "Nuclear", "n": 5}]
            s["concall"]["focus"] = ["We are targeting new customers in the data centre cooling segment next year."]
            s["concall"]["customers"] = [{"name": "Vertiv", "region": "Global", "n": 2, "src": "concall", "link": "",
                                          "ctx": "We received a repeat order from Vertiv for cooling assemblies."}]
        s["orders"] = ([{"title": f"{s['name']} bags Rs 320 crore order from Safran", "link": "https://example.com", "src": "Demo Wire",
                         "ago": "5d ago", "age_h": 120, "cust": ["Safran"], "amt_cr": 320.0}] if i % 3 == 0 else [])
        if i % 2 == 0:
            s["f"]["mcap"] = 1200 + i * 90
        if s.get("concall"):
            s["concall"].update(certs=["AS9100", "NADCAP"] if i % 2 == 0 else [], quals=["We are a qualified single-source supplier under a long-term agreement."] if i % 3 == 0 else [],
                                top_cust_pct=45 if i == 3 else None, v=3)
        for b in s.get("broker", []):
            b.update(who=["Kotak"], target=1500, call="Buy")
    pol = {"themes": {}, "newsletters": [{"title": "Demo newsletter: why T&D capex is accelerating", "link": "https://example.com",
           "src": "demo-letter", "ago": "6h ago", "age_h": 6, "s": 1, "theme": themes[1]}], "at": "demo"}
    for i, th in enumerate(themes):
        its = [{"title": f"Cabinet approves Rs {1000 * (i + 2)} crore scheme for {th.split(' / ')[0].lower()}", "link": "https://pib.gov.in",
                "src": "PIB", "ago": f"{i + 1}d ago", "age_h": 24 * (i + 1), "s": 1}]
        pol["themes"][th] = {"items": its, "score": [12, 8, 5, 11, 2][i], "level": ["High", "Medium", "Medium", "High", "Low"][i]}
    pli_news = [{"title": "Govt approves Rs 1,200 crore PLI incentive for 12 electronics component makers", "link": "https://example.com",
                 "src": "Demo Wire", "ago": "3d ago", "age_h": 72, "amt": "Rs 1,200 crore"}]
    return {"stocks": stocks, "demo": True, "policy": pol, "pli_news": pli_news, "full_at": "demo data",
            "market": {"nifty": {"price": 24500, "ret1m": 2.1}, "vix": {"price": 14.2},
                       "mood": "Constructive - Nifty above 200-DMA and rising. Breakouts have better odds.", "tone": "g"}}

# ----------------------------------------------------------------------------
# Dashboard HTML (single file, mobile-first)
# ----------------------------------------------------------------------------
HTML = r"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>India Moat Screener</title>
<style>
:root{--bg:#f4f5f7;--card:#fff;--tx:#141821;--mut:#667085;--bd:#e3e6ec;--g:#0a8f4e;--r:#d92d20;--a:#b54708;--gb:#e6f6ee;--rb:#fdecea;--ab:#fff3e0}
@media(prefers-color-scheme:dark){:root{--bg:#0d1015;--card:#161a21;--tx:#edf0f5;--mut:#98a2b3;--bd:#2a303a;--g:#32d583;--r:#f97066;--a:#fdb022;--gb:#10281d;--rb:#2e1513;--ab:#2d2210}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--tx);font:15px/1.45 -apple-system,Segoe UI,Roboto,sans-serif;padding-bottom:40px}
header{padding:calc(12px + env(safe-area-inset-top,0px)) 14px 8px}
h1{font-size:19px;margin:0}.sub{color:var(--mut);font-size:12px}
.mood{margin:8px 0 0;padding:9px 11px;border-radius:10px;font-size:13px}
.mood.g{background:var(--gb);color:var(--g)}.mood.a{background:var(--ab);color:var(--a)}.mood.r{background:var(--rb);color:var(--r)}
nav{position:sticky;top:0;background:var(--bg);display:flex;gap:6px;overflow-x:auto;padding:8px 14px;z-index:5;border-bottom:1px solid var(--bd)}
nav button{flex:none;border:1px solid var(--bd);background:var(--card);color:var(--tx);padding:7px 13px;border-radius:20px;font-size:14px}
nav button.on{background:var(--tx);color:var(--bg);border-color:var(--tx)}
main{padding:12px 14px;max-width:760px;margin:auto}
.stats{display:grid;grid-template-columns:repeat(4,1fr);gap:8px;margin-bottom:12px}
.stat{background:var(--card);border:1px solid var(--bd);border-radius:12px;padding:8px;text-align:center}
.stat b{display:block;font-size:20px}.stat span{font-size:11px;color:var(--mut)}
.card{background:var(--card);border:1px solid var(--bd);border-radius:14px;padding:13px;margin-bottom:11px}
.row{display:flex;justify-content:space-between;gap:8px;align-items:flex-start}
.name{font-weight:700;font-size:16px}.theme{font-size:12px;color:var(--mut)}
.badge{display:inline-block;padding:2px 9px;border-radius:12px;font-size:12px;font-weight:700}
.badge.g{background:var(--gb);color:var(--g)}.badge.a{background:var(--ab);color:var(--a)}.badge.r{background:var(--rb);color:var(--r)}
.score{font-size:24px;font-weight:800;text-align:right;line-height:1}.score small{display:block;font-size:10px;color:var(--mut);font-weight:400}
.g{color:var(--g)}.r{color:var(--r)}.a{color:var(--a)}
.kv{display:flex;flex-wrap:wrap;gap:6px 14px;margin:8px 0;font-size:13px}.kv span{color:var(--mut)}
ul{margin:4px 0 6px 18px;padding:0;font-size:13.5px}li{margin:2px 0}
.sec{font-size:12px;font-weight:700;margin-top:8px;text-transform:uppercase;letter-spacing:.04em}
.plan{background:var(--bg);border-radius:10px;padding:9px;font-size:13px;margin-top:8px}
.links a,.nw{color:var(--tx)}.links{display:flex;gap:8px;margin-top:9px}
.links a{font-size:12px;border:1px solid var(--bd);border-radius:8px;padding:5px 9px;text-decoration:none}
.nw{display:block;font-size:13px;text-decoration:none;padding:6px 0;border-top:1px solid var(--bd)}
.nw small{color:var(--mut)}.nw.p{border-left:3px solid var(--g);padding-left:8px}.nw.n{border-left:3px solid var(--r);padding-left:8px}
details summary{cursor:pointer;color:var(--mut);font-size:13px;margin-top:6px}
.bar{height:6px;background:var(--bd);border-radius:4px;overflow:hidden;margin:3px 0 7px}.bar i{display:block;height:100%;background:var(--g)}
h2{font-size:15px;margin:16px 0 8px}.empty{color:var(--mut);padding:20px;text-align:center}
input,select{width:100%;padding:9px;border-radius:10px;border:1px solid var(--bd);background:var(--card);color:var(--tx);margin-bottom:8px;font-size:15px}
.ht{border-collapse:collapse;font-size:12px;width:100%}.ht td,.ht th{padding:4px 7px;border-bottom:1px solid var(--bd);white-space:nowrap;text-align:right}.ht td:first-child,.ht th:first-child{text-align:left;position:sticky;left:0;background:var(--card)}
.chip{display:inline-block;font-size:11px;padding:1px 7px;border-radius:10px;background:var(--bg);border:1px solid var(--bd);margin-right:6px}
.badge.b{background:#e0ecff;color:#1d4ed8}@media(prefers-color-scheme:dark){.badge.b{background:#14233f;color:#7aa7ff}}
.disc{color:var(--mut);font-size:11.5px;margin-top:20px}
</style></head><body>
<header><h1>India Moat Screener</h1><div class="sub" id="upd"></div><div id="mood"></div></header>
<nav id="nav"></nav><main id="app"></main>
<script>
const D=__DATA__;
const esc=t=>String(t==null?'':t).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const sg=(x,d=1)=>x==null?'-':(x>0?'+':'')+Number(x).toFixed(d)+'%';
const vcls=v=>v==='Bullish'?'g':v==='Watch'?'a':'r';
const tabs=[['picks','Rule screen'],['best','Best picks / compare'],['mb','Multibagger'],['vol','Volume surge'],['themes','All stocks by area'],['search','Search'],['results','Results'],['accum','Quiet accumulation'],['ow','Order winners'],['orders','Orders'],['big','Big money'],['brokers','Brokers'],['sectors','Sector cycle'],['focus','Focus / Avoid'],['news','News'],['policy','Policy'],['pli','PLI'],['dma','50/200 DMA']];
let tab='picks',q='',th='';
document.getElementById('upd').textContent='Updated '+D.updated+(D.full_at?'  |  fundamentals: '+D.full_at:'')+(D.coverage&&D.coverage.universe?'  |  Coverage: '+D.coverage.loaded+' of '+D.coverage.universe+' listed stocks loaded'+(D.coverage.note?' ('+D.coverage.note+')':''):'');
const M=D.market||{};
if(M.mood){const n=M.nifty,v=M.vix;document.getElementById('mood').innerHTML='<div class="mood '+(M.tone||'a')+'"><b>Market:</b> '+esc(M.mood)+(n?' <br><small>Nifty '+Math.round(n.price)+' ('+sg(n.ret1m)+' 1m)'+(v?' | VIX '+v.price.toFixed(1):'')+'</small>':'')+'</div>';}
function nav(){document.getElementById('nav').innerHTML=tabs.map(t=>'<button class="'+(t[0]===tab?'on':'')+'" onclick="go(\''+t[0]+'\')">'+t[1]+'</button>').join('')}
function go(t){tab=t;nav();draw();scrollTo(0,0)}
function card(s){
 const vc=s.call?ccls(s.call):vcls(s.verdict),p=s.plan||{};
 const why=s.why.slice(0,3).map(x=>'<li>'+esc(x)+'</li>').join(''),whyMore=s.why.slice(3).map(x=>'<li>'+esc(x)+'</li>').join('');
 const risk=s.risks.map(x=>'<li>'+esc(x)+'</li>').join('');
 const nw=s.news.slice(0,3).map(n=>'<a class="nw '+(n.s>0?'p':n.s<0?'n':'')+'" href="'+esc(n.link)+'" target="_blank" rel="noopener">'+esc(n.title)+' <small>'+esc(n.src)+' | '+esc(n.ago)+'</small></a>').join('');
 return '<div class="card"><div class="row"><div><div class="name">'+esc(s.name)+'</div><div class="theme">'+esc(s.theme)+' | Tier '+esc(s.tier)+' ('+s.flags+'/5 rules)</div></div>'+
 '<div><div class="score '+vc+'">'+s.score+'<small>/100</small></div></div></div>'+
 '<div style="margin-top:6px"><span class="badge '+vc+'">'+esc(s.call||s.verdict)+'</span></div>'+rline(s)+mline(s)+mbBlock(s)+ordBlock(s)+
 '<div class="kv"><div><span>Price</span> '+(s.price?'Rs '+s.price.toFixed(1):'-')+' <b class="'+(s.day>0?'g':'r')+'">'+sg(s.day)+'</b></div>'+
 '<div><span>Volume</span> <b class="'+(s.vol_ratio>=1.5?'g':'')+'">'+(s.vol_ratio?s.vol_ratio.toFixed(1)+'x avg':'-')+'</b></div>'+
 '<div><span>Liquidity</span> '+(s.turnover_cr!=null?'Rs '+s.turnover_cr.toFixed(1)+' Cr/day':'-')+'</div>'+
 '<div><span>P/E</span> '+(s.pe?s.pe.toFixed(0):'-')+'</div><div><span>ROCE</span> '+(s.roce?s.roce.toFixed(0)+'%':'-')+'</div><div><span>50/200 gap</span> '+(s.dma_gap!=null?sg(s.dma_gap):'-')+'</div><div><span>Debtor days</span> '+wcv((s.wc||{}).debtor_prev,(s.wc||{}).debtor_days)+'</div><div><span>Inventory days</span> '+wcv((s.wc||{}).inv_prev,(s.wc||{}).inv_days)+'</div>'+(s.adx!=null?'<div><span>ADX</span> <b class="'+(s.adx>=30?'g':'')+'">'+Math.round(s.adx)+'</b></div>':'')+(s.rs_rank!=null?'<div><span>Rel. strength</span> <b class="'+(s.rs_rank>=80?'g':s.rs_rank<30?'r':'')+'">'+s.rs_rank+'/99</b></div>':'')+'</div>'+
 (why?'<div class="sec g">Why bullish</div><ul>'+why+'</ul>':'')+
 (whyMore?'<details><summary>More reasons</summary><ul>'+whyMore+'</ul></details>':'')+
 (risk?'<div class="sec r">Watch out</div><ul>'+risk+'</ul>':'')+
 (p.stop?'<div class="plan"><b>Plan:</b> '+esc(p.entry)+'<br><b>Stop-loss:</b> Rs '+p.stop+(p.risk_pct?' ('+p.risk_pct+'% risk)':'')+(p.t1?' | <b>Targets:</b> Rs '+p.t1+' then Rs '+p.t2:'')+' | <b>Max weight:</b> '+p.maxw+'% of portfolio</div>':'')+
 (nw?'<details><summary>News ('+s.news.length+')</summary>'+nw+'</details>':'')+deep(s)+
 '<div class="links"><a href="'+esc(s.links.screener)+'" target="_blank" rel="noopener">Financials</a><a href="'+esc(s.links.chart)+'" target="_blank" rel="noopener">Chart</a><a href="'+esc(s.links.news)+'" target="_blank" rel="noopener">News</a></div></div>';
}
function picks(){
 const c=D.counts;let h='<div class="stats"><div class="stat"><b class="g">'+c.bullish+'</b><span>Bullish</span></div><div class="stat"><b>'+c.A+'</b><span>All 5 rules</span></div><div class="stat"><b>'+c.B+'</b><span>4 of 5</span></div><div class="stat"><b>'+c.candidates+'</b><span>Scanned</span></div></div>';
 const bull=D.stocks.filter(s=>s.verdict==='Bullish'),watch=D.stocks.filter(s=>s.verdict==='Watch'&&s.tier!=='C').slice(0,8);
 h+='<div class="card"><div class="sec g">Focus sectors now</div><div style="font-size:14px">'+(D.focus_themes.length?esc(D.focus_themes.join(', ')):'None clearly in an upcycle')+'</div><div class="sec r" style="margin-top:6px">Avoid / wait</div><div style="font-size:14px">'+esc(D.avoid_themes.join(', ')||'-')+'</div></div><h2>Bullish now</h2>'+(bull.length?bull.map(card).join(''):'<div class="empty">No stock passes every test right now. That is information too: patience beats forcing a trade.</div>');
 if(watch.length)h+='<h2>Watchlist - wait for a trigger</h2>'+watch.map(card).join('');
 return h;}
function sectors(){return D.sectors.map(c=>{
 return '<div class="card"><div class="row"><div class="name">'+esc(c.theme)+'</div><span class="badge '+c.tone+'">'+esc(c.stance)+'</span></div>'+
 '<div class="'+c.tone+'" style="margin:4px 0 8px;font-weight:600">'+esc(c.phase)+'</div>'+
 '<div class="theme">Government policy support: <b class="'+(c.policy_level==='High'?'g':c.policy_level==='Medium'?'a':'')+'">'+esc(c.policy_level||'-')+'</b></div>'+
 (c.pli&&c.pli.length?'<div class="sec g">Govt incentive (PLI) support</div>'+c.pli.map(p=>'<div style="font-size:13px">'+esc(p.scheme)+' - Rs '+Number(p.outlay_cr).toLocaleString('en-IN')+' Cr</div>').join(''):'')+
 '<div class="theme">Stocks at record quarterly profit: '+c.earn_ath_pct+'%</div><div class="bar"><i style="width:'+c.earn_ath_pct+'%"></i></div>'+
 '<div class="theme">Above 200-DMA: '+c.above200_pct+'%</div><div class="bar"><i style="width:'+c.above200_pct+'%"></i></div>'+
 '<div class="theme">Margins expanding: '+c.opm_up_pct+'%</div><div class="bar"><i style="width:'+c.opm_up_pct+'%"></i></div>'+
 '<div class="kv"><div><span>Median 1m</span> '+sg(c.ret1m)+'</div><div><span>Median 3m</span> '+sg(c.ret3m)+'</div><div><span>Stocks</span> '+c.n+'</div></div>'+
 (c.drivers?'<div class="sec g">Structural drivers</div><div style="font-size:13.5px">'+esc(c.drivers)+'</div>':'')+
 (c.risks?'<div class="sec r">Risks</div><div style="font-size:13.5px">'+esc(c.risks)+'</div>':'')+
 '<div class="theme" style="margin-top:8px">Top ranked: '+esc(c.top.join(', '))+'</div></div>'}).join('')||'<div class="empty">No sector data yet.</div>';}
function focus(){
 const f=D.sectors.filter(c=>c.stance.startsWith('FOCUS')),a=D.sectors.filter(c=>c.stance==='AVOID'||c.stance==='REDUCE / AVOID'),w=D.sectors.filter(c=>c.stance==='WAIT');
 const sc=(c)=>'<div class="card"><div class="row"><b>'+esc(c.theme)+'</b><span class="badge '+c.tone+'">'+esc(c.stance)+'</span></div><div class="theme" style="margin-top:4px">'+esc(c.phase)+' - '+c.earn_ath_pct+'% at record profit, '+c.above200_pct+'% above 200-DMA</div></div>';
 let h='<h2 class="g">Focus on</h2>'+(f.length?f.map(sc).join(''):'<div class="empty">No sector is in a clean upcycle right now.</div>');
 h+='<h2 class="a">Wait</h2>'+(w.length?w.map(sc).join(''):'<div class="empty">-</div>');
 h+='<h2 class="r">Avoid (sectors)</h2>'+(a.length?a.map(sc).join(''):'<div class="empty">-</div>');
 const av=D.stocks.filter(s=>s.tier!=='-'&&s.verdict==='Avoid').slice(0,12);
 h+='<h2 class="r">Stocks with strong numbers but a red flag</h2>'+(av.length?av.map(s=>'<div class="card"><div class="row"><b>'+esc(s.name)+'</b><span class="badge r">Avoid</span></div><ul>'+s.risks.slice(0,3).map(x=>'<li>'+esc(x)+'</li>').join('')+'</ul></div>').join(''):'<div class="empty">-</div>');
 h+='<h2>Simple rules</h2><div class="card"><ul><li>Prefer Tier A/B stocks in sectors marked FOCUS, with volume above 1.5x average.</li><li>Do not chase a stock more than 8% above its 50-DMA - wait for a dip.</li><li>Record profit with falling margins often means the cycle is near its peak.</li><li>Avoid anything below its 200-DMA, thinly traded, or with fresh negative news.</li><li>Use the stop-loss and keep each stock within the suggested max weight.</li></ul></div>';
 return h;}
function newsTab(){return D.news.length?D.news.map(n=>'<div class="card" style="padding:10px"><div class="theme">'+esc(n.name)+' | '+esc(n.ago)+'</div><a class="nw '+(n.s>0?'p':n.s<0?'n':'')+'" style="border-top:0" href="'+esc(n.link)+'" target="_blank" rel="noopener">'+esc(n.title)+' <small>'+esc(n.src)+'</small></a></div>').join(''):'<div class="empty">No recent news on shortlisted stocks.</div>';}
function policyTab(){
 const P=D.policy||{themes:[],newsletters:[]};
 const it=n=>'<a class="nw '+(n.s>0?'p':n.s<0?'n':'')+'" href="'+esc(n.link)+'" target="_blank" rel="noopener">'+esc(n.title)+' <small>'+esc(n.src)+' | '+esc(n.ago)+'</small></a>';
 let h='<div class="card"><div class="theme">Government and policy headlines from the last 30 days (PIB press releases plus news searches), scored for momentum. A scheme announcement is a lead, not proof of company profit.'+(P.at?' Updated '+esc(P.at)+'.':'')+'</div></div>';
 h+=P.themes.map(t=>'<div class="card"><div class="row"><div class="name">'+esc(t.theme)+'</div><span class="badge '+(t.level==='High'?'g':t.level==='Medium'?'a':'r')+'">'+esc(t.level)+' policy focus</span></div>'+(t.items.length?t.items.map(it).join(''):'<div class="theme">No recent policy headlines found.</div>')+'</div>').join('');
 h+='<h2>Newsletters you follow</h2>'+(P.newsletters.length?P.newsletters.map(n=>'<div class="card" style="padding:10px"><div class="theme">'+esc(n.theme||'General')+'</div>'+it(n)+'</div>').join(''):'<div class="empty">No newsletter feeds added yet. Add RSS links to NEWSLETTER_FEEDS in auto_screener.py.</div>');
 return h;}
const wcv=(a,b)=>a==null||b==null?'-':'<b class="'+(b>a*1.03+0.5?'r':'g')+'">'+Math.round(a)+' to '+Math.round(b)+'</b>';
const ul=a=>a&&a.length?'<ul>'+a.map(x=>'<li>'+esc(x)+'</li>').join('')+'</ul>':'';
const lk=(u,t)=>'<a href="'+esc(u)+'" target="_blank" rel="noopener">'+t+'</a>';
function ordBlock(s){const o=s.ord,c=s.concall||{};let h='';
 if(o&&(o.cr||(o.cust||[]).length||(o.files||[]).length)){h+='<div class="sec">Order wins (last 6 months)</div>'+(o.cr?'<div style="font-size:13.5px"><b>Rs '+Math.round(o.cr).toLocaleString('en-IN')+' Cr announced</b>'+(o.pct!=null?' = <b class="'+(o.pct>=25?'g':'')+'">'+Math.round(o.pct)+'% of annual sales</b>':'')+'</div>':'')+((o.cust||[]).length?'<div class="theme">Customers named: '+esc(o.cust.join(', '))+'</div>':'')+(o.files||[]).map(x=>'<a class="nw p" href="'+esc(x.href)+'" target="_blank" rel="noopener"><span class="chip">Exchange filing</span>'+esc(x.text)+'</a>').join('');}
 if((c.certs||[]).length||(c.quals||[]).length||c.top_cust_pct!=null){h+='<div class="sec">Entry barriers and customer ties (concall)</div>'+((c.certs||[]).length?'<div class="theme">Approvals mentioned: '+esc(c.certs.join(', '))+'</div>':'')+ul(c.quals)+(c.top_cust_pct!=null?'<div class="theme '+(c.top_cust_pct>=40?'r':'')+'">Top customers about '+c.top_cust_pct+'% of sales</div>':'');}
 return h?'<details><summary>Orders, approvals, customer ties</summary>'+h+'</details>':'';}
let owCap='SMALL';
function owTab(){const sel=(v,c)=>v==c?' selected':'';return '<div class="card"><div class="theme">Small and micro companies announcing big orders compared with their own size. The key number is the order value as a share of annual sales: a Rs 300 Cr order for a company with Rs 150 Cr of yearly sales is 200 percent. Amounts come from news headlines and exchange filings in the last 6 months, so verify the order and the customer before acting. Customers are named automatically, for example Safran, Bloom Energy, Apple or the Ministry of Defence.</div></div><select onchange="owCap=this.value;renderOw()"><option value="MICRO"'+sel(owCap,'MICRO')+'>Micro caps (under Rs 500 Cr)</option><option value="SMALL"'+sel(owCap,'SMALL')+'>Small and micro (under Rs 5,000 Cr)</option><option value="ALL"'+sel(owCap,'ALL')+'>All sizes</option></select><div id="owbox"></div>';}
function renderOw(){
 const el=document.getElementById('owbox');if(!el)return;
 if(!U){el.innerHTML='<div class="empty">Loading all stocks...</div>';loadUniv().then(renderOw);return;}
 const lim=owCap==='MICRO'?500:owCap==='SMALL'?5000:1e12,okc=u=>u.c==null||u.c<lim;
 const big=U.filter(u=>okc(u)&&u.oc&&u.op!=null).sort((a,b)=>b.op-a.op);
 const named=U.filter(u=>okc(u)&&(u.ou||[]).length&&!(u.oc&&u.op!=null)).sort((a,b)=>b.sc-a.sc);
 const row=u=>'<div class="card" style="padding:10px;cursor:pointer" onclick="openP(\''+esc(u.s)+'\')"><div class="row"><div><b>'+esc(u.n)+'</b><div class="theme">'+esc(u.t||'')+(u.c?' | Rs '+Math.round(u.c).toLocaleString('en-IN')+' Cr':'')+'</div></div><span class="badge '+ccls(u.v)+'">'+esc(u.v)+'</span></div><div class="kv">'+(u.oc?'<div><span>Orders</span> <b class="g">Rs '+Math.round(u.oc).toLocaleString('en-IN')+' Cr</b></div>':'')+(u.op!=null?'<div><span>Share of annual sales</span> <b class="'+(u.op>=25?'g':'')+'">'+Math.round(u.op)+'%</b></div>':'')+'<div><span>Customers</span> '+esc((u.ou||[]).join(', ')||'-')+'</div><div><span>Quarter</span> '+esc(u.rv||'-')+'</div><div><span>Score</span> '+u.sc+'/100</div></div></div>';
 el.innerHTML='<div class="stats" style="grid-template-columns:repeat(2,1fr)"><div class="stat"><b class="g">'+big.length+'</b><span>With order size</span></div><div class="stat"><b>'+named.length+'</b><span>Customer named, no amount</span></div></div>'+
  '<h2 class="g">Orders big compared with company size ('+big.length+')</h2>'+(big.length?big.slice(0,40).map(row).join(''):'<div class="empty">None found yet. This fills in as more stocks are loaded.</div>')+
  '<h2>Customers named, order size not disclosed ('+named.length+')</h2>'+(named.length?named.slice(0,30).map(row).join(''):'<div class="empty">None found yet.</div>');}
function deep(s){
 const c=s.concall||{},cr=s.credit||{},bk=s.broker||[],pl=s.pli||[];let h='';
 if(s.ob_text||(c.order_book&&c.order_book.length))h+='<div class="sec">Order book</div>'+(s.ob_text?'<div style="font-size:13.5px"><b>'+esc(s.ob_text)+'</b></div>':'')+ul(c.order_book);
 if(c.tone){h+='<div class="sec">Concall: management tone '+esc(c.tone)+'</div>';
  if(c.guidance&&c.guidance.length)h+='<div class="theme">Outlook / guidance</div>'+ul(c.guidance);
  if(c.capex&&c.capex.length)h+='<div class="theme">Capacity / capex</div>'+ul(c.capex);
  if(c.risks&&c.risks.length)h+='<div class="theme">Challenges mentioned</div>'+ul(c.risks);
  if(c.link)h+='<div class="theme">'+lk(c.link,'Open transcript')+(c.ppt?' | '+lk(c.ppt,'Presentation'):'')+'</div>';}
 if(cr.rating||cr.link)h+='<div class="sec">Credit rating</div><div style="font-size:13.5px">'+(cr.rating?'<b>'+esc(cr.rating)+'</b> ':'No grade read - ')+esc(cr.agency||'')+(cr.date?' | '+esc(cr.date):'')+(cr.link?' | '+lk(cr.link,'Report'):'')+'</div>';
 if(bk.length)h+='<div class="sec">Brokerage / analyst headlines</div>'+bk.map(n=>'<a class="nw '+(n.view>0?'p':n.view<0?'n':'')+'" href="'+esc(n.link)+'" target="_blank" rel="noopener">'+esc(n.title)+' <small>'+esc(n.src)+' | '+esc(n.ago)+'</small></a>').join('');
 if(pl.length)h+='<div class="sec">PLI scheme link</div>'+pl.map(n=>'<a class="nw p" href="'+esc(n.link)+'" target="_blank" rel="noopener">'+esc(n.title)+(n.amt?' <b>['+esc(n.amt)+']</b>':'')+' <small>'+esc(n.src)+' | '+esc(n.ago)+'</small></a>').join('');
 return h?'<details><summary>Order book, concall, rating, PLI</summary>'+h+'</details>':'';}
function pliTab(){
 const P=D.pli||{schemes:[],news:[],stocks:[]};
 const nw=n=>'<a class="nw p" href="'+esc(n.link)+'" target="_blank" rel="noopener">'+esc(n.title)+(n.amt?' <b>['+esc(n.amt)+']</b>':'')+' <small>'+esc(n.src)+' | '+esc(n.ago)+'</small></a>';
 let h='<div class="card"><div class="theme">PLI and similar schemes: how much the government has set aside and why. Outlays are approximate figures from public announcements, so verify on the ministry site. Company-level amounts come from news headlines below.</div></div>';
 h+='<h2>Latest PLI news: who and how much</h2>'+(P.news.length?'<div class="card">'+P.news.map(nw).join('')+'</div>':'<div class="empty">No PLI headlines found yet.</div>');
 h+='<h2>Your scanned stocks with PLI headlines</h2>'+(P.stocks.length?P.stocks.map(s=>'<div class="card"><div class="row"><b>'+esc(s.name)+'</b><span class="badge '+vcls(s.verdict)+'">'+esc(s.verdict)+'</span></div><div class="theme">'+esc(s.theme)+'</div>'+s.items.map(nw).join('')+'</div>').join(''):'<div class="empty">None of the scanned stocks has a PLI headline.</div>');
 h+='<h2>Schemes</h2>'+P.schemes.map(p=>'<div class="card"><div class="row"><div class="name">'+esc(p.scheme)+'</div><span class="badge g">Rs '+Number(p.outlay_cr).toLocaleString('en-IN')+' Cr</span></div><div class="theme" style="margin-top:4px">'+esc(p.why)+'</div></div>').join('');
 return h;}
function dmaTab(){
 const lab={golden_cross:'Golden cross: 50-DMA just crossed above 200-DMA',converging_up:'50-DMA rising into the 200-DMA',squeeze:'50 and 200 DMA squeezed together (wait for direction)'};
 const z=D.stocks.filter(s=>s.dma_state&&s.dma_state!=='death_cross');
 const good=z.filter(s=>s.tier!=='-'&&(s.wc||{}).wc_ok!==false).slice(0,20),rest=z.filter(s=>!good.includes(s)).slice(0,10);
 const item=s=>'<div class="theme" style="margin:8px 2px 4px"><b class="a">'+esc(lab[s.dma_state])+'</b> | gap '+sg(s.dma_gap)+(s.cross_days?' | crossed '+s.cross_days+' sessions ago':'')+'</div>'+card(s);
 let h='<div class="card"><div class="theme">Stocks where the 50-day and 200-day averages are meeting (within 3%, or just crossed). This is often where a new trend starts. The first list also needs record-type fundamentals and debtor / inventory days that are not rising.</div></div>';
 h+='<h2>Meeting point + strong fundamentals + healthy working capital</h2>'+(good.length?good.map(item).join(''):'<div class="empty">None right now.</div>');
 h+='<h2>Meeting point, but fundamentals or working capital not clean</h2>'+(rest.length?rest.map(item).join(''):'<div class="empty">None.</div>');
 return h;}
const rcol=v=>v==='Excellent'||v==='Good'?'g':v==='Mixed'?'a':'r';
const pc=x=>x==null?'-':(x>0?'+':'')+Math.round(x)+'%';
function rline(s){const r=s.results;if(!r)return '';return '<div class="theme" style="margin-top:6px">Quarter '+esc(r.period)+': <b class="'+rcol(r.verdict)+'">'+esc(r.verdict)+'</b> | Sales '+pc(r.sales_yoy)+' YoY, '+pc(r.sales_qoq)+' QoQ | Profit '+pc(r.profit_yoy)+' YoY, '+pc(r.profit_qoq)+' QoQ</div>';}
function mline(s){const m=s.margin;if(!m)return '';const c=s.cogs;return '<div class="theme" style="margin-top:4px">Cost quality <b class="'+rcol(m.verdict)+'">'+esc(m.verdict)+'</b> | '+(c&&c.now!=null&&c.yr!=null?'COGS '+Math.round(c.yr)+'% to '+Math.round(c.now)+'% of sales':(m.cost_now!=null&&m.cost_yr!=null?'costs '+Math.round(m.cost_yr)+'% to '+Math.round(m.cost_now)+'% of sales':''))+(m.opm!=null&&m.opm_yr!=null?' | OPM '+Math.round(m.opm_yr)+'% to '+Math.round(m.opm)+'%':'')+(m.op_yoy!=null?' | Operating profit '+pc(m.op_yoy)+' YoY':'')+'</div>';}
function accumTab(){
 const R=D.accum||[];
 return '<div class="card"><div class="theme">Results are good (Excellent or Good quarter) but the price has not run over the last 2 days, 1 week or 1 month, while volume is 1.5x or more its 20-day average. That pattern can mean big institutions are buying quietly before the move. Tap a stock for details.</div></div>'+(R.length?R.map(x=>'<div class="card" style="padding:10px" onclick="openP(\''+esc(x.sym)+'\')"><div class="row"><div><b>'+esc(x.name)+'</b><div class="theme">Quarter '+esc(x.rv)+' | flat over '+esc(x.flat.join(', '))+' | volume '+x.vol.toFixed(1)+'x avg | ADX '+(x.adx==null?'-':Math.round(x.adx))+' | RS '+(x.rs==null?'-':x.rs)+'/99</div></div><span class="badge '+ccls(x.call)+'">'+esc(x.call)+'</span></div></div>').join(''):'<div class="empty">No stock matches right now.</div>');}
function rrow(s){const r=s.results;return '<div class="card" style="padding:10px"><div class="row"><b>'+esc(s.name)+'</b><span class="badge '+rcol(r.verdict)+'">'+esc(r.verdict)+'</span></div><div class="theme">'+esc(r.period)+' | '+esc(s.theme)+'</div><div class="kv"><div><span>Sales YoY</span> <b>'+pc(r.sales_yoy)+'</b></div><div><span>Sales QoQ</span> '+pc(r.sales_qoq)+'</div><div><span>Profit YoY</span> <b>'+pc(r.profit_yoy)+'</b></div><div><span>Profit QoQ</span> '+pc(r.profit_qoq)+'</div><div><span>OPM</span> '+(r.opm!=null?r.opm+'%':'-')+(r.opm_yoy!=null?' (year ago '+r.opm_yoy+'%)':'')+'</div></div>'+(r.accelerating?'<div class="theme g">Profit growth accelerating over the last 3 quarters ('+(r.yoy_trend||[]).map(pc).join(' > ')+')</div>':'')+'</div>';}
function resultsTab(){
 const r=D.stocks.filter(s=>s.results&&s.tier!=='-');
 let h='<div class="card"><div class="theme">How each shortlisted company did in its latest quarter against the same quarter last year (YoY) and the previous quarter (QoQ). Excellent means strong sales and profit growth with margins up. QoQ can mislead for seasonal businesses, so lean on YoY.</div></div>';
 ['Excellent','Good','Mixed','Weak','Loss-making'].forEach(v=>{const x=r.filter(s=>s.results.verdict===v).sort((a,b)=>(b.results.profit_yoy==null?-999:b.results.profit_yoy)-(a.results.profit_yoy==null?-999:a.results.profit_yoy));
  if(x.length)h+='<h2 class="'+rcol(v)+'">'+v+' ('+x.length+')</h2>'+x.slice(0,25).map(rrow).join('');});
 return h;}
let U=null,sq='',sel='',thSel='',thFilter='ALL',thShow=60;
const ccls=v=>v==='BUY'?'g':v==='HOLD'?'b':v==='WAIT'?'a':'r';
const mc=x=>x==null?'-':Math.round(x).toLocaleString('en-IN');
const chips=a=>(a||[]).map(x=>'<span class="chip">'+esc(x)+'</span>').join('');
function loadUniv(){if(U)return Promise.resolve(U);if(D.univ){U=D.univ;return Promise.resolve(U);}return fetch('data/summary.json').then(r=>r.json()).then(j=>{U=j;return U}).catch(()=>{U=[];return U});}
function getStock(sym){const f=D.stocks.find(x=>x.sym===sym);if(f)return Promise.resolve(f);if(D.detail&&D.detail[sym])return Promise.resolve(D.detail[sym]);return fetch('data/d/'+sym.replace(/[^A-Za-z0-9_.-]/g,'_')+'.json').then(r=>r.json()).catch(()=>null);}
function openP(sym){tab='search';sel=sym;nav();draw();scrollTo(0,0);}
const urow=u=>'<div class="card" style="padding:10px" onclick="openP(\''+esc(u.s)+'\')"><div class="row"><div><b>'+esc(u.n)+'</b><div class="theme">Rs '+mc(u.c)+' Cr'+(u.tr!=='-'?' | Tier '+esc(u.tr):'')+(u.rv?' | Qtr '+esc(u.rv):'')+(u.p?' | Rs '+Math.round(u.p)+' '+sg(u.d):'')+'</div></div><div style="text-align:right"><span class="badge '+ccls(u.v)+'">'+esc(u.v)+'</span><div class="theme">'+u.sc+'/100</div></div></div>'+(u.tg&&u.tg.length?'<div class="theme">Targeting: '+esc(u.tg.join(', '))+'</div>':'')+'</div>';
function themesTab(){
 const ar=D.areas||[];
 return '<div class="card"><div class="theme">Every scanned company grouped by area, whether or not it passes your rules. Pick an area to see all its stocks with the BUY / WAIT / AVOID call, the rule tier (record sales and profit plus profit breakout) and what each company says it is targeting.</div></div><select id="thsel" onchange="thSel=this.value;thShow=60;renderThemes()"><option value="">Choose an area...</option>'+ar.map(a=>'<option value="'+esc(a.area)+'"'+(a.area===thSel?' selected':'')+'>'+esc(a.area)+' ('+a.n+')</option>').join('')+'</select><div id="thres"><div class="empty">Loading all stocks...</div></div>';}
let mbShow=30;
function mbBlock(s){const m=s.mb;if(!m||!m.gates)return '';const ins=s.insider||[];return '<div class="card" style="margin:8px 0 0;padding:10px;background:var(--bg)"><div class="sec">Multibagger check: <b class="'+(m.call==='MULTIBAGGER BUY'?'g':m.call?'a':'r')+'">'+esc(m.call||'Not yet')+'</b> ('+m.score+'/100)</div>'+m.gates.map(g=>'<div style="font-size:13px" class="'+(g.ok===true?'g':g.ok===false?'r':'')+'">'+(g.ok===true?'Yes':g.ok===false?'No':'?')+' - '+esc(g.t)+'</div>').join('')+(ins.length?'<div class="theme" style="margin-top:6px">Insider / promoter headlines</div>'+ins.map(n=>'<a class="nw '+(n.kind==='Insider buying'?'p':'n')+'" href="'+esc(n.link)+'" target="_blank" rel="noopener"><span class="chip">'+esc(n.kind)+'</span>'+esc(n.title)+' <small>'+esc(n.ago)+'</small></a>').join(''):'')+'</div>';}
function mbTab(){return '<div class="card"><div class="theme">Early multibagger hunt. A stock gets MULTIBAGGER BUY only when the company is clearly growing, promoters are raising their stake or insiders are buying, nobody is selling or pledging, the price is in an uptrend, the valuation is not stretched and the company is still small enough to grow several times. STRONG WATCH means most of this is true but one proof is missing. Insider buying comes from news about promoter and director purchases. Promoter stake comes from the quarterly shareholding table.</div></div><div id="mbbox"></div>';}
function renderMb(){
 const el=document.getElementById('mbbox');if(!el)return;
 if(!U){el.innerHTML='<div class="empty">Loading all stocks...</div>';loadUniv().then(renderMb);return;}
 const all=U.filter(u=>u.mb!=null).sort((a,b)=>b.mb-a.mb);
 const buy=all.filter(u=>u.mbc==='MULTIBAGGER BUY'),watch=all.filter(u=>u.mbc==='STRONG WATCH');
 const row=(u,i)=>'<div class="card" style="padding:10px;cursor:pointer" onclick="openP(\''+esc(u.s)+'\')"><div class="row"><div><b>'+(i+1)+'. '+esc(u.n)+'</b><div class="theme">'+esc(u.t||'')+(u.c?' | Rs '+Math.round(u.c).toLocaleString('en-IN')+' Cr':'')+'</div></div><div style="text-align:right"><span class="badge '+(u.mbc==='MULTIBAGGER BUY'?'g':u.mbc?'a':'r')+'">'+esc(u.mbc||'Not yet')+'</span><div class="score" style="font-size:18px">'+u.mb+'</div></div></div><div class="kv"><div><span>Profit YoY</span> <b>'+pc(u.py)+'</b></div><div><span>Sales YoY</span> '+pc(u.sy)+'</div><div><span>3y profit growth</span> '+(u.pg==null?'-':Math.round(u.pg)+'%/yr')+'</div><div><span>Promoter</span> '+(u.ph==null?'-':u.ph.toFixed(1)+'%')+(u.pu==null?'':' <b class="'+(u.pu>=0.3?'g':u.pu<=-1?'r':'')+'">('+(u.pu>0?'+':'')+u.pu.toFixed(1)+' pts/yr)</b>')+'</div><div><span>Insider buying</span> '+(u.ib?'<b class="g">Yes</b>':'No')+'</div><div><span>Overall call</span> <b class="'+ccls(u.v)+'">'+esc(u.v)+'</b></div></div></div>';
 let h='<div class="stats" style="grid-template-columns:repeat(3,1fr)"><div class="stat"><b class="g">'+buy.length+'</b><span>Multibagger BUY</span></div><div class="stat"><b class="a">'+watch.length+'</b><span>Strong watch</span></div><div class="stat"><b>'+U.length+'</b><span>Stocks loaded</span></div></div>';
 h+='<h2 class="g">Multibagger BUY ('+buy.length+')</h2>'+(buy.length?buy.slice(0,mbShow).map(row).join(''):'<div class="empty">No stock passes every test right now.</div>');
 h+='<h2 class="a">Strong watch ('+watch.length+')</h2>'+(watch.length?watch.slice(0,mbShow).map(row).join(''):'<div class="empty">None.</div>');
 if(!buy.length&&!watch.length)h+='<h2>Closest to qualifying</h2>'+all.slice(0,15).map(row).join('');
 el.innerHTML=h;}
let volMin=1.5,volF='GOOD';
function volTab(){const sel=(v,c)=>v==c?' selected':'';return '<div class="card"><div class="theme">Stocks trading on much higher volume than usual: today\'s volume compared with the 20-day average. 1.5x or more means big buyers or sellers are active. High volume is a buy clue only when the price is rising and the results are good, so the default filter shows exactly that. High volume on a falling price is selling. During market hours the volume so far is partial, so the multiple looks lower than it will at the close.</div></div><select onchange="volMin=+this.value;renderVol()"><option value="1.5"'+sel(volMin,1.5)+'>1.5x or more</option><option value="2"'+sel(volMin,2)+'>2x or more</option><option value="3"'+sel(volMin,3)+'>3x or more</option></select><select onchange="volF=this.value;renderVol()"><option value="GOOD"'+sel(volF,'GOOD')+'>Price rising + good results</option><option value="UP"'+sel(volF,'UP')+'>Price rising</option><option value="BUY"'+sel(volF,'BUY')+'>BUY / HOLD calls only</option><option value="ALL"'+sel(volF,'ALL')+'>All (including falling)</option></select><div id="volbox"></div>';}
function renderVol(){
 const el=document.getElementById('volbox');if(!el)return;
 if(!U){el.innerHTML='<div class="empty">Loading all stocks...</div>';loadUniv().then(renderVol);return;}
 let r=U.filter(u=>u.vr!=null&&u.vr>=volMin);
 if(volF==='UP')r=r.filter(u=>(u.d||0)>0);
 else if(volF==='GOOD')r=r.filter(u=>(u.d||0)>0&&(u.rv==='Excellent'||u.rv==='Good'));
 else if(volF==='BUY')r=r.filter(u=>u.v==='BUY'||u.v==='HOLD');
 r.sort((a,b)=>b.vr-a.vr);
 const row=(u,i)=>'<div class="card" style="padding:10px;cursor:pointer" onclick="openP(\''+esc(u.s)+'\')"><div class="row"><div><b>'+(i+1)+'. '+esc(u.n)+'</b><div class="theme">'+esc(u.t||'')+(u.c?' | Rs '+Math.round(u.c).toLocaleString('en-IN')+' Cr':'')+'</div></div><div style="text-align:right"><span class="badge '+ccls(u.v)+'">'+esc(u.v)+'</span><div class="theme">score '+u.sc+'</div></div></div><div class="kv"><div><span>Volume</span> <b class="g">'+u.vr.toFixed(1)+'x average</b></div><div><span>Price today</span> <b class="'+((u.d||0)>0?'g':'r')+'">'+pc(u.d)+'</b></div><div><span>Quarter</span> <b class="'+rcol(u.rv)+'">'+esc(u.rv||'-')+'</b></div><div><span>Profit YoY</span> '+pc(u.py)+'</div><div><span>Multibagger</span> '+esc(u.mbc||'-')+'</div></div></div>';
 el.innerHTML='<div class="stats" style="grid-template-columns:repeat(2,1fr)"><div class="stat"><b>'+r.length+'</b><span>Stocks match</span></div><div class="stat"><b>'+U.filter(u=>u.vr!=null&&u.vr>=1.5).length+'</b><span>Above 1.5x volume (all)</span></div></div>'+(r.length?r.slice(0,40).map(row).join(''):'<div class="empty">No stock matches these filters right now. Loosen the filters above.</div>');}
let cmp=[],bestFilter='BUYHOLD',bestShow=30;
function bestTab(){return '<div class="card"><div class="theme">Every loaded stock ranked best to worst by the investment score: your sales and profit rules, quarter results, cost quality, ADX trend strength, relative strength, volume, news and institutional buying. Tick up to 3 stocks and tap Compare to see them side by side.</div></div><div id="bestbox"></div>';}
function renderBest(){
 const el=document.getElementById('bestbox');if(!el)return;
 if(!U){el.innerHTML='<div class="empty">Loading all stocks...</div>';loadUniv().then(renderBest);return;}
 const f=bestFilter,tn={A:'5/5',B:'4/5',C:'3/5'};
 const rows=U.filter(u=>f==='ALL'||(f==='BUYHOLD'?(u.v==='BUY'||u.v==='HOLD'):f==='RULES'?u.tr!=='-':u.v===f)).sort((a,b)=>b.sc-a.sc);
 let h='<div class="links" style="flex-wrap:wrap;margin:0 0 8px">'+[['BUYHOLD','Buy + Hold'],['BUY','BUY'],['HOLD','HOLD'],['WAIT','WAIT'],['AVOID','AVOID'],['RULES','Pass rules'],['ALL','All']].map(x=>'<a href="#" style="'+(x[0]===f?'background:var(--tx);color:var(--bg)':'')+'" onclick="bestFilter=\''+x[0]+'\';bestShow=30;renderBest();return false">'+x[1]+'</a>').join('')+'</div>';
 h+='<div class="theme" style="margin:0 2px 8px">'+rows.length+' of '+U.length+' stocks, best score first.'+(cmp.length?' Selected for compare: '+cmp.length+' of 3.':'')+'</div>';
 if(cmp.length>=2)h+='<div class="links" style="margin:0 0 8px"><a href="#" style="background:var(--tx);color:var(--bg)" onclick="doCompare();return false">Compare '+cmp.length+' stocks</a><a href="#" onclick="cmp=[];renderBest();return false">Clear</a></div>';
 h+=rows.slice(0,bestShow).map((u,i)=>'<div class="card" style="padding:10px"><div class="row"><div style="cursor:pointer" onclick="openP(\''+esc(u.s)+'\')"><b>'+(i+1)+'. '+esc(u.n)+'</b><div class="theme">'+esc(u.t||'')+(u.c?' | Rs '+Math.round(u.c).toLocaleString('en-IN')+' Cr':'')+'</div></div><div style="text-align:right"><span class="badge '+ccls(u.v)+'">'+esc(u.v)+'</span><div class="score '+ccls(u.v)+'" style="font-size:18px">'+u.sc+'</div></div></div><div class="kv"><div><span>Quarter</span> <b class="'+rcol(u.rv)+'">'+esc(u.rv||'-')+'</b></div><div><span>Sales YoY</span> '+pc(u.sy)+'</div><div><span>Profit YoY</span> '+pc(u.py)+'</div><div><span>Costs</span> '+esc(u.mg||'-')+'</div><div><span>ADX</span> '+(u.ad==null?'-':Math.round(u.ad))+'</div><div><span>RS</span> '+(u.rs==null?'-':u.rs)+'/99</div><div><span>Rules</span> '+(tn[u.tr]||'under 3/5')+'</div></div><label style="font-size:13px"><input type="checkbox" style="width:auto;margin:0 6px 0 0" '+(cmp.includes(u.s)?'checked':'')+' onchange="togCmp(\''+esc(u.s)+'\',this.checked)">Compare</label></div>').join('');
 if(rows.length>bestShow)h+='<div class="links"><a href="#" onclick="bestShow+=30;renderBest();return false">Show more</a></div>';
 el.innerHTML=h||'<div class="empty">Nothing here yet.</div>';}
function togCmp(s,on){if(on){if(!cmp.includes(s)){if(cmp.length>=3){alert('Pick up to 3 stocks');renderBest();return;}cmp.push(s);}}else cmp=cmp.filter(x=>x!==s);renderBest();}
function doCompare(){
 const el=document.getElementById('bestbox');el.innerHTML='<div class="empty">Loading...</div>';
 Promise.all(cmp.map(getStock)).then(L=>{
  const row=(lab,fn)=>'<tr><td>'+lab+'</td>'+L.map(s=>{const v=fn(s);return '<td>'+(v==null?'-':v)+'</td>'}).join('')+'</tr>';
  const rs=s=>s.results||{},mg=s=>s.margin||{},pl=s=>s.plan||{};
  el.innerHTML='<div class="links" style="margin:0 0 8px"><a href="#" onclick="renderBest();return false">Back to ranking</a></div><div class="card"><div style="overflow-x:auto"><table class="ht"><tr><th></th>'+L.map(s=>'<th>'+esc(s.name)+'</th>').join('')+'</tr>'+
  row('Call',s=>'<b class="'+ccls(s.call)+'">'+esc(s.call)+'</b>')+row('Score /100',s=>s.score)+row('Rules passed',s=>s.flags+'/5')+
  row('Latest quarter',s=>esc(rs(s).verdict||''))+row('Sales YoY',s=>pc(rs(s).sales_yoy))+row('Profit YoY',s=>pc(rs(s).profit_yoy))+
  row('Cost quality',s=>esc(mg(s).verdict||''))+row('Operating profit YoY',s=>pc(mg(s).op_yoy))+
  row('ADX',s=>s.adx==null?null:Math.round(s.adx))+row('Rel. strength',s=>s.rs_rank==null?null:s.rs_rank+'/99')+
  row('Volume vs 20-day avg',s=>s.vol_ratio==null?null:s.vol_ratio.toFixed(1)+'x')+row('P/E',s=>s.pe==null?null:Math.round(s.pe))+row('ROCE %',s=>s.roce==null?null:Math.round(s.roce))+
  row('Debtor days',s=>s.wc&&s.wc.debtor_days!=null?Math.round(s.wc.debtor_days):null)+row('Inventory days',s=>s.wc&&s.wc.inv_days!=null?Math.round(s.wc.inv_days):null)+
  row('Order book',s=>s.ob_text?esc(s.ob_text):null)+row('Concall tone',s=>(s.concall||{}).tone?esc(s.concall.tone):null)+row('Credit rating',s=>(s.credit||{}).rating?esc(s.credit.rating):null)+
  row('Institutions',s=>(s.holding||{}).inst?esc(s.holding.inst):null)+row('Price',s=>s.price?'Rs '+s.price.toFixed(1):null)+row('Stop-loss',s=>pl(s).stop?'Rs '+pl(s).stop:null)+row('Targets',s=>pl(s).t1?'Rs '+pl(s).t1+' / '+pl(s).t2:null)+
  '</table></div></div><div class="theme">The stock with the higher score and more green flags is the stronger candidate. Always read the risks on each stock page before deciding.</div>';});}
function renderThemes(){
 const el=document.getElementById('thres');if(!el)return;
 if(!U){loadUniv().then(renderThemes);return;}
 if(!thSel){el.innerHTML='<div class="empty">Choose an area above.</div>';return;}
 const rank={BUY:0,WAIT:1,AVOID:2};
 const all_=U.filter(u=>(u.a||[]).includes(thSel)||u.t===thSel),fl=thFilter;
 const rows=all_.filter(u=>fl==='ALL'||(fl==='RULES'?u.tr!=='-':u.v===fl)).sort((a,b)=>(rank[a.v]-rank[b.v])||(b.sc-a.sc));
 const cy=D.sectors.find(c=>c.theme===thSel);
 let h=cy?'<div class="card"><div class="row"><b>Sector cycle</b><span class="badge '+cy.tone+'">'+esc(cy.stance)+'</span></div><div class="'+cy.tone+'" style="font-weight:600">'+esc(cy.phase)+'</div><div class="theme">Govt policy focus: '+esc(cy.policy_level||'-')+' | '+cy.earn_ath_pct+'% at record quarterly profit | '+cy.above200_pct+'% above 200-DMA</div>'+(cy.drivers?'<div class="theme">'+esc(cy.drivers)+'</div>':'')+'</div>':'';
 h+='<div class="links" style="flex-wrap:wrap;margin:0 0 8px">'+['ALL','BUY','WAIT','AVOID','RULES'].map(x=>'<a href="#" style="'+(x===fl?'background:var(--tx);color:var(--bg)':'')+'" onclick="thFilter=\''+x+'\';thShow=60;renderThemes();return false">'+(x==='RULES'?'Pass rules':x)+'</a>').join('')+'</div><div class="theme" style="margin:0 2px 8px">'+rows.length+' of '+all_.length+' stocks</div>';
 h+=rows.slice(0,thShow).map(urow).join('')||'<div class="empty">No stocks.</div>';
 if(rows.length>thShow)h+='<div class="links"><a href="#" onclick="thShow+=60;renderThemes();return false">Show more</a></div>';
 el.innerHTML=h;}
function searchTab(){return '<div class="card"><div class="theme">Search any scanned company by name or symbol: results, ownership, orders, concall, brokers and more. Companies below the market-cap cut-off are not scanned. Add one with the watch box when you run the workflow.</div></div><input id="sq" placeholder="Type a company name or symbol" value="'+esc(sq)+'" oninput="sIn(this.value)"><div id="sres"></div>';}
function sIn(v){sq=v;sel='';sres();}
function sres(){
 const el=document.getElementById('sres');if(!el)return;
 if(sel){el.innerHTML='<div class="empty">Loading...</div>';getStock(sel).then(s=>{const e2=document.getElementById('sres');if(!e2||!sel)return;e2.innerHTML='<div class="links" style="margin:0 0 8px"><a href="#" onclick="sel=\'\';sres();return false">Back to results</a></div>'+profile(s)});return;}
 const t=sq.trim().toLowerCase();
 if(t.length<2){el.innerHTML='<div class="empty">Type at least 2 letters.</div>';return;}
 if(!U){loadUniv().then(sres);return;}
 const r=U.filter(x=>x.n.toLowerCase().includes(t)||x.s.toLowerCase().includes(t)).slice(0,20);
 el.innerHTML=r.length?r.map(urow).join(''):'<div class="empty">Not in the scanned list. Add its symbol in the Run workflow watch box, or check '+lk('https://www.google.com/search?q='+encodeURIComponent(sq+' shareholding mutual fund bulk deal'),'Google')+'.</div>';}
function htable(h){
 if(!h||!h.rows)return '<div class="theme">Shareholding data not available.</div>';
 const nm={promoters:'Promoters',fiis:'FIIs (foreign)',diis:'DIIs (mutual funds, insurers)',government:'Government',public:'Public'};
 let t='<div style="overflow-x:auto"><table class="ht"><tr><th></th>'+h.labels.map(l=>'<th>'+esc(l)+'</th>').join('')+'</tr>';
 Object.keys(h.rows).forEach(k=>{const v=h.rows[k];t+='<tr><td>'+nm[k]+' %</td>'+v.map((x,i)=>{const p=i>0?v[i-1]:null;const c=(x==null||p==null)?'':x>p+0.05?'g':x<p-0.05?'r':'';return '<td class="'+c+'">'+(x==null?'-':x.toFixed(1))+'</td>'}).join('')+'</tr>';});
 if(h.holders&&h.holders.length)t+='<tr><td>Shareholders</td>'+h.holders.map(x=>'<td>'+(x==null?'-':Math.round(x).toLocaleString('en-IN'))+'</td>').join('')+'</tr>';
 return t+'</table></div>';}
const bchips=n=>(n.who&&n.who.length?'<span class="chip">'+esc(n.who.join(', '))+'</span>':'')+(n.call?'<span class="chip">'+esc(n.call)+'</span>':'')+(n.target?'<span class="chip">Target Rs '+mc(n.target)+'</span>':'');
function profile(s){
 if(!s)return '<div class="empty">Could not load this stock. It may not have been scanned yet.</div>';
 const h=s.holding,r=s.results,inv=s.invest||[],fl=s.filings||[],k=s.concall||{},cu=s.customers||[],od=s.orders||[],bk=s.broker||[];
 let o=(s.tier==='-'?'<div class="card" style="padding:10px"><div class="theme">This company does not pass your rules ('+s.flags+' of 5), so it is shown for research.</div></div>':'')+card(s);
 o+='<div class="card"><div class="sec">What it does</div><div style="font-size:13.5px">'+esc(s.about||'Business description not available.')+'</div><div style="margin-top:6px">'+chips((s.areas||[]).concat(s.sector?[s.sector]:[]))+'</div></div>';
 o+='<div class="card"><div class="sec">Concall: what management says and where it is targeting</div>';
 if(k.tone){o+='<div class="theme">Tone: <b>'+esc(k.tone)+'</b>'+(k.link?' | '+lk(k.link,'Transcript'):'')+'</div>'+(k.targets&&k.targets.length?'<div style="margin:4px 0"><span class="theme">Areas discussed most: </span>'+chips(k.targets.map(x=>x.area))+'</div>':'')+(k.focus&&k.focus.length?'<div class="theme">Growth plans / focus</div>'+ul(k.focus):'')+(k.guidance&&k.guidance.length?'<div class="theme">Outlook</div>'+ul(k.guidance):'')+(k.capex&&k.capex.length?'<div class="theme">Capacity / capex</div>'+ul(k.capex):'')+(k.risks&&k.risks.length?'<div class="theme">Challenges</div>'+ul(k.risks):'');}
 else o+='<div class="theme">No concall transcript read yet. It may not exist, or it has not been processed yet.</div>';
 o+='</div>';
 o+='<div class="card"><div class="sec">Who gives it orders / partners</div>'+(cu.length?cu.map(c=>'<div style="margin:6px 0"><b>'+esc(c.name)+'</b> <span class="chip">'+esc(c.region||'')+'</span><span class="chip">'+esc(c.src)+'</span><div class="theme">'+esc(c.ctx)+'</div></div>').join(''):'<div class="theme">No named customers or partners found.</div>')+(od.length?'<div class="theme" style="margin-top:6px">Order and partnership headlines</div>'+od.map(n=>'<a class="nw p" href="'+esc(n.link)+'" target="_blank" rel="noopener">'+esc(n.title)+' <small>'+esc(n.src)+' | '+esc(n.ago)+'</small></a>').join(''):'')+'<div class="theme" style="margin-top:6px">Names are picked up automatically from the concall and news. Check the source before relying on them.</div></div>';
 o+='<div class="card"><div class="sec">What brokerages say (Kotak, ICICI Securities, Motilal and others)</div>'+(bk.length?bk.map(n=>'<a class="nw '+(n.view>0?'p':n.view<0?'n':'')+'" href="'+esc(n.link)+'" target="_blank" rel="noopener">'+bchips(n)+esc(n.title)+' <small>'+esc(n.src)+' | '+esc(n.ago)+'</small></a>').join(''):'<div class="theme">No brokerage headlines found in the last 2 months.</div>')+'</div>';
 o+='<div class="card"><div class="sec">Quarterly results</div>';
 if(r&&r.hist){const cell=x=>'<td>'+(x==null?'-':Math.round(x).toLocaleString('en-IN'))+'</td>';
  o+='<div style="overflow-x:auto"><table class="ht"><tr><th></th>'+r.hist.map(x=>'<th>'+esc(x.q)+'</th>').join('')+'</tr><tr><td>Sales (Cr)</td>'+r.hist.map(x=>cell(x.s)).join('')+'</tr><tr><td>Net profit (Cr)</td>'+r.hist.map(x=>cell(x.p)).join('')+'</tr></table></div><div class="theme" style="margin-top:6px">Latest vs year ago: sales '+pc(r.sales_yoy)+', profit '+pc(r.profit_yoy)+' | vs previous quarter: sales '+pc(r.sales_qoq)+', profit '+pc(r.profit_qoq)+'</div>';
 }else o+='<div class="theme">Not available.</div>';
 o+='</div><div class="card"><div class="sec">Who owns it (last 8 quarters)</div>'+(h?'<div style="margin:4px 0"><span class="badge '+(h.inst==='Accumulating'?'g':h.inst==='Reducing'?'r':'a')+'">Institutions: '+esc(h.inst)+'</span></div>':'')+htable(h)+(h&&h.signals.length?'<ul>'+h.signals.map(x=>'<li class="'+(x.tone==='g'?'g':x.tone==='r'?'r':'a')+'">'+esc(x.t)+'</li>').join('')+'</ul>':'')+'<div class="theme">Screener shows foreign funds (FIIs) and domestic institutions (DIIs, which include mutual funds and insurers) but not individual fund names. For fund-wise holdings, search '+lk('https://www.google.com/search?q='+encodeURIComponent(s.name+' mutual fund holdings'),'Google')+'.</div></div>';
 o+='<div class="card"><div class="sec">Big investors, bulk/block deals, preferential issues (news)</div>'+(inv.length?inv.map(n=>'<a class="nw '+(n.kind==='Big investor'?'p':'')+'" href="'+esc(n.link)+'" target="_blank" rel="noopener"><span class="chip">'+esc(n.kind)+'</span>'+esc(n.title)+' <small>'+esc(n.src)+' | '+esc(n.ago)+'</small></a>').join(''):'<div class="theme">No such headlines found in the last 3 to 6 months.</div>')+'</div>';
 o+='<div class="card"><div class="sec">Company filings: preferential issues, warrants, allotments</div>'+(fl.length?fl.map(x=>'<a class="nw" href="'+esc(x.href)+'" target="_blank" rel="noopener">'+esc(x.text)+'</a>').join(''):'<div class="theme">None found on the recent announcements list.</div>')+'<div class="theme" style="margin-top:6px">A preferential issue to a respected investor at a premium is a positive sign. One to promoters at a discount, or heavy dilution, is not. Always read the filing.</div></div>';
 return o;}
function ordersTab(){
 const O=D.orders||[];
 return '<div class="card"><div class="theme">Which customers are giving orders to, or partnering with, Indian companies. Found automatically in concalls and news. Tap a company for its profile, and verify in the source before acting.</div></div>'+(O.length?O.map(e=>'<div class="card"><div class="row"><div class="name">'+esc(e.name)+'</div><span class="chip">'+esc(e.region||'')+'</span></div>'+e.cos.map(c=>'<div style="margin:8px 0;cursor:pointer" onclick="openP(\''+esc(c.sym)+'\')"><b>'+esc(c.name)+'</b> <span class="badge '+ccls(c.call)+'">'+esc(c.call)+'</span><div class="theme">'+esc(c.ctx)+' ('+esc(c.src)+')</div></div>').join('')+'</div>').join(''):'<div class="empty">No customer mentions found yet. They appear as concalls and news are processed over the first few runs.</div>');}
function bigTab(){
 const B=D.big||{acc:[],deals:[],prefs:[]};
 const nw=n=>'<a class="nw p" href="'+esc(n.link)+'" target="_blank" rel="noopener"><b>'+esc(n.name)+'</b>: '+esc(n.title)+' <small>'+esc(n.src)+(n.ago?' | '+esc(n.ago):'')+'</small></a>';
 let h='<div class="card"><div class="theme">Where big money is going: institutions raising their holding quarter by quarter, block or bulk deal and stake headlines, and preferential issues or fund raises. DII holding includes mutual funds and insurers.</div></div>';
 h+='<h2 class="g">Institutions accumulating</h2>'+(B.acc.length?B.acc.map(x=>'<div class="card" style="padding:10px;cursor:pointer" onclick="openP(\''+esc(x.sym)+'\')"><div class="row"><b>'+esc(x.name)+'</b><span class="badge '+ccls(x.call)+'">'+esc(x.call)+'</span></div>'+ul(x.signals)+'</div>').join(''):'<div class="empty">None found.</div>');
 h+='<h2>Block / bulk deals and stake news</h2>'+(B.deals.length?'<div class="card">'+B.deals.map(nw).join('')+'</div>':'<div class="empty">None found.</div>');
 h+='<h2 class="a">Preferential issues and fund raises</h2>'+(B.prefs.length?'<div class="card">'+B.prefs.map(nw).join('')+'</div><div class="theme">A preferential issue to a respected investor at a premium is a good sign. One to promoters at a discount, or heavy dilution, is not. Read the filing.</div>':'<div class="empty">None found.</div>');
 return h;}
function brokersTab(){
 const R=D.brokers||[];const H={};
 R.forEach(n=>{(n.who&&n.who.length?n.who:['Other / unnamed']).forEach(w=>{(H[w]=H[w]||[]).push(n);});});
 const hs=Object.keys(H).sort((a,b)=>H[b].length-H[a].length);
 let h='<div class="card"><div class="theme">Where the big brokerages are building positions or turning positive, grouped by house (Kotak, ICICI Securities, Motilal Oswal, Axis, Nuvama, Jefferies and others). Headlines only, so open the article for the full note.</div></div>';
 h+=hs.map(w=>'<h2>'+esc(w)+' ('+H[w].length+')</h2>'+H[w].slice(0,12).map(n=>'<div class="card" style="padding:10px"><div class="row"><b style="cursor:pointer" onclick="openP(\''+esc(n.sym)+'\')">'+esc(n.name)+'</b><span class="badge '+ccls(n.scall)+'">'+esc(n.scall||'')+'</span></div><a class="nw '+(n.view>0?'p':n.view<0?'n':'')+'" style="border-top:0" href="'+esc(n.link)+'" target="_blank" rel="noopener">'+bchips(n)+esc(n.title)+' <small>'+esc(n.src)+' | '+esc(n.ago)+'</small></a></div>').join('')).join('');
 return R.length?h:'<div class="empty">No brokerage headlines found yet.</div>';}
function draw(){const a=document.getElementById('app');a.innerHTML=({picks,best:bestTab,mb:mbTab,vol:volTab,themes:themesTab,search:searchTab,results:resultsTab,accum:accumTab,ow:owTab,orders:ordersTab,big:bigTab,brokers:brokersTab,sectors,focus,news:newsTab,policy:policyTab,pli:pliTab,dma:dmaTab})[tab]()+'<div class="disc">Educational screening aid, not investment advice. BUY / WAIT / AVOID is an automatic score from public data (Screener.in, Yahoo Finance, Google News, company filings) that can be delayed or wrong. Do your own research and manage risk.</div>';if(tab==='search')sres();if(tab==='themes')renderThemes();if(tab==='best')renderBest();if(tab==='mb')renderMb();if(tab==='ow')renderOw();if(tab==='vol')renderVol();}
nav();draw();
</script></body></html>
"""

# ----------------------------------------------------------------------------
if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["full", "live", "demo", "catchup"], default="full")
    a = ap.parse_args()
    if a.mode == "demo":
        d = demo_data()
        raw, state = {s["sym"]: s for s in d["stocks"]}, {k: v for k, v in d.items() if k != "stocks"}
    elif a.mode in ("full", "catchup"):
        if a.mode == "catchup":
            st_, rw_ = load_state(), load_raw()
            if st_.get("universe_n") and len(rw_) >= 0.97 * st_["universe_n"]:
                print("All listed stocks are already loaded - nothing to catch up")
                sys.exit(0)
        raw, state = full_scan()
    else:
        raw, state = live_refresh()
    render(raw, state)
