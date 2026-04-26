 !/usr/bin/env python3

"""
LIVE PAPER FVG BOT (simulation only)

Requirements:
    pip install pybit pandas
Environment:
    Set BYBIT API_KEY and BYBIT_API_SECRET in environment if you wantF to use Bybit (read-only for kline).
Notes:
    - This is a paper/simulation bot: it does NOT place real orders.
    - RF (risk factor in $) is locked once per UTC day and used unchanged for all trades that day.
    - SL updates only (TP remains fixed at entry calculation).
"""

import os
import time
import logging
from datetime import datetime, timezone, timedelta
from pybit.unified_trading import HTTP
import pandas as pd
import math
from decimal import Decimal, ROUND_DOWN


# ===========================
# CONFIG (CHANGE AS NEEDED)
# ===========================
PAIRS = []
symbol_specs = {}

INTERVAL = "5"
CANDLE_LIMIT = 5
LOG_LEVEL = logging.INFO

START_BALANCE = 100.0
DAILY_RISK_PCT = 0.05
RR = 2
MIN_SL_PCT = 0.001
TP_BUFFER = 0.001
SL_BUFFER = 0.001

API_KEY = os.getenv("BYBIT_API_KEY", "")
API_SECRET = os.getenv("BYBIT_API_SECRET", "")
TESTNET = False

USE_REAL_TRADING = True
ACCOUNT_TYPE = "UNIFIED"
CATEGORY = "linear"
RF_PERCENT = 0.05

leverage_set = {}

last_daily_check = {}
daily_fvg_state = {}

eligible_pairs = []

recovery_orders = {}  

trade_state = {}  

last_scan = True
last_daily_run = None

for p in PAIRS:
    last_daily_check[p["symbol"]] = None
    daily_fvg_state[p["symbol"]] = {
        "allow_buy": False,
        "allow_sell": False,
        "buy_fvg_high": None,
        "buy_fvg_low": None,
        "sell_fvg_high": None,
        "sell_fvg_low": None,
        "last_new_buy_fvg": None,
        "last_new_sell_fvg": None
        
    }

MAX_SYMBOLS = 100          # number of pairs to scan
MAX_ACTIVE_TRADES = 6    # maximum open positions
DEFAULT_LEVERAGE = 50

last_symbol_refresh_week = None

signal_queue = []

    
# ===========================
# LOGGING & STATE
# ===========================
logging.basicConfig(level=LOG_LEVEL, format="%(asctime)s | %(message)s")
logger = logging.getLogger("paper_fvg_bot")

balance = float(START_BALANCE)
daily_rf = 0.0
current_day = None

weekly_rf = 0.0
current_week = None
siphoned_cash = 0.0

session = HTTP(testnet=TESTNET, api_key=API_KEY, api_secret=API_SECRET)

symbol_state = {}

account_cache = {
    "positions": [],
    "wallet_balance": 0.0,
    "used_margin": 0.0,
    "last_update": None
}

for p in PAIRS:
    symbol_state[p["symbol"]] = {
        "buy_fvg": None,
        "sell_fvg": None,
        "buy_trade": None,
        "sell_trade": None,
        "last_candle_time": 0,
        "buy_fvg_candle_time": None,
        "sell_fvg_candle_time": None,
    }

# ===========================
# HELPERS
# ===========================
def now_ts():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")

def fetch_candles(symbol, interval=INTERVAL, limit=CANDLE_LIMIT):
    for attempt in range(3):  # retry up to 3 times
        try:
            resp = session.get_kline(
                category="linear",
                symbol=symbol,
                interval=interval,
                limit=limit
            )

            raw = resp["result"]["list"]

            if not raw:
                logger.warning(f"{symbol} | Empty candle response")
                return []

            candles = list(reversed(raw))

            parsed = []
            for c in candles:
                parsed.append({
                    "time": int(c[0]),
                    "open": float(c[1]),
                    "high": float(c[2]),
                    "low": float(c[3]),
                    "close": float(c[4])
                })

            return parsed

        except Exception as e:
            err_msg = str(e)

            # 🔥 HANDLE RATE LIMIT
            if "10006" in err_msg or "Too many visits" in err_msg:
                sleep_time = 1 + attempt  # exponential backoff
                logger.warning(f"{symbol} | Rate limited, sleeping {sleep_time}s")
                time.sleep(sleep_time)
                continue

            # 🔥 HANDLE HEADER ERROR
            elif "x-bapi-limit-reset-timestamp" in err_msg:
                logger.warning(f"{symbol} | Header missing, retrying...")
                time.sleep(1)
                continue

            else:
                logger.error(f"{symbol} | Error fetching candles: {e}")
                return []

    return []


def seconds_until_next_candle(interval_minutes):
    now = datetime.now(timezone.utc)
    sec = int(interval_minutes) * 60
    seconds_into_cycle = (now.minute * 60 + now.second) % sec
    wait = sec - seconds_into_cycle
    if wait <= 0:
        wait += sec
    return wait

def fetch_daily_klines(symbol, retries=3, base_delay=1):
    for attempt in range(retries):
        try:
            resp = session.get_kline(
                category="linear",
                symbol=symbol,
                interval="D",
                limit=7
            )

            raw = resp["result"]["list"]

            if not raw:
                logger.warning(f"{symbol} | Empty daily kline response")
                return None

            time.sleep(0.3)  # keep your original delay
            return raw

        except Exception as e:
            err_msg = str(e)

            # 🔥 Rate limit handling
            if "10006" in err_msg or "Too many visits" in err_msg:
                delay = base_delay * (attempt + 1)
                logger.warning(f"{symbol} | Rate limited (daily), retrying in {delay}s...")
                time.sleep(delay)
                continue

            # 🔥 Header / transient API issue
            elif "x-bapi-limit-reset-timestamp" in err_msg:
                logger.warning(f"{symbol} | Header issue, retrying...")
                time.sleep(1)
                continue

            # 🔥 Unknown error
            else:
                logger.error(f"{symbol} | Daily kline fetch error: {e}")
                return None

    logger.error(f"{symbol} | Failed to fetch daily klines after {retries} attempts")
    return None

def sl_too_small(entry, sl):
    sl_pct = abs(entry - sl) / entry
    return sl_pct < 0.001  # 0.1%

def find_structure_sl(symbol, side, sl, lookback=20):
    candles = fetch_candles(symbol, interval=INTERVAL, limit=30)

    levels = []

    for i in range(2, len(candles) - 2):
        c = candles[i]

        if side == "BUY":
            logger.info(f"candle close: {c['open']}")
            is_swing_low = (
                c["low"] < candles[i-1]["low"] and
                c["low"] < candles[i-2]["low"] and
                c["low"] < candles[i+1]["low"] and
                c["low"] < candles[i+2]["low"]
            )

            if is_swing_low and c["low"] < sl:
                levels.append(c["low"])
                logger.info(f"swing low: {c['low']}")

        elif side == "SELL":
            logger.info(f"candle close: {c['open']}")
            is_swing_high = (
                c["high"] > candles[i-1]["high"] and
                c["high"] > candles[i-2]["high"] and
                c["high"] > candles[i+1]["high"] and
                c["high"] > candles[i+2]["high"]
            )

            if is_swing_high and c["high"] > sl:
                logger.info(f"swing high: {c['high']}")
                levels.append(c["high"])
        logger.info(f"levels list: {levels}")

    if not levels:
        return None
        
    if levels:
        logger.info(f"levels fs: {levels}")

    return levels[-1]


def find_consolidation_sl(symbol, entry, side, lookback=20, tolerance=0.002):
    candles = fetch_candles(symbol, interval=INTERVAL, limit=25)

    levels = []

    for i in range(len(candles) - 3):
        window = candles[i:i+4]

        highs = [c["high"] for c in window]
        lows = [c["low"] for c in window]

        if highs:
            logger.info(f"highs: {highs}")
        if lows:
            logger.info(f"lows: {lows}")

        zone_high = max(highs)
        zone_low = min(lows)

        
        if (zone_high - zone_low) / zone_high < tolerance:

            if side == "BUY" and zone_low < entry:
                levels.append(zone_low)

            elif side == "SELL" and zone_high > entry:
                levels.append(zone_high)

    if not levels:
        return None
        
    if levels:
        logger.info(f"levels fc: {levels[-1]}")
        return levels[-1]
    
def get_symbol_specs(symbol):
    if symbol in symbol_specs:
        return symbol_specs[symbol]

    info = session.get_instruments_info(
        category="linear",
        symbol=symbol
    )
    time.sleep(0.1)

    data = info["result"]["list"][0]

    specs = {
        "qty_step": float(data["lotSizeFilter"]["qtyStep"]),
        "min_qty": float(data["lotSizeFilter"]["minOrderQty"]),
        "tick_size": float(data["priceFilter"]["tickSize"]),
        "max_leverage": float(data["leverageFilter"]["maxLeverage"])
    }

    symbol_specs[symbol] = specs
    return specs

def fetch_top_symbols():

    resp = session.get_tickers(category="linear")
    time.sleep(0.2)
    tickers = resp["result"]["list"]

    symbols = []

    for t in tickers:
        sym = t["symbol"]

        if not sym.endswith("USDT"):
            continue

        vol = float(t["turnover24h"])

        symbols.append({
            "symbol": sym,
            "volume": vol
        })

    # rank by volume
    symbols.sort(key=lambda x: x["volume"], reverse=True)

    pairs = []

    for s in symbols:
        sym = s["symbol"]

        try:
            specs = get_symbol_specs(sym)
            max_lev = specs["max_leverage"]

            # ✅ FILTER HERE
            if max_lev < 50:
                continue

            pairs.append({
                "symbol": sym,
                "leverage": max_lev
            })

            logger.info(f"Selected: {sym} | Max Lev: {max_lev}")

            # ✅ STOP when we reach limit
            if len(pairs) >= MAX_SYMBOLS:
                break

            time.sleep(0.05)  # avoid rate limit

        except Exception as e:
            logger.warning(f"{sym} | Spec fetch error: {e}")

    return pairs
def refresh_symbol_universe_if_needed():

    global PAIRS, symbol_state, daily_fvg_state, last_daily_check, last_symbol_refresh_week

    
    now = datetime.now(timezone.utc)
    week = (now.year, now.isocalendar()[1])

    logger.info(f"WEEK: {week}")
    logger.info(f"LAST_SYMBOL_REFRESH_WEEK: {last_symbol_refresh_week}")

    if week == last_symbol_refresh_week:
        return

    logger.info("Refreshing symbol universe using 24h volume")

    new_pairs = fetch_top_symbols()

    PAIRS = new_pairs

    
    for p in new_pairs:
        sym = p["symbol"]
        if sym not in symbol_state:
            symbol_state[sym] = {
                "buy_fvg": None,
                "sell_fvg": None,
                "buy_trade": None,
                "sell_trade": None,
                "last_candle_time": 0,
                "buy_fvg_candle_time": None,
                "sell_fvg_candle_time": None}
            
        if sym not in daily_fvg_state:
            daily_fvg_state[sym] = {
                "allow_buy": False,
                "allow_sell": False,
                "buy_fvg_high": None,
                "buy_fvg_low": None,
                "sell_fvg_high": None,
                "sell_fvg_low": None,
                "last_new_buy_fvg": None,
                "last_new_sell_fvg": None
            }
            
        if sym not in last_daily_check:
            last_daily_check[sym] = None


    for p in PAIRS:

        sym = p["symbol"]

        if sym not in symbol_state:

            symbol_state[sym] = {
                "buy_fvg": None,
                "sell_fvg": None,
                "buy_trade": None,
                "sell_trade": None,
                "last_candle_time": 0,
                "buy_fvg_candle_time": None,
                "sell_fvg_candle_time": None,
            }

            daily_fvg_state[sym] = {
                "allow_buy": False,
                "allow_sell": False,
                "last_new_buy_fvg": None,
                "last_new_sell_fvg": None
            }

            last_daily_check[sym] = None

    last_symbol_refresh_week = week

    logger.info(f"Loaded {len(PAIRS)} top symbols")



def set_symbol_leverage(symbol, desired):

    specs = get_symbol_specs(symbol)

    lev = specs["max_leverage"]
    if leverage_set.get(symbol):
        return

    try:
        session.set_leverage(
            category="linear",
            symbol=symbol,
            buyLeverage=str(lev),
            sellLeverage=str(lev)
        )

        logger.info(f"{symbol} leverage set to {lev}")
        leverage_set[symbol] = True

    except Exception as e:

        if "110043" in str(e):
            logger.info(f"{symbol} leverage already set to {lev}")
        else:
            logger.error(f"{symbol} leverage error: {e}")

def ensure_hedge_mode():

    try:

        session.switch_position_mode(
            category="linear",
            coin="USDT",
            mode=3
        )

        logger.info("Hedge mode enabled")

    except Exception as e:

        if "110025" in str(e):
            logger.info("Hedge mode already enabled")
        else:
            logger.error(f"Hedge mode error: {e}")

def get_real_balance():
    try:
        resp = session.get_wallet_balance(accountType=ACCOUNT_TYPE)
        time.sleep(0.1)
        coins = resp["result"]["list"][0]["coin"]
        for c in coins:
            if c["coin"] == "USDT":
                return float(c["walletBalance"])
    except Exception as e:
        logger.error(f"Error fetching balance: {e}")
    return 0.0

def find_tp_buy(candles, entry):
    # look for nearest swing high (last 10 candles)
    highs = [c["high"] for c in candles[-10:]]
    return max(highs)

def find_tp_sell(candles, entry):
    # look for nearest swing low (last 10 candles)
    lows = [c["low"] for c in candles[-10:]]
    return min(lows)

def calculate_signal_score(entry, fvg_low, fvg_high):

    fvg_size = abs(fvg_high - fvg_low)

    # normalize to price so large coins don't dominate
    size_ratio = fvg_size / entry

    # bigger gap = stronger imbalance
    score = size_ratio * 1000

    return score

def get_open_positions():
    return [p for p in account_cache["positions"] if float(p["size"]) > 0]

def find_latest_swing_30m(symbol, side):
    candles = fetch_30m_candles(symbol, limit=50)

    swing = None

    for i in range(2, len(candles) - 2):
        c = candles[i]

        if side == "BUY":
            is_swing_low = (
                c["low"] < candles[i-1]["low"] and
                c["low"] < candles[i-2]["low"] and
                c["low"] < candles[i+1]["low"] and
                c["low"] < candles[i+2]["low"]
            )
            if is_swing_low:
                swing = c["low"]

        elif side == "SELL":
            is_swing_high = (
                c["high"] > candles[i-1]["high"] and
                c["high"] > candles[i-2]["high"] and
                c["high"] > candles[i+1]["high"] and
                c["high"] > candles[i+2]["high"]
            )
            if is_swing_high:
                swing = c["high"]
    return swing

def update_trade_progress(symbol, candles):
    if symbol not in trade_state:
        return

    t = trade_state[symbol]

    entry = t["entry"]
    sl = t["sl"]
    side = t["side"]

    last = candles[-1]

    if side == "BUY":
        one_r = entry + (entry - sl)
        if last["high"] >= one_r:
            t["reached_1R"] = True

    else:
        one_r = entry - (sl - entry)
        if last["low"] <= one_r:
            t["reached_1R"] = True
 
def update_trailing_sl():
    positions = get_open_positions()

    for pos in positions:
        symbol = pos["symbol"]
        size = float(pos["size"])

        if size == 0:
            continue

        side = pos["side"]  # "Buy" or "Sell"
        entry = float(pos["avgPrice"])
        current_sl = float(pos.get("stopLoss", 0) or 0)

        # Normalize side
        side_clean = "BUY" if side == "Buy" else "SELL"
        entry = 1

        new_swing = find_structure_sl(symbol, side_clean, current_sl)

        if new_swing is None:
            continue

        # =========================
        # BUY LOGIC
        # =========================
        if side_clean == "BUY":
            # only move SL UP
            if new_swing > current_sl and new_swing < entry:
                new_sl = new_swing

            else:
                continue

        # =========================
        # SELL LOGIC
        # =========================
        else:
            # only move SL DOWN
            if (current_sl == 0 or new_swing < current_sl) and new_swing > entry:
                new_sl = new_swing
            else:
                continue
        if abs(new_sl - current_sl) / entry < 0.001:
            continue
        # =========================
        # APPLY UPDATE
        # =========================
        if symbol in trade_state:
            update_recovery_order(symbol, new_sl)
        try:
            session.set_trading_stop(
                category="linear",
                symbol=symbol,
                stopLoss=str(new_sl),
                positionIdx=1 if side_clean == "BUY" else 2
            )

            logger.info(f"{symbol} | SL UPDATED → {new_sl}")

        except Exception as e:
            logger.error(f"{symbol} | SL update failed: {e}")

def position_exists(symbol, side):

    for pos in account_cache["positions"]:
        if pos["symbol"] == symbol:
            size = float(pos["size"])
            pos_side = pos["side"]
            if size > 0 and pos_side == side:
                return True
    return False
    
def lock_weekly_rf_if_needed():
    global current_week, weekly_rf, siphoned_cash

    now = datetime.now(timezone.utc)
    week = (now.year, now.isocalendar()[1])

    logger.info(f"CURRENT WEEK: {current_week}")
    logger.info(f"WEEK: {week}")

    if week != current_week:
        current_week = week

        real_balance = get_real_balance()

        # siphon 25%
        siphon_amount = real_balance * 0
        siphoned_cash += siphon_amount

        effective_balance = real_balance 
        weekly_rf = round(effective_balance * RF_PERCENT, 6)
        # weekly_rf = 10

        logger.info("===========================================")
        logger.info(f"NEW WEEK LOCKED: {current_week}")
        logger.info(f"REAL BALANCE: ${real_balance:.4f}")
        logger.info(f"SIPHONED: ${siphon_amount:.4f}")
        logger.info(f"EFFECTIVE BALANCE: ${effective_balance:.4f}")
        logger.info(f"LOCKED WEEKLY RF: ${weekly_rf:.4f}")
        logger.info("===========================================")

def refresh_account_cache():
    global account_cache

    try:
        # Positions
        pos_resp = session.get_positions(
            category="linear",
            settleCoin="USDT"
        )
        time.sleep(0.1)

        account_cache["positions"] = pos_resp["result"]["list"]

        # Wallet / margin
        wallet = session.get_wallet_balance(accountType="UNIFIED")
        data = wallet["result"]["list"][0]

        account_cache["wallet_balance"] = float(data["totalEquity"])
        account_cache["used_margin"] = float(data["totalInitialMargin"])

        account_cache["last_update"] = datetime.now(timezone.utc)

    except Exception as e:
        logger.error(f"Account cache refresh failed: {e}")
        
def update_daily_bias(symbol):
    global daily_fvg_state, last_daily_check

    utc_plus_1 = timezone(timedelta(hours=1))
    now = datetime.now(utc_plus_1)
    today = now.date()
    
    # -------------------------
    # FIRST STARTUP RUN
    # -------------------------
    if last_daily_check[symbol] is None:
        logger.info(f"{symbol} | First startup daily bias scan")
        run_daily_fvg_scan(symbol, today)
        last_daily_check[symbol] = today
        return

    # -------------------------
    # ONLY RUN AT 01:00
    # -------------------------
    if not (now.hour == 1 and now.minute < 5):
        return

    # -------------------------
    # RUN ONCE PER DAY
    # -------------------------
    if last_daily_check[symbol] == today:
        return

    logger.info(f"{symbol} | E")
    
    logger.info(f"{symbol} | Running scheduled daily bias scan")

    run_daily_fvg_scan(symbol, today)

    last_daily_check[symbol] = today
    logger.info(f"{symbol} | LAST DAILY CHECK {last_daily_check[symbol]}")

def fetch_30m_candles(symbol, limit=999):
    resp = session.get_kline(
        category="linear",
        symbol=symbol,
        interval="30",
        limit=limit
    )
    time.sleep(0.2)

    raw = resp["result"]["list"]
    candles = list(reversed(raw))

    return [{
        "high": float(c[2]),
        "low": float(c[3])
    } for c in candles]

def find_tp_sell_30m(symbol, entry, sl):
    candles_30m = fetch_30m_candles(symbol)

    risk = abs(entry - sl)
    normal_tp = entry - (risk * 2)

    for c in candles_30m:
        if c["low"] <= normal_tp:
            return c["low"]

    return normal_tp  # fallback

def find_tp_buy_30m(symbol, entry, sl):
    candles_30m = fetch_30m_candles(symbol)

    risk = abs(entry - sl)
    normal_tp = entry + (risk * 2)

    for c in candles_30m:
        if c["high"] >= normal_tp:
            return c["high"]

    return normal_tp  # fallback

def find_tp_structure_30m(symbol, entry, side, tp):
    candles = fetch_30m_candles(symbol)

    levels = []

    for i in range(2, len(candles) - 2):
        c = candles[i]

        if side == "BUY" and c["high"] > tp:
            is_high = (
                c["high"] > candles[i-1]["high"] and
                c["high"] > candles[i+1]["high"]
            )
            if is_high and c["high"] > entry:
                levels.append(c["high"])

        else:
            if side == "SELL" and c["low"] < tp:
                if c["low"] < tp:
                    is_low = (
                        c["low"] < candles[i-1]["low"] and
                        c["low"] < candles[i+1]["low"])
                    if is_low and c["low"] < entry:
                        levels.append(c["low"])
                        
    if not levels:
        return None
    logger.info(f"levels ftp: {levels}")
    logger.info(f"levels min: {min(levels)}, levels max: {max(levels)}")

    return levels[-1]

def process_signal_queue():

    global signal_queue

    if len(signal_queue) == 0:
        return

    # sort strongest first
    signal_queue.sort(key=lambda x: x["score"], reverse=True)

    open_positions = get_total_open_positions()
    slots_left = MAX_ACTIVE_TRADES - open_positions

    if slots_left <= 0:
        signal_queue = []
        return

    selected = signal_queue[:slots_left]

    for sig in selected:

        symbol = sig["symbol"]
        side = sig["side"]
        entry = sig["entry"]
        sl = sig["sl"]
        tp = sig["tp"]
        leverage = sig["leverage"]
        qty = sig["qty"]

        place_real_trade(
            symbol,
            side,
            entry,
            sl,
            tp,
            leverage,
            weekly_rf,
            qty
        )

    signal_queue = []


def run_daily_fvg_scan(symbol, today):

    yesterday = today - timedelta(days=1)
    
    # Expire old permissions
    if daily_fvg_state[symbol]["last_new_buy_fvg"]:
        age_days = (today - daily_fvg_state[symbol]["last_new_buy_fvg"]).days
        logger.info(f"{symbol} | AGE DAYS {age_days}")
        if age_days >= 2:
            daily_fvg_state[symbol]["allow_buy"] = False
            logger.info(f"{symbol} BUY FVG expired (2 days)")

    if daily_fvg_state[symbol]["last_new_sell_fvg"]:
        age_days = (today - daily_fvg_state[symbol]["last_new_sell_fvg"]).days
        logger.info(f"{symbol} | AGE DAYS {age_days}")
        if age_days >= 2:
            daily_fvg_state[symbol]["allow_sell"] = False
            logger.info(f"{symbol} SELL FVG expired (2 days)")

    raw = fetch_daily_klines(symbol)
    if not raw:
        return
        
    candles = list(reversed(raw))

    df = pd.DataFrame([{
        "time": int(c[0]),
        "open": float(c[1]),
        "high": float(c[2]),
        "low": float(c[3]),
        "close": float(c[4])
    } for c in candles])

    if len(df) < 4:
        return

    c1 = df.iloc[-4]
    c3 = df.iloc[-2]
    c2 = df.iloc[-5]
    c4 = df.iloc[-3]

    logger.info(f"{symbol} c1: {c1["open"]}")
    logger.info(f"{symbol} c2: {c2["open"]}")
    logger.info(f"{symbol} c3: {c3["open"]}")
    logger.info(f"{symbol} c4: {c4["open"]}")
    
    sell_fvg_exists = c1["low"] > c3["high"]
    buy_fvg_exists = c1["high"] < c3["low"]

    prev_day_sell_fvg_exists = c2["low"] > c4["high"]
    prev_day_buy_fvg_exists = c2["high"] < c4["low"]

    if buy_fvg_exists:
        daily_fvg_state[symbol]["allow_buy"] = True
        daily_fvg_state[symbol]["last_new_buy_fvg"] = today
        
        daily_fvg_state[symbol]["buy_fvg_high"] = c3["low"]
        daily_fvg_state[symbol]["buy_fvg_low"] = c1["high"]
        
        logger.info(f"{symbol} Daily BUY FVG detected")

    if sell_fvg_exists:
        daily_fvg_state[symbol]["allow_sell"] = True
        daily_fvg_state[symbol]["last_new_sell_fvg"] = today

        daily_fvg_state[symbol]["sell_fvg_high"] = c1["low"]
        daily_fvg_state[symbol]["sell_fvg_low"] = c3["high"]
        
        logger.info(f"{symbol} Daily SELL FVG detected")
        
    if prev_day_buy_fvg_exists:
        daily_fvg_state[symbol]["allow_buy"] = True
        daily_fvg_state[symbol]["last_new_buy_fvg"] = yesterday
        logger.info(f"{symbol} Previous Day Daily BUY FVG detected")
        logger.info(f"{symbol} Yesterday date is {yesterday}")

    if prev_day_sell_fvg_exists:
        daily_fvg_state[symbol]["allow_sell"] = True
        daily_fvg_state[symbol]["last_new_sell_fvg"] = yesterday
        logger.info(f"{symbol} Previous Day Daily SELL FVG detected")
        logger.info(f"{symbol} Yesterday date is {yesterday}")
            
def log_candles(symbol, candles):
    logger.info(f"{symbol} | Retrieved {len(candles)} candles (oldest -> newest).")
    for c in candles:
        t = datetime.utcfromtimestamp(c["time"] / 1000).strftime("%Y-%m-%d %H:%M:%S")
        logger.info(f"{symbol} | {t} | O:{c['open']} H:{c['high']} L:{c['low']} C:{c['close']}")

def round_qty(symbol, qty):
    specs = get_symbol_specs(symbol)

    step = Decimal(str(specs["qty_step"]))
    min_qty = Decimal(str(specs["min_qty"]))
    qty = Decimal(str(qty))

    qty = (qty // step) * step  # floor to step

    if qty < min_qty:
        qty = min_qty

    return float(qty)

def get_margin_usage():
    total = account_cache["wallet_balance"]
    used = account_cache["used_margin"]
    return total, used
    
def margin_available_for_trade(required_margin):

    total, used = get_margin_usage()

    max_allowed = total * 0.8

    if used + required_margin > max_allowed:

        remaining = max_allowed - used

        if remaining <= 0:
            return False, 0

        return True, remaining

    return True, required_margin

def calculate_margin_required(price, qty, leverage):

    position_value = price * qty

    margin = position_value / leverage

    return margin

def trade_value_ok(price, qty):

    return price * qty >= 5

def fit_qty_to_margin(symbol, price, leverage, desired_qty):

    margin_needed = calculate_margin_required(price, desired_qty, leverage)

    ok, allowed_margin = margin_available_for_trade(margin_needed)

    if ok:
        return desired_qty

    # reduce qty to fit remaining margin

    new_position_value = allowed_margin * leverage
    new_qty = new_position_value / price

    new_qty = round_qty(symbol, new_qty)

    if not trade_value_ok(price, new_qty):
        return None

    return new_qty

def get_total_open_positions():

    count = 0

    for pos in account_cache["positions"]:
        if float(pos["size"]) > 0:
            count += 1

    return count

def is_position_open(symbol):
    for pos in account_cache["positions"]:
        if pos["symbol"] == symbol and float(pos["size"]) > 0:
            return True
    return False

def place_recovery_order(symbol):
    if symbol not in trade_state:
        return
    if symbol in recovery_orders:
        try:
            session.cancel_order(
            category=CATEGORY,
            symbol=symbol,
            orderId=recovery_orders[symbol]["order_id"])
        except Exception as e:
            logger.error(f"{symbol} | Cancel failed: {e}")
            
        del recovery_orders[symbol]

    t = trade_state[symbol]

    entry = t["entry"]
    sl = t["sl"]
    side = t["side"]
    loss = abs(t["entry"] - t["sl"]) * t["qty"]
    specs = get_symbol_specs(symbol)
    leverage = specs["max_leverage"]
    if side == "BUY":
        rec_side = "Sell"
        rec_entry = sl
        position_idx = 2
    else:
        rec_side = "Buy"
        rec_entry = sl
        position_idx = 1
    entry = 1
    real_sl = find_structure_sl(symbol, rec_side.upper(), rec_entry)

    if real_sl is None:
        logger.warning(f"{symbol} | No valid SL for recovery, skipping")
        return
       
    logger.info(f"recovery chosen sl: {real_sl}")

    rec_sl = real_sl
            
    logger.info(f"{symbol} | RECOVERY STRUCTURE SL: {rec_sl}")
    if rec_side.upper() == "BUY":
        rec_sl = real_sl * (1 - (SL_BUFFER * 1))
        risk_amount = weekly_rf
        risk_sl = rec_sl * (1 - (SL_BUFFER * 1))
    else:
        rec_sl = real_sl * (1 + (SL_BUFFER * 1))
        risk_amount = weekly_rf
        risk_sl = rec_sl * (1 + (SL_BUFFER * 1))
    sl_distance = abs(rec_entry - risk_sl)
    if sl_distance <= 0:
        return
    recovery_qty = risk_amount / sl_distance
    recovery_qty = round_qty(symbol, recovery_qty)
    recovery_qty = fit_qty_to_margin(symbol, rec_entry, leverage, recovery_qty)
    
    if recovery_qty is None:
        return
    if recovery_qty <= 0:
        return
    tp_distance = abs(rec_entry - rec_sl)

    if rec_side.upper() == "BUY":
        rec_tp = rec_entry + tp_distance
    else:
        rec_tp = rec_entry - tp_distance
            
    if recovery_qty <= 0:
        return
    if recovery_qty is None:
        return
    qty = recovery_qty
 
    try:
        resp = session.place_order(
            category=CATEGORY,
            symbol=symbol,
            side=rec_side,
            orderType="Limit",
            price=str(rec_entry),
            qty=str(qty),
            timeInForce="GTC",
            
            triggerPrice=str(rec_entry),
            triggerDirection=1 if rec_side == "Buy" else 2,
            
            takeProfit=str(rec_tp),
            stopLoss=str(rec_sl),

            positionIdx=position_idx)
        order_id = resp["result"]["orderId"]

        recovery_orders[symbol] = {
            "order_id": order_id,
            "side": rec_side,
            "entry": rec_entry,
            "qty": qty
        }

        logger.info(f"{symbol} | Recovery order placed")
        logger.info(
            f"{symbol} | rec_tp={rec_tp}, qty={recovery_qty}, "
            f"sl_dist={sl_distance}, risk_sl={risk_sl}, "
            f"rec_sl={rec_sl}, entry={rec_entry}, loss={loss}")
        
    except Exception as e:
        logger.error(f"{symbol} | Recovery order error: {e}")
        logger.info(
            f"{symbol} | rec_tp={rec_tp}, qty={recovery_qty}, "
            f"sl_dist={sl_distance}, risk_sl={risk_sl}, "
            f"rec_sl={rec_sl}, entry={rec_entry}, loss={loss}")

def update_recovery_order(symbol, new_sl):
    if symbol not in recovery_orders or symbol not in trade_state:
        return

    rec = recovery_orders[symbol]
    t = trade_state[symbol]

    # cancel old
    try:
        session.cancel_order(
            category=CATEGORY,
            symbol=symbol,
            orderId=rec["order_id"]
        )
    except Exception as e:
        logger.error(f"{symbol} | Failed to cancel recovery order: {e}")

    # update SL
    t["sl"] = new_sl

    # place new one
    place_recovery_order(symbol)
 
def simulate_and_resolve_trade(symbol, side, entry_index, entry, sl, tp, candles):
    for j in range(entry_index + 1, len(candles)):
        high = candles[j]["high"]
        low = candles[j]["low"]

        if side == "BUY":
            if low <= sl:
                return "LOSS", j
            if high >= tp:
                return "WIN", j
        elif side == "SELL":
            if high >= sl:
                return "LOSS", j
            if low <= tp:
                return "WIN", j
    return "OPEN", None

def calculate_liquidation_price(entry, qty, side, leverage, available_balance):
    """
    Approximate liquidation price for cross + hedge mode
    """

    position_value = entry * qty
    im = 1 / leverage  # initial margin rate
    mmr = 0.005        # your 0.5% maintenance margin

    extra_margin_ratio = available_balance / position_value

    effective_buffer = im + extra_margin_ratio - mmr

    if side == "Buy":  # LONG
        lp = entry * (1 - effective_buffer)
    else:  # SHORT
        lp = entry * (1 + effective_buffer)

    return lp

# ===========================
# CORE SYMBOL HANDLER
# ===========================
def handle_symbol(pair):
    global balance, weekly_rf

    symbol = pair["symbol"]
    leverage = pair.get("leverage", 1)
    state = symbol_state[symbol]
    
    candles = fetch_candles(symbol, interval=INTERVAL, limit=CANDLE_LIMIT)
    if len(candles) < 5:
        logger.warning(f"{symbol} | Not enough candles fetched ({len(candles)}). Skipping this cycle.")
        return

    now_utc = datetime.now(timezone.utc)
    current_candle_open = int(now_utc.timestamp() // (int(INTERVAL) * 60)) * (int(INTERVAL) * 60) * 1000
    closed_candles = [c for c in candles if c["time"] < current_candle_open]
    if len(closed_candles) < 3:
        logger.warning(f"{symbol} | Not enough strictly closed candles.")
        return

    last_closed = closed_candles[-1]
    
    if daily_fvg_state[symbol]["allow_buy"]:
        current_price = last_closed["low"]
        if daily_fvg_state[symbol]["buy_fvg_high"]:
            high = daily_fvg_state[symbol]["buy_fvg_high"]
            if high is not None and current_price <= high:
                daily_fvg_state[symbol]["allow_buy"] = False
                logger.info(f"{symbol} BUY FVG invalidated (price reached daily fvg upper boundary)")
            
    if daily_fvg_state[symbol]["allow_sell"]:
        current_price = last_closed["high"]
        if daily_fvg_state[symbol]["sell_fvg_low"]:
            low = daily_fvg_state[symbol]["sell_fvg_low"]
            if low is not None and current_price >= low:
                daily_fvg_state[symbol]["allow_sell"] = False
                logger.info(f"{symbol} SELL FVG invalidated (price reached daily fvg lower boundary)")

    
    prev1 = closed_candles[-1]
    prev2 = closed_candles[-3]
    logger.info(f"{symbol} | prev2 H:{prev2['high']} L:{prev2['low']} | prev1 H:{prev1['high']} L:{prev1['low']}")

    if last_closed["time"] == state["last_candle_time"]:
        logger.info(f"{symbol} problem")
        return
    state["last_candle_time"] = last_closed["time"]

    t_last = datetime.utcfromtimestamp(last_closed["time"] / 1000).strftime("%Y-%m-%d %H:%M:%S")
    logger.info(f"{symbol} | Processing closed candle {t_last} | C={last_closed['close']}")

    body = abs(prev1["close"] - prev1["open"])
    range_ = prev1["high"] - prev1["low"]
    
    if range_ == 0:
        return
        
    body_ratio = body / range_
    
    bull_displacement = (
        prev1["close"] > prev1["open"] and
        body_ratio > 0.1 and
        prev1["close"] > prev2["high"])
    
    bear_displacement = (
        prev1["close"] < prev1["open"] and
        body_ratio > 0.1 and
        prev1["close"] < prev2["low"])
    
    bull_fvg = prev1["low"] > prev2["high"] and bull_displacement
    bear_fvg = prev1["high"] < prev2["low"] and bear_displacement
    
    # -----------------------
    # BUY FVG
    # -----------------------
    if bull_fvg:
        new_low = prev2["high"]
        new_high = prev1["low"]
        mid = new_low + (new_high - new_low) * 0.5
        created_at = prev1["time"]
        state["buy_fvg"] = {
            "low": new_low,
            "high": new_high,
            "mid": mid,
            "tapped": False,
            "deepest_touch": None,
            "created_at": created_at}
        logger.info(f"{symbol} | New BUY FVG detected: low={new_low} high={new_high}")

        state["buy_fvg_candle_time"] = prev1["time"]
        if not position_exists(symbol, "Buy"):
            logger.info(f"{symbol} | BUY FVG registered as active watcher (no active buy trade).")
        fvg_size_pct = abs(new_high - new_low) / new_high
        if fvg_size_pct < 0.0001:
            logger.info(f"{symbol} | FVG too small, skipping")
            return

    # -----------------------
    # SELL FVG
    # -----------------------
    if bear_fvg:
        new_high = prev2["low"]
        new_low = prev1["high"]
        mid = new_high - (new_high - new_low) * 0.5
        created_at = prev1["time"]
        state["sell_fvg"] = {
            "high": new_high,
            "low": new_low,
            "mid": mid,
            "tapped": False,
            "deepest_touch": None,
            "created_at": created_at}
        logger.info(f"{symbol} | New SELL FVG detected: high={new_high} low={new_low}")

        state["sell_fvg_candle_time"] = prev1["time"]
        if not position_exists(symbol, "Sell"):
            logger.info(f"{symbol} | SELL FVG registered as active watcher (no active sell trade).")
        fvg_size_pct = abs(new_high - new_low) / new_high
        if fvg_size_pct < 0.0001:
            logger.info(f"{symbol} | FVG too small, skipping")
            return

    # -----------------------
    # TAP CHECK
    # -----------------------
    if state["buy_fvg"] and not state["buy_fvg"]["tapped"]:
        bf = state["buy_fvg"]
        if last_closed["time"] != state["buy_fvg_candle_time"]:
            if last_closed["low"] <= bf["high"] and last_closed["high"] >= bf["low"]:
                bf["tapped"] = True
                logger.info(f"{symbol} | BUY FVG TAPPED (candle touched the FVG range).")
    if state["buy_fvg"] and state["buy_fvg"]["tapped"]:
        bf = state["buy_fvg"]
        if bf["low"] <= last_closed["low"] <= bf["high"]:
            if bf["deepest_touch"] is None:
                bf["deepest_touch"] = last_closed["low"]
            else:
                bf["deepest_touch"] = min(bf["deepest_touch"], last_closed["low"])

    if state["sell_fvg"] and not state["sell_fvg"]["tapped"]:
        sf = state["sell_fvg"]
        if last_closed["time"] != state["sell_fvg_candle_time"]:
            if last_closed["low"] <= sf["high"] and last_closed["high"] >= sf["low"]:
                sf["tapped"] = True
                logger.info(f"{symbol} | SELL FVG TAPPED (candle touched the FVG range).")
    if state["sell_fvg"] and state["sell_fvg"]["tapped"]:
        sf = state["sell_fvg"]
        if sf["low"] <= last_closed["high"] <= sf["high"]:
            if sf["deepest_touch"] is None:
                sf["deepest_touch"] = last_closed["high"]
            else:
                sf["deepest_touch"] = max(sf["deepest_touch"], last_closed["high"])

    # -----------------------
    # FVG INVALIDATION
    # -----------------------
    if state["buy_fvg"]:
        bf = state["buy_fvg"]
        if last_closed["low"] < bf["low"]:
            logger.info(f"{symbol} | BUY FVG INVALIDATED (closed below {bf['low']})")
            state["buy_fvg"] = None

    if state["sell_fvg"]:
        sf = state["sell_fvg"]
        if last_closed["high"] > sf["high"]:
            logger.info(f"{symbol} | SELL FVG INVALIDATED (closed above {sf['high']})")
            state["sell_fvg"] = None

    # -----------------------
    # CONFIRMATION (OPEN PAPER/REAL TRADE)
    # -----------------------
    # BUY confirmation
    if state["buy_fvg"] and state["buy_fvg"]["tapped"] and not position_exists(symbol, "Buy") and last_closed["time"] != state["buy_fvg_candle_time"]:
        bf = state["buy_fvg"]
        
        if bf["deepest_touch"] is None or bf["deepest_touch"] > bf["mid"]:
            if not (last_closed["close"] > bf["high"]):
                logger.info(f"{symbol} | BUY ignored: price did not reach FVG mid")
            return
        
        if bf["deepest_touch"] is not None:
            extreme_not_touched = bf["deepest_touch"] > bf["low"]    # did not touch extreme low
            if not extreme_not_touched:
                if not (last_closed["close"] > bf["high"]):
                    logger.info(f"{symbol} | BUY ignored: touched extreme")
                return

        if not daily_fvg_state[symbol]["allow_buy"]:
            logger.info(f"{symbol} | Daily bias does not allow BUY, skipping")
            return
            
        if last_closed["close"] > bf["high"]:
            entry = last_closed["close"]
            
            deep = bf["deepest_touch"]
            
            if deep is None:
                logger.info(f"{symbol} | BUY ignored: no deepest touch recorded")
                return
            sl = bf["low"]
            chosen_sl = find_structure_sl(symbol, "BUY", sl)
       
            logger.info(f"chosen sl: {chosen_sl}")

                
            real_sl = chosen_sl if chosen_sl else min(
                bf["low"],
                prev2["low"],
                bf["deepest_touch"])
            
            logger.info(f"{symbol} | STRUCTURE SL (BUY): {real_sl}")
            
            risk_sl = real_sl * (1 - (SL_BUFFER * 2))
            
            risk_amount = weekly_rf
            raw_qty = risk_amount / abs(entry - risk_sl)
            
            specs = get_symbol_specs(symbol)
            step = specs["qty_step"]
            
            qty = round_qty(symbol, raw_qty)
            qty = fit_qty_to_margin(     
                symbol,     
                entry,   
                leverage, 
                qty) 
            if qty is None:  
                logger.info(f"{symbol} | Not enough margin for trade")  
                return

            if not trade_value_ok(entry, qty):
                logger.info(f"{symbol} | Trade value < $5. Skipping")
                return
            
            sl = real_sl * (1 - SL_BUFFER)  # this is what will be sent to exchange
            
            state["buy_fvg"] = None
            if sl_too_small(entry, real_sl):
                logger.info(f"{symbol} | BUY skipped: SL distance < 0.1%")
                return
            normal_tp = entry + (abs(entry - sl) * 2)
            tp = find_tp_structure_30m(symbol, entry, "BUY", normal_tp)
            if tp is None:
                tp = normal_tp

            if abs(tp - entry) < 2 * abs(entry - sl):
                logger.info(f"{symbol} | BUY skipped: RR too low after liquidity TP")
                return  # skip weak trade
            logger.info(f"{symbol} | BUY CONFIRMED | entry={entry} sl={sl} tp={tp}")
            if USE_REAL_TRADING and position_exists(symbol, "Sell"):
                try:
                    logger.info(f"{symbol} | Closing existing SELL before opening BUY")
                    session.place_order(
                        category=CATEGORY,
                        symbol=symbol,
                        side="Buy",
                        orderType="Market",
                        qty="0",
                        reduceOnly=True,
                        positionIdx=2
                    )
                    time.sleep(0.2)  # small delay for safety
                except Exception as e:
                    logger.error(f"{symbol} | Failed closing SELL: {e}")
            if USE_REAL_TRADING:
                available_balance = get_real_balance()  # use your balance function
                risk_amount = weekly_rf  # your frozen risk
                raw_qty = risk_amount / abs(entry - risk_sl)
                    
                specs = get_symbol_specs(symbol)
                step = specs["qty_step"]
                
                qty = round_qty(symbol, raw_qty)
                qty = fit_qty_to_margin(     
                    symbol,     
                    entry,   
                    leverage, 
                    qty) 
                if qty is None:  
                    logger.info(f"{symbol} | Not enough margin for trade")                          
                    return

                if not trade_value_ok(entry, qty):
                    logger.info(f"{symbol} | Trade value < $5. Skipping")
                    return
                    
                lp = calculate_liquidation_price(
                    entry=entry,
                    qty=qty,
                    side="Buy",
                    leverage=leverage,
                    available_balance=available_balance)
                distance_to_lp_pct = abs((sl - lp) / entry)
                if distance_to_lp_pct < 0.003:  # 0.1%
                    logger.info(f"{symbol} | Skipping BUY - SL too close to liquidation ({distance_to_lp_pct*100:.3f}%)")
                    return
                score = calculate_signal_score(entry, bf["low"], bf["high"])
                    
                signal_queue.append({
                    "symbol": symbol,
                    "side": "BUY",
                    "entry": entry,
                    "sl": sl,
                    "tp": tp,
                    "score": score,
                    "qty": qty,
                    "leverage": leverage})
                logger.info(f"{symbol} BUY signal queued | score={score:.4f}")
            else:
                signal_queue.append({
                    "symbol": symbol,
                    "side": "BUY",
                    "entry": entry,
                    "sl": sl,
                    "tp": tp,
                    "score": score,
                     "qty": qty,
                    "leverage": leverage})
                logger.info(f"{symbol} BUY signal queued | score={score:.4f}")
        else:
            logger.info(f"{symbol} | BUY confirmation ignored: SL too tight")

    # SELL confirmation
    if state["sell_fvg"] and state["sell_fvg"]["tapped"] and not position_exists(symbol, "Sell") and last_closed["time"] != state["sell_fvg_candle_time"]:
        sf = state["sell_fvg"]
        
        if sf["deepest_touch"] is None or sf["deepest_touch"] < sf["mid"]:
            if not (last_closed["close"] < sf["low"]):
                logger.info(f"{symbol} | SELL ignored: price did not reach FVG mid")
            return


        if sf["deepest_touch"] is not None:
            extreme_not_touched = sf["deepest_touch"] < sf["high"]
            if not extreme_not_touched:
                if not (last_closed["close"] < sf["low"]):
                    logger.info(f"{symbol} | SELL ignored: touched extreme")
                return

        if not daily_fvg_state[symbol]["allow_sell"]:
            logger.info(f"{symbol} | Daily bias does not allow SELL, skipping")
            return
            
        if last_closed["close"] < sf["low"]:
            entry = last_closed["close"]

            
            deep = sf["deepest_touch"]
            
            if deep is None:
                logger.info(f"{symbol} | SELL ignored: no deepest touch recorded")
                return
            sl = sf["high"] 
            chosen_sl = find_structure_sl(symbol, "SELL", sl)      
                
            logger.info(f"chosen sl: {chosen_sl}")
                
            real_sl = chosen_sl if chosen_sl else max(
                sf["high"],
                prev2["high"],
                sf["deepest_touch"])
            
            logger.info(f"{symbol} | STRUCTURE SL (SELL): {real_sl}")
                
            risk_sl = real_sl * (1 + (SL_BUFFER * 2))
            
            risk_amount = weekly_rf
            raw_qty = risk_amount / abs(entry - risk_sl)
            
            specs = get_symbol_specs(symbol)
            step = specs["qty_step"]
            
            qty = round_qty(symbol, raw_qty)  
            qty = fit_qty_to_margin(     
                symbol,   
                entry,    
                leverage,   
                qty) 
            if qty is None:  
                logger.info(f"{symbol} | Not enough margin for trade")  
                return

            if not trade_value_ok(entry, qty):
                logger.info(f"{symbol} | Trade value < $5. Skipping")
                return
                
            sl = real_sl * (1 + SL_BUFFER)

            state["sell_fvg"] = None
            if sl_too_small(entry, risk_sl):
                logger.info(f"{symbol} | SELL skipped: SL distance < 0.1%")
                return
            normal_tp = entry - (abs(entry - sl) * 2)
            tp = find_tp_structure_30m(symbol, entry, "SELL", normal_tp)
            if tp is None:
                tp = normal_tp

            if abs(tp - entry) < 2 * abs(entry - sl):
                logger.info(f"{symbol} | SELL skipped: RR too low after liquidity TP")
                return  # skip weak trade
            
            logger.info(f"{symbol} | SELL CONFIRMED | entry={entry} sl={sl} tp={tp}")
            if USE_REAL_TRADING and position_exists(symbol, "Buy"):
                try:
                    logger.info(f"{symbol} | Closing existing BUY before opening SELL")
                    session.place_order(
                        category=CATEGORY,
                        symbol=symbol,
                        side="Sell",
                        orderType="Market",
                        qty="0",
                        reduceOnly=True,
                        positionIdx=1)
                    time.sleep(0.2)
                except Exception as e:
                    logger.error(f"{symbol} | Failed closing BUY: {e}")
            if USE_REAL_TRADING:
                available_balance = get_real_balance()  # use your balance function
                risk_amount = weekly_rf  # your frozen risk
                raw_qty = risk_amount / abs(entry - risk_sl)
                    
                specs = get_symbol_specs(symbol)
                step = specs["qty_step"]
                qty = round_qty(symbol, raw_qty) 
                qty = fit_qty_to_margin(   
                    symbol,  
                    entry,   
                    leverage,
                    qty) 
                if qty is None:   
                    logger.info(f"{symbol} | Not enough margin for trade")  
                    return

                if not trade_value_ok(entry, qty):
                    logger.info(f"{symbol} | Trade value < $5. Skipping")
                    return
                    
                lp = calculate_liquidation_price(
                    entry=entry,
                    qty=qty,
                    side="Sell",
                    leverage=leverage,
                    available_balance=available_balance)
                
                distance_to_lp_pct = abs((lp - sl) / entry)
                    
                if distance_to_lp_pct < 0.003:
                    logger.info(f"{symbol} | Skipping SELL - SL too close to liquidation ({distance_to_lp_pct*100:.3f}%)")
                    return
                score = calculate_signal_score(entry, sf["low"], sf["high"])                    
                signal_queue.append({
                    "symbol": symbol,
                    "side": "SELL",
                    "entry": entry,
                    "sl": sl,
                    "tp": tp,
                    "score": score,
                    "qty": qty,
                    "leverage": leverage})
                logger.info(f"{symbol} SELL signal queued | score={score:.4f}")

            else:
                signal_queue.append({
                    "symbol": symbol,
                    "side": "SELL",
                    "entry": entry,
                    "sl": sl,
                    "tp": tp,
                    "score": score,
                    "qty": qty,
                    "leverage": leverage})
                logger.info(f"{symbol} SELL signal queued | score={score:.4f}")
        else:
            logger.info(f"{symbol} | SELL confirmation ignored: SL too tight")
    
def place_real_trade(symbol, side, entry, sl, tp, leverage, frozen_risk, qty):

    side = side.upper()

    if symbol in recovery_orders:
        try:
            session.cancel_order(
                category=CATEGORY,
                symbol=symbol,
                orderId=recovery_orders[symbol]["order_id"])
        except Exception as e:
            logger.error(f"{symbol} | Failed to cancel recovery order: {e}")
        del recovery_orders[symbol]
    
    if symbol in trade_state:
        del trade_state[symbol]

    if get_total_open_positions() >= MAX_ACTIVE_TRADES:
        logger.info(f"Max {MAX_ACTIVE_TRADES} open trades reached. Skipping.")
        return

    if side == "BUY":
        order_side = "Buy"
        position_idx = 1
    elif side == "SELL":
        order_side = "Sell"
        position_idx = 2
    else:
        logger.error(f"{symbol} | Invalid side: {side}")
        return

    if position_exists(symbol, order_side):
        logger.info(f"{symbol} | {side} position already exists. Skipping.")
        return

    if frozen_risk <= 0:
        logger.warning(f"{symbol} | Frozen risk is zero. Skipping trade.")
        return

    try:
        sl_distance = abs(entry - sl)

        if sl_distance <= 0:
            logger.warning(f"{symbol} | SL distance zero. Aborting.")
            return

        if qty <= 0:
            logger.warning(f"{symbol} | Invalid qty ({qty}). Aborting.")
            return

        logger.info(f"{symbol} | Frozen Risk: ${frozen_risk:.4f}")
        logger.info(f"{symbol} | Qty: {qty}")

        # =============================
        # SIMULATION MODE
        # =============================
        if not USE_REAL_TRADING:
            logger.info(f"[SIMULATED] {symbol} {side} | entry={entry} sl={sl} tp={tp} qty={qty}")
            refresh_account_cache()
            return

        # =============================
        # REAL EXECUTION
        # =============================
        order_response = session.place_order(
            category=CATEGORY,
            symbol=symbol,
            side=order_side,
            orderType="Market",
            qty=str(qty),
            timeInForce="IOC",
            positionIdx=position_idx
        )
        time.sleep(0.2)

        logger.info(f"{symbol} | Order response: {order_response}")

        session.set_trading_stop(
            category=CATEGORY,
            symbol=symbol,
            takeProfit=str(tp),
            stopLoss=str(sl),
            positionIdx=position_idx
        )
        time.sleep(0.2)

        refresh_account_cache()

        logger.info(f"{symbol} | REAL {side} ORDER PLACED | TP={tp} SL={sl}")
        trade_state[symbol] = {
            "entry": entry,
            "sl": sl,
            "side": side,
            "reached_1R": False,
            "qty": qty}
    except Exception as e:
        logger.error(f"{symbol} | Order error: {e}")# MAIN LOOP

def main():
    global balance, daily_rf, last_scan, eligible_pairs

    logger.info("LIVE PAPER FVG BOT (simulation) STARTED")
    real_balance = get_real_balance()
    logger.info(f"STARTUP BALANCE = ${real_balance:.4f}")
    refresh_account_cache()
    ensure_hedge_mode()
    # Lock initial daily RF for current UTC day
    # update_daily_bias()

    refresh_symbol_universe_if_needed()

    for p in PAIRS:
        logger.info(f"Symbol loaded: {p['symbol']} | leverage: {p['leverage']}")
    
    for p in PAIRS:
        get_symbol_specs(p["symbol"])
        
    for p in PAIRS:
        set_symbol_leverage(p["symbol"], p["leverage"])
        time.sleep(0.2)
    lock_weekly_rf_if_needed()

    try:
        while True:
            refresh_symbol_universe_if_needed()
            
            # wait until next candle close (UTC)
            wait = seconds_until_next_candle(INTERVAL)
            logger.info(f"Waiting {wait}s for next {INTERVAL}m candle close (UTC)...")
            time.sleep(wait + 0.8)  # small offset to ensure candle is closed on exchange

            refresh_account_cache()
            update_trailing_sl()
            for p in PAIRS: 
                update_daily_bias(p["symbol"])
            for p in PAIRS:
                symbol = p["symbol"]
                candles = fetch_candles(symbol)
                
                update_trade_progress(symbol, candles)
                    
            for sym in list(trade_state.keys()):
                if not is_position_open(sym):
                    if sym in recovery_orders:
                        try:
                            session.cancel_order(
                                category=CATEGORY,
                                symbol=sym,
                                orderId=recovery_orders[sym]["order_id"])
                        except Exception as e:
                            logger.error(f"{sym} | Failed to cancel recovery order: {e}")
                        del recovery_orders[sym]
                    del trade_state[sym]
            for sym in trade_state:
                if sym not in recovery_orders:
                    place_recovery_order(sym)
                    logger.info(f"{sym} | Recovery order placed")
            
            # Lock per-day RF at start of UTC day if needed (one global RF for all pairs)
            lock_weekly_rf_if_needed()

            # Process each pair independently
            
            for p in PAIRS:
                utc_plus_1 = timezone(timedelta(hours=1))
                now = datetime.now(utc_plus_1)
                today = now.date()
                should_run = False
                
                if last_scan:
                    should_run = True
                elif now.hour == 1 and now.minute < 5:
                    if last_daily_run != today:
                        should_run = True
                        last_daily_run = today
                if should_run:
                    eligible_pairs = []
                    for p in PAIRS:
                        sym = p["symbol"]
                        if daily_fvg_state[sym]["allow_buy"] or daily_fvg_state[sym]["allow_sell"]:
                            logger.info(f"{sym} | Daily bias: buy={daily_fvg_state[sym]['allow_buy']}, sell={daily_fvg_state[sym]['allow_sell']}")
                            eligible_pairs.append(p)
                    logger.info(f"Scanning {len(eligible_pairs)} eligible symbols out of {len(PAIRS)}")
                    
                    last_scan = False
                    
            for p in eligible_pairs:
                try:
                    handle_symbol(p)
                    time.sleep(0.15)
                except Exception as e:
                    logger.exception(f"{p['symbol']} | Error in handle_symbol: {e}")
            if len(eligible_pairs) == 0:
                logger.info("No eligible pairs from daily bias. Skipping cycle.")
                continue
                    
            process_signal_queue()
            # small sleep to avoid rate-limit bursts
            time.sleep(0.2)

    except KeyboardInterrupt:
        logger.info("Stopped by user (KeyboardInterrupt). Final balance: ${:.4f}".format(balance))


if __name__ == "__main__":
    main()
