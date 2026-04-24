import os
import time
from pybit.unified_trading import HTTP

# === CONFIG ===
API_KEY = os.getenv("BYBIT_API_KEY")       # or replace with "your_key"
API_SECRET = os.getenv("BYBIT_API_SECRET") # or replace with "your_secret"

COIN = "USDT"
FROM_ACCT = "6"  # UNIFIED trading
TO_ACCT = "7"    # Funding

CHECK_INTERVAL = 3600  # check once every hour

# === INIT SESSION ===
session = HTTP(testnet=False, api_key=API_KEY, api_secret=API_SECRET)

# === STATE VARIABLES ===
siphon_start = 10.0  # start siphoning when balance >= $10
current_threshold = siphon_start

def get_balance():
    """Return current USDT balance on the trading account."""
    resp = session.get_wallet_balance(accountType="UNIFIED", coin=COIN)
    return float(resp["result"]["list"][0]["coin"][0]["walletBalance"])

def has_open_trades():
    """Check if there are any open positions on the trading account."""
    resp = session.get_positions(category="linear", symbol="TRXUSDT")  # Replace symbol if needed
    for pos in resp["result"]["list"]:
        if float(pos["size"]) > 0:  # any open position
            return True
    return False

def siphon_amount(balance):
    """Calculate 25% siphon amount from balance."""
    return round(balance * 0.25, 6)

def transfer_to_fund(amount):
    """Execute internal transfer from trading to funding account."""
    transfer_id = f"transfer_{int(time.time())}"
    try:
        resp = session.create_internal_transfer(
            transferId=transfer_id,
            coin=COIN,
            amount=str(amount),
            fromAccountType=FROM_ACCT,
            toAccountType=TO_ACCT
        )
        print(f"Siphoned {amount} {COIN} to fund account. Response: {resp}")
    except Exception as e:
        print("Error during transfer:", e)

# === MAIN LOOP ===
print("Starting hourly balance monitor with open-trade check...")
while True:
    try:
        balance = get_balance()
        open_trades = has_open_trades()
        print(f"Current balance: {balance} USDT | Next threshold: {current_threshold} USDT | Open trades: {open_trades}")

        if balance >= current_threshold and not open_trades:
            amount_to_siphon = siphon_amount(balance)
            transfer_to_fund(amount_to_siphon)
            # Update threshold: double previous threshold
            current_threshold *= 2

        time.sleep(CHECK_INTERVAL)
    except Exception as e:
        print("Error in main loop:", e)
        time.sleep(CHECK_INTERVAL)

  
