#!/usr/bin/env python3
"""Retarget the campaign pin_* alias to a frozen pin.

Frozen pins live in Pin.v / cas/lib/pin.gp as pin187_*, pin1363_*,
pin2491_*.  This script rewrites only the CAMPAIGN_ALIAS_BEGIN …
CAMPAIGN_ALIAS_END blocks.  Accident theorems pointed at pin187_*
are not touched.
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PIN_V = ROOT / "rocq" / "Pin.v"
PIN_GP = ROOT / "cas" / "lib" / "pin.gp"

# (p, q) → frozen prefix
PINS = {
    (11, 17): "pin187",
    (29, 47): "pin1363",
    (47, 53): "pin2491",
}


def retarget(text: str, prefix: str, begin: str, end: str) -> str:
    m = re.search(
        rf"({re.escape(begin)}.*?\n)(.*?)({re.escape(end)})",
        text,
        re.S,
    )
    if not m:
        raise SystemExit(f"alias block {begin} … {end} not found")
    body = m.group(2)
    body2, n = re.subn(r"\bpin(?:187|1363|2491)_", prefix + "_", body)
    if n == 0:
        raise SystemExit(f"no frozen-pin names to retarget in {begin} block")
    # Header comment / GP marker records the current prefix.
    head = re.sub(r"pin(?:187|1363|2491)\b", prefix, m.group(1), count=1)
    return text[: m.start()] + head + body2 + m.group(3) + text[m.end() :]


def main():
    if len(sys.argv) != 3:
        sys.stderr.write("usage: swap_pin.py P Q\n")
        sys.stderr.write("known pins: " + ", ".join(f"{p}×{q}" for p, q in PINS) + "\n")
        raise SystemExit(2)
    p, q = int(sys.argv[1]), int(sys.argv[2])
    prefix = PINS.get((p, q))
    if prefix is None:
        known = ", ".join(f"{a}×{b}→{pre}" for (a, b), pre in PINS.items())
        raise SystemExit(f"no frozen pin for {p}×{q}; known: {known}")
    PIN_V.write_text(retarget(PIN_V.read_text(), prefix, "CAMPAIGN_ALIAS_BEGIN", "CAMPAIGN_ALIAS_END"))
    PIN_GP.write_text(retarget(PIN_GP.read_text(), prefix, "CAMPAIGN_ALIAS_BEGIN", "CAMPAIGN_ALIAS_END"))
    print(f"campaign alias → {prefix} (N={p * q})")


if __name__ == "__main__":
    main()
