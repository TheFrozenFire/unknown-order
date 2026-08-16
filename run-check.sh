#!/usr/bin/env bash
# Top-level cross-confirmation gate for the unknown-order project.
# TWO tracks that FAIL DIFFERENTLY (CLAUDE.md #1): CAS (PARI/GP forward computation) and Rocq
# (deductive proof). EVM tiers are skipped-by-construction. Each track SKIPs cleanly (exit 0)
# when its tool is absent; a present tool that FAILS exits non-zero.
set -uo pipefail
cd "$(dirname "$0")"

fail=0
echo "===================== CAS (PARI/GP) ====================="
bash cas/run-check.sh || fail=1
echo
echo "===================== Rocq (coqc) ======================="
bash rocq/run-check.sh || fail=1

echo
if [[ $fail -eq 0 ]]; then echo "unknown-order: all present tracks OK"; else echo "unknown-order: a track FAILED" >&2; exit 1; fi
