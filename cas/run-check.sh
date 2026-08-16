#!/usr/bin/env bash
set -uo pipefail
cd "$(dirname "$0")"
# Shared robust gating: gp -q exits 0 even on error() on this build, so gate on the OUTPUT tally.
# (cas-gate.sh is vendored under ../tooling from the formal-verification harness.)
source "$(cd .. && pwd)/tooling/cas-gate.sh"
# Glob so new witnesses (NN_<topic>.gp) are picked up automatically, in numeric order.
shopt -s nullglob
witnesses=( [0-9][0-9]_*.gp )
if [[ ${#witnesses[@]} -eq 0 ]]; then
  echo "cas: no witnesses registered yet"
  exit 0
fi
cas_gate "${witnesses[@]}"
