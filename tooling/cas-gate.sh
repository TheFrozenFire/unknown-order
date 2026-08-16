#!/usr/bin/env bash
# Shared robust gating for PARI/GP CAS witnesses — the single source of truth for "did this witness
# pass?", so the footgun below is defended against ONCE rather than re-litigated per target.
#
# THE FOOTGUN (logged in .claude/skills/cas-witness/reference/runner.md): on this PARI/GP build,
# `gp -q file.gp` returns exit status 0 EVEN WHEN the script calls error() and aborts. So a run-check
# that gates purely on gp's exit code passes SILENTLY in CI even though the witness blew up — a false
# green. (Verified: error() emits `*** ... user error: ...` to stderr but the process exits 0.)
#
# THE FIX — inspect the OUTPUT, not the exit code. `cas_gate` fails (returns 1) on ANY of:
#   * a PARI error      — `*** ` or `user error`  → the script aborted (e.g. an error() call)
#   * a failure tally   — `FAIL` (per-probe, convention A) or `<n> fail` with n>0 (convention B)
#   * no pass output    — neither `ok`/`OK` nor an `<n> ok` tally appeared → script produced nothing
# and otherwise reports OK. It SKIPs cleanly (returns 0) when gp is absent, so CI hosts without
# PARI/GP stay green.
#
# Case sensitivity matters: convention B prints the word "fail" on EVERY run (e.g. "12 ok, 0 fail"),
# so the fail-grep is case-SENSITIVE (`FAIL` or `[1-9][0-9]* fail`) — "0 fail" matches neither.
#
# Usage:
#   source "<repo>/tooling/cas-gate.sh"
#   cas_gate witness1.gp [witness2.gp ...]    # cwd should hold the .gp files (cd "$(dirname "$0")")

cas_gate() {
  if ! command -v gp >/dev/null 2>&1; then echo "cas: gp (PARI/GP) not found — SKIP"; return 0; fi
  local fail=0 s out
  for s in "$@"; do
    if [[ ! -f "$s" ]]; then echo "==> $s   MISSING"; fail=1; continue; fi
    # </dev/null: on error() this gp build drops into interactive mode and would HANG waiting on
    # stdin (the footgun's second face — a broken witness hangs CI rather than failing it).
    out="$(gp -q "$s" </dev/null 2>&1)"
    echo "$out"
    if echo "$out" | grep -qE '\*\*\*|user error'; then
      echo "==> $s   FAIL (PARI error — script aborted before completing)"; fail=1; continue
    fi
    if echo "$out" | grep -qE 'FAIL|[1-9][0-9]* fail'; then
      echo "==> $s   FAIL (a witness probe reported failure)"; fail=1; continue
    fi
    if ! echo "$out" | grep -qiE '(^| )ok( |$)|[0-9]+ ok'; then
      echo "==> $s   FAIL (no pass output — wrong file or aborted with no probes)"; fail=1; continue
    fi
    echo "==> $s   OK"
  done
  echo
  if [[ $fail -ne 0 ]]; then echo "cas: failures present" >&2; return 1; fi
  echo "cas: $#/$# witness(es) OK"
  return 0
}
