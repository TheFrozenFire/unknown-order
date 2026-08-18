#!/usr/bin/env bash
# Print Assumptions snapshot for this tree (every Theorem/Lemma/…).
# Uses the harness runner against _CoqProject and the rocq-lsp compiler.
set -euo pipefail
cd "$(dirname "$0")"
ROOT="$(cd .. && pwd)"
FV="$(cd "$ROOT/../formal-verification" && pwd)"
if [[ ! -x "$FV/tooling/print-assumptions-snapshot" ]]; then
  echo "print-assumptions: harness tooling not found — SKIP"
  exit 0
fi
export ROCQ_DIR="$PWD"
export ROCQ_MODULE=UnknownOrder
export PA_FROM_COQPROJECT=1
export PA_TIMEOUT="${PA_TIMEOUT:-180}"
export COQC="${COQC:-opam exec --switch=rocq-lsp -- rocq compile}"
exec bash "$FV/tooling/print-assumptions-snapshot" "$@"
