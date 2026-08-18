#!/usr/bin/env bash
# Generate coverage TOC, named-skip inventory, and math lint from the
# Rocq tree.  Writes ../generated/{COVERAGE,NAMED_SKIPS,LINT}.md.
# Optional: CHECK=1 diffs against the committed copies (CI drift).
set -euo pipefail
cd "$(dirname "$0")"
ROOT="$(cd .. && pwd)"
OUT="$ROOT/generated"
FV="$(cd "$ROOT/../formal-verification" && pwd)"
if [[ ! -x "$FV/tooling/coverage-toc" ]]; then
  echo "coverage: harness tooling not found at $FV/tooling — SKIP"
  exit 0
fi
mkdir -p "$OUT"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
bash "$FV/tooling/coverage-toc" --rocq-dir "$PWD" -o "$tmp/COVERAGE.md"
bash "$FV/tooling/named-skips"  --rocq-dir "$PWD" -o "$tmp/NAMED_SKIPS.md"
set +e
bash "$FV/tooling/rocq-math-lint" --rocq-dir "$PWD" -o "$tmp/LINT.md"
lint_rc=$?
set -e
if [[ "${CHECK:-0}" == "1" ]]; then
  drift=0
  for f in COVERAGE.md NAMED_SKIPS.md LINT.md; do
    if ! diff -q "$OUT/$f" "$tmp/$f" >/dev/null 2>&1; then
      echo "coverage: DRIFT $f"
      diff -u "$OUT/$f" "$tmp/$f" || true
      drift=1
    fi
  done
  if [[ $drift -ne 0 ]]; then
    echo "coverage: regenerate with bash rocq/gen-coverage.sh and commit" >&2
    exit 1
  fi
  echo "coverage: generated files match"
else
  cp "$tmp/COVERAGE.md" "$tmp/NAMED_SKIPS.md" "$tmp/LINT.md" "$OUT/"
  echo "coverage: wrote $OUT/{COVERAGE,NAMED_SKIPS,LINT}.md"
fi
if [[ $lint_rc -ne 0 ]]; then
  echo "coverage: math lint reported hits (see $OUT/LINT.md)" >&2
  exit 1
fi
