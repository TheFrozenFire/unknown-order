#!/usr/bin/env bash
set -uo pipefail
cd "$(dirname "$0")"

# --- Toolchain selection -----------------------------------------------------------------------
# There is ONE local Rocq toolchain: the opam `rocq-lsp` switch (OCaml 5.2.1), the SAME one that
# rocq-mcp/pet uses.  Building here therefore produces exactly the .vo that pet loads — no more
# opam-vs-pacman .vo clobber (the two OCaml builds emit mutually-unreadable .vo into shared dirs).
#
# NOTE: the rocq-lsp switch ships `rocq` but NOT its own `coqc`, so a bare `coqc` (even under
# `opam exec`) silently resolves to the system/pacman binary and reintroduces the clobber.  We must
# invoke `rocq compile`.  Selection order:
#   1. $COQC set explicitly            -> honor it (word-split; power users / CI images)
#   2. opam `rocq-lsp` switch present  -> `opam exec --switch=rocq-lsp -- rocq compile`  (default)
#   3. `rocq` on PATH                  -> `rocq compile`
#   4. `coqc` on PATH                  -> `coqc`  (last resort; may clobber pet's .vo)
#   5. none                            -> SKIP (exit 0)
if [[ -n "${COQC:-}" ]]; then
  read -r -a RC <<< "$COQC"
  TOOL_DESC="\$COQC override: $COQC"
elif opam switch list --short 2>/dev/null | grep -qx 'rocq-lsp' \
     && opam exec --switch=rocq-lsp -- sh -c 'command -v rocq >/dev/null 2>&1'; then
  RC=(opam exec --switch=rocq-lsp -- rocq compile)
  TOOL_DESC="opam rocq-lsp switch (rocq compile) — matches rocq-mcp/pet"
elif command -v rocq >/dev/null 2>&1; then
  RC=(rocq compile)
  TOOL_DESC="rocq compile (PATH)"
elif command -v coqc >/dev/null 2>&1; then
  RC=(coqc)
  TOOL_DESC="coqc (PATH) — WARNING: if this is pacman-built it clobbers pet's opam .vo"
else
  echo "rocq: no rocq/coqc toolchain found — SKIP"; exit 0
fi
echo "[rocq] toolchain: $TOOL_DESC"

# The proofs depend on the RocqProofs library (sibling repo ../../rocq-proofs). Build its .vo
# artifacts first so `Require Import RocqProofs.*` resolves, then compile ours.
DEP="../../rocq-proofs"
if [[ ! -d "$DEP" ]]; then
  echo "rocq: dependency $DEP not found — clone TheFrozenFire/rocq-proofs beside this repo — SKIP"
  exit 0
fi

fail=0
echo "[rocq] building RocqProofs dependency"
while IFS= read -r f; do
  if ! "${RC[@]}" -R "$DEP" RocqProofs -native-compiler no "$DEP/$f" >/tmp/uo_dep.log 2>&1; then
    echo "  FAIL (dep): $f" >&2; cat /tmp/uo_dep.log >&2; fail=1; break
  fi
done < <(grep -E '\.v$' "$DEP/_CoqProject")

if [[ $fail -eq 0 ]]; then
  while IFS= read -r f; do
    printf '[rocq] %s\n' "$f"
    if ! "${RC[@]}" -R . UnknownOrder -R "$DEP" RocqProofs -native-compiler no "$f" >/tmp/uo.log 2>&1; then
      echo "  FAIL: $f" >&2; cat /tmp/uo.log >&2; fail=1; break
    fi
  done < <(grep -E '\.v$' _CoqProject)
fi

if [[ $fail -eq 0 ]]; then echo "rocq: compiled"; else exit 1; fi
