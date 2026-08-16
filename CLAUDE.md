# unknown-order — operating rules

This project formalizes **computational problems in groups of unknown order**. It applies the
`formal-verification` harness's disciplines to a pure-mathematics / algorithmic domain instead of
smart contracts. Read these before adding a definition, a proof, or a witness.

## Where work goes (three layers)

- **Reusable, problem-agnostic number theory → `../rocq-proofs/`.** Anything that is not specific
  to one problem (gcd / Euler totient / Carmichael λ facts, a group-of-unknown-order axiom, a
  splitting lemma used by more than one algorithm) belongs in the shared library, where the next
  problem inherits it. You have ownership of that repo. Prefer a new focused file (e.g.
  `NumberTheory.v`) over stuffing `GroupTheory.v` — that file is an abstract finite-group
  signature aimed at Coxeter / tiling work, not `(ℤ/Nℤ)*`.
- **Problem-specific model + proofs → `rocq/<Problem>.v`.** Instantiate the library; don't
  re-derive. First file: `rocq/RSA.v`.
- **Numerical witnesses → `cas/NN_<topic>.gp`.** One concern per file, numbered.
- Keep this repo target-free of anything reusable: if you prove the same lemma for a second
  problem, that is the signal to lift it into `rocq-proofs`.

This is a **dedicated theory repo**, not a contract target. Work lives at the repo root
(`rocq/`, `cas/`), the same layout as `ciphering`. Do not introduce a
`formal-verification/` subtree.

## Core disciplines

1. **Cross-confirm (≥2 tools that fail differently).** Every headline property is proven in Rocq
   (holds for all inputs of the modeled object) **and** witnessed in PARI/GP (holds on concrete
   inputs an independent tool computed). Rocq can be vacuously green about the wrong object; CAS
   catches that. Name both in the crosswalk (README) for each property.

2. **A green result is not a proof until you know what it constrained.** Run `Print Assumptions` on
   every headline theorem; it must be *Closed under the global context* (0 axioms) unless an axiom
   is deliberately disclosed in the statement. A theorem that closed suspiciously fast is the prime
   suspect for vacuity — e.g. a `vm_compute; reflexivity` that would pass no matter what the
   definition said. Pin the same concrete case in CAS so the two must agree.

3. **Model the real object.** Integer / modular reality, not a convenient real-number stand-in.
   Residues, exact `ed − 1` splitting, the precise modulus of `d` (λ(N) vs φ(N)), the exact
   success condition of a randomized splitting step — model them as they are. The CAS witness
   reproduces the low-level operation (`Mod`, `gcd`, `znorder`, floor division) exactly, not the
   idealized math.

4. **State intent-derived properties, not only definitional ones.** "`d` is an inverse of `e` mod
   λ(N)" is definitional; "knowledge of `(e, d)` lets an algorithm output `{p, q}`" is
   intent-derived and is where the *cryptanalytic* content lives. Prove the reductions, not just
   the mechanics of modular exponentiation.

5. **Honest closure (never let a headline outrun its theorem).** Say exactly what a proof
   establishes: existence vs construction, deterministic vs Monte-Carlo, success probability vs
   worst-case, λ(N) vs φ(N), one algorithm vs the whole family. A randomized factoring procedure
   that succeeds on a positive-density set of coins is not "N is factored."

6. **Record why a tier was skipped.** Certora, Halmos, and the Rocq equivalence (Gallina ↔ solc-Yul)
   tiers are EVM-bound and skipped-by-construction. CAS + Rocq-SIM are the two differently-failing
   tools that satisfy the cross-confirm rule. An SMT track (as in `ciphering`) is optional and
   earned when a proof takes a premise that should be *searched* rather than assumed.

## Toolchain

- **Rocq 9.1** (`rocq compile` / `coqc`), stdlib namespace `From Stdlib Require Import`. Build flag
  `-native-compiler no`. The Coq 8.20.1 pin is equivalence-tier-scoped (rocq-of-solidity `.vo`);
  this SIM-only target does not take it. The proofs depend on `../rocq-proofs`
  (`-R ../../rocq-proofs RocqProofs`); `rocq/run-check.sh` builds it first.
- **PARI/GP** (`gp`). Gate witnesses through `tooling/cas-gate.sh` — `gp -q` exits 0 even on
  `error()`, so the gate inspects output, not the exit code. Multi-line `for(...)` loops need
  trailing `\` continuations (this build parses a bare newline inside the loop as end-of-input).
- `bash run-check.sh` runs both; each track SKIPs cleanly if its tool is absent.

The one local Rocq toolchain is the opam `rocq-lsp` switch (same one `rocq-mcp` / pet uses).
`rocq/run-check.sh` selects `opam exec --switch=rocq-lsp -- rocq compile` so `.vo` artifacts stay
readable by the interactive server. Do not invoke a bare PATH `coqc` (the pacman build clobbers
pet's `.vo`).

## Rocq style (matches rocq-proofs/PROOF_STYLE.md)

- `From Stdlib Require Import`; open `Z_scope`; `(** * *)` / `(** ** *)` section headers.
- Descriptive hypothesis names (`Hn`, `Hp`, `Hq`, `Hcoprime`, `Hinv`), never `H0`/`H1`.
- `Set Default Proof Using "Type"` is the library default — but omit it (with a note) in files whose
  sections carry *hypotheses used selectively*, or a blanket setting attaches unused premises to
  every lemma and spawns spurious side goals downstream.
