# Groups of unknown order — policy, not the map

This file is **not** the theory.  The theory is the Rocq tree.

| What you want | Where it lives |
|---|---|
| Table of contents (every section, every theorem) | [`generated/COVERAGE.md`](generated/COVERAGE.md) |
| Named skips (refuses and weaknesses) | [`generated/NAMED_SKIPS.md`](generated/NAMED_SKIPS.md) |
| Math/SIM lint | [`generated/LINT.md`](generated/LINT.md) |
| Paper-check overlaps | [`notes/paper-overlaps.md`](notes/paper-overlaps.md) |
| Relation table | [`notes/hardness.md`](notes/hardness.md) |
| Working rules | [`AGENTS.md`](AGENTS.md) |

Regenerate the first three with `bash rocq/gen-coverage.sh` (also run from `run-check.sh`).  The harness emitters are `formal-verification/tooling/{coverage-toc,named-skips,rocq-math-lint}`.

## What a group of unknown order is

The group operation is public.  The order is not.  RSA, strong RSA,
adaptive root, order, and low-order are the same *winning conditions*
on different carriers (`(ℤ/Nℤ)*`, `Cl(Δ)`, the Williams torus).
Those conditions are `Problem_*` in `UnknownOrder.v` / `Hardness.v` /
`Presentation.v`.  None of them is assumed hard.

A hardness *claim* needs a named KeyGen distribution and a class of
algorithms.  This corpus records **relations** (which witnesses exist)
and **refuses** PPT/advantage (`Refuse_PPT_advantage`).

## How gaps are recorded

Rocq has no “we will not prove this” keyword.  Comments are invisible
to `Print Assumptions`.

- `Definition foo_named : Prop` **unused** → refuse
- `Definition foo_named` taken as a **hypothesis** → weakness
- `NamedRefuse` constructor → refuse that is not a proposition
- `Axiom` / `Admitted` → load-bearing trust (this tree has none)

See `rocq/NamedSkips.v` and `rocq-proofs/PROOF_STYLE.md` §5.1.

## What must not be axiomatized

Do not close a “security” proof by assuming any of the following.
They are `NamedRefuse` constructors, not axioms.

- A global `RSA_hard` / `Factoring_hard` / `sRSA_hard`
- Decisional RSA on units with `gcd(e, λ) = 1`
- Standard-model RSA ≡ factoring (`Refuse_RSA_eq_factoring_standard_model`);
  AM09 is generic-ring (`Refuse_AM09_generic_ring_as_standard_model`)
- ROM, SHA-in-Rocq, PPT/advantage, NFS cost
- LLL / Coppersmith *development* (`Refuse_lattice_lll_development`);
  the algebraic use of a recovered `φ` is a theorem
- An undirected §6.11 hunt (`Refuse_undirected_611_hunt`)
- Elliptic-curve or lattice *branching* of this corpus
- FO/DF simulation, pairing accumulators, “this is a VDF”

## How to read a headline

`Print Assumptions` on a headline of this tree is Closed under the
global context unless the statement *takes* a `*_named` hypothesis.
A Closed theorem that does not take a named hyp is not “missing an
axiom.”  It is the honest scope.

Until a claim has a Rocq theorem **and** a CAS witness, it is a
design target, not a fact.
