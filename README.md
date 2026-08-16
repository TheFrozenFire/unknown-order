# unknown-order

Computational problems in **groups of unknown order**, formalized the way you'd verify a smart
contract: every claim that matters is machine-checked, and checked by **two tools that fail
differently** so that agreement between them is evidence rather than an artifact of one setup.

The first object is the **RSA problem** on `(ℤ/Nℤ)*` with `N = pq`: the public exponent `e`, the
private exponent `d`, and the algorithms that recover `{p, q}` from knowledge of `(N, e, d)`. Some
of those algorithms are deterministic; some are randomized. The definitions of both kinds are the
first work.

## The method: cross-confirmation across independent tools

| Tool | Proves | Fails differently because |
|------|--------|---------------------------|
| **Rocq** (Coq 9.1) | Theorems about a Gallina model — for *all* inputs | deductive; a wrong model, or a wrong *premise*, still proves cleanly |
| **CAS** (PARI/GP) | Concrete numerical witnesses on sampled / exhaustive inputs | third-party arithmetic computed *forward*; catches a wrong model, proves nothing universal |

A property is only "understood" here when Rocq proves it in general **and** a PARI/GP witness pins
it on concrete numbers. Rocq proves *the property holds for the modeled object*; CAS is insurance
that *the modeled object is the right object*. See [`THEORY.md`](THEORY.md) for the mathematics and
[`CLAUDE.md`](CLAUDE.md) for the working discipline.

EVM-bound tiers (Certora, Halmos, Rocq Gallina↔Yul equivalence) are skipped-by-construction: there
is no bytecode. An SMT track can be added later if a proof takes a premise that should be searched
rather than assumed (the lesson `ciphering` learned on wide-trail bounds).

## Layered across three repos

- **[`rocq-proofs`](https://github.com/TheFrozenFire/rocq-proofs)** — reusable, problem-agnostic
  algebra. Facts that a second unknown-order problem would also need are lifted here.
- **`unknown-order`** (this repo) — RSA (and later siblings) as instantiations, plus the CAS
  witnesses.
- **[`formal-verification`](https://github.com/TheFrozenFire/formal-verification)** — the harness
  whose methodology (cross-confirm, no-vacuity, honest closure) this project applies. Setup
  follows the sibling **[`ciphering`](https://github.com/TheFrozenFire/ciphering)** repo, the last
  place this method was applied to a pure-theory target.

## What's proven so far

Nothing yet. The tree is a scaffold: `rocq/RSA.v` is a documented empty module, `cas/` has no
witnesses, the runners are wired and green. The claim → tools matrix will be filled as definitions
land. Planned first row, status empty:

| Property | Rocq | CAS | Status |
|----------|------|-----|--------|
| RSA instance `(N, e, d)` and the private exponent `d` | `rocq/RSA.v` | `cas/01_*.gp` | scaffolded |
| Factoring `N = pq` given `(e, d)` — deterministic algorithms | `rocq/RSA.v` | `cas/NN_*.gp` | scaffolded |
| Factoring `N = pq` given `(e, d)` — randomized algorithms | `rocq/RSA.v` | `cas/NN_*.gp` | scaffolded |

## Run it

```sh
bash run-check.sh          # CAS (gp) + Rocq (rocq compile) — each SKIPs cleanly if its tool is absent
```

Requires PARI/GP (`gp`) for the CAS track and Rocq 9.1 for the proofs. The Rocq track builds the
sibling `../rocq-proofs` library automatically; clone it beside this repo:

```sh
git clone https://github.com/TheFrozenFire/rocq-proofs   # beside unknown-order/
```

## Where this is going

See [`ROADMAP.md`](ROADMAP.md). First: RSA's definition, `d`, and the factoring algorithms that
take `(e, d)` as input. After that, the other standard problems in groups of unknown order, under
one abstraction where they share one.
