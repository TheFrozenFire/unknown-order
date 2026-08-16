# Roadmap

Status legend: ✅ done · ⬜ planned · 🔧 in progress · ⏸ blocked on analysis seed.

## 0. Scaffold ✅

Dedicated theory repo, ciphering-shaped: Rocq SIM + CAS, sibling `rocq-proofs` dependency, EVM
tiers skipped-by-construction.

## 1. RSA problem, private exponent, factoring from `(e, d)` ⏸

The first content. Paused until the prior-conversation seed is in.

- ⬜ RSA instance `(N = pq, e, d)` — including the definition of `d`
- ⬜ RSA problem (invert `x ↦ x^e (mod N)`)
- ⬜ Deterministic algorithms that output `{p, q}` given `(N, e, d)`
- ⬜ Randomized algorithms that output `{p, q}` given `(N, e, d)`
- ⬜ CAS witnesses that pin each algorithm on concrete `(N, e, d)`
- ⬜ Crosswalk row per algorithm: Rocq theorem + CAS file, with honest success statement

## 2. Lift what recurs into `rocq-proofs` ⬜

gcd / totient / Carmichael / splitting facts used by a second problem get lifted. Not before they
are used twice.

## 3. Other unknown-order problems ⬜

Only after RSA is a worked example and the shared skeleton is visible. Candidates (not a
commitment): strong RSA, adaptive root, order / low-order, class-group analogues. Each either
instantiates the existing abstraction or forces us to generalize it.
