# Roadmap

Status legend: ✅ done · ⬜ planned · 🔧 in progress · ⏸ blocked on analysis seed.

## 0. Scaffold ✅

Dedicated theory repo, ciphering-shaped: Rocq SIM + CAS, sibling `rocq-proofs` dependency, EVM
tiers skipped-by-construction.

## 1. RSA problem, private exponent, factoring from `(e, d)` ✅ (with named skips)

- ✅ RSA instance `(N = pq, e, d)` — `d ≡ e⁻¹ (mod λ(N))`; `φ` inverse is a separate hypothesis
- ✅ RSA problem as a proposition; enc/dec on units
- ✅ `M = ed − 1` annihilates `(ℤ/Nℤ)*`
- ✅ Multiplier enumeration / quadratic from `φ` or `p+q`
- ✅ Miller successive-squaring (witness ⇒ factor); density CAS-only on 187
- ✅ Sequential-base Miller defined + witnessed; ERH poly-time **not** claimed
- ⬜ Coron–May / LLL (interface only — `Lattice.v`)
- ✅ Miller–Rabin polarity (same engine)
- ✅ Pratt 2-torsion duality; full Pratt completeness ⬜
- ✅ CAS witnesses `01`–`07`

## 2. Lift what recurs into `rocq-proofs` ✅

`NumberTheory.v` holds `powm`, Euler/Carmichael for semiprimes, CRT, the quadratic, `√1` splitting, 2-adic split.

## 2.5 Key-generation leaks (the annihilator, without `d`) ✅ (with named skips)

Known weaknesses catalogued in `THEORY.md` §6–§7 and `notes/keygen-weaknesses.md`.
Each row is a generation choice that makes a *partial* or *short* annihilator public.

- ✅ Fermat / close primes — `FermatFactor`, `cas/08`
- ✅ Shared primes / batch GCD — `SharedPrime`, `cas/09`
- ✅ Pollard `p−1` as a one-sided annihilator — `PollardP1`, `cas/10`
- ✅ Safe primes refuse that annihilator — `StrongPrimes`; Williams `p+1` ⬜ (definition only)
- ✅ Wiener identities + basin — `Wiener`, `cas/11`; Boneh–Durfee / LLL ⬜
- ✅ Hastad cube / small `e` — `SmallExponent`, `cas/12`; Franklin–Reiter gcd ⬜
- ✅ CRT-RSA small `d_p` — `CRTRSA`, `cas/10`
- ✅ Unbalanced primes (`p ≤ √N`) — `KeyGen.small_prime_le_sqrt`, `cas/08`
- ✅ Keygen intent-spec + refusal lemmas — `KeyGen`
- ⬜ Bit leaks / ROCA as Coppersmith (`BitLeak` records the shape)
- ✅ Sampler of real-looking distributions vs the rulers — `KeyGenSampler`, `cas/13`
- ✅ Type B beyond `p±1` — `Cyclotomic`, `cas/14` (`p=653` is a strong-prime miss on `Φ_3`)
- ✅ Type D without a shared prime — `BatchOrder`, `cas/15`
- ✅ Type C past Wiener (sufficient `36 d⁴ < N`, CF frontier) — `Wiener`, `cas/16`; BD / LLL ⬜
- ✅ Type A geometries modern keygens commit — `KeyGenGeom`, `cas/17`
- ⬜ A new Type-A/B/C/D/E leak that current keygens actually commit *and that is not a row above* (the remaining cryptanalysis goal)

## 3. Other unknown-order problems ⬜

Only after RSA is a worked example and the shared skeleton is visible. Candidates (not a
commitment): strong RSA, adaptive root, order / low-order, class-group analogues. Each either
instantiates the existing abstraction or forces us to generalize it.

## 4. Cryptanalysis direction (from this foundation)

The rulers in `rocq/` say when a generation distribution has leaked. The hunt is for a
distribution that honest-looking keygens still use, that is *not* a row of the catalog, and
that still produces a Type A–E handle cheap enough that a smaller `N` would feel it. See
`THEORY.md` §6.11.
