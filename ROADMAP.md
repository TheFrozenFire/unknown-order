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

## 2.6 Hardness claims as theory, not axioms ✅ (relations only)

- ✅ Search problem ≠ assumption; four ingredients of a claim (`THEORY.md` §9)
- ✅ `e`-power map is a permutation of units (`Hardness.rsa_units_are_eth_powers`; `cas/18`)
- ✅ Trapdoor inverts RSA; RSA solution is sRSA at that `e`; `λ` trivializes sRSA
- ✅ Order divides `λ`; one-sided low-order factors; two-sided does not
- ✅ Decision neighbours (QR, Φ-hiding, DCR) recorded as *not* RSA
- ⬜ Probability / PPT / advantage (not a design target without a named `KG`)
- ⬜ Factoring ≤ RSA (open; not a target)
- ❌ Global axiom `RSA_hard` — refused (§9.10)

## 2.7 Rabin–Williams (same group, different map) ✅ (with named skips)

- ✅ `e = 2` is not an RSA exponent (`two_not_rsa_exponent`); squaring is 4-to-1
- ✅ Blum / Williams prime shapes; `v₂(p−1) = 1`; `p≡3 (mod 4)` root formula
- ✅ Williams combinatorics: unique QR among `{±a, ±2a}` given the mod-8 symbols
- ✅ Rabin reduction: non-associated square roots split `N`
- ✅ Overlap written in `THEORY.md` §10; `rsa_test` primes are *not* a Williams pair
- ⬜ `(2/p)` as a theorem (Gauss); Euler QNR direction
- ⬜ Principal-root convention, hash wrapper, signature game

## 2.8 2-primary structure of `(ℤ/Nℤ)*` ✅ (counting under cyclicity is CAS)

- ✅ `v₂(p−1)` in the Blum / `≡1 (mod 4)` cases; Williams ⇒ `(1,1)`
- ✅ Four constructed square roots of 1; mixed roots split `N`
- ✅ 2-height; mismatched heights split `N` (Miller’s success condition)
- ✅ KeyGen rulers: Blum, unbalanced, matched-deep
- ✅ CAS mismatch counts match the cyclic formula on `(1,4)`, `(1,1)`, `(3,3)`
- ⬜ Cyclicity of `(ℤ/pℤ)*` as a Rocq hypothesis; `val2(lcm)=max` in general
- ⬜ Existence of a 2-height for every unit, packaged; Rocq density theorem

## 3. Other unknown-order problems ⬜

Only after RSA is a worked example and the shared skeleton is visible. Candidates (not a
commitment): strong RSA, adaptive root, order / low-order, class-group analogues. Each either
instantiates the existing abstraction or forces us to generalize it.

## 4. Cryptanalysis direction (from this foundation)

The rulers in `rocq/` say when a generation distribution has leaked. The hunt is for a
distribution that honest-looking keygens still use, that is *not* a row of the catalog, and
that still produces a Type A–E handle cheap enough that a smaller `N` would feel it. See
`THEORY.md` §6.11.
