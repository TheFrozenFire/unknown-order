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

## 2.8 2-primary structure of `(ℤ/Nℤ)*` ✅ (cyclicity named, not proved)

- ✅ `v₂(p−1)` including the mod-8 table; `v₂(λ) = max`; `v₂` is a valuation
- ✅ Four constructed square roots of 1; mixed roots split `N`
- ✅ 2-height exists; same-`t` under `cyclic_units`; mismatch splits `N`
- ✅ Miller-from-`d` is that corollary (`MillerHeight`)
- ✅ Cyclic-model mismatch rates, including 150/158 (`CyclicCount`)
- ✅ KeyGen rulers: Blum, unbalanced, matched-deep, both-deep
- ✅ CAS mismatch counts match the formula on `(1,4)`, `(1,1)`, `(3,3)`
- ⬜ Cyclicity of `(ℤ/pℤ)*` itself; `height_stable_under` without it

## 2.9 Shape of `λ`, Type B vs adaptive root ✅ (with named skips)

- ✅ Forced `1 (mod 2^d)` is both-deep; independent / nextprime / safe are not (`cas/21`)
- ✅ Lucas `V` recurrence + doubling table; Williams handle is `cyc2`
- ✅ Adaptive root = sRSA; `λ+1` trivializes it on `(ℤ/Nℤ)*`; no `discriminant_to_lambda`
- ⬜ Lucas addition formula; QNR ⇒ `V_{p+1} ≡ 2` as a theorem — **month 1 week 2**
- ⬜ Class-group arithmetic — **month 2** (named presentation `Cl(Δ)`)

## 3. Three-month wave: presentations, not another RSA file ⬜

RSA is a worked example. The next wave adds theorems that are **not about `N = pq`**,
or proves a known `(ℤ/Nℤ)*` fact hard enough that we can see whether that theorem is
true, false, or presentation-dependent.

Second incarnation: imaginary-quadratic class groups `Cl(Δ)`. Consumer: algebra of a
proof of exponentiation (Wesolowski / Pietrzak), not a sequentiality game.

Elliptic curves, lattices, LLL, PPT, and Factoring ≤ RSA stay out.

### 3.0 Success is five sentences, two instantiations

A “theorem” that only holds for `N = pq` stays in an RSA file. If it holds for both
carriers, it is lifted to the shared set (sibling `rocq-proofs` when it mentions
neither `N` nor `Δ`).

| Sentence | `(ℤ/Nℤ)*` | `Cl(Δ)` |
|---|---|---|
| Units have an order, which divides every annihilator | week 1 | week 8 (once composition is there) |
| Low-order for `B = 2` is a public construction | no (needs factors, except `−1`) | week 6 (ambiguous forms) |
| Adaptive root is trivial from public data | yes (`λ+1`) | no |
| A Wesolowski proof is an `ℓ`-th root | week 10 | week 10 |
| A Pietrzak forgery is low-order | week 10, and may be `±1` | week 10, and may be *constructible* 2-torsion |

The last row is the edge most likely to be “the well was not dry”: Pietrzak stated on
`Cl(Δ)` without excluding `Cl[2]` is a break of unrestricted `Problem_LowOrder` using
only the discriminant.

### 3.1 Month 1 — Dry the first well ⬜

Package facts `(ℤ/Nℤ)*` has been using as comments, so `Cl(Δ)` can reuse them.

**Week 1 — Orders as objects.** `rocq/Order.v`; lift reusable bits to `rocq-proofs`.
- Existence of `is_order` for `a` coprime to `n > 1` (least annihilating exponent).
- `ord(a) | m` iff `a^m ≡ 1`; `ord(a^k) = ord(a) / gcd(ord(a), k)`.
- `lcm` of orders divides `λ` (`order_divides_lambda` already exists).
- Completeness (“enough random `a` generate `λ`”) stays a **named density
  hypothesis**, with CAS on 187 / 11×19 / 41×73.
- Outcome: Miller heights become `v₂(ord)` under that packaging, not only under
  `cyclic_units`.

**Week 2 — Lucas for real.** Finish `Lucas.v`; grow `cas/22`.
- Addition `V_{m+n} = V_m V_n − Q^n V_{|m−n|}`; doubling as a corollary.
- Williams handle: `cyc2` + `V_M ≡ 2 (mod p)` when `p+1 | M` and `P²−4` is a QNR,
  or a named Euler/QNR hypothesis if Gauss would swallow the week.
- CAS: more `(P, p)` pairs, including a safe prime with smooth `p+1`.
- Outcome: Type B at `n = 2` is an evaluation theorem. Shrinks §2.5 / §2.9 Lucas skips.

**Week 3 — 2-Sylow of `(ℤ/Nℤ)*` as a structure theorem.**
- Always exactly four solutions of `x² = 1`.
- An element of order 4 exists iff `v₂(λ) ≥ 2` (not Blum).
- Blum ⇔ 2-torsion is exactly `{±1}²` via CRT.
- Connect to Rabin: four roots of a square are the four `√1` translates.
- Outcome: `kg_blum_2adic` is a theorem about the 2-Sylow, not a KeyGen flag.

**Week 4 — Same-`t` without a cyclicity axiom, as far as Fermat goes.**
- `height_stable_under` when `odd_part(p−1) | t` and `t` odd, using `ord | p−1`
  (Fermat + week 1), not `cyclic_units`.
- `cyclic_units` remains only for *counts*.
- Outcome: `cyclic_same_t` becomes a theorem; the named hypothesis is pushed back
  to density / `CyclicCount`.

Named skips this month: cyclicity of `(ℤ/pℤ)*`, `(2/p)`, Pratt trees, LLL.

### 3.2 Month 2 — Second incarnation: `Cl(Δ)` ⬜

Same winning conditions on a group whose public data is a discriminant, not a
modulus. Do **not** formalize a class-number algorithm. Do formalize the forms you
can write down from `Δ`.

**Week 5 — Primitive forms.** `rocq/BinForms.v`; lift the type if it stays
presentation-agnostic.
- `form = (a, b, c)` with `b² − 4ac = Δ`, `gcd(a,b,c) = 1`, `Δ < 0`,
  `Δ ≡ 0 or 1 (mod 4)`.
- Reduction, identity form, inverse `(a, −b, c)`.
- Composition at least for the identity and inverses; full Dirichlet composition
  if it stays elementary. No Bhargava cubes.

**Week 6 — Ambiguous forms are public order-2 elements.**
- Order dividing 2 ⇔ equivalent to an ambiguous form (`b = 0`, `a = b`, or `a = −b`).
- Construct them from the prime factorization of `Δ`.
- Those elements win unrestricted `Problem_LowOrder` for `B = 2`.
- CAS `23_class_group.gp`: `Δ ∈ {−23, −47, −87, −403, −455}`; reduced forms,
  order-2 classes, 2-rank vs number of distinct odd prime factors.

**Week 7 — Restricted low-order, and which arrows die.**
- `Problem_LowOrderOutside H`: order `≤ B` and not in constructible `H`.
- On `(ℤ/Nℤ)*`, `H = {1}` or `{±1}`. On `Cl(Δ)`, `H = Cl[2]`.
- Adaptive root and order keep the same *relation* on a different carrier;
  `lambda_solves_strong_RSA` has **no** analogue.
- Rewrite `ClassGroupWall.v` into these theorems. Replace “no period from `Δ`”
  with “no odd annihilator from `Δ`; the 2-annihilator is public.”

**Week 8 — Same mechanics, no modulus.**
- `Problem_Order`, `Problem_AdaptiveRoot` on forms (exponentiation = repeated
  composition).
- One-sided low-order / CRT splitting has **no** analogue. Record the missing
  arrow; do not prove `False`.
- CAS: exhaustive order of every reduced form on the week-6 discriminants;
  odd orders are not 2-power; no `λ+1`-style witness derived from `Δ`.

Named skips this month: computing `h(Δ)`, Hilbert class field, real-quadratic
fields, anything above 2-primary in `Cl`.

### 3.3 Month 3 — Shared carrier, then a consumer that is not a cryptosystem ⬜

Stop saying “the same relation.” Write the relation once. Then run a
protocol-shaped object that uses root extraction the way RSA and RW do.

**Week 9 — `Presentation.v`.**
- Carrier, multiplication, identity, inverses on a named subset of units.
- `constructible_torsion`; `public_annihilator` (`Some λ` / `None` / `Some 2`).
- Problems: `Root e y`, `AdaptiveRoot y`, `Order a`, `LowOrder B`,
  `LowOrderOutside B`.
- Sentences 1–3 instantiated on `rsa_presentation` and `cl_presentation`.
- Lift only lemmas that mention neither `N` nor `Δ`.

**Week 10 — Proof of exponentiation, algebra only.** `rocq/ExpProof.v`,
`cas/24_exp_proof.gp`.
- Wesolowski: a correct `π` is an `ℓ`-th root; a wrong verifying `π` is an
  adaptive-root witness.
- Pietrzak: a bad midpoint yields an element of 2-power order (low-order, not
  adaptive root).
- Run both on `(ℤ/Nℤ)*` with known `λ` (Wesolowski trivial; Pietrzak hits
  `{±1}` or a 2-power) and on a toy `Cl(Δ)` (Pietrzak must not count
  ambiguous forms as a break of the *restricted* assumption).
- Sequentiality, random oracles, and “this is a VDF” stay named.

**Week 11 — Accumulator membership as the RSA-shaped map.** `rocq/Accumulator.v`.
- `A ↦ A^x`. A membership witness is a root. A forged witness for a non-member,
  given a random base, is adaptive root / strong RSA.
- Instantiated on `rsa_presentation`; stated on `cl_presentation` (no trapdoor
  to update with `λ`).
- Hash-to-prime is a named skip. No pairings, no Merkle.

**Week 12 — Close the loop and write the edges.**
- `THEORY.md` §14–16: presentations; constructible torsion; PoE algebra.
- `Print Assumptions` on every new headline theorem. Anything that still
  mentions `cyclic_units`, QNR, or “forms compose associatively” is listed.
- This section becomes a table of incarnations × winning conditions × which
  arrows exist.
- One CAS gate over `23`–`24` plus `01`–`22`.

### 3.4 Refused this wave (named, not pursued as formalization)

- Boneh–Durfee, Coron–May, ROCA, Franklin–Reiter as LLL developments.
- Another undirected KeyGen sampler pass. §6.11 stays a hunt with a *named*
  distribution, not a month.
- Gauss’s lemma for `(2/p)` unless week 2 is blocked on it.
- A `Problem_UFO` record with no construction.
- Anything whose first sentence is “assume a random oracle” or “assume
  sequentiality.”
- Higher-degree class groups; Paillier / `N²` except as a one-line neighbour
  (order is `N φ(N)`, so it is not unknown-order in the same sense).

## 4. Cryptanalysis direction (from this foundation)

The rulers in `rocq/` say when a generation distribution has leaked. The hunt is for a
distribution that honest-looking keygens still use, that is *not* a row of the catalog, and
that still produces a Type A–E handle cheap enough that a smaller `N` would feel it. See
`THEORY.md` §6.11. Not a month of §3 unless a named modern sampler is on the table.
