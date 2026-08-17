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
- ✅ Lucas addition formula; QNR ⇒ `V_{p+1} ≡ 2` as a theorem — **month 1 week 2** (QNR direction CAS-pinned)
- ✅ Class-group arithmetic — **month 2** (named presentation `Cl(Δ)`)

## 3. Three-month wave: presentations, not another RSA file ✅

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

### 3.1 Month 1 — Dry the first well ✅

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

### 3.2 Month 2 — Second incarnation: `Cl(Δ)` ✅

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

### 3.3 Month 3 — Shared carrier, then a consumer that is not a cryptosystem ✅

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
`THEORY.md` §6.11. Not a month of §3 or §5 unless a named modern sampler is on the table.

## 5. Next three months: run the consumer, then a third presentation ⬜

§3 made RSA a worked example and `Cl(Δ)` a second carrier. What is still thin:
Dirichlet of two non-unit forms is named; Wesolowski / Pietrzak / the accumulator
are proved on `(ℤ/Nℤ)*` and stated on `Cl`; Williams `p+1` is a definition;
every “four `√1`” theorem is secretly two-prime.

This wave (1) dries the leftovers that block the consumer, (2) runs the consumer
on both existing carriers, (3) adds a third presentation whose order is
`lcm(p+1, q+1)`, not `λ`. Same refusals as §3.4 (no ECC, lattices, LLL, PPT,
`h(Δ)`, RO, sequentiality, Paillier, undirected §6.11).

### 5.0 Success is five sentences, three instantiations

| Sentence | `(ℤ/Nℤ)*` | `Cl(Δ)` | Williams torus mod `N` |
|---|---|---|---|
| Group law on the generators we use is a theorem | `powm` | id and inverse are theorems; two-form Dirichlet week 1 | Lucas addition already |
| A verifying Wesolowski `π` is an `ℓ`-th root *on the presentation* | done | week 5 | week 10 |
| A Pietrzak quotient is an element of order dividing 2 | week 6 | week 6; may be `Cl[2]` | week 11 |
| Type B is LowOrder / a one-sided annihilator on a named presentation | `p−1` on units | no | `p+1` on the torus (native) |
| A public integer built like `N+1` annihilates | `λ+1` does, if `λ` is known | no | **no**: torus order is `N+(p+q)+1` |

The last row is the edge most likely to not be dry. On the torus the public
guess `N+1` is *wrong*. If `p ≈ q`, Fermat leaks `p+q` and the torus order
becomes public — Type A on a different presentation, already in the catalog.

### 5.1 Month 1 — Dry what the consumer is standing on ⬜

**Week 1 — Two-form Dirichlet.** `BinForms.v`; grow `cas/23`.
- `compose_preserves_disc` when discs match and the existing `n`-formula applies:
  `4 a_new | (B²−Δ)`; primitivity if both inputs are primitive.
- Associativity named, or proved only for `{id, f, f⁻¹}`. No Bhargava cubes.
- Outcome: `bqf_exp` of an ambiguous form at `2` is equivalent to the identity
  without a catalog `vm_compute`.

**Week 2 — Williams as an evaluation, not a definition.** `Lucas.v`,
`StrongPrimes.v`; grow `cas/22`.
- Addition + doubling give `V_{k(p+1)} ≡ 2 (mod p)` from a named QNR/Euler
  hypothesis (`V_{p+1} ≡ 2`), not a new Gauss development.
- `pp1_resistant` becomes “the torus period is not `B`-smooth”.
- Outcome: Type B at `n = 2` is an evaluation theorem. Shrinks the §2.5 skip.

**Week 3 — Presentation grows an inverse.** `Presentation.v`; `MultiPrime.v`.
- Add `Pinv`. RSA: inverse on units. `Cl`: `bqf_inv`.
- Laws: `Pexp (S n) = Pmul a (Pexp n)`, `Pexp 0 = id`, `Pmul a (Pinv a) ~ id`.
- Multi-prime stress test: `N = pqr` has `2³` roots of `1`, not four.
  `sqrt1_is_crt_pm1` is two-prime. Do not rewrite TwoSylow; record the arity.
- Outcome: Pietrzak’s quotient is writable as `Pmul μ (Pinv mid)`.

**Week 4 — Exponent laws and a false Wesolowski.** `ExpProof.v`.
- `wesolowski_verify` on `Presentation`, not only `powm`.
- Correct `π` is `P_Root`. A verifying `π` for a false `y` is
  `P_AdaptiveRoot` for the quotient, on RSA units. On `Cl`, state it and
  CAS-pin a toy `Δ`.
- Named skip: sequentiality, the random oracle that picks `ℓ`.

Named skips this month: Gauss `(2/p)`, cyclicity of `(ℤ/pℤ)*`, full Dirichlet
associativity, Pratt trees.

### 5.2 Month 2 — The consumer on both carriers ⬜

**Week 5 — Wesolowski on `Cl(Δ)`.** `ExpProof.v`, `cas/26_cl_poe.gp`.
- `bqf_exp` of a reduced form of odd order (catalog: `(4,3,6)` on `−87`).
- Verification is `Pmul (Pexp π ℓ) (Pexp x r) ~ y`.
- Outcome: sentence 2 has a `Cl` theorem, not a comment.

**Week 6 — Pietrzak quotient as an object.**
- `T = 2`: `μ² ~ y`, `y ~ x⁴`, `q = Pmul μ (Pinv (Pexp x 2))`, then
  `Pexp q 2 ~ id`.
- RSA: `q ∈ {±1}` or a mixed CRT root. `Cl`: `q` may be ambiguous;
  `P_LowOrderOutside` still fails on it.
- Outcome: the last-wave edge is a constructed element.

**Week 7 — Accumulator as an instance, not a definition.** `Accumulator.v`;
grow `cas/24`.
- RSA: unit `A0`, `acc_add` by `e`, witness is `A0`, forge from `λ+1`.
- `Cl`: no trapdoor update from `Pannihilator = Some 2` (cannot divide by
  an odd `x`). Hash-to-prime stays named.

**Week 8 — Close month 2.**
- `THEORY.md` §17: consumer on two carriers; multi-prime arity of `√1`.
- `Print Assumptions` on the new headlines. CAS gate includes `26`.

Named skips this month: hash-to-prime, VDF sequentiality, `h(Δ)`, anything
above 2-primary in `Cl`.

### 5.3 Month 3 — Third incarnation: the Williams torus mod `N` ⬜

Public data: `N = pq` and a parameter `P` (discriminant `P²−4`). The group
law is Lucas addition. The hidden order, when `P²−4` is a QNR mod `p` and
mod `q`, is `lcm(p+1, q+1)`. That is not `λ(N)`.

**Week 9 — `Torus.v` / `lucas_presentation`.**
- Carrier: `V_n` with composition via the addition formula. Identity `V_0 = 2`.
- Constructible torsion: solutions of `V_n = 2` you can write without factors
  (the identity). No public `Cl[2]` analogue from `N` alone — record the absence.
- `Pannihilator`: `None`. Not `Some (N+1)`.

**Week 10 — Same winning conditions.**
- `P_Order`, `P_LowOrder`, `P_AdaptiveRoot`, `P_Root` on
  `lucas_presentation N P`.
- Type B at `n = 2` *is* `P_LowOrder` / a one-sided annihilator on this
  carrier (`p+1 | M` ⇒ `V_M ≡ 2 (mod p)` under the week-2 QNR hyp).
- Wesolowski on the torus. CAS `27_torus.gp` on `11×19` with `P=5`.

**Week 11 — Which arrows exist here and not elsewhere.**
- CRT-split *does* exist: one-sided `V_M ≡ 2 (mod p)` and not `(mod q)`
  splits `N` (Williams analogue of Miller). Unlike `Cl`.
- `N+1` does **not** annihilate: `(p+1)(q+1) = N+(p+q)+1`. No lemma
  `N_plus_one_annihilates_torus`. CAS: `V_{N+1} ≢ 2 (mod N)` on the toy.
- If `p ≈ q`, Fermat gives `p+q`, hence the torus order. Type A, already
  catalogued — do not claim a new leak.
- Pietrzak quotient: order `| 2`; constructible set is `{V_0}` unless a
  public `V_k = 2` appears from `N`.

**Week 12 — Close the loop.**
- `THEORY.md` §18–19: torus presentation; `N+1` is not `λ+1`; incarnation
  × arrow table grows a column.
- `Print Assumptions` on every new headline. QNR hyp and Dirichlet
  associativity stay listed if still used.
- One CAS gate over `26`–`27` plus `01`–`25`.

### 5.4 Refused this wave (named)

Same list as §3.4. In particular: no undirected §6.11 sampler; no Gauss
`(2/p)` unless week 2 is blocked on it; no cyclicity of `(ℤ/pℤ)*` unless a
count is required as a theorem; no `Problem_UFO` with no construction.

The surprise, if any, is whether `N+1` can be twisted into a torus
annihilator by some public function of `N` other than Fermat’s `p+q`. If
that function appears, it is a Type A handle and belongs in §6.11 with a
*name*.
