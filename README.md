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

Reusable algebra lives in `rocq-proofs/NumberTheory.v` (`powm`, Euler/Carmichael for
semiprimes, CRT, the sum/product quadratic, non-trivial square roots of 1, 2-adic split,
`v₂(lcm)=max`, `v₂` a valuation).
Domain files instantiate it. All headline Rocq theorems below close under the global
context unless a skip is named.

| Property | Rocq | CAS | Status |
|----------|------|-----|--------|
| Fermat / Euler / Carmichael on `N = pq`; `λ \| φ`; annihilator of units | `NumberTheory.annihilates_units` | `cas/02_annihilator.gp` (exhaustive on 187 and 65) | proven |
| `p+q = N−φ+1`; quadratic recovers `{p,q}` | `factors_from_phi_correct` | `cas/03_enum_factor.gp` | proven |
| Non-trivial `√1` splits `N`; unique `√1 = ±1` on a prime | `nontrivial_sqrt1_splits`, `Pratt.duality_unique_order_2_on_prime` | `cas/06_sqrt1.gp` | proven |
| RSA instance, `d ≡ e⁻¹ (mod λ)`, enc/dec on units | `RSA.rsa_dec_enc_units` | `cas/01_rsa_instance.gp` | proven |
| Textbook vector `p=11,q=17,e=3,d=27`: `enc(42)=36` | `rsa_test_vector` (`vm_compute`) | `cas/01_rsa_instance.gp` | proven |
| Multiplier enumeration / `φ`-cofactor | `FactorEnum` | `cas/03_enum_factor.gp` | proven (recovery from `φ`; `k < e` only when `d` is the `φ`-inverse) |
| Miller successive-squaring; witness ⇒ factor | `Miller.miller_witness_factors` | `cas/04_miller_factor.gp` (150/158 units split 187) | proven (criterion); density is CAS-exhaustive on 187, not a general count |
| Sequential-base Miller | `Miller.first_n_bases` | `cas/05_seq_miller.gp` | defined + witnessed; ERH poly-time **not** claimed |
| Coron–May / Coppersmith | `Lattice.lattice_phi_factors` | `cas/03_enum_factor.gp` | **interface only** — LLL/Howgrave–Graham skipped; once `φ` or `p+q` is known, factors follow |
| Miller–Rabin polarity | `MillerRabin` | `cas/07_miller_rabin.gp` | same engine, two exponents |
| Pratt certificate type + 2-torsion duality | `Pratt` | `cas/06_sqrt1.gp` | soundness of the 2-primary fact; completeness (every prime has a Pratt tree) **not** proved |
| RSA / strong RSA / order / low-order / adaptive-root as propositions | `UnknownOrder` | — | winning conditions; no hardness claim (§9) |
| Relation arrows (trapdoor ⇒ roots; RSA ⇒ sRSA at `e`; `λ` ⇒ `(y,λ+1)`; order `\| λ`; one-sided split) | `Hardness` | `cas/18_hardness.gp` | relations only; no PPT, no “RSA is hard”; `e`-power is a permutation of units when `gcd(e,λ)=1` |
| Fermat identity; close primes recover from `⌈√N⌉`; far-apart gap | `FermatFactor` | `cas/08_fermat.gp` | proven (recovery + gap); Fermat *runtime* as `O(\|p−q\|² / √N)` is the identity, not a complexity claim |
| Shared prime: `gcd(N₁,N₂) = p` | `SharedPrime` | `cas/09_shared_prime.gp` | proven (unique factorization) |
| Pollard `p−1`: one-sided annihilator splits `N` | `PollardP1.pollard_p1_splits` | `cas/10_pollard_p1.gp` | proven (criterion); `M = lcm(1..B)` is the CAS handle, not a formal construction |
| Safe / strong primes refuse a `B`-smooth `p−1` | `StrongPrimes.safe_prime_resists_p1` | `cas/10_pollard_p1.gp` | proven for `p−1`; Williams `p+1` is Lucas / `cyc2` |
| Wiener: `ed = 1+kφ`, basin, `d<φ ⇒ k<e` | `Wiener` | `cas/11_wiener.gp` (CF recovers `k/d`) | identities + basin proven; CF algorithm itself is CAS-only; Boneh–Durfee / LLL skipped |
| Hastad broadcast: CRT lift of three cubes *is* `m³` | `SmallExponent.hastad_cube_if_small` | `cas/12_small_e.gp` | proven when `m³` fits; Franklin–Reiter gcd **not** proved |
| CRT-RSA: `e d_p − 1` annihilates the `p`-side | `CRTRSA.crt_dp_annihilates` | `cas/10_pollard_p1.gp` | proven for `p ≥ 3` |
| Bit-leak / ROCA shape | `BitLeak` | — | shape only; Coppersmith / LLL skipped |
| Keygen intent-spec and refusal lemmas | `KeyGen.satisfies_keygen` | `cas/08`–`12` | each obligation blocks one leak; no hardness claim |
| Cyclotomic periods `Φ_n(p)` for `n ∈ {1,2,3,4,6}` | `Cyclotomic` | `cas/14_cyclotomic.gp` (`p=653` leaks `Φ_3` while strong at 20) | identities proven; Lucas `V` is `Lucas.v` / `cas/22` |
| Batch order: one `M` splits two coprime moduli | `BatchOrder.batch_p1_splits_pair` | `cas/15_batch_order.gp` | proven; shared `r \| gcd(p−1,p'−1)` recorded as Type A |
| Classical Wiener sufficient `36 d⁴ < N` | `Wiener.wiener_classical_sufficient` | `cas/16_wiener_frontier.gp` | sufficient, not equivalent to `d < ⅓ N^{1/4}`; BD 0.292 is interface |
| Shared-prefix / increment-window / twins | `KeyGenGeom` | `cas/17_keygen_geom.gp` | each bounds `\|p−q\|` and fails `kg_far` |
| Named keygen distributions vs rulers | `KeyGenSampler` | `cas/13_keygen_sampler.gp` | refusal theorems; frequencies are CAS |
| Quadratic residues; `p≡3 (mod 4)` root; Euler for `−1` | `QuadResidue` | `cas/19_rabin_williams.gp` | QR-direction of Euler; QNR direction and `(2/p)` skipped (Gauss) |
| Rabin–Williams: `e=2` not RSA; Williams tweak; Rabin reduction | `RabinWilliams` | `cas/19` (`N=11·23`, unique QR tweak on every unit) | combinatorics of `{±a,±2a}` proved; `(2/p)` generation-side; no signature game |
| 2-primary structure: `v₂(λ)=max`, mod-8 table, height exists | `TwoPrimary` | `cas/20_two_primary.gp` | `val2_lcm_max` in `rocq-proofs`; cyclicity named, not proved |
| Miller-from-`d` is a height mismatch on `odd_part(M)` | `MillerHeight.miller_from_d` | `cas/04`, `cas/20` | corollary of 2-heights; textbook `2` at `11×17` is `(1,3)` |
| Cyclic-model mismatch, including 150/158 | `CyclicCount` | `cas/20` | formula proved; realization is CAS + `cyclic_units` |
| Forced `1 (mod 2^d)` is both-deep; nextprime/safe are not | `TwoPrimary.dist_forced_2adic_both_deep` | `cas/21_matched_deep.gp` | live defect is the *progression*, not ordinary KeyGen |
| Lucas `V`; Type B is a presentation, adaptive root a relation | `Lucas`, `ClassGroupWall` | `cas/22_lucas.gp` | addition proved; QNR ⇒ `V_{p+1}≡2` is CAS; no `discriminant_to_lambda` |
| Primitive forms, identity composition, public order-2 classes | `BinForms` | `cas/23_class_group.gp` | `id ∘ f = f`; ambiguous forms win unrestricted LowOrder at `B=2` |
| Restricted low-order; presentations of RSA and `Cl(Δ)` | `ClassGroupWall`, `Presentation` | `cas/23` | `H={±1}` vs `H=Cl[2]`; public annihilator is `None` / `Some 2` |
| Wesolowski is an `ℓ`-th root; Pietrzak forgery is low-order | `ExpProof` | `cas/24_exp_proof.gp` | restricted LowOrder ignores constructible `Cl[2]` |
| Accumulator membership is a root | `Accumulator` | `cas/24` | forged witness is adaptive root; no `λ` to update `Cl` |
| Multi-prime: eight roots of 1, not four | `MultiPrime` | — | `TwoSylow` is two-prime; arity recorded |
| Williams torus: order `lcm(p+1,q+1)`, not `N+1` | `Torus` | `cas/27_torus.gp` | one-sided `V_M` splits; Fermat is Type A on the torus |
| Wesolowski on `Cl(−87)` | `ExpProof` | `cas/26_cl_poe.gp` | `(4,3,6)` has order 3; `π^ℓ x^r ~ y` |

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

See [`ROADMAP.md`](ROADMAP.md). RSA is a worked example. The same winning conditions are
instantiated on `Cl(Δ)` (`Presentation.v`); a Wesolowski proof is an `ℓ`-th root and a Pietrzak
forgery is low-order (`ExpProof.v`). The remaining hunt is §6.11 — a named sampler, not another
incarnation.
