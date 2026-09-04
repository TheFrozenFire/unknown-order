# unknown-order

Computational problems in **groups of unknown order**: the group law is public, the
order is not. RSA, strong RSA, adaptive root, order, and low-order are the same
winning conditions on different carriers. This repo writes those conditions once,
instantiates them, and records which arrows exist.

Every claim that matters is checked twice. Rocq (Coq 9.1) proves it for the model.
PARI/GP pins it on numbers. Agreement is evidence because the tools fail differently:
a wrong premise still proves cleanly in Rocq; a wrong model still computes in CAS.

The map of the theory is generated from the Rocq tree:
[`generated/COVERAGE.md`](generated/COVERAGE.md) (TOC) and
[`generated/NAMED_SKIPS.md`](generated/NAMED_SKIPS.md) (refuses).
Policy (what must not be axiomatized) is in [`THEORY.md`](THEORY.md).
Working rules are in [`AGENTS.md`](AGENTS.md).

## Three presentations

| | `(ℤ/Nℤ)*` | `Cl(Δ)` | Williams torus |
|---|---|---|---|
| Public data | `N = pq` | discriminant `Δ < 0` | `N` and a Lucas parameter `P` |
| Hidden order | `λ = lcm(p−1, q−1)` | class number (not computed) | `lcm(p+1, q+1)` |
| Constructible torsion | `{±1}` | ambiguous forms (`Cl[2]`) | `V_n ≡ 2` written without factors |
| Public annihilator | `None` (trapdoor: `Some λ`) | `Some 2` | `None` — not `N+1` |
| Type B (a period becomes public `M`) | `p−1` on units | no | `p+1` on the torus |
| CRT-split | yes (one-sided order) | no | yes (one-sided `V_M ≡ 2`) |
| `N+1` / `λ+1` annihilates | `λ+1` does, if `λ` is known | no | **no** — order is `N+(p+q)+1` |

RSA is the worked example, not the only object. Rabin–Williams is the same unit
group at a forbidden exponent `e = 2`.

A Pietrzak forgery is low-order. On `Cl(Δ)` that element may be an ambiguous
form built from `factor(Δ)`, so unrestricted `LowOrder` at `B = 2` is a public
construction. The restricted problem (`LowOrderOutside H`, `H = Cl[2]`) is the
one a protocol needs.

Reusable algebra (`powm`, Carmichael, CRT, `√1` splitting, `v₂`) lives in the
sibling [`rocq-proofs`](https://github.com/TheFrozenFire/rocq-proofs). Clone it
beside this repo. Methodology comes from
[`formal-verification`](https://github.com/TheFrozenFire/formal-verification)
and the last pure-theory run in
[`ciphering`](https://github.com/TheFrozenFire/ciphering). There is no EVM
track: there is no bytecode.

## What is proved

Headline theorems close under the global context unless the statement
takes a `*_named` hypothesis. The refuse list is
`generated/NAMED_SKIPS.md` (`NamedRefuse`, unused `*_named`).
Cyclicity of `(ℤ/pℤ)*` as used in-corpus is `cyclic_units_holds`.
Williams evaluation `V_{p+1} ≡ 2` when `P²−4` is a QNR is
`williams_eval_of_qnr`. Gauss `(2/p)` is a theorem (`QuadRecip.v`).
Hash-to-prime is two encodings (`HashSlot.v`), not a hash
(`Refuse_hash_as_oracle`).

### Campaign pin

Integers for campaign moduli live in `rocq/Pin.v` (twin of `cas/lib/pin.gp`).
Default semiprime: `pin_p`, `pin_q`, `pin_N`, residual `(pin_x, pin_y, pin_e)`.
Named extras: `pin_77` (safeprime-shaped), `pin_91` (cubic kernel), `pin_247`
(matching orders), `pin_253` (Williams), `pin_45` (Takagi), `pin_105` (triprime),
`pin_Nsq` (Paillier). Computed attachments (Dixon residues, NFS quadratics,
mixed `√1`) sit with the default pin. `rsa_test` is built from those names.
RSA exports `Pin`; other files import it. Write `pin_N`, not a literal `187`.

### RSA and the annihilator

`d ≡ e⁻¹ (mod λ)`. `M = ed − 1` annihilates the units. Multiplier enumeration
recovers `{p, q}` from `φ` or `p+q`. Miller successive-squaring turns a height
mismatch into a factor (`MillerHeight`: heights are `v₂(ord)`). Miller–Rabin is
the same engine on a different exponent.

`rocq/RSA.v`, `FactorEnum.v`, `Miller.v`, `Order.v`, `TwoSylow.v`.
Two order-2 units do not generate `λ` (`lcm_two_order2_not_lambda`).
CAS `01`–`07`, `25`, `64`.

### Key generation is a leaked annihilator

Each catalog row is a generation choice that makes a *partial* or *short*
period public (Type A–E in `notes/keygen-weaknesses.md`). Fermat, shared primes, Pollard
`p−1`, Wiener, small `e`, CRT-RSA `d_p`, unbalanced primes, cyclotomic
`Φ_n(p)`, batch order, and close-prime geometries have refusal lemmas in
`KeyGen`. Matched-deep `v₂` is a shape of `λ`, not an annihilator; the live
defect is sampling both primes `≡ 1 (mod 2^d)`, not ordinary `nextprime`.

`notes/keygen-weaknesses.md`. CAS `08`–`17`, `21`. LLL-shaped rows (Boneh–Durfee,
ROCA, Coron–May) are interfaces only.

### The same group, a different map

`e = 2` is not an RSA exponent. Squaring is 4-to-1. Four `√1` via CRT; mixed
roots split `N`. Williams primes give a unique QR among `{±a, ±2a}`. Three
primes give eight roots of 1, not four (`eight_sqrt1_squares`); a mixed
pattern splits `N` (`mixed_pqr_splits`). `λ(pqr)` annihilates units
(`carmichael_threeprime`).

`QuadResidue.v`, `RabinWilliams.v`, `TwoPrimary.v`, `MultiPrime.v`. CAS `19`–`20`, `59`.

### Sieve relations (QS / NFS payload)

Dixon combination of B-smooth squares is a congruence of squares
(`dixon_combination_splits`). NFS setup is a common root of two integer
polynomials and the homogenised remainder `F ≡ GH (mod N)`. Two-sided even
combination splits the pin. Cost stays out.

`rocq/SieveRelation.v` consumes `Pin`. `notes/sieve-rsa.md`. CAS `161`–`163`.

### Second incarnation: `Cl(Δ)`

Primitive forms, Gauss reduction, identity, inverse. `id ∘ f = f`. `f ∘ f⁻¹`
lands back on `Δ` and is principal. Construction-side ambiguous forms
(`b = 0` or `a = ±b`) satisfy `[f]² = 1` and win unrestricted low-order at
`B = 2` when they are not principal.

`BinForms.v`, `ClassGroupWall.v`, `Presentation.v`. CAS `23`.

### Consumer: proof of exponentiation, then an accumulator

A correct Wesolowski `π` is an `ℓ`-th root. A Pietrzak midpoint that is not
the true one yields an element of order dividing 2. Membership in an
accumulator is a root; a forged witness for a random base is adaptive root.
Run on `(ℤ/Nℤ)*` (Wesolowski is trivial given `λ`; Pietrzak hits `{±1}` or a
mixed CRT root) and on toy `Cl(Δ)` (Pietrzak must not count `Cl[2]` as a
restricted break). CAS `24`, `26`.

`ExpProof.v`, `Accumulator.v`, `GQ.v`. Sequentiality and the ROM are
`Refuse_this_is_a_VDF` / `Refuse_ROM`.
A composite member splits the witness; same bit length does not restore
soundness (`bdm_same_bits_still_splits`). Wesolowski algebra does not
use `Z.prime ℓ`. On raw units an odd challenge accepts `−y` via `π ↦ −π`
(`wesolowski_soundness_fails_on_units_odd_challenge`). A poly-size or
smooth adaptive-root challenge space is broken
(`adaptive_root_known_product_breaks`).
LLX non-membership is Bézout (`llx_complete`); `θ` and `λ` forge it
even for a member (`peng_bao_member_still_forges`). Trapdoor add is
`rsa_trapdoor_add`. GQ completeness and two-transcript extraction
are `gq_complete` / `gq_extract`; a mixed `√1` factors and is not ZK.
CAS `42`.

Excluding `Cl[2]` is not enough for restricted low-order: on the
Mersenne discriminant `Δ = −31` the Shanks form `(2,1,4)` has order 3
(`mersenne31_wins_restricted_LowOrder`). CAS `40`.

Constructible torsion is a family parameter (`cl_presentation_H`).
Ordinary `Cl` has `H =` ambiguous forms; a Mersenne family also
constructs the Shanks order-3 class. The same form wins restricted
low-order on one sampler and is excluded on the other
(`ordinary_vs_mersenne_H`). Adaptive root the game is
`Problem_AdaptiveRoot_C` (challenge space `C`); Strong RSA is the
search. `λ+1` wins the search and misses prime-`C`
(`search_lambda_plus_one_misses_prime_AR`). `2 ∈ C` on `Cl` is
`cl_AR_C_broken_when_two_in_C`. Knowing an annihilator `M` of `y`
gives AR search via `(y, M+1)` (`annihilator_plus_one_is_strong_RSA`);
on `Cl(−31)` that is the class number (`class_number_solves_AR_neg31`).
The order assumption and fractional root are named relations
(`Problem_Annihilator`, `Problem_FractionalRoot`).

When checking another paper against this corpus, start at
[`notes/paper-overlaps.md`](notes/paper-overlaps.md).

### Third incarnation: the Williams torus

Lucas `V` addition is a theorem. `V_{p+1} ≡ 2 (mod p)` is a named QNR
hypothesis; multiples of the period are a theorem. One-sided `V_M ≡ 2`
splits `N`. `N+1` does not annihilate. If Fermat leaks `p+q`, the torus
order is public — Type A, already in the catalog.

`Lucas.v`, `Torus.v`. CAS `22`, `27`.

## Hardness is a relation, not an axiom

`Hardness.v` records arrows: trapdoor inverts RSA; an RSA solution is strong
RSA at that `e`; `λ+1` solves adaptive root on units; order divides `λ`;
one-sided low-order factors. There is no global `RSA_hard`. A hardness
*claim* needs a named KeyGen distribution (`Refuse_PPT_advantage`). PPT /
advantage is out of *model*. Whether an RSA inverter or Strong-RSA solver
constructs a factor is a live Gallina target
(`rsa_inverter_constructs_factor_open_named`,
`strong_rsa_solver_constructs_factor_open_named`,
`residual_solver_constructs_factor_open_named`) — unproved, on-goal.

Strong RSA solver-class cuts (peel, leftover subgroup, gcd vs
multiply, public maps of `x` and `e`) are grouped by *question* in
[`notes/srsa-cuts.md`](notes/srsa-cuts.md). Rocq IDs are semantic
(`residual_*`, `period_*`, `xmap_*`, …); CAS numbered files stay.

## Run it

```sh
git clone https://github.com/TheFrozenFire/rocq-proofs   # sibling of this repo
bash run-check.sh                 # CAS + Rocq + generated coverage
bash rocq/print-assumptions.sh    # Closed / 0 axioms; count in the snapshot summary
```

Needs PARI/GP (`gp`) and Rocq 9.1. The Rocq track builds `../rocq-proofs` first.
CAS is 165 witnesses, `cas/01`–`165`. PARI is the gated CAS; do not add OSCAR.

RSA constructions beyond textbook inversion (Chaum blinding, threshold /
mediated shares, Shoup extract, shared-modulus DKG, CRT decrypt, RSW
time-lock, Takagi `p²q`, Cramer–Shoup verify, Paillier / Okamoto–Uchiyama
neighbours, sampled-`τ` powers in `(ℤ/Nℤ)*`) are catalogued in
[`notes/rsa-land.md`](notes/rsa-land.md). Protocol / ROM / PPT stay named.
The sampled-`τ` string is `rocq/PowersOfTau.v`, CAS `82`.
QR modulo `N`, Jacobi degeneracy, and Cocks 2001 algebra are
`rocq/QRModN.v` / `rocq/Cocks.v`, CAS `83`–`84`.
Endomorphisms, auxiliary self-bilinear maps, DARK openings,
the `τ`-string on `Cl(Δ)`, and the Cocks/BGH 1-bit catalog are
`rocq/Endo.v` / `AuxBil.v` / `Dark.v` / `PotCl.v` / `BGH.v`,
CAS `89`–`93`. The equal-DL ladder that makes extra published
powers a proven `ρ^i`-update is `rocq/PotLadder.v`, CAS `94`.
Committed evaluations and the product \(f(\tau)h(\tau)\) are
`rocq/EvalProduct.v`, CAS `95`. QAP completeness on those
encodings is `rocq/QAP.v`, CAS `96`. Coefficient PoK, a compiled
mul gate, and the same-witness check are `rocq/CoeffPoK.v` /
`MulGate.v` / `SameW.v`, CAS `97`–`99`.
Witness PoK on a specialized CRS, addition, and bits are
`rocq/WirePoK.v` / `AddGate.v`, CAS `100`–`101`.
A two-gate circuit, bit logic, and 2-bit range are
`rocq/Circuit.v` / `BitLogic.v` / `Range2.v`, CAS `102`–`104`.
Mux, wire equality, and bit-sum encodings are `rocq/Mux.v` /
`WireEq.v` / `BitSum.v`, CAS `105`–`107`.
Inner product, bit less-than, conditional swap, and n-bit
unfolding are `rocq/Inner2.v` / `BitLt.v` / `CondSwap.v` /
`AllBits.v`, CAS `108`–`111`. The public quadratic check of
two committed evaluations (bounded slot search + CRS bilinear
combine; not group-mul) is `rocq/PublicQuad.v`, CAS `112`.
Fiat–Shamir compilation of the public-coin eqdl / slot Sigma
(`c` from statement + commitment; no verifier coin) is
`rocq/FiatShamir.v`, CAS `113`. ROM soundness stays named.
A logarithmic fold of the bilinear CRS combine (proof length
`13 log₂ n + 2`, not one encoding per slot) is
`rocq/Succinct.v`, CAS `114`.

## Constructor (not a filter)

`KeyGenCtor.v` emits `p = a + k·M` with `M = 4 r s u v w`, so
`r | p−1`, `s | p+1`, `p ≡ 3 (mod 4)`, and `u,v,w` divide
`Φ₃(p)`, `Φ₄(p)`, `Φ₆(p)`. A `PlacedCtorPair` carries
balanced / far / bits as fields. A `CtorKey` adds `(e,d)` and
`ctor_to_rsa` is an `RSAInstance` that discharges
`satisfies_keygen_full`. The CRT walk does not force placement.
If `M` is public, the image is a thin AP (ROCA shape) and
AP-search bits are `bitlen(p) − bitlen(M)`. If the auxiliaries
are per-key secrets, that test is not free. Catalog handle
bits are 0; NFS is not proved. There is no running sampler.
CAS `28`.

## Two encodings (not a hash)

`HashSlot.v` is the constructor walk at `k = seed`. Every output
is already in the no-handle AP. Accept is primality. If the map
is public, the image is Type A. `ChallengePrime.v` is the other
map: odd integers, not the constructor residue. A membership
witness for `ab` is a witness for `a` and for `b`. Neither map
is SHA. CAS `29`–`31`.

## Secure derivation

`Derive.v` turns a seed into a candidate in `S_b` (class ∩ bit
range). Uniform index ⇒ uniform on `S_b`. `seed mod L` and
force-residue are biased. Increment is not resample. A public
map into one AP leaks `M`; reuse of `(a, M)` is publication.
Placement is an interval on the second index, or empty.
`derive_key_success` is the key relation (`e = 65537`). Long
seed is a bijection; short seed plus stretch is `Refuse_PRF_stretch`.
Pocklington is blocked at `B = 160` for 512-bit primes.
CAS `32`–`38`.

## What is left

The sixth-type hunt on public `N` is exhausted
([`notes/sixth-type-plan.md`](notes/sixth-type-plan.md)).
Transcripts and oracles are catalogued and the cheap algebra
is closed
([`notes/transcript-oracle-plan.md`](notes/transcript-oracle-plan.md)).
`Refuse_undirected_611_hunt` still names “wander through
KeyGen samplers.” Active work is the deepen/widen/refine
runway: [`notes/autonomous-runway.md`](notes/autonomous-runway.md).
Gaps that stay named are `generated/NAMED_SKIPS.md`.
