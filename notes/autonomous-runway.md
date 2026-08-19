# Autonomous runway (deepen / widen / refine)

Written so this session can run for hours without a new
direction. Constraints stay: no SHA/ROM/PPT discharge, no
LLL/NFS development, no OSCAR, no ECC corpus, no sixth-type
restart, no TLS stack. PARI stays the gated CAS.

Pace note: recent sits closed a catalog plus two formalization
waves in one day. Batches below are sized so a collapse still
leaves the next batch. Each batch ends in a commit when it
produces a theorem, a CAS pin, or an honest negative.

## What is already thick

RSA annihilator, Miller, KeyGen A–E, Euler quotient, sixth-type
Methods 1–12 (negative), class-group wall / Shanks family,
accumulators (BdM, Shamir, LLX, Peng–Bao), GQ extract, RW
algebra, transcript/oracle T4–T5, T8, T11–T12, T16, T24–T25,
T27/T29, K1/K5/K13, `m_p` sweep (no public CRT-side bit).

Do not redo those.

## What this runway is not

Another hunt for a sixth letter on `N`. Another padding-oracle
parser. A GGM. Camenisch–Michels. Sutherland `h(Δ)` at size.

## Batches (do in order; skip a batch only with a written death)

### A — Hygiene (refine)

- Point `THEORY.md` at transcript-oracle and this runway.
- README “What is left” is no longer the sixth-type hunt alone.
- `paper-overlaps.md`: Rabin inverter factors; RSA inverter does
  not; CRT-asymmetric predicate / Bellcore as use-time overlaps.
- `hardness.md`: one line that an `rsa_inverter` is not
  `Problem_Factor`.
- `arxiv-corpus.md`: mark Hhan as named refuse (UO-GGM ≠ SM);
  Jurkiewicz as overlap-only.

### B — Multi-prime √1 (widen)

`MultiPrime.v` states the arity (eight sign patterns) but does
not construct them or split on a mixed triple. Construct all
eight CRT combinations of `±1`; prove a root that is not
`±1` on every prime factors `N = pqr` (gcd with `x−1` is a
proper factor). CAS: `11·13·17`.

### C — Fiat–Shamir factoring ID algebra (deepen ZK catalog)

`notes/accumulators-zk.md` §2.1: GQ at `e=2` is PoK of a square
root; a non-trivial `√1` factors. Completeness is `gq_complete`
at `e=2`. Extraction + `rabin_roots_split` is the ID. Do **not**
simulate. CAS on `11·17` or `11·23`.

### D — Integer-commitment binding as a relation (widen)

`C = g^x h^r`. Two openings `(x,r) ≠ (x',r')` with
`g^x h^r = g^{x'} h^{r'}` give `g^{x−x'} = h^{r'−r}`, a
fractional root / sRSA witness. Hiding stays named
(`Refuse_HVZK_simulation` / `Refuse_PPT_advantage`). This is
FO/DF *binding*, not the broken 1997 proof.

### E — Product of raw signatures (T7 algebra)

`sign(∏ m_i^{a_i}) = ∏ sign(m_i)^{a_i}` for `a_i ≥ 0`. Already
implied by `sign_homomorphism`. Write the finite-product lemma
and the “if `∏ m_i^{a_i} = 1` then `∏ σ_i^{a_i} = 1`”
annihilator. Hash-DO stays refused.

### F — CRT-RSA `d_q` twin (deepen)

`CRTRSA.v` has `d_p`. The `q`-side is the same lemma with
`p ↔ q`. `e d_q ≡ 1 (mod q−1)`; `e d_q − 1` annihilates on `q`.

### G — `λ` of three primes (widen)

`λ(pqr) = lcm(p−1,q−1,r−1)`. Annihilator on units of `ℤ/pqrℤ`.
One-sided `a^M ≡ 1 (mod p)` still splits off `p` from `pqr`.

### H — Two orders’ lcm is not `λ` (negative, deepen `Order.v`)

`orders_generate_lambda_named` is a refuse. Pin: exist units
`a,b` with `lcm(ord a, ord b) ≠ λ` (e.g. both in the 2-Sylow).
CAS + a Closed exhibit on `rsa_test`.

### I — Named model mismatches (refine arXiv B)

- `Refuse_UO_GGM` (Hhan / Damgård–Koprowski): generic-group
  lower bounds are not standard-model hardness.
- Jurkiewicz even-order / `√1` is `TwoSylow` / Rabin. One
  sentence in `arxiv-corpus.md`, no new file.

### J — Lipmaa membership is `P_Root` on `Cl` (thin widen)

One lemma: a witness `W^x = A` in `cl_presentation` is
`P_Root`. No class-number algorithm. CAS: `Cl(−31)`, known
order-3 form.

### K — Self-review of `TranscriptOracle.v`

Read every new theorem as an adversary. Flag any that constrain
nothing (definitional `rsa_enc`, `let` tautologies). Fix or
narrow. Do not add PPT.

### L — CAS completeness for this runway

New witnesses `59+` only for batches that produce algebra.
Do not add Julia. Gate through `cas-gate.sh`.

### M — Stop conditions (after L, or earlier if stuck)

If a batch dies, write the death in this file and take the
next. After L: update this file’s “done” column, regenerate
coverage + PA, push. Do not invent Batch N to stay busy.
If time remains, prefer **K then H then G** over new letters.

## Done column

Update in place.

| Batch | Status |
|---|---|
| A Hygiene | done |
| B Multi-prime √1 | done (`eight_sqrt1_squares`, `mixed_pqr_splits`; CAS 59) |
| C FS / GQ `e=2` | done (`gq_e2_complete`, `gq_e2_odd_delta_extracts_sqrt`; CAS 60) |
| D Commitment binding | done (`icomm_binding_is_fractional_root`; CAS 61) |
| E Sign products | done (`sign_hom_3`, `sign_weighted_product`; CAS 62) |
| F `d_q` | done (`crt_dq_annihilates`; CAS 63) |
| G `λ(pqr)` | done (`carmichael_threeprime`, `onesided_period_splits_triple`; CAS 59) |
| H lcm of orders | done (`lcm_two_order2_not_lambda`; CAS 64) |
| I UO-GGM refuse | done (`Refuse_UO_GGM`) |
| J Lipmaa/`P_Root` | done (`lipmaa_cl_membership_is_P_Root`; CAS 65) |
| K Self-review | done (`rsa_inverter_recovers_message` now returns `m`) |
| L CAS + gate | done (CAS 59–65 green, 65/65; PA 881 Closed; coverage regenerated) |

RSA-land wave 3 (after L): Takagi `N=p²q`, Paillier `(1+N)^m`,
Cramer–Shoup verify, T10 wrap + PKCS#1 `[2B,3B)`, Shamir 2-of-3,
`φ = λ · gcd`, Okamoto–Uchiyama `L`. CAS 72–76.

RSA-land wave 4: Damgård–Jurik `s=2` binomial on `N³`; Takagi
`a^{ed} ≡ a (mod p²)`. CAS 77.

Shared-key DKG algebra: product of two KeyGen-valid moduli,
CRT of local inverses of a common `e`, Garner of local decrypts
is `c^{d*}`. Arity 3 is the same theorem. CAS 78–80.
