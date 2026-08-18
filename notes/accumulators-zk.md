# RSA accumulators and RSA-based ZK — approaches we can formalize

Pivot catalog. Accumulators: constructions besides 2024/505 whose
*algebra* sits on this corpus. ZK: RSA / hidden-order proofs,
including ones that failed. Completeness and extraction are in
scope. Simulation / ROM / PPT stay named.

Companion to `Accumulator.v`, `notes/paper-overlaps.md`,
`notes/arxiv-corpus.md`.

## 1. RSA accumulators

All of these are the map `A ↦ A^x` in a group of unknown order
unless noted. What changes is the *member encoding*, the
*witness shape*, and whether a trapdoor is used.

| Approach | Members | Witness | Extra | Formalize? |
|---|---|---|---|---|
| Benaloh–de Mare 1994 | integers | `W^x = A` | informal soundness | **Have:** map, composite split, same-bit-length fail |
| Barić–Pfitzmann 1997 | primes | same | Strong RSA | **Have** the reason primes are load-bearing |
| Camenisch–Lysyanskaya 2002 | primes | Shamir update on delete | needs `gcd(x,y)=1` | **Have** `shamir_trick` |
| Li–Li–Xue 2007 | primes | non-membership `(a,B)` with `A^a B^x = g` | Bézout on `∏S` and `x` | **Have:** `llx_complete`, `llx_extract_root`. Peng–Bao: `llx_lambda_forges_nonmem`, `peng_bao_member_still_forges` |
| 2024/505 | odd integers + peel small factors | `(W, s)` | ROM + large prime factor | Algebra have; ROM named |
| Baldimtsi et al. Braavos / CL-RSA-B | primes | trapdoor add: `w = A^{H(x)^{-1} mod λ}` | acc unchanged on add | **Have:** `rsa_trapdoor_add` (no hash; `x` is the exponent). Also `rsa_acc_forge_from_lambda` |
| Boneh–Bünz–Fisch 2019 | primes | batched via PoE | Wesolowski | **Have** PoE algebra; aggregation is the same root |
| Lipmaa 2012 | Euclidean ring / DIH | static | class groups, no setup | **Yes** on `cl_presentation`; `H` is the family |
| Mashatan–Vaudenay 2013 | primes | dynamic non-membership | LLX + updates | After LLX |
| Camacho–Hevia 2010 | any secure dynamic | — | `Ω(m)` update communication | Interface theorem, not a group problem |
| Sander / Goodrich–Tamassia–Hasic | RSA + trees | logarithmic | hybrid | Skip trees |

**Done this sitting.** LLX completeness / extract / Peng–Bao, and trapdoor add. Next, if we keep going on accumulators: Lipmaa on `Cl` (same map, `H` from the family; membership is `P_Root`; no `λ` to delete with). Mashatan–Vaudenay is LLX + updates.

Not RSA accumulators (out of this pivot): Nguyen pairings, Merkle, bilinear Braavos variants.

## 2. ZK built on RSA / hidden order

Three layers. Only the first is this repo’s style.

### 2.1 Algebra we can close (completeness + extraction)

| Approach | Statement | Extraction / algebra | Formalize? |
|---|---|---|---|
| Guillou–Quisquater 1988 | PoK of an `e`-th root: `x^e = z` | two transcripts `(c,r)`, `(c',r')` ⇒ Shamir on `r/r'` and `c−c'` yields an `e`-th root if `gcd(c−c', e)=1` | **Have:** `gq_complete`, `gq_extract`. ZK simulation named |
| Fiat–Shamir 1986 (factoring ID) | PoK of a square root | same, `e=2`; a non-trivial `√1` factors | **Yes.** Completeness + Rabin split (have) |
| “Here is `√1 ≠ ±1`” | “I know the factors” | mixed CRT root *is* the factors | **Have:** `publishing_mixed_sqrt1_factors`, `gq_on_one_with_mixed_sqrt_is_factorization`. Proof of knowledge, **not** ZK |
| FO / DF integer commitment | `C = g^x h^r` in a UO group | binding = Strong RSA (opening two ways ⇒ a root) | **Yes**, binding as a relation. Hiding named |
| CL-RSA-B / trapdoor membership | `w^x = A` | that *is* `P_Root` | **Have** |
| Wesolowski / Pietrzak | `v^e = u` | PoE, not ZK (the statement is the result) | **Have** the algebra; do not call it ZK |

### 2.2 Attempts that failed or only half-worked

| Approach | What they wanted | What broke |
|---|---|---|
| Naive “I know `d`”: decrypt a random challenge | ZK of the RSA trapdoor | Verifier (or a man-in-the-middle) gets a decryption oracle. Not ZK, not even a PoK of `d` vs of an inversion oracle |
| Send a non-trivial square root of 1 | ZK of factorization | Instantly factors `N`. Proof of knowledge, **zero** knowledge |
| Fujisaki–Okamoto 1997 integer commitments + ZK for polynomial relations | statistical HVZK + binding from Strong RSA | **Security proof was wrong.** Damgård–Fujisaki 2001/02 repaired the proof and the assumptions (hidden-order group axioms). Construction survived; the original argument did not |
| GQ with composite `e` and no gcd condition | extract an `e`-th root from two transcripts | Extraction needs `gcd(Δc, e)=1`. If `e` is the RSA public exponent and challenges share a factor with `e`, special soundness fails. That is why GQ wants prime `e` or a prime challenge space — same `C` lesson as Wesolowski |
| Interactive GQ + “just hash the first message” | NIZK | Fiat–Shamir / ROM. Named skip |
| “ZK inversion ⇒ factoring in the standard model” | RSA ≡ factoring | Boneh–Venkatesan: algebraic reductions for low `e` collapse. Named refuse |
| Prove non-membership and publish `∏S mod φ(N)` | universal accumulator + ZK | Peng–Bao: that product *is* the trapdoor (`peng_bao_member_still_forges`) |
| Statistical ZK for *RSA inversion* (the permutation) | hide `x` given `x^e` | On units the map is a permutation; “`y` is an `e`-th power” is vacuous. There is nothing to prove except knowledge of a preimage. Decision-RSA is not a thing (`THEORY.md` §9.7) |

### 2.3 Worked, but scheme-heavy (do not grow a ZK stack here)

- Camenisch–Michels 1999: statistical ZK that `N` is a product of two (safe) primes. Uses integer commitments. Completeness identities are doable; the protocol is long.
- Poupard–Stern: short PoK of factorization.
- Boudot 2000, Lipmaa: range proofs on committed integers (`0 ≤ x < 2^ℓ`). Completeness is integer arithmetic plus FO/DF openings.
- Camenisch–Lysyanskaya 2001/03: signatures with efficient ZK protocols (anonymous credentials). Strong RSA + GQ-shaped proofs.
- Cramer–Shoup 2000: Strong RSA *signatures*, not ZK.
- Couteau 2016/17 (EUROCRYPT): remove Strong RSA from arguments over the integers, use standard RSA. Reduction-heavy.
- Groth 2005: cryptography in subgroups of `(ℤ/nℤ)*`.
- Maurer 2009: GQ and Schnorr as one template (special soundness).
- DARK (Bünz–Fisch–Szepieniec): polynomial commitments from UO groups (order / AR / fractional-root assumptions). We named those relations; the PCS is a scheme.

## 3. What to formalize if this pivot is real work

**Accumulators (this sitting):** `llx_complete`, `llx_extract_root`, `llx_lambda_forges_nonmem`, `peng_bao_member_still_forges`, `rsa_trapdoor_add`. CAS `42`. Lipmaa-on-`Cl` is the same map on `cl_presentation_H` (not started).

**ZK (this sitting):** `gq_complete`, `gq_extract`, `gq_on_one_with_mixed_sqrt_is_factorization`. Simulation / ROM stay named. Do **not** start FO/DF simulation or Camenisch–Michels.

Refuse: ROM NIZK, ZK simulators, pairing accumulators, “prove RSA ≡ factoring.”
