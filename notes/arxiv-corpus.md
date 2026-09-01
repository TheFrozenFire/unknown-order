# arXiv / ePrint corpus — claims we could prove

Breadth-first pass (2026-08-18). Not a bibliography of every VDF
or accumulator. A paper is here if it *states a property of a
named unknown-order problem* that this repo could treat as a
theorem, a new cell, or a named refuse. Scheme papers that only
*assume* Strong RSA / AR are listed once as a class, not itemized.

Axes: carrier × winning condition × family `H` × challenge space
`C`. See `notes/paper-overlaps.md`.

## A. Algebra we already have, or could close next

These papers' unknown-order *claims* are relation-level. A later
pass would quote the claim and point at a Rocq name (or add one).

| Paper | Claim that sits on our map | Status |
|---|---|---|
| Wesolowski JoC 2020 (eprint 2018/623) | correct `π` is an `ℓ`-th root; AR game with prime `C` | `wesolowski_correct_is_root`; `P_AdaptiveRoot_C` |
| Pietrzak ITCS 2019 (eprint 2018/627) | bad midpoint is 2-torsion | `pietrzak_quotient_squares_to_one_rsa`; `H = Cl[2]` |
| Boneh–Bünz–Fisch 2018/712, CRYPTO 2019, CiC 2024 | `−1` on units; AR ⇒ low-order; smooth `C` | rows 2–3 of `paper-overlaps` |
| Kemmoe–Lysyanskaya 2024/505 | Shamir; Odds-AR; composite members | `shamir_trick`; `bdm_*`; `AdaptiveRoot_C` |
| Belabas–Kleinjung–Sanso–Wesolowski 2020/1310 (also Math. Cryptology) | Mersenne / Shanks form has odd order | `mersenne31_wins_restricted_LowOrder`; `cl_mersenne_H` |
| Coron–May JoC 2007 / May CRYPTO 2004 | `(N,e,d)` ⇒ factor, deterministic | in-corpus Miller / Coron–May algebra |
| Boneh–Venkatesan EUROCRYPT 1998 | algebraic FACT ≤ low-`e` RSA collapses | `bv_few_query_low_e_drops_oracle` (in-model unwind; not RSA ≢ factoring) |
| Aggarwal–Maurer EUROCRYPT 2009 | RSA ≡ factoring in the *generic ring* | `gra_inv_nonunit_factors`; `rational_Pe_minus_XQe_leading`. Standard-model slogan still `Refuse_AM09_generic_ring_as_standard_model` |
| Leander–Rupp ASIACRYPT 2006 | GRA, no division, low `e` | `gra_nodiv_identical_root_impossible_X3`; `gra_eq_leak_factors` |
| Aggarwal–Maurer–Shparlinski WCC 2011 | Strong RSA in the GRA | `gra_const_lambda_plus_one_solves_sRSA_without_factoring` (negative: `λ+1` is a constant) |
| Brown ePrint 2005/380 | SLP solver for low-`e` RSA | `slp_carmichael_is_functional`; `slp_solver_not_poly_identity_linear` |
| Jager–Schwenk JoC / ASIACRYPT 2009 | Jacobi GRA-hard, standard-easy | `jacobi_two_values`; `gra_jacobi_not_deg2_fit` |
| Barić–Pfitzmann 1997, Camenisch–Lysyanskaya 2002 | prime members; Shamir updates | `rsa_composite_member_splits_witness`; `shamir_trick` |

## B. New cells we could add (do not have yet)

| Paper | New cell | What a proof would be | Skip? |
|---|---|---|---|
| Dobson–Galbraith–Smith [arXiv:2211.16128](https://arxiv.org/abs/2211.16128) (eprint 2020/196) | knowing `h(Δ)` trivializes AR *search* on `Cl`, same as `λ+1` on units | `annihilator_plus_one_is_strong_RSA`; `class_number_solves_AR_neg31` (pin `h=3` on `Cl(−31)`). `D+1` is still not `h` (`cl_has_no_lambda_plus_one`). Bit-length / Sutherland cost stays named. |
| Bünz–Fisch–Szepieniec DARK (eprint 2019/1229; surveyed in [arXiv:2306.11383](https://arxiv.org/abs/2306.11383)) | *order assumption*: given random `g`, find `e ≠ 0` with `g^e = 1`; *r-fractional root*: `x^a = y^b` | `Problem_Annihilator` / `P_Annihilator`; `Problem_FractionalRoot` / `P_FractionalRoot`. RSA/sRSA are fractional root at `b=1`. `r`-powers stay named. |
| Hhan [arXiv:2402.11269](https://arxiv.org/abs/2402.11269) | unknown-order *generic group* lower bounds for order-finding, root extraction, repeated squaring | Interpreter: `ggm_eval`, `ggm_eq_leak_factors`. Query lower bounds stay `Refuse_UO_GGM`. | Do **not** treat GGM lower bounds as standard-model. |
| Jurkiewicz [arXiv:2503.00950](https://arxiv.org/abs/2503.00950) | even-order elements / `√1` factor `N` | Overlap only: `mixed_sqrt1_splits`, `rabin_roots_split`, `TwoSylow`, `MultiPrime` | Do not re-derive. |
| Damgård–Koprowski (generic UO groups, 2002; not arXiv-native) | generic-group lower bounds for DL / order in UO groups | `ggm_eval`; `ggm_add_uninhabited`; `generic_group_does_not_separate_rsa_from_srsa`. Query lower bounds stay `Refuse_UO_GGM`. | Do **not** treat GGM lower bounds as standard-model. |

## C. Uses the assumptions; do not treat as hardness theorems

These *define* or *consume* Strong RSA / AR / low-order. A
paper-check walks `paper-overlaps` (carrier, `H`, `C`) and stops.
No new winning condition.

- Wesolowski / Pietrzak VDF instantiations and surveys ([arXiv:2211.08162](https://arxiv.org/abs/2211.08162) and kin)
- RSA-accumulator applications (blocklists, UTXO prune, credentials)
- BHR+21 arguments from UO groups (eprint / CRYPTO 2021)
- Anything that only says “assume adaptive root on `GGen`”

## D. Out of scope for this corpus

- Quantum factoring cost (Gidney, Regev, Chevignard, Shor variants)
- Hyperelliptic / Jacobian “better UO group” ([arXiv:2211.16128](https://arxiv.org/abs/2211.16128) §Jacobians) — new carrier, and the project does not branch into curves
- Isogenies over RSA moduli ([arXiv:1810.00022](https://arxiv.org/abs/1810.00022))
- ROM / PPT scheme proofs (OAEP tightness, 2024/505 Theorems 3–8)
- Sequentiality of repeated squaring

## What “could prove” means here

A row in A or B is a candidate if it is a sentence about a
winning condition, a presentation, a family `H`, or a challenge
space `C`, and it does not need ROM, LLL, NFS, or a new
curve carrier. Everything in C is already covered by the
overlap table. Everything in D stays refused.

Highest-value sentence from that pass is now a theorem:
`class_number_solves_AR_neg31` / `annihilator_plus_one_is_strong_RSA`.
Sutherland bit-length claims and the general `y^{h+1}≡y` step on
unreduced Dirichlet representatives stay named.
