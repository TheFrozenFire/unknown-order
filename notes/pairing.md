# Pairing and sampled-`τ` SRS

Companion to `PowersOfTau.v` (CAS `82`), `QRModN.v` / `Cocks.v`
(CAS `83`–`84`), and the checkable-CRS files through `BGH.v`.
A pairing that multiplies two hidden exponents and lands in a
*large* group would check consecutive CRS powers without
publishing `τ`. Jacobi does the first and fails the second
(`jacobi_sees_only_parity`). Curve pairings stay
`Refuse_elliptic_curve_branch`.

| Fact | Rocq |
|---|---|
| Sampled `τ`; contribute multiplies; walker is `τ⁻¹` | `pot_succ_is_tau_power`, `pot_contribute_multiplies_tau`, `backward_walker_is_tau_inv` |
| Equal-DL completeness / extract | `eqdl_complete`, `eqdl_extracts_tau` |
| Jacobi sees only parity; `τ`-tail constant | `jacobi_sees_only_parity`, `pot_jacobi_tail_constant` |
| Blum Jacobi `+1` ⇒ exactly one of `{a,−a}` is QR | `blum_jacobi_one_exactly_one_pm` |
| Cocks `t + a t⁻¹` decrypts a Jacobi bit | `cocks_decrypt_jacobi` |
| Self-bilinear spec checks / evaluates the string | `self_bil_checks_pot`, `self_bil_evaluates_pot` |
| Aux self-bilinear publishes `P_{i+1}` if `e(aux,g,g)=g` | `aux_eval_publishes_next` |
| Committed product `g^{f(τ)h(τ)}` | `poly_eval_conv`, `self_bil_committed_product` |
| Public quadratic on CRS slots | `public_quad_complete` (reveals bounded coeffs; not hiding) |
| QAP completeness at `τ` | `qap_complete_at_tau`, `qap_point_sound` |
| Equal-DL ladder realizes a `ρ^i` update | `ladder_realizes_update` |
| 2-of-2 “pairing” oracle is raise-to-`d*` | `two_party_next_forces_dstar` |
| DARK opening is an exponent identity | `dark_deg1_open`, `dark_deg2_open` (check without `s` is pairing or PoE) |
| Same `τ`-string on `Cl(Δ)` | `potP_cl_at_zero`, `pot_cl_no_lambda` |
| Cubic kernel on `N=pq` is `C₃×C₃`; mixed `μ₃` splits | `mu3N_det_gp_gq`, `mixed_mu3_splits` |
| Alternating bilinear on cyclic `μ₃` is constantly 1 | `alternating_bilinear_mu3_trivial` |

iO, ROM, HVZK simulation, and “this is a VDF” stay named.
