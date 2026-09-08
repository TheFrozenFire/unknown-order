# Named skips

A `Definition foo_named` is first-class Rocq.  **Unused** means
refuse (nothing depends on it).  **Used** means a consumer is
weaker by exactly that hypothesis.  `Definition foo_open_named`
is a live algebraic target: unused means *unproved*, not banned.
`NamedRefuse` constructors are out of model (ROM, PPT, NFS) —
not a ban on proving a nearby Gallina reduction.

Generated.  Do not edit by hand.

## `*_named` propositions

| Name | File | Line | Status | Used at |
|---|---|---:|---|---|
| `strong_rsa_solver_constructs_factor_open_named` | `Hardness.v` | 79 | open | — |
| `residual_solver_constructs_factor_open_named` | `StrongRSAPeel.v` | 285 | open | — |
| `rsa_inverter_constructs_factor_open_named` | `TranscriptOracle.v` | 587 | open | — |
| `compose_preserves_disc_named` | `BinForms.v` | 677 | refuse | — |
| `compose_assoc_named` | `BinForms.v` | 803 | refuse | — |
| `compose_left_compat_named` | `BinForms.v` | 812 | refuse | — |
| `cocks_hash_named` | `Cocks.v` | 30 | refuse | — |
| `cocks_ind_id_cpa_named` | `Cocks.v` | 33 | refuse | — |
| `eval_pair_needs_integer_named` | `EvalPairing.v` | 229 | refuse | — |
| `coppersmith_named` | `Lattice.v` | 67 | refuse | — |
| `dirichlet_ap_prime_named` | `NamedSkips.v` | 73 | refuse | — |
| `orders_generate_lambda_named` | `Order.v` | 290 | refuse | — |
| `pot_bilinear_verify_named` | `PowersOfTau.v` | 36 | refuse | — |
| `pot_hvzk_eqdl_named` | `PowersOfTau.v` | 41 | refuse | — |
| `pratt_complete_named` | `Pratt.v` | 110 | refuse | — |
| `dstar_is_zk_like_tau_named` | `SharedKey.v` | 636 | refuse | — |
| `pot_bilinear_crs_named` | `SharedKey.v` | 641 | refuse | — |
| `boneh_durfee_named` | `Wiener.v` | 158 | refuse | — |

## `NamedRefuse` constructors

| Constructor | File | Line |
|---|---|---:|
| `Refuse_ROM` | `NamedSkips.v` | 41 |
| `Refuse_SHA_in_Rocq` | `NamedSkips.v` | 42 |
| `Refuse_PPT_advantage` | `NamedSkips.v` | 43 |
| `Refuse_NFS_cost` | `NamedSkips.v` | 44 |
| `Refuse_RSA_eq_factoring_standard_model` | `NamedSkips.v` | 45 |
| `Refuse_AM09_generic_ring_as_standard_model` | `NamedSkips.v` | 46 |
| `Refuse_BP97_vs_modern_sRSA` | `NamedSkips.v` | 47 |
| `Refuse_undirected_611_hunt` | `NamedSkips.v` | 48 |
| `Refuse_elliptic_curve_branch` | `NamedSkips.v` | 49 |
| `Refuse_lattice_lll_development` | `NamedSkips.v` | 50 |
| `Refuse_FO_DF_simulation` | `NamedSkips.v` | 51 |
| `Refuse_pairing_accumulators` | `NamedSkips.v` | 52 |
| `Refuse_this_is_a_VDF` | `NamedSkips.v` | 53 |
| `Refuse_HVZK_simulation` | `NamedSkips.v` | 54 |
| `Refuse_PRF_stretch` | `NamedSkips.v` | 55 |
| `Refuse_hash_as_oracle` | `NamedSkips.v` | 56 |
| `Refuse_NIZK_Fiat_Shamir` | `NamedSkips.v` | 57 |
| `Refuse_Camenisch_Michels_protocol` | `NamedSkips.v` | 58 |
| `Refuse_Mollin_general_2020_1310` | `NamedSkips.v` | 59 |
| `Refuse_r_power_hardness` | `NamedSkips.v` | 60 |
| `Refuse_polynomial_gcd_over_ZN` | `NamedSkips.v` | 61 |
| `Refuse_RW_signature_scheme` | `NamedSkips.v` | 62 |
| `Refuse_EN_card_from_N` | `NamedSkips.v` | 63 |
| `Refuse_Redei_4rank_fund_minus4N` | `NamedSkips.v` | 64 |
| `Refuse_UO_GGM` | `NamedSkips.v` | 65 |
| `Refuse_DKG_MPC` | `NamedSkips.v` | 66 |
| `Refuse_threshold_robustness` | `NamedSkips.v` | 67 |
| `Refuse_OAEP_PSS` | `NamedSkips.v` | 68 |

## Does not discharge

A `(** **` subsection whose comment says `Not [foo_open_named]`
(or `Not a proof of` / `Neither is a proof of`) applies to every
Theorem/Lemma/Corollary until the next section comment. Those
results do not inhabit the live target. Generated from `.v`
comments; do not maintain this table by hand.

### `residual_solver_constructs_factor_open_named`

| Closed result | File | Line |
|---|---|---:|
| `cong_mod_lcm` | `CRTRSA.v` | 237 |
| `crt_dp_dq_recover_d` | `CRTRSA.v` | 255 |
| `inverse_unique_mod` | `CRTRSA.v` | 270 |
| `local_inv_is_crt_dp` | `CRTRSA.v` | 297 |
| `local_inv_is_crt_dq` | `CRTRSA.v` | 312 |
| `miller_multiple_annihilates` | `MillerHeight.v` | 200 |
| `miller_height_exists_multiple` | `MillerHeight.v` | 218 |
| `miller_from_multiple` | `MillerHeight.v` | 256 |
| `miller_from_multiple_q` | `MillerHeight.v` | 279 |
| `trapdoor_exponent_divides_lambda` | `MillerHeight.v` | 302 |
| `miller_from_trapdoor_exponent` | `MillerHeight.v` | 313 |
| `miller_from_trapdoor_exponent_q` | `MillerHeight.v` | 330 |
| `residual_square_denotes_X2` | `SrsaResidualGRA.v` | 751 |
| `residual_square_degree_eq_bound` | `SrsaResidualGRA.v` | 756 |
| `residual_square_eval` | `SrsaResidualGRA.v` | 766 |
| `residual_square_Q_degree_is_6` | `SrsaResidualGRA.v` | 775 |
| `residual_square_Q_nth1` | `SrsaResidualGRA.v` | 783 |
| `residual_square_cannot_vanish_on_ZN_units` | `SrsaResidualGRA.v` | 791 |
| `residual_square_unit_2_not_root` | `SrsaResidualGRA.v` | 811 |
| `residual_cube_is_nodiv` | `SrsaResidualGRA.v` | 821 |
| `residual_cube_denotes_X3` | `SrsaResidualGRA.v` | 825 |
| `residual_cube_degree_eq_bound` | `SrsaResidualGRA.v` | 830 |
| `residual_cube_eval` | `SrsaResidualGRA.v` | 842 |
| `residual_cube_Q_degree_is_9` | `SrsaResidualGRA.v` | 853 |
| `residual_cube_Q_nth1` | `SrsaResidualGRA.v` | 861 |
| `residual_cube_cannot_vanish_on_ZN_units` | `SrsaResidualGRA.v` | 869 |
| `residual_cube_unit_2_not_root` | `SrsaResidualGRA.v` | 893 |
| `residual_trapdoor_inverts_pin` | `SrsaResidualGRA.v` | 905 |
| `residual_trapdoor_not_a_low_degree_identity` | `SrsaResidualGRA.v` | 909 |
| `trapdoor_monomial_inverts_all_units` | `SrsaRootPoly.v` | 1038 |
| `monomial_all_units_invert_is_trapdoor` | `SrsaRootPoly.v` | 1066 |
| `pin_d_monomial_is_trapdoor` | `SrsaRootPoly.v` | 1107 |
| `pin_dp_monomial_not_trapdoor` | `SrsaRootPoly.v` | 1111 |
| `pin_dq_monomial_not_trapdoor` | `SrsaRootPoly.v` | 1115 |
| `pin_d_plus_lam_is_trapdoor` | `SrsaRootPoly.v` | 1119 |
| `pin_d_plus_2lam_is_trapdoor` | `SrsaRootPoly.v` | 1123 |
| `pin_trapdoor_k_M_pos` | `SrsaRootPoly.v` | 1127 |
| `monomial_all_units_invert_miller` | `SrsaRootPoly.v` | 1140 |
| `pin_miller_from_d_plus_lam` | `SrsaRootPoly.v` | 1171 |
| `pin_base2_height_p_at_35` | `SrsaRootPoly.v` | 1193 |
| `pin_base2_height_q_at_35` | `SrsaRootPoly.v` | 1201 |
| `pin_odd_part_d_plus_2lam` | `SrsaRootPoly.v` | 1211 |
| `pin_miller_from_d_plus_2lam` | `SrsaRootPoly.v` | 1215 |
| `pin_d_mod_pminus1` | `SrsaRootPoly.v` | 1239 |
| `pin_d_mod_qminus1` | `SrsaRootPoly.v` | 1243 |
| `pin_inv3_p_is_crt_dp` | `SrsaRootPoly.v` | 1247 |
| `pin_inv3_q_is_crt_dq` | `SrsaRootPoly.v` | 1251 |
| `pin_local_inverses_recover_d` | `SrsaRootPoly.v` | 1255 |
| `pin_local_inv_unique_p` | `SrsaRootPoly.v` | 1273 |
| `pin_local_inv_unique_q` | `SrsaRootPoly.v` | 1285 |
| `invert_all_units_monomial_degree_mod_lam` | `SrsaRootPoly.v` | 2050 |
| `invert_all_units_both_folds_are_local_monomials` | `SrsaRootPoly.v` | 2458 |
| `invert_all_units_fold_degrees_crt_d` | `SrsaRootPoly.v` | 2474 |
| `pin_crt_binomial_both_folds` | `SrsaRootPoly.v` | 2634 |

_43 refuses, 3 open targets, 0 used-as-hypothesis weaknesses, 54 does-not-discharge rows._
