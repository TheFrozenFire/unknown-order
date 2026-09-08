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
| `strong_rsa_solver_constructs_factor_open_named` | `Hardness.v` | 80 | open | — |
| `residual_solver_constructs_factor_open_named` | `StrongRSAPeel.v` | 289 | open | — |
| `rsa_inverter_constructs_factor_open_named` | `TranscriptOracle.v` | 588 | open | — |
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
| `gcd_powm_minus_1` | `Hardness.v` | 518 |
| `leftover_mismatch_factors` | `Hardness.v` | 531 |
| `miller_multiple_annihilates` | `MillerHeight.v` | 200 |
| `miller_height_exists_multiple` | `MillerHeight.v` | 218 |
| `miller_from_multiple` | `MillerHeight.v` | 256 |
| `miller_from_multiple_q` | `MillerHeight.v` | 279 |
| `trapdoor_exponent_divides_lambda` | `MillerHeight.v` | 302 |
| `miller_from_trapdoor_exponent` | `MillerHeight.v` | 313 |
| `miller_from_trapdoor_exponent_q` | `MillerHeight.v` | 330 |
| `mod_cbrt_nonunit_factors` | `SrsaModCbrt.v` | 160 |
| `pin_trapdoor_solver_returns_e` | `SrsaModCbrt.v` | 378 |
| `residual_solver_reduced_pin_e_is_mod_cbrt` | `SrsaModCbrt.v` | 382 |
| `residual_solver_reduced_pin_e_is_trapdoor` | `SrsaModCbrt.v` | 398 |
| `residual_solver_reduced_pin_e_constructs_factor` | `SrsaModCbrt.v` | 420 |
| `is_order_pin_y_40` | `SrsaOrderArrows.v` | 30 |
| `order_yields_residual_sRSA` | `SrsaOrderArrows.v` | 40 |
| `order_yields_residual_pin` | `SrsaOrderArrows.v` | 62 |
| `order_invert_pin_is_cube_root` | `SrsaOrderArrows.v` | 78 |
| `residual_mismatch_factors` | `SrsaOrderArrows.v` | 94 |
| `leftover_x_one_sided_pin` | `SrsaOrderArrows.v` | 106 |
| `leftover_x_mismatch_factors_pin` | `SrsaOrderArrows.v` | 115 |
| `residual_mismatch_factors_pin` | `SrsaOrderArrows.v` | 124 |
| `leftover_y_one_sided_pin` | `SrsaOrderArrows.v` | 136 |
| `order_mismatch_factors_pin` | `SrsaOrderArrows.v` | 145 |
| `leftover_77_one_sided` | `SrsaOrderArrows.v` | 154 |
| `leftover_77_mismatch_factors` | `SrsaOrderArrows.v` | 163 |
| `matching_247_not_one_sided` | `SrsaOrderArrows.v` | 176 |
| `matching_247_gcd_not_proper` | `SrsaOrderArrows.v` | 184 |
| `matching_247_two_sided_gcd_is_N` | `SrsaOrderArrows.v` | 194 |
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
| `trapdoor_monomial_inverts_all_units` | `SrsaRootPoly.v` | 1041 |
| `monomial_all_units_invert_is_trapdoor` | `SrsaRootPoly.v` | 1069 |
| `pin_d_monomial_is_trapdoor` | `SrsaRootPoly.v` | 1110 |
| `pin_dp_monomial_not_trapdoor` | `SrsaRootPoly.v` | 1114 |
| `pin_dq_monomial_not_trapdoor` | `SrsaRootPoly.v` | 1118 |
| `pin_d_plus_lam_is_trapdoor` | `SrsaRootPoly.v` | 1122 |
| `pin_d_plus_2lam_is_trapdoor` | `SrsaRootPoly.v` | 1126 |
| `pin_trapdoor_k_M_pos` | `SrsaRootPoly.v` | 1130 |
| `monomial_all_units_invert_miller` | `SrsaRootPoly.v` | 1143 |
| `pin_miller_from_d_plus_lam` | `SrsaRootPoly.v` | 1174 |
| `pin_base2_height_p_at_35` | `SrsaRootPoly.v` | 1196 |
| `pin_base2_height_q_at_35` | `SrsaRootPoly.v` | 1204 |
| `pin_odd_part_d_plus_2lam` | `SrsaRootPoly.v` | 1214 |
| `pin_miller_from_d_plus_2lam` | `SrsaRootPoly.v` | 1218 |
| `pin_d_mod_pminus1` | `SrsaRootPoly.v` | 1242 |
| `pin_d_mod_qminus1` | `SrsaRootPoly.v` | 1246 |
| `pin_inv3_p_is_crt_dp` | `SrsaRootPoly.v` | 1250 |
| `pin_inv3_q_is_crt_dq` | `SrsaRootPoly.v` | 1254 |
| `pin_local_inverses_recover_d` | `SrsaRootPoly.v` | 1258 |
| `pin_local_inv_unique_p` | `SrsaRootPoly.v` | 1276 |
| `pin_local_inv_unique_q` | `SrsaRootPoly.v` | 1288 |
| `invert_all_units_monomial_degree_mod_lam` | `SrsaRootPoly.v` | 2053 |
| `invert_all_units_both_folds_are_local_monomials` | `SrsaRootPoly.v` | 2461 |
| `invert_all_units_fold_degrees_crt_d` | `SrsaRootPoly.v` | 2477 |
| `pin_crt_binomial_both_folds` | `SrsaRootPoly.v` | 2637 |
| `poly_degree_gt_nth_zero` | `SrsaRootPoly.v` | 2658 |
| `leftover_kernel_span` | `SrsaRootPoly.v` | 2666 |
| `leftover_monic_is_kernel` | `SrsaRootPoly.v` | 2695 |
| `pin_geo_kernel_inv_mod` | `SrsaRootPoly.v` | 2728 |
| `leftover_kernel_exists_scalar` | `SrsaRootPoly.v` | 2732 |
| `class_sum_from_add` | `SrsaRootPoly.v` | 2916 |
| `class_sum_from_map_mul` | `SrsaRootPoly.v` | 2930 |
| `class_sum_poly_sub` | `SrsaRootPoly.v` | 2940 |
| `invert_all_units_diff_fold_p_zero` | `SrsaRootPoly.v` | 2949 |
| `invert_all_units_diff_fold_q_zero` | `SrsaRootPoly.v` | 2966 |
| `pin_NX20_root_poly_inverts` | `SrsaRootPoly.v` | 2986 |
| `pin_crt_vs_NX20_diff_folds_zero` | `SrsaRootPoly.v` | 3000 |
| `pin_trapdoor_monomial_poly_inverts` | `SrsaRootPoly.v` | 3020 |
| `pin_crt_vs_monomial_diff_folds_zero` | `SrsaRootPoly.v` | 3032 |
| `pin_binomial_plus_N_kernel_cong_mod_N` | `SrsaRootPoly.v` | 3063 |
| `pin_binomial_plus_N_kernel_deg_lt_qminus1` | `SrsaRootPoly.v` | 3075 |
| `pin_miller_from_d_factors` | `SrsaRootPoly.v` | 3079 |
| `invert_all_units_poly_constructs_factor` | `SrsaRootPoly.v` | 3097 |
| `nodiv_gra_invert_all_units_constructs_factor` | `SrsaRootPoly.v` | 3125 |
| `invert_all_units_rational_is_trapdoor_map` | `SrsaRootPoly.v` | 3158 |
| `invert_all_units_rational_constructs_factor` | `SrsaRootPoly.v` | 3216 |
| `invert_all_units_rational_over_one` | `SrsaRootPoly.v` | 3232 |
| `invert_all_units_rational_monomial_over_one` | `SrsaRootPoly.v` | 3254 |
| `invert_all_units_rational_Xd1_over_X` | `SrsaRootPoly.v` | 3263 |
| `unit_ginv_gra_invert_all_units_constructs_factor` | `SrsaRootPoly.v` | 3296 |
| `srsa_residual_pin` | `StrongRSAPeel.v` | 257 |
| `srsa_residual_pin187` | `StrongRSAPeel.v` | 268 |

### `rsa_inverter_constructs_factor_open_named`

| Closed result | File | Line |
|---|---|---:|
| `rabin_oracle_nonassociate_factors` | `RabinWilliams.v` | 272 |
| `eth_root_nonunit_factors` | `SrsaInverter.v` | 61 |
| `pin_eth_root_p_factors` | `SrsaInverter.v` | 129 |
| `rsa_inverter_reduced_units_is_trapdoor` | `SrsaInverter.v` | 187 |
| `rsa_inverter_reduced_units_constructs_factor` | `SrsaInverter.v` | 204 |
| `inverter_as_residual_returns_e` | `SrsaInverter.v` | 230 |
| `rsa_inverter_recovers_message` | `TranscriptOracle.v` | 592 |

### `strong_rsa_solver_constructs_factor_open_named`

| Closed result | File | Line |
|---|---|---:|
| `rsa_solution_is_strong_RSA` | `Hardness.v` | 84 |
| `lambda_solves_strong_RSA` | `Hardness.v` | 98 |
| `strong_RSA_trivial_at_one` | `Hardness.v` | 122 |
| `rsa_trivial_at_one` | `Hardness.v` | 130 |
| `order_inverts_in_cyclic` | `Hardness.v` | 467 |
| `order_yields_strong_RSA` | `Hardness.v` | 492 |
| `gcd_powm_minus_1` | `Hardness.v` | 518 |
| `leftover_mismatch_factors` | `Hardness.v` | 531 |
| `pin_lambda_strong_solver_output_is_unit` | `SrsaInverter.v` | 257 |
| `pin_lambda_plus_one_does_not_split` | `SrsaInverter.v` | 265 |
| `pin_lambda_strong_solver_not_residual` | `SrsaInverter.v` | 269 |
| `strong_rsa_solver_pin_e_constructs_factor` | `SrsaInverter.v` | 299 |
| `residual_mismatch_factors` | `SrsaOrderArrows.v` | 94 |
| `leftover_x_one_sided_pin` | `SrsaOrderArrows.v` | 106 |
| `leftover_x_mismatch_factors_pin` | `SrsaOrderArrows.v` | 115 |
| `residual_mismatch_factors_pin` | `SrsaOrderArrows.v` | 124 |
| `leftover_y_one_sided_pin` | `SrsaOrderArrows.v` | 136 |
| `order_mismatch_factors_pin` | `SrsaOrderArrows.v` | 145 |
| `leftover_77_one_sided` | `SrsaOrderArrows.v` | 154 |
| `leftover_77_mismatch_factors` | `SrsaOrderArrows.v` | 163 |
| `matching_247_not_one_sided` | `SrsaOrderArrows.v` | 176 |
| `matching_247_gcd_not_proper` | `SrsaOrderArrows.v` | 184 |
| `matching_247_two_sided_gcd_is_N` | `SrsaOrderArrows.v` | 194 |

_43 refuses, 3 open targets, 0 used-as-hypothesis weaknesses, 133 does-not-discharge rows._
