# Print Assumptions snapshot — UnknownOrder

**Headline:** all 2496 named results are **Closed under the global context** — **0 load-bearing axioms** across the whole corpus.

Captured for 2496 results across 119 files.

Counts:

- **axioms_total** — every entry under `Axioms:` for the result.
- **axioms_load_bearing** — total minus kernel primitives (KERNEL_AXIOM_PREFIXES). For a pure-stdlib tree the prefix set is empty and load-bearing == total.

## Accumulator.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `membership_witness_is_root` | 34 | 0 | 0 | OK |
| `forged_mem_is_adaptive_root` | 45 | 0 | 0 | OK |
| `rsa_acc_add_is_powm` | 56 | 0 | 0 | OK |
| `rsa_mem_wit_is_powm` | 61 | 0 | 0 | OK |
| `cl_acc_add_is_exp` | 72 | 0 | 0 | OK |
| `cl_has_no_trapdoor_update` | 79 | 0 | 0 | OK |
| `rsa_public_has_no_trapdoor_update` | 83 | 0 | 0 | OK |
| `rsa_acc_forge_from_lambda` | 87 | 0 | 0 | OK |
| `cl_odd_invertible_mod_two` | 102 | 0 | 0 | OK |
| `cl_no_trapdoor_from_two` | 111 | 0 | 0 | OK |
| `rsa_composite_member_splits_witness` | 125 | 0 | 0 | OK |
| `powm_mul_l_mod` | 158 | 0 | 0 | OK |
| `powm_inv_cancels` | 168 | 0 | 0 | OK |
| `mul_pow_mod_cong` | 184 | 0 | 0 | OK |
| `zmul_nonneg_eq_1` | 200 | 0 | 0 | OK |
| `shamir_neg_beta` | 207 | 0 | 0 | OK |
| `shamir_trick` | 248 | 0 | 0 | OK |
| `bdm_coprime_gives_product_witness` | 304 | 0 | 0 | OK |
| `bdm_same_bits_still_splits` | 326 | 0 | 0 | OK |
| `llx_complete_nonneg` | 357 | 0 | 0 | OK |
| `llx_complete` | 379 | 0 | 0 | OK |
| `llx_Bx_eq_g_times_inv` | 415 | 0 | 0 | OK |
| `g_times_inv_succ` | 450 | 0 | 0 | OK |
| `llx_extract_root` | 466 | 0 | 0 | OK |
| `bezout3` | 529 | 0 | 0 | OK |
| `llx_lambda_forges_nonmem` | 543 | 0 | 0 | OK |
| `rsa_trapdoor_add` | 596 | 0 | 0 | OK |
| `peng_bao_member_still_forges` | 631 | 0 | 0 | OK |
| `icomm_cancel_h` | 663 | 0 | 0 | OK |
| `icomm_binding_is_fractional_root` | 707 | 0 | 0 | OK |
| `icomm_same_msg_is_annihilator` | 723 | 0 | 0 | OK |
| `lipmaa_cl_membership_is_P_Root` | 748 | 0 | 0 | OK |

## AddGate.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `add_gate_sat` | 32 | 0 | 0 | OK |
| `add_gate_complete` | 43 | 0 | 0 | OK |
| `add_is_public_sum` | 63 | 0 | 0 | OK |

## AllBits.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `all_bits_nn` | 28 | 0 | 0 | OK |
| `all_bits_value_nonneg` | 36 | 0 | 0 | OK |
| `all_bits_qap` | 42 | 0 | 0 | OK |
| `three_bit_encoding` | 53 | 0 | 0 | OK |

## ArithShape.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `arith_newton_inv3` | 28 | 0 | 0 | OK |
| `arith_newton_from_one` | 32 | 0 | 0 | OK |
| `arith_e5_divides_yminus1` | 39 | 0 | 0 | OK |
| `arith_e7_divides_yminus1` | 43 | 0 | 0 | OK |
| `arith_e7_residual` | 47 | 0 | 0 | OK |
| `arith_xy_period_residual` | 53 | 0 | 0 | OK |
| `arith_xy_period_no_split` | 57 | 0 | 0 | OK |
| `arith_witness_gap_no_split` | 69 | 0 | 0 | OK |
| `arith_takagi_shape` | 75 | 0 | 0 | OK |
| `arith_takagi_euler_p2` | 81 | 0 | 0 | OK |
| `arith_takagi_p_on_tape` | 85 | 0 | 0 | OK |
| `arith_double_y_not_root` | 91 | 0 | 0 | OK |
| `prime_37` | 97 | 0 | 0 | OK |
| `arith_nextprime_e37` | 112 | 0 | 0 | OK |
| `arith_nextprime_residual` | 118 | 0 | 0 | OK |
| `arith_nextprime_root_is_49` | 122 | 0 | 0 | OK |
| `arith_cf_euclidean` | 128 | 0 | 0 | OK |
| `arith_cf_convergents_not_root` | 132 | 0 | 0 | OK |
| `arith_two_moduli_coprime` | 138 | 0 | 0 | OK |
| `arith_two_moduli_same_x` | 142 | 0 | 0 | OK |
| `three_prime_357` | 149 | 0 | 0 | OK |
| `arith_mixed_pqr_is_factor` | 156 | 0 | 0 | OK |
| `arith_composite_e15_shares_lambda` | 168 | 0 | 0 | OK |
| `arith_36_not_in_ltwo` | 184 | 0 | 0 | OK |
| `arith_two_and_thirtysix_same_order_period` | 188 | 0 | 0 | OK |

## AuxBil.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `aux_is_self_bil` | 30 | 0 | 0 | OK |
| `aux_self_bil_checks_pot` | 40 | 0 | 0 | OK |
| `aux_self_bil_evaluates_pot` | 54 | 0 | 0 | OK |
| `aux_eval_publishes_next` | 72 | 0 | 0 | OK |
| `forget_aux_is_self_bil` | 82 | 0 | 0 | OK |

## BGH.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `jacobi_additive_pairing` | 29 | 0 | 0 | OK |
| `jacobi_neg1_on_blum` | 58 | 0 | 0 | OK |
| `jacobi_one_mul_closed` | 73 | 0 | 0 | OK |
| `cocks_pair_first_decrypts` | 95 | 0 | 0 | OK |
| `cocks_pair_second_decrypts` | 118 | 0 | 0 | OK |
| `cocks_pair_covers_blum` | 141 | 0 | 0 | OK |

## BatchOrder.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `shared_pminus1_divides_gcd` | 27 | 0 | 0 | OK |
| `gcd_pminus1_pos` | 36 | 0 | 0 | OK |
| `distinct_semiprimes_coprime` | 46 | 0 | 0 | OK |
| `batch_p1_splits_pair` | 64 | 0 | 0 | OK |
| `shared_pminus1_is_ap` | 91 | 0 | 0 | OK |

## BinForms.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `bqf_inv_disc` | 44 | 0 | 0 | OK |
| `bqf_inv_primitive` | 48 | 0 | 0 | OK |
| `bqf_inv_inv` | 56 | 0 | 0 | OK |
| `bqf_id_a` | 63 | 0 | 0 | OK |
| `four_times_div4` | 69 | 0 | 0 | OK |
| `one_minus_D_mod4` | 78 | 0 | 0 | OK |
| `bqf_id_disc` | 89 | 0 | 0 | OK |
| `bqf_id_primitive` | 107 | 0 | 0 | OK |
| `bqf_id_of_disc` | 114 | 0 | 0 | OK |
| `bqf_id_disc_neg4` | 118 | 0 | 0 | OK |
| `bqf_id_disc_neg47` | 121 | 0 | 0 | OK |
| `bqf_id_disc_neg23` | 124 | 0 | 0 | OK |
| `bqf_id_of_disc_neg47` | 127 | 0 | 0 | OK |
| `of_disc_a_nz` | 131 | 0 | 0 | OK |
| `bqf_id_ambiguous_mod0` | 152 | 0 | 0 | OK |
| `disc_neg47` | 158 | 0 | 0 | OK |
| `sl2_I_ok` | 204 | 0 | 0 | OK |
| `sl2_T_ok` | 207 | 0 | 0 | OK |
| `sl2_S_ok` | 210 | 0 | 0 | OK |
| `bqf_act_I` | 213 | 0 | 0 | OK |
| `bqf_equiv_refl` | 220 | 0 | 0 | OK |
| `sl2_mul_det` | 235 | 0 | 0 | OK |
| `sl2_mul_ok` | 243 | 0 | 0 | OK |
| `sl2_inverse_ok` | 249 | 0 | 0 | OK |
| `bqf_act_mul` | 261 | 0 | 0 | OK |
| `bqf_equiv_trans` | 271 | 0 | 0 | OK |
| `bqf_act_disc` | 280 | 0 | 0 | OK |
| `bqf_act_disc_sl2` | 289 | 0 | 0 | OK |
| `bqf_act_T` | 295 | 0 | 0 | OK |
| `bqf_act_S` | 306 | 0 | 0 | OK |
| `ambiguous_equiv_inv` | 317 | 0 | 0 | OK |
| `bqf_act_eval` | 340 | 0 | 0 | OK |
| `bqf_id_eval_1` | 350 | 0 | 0 | OK |
| `z_le_abs` | 357 | 0 | 0 | OK |
| `reduced_eval_ge_a` | 360 | 0 | 0 | OK |
| `reduced_a_gt_1_not_principal` | 399 | 0 | 0 | OK |
| `compose_gcd_id_l` | 449 | 0 | 0 | OK |
| `dirichlet_B_id_l` | 456 | 0 | 0 | OK |
| `compose_id_left` | 463 | 0 | 0 | OK |
| `compose_inv_gcd` | 489 | 0 | 0 | OK |
| `compose_inv_leading_one` | 497 | 0 | 0 | OK |
| `dirichlet_B_inv_plus_2` | 507 | 0 | 0 | OK |
| `four_divides_B2_minus_disc_inv` | 520 | 0 | 0 | OK |
| `reconstruct_disc_div4` | 530 | 0 | 0 | OK |
| `compose_inv_c` | 537 | 0 | 0 | OK |
| `compose_inv_primitive` | 550 | 0 | 0 | OK |
| `compose_inv_of_disc` | 561 | 0 | 0 | OK |
| `form_a_one_equiv_id` | 581 | 0 | 0 | OK |
| `compose_inv_equiv_id` | 658 | 0 | 0 | OK |
| `ambiguous_div_is_ambiguous` | 684 | 0 | 0 | OK |
| `solve_cong_target_0` | 688 | 0 | 0 | OK |
| `compose_self_gcd_div` | 699 | 0 | 0 | OK |
| `dirichlet_B_self_div` | 716 | 0 | 0 | OK |
| `compose_self_leading_one` | 725 | 0 | 0 | OK |
| `compose_self_b` | 737 | 0 | 0 | OK |
| `compose_self_c` | 743 | 0 | 0 | OK |
| `four_divides_b2_minus_disc` | 759 | 0 | 0 | OK |
| `compose_self_of_disc` | 766 | 0 | 0 | OK |
| `compose_self_ambiguous_equiv_id` | 788 | 0 | 0 | OK |
| `compose_assoc_id_inv` | 818 | 0 | 0 | OK |
| `amb_from_div_ambiguous` | 840 | 0 | 0 | OK |
| `amb_from_div_disc_mod0` | 848 | 0 | 0 | OK |
| `amb_from_div_disc_mod1` | 866 | 0 | 0 | OK |
| `iq_neg23` | 906 | 0 | 0 | OK |
| `iq_neg47` | 909 | 0 | 0 | OK |
| `iq_neg87` | 912 | 0 | 0 | OK |
| `iq_neg403` | 915 | 0 | 0 | OK |
| `iq_neg455` | 918 | 0 | 0 | OK |
| `form_neg87_amb_of_disc` | 921 | 0 | 0 | OK |
| `form_neg403_amb_of_disc` | 924 | 0 | 0 | OK |
| `form_neg403_amb_red_of_disc` | 927 | 0 | 0 | OK |
| `form_neg455_5_of_disc` | 930 | 0 | 0 | OK |
| `form_neg455_7_of_disc` | 933 | 0 | 0 | OK |
| `form_neg455_13_red_of_disc` | 936 | 0 | 0 | OK |
| `form_neg87_amb_reduced` | 939 | 0 | 0 | OK |
| `form_neg403_amb_red_reduced` | 942 | 0 | 0 | OK |
| `form_neg455_5_reduced` | 945 | 0 | 0 | OK |
| `form_neg455_7_reduced` | 948 | 0 | 0 | OK |
| `form_neg455_13_red_reduced` | 951 | 0 | 0 | OK |
| `form_neg87_amb_is_ambiguous` | 954 | 0 | 0 | OK |
| `form_neg403_amb_is_ambiguous` | 957 | 0 | 0 | OK |
| `form_neg403_amb_red_is_ambiguous` | 960 | 0 | 0 | OK |
| `form_neg455_5_is_ambiguous` | 963 | 0 | 0 | OK |
| `form_neg455_7_is_ambiguous` | 966 | 0 | 0 | OK |
| `form_neg455_13_red_is_ambiguous` | 969 | 0 | 0 | OK |
| `form_neg87_not_principal` | 972 | 0 | 0 | OK |
| `form_neg403_not_principal` | 981 | 0 | 0 | OK |
| `form_neg455_5_not_principal` | 990 | 0 | 0 | OK |
| `form_neg455_7_not_principal` | 999 | 0 | 0 | OK |
| `form_neg455_13_not_principal` | 1008 | 0 | 0 | OK |
| `catalog_compose_inv_is_principal` | 1026 | 0 | 0 | OK |
| `catalog_wins_LowOrder_B2` | 1037 | 0 | 0 | OK |
| `bqf_exp_0` | 1070 | 0 | 0 | OK |
| `bqf_exp_1` | 1073 | 0 | 0 | OK |
| `bqf_exp_2` | 1083 | 0 | 0 | OK |
| `bqf_exp_2_ambiguous_div` | 1093 | 0 | 0 | OK |

## BitLeak.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `high_bits_unknown_is_x` | 37 | 0 | 0 | OK |
| `roca_unknown_is_k` | 43 | 0 | 0 | OK |
| `bitleak_poly_divides_N` | 59 | 0 | 0 | OK |

## BitLogic.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `bit_and_is_mul` | 31 | 0 | 0 | OK |
| `bit_and_closed` | 41 | 0 | 0 | OK |
| `bit_or_table` | 48 | 0 | 0 | OK |
| `bit_or_closed` | 57 | 0 | 0 | OK |
| `bit_xor_table` | 64 | 0 | 0 | OK |
| `bit_xor_closed` | 72 | 0 | 0 | OK |
| `bit_or_from_and` | 79 | 0 | 0 | OK |
| `bit_xor_from_and` | 84 | 0 | 0 | OK |

## BitLt.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `bit_lt_table` | 24 | 0 | 0 | OK |
| `bit_lt_closed` | 35 | 0 | 0 | OK |
| `bit_lt_is_and` | 42 | 0 | 0 | OK |
| `bit_lt_mul` | 46 | 0 | 0 | OK |

## BitSum.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `bit_value_nil` | 28 | 0 | 0 | OK |
| `bit_value_cons` | 31 | 0 | 0 | OK |
| `bit_value_nonneg` | 35 | 0 | 0 | OK |
| `bit_value_cons_encoding` | 50 | 0 | 0 | OK |
| `bit_value_range2` | 66 | 0 | 0 | OK |
| `nested_square` | 70 | 0 | 0 | OK |

## BlindRSA.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `chaum_sign_blinded_is_raw_times_r` | 25 | 0 | 0 | OK |
| `chaum_unblind_is_raw_sign` | 46 | 0 | 0 | OK |

## BonehVenkatesan.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `bv_two_is_integer_cube` | 26 | 0 | 0 | OK |
| `bv_36_is_not_integer_cube` | 30 | 0 | 0 | OK |
| `cube_is_powm3_pin` | 34 | 0 | 0 | OK |
| `integer_cube_root_8` | 38 | 0 | 0 | OK |
| `bv_groot_8_is_2` | 42 | 0 | 0 | OK |
| `bv_root_gate_is_not_rsa_inverter` | 46 | 0 | 0 | OK |
| `bv_groot_handle_is_2` | 75 | 0 | 0 | OK |
| `bv_unwound_handle_is_2` | 79 | 0 | 0 | OK |
| `bv_with_root_outputs_11` | 83 | 0 | 0 | OK |
| `bv_unwound_outputs_11` | 87 | 0 | 0 | OK |
| `bv_unwind_one_cube` | 91 | 0 | 0 | OK |
| `bv_few_query_low_e_drops_oracle` | 96 | 0 | 0 | OK |
| `bv_factor_from_root_handle` | 102 | 0 | 0 | OK |
| `bv_42_cube_in_Z_is_not_36` | 108 | 0 | 0 | OK |
| `bv_query_leak_already_factors` | 112 | 0 | 0 | OK |

## BrownSLP.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `slp_carmichael_is_functional` | 27 | 0 | 0 | OK |
| `slp_solver_not_poly_identity_linear` | 31 | 0 | 0 | OK |
| `slp_solver_not_poly_identity_last` | 35 | 0 | 0 | OK |
| `X81_minus_X_leading_not_zero_mod_11` | 39 | 0 | 0 | OK |
| `brown_low_degree_identity_forbids_N_dividing_minus1` | 43 | 0 | 0 | OK |
| `two_pow_81_is_two_mod_N` | 47 | 0 | 0 | OK |
| `brown_dual_pow27_fst` | 60 | 0 | 0 | OK |
| `brown_dual_not_identity` | 64 | 0 | 0 | OK |
| `brown_dual_tangent_mod_N` | 68 | 0 | 0 | OK |
| `brown_dual_gcd_pin` | 72 | 0 | 0 | OK |
| `brown_ed_minus_1_is_80` | 76 | 0 | 0 | OK |

## CPP17.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `cpp17_witness_is_rsa` | 21 | 0 | 0 | OK |
| `cpp17_complete_pin` | 25 | 0 | 0 | OK |
| `cpp17_second_transcript` | 32 | 0 | 0 | OK |
| `cpp17_shamir_gcd_pin` | 39 | 0 | 0 | OK |
| `cpp17_extract_is_fixed_e` | 43 | 0 | 0 | OK |
| `cpp17_protocol_e_is_three` | 51 | 0 | 0 | OK |
| `cpp17_srsa_other_pair` | 55 | 0 | 0 | OK |
| `cpp17_sigma_does_not_output_that_pair` | 62 | 0 | 0 | OK |

## CRTRSA.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `lambda_gt_1_of` | 27 | 0 | 0 | OK |
| `ed_one_mod_pminus1_of` | 43 | 0 | 0 | OK |
| `dp_congruent_d` | 64 | 0 | 0 | OK |
| `crt_dp_annihilates` | 68 | 0 | 0 | OK |
| `short_dp_short_annihilator` | 105 | 0 | 0 | OK |
| `lambda_semiprime_comm` | 118 | 0 | 0 | OK |
| `crt_dq_annihilates` | 122 | 0 | 0 | OK |
| `short_dq_short_annihilator` | 135 | 0 | 0 | OK |
| `powm_reduce_pminus1` | 151 | 0 | 0 | OK |
| `crt_decrypt_eq_rsa_dec` | 179 | 0 | 0 | OK |
| `cong_mod_lcm` | 237 | 0 | 0 | OK |
| `crt_dp_dq_recover_d` | 255 | 0 | 0 | OK |
| `inverse_unique_mod` | 270 | 0 | 0 | OK |
| `local_inv_is_crt_dp` | 297 | 0 | 0 | OK |
| `local_inv_is_crt_dq` | 312 | 0 | 0 | OK |

## ChallengePrime.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `ch_encode_odd` | 30 | 0 | 0 | OK |
| `ch_accept_is_prime` | 37 | 0 | 0 | OK |
| `ch_encode_not_slot_residue` | 41 | 0 | 0 | OK |
| `ch_image_is_not_slot_image` | 45 | 0 | 0 | OK |
| `ch_encode_not_roca_on_cas28` | 56 | 0 | 0 | OK |

## Circuit.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `prod_add_sat` | 24 | 0 | 0 | OK |
| `prod_add_complete` | 39 | 0 | 0 | OK |
| `mul_public_first` | 64 | 0 | 0 | OK |

## ClassGroupWall.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `adaptive_root_trivial_from_lambda` | 35 | 0 | 0 | OK |
| `typeB_pminus1_is_cyc1` | 48 | 0 | 0 | OK |
| `typeB_pplus1_is_cyc2` | 52 | 0 | 0 | OK |
| `typeB_leak_needs_modulus` | 70 | 0 | 0 | OK |
| `iq_disc_agrees` | 81 | 0 | 0 | OK |
| `rsa_minus1_is_constructible` | 103 | 0 | 0 | OK |
| `unrestricted_LowOrder_won_by_Cl2` | 107 | 0 | 0 | OK |
| `restricted_LowOrder_excludes_Cl2` | 111 | 0 | 0 | OK |
| `catalog_ambiguous_is_constructible` | 119 | 0 | 0 | OK |
| `public_2_annihilator_hits_ambiguous` | 139 | 0 | 0 | OK |
| `disc_mod1_is_odd` | 145 | 0 | 0 | OK |
| `adaptive_root_relation_is_presentation_blind` | 157 | 0 | 0 | OK |
| `iq_neg31` | 180 | 0 | 0 | OK |
| `form_neg31_ord3_of_disc` | 183 | 0 | 0 | OK |
| `form_neg31_ord3_reduced` | 189 | 0 | 0 | OK |
| `form_neg31_ord3_not_ambiguous` | 192 | 0 | 0 | OK |
| `form_neg31_ord3_not_principal` | 197 | 0 | 0 | OK |
| `form_neg31_sq_compute` | 206 | 0 | 0 | OK |
| `form_neg31_cube_compute` | 210 | 0 | 0 | OK |
| `form_neg31_exp2` | 214 | 0 | 0 | OK |
| `form_neg31_exp3` | 221 | 0 | 0 | OK |
| `form_neg31_sq_equiv_inv` | 230 | 0 | 0 | OK |
| `form_neg31_inv_reduced` | 237 | 0 | 0 | OK |
| `form_neg31_inv_of_disc` | 240 | 0 | 0 | OK |
| `form_neg31_inv_not_principal` | 247 | 0 | 0 | OK |
| `form_neg31_actS_inv_is_sq` | 256 | 0 | 0 | OK |
| `form_neg31_sq_not_principal` | 260 | 0 | 0 | OK |
| `sl2_reduce_cube_ok` | 274 | 0 | 0 | OK |
| `form_neg31_cube_equiv_id` | 277 | 0 | 0 | OK |
| `form_neg31_exp3_equiv_id` | 284 | 0 | 0 | OK |
| `form_neg31_exp1` | 288 | 0 | 0 | OK |
| `mersenne31_wins_restricted_LowOrder` | 307 | 0 | 0 | OK |
| `mersenne31_is_odd_order` | 324 | 0 | 0 | OK |
| `shanks_disc_2` | 340 | 0 | 0 | OK |
| `shanks_form_2` | 343 | 0 | 0 | OK |
| `shanks_form_disc` | 346 | 0 | 0 | OK |
| `shanks_disc_3` | 356 | 0 | 0 | OK |
| `iq_neg107` | 359 | 0 | 0 | OK |
| `shanks_u3_of_disc` | 362 | 0 | 0 | OK |
| `shanks_u3_not_ambiguous` | 369 | 0 | 0 | OK |
| `shanks_u3_exp3_compute` | 380 | 0 | 0 | OK |
| `shanks_u3_cube_equiv_id` | 388 | 0 | 0 | OK |
| `shanks_u3_exp3_equiv_id` | 395 | 0 | 0 | OK |
| `shanks_family_has_3` | 399 | 0 | 0 | OK |
| `mersenne31_shanks_in_family_H` | 417 | 0 | 0 | OK |
| `mersenne31_shanks_not_ordinary_H` | 424 | 0 | 0 | OK |
| `bqf_exp_id` | 437 | 0 | 0 | OK |
| `neg31_id_annihilated_by_h` | 448 | 0 | 0 | OK |
| `form_neg31_inv_exp2` | 455 | 0 | 0 | OK |
| `form_neg31_inv_sq_equiv_f` | 462 | 0 | 0 | OK |
| `shanks_inv_square_is_shanks` | 469 | 0 | 0 | OK |
| `shanks_annihilated_by_h` | 477 | 0 | 0 | OK |

## Cocks.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `cocks_carefully_chosen` | 39 | 0 | 0 | OK |
| `cocks_ct_times_t` | 53 | 0 | 0 | OK |
| `euler_sign_cong_mod` | 84 | 0 | 0 | OK |
| `jacobi_cong` | 100 | 0 | 0 | OK |
| `jacobi_mul` | 124 | 0 | 0 | OK |
| `jacobi_sq_one` | 143 | 0 | 0 | OK |
| `jacobi_self_sq` | 163 | 0 | 0 | OK |
| `cocks_decrypt_jacobi` | 180 | 0 | 0 | OK |

## CoeffPoK.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `coeff_slot_eval` | 41 | 0 | 0 | OK |
| `slots_from_i` | 56 | 0 | 0 | OK |
| `slots_assemble` | 84 | 0 | 0 | OK |
| `two_coeff_assemble` | 98 | 0 | 0 | OK |
| `coeff_slot_eqdl` | 118 | 0 | 0 | OK |
| `coeff_slot_extracts` | 142 | 0 | 0 | OK |

## CondSwap.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `cswap_off` | 24 | 0 | 0 | OK |
| `cswap_on` | 32 | 0 | 0 | OK |
| `cswap_select` | 40 | 0 | 0 | OK |
| `cswap_involution` | 52 | 0 | 0 | OK |

## CramerShoup.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `powm_mul_base` | 24 | 0 | 0 | OK |
| `cs_verify_is_rsa` | 34 | 0 | 0 | OK |
| `cs_verify_is_strong_rsa` | 44 | 0 | 0 | OK |
| `cs_same_e_ratio` | 55 | 0 | 0 | OK |

## CubicResidue.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `cubing_invertible_on_units` | 46 | 0 | 0 | OK |
| `cube_root_map_is_cube` | 75 | 0 | 0 | OK |
| `cube_euler_one_direction` | 89 | 0 | 0 | OK |
| `three_divides_lambda_forbids_e3` | 128 | 0 | 0 | OK |
| `cube_euler_converse` | 146 | 0 | 0 | OK |
| `cube_euler_iff` | 186 | 0 | 0 | OK |
| `cube_N_implies_local` | 199 | 0 | 0 | OK |
| `cube_N_of_local` | 224 | 0 | 0 | OK |
| `cube_N_iff_both` | 251 | 0 | 0 | OK |
| `cube_root_coprime` | 263 | 0 | 0 | OK |
| `cube_euler_lambda_necessary` | 293 | 0 | 0 | OK |
| `prime_7_cubic` | 320 | 0 | 0 | OK |
| `prime_13` | 328 | 0 | 0 | OK |
| `prime_19` | 338 | 0 | 0 | OK |
| `cube_mixed_5_not_global` | 349 | 0 | 0 | OK |
| `cube_euler_lambda_not_sufficient_247` | 368 | 0 | 0 | OK |
| `pin_units_are_cubes` | 383 | 0 | 0 | OK |
| `omega_from_primitive_root` | 399 | 0 | 0 | OK |
| `primitive_3rd_root_cyclotomic` | 412 | 0 | 0 | OK |
| `cube_char_cubed_one` | 437 | 0 | 0 | OK |
| `cube_char_mul` | 457 | 0 | 0 | OK |
| `mu3_N_iff_locals` | 470 | 0 | 0 | OK |
| `mu3_unique_one_prime` | 491 | 0 | 0 | OK |
| `pin_cube_kernel_trivial` | 516 | 0 | 0 | OK |
| `cube_kernel_three` | 534 | 0 | 0 | OK |
| `omega_13_order_3` | 579 | 0 | 0 | OK |
| `mixed_kernel_pin_91` | 587 | 0 | 0 | OK |
| `cube_minus_one_fact` | 623 | 0 | 0 | OK |
| `mixed_mu3_gcd_xminus1` | 631 | 0 | 0 | OK |
| `mixed_mu3_gcd_phi3` | 652 | 0 | 0 | OK |
| `mixed_mu3_splits` | 687 | 0 | 0 | OK |
| `diagonal_mu3_gcd_xminus1` | 704 | 0 | 0 | OK |
| `diagonal_mu3_gcd_phi3` | 729 | 0 | 0 | OK |
| `mixed_kernel_pin_91_splits` | 752 | 0 | 0 | OK |
| `gq_kernel_pin_91_splits` | 757 | 0 | 0 | OK |
| `diagonal_pin_91_no_split` | 762 | 0 | 0 | OK |
| `phi3_small_omega_is_prime` | 767 | 0 | 0 | OK |
| `pin_mu3_gcd_is_N` | 771 | 0 | 0 | OK |

## CyclicCount.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `sum_up_ext` | 43 | 0 | 0 | OK |
| `cyclic_count_agree_below` | 55 | 0 | 0 | OK |
| `cyclic_count_top` | 70 | 0 | 0 | OK |
| `cyclic_count_sum` | 80 | 0 | 0 | OK |
| `cyclic_mismatch_11_17` | 111 | 0 | 0 | OK |
| `miller_150_of_158` | 116 | 0 | 0 | OK |
| `cyclic_mismatch_14_is_15_16` | 121 | 0 | 0 | OK |
| `cyclic_mismatch_blum_11_19` | 127 | 0 | 0 | OK |
| `blum_mismatch_is_half` | 132 | 0 | 0 | OK |
| `cyclic_mismatch_33` | 137 | 0 | 0 | OK |
| `cyclic_mismatch_33_is_21_32` | 142 | 0 | 0 | OK |

## Cyclotomic.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `cyc_p2_minus_1` | 32 | 0 | 0 | OK |
| `cyc_p3_minus_1` | 36 | 0 | 0 | OK |
| `cyc_p4_minus_1` | 40 | 0 | 0 | OK |
| `cyc_p6_minus_1` | 44 | 0 | 0 | OK |
| `cyc1_divides_p2_minus_1` | 50 | 0 | 0 | OK |
| `cyc2_divides_p2_minus_1` | 54 | 0 | 0 | OK |
| `cyc3_divides_p3_minus_1` | 58 | 0 | 0 | OK |
| `cyc1_divides_p3_minus_1` | 62 | 0 | 0 | OK |
| `cyc1_handle_is_p1` | 72 | 0 | 0 | OK |
| `cyc2_handle_is_williams` | 76 | 0 | 0 | OK |
| `cyc1_resistant_iff_p1` | 83 | 0 | 0 | OK |
| `cyc2_resistant_iff_pp1` | 87 | 0 | 0 | OK |
| `strong_prime_is_partial_cyc` | 104 | 0 | 0 | OK |
| `cyc3_pos` | 110 | 0 | 0 | OK |
| `cyc4_pos` | 114 | 0 | 0 | OK |
| `cyc6_pos_ge3` | 118 | 0 | 0 | OK |

## DamgardJurik.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `one_plus_N_pow_N3` | 19 | 0 | 0 | OK |
| `one_plus_N_pow_N3_div` | 31 | 0 | 0 | OK |
| `dj_add` | 47 | 0 | 0 | OK |

## Dark.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `poly1_factor` | 46 | 0 | 0 | OK |
| `poly2_factor` | 51 | 0 | 0 | OK |
| `dark_deg1_open` | 57 | 0 | 0 | OK |
| `dark_deg2_open` | 79 | 0 | 0 | OK |
| `dark_deg1_commit_is_powm` | 106 | 0 | 0 | OK |
| `dark_deg2_commit_is_powm` | 111 | 0 | 0 | OK |

## Derive.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `pow_pos_ge1` | 48 | 0 | 0 | OK |
| `range_lo_lt_hi` | 55 | 0 | 0 | OK |
| `in_S_b_is_ap` | 64 | 0 | 0 | OK |
| `ctor_in_S_b_iff_k` | 75 | 0 | 0 | OK |
| `div_ge_if_prod` | 91 | 0 | 0 | OK |
| `k_min_lower` | 102 | 0 | 0 | OK |
| `k_max_upper` | 121 | 0 | 0 | OK |
| `k_in_slice_of_S_b` | 137 | 0 | 0 | OK |
| `residue_in_range_is_k_zero` | 151 | 0 | 0 | OK |
| `regime_512_card_vs_M` | 164 | 0 | 0 | OK |
| `index_of_seed_in_interval` | 177 | 0 | 0 | OK |
| `index_of_seed_injective` | 183 | 0 | 0 | OK |
| `index_of_seed_surjective` | 189 | 0 | 0 | OK |
| `derive_candidate_in_S_b` | 195 | 0 | 0 | OK |
| `mod_hits_differ` | 215 | 0 | 0 | OK |
| `mod_bias_example` | 223 | 0 | 0 | OK |
| `two_hits_zero_one_hit_five` | 229 | 0 | 0 | OK |
| `force_residue_leaves_range_example` | 236 | 0 | 0 | OK |
| `slot_encode_unbounded_not_in_S_b` | 249 | 0 | 0 | OK |
| `increment_hits_first` | 276 | 0 | 0 | OK |
| `increment_from_min_skips_later` | 287 | 0 | 0 | OK |
| `resample_includes_every_slice_prime` | 298 | 0 | 0 | OK |
| `public_map_difference_divides` | 306 | 0 | 0 | OK |
| `public_two_outputs_leak_multiple` | 314 | 0 | 0 | OK |
| `gcd_of_index_diffs_divides_output_gcd` | 322 | 0 | 0 | OK |
| `no_public_hidden_class` | 334 | 0 | 0 | OK |
| `public_derive_is_roca` | 347 | 0 | 0 | OK |
| `domain_tag_separates` | 367 | 0 | 0 | OK |
| `cas28_aux_split_ready` | 375 | 0 | 0 | OK |
| `empty_slice_example` | 392 | 0 | 0 | OK |
| `reuse_gives_public_ap` | 409 | 0 | 0 | OK |
| `reuse_recovers_residue` | 420 | 0 | 0 | OK |
| `placement_implies_balanced` | 452 | 0 | 0 | OK |
| `placement_hi_enforces_far` | 466 | 0 | 0 | OK |
| `cas28_same_slot_not_placeable` | 481 | 0 | 0 | OK |
| `far_can_empty_placement` | 485 | 0 | 0 | OK |
| `derive_e_not_tiny` | 503 | 0 | 0 | OK |
| `derive_success_has_e` | 527 | 0 | 0 | OK |
| `large_d_if_not_wiener` | 533 | 0 | 0 | OK |
| `pocklington_needs_R_gt_sqrt` | 542 | 0 | 0 | OK |
| `B160_not_sqrt_of_512bit` | 549 | 0 | 0 | OK |
| `aux_at_B_not_pocklington_size` | 556 | 0 | 0 | OK |
| `rw_p_is_blum` | 573 | 0 | 0 | OK |
| `derive_e_fixed` | 585 | 0 | 0 | OK |
| `dist_public_slot_is_roca` | 593 | 0 | 0 | OK |
| `dist_reused_slot_leaks_M` | 606 | 0 | 0 | OK |
| `dist_force_residue_can_leave_range` | 621 | 0 | 0 | OK |
| `dist_seeded_slot_balanced` | 633 | 0 | 0 | OK |
| `long_seed_hits_every_index` | 649 | 0 | 0 | OK |

## DozenInroads.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `dozen_jacobi_gate_minus1` | 31 | 0 | 0 | OK |
| `dozen_jacobi_gate_forces_odd` | 35 | 0 | 0 | OK |
| `dozen_sagm_both_pin` | 41 | 0 | 0 | OK |
| `dozen_sagm_ae_eq_c_mod_lambda` | 46 | 0 | 0 | OK |
| `dozen_related_coprime_exps` | 53 | 0 | 0 | OK |
| `dozen_related_shamir_gcd` | 58 | 0 | 0 | OK |
| `dozen_fifth_divides_pminus1` | 66 | 0 | 0 | OK |
| `dozen_fifth_power_euler` | 70 | 0 | 0 | OK |
| `dozen_onesided_e11` | 76 | 0 | 0 | OK |
| `dozen_e11_residual_shaped` | 84 | 0 | 0 | OK |
| `dozen_short_e3` | 90 | 0 | 0 | OK |
| `dozen_short_e_is_residual_cube` | 94 | 0 | 0 | OK |
| `dozen_advice_bit_no_split` | 100 | 0 | 0 | OK |
| `dozen_advice_div_splits` | 104 | 0 | 0 | OK |
| `prime_23` | 113 | 0 | 0 | OK |
| `dozen_blum_shape` | 125 | 0 | 0 | OK |
| `dozen_blum_e5_names_p` | 130 | 0 | 0 | OK |
| `dozen_blum_e11_names_q` | 134 | 0 | 0 | OK |
| `dozen_phi_160` | 141 | 0 | 0 | OK |
| `dozen_every_unit_is_cube` | 145 | 0 | 0 | OK |
| `dozen_gq_extract_is_residual` | 159 | 0 | 0 | OK |
| `dozen_gq_complete_still` | 164 | 0 | 0 | OK |
| `dozen_N_cong_q` | 170 | 0 | 0 | OK |
| `dozen_gcd_Nminus1_pminus1` | 174 | 0 | 0 | OK |
| `dozen_e11_minus1_shares_lambda` | 180 | 0 | 0 | OK |

## Endo.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `rsa_inverse_is_constructible` | 36 | 0 | 0 | OK |
| `cl_inverse_is_constructible` | 43 | 0 | 0 | OK |
| `rsa_gii_search_empty` | 52 | 0 | 0 | OK |
| `power_endo_hom` | 62 | 0 | 0 | OK |
| `power_endo_on_dlog` | 77 | 0 | 0 | OK |
| `power_endo_not_product_of_dlogs` | 90 | 0 | 0 | OK |
| `power_endo_next_forces_k` | 115 | 0 | 0 | OK |

## EulerQuotient.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `powm_mod_divisor` | 24 | 0 | 0 | OK |
| `powm_mod_prime_factor` | 43 | 0 | 0 | OK |
| `powm_multiple` | 53 | 0 | 0 | OK |
| `not_coprime_prime_divides` | 69 | 0 | 0 | OK |
| `fermat_powm` | 82 | 0 | 0 | OK |
| `powm_Nplus1_mod_p` | 99 | 0 | 0 | OK |
| `powm_s_mod_p` | 116 | 0 | 0 | OK |
| `powm_Nplus1_eq_s_mod_p` | 131 | 0 | 0 | OK |
| `phi_plus_sum` | 140 | 0 | 0 | OK |
| `euler_quotient_units` | 144 | 0 | 0 | OK |
| `euler_quotient` | 162 | 0 | 0 | OK |
| `powm_reduce_to_qminus1` | 178 | 0 | 0 | OK |
| `powm_Nminus1_mod_p` | 212 | 0 | 0 | OK |
| `euler_quotient_pred` | 222 | 0 | 0 | OK |
| `prime_2` | 240 | 0 | 0 | OK |
| `odd_prime_mod2` | 247 | 0 | 0 | OK |
| `odd_primes_sum_even` | 258 | 0 | 0 | OK |
| `odd_prime_mod4` | 269 | 0 | 0 | OK |
| `sum_mod4_of_N` | 286 | 0 | 0 | OK |
| `euler_quotient_rsa` | 309 | 0 | 0 | OK |

## EvalPairing.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `eval_pair_stays_in_mu` | 44 | 0 | 0 | OK |
| `eval_pair_add` | 61 | 0 | 0 | OK |
| `eval_pair_mul_base` | 74 | 0 | 0 | OK |
| `eval_pair_reduce_mod_n` | 89 | 0 | 0 | OK |
| `eval_pair_image_divides_n` | 112 | 0 | 0 | OK |
| `eval_pair_mu2` | 122 | 0 | 0 | OK |
| `eval_pair_mu2_on_mixed` | 137 | 0 | 0 | OK |
| `omega_cube_is_one` | 152 | 0 | 0 | OK |
| `eval_pair_mu3` | 172 | 0 | 0 | OK |
| `mu2_is_mu6` | 185 | 0 | 0 | OK |
| `mu3_is_mu6` | 200 | 0 | 0 | OK |
| `eval_pair_mu6` | 215 | 0 | 0 | OK |
| `in_mu3_one` | 247 | 0 | 0 | OK |
| `in_mu3_mod` | 254 | 0 | 0 | OK |
| `pairing_one_left` | 262 | 0 | 0 | OK |
| `pairing_one_right` | 288 | 0 | 0 | OK |
| `two_omega_is_sq` | 314 | 0 | 0 | OK |
| `in_mu3_omega` | 326 | 0 | 0 | OK |
| `in_mu3_omega2` | 345 | 0 | 0 | OK |
| `pairing_omega_omega2` | 369 | 0 | 0 | OK |
| `pairing_omega2_omega` | 384 | 0 | 0 | OK |
| `pairing_omega2_omega2` | 399 | 0 | 0 | OK |
| `alternating_bilinear_mu3_trivial` | 412 | 0 | 0 | OK |
| `eval_pair_omega_13_not_alternating` | 464 | 0 | 0 | OK |
| `pin_mu3_only_one` | 468 | 0 | 0 | OK |
| `mu3_log_range` | 494 | 0 | 0 | OK |
| `mu3N_det_alternating` | 501 | 0 | 0 | OK |
| `gp_pin_91_order_3` | 515 | 0 | 0 | OK |
| `gq_pin_91_order_3` | 523 | 0 | 0 | OK |
| `mu3N_det_gp_gq` | 531 | 0 | 0 | OK |
| `mu3N_det_gq_gp` | 535 | 0 | 0 | OK |
| `mu3_pin_91_kernel_not_cyclic` | 540 | 0 | 0 | OK |
| `mu3_order_coprime` | 557 | 0 | 0 | OK |
| `mu3_order_divides_pminus1` | 577 | 0 | 0 | OK |
| `mu3_prime_ne_2` | 589 | 0 | 0 | OK |
| `mu3_pow_1_ne_2` | 600 | 0 | 0 | OK |
| `mu3_log_of_pow` | 624 | 0 | 0 | OK |
| `mu3_is_omega_power` | 660 | 0 | 0 | OK |
| `mu3_log_reconstructs` | 723 | 0 | 0 | OK |
| `mu3_log_mul` | 745 | 0 | 0 | OK |
| `zmod3_mul` | 786 | 0 | 0 | OK |
| `zmod3_mul_l` | 796 | 0 | 0 | OK |
| `det_exp_left_add` | 803 | 0 | 0 | OK |
| `det_exp_right_add` | 818 | 0 | 0 | OK |
| `mu3_log_mod_reduce` | 833 | 0 | 0 | OK |
| `mu3_log_base_mod` | 847 | 0 | 0 | OK |
| `omega_7_order_3` | 856 | 0 | 0 | OK |
| `pin_mu3_log_one` | 864 | 0 | 0 | OK |
| `mu3N_det_left_bilinear` | 867 | 0 | 0 | OK |
| `mu3N_det_right_bilinear` | 929 | 0 | 0 | OK |
| `mu3N_det_skew` | 991 | 0 | 0 | OK |

## EvalProduct.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `poly_eval_nonneg` | 39 | 0 | 0 | OK |
| `poly_eval_map_mul` | 52 | 0 | 0 | OK |
| `poly_eval_add` | 67 | 0 | 0 | OK |
| `poly_eval_shift` | 81 | 0 | 0 | OK |
| `poly_eval_conv` | 92 | 0 | 0 | OK |
| `pot_poly_is_eval` | 109 | 0 | 0 | OK |
| `pot_poly_add` | 114 | 0 | 0 | OK |
| `pot_poly_scale` | 128 | 0 | 0 | OK |
| `pot_poly_shift` | 143 | 0 | 0 | OK |
| `pot_poly_conv_raise` | 160 | 0 | 0 | OK |
| `pot_poly_conv_raise_comm` | 174 | 0 | 0 | OK |
| `pot_poly_mul_is_add` | 190 | 0 | 0 | OK |
| `nn_Xn` | 209 | 0 | 0 | OK |
| `poly_eval_Xn` | 216 | 0 | 0 | OK |
| `pot_poly_Xn` | 232 | 0 | 0 | OK |
| `monomial_eval_product` | 244 | 0 | 0 | OK |
| `monomial_conv_is_later_slot` | 258 | 0 | 0 | OK |
| `monomial_group_mul_is_sum` | 273 | 0 | 0 | OK |
| `self_bil_committed_product` | 288 | 0 | 0 | OK |
| `self_bil_monomial_product` | 310 | 0 | 0 | OK |
| `two_wire_commit` | 329 | 0 | 0 | OK |
| `two_wire_product_raise` | 347 | 0 | 0 | OK |

## ExpProof.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `wesolowski_correct_is_root` | 34 | 0 | 0 | OK |
| `wesolowski_pi_is_ell_th_root` | 56 | 0 | 0 | OK |
| `pietrzak_mid_squares_to_y` | 75 | 0 | 0 | OK |
| `pietrzak_y_is_fourth_power` | 85 | 0 | 0 | OK |
| `pietrzak_forgery_is_low_order_shape` | 95 | 0 | 0 | OK |
| `pietrzak_on_Cl_may_be_constructible` | 111 | 0 | 0 | OK |
| `pietrzak_restricted_ignores_Cl2` | 115 | 0 | 0 | OK |
| `wesolowski_verify_rsa_agrees` | 127 | 0 | 0 | OK |
| `wesolowski_correct_is_PRoot` | 138 | 0 | 0 | OK |
| `verifying_pi_is_adaptive_root` | 158 | 0 | 0 | OK |
| `pietrzak_quotient_squares_to_one_rsa` | 175 | 0 | 0 | OK |
| `pietrzak_quotient_on_Cl_may_be_ambiguous` | 196 | 0 | 0 | OK |
| `form_neg87_ord3_of_disc` | 210 | 0 | 0 | OK |
| `wesolowski_on_Cl_exp` | 216 | 0 | 0 | OK |
| `wesolowski_root_does_not_need_prime_ell` | 227 | 0 | 0 | OK |
| `wesolowski_verify_does_not_need_prime_ell` | 236 | 0 | 0 | OK |
| `powm_opp_odd` | 257 | 0 | 0 | OK |
| `wesolowski_odd_challenge_accepts_negation` | 273 | 0 | 0 | OK |
| `wesolowski_soundness_fails_on_units_odd_challenge` | 303 | 0 | 0 | OK |

## ExtraRelations.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `one_more_pin` | 30 | 0 | 0 | OK |
| `one_more_queried_is_not_extra` | 41 | 0 | 0 | OK |
| `prime_3` | 53 | 0 | 0 | OK |
| `ghr_pin` | 61 | 0 | 0 | OK |
| `ghr_is_rsa` | 68 | 0 | 0 | OK |
| `ghr_prime_e_shamir_gcd` | 72 | 0 | 0 | OK |
| `ghr_shamir_gcd_pin` | 83 | 0 | 0 | OK |
| `phi_hiding_lambda_80` | 92 | 0 | 0 | OK |
| `phi_hiding_pin_e5` | 96 | 0 | 0 | OK |
| `phi_hiding_public_e3_misses` | 103 | 0 | 0 | OK |

## FactorEnum.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `enum_recovers_when_phi` | 32 | 0 | 0 | OK |
| `enum_k_from_phi_multiple` | 47 | 0 | 0 | OK |
| `phi_divides_ed_minus_1_if_d_inv_mod_phi` | 65 | 0 | 0 | OK |
| `rsa_test_enum_from_phi` | 88 | 0 | 0 | OK |
| `rsa_test_ed_minus_1_is_lambda` | 96 | 0 | 0 | OK |

## FermatFactor.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `odd_prime_ge_3` | 21 | 0 | 0 | OK |
| `odd_add_even` | 26 | 0 | 0 | OK |
| `odd_sub_even` | 35 | 0 | 0 | OK |
| `prime_odd_if_ne_2` | 44 | 0 | 0 | OK |
| `fermat_identity` | 57 | 0 | 0 | OK |
| `fermat_square_gap` | 76 | 0 | 0 | OK |
| `ceil_sqrt_ge` | 92 | 0 | 0 | OK |
| `ceil_sqrt_le_of_square` | 102 | 0 | 0 | OK |
| `fermat_sum_ge_ceil_sqrt` | 116 | 0 | 0 | OK |
| `fermat_recovers` | 144 | 0 | 0 | OK |
| `fermat_diff_abs` | 171 | 0 | 0 | OK |
| `far_apart_large_diff` | 184 | 0 | 0 | OK |
| `fermat_square_gap_from_diff` | 195 | 0 | 0 | OK |

## FiatShamir.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `fs_step_nonneg` | 43 | 0 | 0 | OK |
| `fs_fold_nonneg` | 52 | 0 | 0 | OK |
| `fs_challenge_nonneg` | 65 | 0 | 0 | OK |
| `fs_eqdl_challenge_nonneg` | 79 | 0 | 0 | OK |
| `eqdl_verifyb_iff` | 114 | 0 | 0 | OK |
| `fs_eqdl_verifyb_iff` | 124 | 0 | 0 | OK |
| `fs_eqdl_complete` | 133 | 0 | 0 | OK |
| `fs_eqdl_complete_b` | 148 | 0 | 0 | OK |
| `fs_slot_complete` | 163 | 0 | 0 | OK |
| `fs_wire_complete` | 180 | 0 | 0 | OK |
| `fs_pin_accepts` | 209 | 0 | 0 | OK |
| `fs_pin_rejects_wrong_challenge` | 213 | 0 | 0 | OK |
| `fs_pin_challenge_depends_on_commit` | 222 | 0 | 0 | OK |
| `fs_pin_second_accepts` | 229 | 0 | 0 | OK |
| `fs_pin_commits_distinct` | 233 | 0 | 0 | OK |

## FilterShape.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `filter_onesided_local_mod_p` | 25 | 0 | 0 | OK |
| `filter_onesided_not_global` | 29 | 0 | 0 | OK |
| `filter_onesided_integer_splits` | 33 | 0 | 0 | OK |
| `filter_neg_y_not_cube_root` | 43 | 0 | 0 | OK |
| `filter_y_square_not_minus1` | 47 | 0 | 0 | OK |
| `filter_euclid_y_minus_1` | 53 | 0 | 0 | OK |
| `filter_euclid_y_plus_1` | 57 | 0 | 0 | OK |
| `filter_fifth_shares_lambda` | 63 | 0 | 0 | OK |
| `filter_fifth_root_of_1_splits` | 68 | 0 | 0 | OK |
| `filter_Nplus1_does_not_annihilate` | 78 | 0 | 0 | OK |
| `filter_phi_gives_sum` | 87 | 0 | 0 | OK |
| `filter_phi_enum_factors` | 92 | 0 | 0 | OK |
| `filter_phi_is_factor` | 97 | 0 | 0 | OK |
| `filter_val2_36` | 103 | 0 | 0 | OK |
| `filter_val2_not_div_by_3` | 107 | 0 | 0 | OK |
| `filter_locally_constant_clash` | 113 | 0 | 0 | OK |
| `filter_jacobi_branch_lambda_type` | 121 | 0 | 0 | OK |
| `filter_jacobi_branch_not_residual` | 125 | 0 | 0 | OK |
| `filter_cube_fails_public_e` | 133 | 0 | 0 | OK |
| `filter_e11_passes_public_e` | 137 | 0 | 0 | OK |
| `filter_public_e11_miller_splits` | 141 | 0 | 0 | OK |
| `filter_lowbit_e9` | 153 | 0 | 0 | OK |
| `filter_lowbit_e9_residual` | 157 | 0 | 0 | OK |
| `filter_lowbit_root_is_70` | 161 | 0 | 0 | OK |
| `filter_trace_not_root` | 167 | 0 | 0 | OK |
| `filter_torus_order_not_Nplus1` | 171 | 0 | 0 | OK |
| `filter_residual_tests_on_cube` | 182 | 0 | 0 | OK |
| `filter_e5_shares_lambda` | 192 | 0 | 0 | OK |
| `filter_e15_odd_shares_lambda` | 197 | 0 | 0 | OK |
| `filter_e7_residual_shaped` | 202 | 0 | 0 | OK |
| `filter_e5_passes_public_e` | 212 | 0 | 0 | OK |
| `filter_e7_passes_public_e` | 216 | 0 | 0 | OK |
| `filter_e_coprime_N_cube_passes` | 220 | 0 | 0 | OK |
| `filter_e_coprime_N_accepts_nonresidual` | 224 | 0 | 0 | OK |
| `filter_e_coprime_N_does_not_certify` | 229 | 0 | 0 | OK |
| `filter_phi_y_of_36` | 234 | 0 | 0 | OK |
| `filter_e_coprime_phi_y_rejects_cube` | 242 | 0 | 0 | OK |
| `filter_jacobi_x_plus` | 254 | 0 | 0 | OK |
| `filter_jacobi_10_plus_not_leftover` | 259 | 0 | 0 | OK |
| `filter_jacobi_2_minus` | 266 | 0 | 0 | OK |
| `filter_x_cube_check_is_rsa_e3` | 271 | 0 | 0 | OK |

## Fp2.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `fp2_eq_refl` | 48 | 0 | 0 | OK |
| `fp2_mul_embed_l` | 51 | 0 | 0 | OK |
| `fp2_add_conj` | 57 | 0 | 0 | OK |
| `fp2_mul_conj` | 61 | 0 | 0 | OK |
| `inv2_exists` | 66 | 0 | 0 | OK |
| `alpha_plus_beta` | 92 | 0 | 0 | OK |
| `alpha_mul_beta` | 97 | 0 | 0 | OK |
| `alpha_beta_is_one` | 104 | 0 | 0 | OK |
| `alpha_plus_beta_is_P` | 124 | 0 | 0 | OK |
| `fp2_pow_0` | 144 | 0 | 0 | OK |
| `fp2_pow_1` | 147 | 0 | 0 | OK |
| `fp2_mul_one_r` | 150 | 0 | 0 | OK |
| `fp2_mul_comm` | 154 | 0 | 0 | OK |
| `fp2_eq_trans` | 158 | 0 | 0 | OK |
| `fp2_eq_sym` | 163 | 0 | 0 | OK |
| `opp_mod_compat` | 167 | 0 | 0 | OK |
| `fp2_eq_opp` | 178 | 0 | 0 | OK |
| `fp2_pow_succ` | 192 | 0 | 0 | OK |
| `fp2_eq_mul` | 196 | 0 | 0 | OK |
| `fp2_eq_opp_mul` | 226 | 0 | 0 | OK |
| `fp2_eq_add` | 236 | 0 | 0 | OK |
| `fp2_mul_assoc` | 250 | 0 | 0 | OK |
| `fp2_mul_add_r` | 258 | 0 | 0 | OK |
| `fp2_mul_add_l` | 266 | 0 | 0 | OK |
| `fp2_pow_add_r` | 274 | 0 | 0 | OK |
| `fp2_pow_SS` | 283 | 0 | 0 | OK |
| `alpha_beta_rec` | 288 | 0 | 0 | OK |
| `lucasV_as_fp2` | 312 | 0 | 0 | OK |
| `binom_n_0` | 368 | 0 | 0 | OK |
| `binom_0_S` | 371 | 0 | 0 | OK |
| `binom_gt` | 374 | 0 | 0 | OK |
| `binom_n_n` | 382 | 0 | 0 | OK |
| `binom_n_1` | 388 | 0 | 0 | OK |
| `binom_S_S_expand` | 394 | 0 | 0 | OK |
| `binom_mul_row` | 398 | 0 | 0 | OK |
| `prime_divides_binom` | 418 | 0 | 0 | OK |
| `fp2_scale_as_mul` | 444 | 0 | 0 | OK |
| `fp2_scale_add` | 451 | 0 | 0 | OK |
| `fp2_eq_scale` | 459 | 0 | 0 | OK |
| `fp2_eq_scale_mod` | 469 | 0 | 0 | OK |
| `fp2_scale_p_zero` | 483 | 0 | 0 | OK |
| `fp2_scale_mul_div` | 493 | 0 | 0 | OK |
| `fp2_eq_sum` | 512 | 0 | 0 | OK |
| `fp2_sum_zero` | 524 | 0 | 0 | OK |
| `fermat_pow_id` | 541 | 0 | 0 | OK |
| `fp2_pow_sqrt_even` | 568 | 0 | 0 | OK |
| `fp2_pow_sqrt_odd` | 583 | 0 | 0 | OK |
| `nat_odd_prime` | 596 | 0 | 0 | OK |
| `fp2_pow_sqrt_p` | 613 | 0 | 0 | OK |
| `fp2_mul_embed_embed` | 630 | 0 | 0 | OK |
| `fp2_mul_embed_comm` | 637 | 0 | 0 | OK |
| `fp2_embed_pow` | 642 | 0 | 0 | OK |
| `fp2_scale_pow` | 654 | 0 | 0 | OK |
| `zsum_ext` | 677 | 0 | 0 | OK |
| `zsum_mod` | 688 | 0 | 0 | OK |
| `zsum_zero_mod` | 700 | 0 | 0 | OK |
| `gamma_split` | 719 | 0 | 0 | OK |
| `alpha_as_scale` | 723 | 0 | 0 | OK |
| `beta_as_scale` | 730 | 0 | 0 | OK |
| `zsum_uncons` | 737 | 0 | 0 | OK |
| `zsum_mul_l` | 746 | 0 | 0 | OK |
| `zsum_add` | 754 | 0 | 0 | OK |
| `zsum_shift` | 762 | 0 | 0 | OK |
| `zsum_pad` | 771 | 0 | 0 | OK |
| `z_binom` | 777 | 0 | 0 | OK |
| `z_freshman` | 807 | 0 | 0 | OK |
| `fp2_sum_uncons` | 854 | 0 | 0 | OK |
| `fp2_sum_shift` | 867 | 0 | 0 | OK |
| `fp2_sum_pad` | 876 | 0 | 0 | OK |
| `fp2_sum_add` | 883 | 0 | 0 | OK |
| `fp2_mul_scale` | 895 | 0 | 0 | OK |
| `fp2_scale_zero` | 903 | 0 | 0 | OK |
| `fp2_sum_ext_eq` | 910 | 0 | 0 | OK |
| `fp2_sum_scale_mul` | 921 | 0 | 0 | OK |
| `fp2_binterm_gt` | 930 | 0 | 0 | OK |
| `fp2_binom` | 939 | 0 | 0 | OK |
| `fp2_scale_one` | 989 | 0 | 0 | OK |
| `fp2_freshman` | 993 | 0 | 0 | OK |
| `fp2_eq_embed` | 1043 | 0 | 0 | OK |
| `fp2_pow_S_to_nat` | 1050 | 0 | 0 | OK |
| `euler_pow_half` | 1061 | 0 | 0 | OK |
| `fp2_conj_mul_ok` | 1068 | 0 | 0 | OK |
| `fp2_pow_conj` | 1075 | 0 | 0 | OK |
| `gamma_pow_p` | 1084 | 0 | 0 | OK |
| `alpha_pow_p_is_beta` | 1116 | 0 | 0 | OK |
| `beta_is_conj_alpha` | 1145 | 0 | 0 | OK |
| `fp2_conj_one` | 1149 | 0 | 0 | OK |
| `fp2_eq_conj` | 1153 | 0 | 0 | OK |
| `williams_eval_of_qnr` | 1165 | 0 | 0 | OK |

## GQ.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `gq_complete` | 31 | 0 | 0 | OK |
| `gq_ratio_is_delta_power` | 51 | 0 | 0 | OK |
| `gq_extract` | 91 | 0 | 0 | OK |
| `publishing_mixed_sqrt1_factors` | 123 | 0 | 0 | OK |
| `gq_on_one_with_mixed_sqrt_is_factorization` | 141 | 0 | 0 | OK |
| `gq_e2_complete` | 161 | 0 | 0 | OK |
| `gq_e2_odd_delta_extracts_sqrt` | 173 | 0 | 0 | OK |

## GenericGroup.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `ggm_add_uninhabited` | 48 | 0 | 0 | OK |
| `ggm_step_is_mul_inv_or_eq` | 52 | 0 | 0 | OK |
| `ggm_init_is_one_and_y` | 72 | 0 | 0 | OK |
| `ggm_pow10_handle` | 76 | 0 | 0 | OK |
| `ggm_eq_leak_from_tape` | 80 | 0 | 0 | OK |
| `ggm_eq_leak_factors` | 84 | 0 | 0 | OK |
| `ggm_yyy_pin` | 93 | 0 | 0 | OK |

## GenericRing.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `gra_eq_tape_88` | 115 | 0 | 0 | OK |
| `gra_eq_tape_zero` | 119 | 0 | 0 | OK |
| `gra_eq_leak_pin` | 123 | 0 | 0 | OK |
| `gra_eq_leak_factors` | 127 | 0 | 0 | OK |
| `gra_eq_leak_onesided` | 135 | 0 | 0 | OK |
| `gra_eq_N_is_not_a_split` | 139 | 0 | 0 | OK |
| `gra_mul_y_pin` | 143 | 0 | 0 | OK |
| `gra_const42` | 147 | 0 | 0 | OK |
| `slp_init_eval` | 172 | 0 | 0 | OK |
| `slp_to_poly_mul_pin` | 183 | 0 | 0 | OK |
| `nth_app_last` | 201 | 0 | 0 | OK |
| `nth_app_lt` | 208 | 0 | 0 | OK |
| `step_length` | 216 | 0 | 0 | OK |
| `step_poly_length` | 220 | 0 | 0 | OK |
| `step_nodiv_prefix` | 224 | 0 | 0 | OK |
| `step_nodiv_new` | 238 | 0 | 0 | OK |
| `step_nodiv_overflow` | 258 | 0 | 0 | OK |
| `step_nodiv_agree` | 271 | 0 | 0 | OK |
| `gra_run_nodiv_agree` | 291 | 0 | 0 | OK |
| `slp_init_length` | 308 | 0 | 0 | OK |
| `gra_init_length` | 311 | 0 | 0 | OK |
| `gra_init_agrees` | 314 | 0 | 0 | OK |
| `gra_nodiv_denotes` | 327 | 0 | 0 | OK |
| `slp_init_deg_le` | 366 | 0 | 0 | OK |
| `step_deg_bound_length` | 378 | 0 | 0 | OK |
| `step_nodiv_degree_le` | 382 | 0 | 0 | OK |
| `gra_run_poly_length` | 413 | 0 | 0 | OK |
| `gra_nodiv_degree_le` | 421 | 0 | 0 | OK |
| `gra_deg_bound_identity` | 446 | 0 | 0 | OK |
| `gra_deg_bound_square` | 450 | 0 | 0 | OK |
| `gra_deg_bound_x3` | 454 | 0 | 0 | OK |
| `gra_deg_bound_x4` | 458 | 0 | 0 | OK |
| `gra_nodiv_mul_is_nodiv` | 462 | 0 | 0 | OK |
| `gra_nodiv_mul_denotes_square` | 466 | 0 | 0 | OK |
| `gra_nodiv_integer_eth_root_forbidden` | 473 | 0 | 0 | OK |
| `gra_nodiv_const42_inverts_36` | 491 | 0 | 0 | OK |
| `gra_nodiv_const42_fails_on_8` | 495 | 0 | 0 | OK |
| `gra_identity_not_cube_root_at_2` | 499 | 0 | 0 | OK |
| `gra_identity_at_one` | 503 | 0 | 0 | OK |
| `gra_identity_gcd_at_2` | 507 | 0 | 0 | OK |
| `gra_nodiv_identical_X3_linear` | 511 | 0 | 0 | OK |
| `gra_nodiv_N_does_not_divide_minus1` | 515 | 0 | 0 | OK |
| `gra_nodiv_identical_root_impossible_X3` | 519 | 0 | 0 | OK |
| `Pe_minus_X_eval2_is_six_on_X` | 527 | 0 | 0 | OK |
| `gra_inv_nonunit_pin` | 540 | 0 | 0 | OK |
| `gra_inv_nonunit_factors` | 544 | 0 | 0 | OK |
| `gra_inv_22_from_tape` | 551 | 0 | 0 | OK |
| `gra_inv_unit_gcd` | 555 | 0 | 0 | OK |
| `gra_inv_unit_from_tape` | 559 | 0 | 0 | OK |
| `gra_fixed_e_leading_const` | 563 | 0 | 0 | OK |
| `gra_fixed_e_leading` | 567 | 0 | 0 | OK |
| `rsa_inverter_is_not_a_GRA_comment` | 573 | 0 | 0 | OK |
| `powm_d_inverts_cube_pin` | 579 | 0 | 0 | OK |
| `gra_const_81` | 585 | 0 | 0 | OK |
| `gra_const_lambda_plus_one_solves_sRSA_without_factoring` | 590 | 0 | 0 | OK |
| `gra_const_81_does_not_factor` | 600 | 0 | 0 | OK |
| `lambda_plus_one_is_81` | 604 | 0 | 0 | OK |
| `gra_add_mul_of_36_is_not_81` | 608 | 0 | 0 | OK |
| `am09_fixed_e_is_a_parameter` | 614 | 0 | 0 | OK |
| `gadd_is_not_a_ggm_op` | 630 | 0 | 0 | OK |
| `gsub_is_not_a_ggm_op` | 634 | 0 | 0 | OK |
| `gconst_is_not_a_ggm_op` | 638 | 0 | 0 | OK |
| `gra_poly_construction_needs_add` | 642 | 0 | 0 | OK |
| `generic_group_does_not_separate_rsa_from_srsa` | 646 | 0 | 0 | OK |
| `ggm_mul_pin` | 653 | 0 | 0 | OK |

## Hardness.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `rsa_units_are_eth_powers` | 39 | 0 | 0 | OK |
| `trapdoor_inverts_RSA` | 50 | 0 | 0 | OK |
| `rsa_solution_is_strong_RSA` | 83 | 0 | 0 | OK |
| `lambda_solves_strong_RSA` | 97 | 0 | 0 | OK |
| `strong_RSA_trivial_at_one` | 121 | 0 | 0 | OK |
| `rsa_trivial_at_one` | 129 | 0 | 0 | OK |
| `order_divides_annihilator` | 138 | 0 | 0 | OK |
| `order_divides_lambda` | 167 | 0 | 0 | OK |
| `one_sided_low_order_factors` | 195 | 0 | 0 | OK |
| `one_sided_low_order_is_factor` | 227 | 0 | 0 | OK |
| `adaptive_root_is_strong_RSA` | 240 | 0 | 0 | OK |
| `order_is_annihilator` | 251 | 0 | 0 | OK |
| `low_order_is_annihilator` | 260 | 0 | 0 | OK |
| `lambda_is_annihilator_on_units` | 269 | 0 | 0 | OK |
| `annihilator_plus_one_is_strong_RSA` | 282 | 0 | 0 | OK |
| `rsa_is_fractional_root` | 299 | 0 | 0 | OK |
| `strong_RSA_is_fractional_root` | 315 | 0 | 0 | OK |
| `annihilator_is_fractional_root_of_one` | 330 | 0 | 0 | OK |
| `ar_C_implies_strong_RSA` | 359 | 0 | 0 | OK |
| `ar_C_requires_C` | 368 | 0 | 0 | OK |
| `strong_RSA_is_ar_C_iff` | 373 | 0 | 0 | OK |
| `lambda_plus_one_11_17` | 384 | 0 | 0 | OK |
| `lambda_plus_one_11_17_not_prime` | 388 | 0 | 0 | OK |
| `lambda_solves_search_11_17` | 397 | 0 | 0 | OK |
| `search_lambda_plus_one_misses_prime_AR` | 408 | 0 | 0 | OK |
| `adaptive_root_known_product_breaks` | 426 | 0 | 0 | OK |
| `adaptive_root_smooth_power_breaks` | 442 | 0 | 0 | OK |
| `order_inverts_in_cyclic` | 465 | 0 | 0 | OK |
| `order_yields_strong_RSA` | 490 | 0 | 0 | OK |
| `gcd_powm_minus_1` | 513 | 0 | 0 | OK |
| `leftover_mismatch_factors` | 526 | 0 | 0 | OK |

## HashSlot.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `slot_encode_in_image` | 34 | 0 | 0 | OK |
| `slot_encode_rulers` | 39 | 0 | 0 | OK |
| `slot_accept_implies_rulers` | 55 | 0 | 0 | OK |
| `slot_reject_is_composite` | 69 | 0 | 0 | OK |
| `slot_encode_public_ap` | 82 | 0 | 0 | OK |
| `public_slot_encode_is_roca` | 91 | 0 | 0 | OK |
| `public_encode_admits_ap_test` | 103 | 0 | 0 | OK |
| `public_slot_encode_ap_budget` | 108 | 0 | 0 | OK |
| `cas28_seeds_not_balanced` | 125 | 0 | 0 | OK |
| `slot_encode_does_not_place` | 129 | 0 | 0 | OK |
| `pair_encode_does_not_force_balance` | 144 | 0 | 0 | OK |
| `slot_try_sound` | 163 | 0 | 0 | OK |
| `slot_try_complete` | 183 | 0 | 0 | OK |

## Inner2.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `inner2_sat` | 24 | 0 | 0 | OK |
| `inner2_complete` | 46 | 0 | 0 | OK |
| `inner2_public_sum` | 67 | 0 | 0 | OK |

## JagerSchwenk.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `jacobi_one_pin` | 27 | 0 | 0 | OK |
| `jacobi_two_pin` | 31 | 0 | 0 | OK |
| `jacobi_two_values` | 35 | 0 | 0 | OK |
| `jacobi_is_standard_easy` | 39 | 0 | 0 | OK |
| `jacobi_is_not_a_constant_polynomial` | 43 | 0 | 0 | OK |
| `jacobi_is_not_a_ring_polynomial` | 51 | 0 | 0 | OK |
| `jacobi_three_pin` | 56 | 0 | 0 | OK |
| `jacobi_five_pin` | 60 | 0 | 0 | OK |
| `lagrange_125_at_1` | 73 | 0 | 0 | OK |
| `lagrange_125_at_2` | 76 | 0 | 0 | OK |
| `lagrange_125_at_5` | 79 | 0 | 0 | OK |
| `lagrange_125_at_3` | 82 | 0 | 0 | OK |
| `gra_jacobi_not_deg2_fit` | 85 | 0 | 0 | OK |

## JouxNaccacheThome.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `jnt_roots_affine` | 19 | 0 | 0 | OK |
| `jnt_affine_is_plain_cube` | 23 | 0 | 0 | OK |
| `jnt_not_a_general_root` | 27 | 0 | 0 | OK |
| `jnt_general_roots_plain_cubes` | 31 | 0 | 0 | OK |
| `jnt_c0_is_general` | 35 | 0 | 0 | OK |

## KeyGen.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `balanced_sum_bound` | 69 | 0 | 0 | OK |
| `balanced_q_le_sqrt` | 77 | 0 | 0 | OK |
| `balanced_sum_vs_sqrt` | 91 | 0 | 0 | OK |
| `balanced_implies_odd_candidates` | 102 | 0 | 0 | OK |
| `keygen_refuses_wiener` | 113 | 0 | 0 | OK |
| `keygen_refuses_smooth_p` | 121 | 0 | 0 | OK |
| `keygen_refuses_smooth_q` | 131 | 0 | 0 | OK |
| `p1_resistant_not_smooth` | 141 | 0 | 0 | OK |
| `keygen_p1_not_smooth` | 151 | 0 | 0 | OK |
| `keygen_far_large_fermat_diff` | 164 | 0 | 0 | OK |
| `small_prime_le_sqrt` | 185 | 0 | 0 | OK |
| `tiny_e_is_degree` | 199 | 0 | 0 | OK |
| `balanced_wiener_sufficient` | 206 | 0 | 0 | OK |

## KeyGenCtor.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `sa_prime_ge_2` | 61 | 0 | 0 | OK |
| `sa_mod_pos` | 64 | 0 | 0 | OK |
| `sa_r_divides_mod` | 74 | 0 | 0 | OK |
| `sa_s_divides_mod` | 77 | 0 | 0 | OK |
| `sa_u_divides_mod` | 80 | 0 | 0 | OK |
| `sa_v_divides_mod` | 83 | 0 | 0 | OK |
| `sa_w_divides_mod` | 86 | 0 | 0 | OK |
| `four_divides_mod` | 89 | 0 | 0 | OK |
| `ctor_plus_mod` | 107 | 0 | 0 | OK |
| `ctor_prime_mod_r` | 118 | 0 | 0 | OK |
| `ctor_prime_mod_s` | 129 | 0 | 0 | OK |
| `ctor_prime_mod_4` | 141 | 0 | 0 | OK |
| `ctor_r_divides_pminus1` | 151 | 0 | 0 | OK |
| `ctor_s_divides_pplus1` | 164 | 0 | 0 | OK |
| `ctor_is_blum_mod4` | 177 | 0 | 0 | OK |
| `cyc3_of_ctor` | 181 | 0 | 0 | OK |
| `cyc4_of_ctor` | 189 | 0 | 0 | OK |
| `cyc6_of_ctor` | 196 | 0 | 0 | OK |
| `ctor_u_divides_phi3` | 203 | 0 | 0 | OK |
| `ctor_v_divides_phi4` | 215 | 0 | 0 | OK |
| `ctor_w_divides_phi6` | 227 | 0 | 0 | OK |
| `ctor_p1_resistant` | 239 | 0 | 0 | OK |
| `ctor_pp1_resistant` | 251 | 0 | 0 | OK |
| `ctor_p3_resistant` | 263 | 0 | 0 | OK |
| `ctor_p4_resistant` | 276 | 0 | 0 | OK |
| `ctor_p6_resistant` | 289 | 0 | 0 | OK |
| `ctor_cyc_strong` | 302 | 0 | 0 | OK |
| `ctor_strong` | 318 | 0 | 0 | OK |
| `placed_p1_strong` | 364 | 0 | 0 | OK |
| `placed_pp1_strong` | 374 | 0 | 0 | OK |
| `placed_cyc_strong` | 384 | 0 | 0 | OK |
| `ctor_rsa_p` | 432 | 0 | 0 | OK |
| `ctor_key_satisfies` | 443 | 0 | 0 | OK |
| `ctor_key_satisfies_filter` | 475 | 0 | 0 | OK |
| `in_slot_image_on_ap` | 487 | 0 | 0 | OK |
| `slot_image_is_public_ap` | 506 | 0 | 0 | OK |
| `slot_image_has_secret_aux` | 529 | 0 | 0 | OK |
| `ap_candidates_bound` | 547 | 0 | 0 | OK |
| `public_ap_div_le_shift` | 560 | 0 | 0 | OK |
| `public_ap_search_bits` | 576 | 0 | 0 | OK |
| `regime_1024_ap_budget` | 599 | 0 | 0 | OK |

## KeyGenGeom.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `shared_high_bits_bound` | 30 | 0 | 0 | OK |
| `shared_high_bits_fails_far` | 45 | 0 | 0 | OK |
| `increment_window_bound` | 62 | 0 | 0 | OK |
| `increment_window_fails_far` | 70 | 0 | 0 | OK |
| `adjacent_fermat_diff` | 86 | 0 | 0 | OK |
| `adjacent_fails_far_ge2` | 98 | 0 | 0 | OK |

## KeyGenSampler.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `dist_close_pair_fails_far` | 31 | 0 | 0 | OK |
| `dist_twin_odd_fails_far` | 45 | 0 | 0 | OK |
| `dist_shared_prefix_fails_far` | 58 | 0 | 0 | OK |
| `dist_increment_fails_far` | 73 | 0 | 0 | OK |
| `dist_safe_p_resists_p1` | 89 | 0 | 0 | OK |
| `dist_shared_pool_gcd` | 104 | 0 | 0 | OK |
| `dist_smooth_has_public_annihilator` | 118 | 0 | 0 | OK |
| `dist_cyc3_leak_not_p3_resistant` | 136 | 0 | 0 | OK |
| `dist_small_d_fails_large_d` | 149 | 0 | 0 | OK |
| `dist_independent_passes_geom` | 163 | 0 | 0 | OK |

## Lattice.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `lattice_phi_factors` | 28 | 0 | 0 | OK |
| `lattice_sum_factors` | 39 | 0 | 0 | OK |
| `phi_from_k_correct` | 54 | 0 | 0 | OK |

## Lucas.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `lucasV_0` | 32 | 0 | 0 | OK |
| `lucasV_1` | 35 | 0 | 0 | OK |
| `lucasV_rec` | 38 | 0 | 0 | OK |
| `lucasV_2` | 43 | 0 | 0 | OK |
| `lucasV_succ` | 47 | 0 | 0 | OK |
| `lucasV_add` | 59 | 0 | 0 | OK |
| `lucasV_double` | 106 | 0 | 0 | OK |
| `lucasV_double_Q1` | 116 | 0 | 0 | OK |
| `lucasV_double_Q1_table` | 125 | 0 | 0 | OK |
| `williams_handle_is_cyc2` | 139 | 0 | 0 | OK |
| `safe_prime_refuses_pminus1_only` | 143 | 0 | 0 | OK |
| `lucas_period_is_cyc2` | 155 | 0 | 0 | OK |
| `lucasV_add_Q1` | 167 | 0 | 0 | OK |
| `williams_eval_k_times` | 177 | 0 | 0 | OK |
| `williams_eval_on_multiples` | 202 | 0 | 0 | OK |
| `pp1_resistant_is_torus_period` | 219 | 0 | 0 | OK |
| `typeB_n2_is_williams_period` | 223 | 0 | 0 | OK |

## Miller.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `miller_M_pos` | 26 | 0 | 0 | OK |
| `miller_M_split` | 29 | 0 | 0 | OK |
| `miller_t_nonneg` | 36 | 0 | 0 | OK |
| `miller_M_annihilates` | 42 | 0 | 0 | OK |
| `miller_witness_factors` | 73 | 0 | 0 | OK |
| `rsa_test_miller_split` | 104 | 0 | 0 | OK |
| `rsa_test_miller_t` | 107 | 0 | 0 | OK |
| `rsa_test_miller_s` | 110 | 0 | 0 | OK |
| `rsa_test_base2_splits` | 114 | 0 | 0 | OK |

## MillerHeight.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `miller_t_pos` | 24 | 0 | 0 | OK |
| `miller_t_odd` | 30 | 0 | 0 | OK |
| `miller_t_multiple_of_lambda_odd` | 36 | 0 | 0 | OK |
| `powm_one_mod_factor` | 54 | 0 | 0 | OK |
| `miller_height_exists` | 67 | 0 | 0 | OK |
| `miller_from_d` | 104 | 0 | 0 | OK |
| `miller_from_d_q` | 125 | 0 | 0 | OK |
| `rsa_test_base2_heights` | 148 | 0 | 0 | OK |
| `rsa_test_miller_from_d` | 168 | 0 | 0 | OK |
| `miller_multiple_annihilates` | 200 | 0 | 0 | OK |
| `miller_height_exists_multiple` | 218 | 0 | 0 | OK |
| `miller_from_multiple` | 256 | 0 | 0 | OK |
| `miller_from_multiple_q` | 279 | 0 | 0 | OK |
| `trapdoor_exponent_divides_lambda` | 302 | 0 | 0 | OK |
| `miller_from_trapdoor_exponent` | 313 | 0 | 0 | OK |
| `miller_from_trapdoor_exponent_q` | 330 | 0 | 0 | OK |

## MillerRabin.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `mr_split` | 28 | 0 | 0 | OK |
| `miller_mr_same_engine` | 48 | 0 | 0 | OK |
| `mr_nontrivial_sqrt_factors` | 63 | 0 | 0 | OK |
| `mr_fermat_on_prime` | 84 | 0 | 0 | OK |

## MulGate.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `mul_Aw` | 39 | 0 | 0 | OK |
| `mul_Bw` | 47 | 0 | 0 | OK |
| `mul_Cw` | 55 | 0 | 0 | OK |
| `mul_eval_Aw` | 63 | 0 | 0 | OK |
| `mul_eval_Bw` | 68 | 0 | 0 | OK |
| `mul_eval_Cw` | 73 | 0 | 0 | OK |
| `mul_gate_sat` | 78 | 0 | 0 | OK |
| `mul_gate_complete` | 92 | 0 | 0 | OK |
| `mul_wires_nn` | 115 | 0 | 0 | OK |
| `bit_sat` | 141 | 0 | 0 | OK |
| `bit_complete` | 154 | 0 | 0 | OK |

## MultiPrime.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `two_prime_sqrt1_is_pm1_each` | 25 | 0 | 0 | OK |
| `three_prime_sqrt1_is_pm1_each` | 33 | 0 | 0 | OK |
| `eight_pats_length` | 77 | 0 | 0 | OK |
| `two_prime_arity_is_four` | 80 | 0 | 0 | OK |
| `two_sylow_is_two_prime` | 88 | 0 | 0 | OK |
| `prime_gcd_1` | 95 | 0 | 0 | OK |
| `crt_coprime_exists` | 104 | 0 | 0 | OK |
| `crt2_exists` | 129 | 0 | 0 | OK |
| `mod_mod_product` | 143 | 0 | 0 | OK |
| `three_prime_pq_coprime_r` | 157 | 0 | 0 | OK |
| `crt3_exists` | 166 | 0 | 0 | OK |
| `mixed_triple_splits` | 198 | 0 | 0 | OK |
| `crt3_mod` | 257 | 0 | 0 | OK |
| `sign_residue_pm1` | 290 | 0 | 0 | OK |
| `square_mod_one_of_pm1` | 294 | 0 | 0 | OK |
| `eight_sqrt1_mod` | 310 | 0 | 0 | OK |
| `eight_sqrt1_squares` | 323 | 0 | 0 | OK |
| `mixed_pqr_splits` | 364 | 0 | 0 | OK |
| `lambda_threeprime_divides_pminus1` | 393 | 0 | 0 | OK |
| `lambda_threeprime_divides_qminus1` | 402 | 0 | 0 | OK |
| `lambda_threeprime_divides_rminus1` | 411 | 0 | 0 | OK |
| `lambda_threeprime_pos` | 415 | 0 | 0 | OK |
| `crt_one_three` | 430 | 0 | 0 | OK |
| `carmichael_threeprime` | 458 | 0 | 0 | OK |
| `onesided_period_splits_triple` | 500 | 0 | 0 | OK |

## Mux.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `mux_on_zero` | 25 | 0 | 0 | OK |
| `mux_on_one` | 29 | 0 | 0 | OK |
| `mux_select` | 33 | 0 | 0 | OK |
| `mux_nonneg` | 44 | 0 | 0 | OK |
| `mux_gates` | 55 | 0 | 0 | OK |
| `mux_complete` | 77 | 0 | 0 | OK |

## OkamotoUchiyama.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `one_plus_p_pow` | 22 | 0 | 0 | OK |
| `ou_L_of_plain` | 33 | 0 | 0 | OK |
| `ou_L_of_scaled` | 48 | 0 | 0 | OK |
| `ou_L_of_base` | 69 | 0 | 0 | OK |
| `ou_rand_vanishes` | 81 | 0 | 0 | OK |

## Order.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `is_order_unique` | 36 | 0 | 0 | OK |
| `no_smaller_order_sound` | 55 | 0 | 0 | OK |
| `is_order_by_vm` | 78 | 0 | 0 | OK |
| `powm_one_of_divide` | 90 | 0 | 0 | OK |
| `order_iff_divides` | 106 | 0 | 0 | OK |
| `order_exists_from_annihilator` | 128 | 0 | 0 | OK |
| `order_exists_prime` | 178 | 0 | 0 | OK |
| `order_exists_semiprime` | 192 | 0 | 0 | OK |
| `order_of_power` | 209 | 0 | 0 | OK |
| `lcm_orders_divides_lambda` | 271 | 0 | 0 | OK |
| `is_order_2_of` | 298 | 0 | 0 | OK |
| `minus1_order_2_rsa_test` | 312 | 0 | 0 | OK |
| `mixed67_order_2_rsa_test` | 318 | 0 | 0 | OK |
| `lcm_two_order2_not_lambda` | 324 | 0 | 0 | OK |
| `is_order_pin_g_p` | 335 | 0 | 0 | OK |
| `is_order_pin_g_q` | 340 | 0 | 0 | OK |
| `pin_unit_3_coprime` | 347 | 0 | 0 | OK |
| `powm_eq_1_iff_order_divides` | 353 | 0 | 0 | OK |
| `pow2_divides_pow2` | 364 | 0 | 0 | OK |
| `two_height_is_val2_ord` | 387 | 0 | 0 | OK |
| `order_2_mod_11` | 446 | 0 | 0 | OK |
| `order_2_mod_17` | 451 | 0 | 0 | OK |
| `two_height_independent_of_odd_multiple` | 458 | 0 | 0 | OK |
| `height_is_val2_ord_textbook` | 474 | 0 | 0 | OK |
| `zseq_length` | 510 | 0 | 0 | OK |
| `zseq_In_bounds` | 517 | 0 | 0 | OK |
| `zseq_Forall_distinct_head` | 530 | 0 | 0 | OK |
| `zseq_pairwise_distinct` | 550 | 0 | 0 | OK |
| `units_mod_prime_length` | 566 | 0 | 0 | OK |
| `units_mod_prime_In` | 570 | 0 | 0 | OK |
| `units_mod_prime_coprime` | 580 | 0 | 0 | OK |
| `units_mod_prime_distinct` | 592 | 0 | 0 | OK |
| `units_mod_prime_nonnil` | 602 | 0 | 0 | OK |
| `order_mul_coprime` | 610 | 0 | 0 | OK |
| `order_of_divisor_power` | 681 | 0 | 0 | OK |
| `order_lcm_attained` | 710 | 0 | 0 | OK |
| `exists_max_order_in` | 741 | 0 | 0 | OK |
| `zseq_In_interval` | 775 | 0 | 0 | OK |
| `unit_mod_in_list` | 788 | 0 | 0 | OK |
| `is_order_mod_base` | 809 | 0 | 0 | OK |
| `is_order_of_mod` | 823 | 0 | 0 | OK |
| `is_order_eq_mod` | 837 | 0 | 0 | OK |
| `primitive_root_exists` | 850 | 0 | 0 | OK |
| `order_semiprime_from_locals` | 916 | 0 | 0 | OK |
| `exists_unit_order_lambda` | 959 | 0 | 0 | OK |
| `is_order_pin_3_80` | 995 | 0 | 0 | OK |
| `exists_unit_order_lambda_pin` | 1004 | 0 | 0 | OK |
| `pin_attains_lambda` | 1010 | 0 | 0 | OK |
| `orders_generate_lambda_pin` | 1019 | 0 | 0 | OK |
| `mul_cancel_unit_mod` | 1029 | 0 | 0 | OK |
| `powm_eq_pow_cancel` | 1044 | 0 | 0 | OK |
| `powm_inj_lt_order` | 1068 | 0 | 0 | OK |
| `nodup_incl_le` | 1097 | 0 | 0 | OK |
| `powers_upto_length` | 1126 | 0 | 0 | OK |
| `powers_upto_In` | 1132 | 0 | 0 | OK |
| `powers_upto_NoDup` | 1145 | 0 | 0 | OK |
| `primitive_root_generates` | 1165 | 0 | 0 | OK |

## Paillier.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `powm_mul_base` | 23 | 0 | 0 | OK |
| `one_plus_N_pow` | 33 | 0 | 0 | OK |
| `paillier_L_of_plain` | 44 | 0 | 0 | OK |
| `paillier_L_recovers_exp` | 56 | 0 | 0 | OK |
| `paillier_add` | 68 | 0 | 0 | OK |
| `one_plus_N_order_N` | 86 | 0 | 0 | OK |

## PhiLambda.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `phi_eq_lambda_times_gcd` | 17 | 0 | 0 | OK |
| `phi_div_lambda_is_gcd` | 29 | 0 | 0 | OK |

## Pin.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `Zprime_sqrt` | 11 | 0 | 0 | OK |
| `pin187_N_pos` | 120 | 0 | 0 | OK |
| `pin187_N_gt_1` | 123 | 0 | 0 | OK |
| `pin187_p_neq_q` | 126 | 0 | 0 | OK |
| `pin187_p_lt_q` | 129 | 0 | 0 | OK |
| `pin187_p_prime` | 132 | 0 | 0 | OK |
| `pin187_q_prime` | 142 | 0 | 0 | OK |
| `pin1363_N_pos` | 210 | 0 | 0 | OK |
| `pin1363_N_gt_1` | 213 | 0 | 0 | OK |
| `pin1363_p_neq_q` | 216 | 0 | 0 | OK |
| `pin1363_p_lt_q` | 219 | 0 | 0 | OK |
| `pin1363_p_prime` | 222 | 0 | 0 | OK |
| `pin1363_q_prime` | 232 | 0 | 0 | OK |
| `pin2491_N_pos` | 300 | 0 | 0 | OK |
| `pin2491_N_gt_1` | 303 | 0 | 0 | OK |
| `pin2491_p_neq_q` | 306 | 0 | 0 | OK |
| `pin2491_p_lt_q` | 309 | 0 | 0 | OK |
| `pin2491_p_prime` | 312 | 0 | 0 | OK |
| `pin2491_q_prime` | 322 | 0 | 0 | OK |
| `pin_p_prime` | 439 | 0 | 0 | OK |
| `pin_q_prime` | 442 | 0 | 0 | OK |
| `pin_N_pos` | 445 | 0 | 0 | OK |
| `pin_N_gt_1` | 448 | 0 | 0 | OK |
| `pin_p_neq_q` | 451 | 0 | 0 | OK |
| `pin_p_lt_q` | 454 | 0 | 0 | OK |

## PollardP1.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `fermat_on_multiple` | 30 | 0 | 0 | OK |
| `gcd_onesided_semiprime` | 46 | 0 | 0 | OK |
| `pollard_p1_splits` | 62 | 0 | 0 | OK |
| `smooth_implies_public_annihilator` | 101 | 0 | 0 | OK |

## PotCheck.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `contribute_slot_one_is_rho_power` | 22 | 0 | 0 | OK |
| `update_first_is_old_first_to_rho` | 35 | 0 | 0 | OK |
| `update_pok_complete` | 50 | 0 | 0 | OK |
| `extracted_contributor_agrees` | 73 | 0 | 0 | OK |

## PotCl.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `potP_rsa_is_pot` | 38 | 0 | 0 | OK |
| `potP_cl_is_bqf_exp` | 50 | 0 | 0 | OK |
| `potP_rsa_at_zero` | 56 | 0 | 0 | OK |
| `potP_rsa_at_one` | 66 | 0 | 0 | OK |
| `potP_cl_at_zero` | 77 | 0 | 0 | OK |
| `potP_cl_at_one` | 88 | 0 | 0 | OK |
| `potP_rsa_contribute_multiplies` | 96 | 0 | 0 | OK |
| `potP_rsa_succ` | 119 | 0 | 0 | OK |
| `pot_cl_no_lambda` | 132 | 0 | 0 | OK |
| `pot_cl_inv_is_public` | 142 | 0 | 0 | OK |
| `pot_cl_contribute_slot0` | 147 | 0 | 0 | OK |
| `pot_cl_neg31_at_zero` | 158 | 0 | 0 | OK |
| `pot_cl_neg31_at_one` | 166 | 0 | 0 | OK |

## PotLadder.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `rho_ladder_0` | 30 | 0 | 0 | OK |
| `rho_ladder_succ` | 34 | 0 | 0 | OK |
| `rho_ladder_succ_is_power` | 39 | 0 | 0 | OK |
| `ladder_realizes_update` | 58 | 0 | 0 | OK |
| `contribution_ladder_step` | 75 | 0 | 0 | OK |
| `slot2_aux_is_ladder_one` | 109 | 0 | 0 | OK |
| `slot2_new_is_rho_sq` | 117 | 0 | 0 | OK |
| `slot2_aux_then_rho` | 129 | 0 | 0 | OK |
| `slot2_new_is_ladder_two` | 144 | 0 | 0 | OK |
| `slot2_leg1_complete` | 155 | 0 | 0 | OK |
| `slot2_leg2_complete` | 182 | 0 | 0 | OK |

## PowersOfTau.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `pot_at_zero` | 48 | 0 | 0 | OK |
| `pot_at_one` | 57 | 0 | 0 | OK |
| `pot_succ_is_tau_power` | 66 | 0 | 0 | OK |
| `pot_first_is_dlog` | 81 | 0 | 0 | OK |
| `pot_contribute_multiplies_tau` | 94 | 0 | 0 | OK |
| `two_contributors_product` | 110 | 0 | 0 | OK |
| `three_contributors_product` | 123 | 0 | 0 | OK |
| `coprime_powm` | 143 | 0 | 0 | OK |
| `powm_eq_implies_abs_annihilator` | 169 | 0 | 0 | OK |
| `honest_contribution_moves_string` | 213 | 0 | 0 | OK |
| `honest_tau_one_if_coprime` | 242 | 0 | 0 | OK |
| `powm_reduce_mod_order` | 263 | 0 | 0 | OK |
| `tau_inv_walks_backward` | 285 | 0 | 0 | OK |
| `backward_walker_is_tau_inv` | 314 | 0 | 0 | OK |
| `eqdl_complete` | 367 | 0 | 0 | OK |
| `eqdl_extracts_tau` | 392 | 0 | 0 | OK |
| `self_bil_checks_pot` | 446 | 0 | 0 | OK |
| `self_bil_evaluates_pot` | 465 | 0 | 0 | OK |

## Pratt.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `pratt_2_prime` | 48 | 0 | 0 | OK |
| `pratt_fermat_side` | 53 | 0 | 0 | OK |
| `duality_unique_order_2_on_prime` | 66 | 0 | 0 | OK |

## PreprocessGRA.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `prep_advice_depends_on_N` | 27 | 0 | 0 | OK |
| `prep_advice_ignores_y` | 31 | 0 | 0 | OK |
| `prep_factor_advice` | 35 | 0 | 0 | OK |
| `prep_id_advice_not_a_split` | 43 | 0 | 0 | OK |
| `prep_ginv_of_factor_advice` | 55 | 0 | 0 | OK |
| `prep_then_gra_factors` | 59 | 0 | 0 | OK |

## Presentation.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `rsa_order_divides_lambda` | 130 | 0 | 0 | OK |
| `cl_constructible_order_divides_2` | 138 | 0 | 0 | OK |
| `rsa_public_annihilator_is_none` | 145 | 0 | 0 | OK |
| `cl_public_annihilator_is_two` | 149 | 0 | 0 | OK |
| `rsa_minus1_constructible` | 153 | 0 | 0 | OK |
| `cl_unrestricted_LowOrder_B2` | 157 | 0 | 0 | OK |
| `cl_restricted_excludes_ambiguous` | 161 | 0 | 0 | OK |
| `mersenne31_wins_P_LowOrderOutside` | 170 | 0 | 0 | OK |
| `mersenne31_family_excludes_shanks` | 188 | 0 | 0 | OK |
| `ordinary_vs_mersenne_H` | 198 | 0 | 0 | OK |
| `mersenne_family_at_2` | 207 | 0 | 0 | OK |
| `class_number_solves_AR_neg31_id` | 211 | 0 | 0 | OK |
| `class_number_solves_AR_neg31_f` | 222 | 0 | 0 | OK |
| `class_number_solves_AR_neg31_sq` | 232 | 0 | 0 | OK |
| `class_number_solves_AR_neg31` | 247 | 0 | 0 | OK |
| `shanks_is_annihilator` | 260 | 0 | 0 | OK |
| `shanks_AR_is_fractional_root` | 269 | 0 | 0 | OK |
| `cl_AR_C_broken_when_two_in_C` | 283 | 0 | 0 | OK |
| `rsa_trapdoor_annihilator_is_lambda` | 302 | 0 | 0 | OK |
| `rsa_lambda_solves_adaptive_root` | 306 | 0 | 0 | OK |
| `cl_has_no_lambda_plus_one` | 315 | 0 | 0 | OK |
| `no_crt_split_from_disc` | 335 | 0 | 0 | OK |
| `cl_exp_0_is_id` | 341 | 0 | 0 | OK |
| `cl_exp_1_is_f` | 345 | 0 | 0 | OK |
| `cl_inv_is_bqf_inv` | 352 | 0 | 0 | OK |
| `cl_mul_inv_equiv_id` | 356 | 0 | 0 | OK |
| `unit_inverse_exists` | 373 | 0 | 0 | OK |
| `rsa_trapdoor_inv_is_root` | 389 | 0 | 0 | OK |
| `Pexp_0` | 411 | 0 | 0 | OK |
| `Pexp_S_rsa` | 418 | 0 | 0 | OK |

## PublicQuad.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `find_exp_from_sound` | 55 | 0 | 0 | OK |
| `find_exp_from_complete` | 85 | 0 | 0 | OK |
| `find_exp_complete` | 108 | 0 | 0 | OK |
| `find_exp_sound` | 124 | 0 | 0 | OK |
| `pot_crs_from_length` | 172 | 0 | 0 | OK |
| `pot_crs_length` | 182 | 0 | 0 | OK |
| `pot_crs_from_nth` | 189 | 0 | 0 | OK |
| `pot_crs_nth` | 206 | 0 | 0 | OK |
| `recover_honest` | 231 | 0 | 0 | OK |
| `quad_row_spec` | 278 | 0 | 0 | OK |
| `quad_combine_spec` | 314 | 0 | 0 | OK |
| `quad_combine_is_product` | 349 | 0 | 0 | OK |
| `first_exps_nn` | 379 | 0 | 0 | OK |
| `public_quad_complete` | 391 | 0 | 0 | OK |
| `public_quad_qap` | 421 | 0 | 0 | OK |
| `public_quad_pin_accepts` | 455 | 0 | 0 | OK |
| `public_quad_pin_rejects_group_mul` | 466 | 0 | 0 | OK |
| `public_quad_pin_sum_neq_prod` | 478 | 0 | 0 | OK |
| `public_quad_pin_qap` | 484 | 0 | 0 | OK |

## QAP.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `poly_eval_sub` | 34 | 0 | 0 | OK |
| `qap_rem_eval` | 51 | 0 | 0 | OK |
| `qap_at_iff_rem_zero` | 63 | 0 | 0 | OK |
| `qap_complete_at_tau` | 70 | 0 | 0 | OK |
| `qap_point_sound` | 91 | 0 | 0 | OK |
| `qap_sound_at_tau` | 109 | 0 | 0 | OK |
| `poly_eval_lincomb` | 151 | 0 | 0 | OK |
| `wires_nn_lincomb_nonneg` | 166 | 0 | 0 | OK |
| `pot_wires_is_lincomb` | 178 | 0 | 0 | OK |
| `same_witness_two_families` | 198 | 0 | 0 | OK |
| `qap_witness_complete` | 210 | 0 | 0 | OK |
| `pot_wires_bounded` | 232 | 0 | 0 | OK |
| `pot_wires_app` | 246 | 0 | 0 | OK |

## QRModN.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `euler_crit_agree` | 39 | 0 | 0 | OK |
| `mod_pq_to_p` | 46 | 0 | 0 | OK |
| `qr_N_implies_local` | 57 | 0 | 0 | OK |
| `qr_N_of_local` | 77 | 0 | 0 | OK |
| `qr_N_iff_both` | 102 | 0 | 0 | OK |
| `euler_sign_of_pm1` | 115 | 0 | 0 | OK |
| `euler_sign_of_qr` | 132 | 0 | 0 | OK |
| `jacobi_of_qr_N` | 146 | 0 | 0 | OK |
| `euler_one_implies_qr_blum` | 166 | 0 | 0 | OK |
| `euler_sign_one_is_crit_one` | 188 | 0 | 0 | OK |
| `euler_sign_minus_is_crit_pm1` | 205 | 0 | 0 | OK |
| `euler_sign_one_implies_qr_blum` | 220 | 0 | 0 | OK |
| `euler_sign_minus_implies_qnr` | 234 | 0 | 0 | OK |
| `coprime_neg1` | 247 | 0 | 0 | OK |
| `coprime_opp` | 255 | 0 | 0 | OK |
| `euler_sign_neg1_blum` | 259 | 0 | 0 | OK |
| `euler_crit_mul` | 276 | 0 | 0 | OK |
| `euler_sign_mul` | 291 | 0 | 0 | OK |
| `euler_sign_neg_a` | 335 | 0 | 0 | OK |
| `jacobi_neg1_blum` | 350 | 0 | 0 | OK |
| `neg1_not_qr_N_blum` | 365 | 0 | 0 | OK |
| `blum_jacobi_one_exactly_one_pm` | 385 | 0 | 0 | OK |
| `williams_both_qr_is_qr_N` | 436 | 0 | 0 | OK |
| `coprime_powm_prime` | 467 | 0 | 0 | OK |
| `coprime_powm_N_prime` | 483 | 0 | 0 | OK |
| `jacobi_even_power` | 504 | 0 | 0 | OK |
| `jacobi_odd_power` | 534 | 0 | 0 | OK |
| `jacobi_sees_only_parity` | 610 | 0 | 0 | OK |
| `even_pow_succ` | 635 | 0 | 0 | OK |
| `odd_pow_pos` | 652 | 0 | 0 | OK |
| `pot_jacobi_tail_constant` | 674 | 0 | 0 | OK |
| `sixth_root_from_square_and_cube` | 708 | 0 | 0 | OK |
| `cubic_decision_vacuous` | 731 | 0 | 0 | OK |

## QuadResidue.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `odd_prime_minus1_even` | 22 | 0 | 0 | OK |
| `p_mod4_3_decomp` | 38 | 0 | 0 | OK |
| `p_mod8_decomp` | 44 | 0 | 0 | OK |
| `mod8_3_is_mod4_3` | 50 | 0 | 0 | OK |
| `mod8_7_is_mod4_3` | 59 | 0 | 0 | OK |
| `blum_prime_pminus1_form` | 69 | 0 | 0 | OK |
| `two_times_div4` | 82 | 0 | 0 | OK |
| `half_plus_one` | 95 | 0 | 0 | OK |
| `euler_qr_is_one` | 110 | 0 | 0 | OK |
| `sqrt_mod4_3_correct` | 151 | 0 | 0 | OK |
| `pow_neg1_even` | 179 | 0 | 0 | OK |
| `pow_neg1_odd` | 189 | 0 | 0 | OK |
| `neg1_euler_mod4_3` | 200 | 0 | 0 | OK |

## RSA.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `rsa_N_gt_1` | 39 | 0 | 0 | OK |
| `rsa_lambda_pos` | 46 | 0 | 0 | OK |
| `rsa_lambda_gt_1` | 52 | 0 | 0 | OK |
| `rsa_phi_pos` | 71 | 0 | 0 | OK |
| `rsa_lambda_divides_phi` | 77 | 0 | 0 | OK |
| `rsa_ed_minus_1_divides` | 80 | 0 | 0 | OK |
| `rsa_ed_gt_1` | 89 | 0 | 0 | OK |
| `rsa_dec_enc_units` | 102 | 0 | 0 | OK |
| `rsa_enc_dec_units` | 126 | 0 | 0 | OK |
| `rsa_d_is_cube_root_map` | 153 | 0 | 0 | OK |
| `prime_11` | 164 | 0 | 0 | OK |
| `prime_17` | 173 | 0 | 0 | OK |
| `rsa_test_lambda` | 183 | 0 | 0 | OK |
| `rsa_test_phi` | 186 | 0 | 0 | OK |
| `rsa_test_inv` | 189 | 0 | 0 | OK |
| `rsa_test_coprime_e` | 192 | 0 | 0 | OK |
| `rsa_test_N` | 207 | 0 | 0 | OK |
| `rsa_test_vector` | 210 | 0 | 0 | OK |
| `rsa_test_roundtrip` | 214 | 0 | 0 | OK |
| `rsa_test_annihilator` | 218 | 0 | 0 | OK |
| `N_cong_q_mod_pminus1` | 233 | 0 | 0 | OK |
| `gcd_polyN_pminus1_is_gcd_at_q` | 244 | 0 | 0 | OK |

## RabinWilliams.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `rabin_of_square` | 37 | 0 | 0 | OK |
| `rw_p_is_blum` | 51 | 0 | 0 | OK |
| `rw_q_is_blum` | 57 | 0 | 0 | OK |
| `rw_pair_odd` | 63 | 0 | 0 | OK |
| `lcm_even_of_even_l` | 72 | 0 | 0 | OK |
| `lambda_even_odd_primes` | 81 | 0 | 0 | OK |
| `two_not_rsa_exponent` | 92 | 0 | 0 | OK |
| `pm1_cases` | 123 | 0 | 0 | OK |
| `williams_tweak_exists` | 129 | 0 | 0 | OK |
| `williams_tweak_unique` | 143 | 0 | 0 | OK |
| `williams_which_correct` | 175 | 0 | 0 | OK |
| `williams_two_symbol_p` | 191 | 0 | 0 | OK |
| `williams_two_symbol_q` | 195 | 0 | 0 | OK |
| `williams_neg1_on_blum` | 199 | 0 | 0 | OK |
| `rabin_roots_split` | 218 | 0 | 0 | OK |
| `rabin_oracle_nonassociate_factors` | 269 | 0 | 0 | OK |
| `rw_verify_of_root` | 305 | 0 | 0 | OK |
| `kg_rw_implies_blum` | 316 | 0 | 0 | OK |
| `kg_rw_pminus1_almost_odd` | 324 | 0 | 0 | OK |

## Range2.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `range2_bits` | 24 | 0 | 0 | OK |
| `range2_bit_qap` | 34 | 0 | 0 | OK |
| `range2_encoding` | 51 | 0 | 0 | OK |
| `range2_eval_commit` | 67 | 0 | 0 | OK |

## SAGM.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `sagm_eval_21` | 31 | 0 | 0 | OK |
| `sagm_product_adds_exponents` | 36 | 0 | 0 | OK |
| `sagm_mul_exps` | 44 | 0 | 0 | OK |

## SameW.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `zip_scale_eval` | 32 | 0 | 0 | OK |
| `zip_wires_nn` | 55 | 0 | 0 | OK |
| `same_w_check` | 76 | 0 | 0 | OK |

## SharedKey.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `lambda_A_divides_product` | 52 | 0 | 0 | OK |
| `lambda_B_divides_product` | 56 | 0 | 0 | OK |
| `lambda_product_pos` | 60 | 0 | 0 | OK |
| `lambda_product_gt_1` | 73 | 0 | 0 | OK |
| `coprime_product_split` | 83 | 0 | 0 | OK |
| `crt_mod_eq_coprime` | 89 | 0 | 0 | OK |
| `crt_one_coprime_moduli` | 106 | 0 | 0 | OK |
| `carmichael_shared` | 127 | 0 | 0 | OK |
| `gcd_of_divisor` | 154 | 0 | 0 | OK |
| `inverses_agree_mod_gcd` | 172 | 0 | 0 | OK |
| `rsa_e_gcd_lambda` | 203 | 0 | 0 | OK |
| `crt_exists_gcd` | 207 | 0 | 0 | OK |
| `d_star_exists` | 254 | 0 | 0 | OK |
| `d_star_exists_nonneg` | 274 | 0 | 0 | OK |
| `d_star_inverts` | 302 | 0 | 0 | OK |
| `powm_mod_lambda` | 330 | 0 | 0 | OK |
| `shared_dec_mod_A` | 358 | 0 | 0 | OK |
| `shared_dec_mod_B` | 372 | 0 | 0 | OK |
| `shared_dec_eq_powm` | 384 | 0 | 0 | OK |
| `prime_5` | 429 | 0 | 0 | OK |
| `prime_23` | 437 | 0 | 0 | OK |
| `prime_41` | 449 | 0 | 0 | OK |
| `rsa_5_23_N` | 489 | 0 | 0 | OK |
| `rsa_5_41_N` | 492 | 0 | 0 | OK |
| `d_star_depends_on_both` | 495 | 0 | 0 | OK |
| `two_partners_two_dstars` | 505 | 0 | 0 | OK |
| `product_carries_component_keygen` | 526 | 0 | 0 | OK |
| `product_common_e_inverts` | 532 | 0 | 0 | OK |
| `product_refuses_shared_prime` | 542 | 0 | 0 | OK |
| `d_star_gt_lambda_div_e` | 548 | 0 | 0 | OK |
| `carmichael_shared3` | 586 | 0 | 0 | OK |
| `d_star_unique_mod_lambda` | 646 | 0 | 0 | OK |
| `d_star_inverts_on_A` | 662 | 0 | 0 | OK |
| `d_star_inverts_on_B` | 676 | 0 | 0 | OK |
| `d_star_ed_minus_1_divides_lambda` | 690 | 0 | 0 | OK |
| `d_star_annihilates_shared` | 703 | 0 | 0 | OK |
| `d_star_decrypts_B` | 727 | 0 | 0 | OK |
| `d_star_decrypts_A` | 742 | 0 | 0 | OK |
| `coprime_powm` | 767 | 0 | 0 | OK |
| `shared_N_gt_1` | 793 | 0 | 0 | OK |
| `dstar_power_crs_is_powm` | 802 | 0 | 0 | OK |
| `shared_dec_is_eth_root` | 844 | 0 | 0 | OK |
| `srs_first_checks` | 871 | 0 | 0 | OK |
| `srs_step_checks` | 893 | 0 | 0 | OK |
| `srs_first_is_rsa` | 934 | 0 | 0 | OK |
| `srs_first_is_strong_rsa` | 949 | 0 | 0 | OK |
| `lambda_plus_one_is_other_strong_rsa` | 965 | 0 | 0 | OK |
| `dstar_inverts_every_unit` | 984 | 0 | 0 | OK |
| `powm_eq_implies_abs_annihilator` | 1008 | 0 | 0 | OK |
| `dlog_of_srs_agrees_mod_order` | 1052 | 0 | 0 | OK |
| `dlog_at_full_order_inverts_e` | 1075 | 0 | 0 | OK |

## SharedModulus.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `dkg_N_is_product` | 29 | 0 | 0 | OK |
| `dkg_N_cross_terms` | 34 | 0 | 0 | OK |
| `published_sum_is_phi_plus_one` | 40 | 0 | 0 | OK |
| `two_prime_four_roots_triprime_eight` | 45 | 0 | 0 | OK |
| `triprime_mixed_root_refutes_biprime` | 70 | 0 | 0 | OK |

## SharedPrime.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `gcd_shared_prime` | 14 | 0 | 0 | OK |
| `gcd_shared_prime_divides_both` | 29 | 0 | 0 | OK |

## SieveRelation.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `even_nonneg_pow_square` | 30 | 0 | 0 | OK |
| `square_times_square` | 44 | 0 | 0 | OK |
| `even_exp_2_3_5_square` | 51 | 0 | 0 | OK |
| `mul_mod_cong` | 61 | 0 | 0 | OK |
| `not_div_mod` | 75 | 0 | 0 | OK |
| `dixon_two_relations` | 85 | 0 | 0 | OK |
| `dixon_combination_splits` | 99 | 0 | 0 | OK |
| `dixon_pin_residue_factors` | 118 | 0 | 0 | OK |
| `dixon_pin_cong` | 122 | 0 | 0 | OK |
| `dixon_pin_not_assoc` | 138 | 0 | 0 | OK |
| `dixon_pin_splits` | 147 | 0 | 0 | OK |
| `dixon_pin_gcd` | 163 | 0 | 0 | OK |
| `dixon_pin_b_splits` | 168 | 0 | 0 | OK |
| `asquare_pin_splits` | 187 | 0 | 0 | OK |
| `hom_quad_remainder` | 206 | 0 | 0 | OK |
| `hom_quad_cong` | 213 | 0 | 0 | OK |
| `poly_eval_quad` | 236 | 0 | 0 | OK |
| `nfs_eval_irr` | 241 | 0 | 0 | OK |
| `nfs_eval_red` | 245 | 0 | 0 | OK |
| `nfs_common_root_irr` | 249 | 0 | 0 | OK |
| `nfs_common_root_red` | 253 | 0 | 0 | OK |
| `nfs_irr_disc_neg` | 257 | 0 | 0 | OK |
| `nfs_neg_not_square` | 265 | 0 | 0 | OK |
| `nfs_red_splits_Z` | 272 | 0 | 0 | OK |
| `nfs_F_cong_GH_irr` | 277 | 0 | 0 | OK |
| `nfs_F_cong_GH_red` | 287 | 0 | 0 | OK |
| `nfs_two_sided_product` | 299 | 0 | 0 | OK |
| `nfs_two_sided_pin_squares` | 318 | 0 | 0 | OK |
| `nfs_two_sided_pin_sqrt1` | 351 | 0 | 0 | OK |
| `nfs_two_sided_splits` | 361 | 0 | 0 | OK |
| `nfs_two_sided_gcd` | 374 | 0 | 0 | OK |
| `nfs_onesided_no_split` | 379 | 0 | 0 | OK |

## SixthType.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `form_N01_disc` | 21 | 0 | 0 | OK |
| `minus4N_mod4` | 27 | 0 | 0 | OK |
| `minus4N_div4` | 33 | 0 | 0 | OK |
| `form_N01_equiv_principal` | 42 | 0 | 0 | OK |
| `Nsq_minus_4_factors` | 63 | 0 | 0 | OK |
| `gcd_N_minus_2_N` | 67 | 0 | 0 | OK |
| `odd_N_gcd_Nminus2` | 78 | 0 | 0 | OK |
| `factor_4N_gives_square_disc` | 100 | 0 | 0 | OK |
| `N_plus_one_powm` | 115 | 0 | 0 | OK |
| `N_plus_one_euler_is_one` | 130 | 0 | 0 | OK |
| `form_p0q_disc` | 151 | 0 | 0 | OK |
| `form_p0q_ambiguous` | 157 | 0 | 0 | OK |
| `form_p0q_reduced_when_ordered` | 161 | 0 | 0 | OK |
| `williams_N_mod4` | 182 | 0 | 0 | OK |
| `both_1_mod4_N_mod4` | 190 | 0 | 0 | OK |
| `mixed_mod4_N_mod4` | 198 | 0 | 0 | OK |

## SmallExponent.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `rsa_poly_degree_is_e` | 21 | 0 | 0 | OK |
| `cube_is_powm3` | 26 | 0 | 0 | OK |
| `unique_nonneg_rep` | 34 | 0 | 0 | OK |
| `three_moduli_divide` | 49 | 0 | 0 | OK |
| `hastad_cube_if_small` | 74 | 0 | 0 | OK |
| `related_message_common_root` | 97 | 0 | 0 | OK |
| `fr_cube_gap` | 110 | 0 | 0 | OK |
| `fr_cube_gap_mod` | 116 | 0 | 0 | OK |

## SolverRestrict.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `sagm_powm_mul_exp` | 30 | 0 | 0 | OK |
| `sagm_root_of_generator_pin` | 41 | 0 | 0 | OK |
| `sagm_ae_minus_one_is_lambda` | 45 | 0 | 0 | OK |
| `sagm_generator_annihilated` | 49 | 0 | 0 | OK |
| `sagm_only_miller_splits` | 53 | 0 | 0 | OK |
| `sagm_scale_eval_pin` | 61 | 0 | 0 | OK |
| `sagm_scale_lambda_type` | 67 | 0 | 0 | OK |
| `safeprime_e3_names_p` | 75 | 0 | 0 | OK |
| `safeprime_e5_names_q` | 81 | 0 | 0 | OK |
| `safeprime_e3_not_residual` | 87 | 0 | 0 | OK |
| `safeprime_residual_e7` | 91 | 0 | 0 | OK |
| `poly_e_constant` | 104 | 0 | 0 | OK |
| `poly_e_constant_is_fixed_e` | 108 | 0 | 0 | OK |
| `poly_e_X_two_points` | 113 | 0 | 0 | OK |
| `poly_e_X_not_rerand` | 117 | 0 | 0 | OK |
| `poly_e_nonconstant_not_fixed_parameter` | 121 | 0 | 0 | OK |
| `poly_e_quadratic` | 135 | 0 | 0 | OK |
| `poly_e_quadratic_residual_shaped` | 139 | 0 | 0 | OK |
| `poly_e_quadratic_leftover_with_period` | 146 | 0 | 0 | OK |
| `poly_e_quadratic_encrypt_not_leftover` | 150 | 0 | 0 | OK |
| `poly_e_square_even_peel` | 157 | 0 | 0 | OK |
| `reject_sample_public_e_emits_5` | 168 | 0 | 0 | OK |
| `reject_sample_emits_nonresidual` | 172 | 0 | 0 | OK |

## SolverShape.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `shape_even_ndiv_odd` | 32 | 0 | 0 | OK |
| `shape_monomial_k2_period_obstruction` | 39 | 0 | 0 | OK |
| `shape_monomial_k2_pin` | 47 | 0 | 0 | OK |
| `shape_inverse_of_36_residual_shaped` | 55 | 0 | 0 | OK |
| `shape_inverse_of_generator` | 59 | 0 | 0 | OK |
| `shape_inverse_generator_miller` | 64 | 0 | 0 | OK |
| `shape_affine_identity_forbidden` | 74 | 0 | 0 | OK |
| `shape_affine_eval_not_zero` | 83 | 0 | 0 | OK |
| `shape_affine_pointwise_const_residual` | 87 | 0 | 0 | OK |
| `shape_eth_root_of_1` | 93 | 0 | 0 | OK |
| `shape_unique_eth_root` | 109 | 0 | 0 | OK |
| `shape_two_unit_cube_roots_agree` | 122 | 0 | 0 | OK |
| `shape_unique_unit_cube_root_of_36` | 137 | 0 | 0 | OK |
| `shape_fr_small_integer` | 152 | 0 | 0 | OK |
| `shape_fr_cube_gap_small` | 160 | 0 | 0 | OK |
| `shape_fr_residual_not_integer_cube` | 165 | 0 | 0 | OK |
| `shape_fr_reduced_offset_not_integer` | 172 | 0 | 0 | OK |
| `shape_chaum_unblind` | 179 | 0 | 0 | OK |
| `shape_chaum_recovers_cube_root` | 189 | 0 | 0 | OK |
| `shape_chaum_e_is_protocol` | 193 | 0 | 0 | OK |
| `shape_jacobi_e_on_square` | 202 | 0 | 0 | OK |
| `shape_jacobi_e_on_nonsquare` | 207 | 0 | 0 | OK |
| `shape_short_period_of_y_no_split` | 215 | 0 | 0 | OK |
| `shape_lambda_quality_miller` | 225 | 0 | 0 | OK |
| `shape_ed_minus_one_is_lambda` | 235 | 0 | 0 | OK |
| `shape_ed_miller` | 240 | 0 | 0 | OK |
| `shape_e3_not_invertible_mod_Nminus1` | 250 | 0 | 0 | OK |
| `shape_wrong_euler_inv` | 255 | 0 | 0 | OK |
| `shape_crt_residues` | 265 | 0 | 0 | OK |
| `shape_crt_recovers_root` | 270 | 0 | 0 | OK |
| `shape_crt_moduli_are_factors` | 274 | 0 | 0 | OK |
| `shape_miller_e11_on_y_splits` | 285 | 0 | 0 | OK |
| `shape_miller_e3_on_y_survives` | 293 | 0 | 0 | OK |
| `shape_public_chain_e3` | 305 | 0 | 0 | OK |
| `shape_trapdoor_chain_d27` | 313 | 0 | 0 | OK |
| `shape_poly_x_quadratic` | 318 | 0 | 0 | OK |
| `shape_public_bases_2_3` | 326 | 0 | 0 | OK |
| `shape_gcdfree_bounded_from_y` | 336 | 0 | 0 | OK |
| `shape_public_exp_not_membership` | 344 | 0 | 0 | OK |

## SrsaDict.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `dict_e_eq_d` | 21 | 0 | 0 | OK |
| `dict_e43_same_x_leaf` | 25 | 0 | 0 | OK |
| `dict_N_mod_40_is_d` | 29 | 0 | 0 | OK |
| `dict_public_N_mod_40` | 33 | 0 | 0 | OK |
| `dict_y_to_d` | 38 | 0 | 0 | OK |
| `dict_x93_e67` | 42 | 0 | 0 | OK |
| `dict_x25_e11` | 46 | 0 | 0 | OK |
| `dict_x25_e51` | 50 | 0 | 0 | OK |
| `dict_x15_e29` | 54 | 0 | 0 | OK |
| `dict_x15_e69` | 58 | 0 | 0 | OK |
| `dict_x168_e61` | 62 | 0 | 0 | OK |
| `dict_x104_e57` | 66 | 0 | 0 | OK |
| `dict_x185_e53` | 70 | 0 | 0 | OK |
| `dict_xy_e41` | 74 | 0 | 0 | OK |
| `dict_y_lambda_type` | 78 | 0 | 0 | OK |
| `dict_e_plus_80` | 82 | 0 | 0 | OK |
| `dict_phi80` | 86 | 0 | 0 | OK |
| `dict_phi40` | 90 | 0 | 0 | OK |
| `dict_two_e_per_x` | 94 | 0 | 0 | OK |
| `dict_e_mod_40` | 98 | 0 | 0 | OK |
| `dict_kernel_1_41` | 102 | 0 | 0 | OK |
| `dict_cube_bij_on_cyc` | 108 | 0 | 0 | OK |
| `dict_27th_is_inverse_auto` | 112 | 0 | 0 | OK |
| `dict_compose_autos` | 117 | 0 | 0 | OK |
| `dict_ae_is_lambda_plus_1` | 122 | 0 | 0 | OK |
| `dict_bits_of_27` | 126 | 0 | 0 | OK |
| `dict_binary_product` | 130 | 0 | 0 | OK |
| `dict_add_chain_y6` | 137 | 0 | 0 | OK |
| `dict_add_chain_y12` | 141 | 0 | 0 | OK |
| `dict_add_chain_y24` | 145 | 0 | 0 | OK |
| `dict_k_odd` | 149 | 0 | 0 | OK |
| `dict_hamming_27` | 153 | 0 | 0 | OK |
| `dict_naf_shape` | 157 | 0 | 0 | OK |
| `dict_y25` | 163 | 0 | 0 | OK |
| `dict_y16_is_g5sq` | 167 | 0 | 0 | OK |
| `dict_sagm_on_y` | 172 | 0 | 0 | OK |
| `dict_y81` | 176 | 0 | 0 | OK |
| `dict_ae_lambda_plus_1` | 180 | 0 | 0 | OK |
| `dict_e43_same_x` | 184 | 0 | 0 | OK |
| `dict_e83_same_x` | 188 | 0 | 0 | OK |
| `dict_e43_minus_3` | 192 | 0 | 0 | OK |
| `dict_e83_minus_3` | 196 | 0 | 0 | OK |
| `dict_e67_coprime` | 200 | 0 | 0 | OK |
| `dict_e51_coprime` | 204 | 0 | 0 | OK |
| `dict_e61_coprime` | 208 | 0 | 0 | OK |
| `dict_e57_coprime` | 212 | 0 | 0 | OK |
| `dict_e29_coprime` | 216 | 0 | 0 | OK |
| `dict_e39_coprime` | 220 | 0 | 0 | OK |
| `dict_x26_e39` | 224 | 0 | 0 | OK |
| `dict_self_inverse_11` | 228 | 0 | 0 | OK |
| `dict_sagm_ae_minus_1` | 232 | 0 | 0 | OK |
| `dict_inv_mod_40` | 236 | 0 | 0 | OK |
| `dict_inv_mod_lam` | 240 | 0 | 0 | OK |
| `dict_cycle_70_cube` | 244 | 0 | 0 | OK |
| `dict_cycle_42_cube` | 248 | 0 | 0 | OK |
| `dict_cycle_36_cube` | 252 | 0 | 0 | OK |
| `dict_cycle_93_cube` | 256 | 0 | 0 | OK |
| `dict_three_order_4_mod_40` | 260 | 0 | 0 | OK |
| `dict_27_order_4_mod_40` | 264 | 0 | 0 | OK |
| `dict_cycle2_9` | 268 | 0 | 0 | OK |
| `dict_cycle2_168` | 272 | 0 | 0 | OK |
| `dict_cycle2_15` | 276 | 0 | 0 | OK |
| `dict_k27_coords` | 280 | 0 | 0 | OK |
| `dict_e3_coords` | 285 | 0 | 0 | OK |
| `dict_3_order_4_mod_40` | 290 | 0 | 0 | OK |
| `dict_cube_root_of_2` | 295 | 0 | 0 | OK |
| `dict_sagm_of_3` | 300 | 0 | 0 | OK |
| `dict_75_not_42` | 305 | 0 | 0 | OK |
| `dict_cycle2_60` | 309 | 0 | 0 | OK |
| `dict_cycle3_25` | 313 | 0 | 0 | OK |
| `dict_cycle3_104` | 317 | 0 | 0 | OK |
| `dict_cycle3_59` | 321 | 0 | 0 | OK |
| `dict_cycle3_53` | 325 | 0 | 0 | OK |
| `dict_cycle4_49` | 329 | 0 | 0 | OK |
| `dict_cycle4_26` | 333 | 0 | 0 | OK |
| `dict_cycle4_185` | 337 | 0 | 0 | OK |
| `dict_cycle4_179` | 341 | 0 | 0 | OK |
| `dict_cbrt_2_in_ltwo` | 345 | 0 | 0 | OK |
| `dict_cbrt_3_in_lthree` | 350 | 0 | 0 | OK |
| `dict_cbrt_36_in_ly` | 355 | 0 | 0 | OK |
| `dict_three_x_for_k27` | 360 | 0 | 0 | OK |

## SrsaEngines.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `engine_pollard_p1` | 21 | 0 | 0 | OK |
| `engine_rho_walk` | 31 | 0 | 0 | OK |
| `engine_bsgs_wrong_order` | 37 | 0 | 0 | OK |
| `engine_fermat_splits` | 42 | 0 | 0 | OK |
| `engine_trial_division` | 56 | 0 | 0 | OK |
| `engine_williams_pplus1` | 64 | 0 | 0 | OK |
| `engine_index_calculus_Nminus1` | 72 | 0 | 0 | OK |
| `engine_F9_splits` | 76 | 0 | 0 | OK |
| `engine_F10_splits` | 84 | 0 | 0 | OK |
| `engine_mersenne_255` | 92 | 0 | 0 | OK |
| `engine_pminus1_B8` | 100 | 0 | 0 | OK |
| `engine_rho_x2_minus_1` | 104 | 0 | 0 | OK |
| `engine_williams_P3_no_split` | 110 | 0 | 0 | OK |
| `engine_factorial_trial` | 114 | 0 | 0 | OK |
| `engine_hart_square` | 118 | 0 | 0 | OK |
| `engine_fermat_recovers` | 124 | 0 | 0 | OK |
| `engine_trial_13_then_11` | 136 | 0 | 0 | OK |
| `engine_fibonacci_gcd_engine` | 146 | 0 | 0 | OK |
| `engine_mersenne_engine` | 154 | 0 | 0 | OK |
| `engine_shor_period_of_2` | 162 | 0 | 0 | OK |
| `engine_lam_ne_Nminus1` | 167 | 0 | 0 | OK |

## SrsaExtra.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `extra_shamir_two_leftovers` | 20 | 0 | 0 | OK |
| `extra_crt_dp` | 24 | 0 | 0 | OK |
| `extra_fermat_difference` | 29 | 0 | 0 | OK |
| `extra_sqrt_splits` | 34 | 0 | 0 | OK |
| `extra_order_is_lambda` | 42 | 0 | 0 | OK |
| `extra_factor_e_minus_1` | 46 | 0 | 0 | OK |
| `extra_factor_N_minus_1` | 50 | 0 | 0 | OK |
| `extra_wiener_d_not_small` | 54 | 0 | 0 | OK |
| `extra_sequential_square_period` | 58 | 0 | 0 | OK |
| `extra_height_mismatch` | 62 | 0 | 0 | OK |
| `extra_primitive_root_mod_p` | 67 | 0 | 0 | OK |
| `extra_half_bits` | 72 | 0 | 0 | OK |
| `extra_cubic_symbol_vacuous` | 77 | 0 | 0 | OK |
| `extra_inverse_challenge` | 81 | 0 | 0 | OK |
| `extra_neg_y` | 85 | 0 | 0 | OK |
| `extra_two_y` | 89 | 0 | 0 | OK |
| `extra_three_powers_gcd` | 93 | 0 | 0 | OK |
| `extra_y_plus_1_root` | 97 | 0 | 0 | OK |
| `extra_batch_gcd_of_roots` | 101 | 0 | 0 | OK |
| `extra_adaptive_lambda_plus_one` | 105 | 0 | 0 | OK |
| `extra_same_y_two_moduli` | 110 | 0 | 0 | OK |
| `extra_twin_exponents` | 115 | 0 | 0 | OK |
| `extra_product_of_leftovers` | 119 | 0 | 0 | OK |
| `extra_rerand_forces_fixed_e` | 125 | 0 | 0 | OK |
| `extra_coins_independent_fixed_e` | 129 | 0 | 0 | OK |
| `extra_squaring_only` | 134 | 0 | 0 | OK |
| `extra_advice_on_y_lsb` | 140 | 0 | 0 | OK |
| `extra_streaming_first_bit` | 144 | 0 | 0 | OK |
| `extra_dl_base3` | 148 | 0 | 0 | OK |
| `extra_p_plus_q` | 152 | 0 | 0 | OK |
| `extra_torus_order_is_y` | 156 | 0 | 0 | OK |
| `extra_hamming_N` | 160 | 0 | 0 | OK |
| `extra_digit_reverse_splits` | 164 | 0 | 0 | OK |
| `extra_digits_of_N` | 172 | 0 | 0 | OK |
| `extra_N_mod_100` | 177 | 0 | 0 | OK |
| `extra_nextprime_N` | 181 | 0 | 0 | OK |
| `extra_prevprime_associate` | 185 | 0 | 0 | OK |
| `extra_xor_leftovers` | 189 | 0 | 0 | OK |
| `extra_related_y_cube` | 195 | 0 | 0 | OK |
| `extra_leftover_pair_splits` | 200 | 0 | 0 | OK |
| `extra_first_nibble` | 208 | 0 | 0 | OK |
| `extra_two_bit_advice` | 212 | 0 | 0 | OK |
| `extra_dl_base5` | 216 | 0 | 0 | OK |
| `extra_dl_base9` | 220 | 0 | 0 | OK |
| `extra_gen_pair_42_9` | 224 | 0 | 0 | OK |
| `extra_gen_pair_42_53` | 232 | 0 | 0 | OK |
| `extra_gen_pair_42_93` | 240 | 0 | 0 | OK |
| `extra_y_minus_x` | 248 | 0 | 0 | OK |
| `extra_advice_five_div_lam` | 252 | 0 | 0 | OK |
| `extra_advice_local_9` | 256 | 0 | 0 | OK |
| `extra_euclid_x_minus_y` | 260 | 0 | 0 | OK |
| `extra_low_bits_y` | 264 | 0 | 0 | OK |
| `extra_hensel_p2` | 268 | 0 | 0 | OK |
| `extra_dp` | 272 | 0 | 0 | OK |
| `extra_edp_minus_1` | 276 | 0 | 0 | OK |
| `extra_dq` | 280 | 0 | 0 | OK |
| `extra_edq_minus_1` | 284 | 0 | 0 | OK |
| `extra_shamir_3_7` | 288 | 0 | 0 | OK |
| `extra_rerand_fixed_e` | 292 | 0 | 0 | OK |

## SrsaModulus.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `modulus_paillier_carrier` | 24 | 0 | 0 | OK |
| `modulus_williams_Ve` | 32 | 0 | 0 | OK |
| `modulus_ou_carrier` | 37 | 0 | 0 | OK |
| `modulus_dj_carrier` | 46 | 0 | 0 | OK |
| `modulus_cocks_jacobi` | 50 | 0 | 0 | OK |
| `modulus_prime_power_field` | 54 | 0 | 0 | OK |
| `modulus_two_safeprimes` | 60 | 0 | 0 | OK |
| `modulus_rw_shape_odd_e` | 71 | 0 | 0 | OK |
| `modulus_twins` | 76 | 0 | 0 | OK |
| `modulus_unbalanced` | 81 | 0 | 0 | OK |
| `modulus_triprime_cube_not_residual` | 91 | 0 | 0 | OK |
| `modulus_prime_field` | 102 | 0 | 0 | OK |
| `modulus_N55_cube_residual_shaped` | 108 | 0 | 0 | OK |
| `modulus_N119_cube_shares` | 114 | 0 | 0 | OK |
| `modulus_N209_cube_shares` | 120 | 0 | 0 | OK |
| `modulus_N221_cube_shares` | 126 | 0 | 0 | OK |
| `modulus_N323_cube_shares` | 132 | 0 | 0 | OK |
| `modulus_prime_cube` | 138 | 0 | 0 | OK |

## SrsaOrderArrows.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `is_order_pin_y_40` | 26 | 0 | 0 | OK |
| `order_yields_residual_sRSA` | 36 | 0 | 0 | OK |
| `order_yields_residual_pin` | 58 | 0 | 0 | OK |
| `order_invert_pin_is_cube_root` | 74 | 0 | 0 | OK |
| `residual_mismatch_factors` | 85 | 0 | 0 | OK |
| `leftover_x_one_sided_pin` | 97 | 0 | 0 | OK |
| `leftover_x_mismatch_factors_pin` | 106 | 0 | 0 | OK |
| `residual_mismatch_factors_pin` | 115 | 0 | 0 | OK |
| `leftover_y_one_sided_pin` | 127 | 0 | 0 | OK |
| `order_mismatch_factors_pin` | 136 | 0 | 0 | OK |
| `leftover_77_one_sided` | 145 | 0 | 0 | OK |
| `leftover_77_mismatch_factors` | 154 | 0 | 0 | OK |
| `matching_247_not_one_sided` | 167 | 0 | 0 | OK |
| `matching_247_gcd_not_proper` | 175 | 0 | 0 | OK |
| `matching_247_two_sided_gcd_is_N` | 185 | 0 | 0 | OK |

## SrsaPeriod.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `period_base3_period` | 22 | 0 | 0 | OK |
| `period_y32_splits` | 30 | 0 | 0 | OK |
| `period_y5_minus_1_splits` | 38 | 0 | 0 | OK |
| `period_y8_minus_1_splits` | 46 | 0 | 0 | OK |
| `period_y10_minus_1_splits` | 54 | 0 | 0 | OK |
| `period_phi8_y_splits` | 62 | 0 | 0 | OK |
| `period_y2_plus_1_gcd` | 70 | 0 | 0 | OK |
| `period_phi5_y_splits` | 74 | 0 | 0 | OK |
| `period_x2_minus_1_int` | 82 | 0 | 0 | OK |
| `period_full_period_no_split` | 86 | 0 | 0 | OK |
| `period_miller_on_period2` | 91 | 0 | 0 | OK |
| `period_local_orders` | 99 | 0 | 0 | OK |
| `period_gcd_pminus1_qminus1` | 106 | 0 | 0 | OK |
| `period_public_d5_pohlig` | 110 | 0 | 0 | OK |
| `period_mismatched_local_orders` | 118 | 0 | 0 | OK |
| `period_lcm_local_orders` | 123 | 0 | 0 | OK |
| `period_v2_local_orders` | 127 | 0 | 0 | OK |
| `period_gcd_path_splits` | 132 | 0 | 0 | OK |
| `period_exp_path_leftover` | 140 | 0 | 0 | OK |
| `period_eq_order_40` | 148 | 0 | 0 | OK |
| `period_eq_not_8` | 153 | 0 | 0 | OK |
| `period_eq_not_5` | 157 | 0 | 0 | OK |
| `period_eq_y40` | 161 | 0 | 0 | OK |
| `period_eq_y20` | 165 | 0 | 0 | OK |
| `period_eq_y8` | 169 | 0 | 0 | OK |
| `period_eq_y5` | 173 | 0 | 0 | OK |
| `period_gcd_y5_splits` | 177 | 0 | 0 | OK |
| `period_gcd_y8_splits` | 185 | 0 | 0 | OK |
| `period_gcd_full_period` | 193 | 0 | 0 | OK |
| `period_after_ord_invert` | 197 | 0 | 0 | OK |
| `period_v2_ord_p` | 205 | 0 | 0 | OK |
| `period_v2_ord_q` | 209 | 0 | 0 | OK |
| `period_v2_ord_N` | 213 | 0 | 0 | OK |
| `period_v2_lam_bigger` | 218 | 0 | 0 | OK |
| `period_x5_minus_1_splits` | 223 | 0 | 0 | OK |
| `period_x8_minus_1_splits` | 231 | 0 | 0 | OK |
| `period_x10_minus_1_splits` | 239 | 0 | 0 | OK |
| `period_x16_minus_1_splits` | 247 | 0 | 0 | OK |
| `period_x4_minus_1` | 255 | 0 | 0 | OK |
| `period_x2_minus_1` | 259 | 0 | 0 | OK |
| `period_same_oracle` | 263 | 0 | 0 | OK |
| `period_ten_order_16` | 267 | 0 | 0 | OK |
| `period_ten_pow8_miller` | 272 | 0 | 0 | OK |
| `period_ten_pow8_splits` | 276 | 0 | 0 | OK |
| `period_ten_pow16` | 284 | 0 | 0 | OK |
| `period_21_order_4` | 288 | 0 | 0 | OK |
| `period_21_sq_splits` | 292 | 0 | 0 | OK |
| `period_89_order_4` | 300 | 0 | 0 | OK |
| `period_77_pminus1` | 305 | 0 | 0 | OK |
| `period_77_qminus1` | 313 | 0 | 0 | OK |
| `period_77_leftover_pohlig` | 321 | 0 | 0 | OK |
| `period_77_ord2_is_lam` | 329 | 0 | 0 | OK |
| `period_two_subgroups_split` | 334 | 0 | 0 | OK |
| `period_three_pohlig_5` | 342 | 0 | 0 | OK |
| `period_three_pohlig_16` | 350 | 0 | 0 | OK |
| `period_three_pow8_no_split` | 358 | 0 | 0 | OK |
| `period_cbrt2_cbrt36_split` | 362 | 0 | 0 | OK |
| `period_cbrt3_cbrt36_split` | 370 | 0 | 0 | OK |
| `period_cbrt3_cbrt2` | 378 | 0 | 0 | OK |
| `period_five_max_order` | 382 | 0 | 0 | OK |
| `period_five_pohlig_5` | 387 | 0 | 0 | OK |
| `period_five_pohlig_16` | 395 | 0 | 0 | OK |
| `period_ord16_to_miller` | 403 | 0 | 0 | OK |
| `period_77_51_is_2_pow7` | 407 | 0 | 0 | OK |
| `period_77_lambda` | 411 | 0 | 0 | OK |
| `period_77_two_pow3` | 415 | 0 | 0 | OK |
| `period_77_two_pow5` | 423 | 0 | 0 | OK |
| `period_187_mismatch_gcd` | 435 | 0 | 0 | OK |
| `period_77_mismatch_gcd` | 439 | 0 | 0 | OK |
| `period_247_match_gcd` | 443 | 0 | 0 | OK |
| `period_247_leftover_pair` | 449 | 0 | 0 | OK |
| `period_247_residual_leaf` | 455 | 0 | 0 | OK |
| `period_247_local_residues` | 466 | 0 | 0 | OK |
| `period_247_matching_local_orders` | 471 | 0 | 0 | OK |
| `period_247_x5_minus_1_no_split` | 478 | 0 | 0 | OK |
| `period_247_x8_minus_1_no_split` | 482 | 0 | 0 | OK |
| `period_247_x6_minus_1_is_N` | 486 | 0 | 0 | OK |
| `period_Nminus1_factors` | 497 | 0 | 0 | OK |
| `period_pohlig_ndiv_Nminus1` | 501 | 0 | 0 | OK |
| `period_ord_ndiv_Nminus1` | 508 | 0 | 0 | OK |
| `period_Nminus1_divisors_no_split` | 514 | 0 | 0 | OK |
| `period_y_Nminus1_no_annihilator` | 523 | 0 | 0 | OK |
| `period_x_Nminus1_no_membership` | 529 | 0 | 0 | OK |
| `period_Nplus1_factors` | 535 | 0 | 0 | OK |
| `period_Nplus1_divisors_no_split` | 539 | 0 | 0 | OK |
| `period_y_Nplus1_no_annihilator` | 545 | 0 | 0 | OK |
| `period_lam_v2_odd_part` | 558 | 0 | 0 | OK |
| `period_M2_no_split` | 563 | 0 | 0 | OK |
| `period_M4_no_split` | 567 | 0 | 0 | OK |
| `period_advice_odd_part_splits` | 571 | 0 | 0 | OK |
| `period_advice_v2_8_splits` | 579 | 0 | 0 | OK |
| `period_advice_v2_16_splits` | 587 | 0 | 0 | OK |
| `period_advice_ord_invert_no_proper` | 595 | 0 | 0 | OK |
| `period_advice_lam_miller` | 600 | 0 | 0 | OK |

## SrsaPrimary.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `primary_y20_miller` | 20 | 0 | 0 | OK |
| `primary_y16_five_torsion` | 25 | 0 | 0 | OK |
| `primary_y8_five_torsion` | 30 | 0 | 0 | OK |
| `primary_y5_order8` | 35 | 0 | 0 | OK |
| `primary_y10_order4` | 40 | 0 | 0 | OK |
| `primary_y4_order10` | 44 | 0 | 0 | OK |
| `primary_x_to_8_is_five_torsion` | 48 | 0 | 0 | OK |
| `primary_C8_generator` | 53 | 0 | 0 | OK |
| `primary_C8_squares` | 57 | 0 | 0 | OK |
| `primary_C5_generator` | 61 | 0 | 0 | OK |
| `primary_C5_elements` | 65 | 0 | 0 | OK |
| `primary_cube_bij_C5` | 70 | 0 | 0 | OK |
| `primary_cube_bij_C8` | 74 | 0 | 0 | OK |
| `primary_reconstruct_y` | 78 | 0 | 0 | OK |
| `primary_bezout_5_8` | 82 | 0 | 0 | OK |
| `primary_C8_order2_is_miller` | 86 | 0 | 0 | OK |
| `primary_eight_div_ord` | 90 | 0 | 0 | OK |
| `primary_five_div_ord` | 96 | 0 | 0 | OK |
| `primary_C8_is_y5` | 102 | 0 | 0 | OK |
| `primary_order4_in_C8` | 106 | 0 | 0 | OK |
| `primary_C8_pow6` | 110 | 0 | 0 | OK |
| `primary_C8_pow3` | 114 | 0 | 0 | OK |
| `primary_C8_pow5` | 118 | 0 | 0 | OK |
| `primary_C8_pow7` | 122 | 0 | 0 | OK |
| `primary_C5_pow3` | 126 | 0 | 0 | OK |
| `primary_ker_squaring_C8` | 130 | 0 | 0 | OK |
| `primary_C8_order` | 134 | 0 | 0 | OK |
| `primary_C5_order` | 139 | 0 | 0 | OK |
| `primary_lcm_primaries` | 144 | 0 | 0 | OK |
| `primary_coprime_primaries` | 148 | 0 | 0 | OK |
| `primary_cube_bij_primaries` | 152 | 0 | 0 | OK |
| `primary_x5_generates_C8` | 157 | 0 | 0 | OK |
| `primary_x8_in_C5` | 162 | 0 | 0 | OK |
| `primary_reconstruct_x` | 166 | 0 | 0 | OK |
| `primary_69_generates_C5` | 170 | 0 | 0 | OK |
| `primary_111_generates_C8` | 174 | 0 | 0 | OK |

## SrsaResidual.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `residual_phi_over_lambda` | 26 | 0 | 0 | OK |
| `residual_N_mod_8` | 30 | 0 | 0 | OK |
| `residual_bitlength_N` | 34 | 0 | 0 | OK |
| `residual_v2_N_minus_1` | 38 | 0 | 0 | OK |
| `residual_units_not_cyclic` | 43 | 0 | 0 | OK |
| `residual_mod4_shape` | 48 | 0 | 0 | OK |
| `residual_N_mod_8_two_sylow` | 53 | 0 | 0 | OK |
| `residual_y_to_lambda` | 57 | 0 | 0 | OK |
| `residual_y_to_phi` | 61 | 0 | 0 | OK |
| `residual_ord2_is_40` | 65 | 0 | 0 | OK |
| `residual_phi_is_product` | 70 | 0 | 0 | OK |
| `residual_y_to_lam_identity` | 74 | 0 | 0 | OK |
| `residual_x_in_cyc_y` | 81 | 0 | 0 | OK |
| `residual_x_generates` | 85 | 0 | 0 | OK |
| `residual_x_is_y_to_27` | 91 | 0 | 0 | OK |
| `residual_cube_root_of_1` | 96 | 0 | 0 | OK |
| `residual_unique_unit_cube` | 102 | 0 | 0 | OK |
| `residual_e_inv_mod_16` | 110 | 0 | 0 | OK |
| `residual_e_inv_mod_5` | 114 | 0 | 0 | OK |
| `residual_crt_e_inverse` | 118 | 0 | 0 | OK |
| `residual_five_divides_lambda` | 124 | 0 | 0 | OK |
| `residual_local_squares` | 129 | 0 | 0 | OK |
| `residual_qr_both_sides` | 136 | 0 | 0 | OK |
| `residual_not_in_ltwo` | 141 | 0 | 0 | OK |
| `residual_in_lthree_and_lfive` | 147 | 0 | 0 | OK |
| `residual_local_cube_mod_p` | 152 | 0 | 0 | OK |
| `residual_local_x_mod_q` | 158 | 0 | 0 | OK |
| `residual_crt_locals` | 162 | 0 | 0 | OK |
| `residual_bits_of_x` | 167 | 0 | 0 | OK |
| `residual_x_mod_8` | 171 | 0 | 0 | OK |
| `residual_x_minus_1_prime` | 175 | 0 | 0 | OK |
| `residual_x_plus_1_prime` | 179 | 0 | 0 | OK |
| `residual_sixteen_generators` | 183 | 0 | 0 | OK |
| `residual_even_k_not_generator` | 187 | 0 | 0 | OK |
| `residual_y_inv_generator` | 195 | 0 | 0 | OK |
| `residual_x_inv_generator` | 200 | 0 | 0 | OK |
| `residual_y29` | 205 | 0 | 0 | OK |
| `residual_y3_generator` | 209 | 0 | 0 | OK |
| `residual_y9_generator` | 214 | 0 | 0 | OK |
| `residual_five_divides_ord` | 219 | 0 | 0 | OK |
| `residual_eight_divides_ord` | 223 | 0 | 0 | OK |
| `residual_three_index_two` | 227 | 0 | 0 | OK |
| `residual_dl_even` | 231 | 0 | 0 | OK |
| `residual_y_in_square_subgroup` | 235 | 0 | 0 | OK |
| `residual_v2_lambda` | 239 | 0 | 0 | OK |
| `residual_ord_divides_lam` | 244 | 0 | 0 | OK |
| `residual_y_to_ord` | 248 | 0 | 0 | OK |
| `residual_phi_over_lam` | 252 | 0 | 0 | OK |
| `residual_ord_div_lam` | 256 | 0 | 0 | OK |
| `residual_e_coprime_10_16` | 260 | 0 | 0 | OK |
| `residual_five_ndiv_e` | 265 | 0 | 0 | OK |
| `residual_y_local_qr` | 270 | 0 | 0 | OK |
| `residual_bitlength_lam` | 277 | 0 | 0 | OK |
| `residual_lambda_lcm` | 281 | 0 | 0 | OK |
| `residual_y_to_e_inv` | 285 | 0 | 0 | OK |
| `residual_k1_is_y` | 295 | 0 | 0 | OK |
| `residual_k3_is_y_cube` | 299 | 0 | 0 | OK |
| `residual_even_k_shares_ord` | 304 | 0 | 0 | OK |
| `residual_crt_is_residual_x` | 309 | 0 | 0 | OK |
| `residual_ratio_five_torsion` | 314 | 0 | 0 | OK |
| `residual_ratio_y4` | 319 | 0 | 0 | OK |
| `residual_ord_5_smooth` | 324 | 0 | 0 | OK |
| `residual_index_lam_over_ord` | 328 | 0 | 0 | OK |
| `residual_x_order_40_not_20` | 332 | 0 | 0 | OK |
| `residual_three_not_in_cyc_y` | 337 | 0 | 0 | OK |
| `residual_three_full_lambda` | 341 | 0 | 0 | OK |
| `residual_y_even_power_of_3` | 345 | 0 | 0 | OK |
| `residual_product_primaries` | 349 | 0 | 0 | OK |
| `residual_cube_of_x` | 353 | 0 | 0 | OK |
| `residual_y_to_27` | 357 | 0 | 0 | OK |
| `residual_jacobi_x_vs_2` | 361 | 0 | 0 | OK |
| `residual_x_not_in_lten` | 367 | 0 | 0 | OK |
| `residual_pminus1_qminus1` | 372 | 0 | 0 | OK |
| `residual_phi_product` | 377 | 0 | 0 | OK |
| `residual_index_four` | 381 | 0 | 0 | OK |
| `residual_x_order_40` | 385 | 0 | 0 | OK |
| `residual_v2_ord_x` | 390 | 0 | 0 | OK |
| `residual_v2_lam` | 395 | 0 | 0 | OK |
| `residual_x_generates_5_sylow` | 400 | 0 | 0 | OK |
| `residual_N_mod_8_for_2` | 405 | 0 | 0 | OK |
| `residual_ten_jacobi_plus` | 409 | 0 | 0 | OK |
| `residual_ten_not_ord40` | 413 | 0 | 0 | OK |
| `residual_21_mod_8` | 418 | 0 | 0 | OK |
| `residual_ltwo_ord40` | 422 | 0 | 0 | OK |
| `residual_two_ne_y` | 426 | 0 | 0 | OK |
| `residual_four_cosets` | 430 | 0 | 0 | OK |
| `residual_jacobi_plus_count` | 440 | 0 | 0 | OK |
| `residual_phi40_generators` | 445 | 0 | 0 | OK |
| `residual_coset_10_no_split` | 453 | 0 | 0 | OK |
| `residual_coset_2_no_split` | 458 | 0 | 0 | OK |
| `residual_x16_not_1` | 464 | 0 | 0 | OK |
| `residual_x8_not_1` | 469 | 0 | 0 | OK |
| `residual_lam_bitlength` | 473 | 0 | 0 | OK |
| `residual_x_local_qr` | 477 | 0 | 0 | OK |
| `residual_161_mod_8` | 482 | 0 | 0 | OK |
| `residual_x_not_ord16` | 487 | 0 | 0 | OK |
| `residual_x_not_ord10` | 491 | 0 | 0 | OK |

## SrsaResidualGRA.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `residual_shaped_e_3` | 43 | 0 | 0 | OK |
| `residual_shaped_e_lam_minus_1` | 53 | 0 | 0 | OK |
| `not_residual_shaped_e_lam_plus_1` | 65 | 0 | 0 | OK |
| `lambda_plus_one_witness_not_residual` | 73 | 0 | 0 | OK |
| `residual_gra_const81_independent_of_y` | 81 | 0 | 0 | OK |
| `residual_gra_const81_gcd_is_1` | 86 | 0 | 0 | OK |
| `residual_gra_const81_solves_sRSA_not_residual` | 90 | 0 | 0 | OK |
| `residual_gra_const42_inverts_pin_not_8` | 103 | 0 | 0 | OK |
| `residual_gra_const42_misses_unit_2` | 115 | 0 | 0 | OK |
| `residual_shaped_forbids_rational_Pe_XQe` | 122 | 0 | 0 | OK |
| `residual_shaped_e3_leading` | 131 | 0 | 0 | OK |
| `residual_shaped_elam_leading` | 139 | 0 | 0 | OK |
| `residual_gra_Xe_minus_X_N_ndiv_linear` | 147 | 0 | 0 | OK |
| `residual_gra_X3_minus_X_N_ndiv_linear` | 158 | 0 | 0 | OK |
| `residual_gra_X7_minus_X_N_ndiv_linear` | 163 | 0 | 0 | OK |
| `residual_gra_eq_leak_factors` | 171 | 0 | 0 | OK |
| `residual_gra_inv_nonunit_factors` | 181 | 0 | 0 | OK |
| `residual_gra_nodiv_empty_is_nodiv` | 189 | 0 | 0 | OK |
| `residual_gra_identity_tape_is_y` | 193 | 0 | 0 | OK |
| `residual_gra_identity_tape_not_cube` | 197 | 0 | 0 | OK |
| `residual_gra_nodiv_integer_identity_forbidden` | 201 | 0 | 0 | OK |
| `residual_gra_nodiv_cube_identity_forbidden` | 213 | 0 | 0 | OK |
| `residual_gra_mul_denotes_square` | 224 | 0 | 0 | OK |
| `residual_identity_is_low_degree` | 243 | 0 | 0 | OK |
| `residual_X3_eval` | 249 | 0 | 0 | OK |
| `cube_minus_id_factor` | 253 | 0 | 0 | OK |
| `prime_divides_cube_minus_id` | 257 | 0 | 0 | OK |
| `residual_X3_roots_mod_prime` | 273 | 0 | 0 | OK |
| `residual_X3_roots_mod_11` | 306 | 0 | 0 | OK |
| `residual_X3_unit_2_not_root_mod_11` | 316 | 0 | 0 | OK |
| `residual_X3_unit_2_not_root_mod_17` | 326 | 0 | 0 | OK |
| `residual_X3_roots_mod_17` | 336 | 0 | 0 | OK |
| `residual_const_Pe_minus_X_nth1` | 346 | 0 | 0 | OK |
| `residual_const_N_ndiv_linear` | 350 | 0 | 0 | OK |
| `residual_nodiv_identity_denotes_X` | 356 | 0 | 0 | OK |
| `residual_identity_cube_minus_y` | 360 | 0 | 0 | OK |
| `residual_nodiv_const_is_nodiv` | 370 | 0 | 0 | OK |
| `residual_nodiv_const_denotes` | 374 | 0 | 0 | OK |
| `residual_low_degree_identity_not_all_Fp_units` | 385 | 0 | 0 | OK |
| `pin_Fp_star_length` | 406 | 0 | 0 | OK |
| `forall_pin_Fp_star` | 409 | 0 | 0 | OK |
| `pin_Fp_star_coprime` | 419 | 0 | 0 | OK |
| `pin_Fp_star_distinct_mod_11` | 432 | 0 | 0 | OK |
| `residual_low_degree_units_divides_11` | 438 | 0 | 0 | OK |
| `residual_nodiv_low_degree_units_divides_11` | 452 | 0 | 0 | OK |
| `residual_identity_nth1_ndiv_11` | 470 | 0 | 0 | OK |
| `residual_identity_cannot_vanish_on_Fp_star` | 474 | 0 | 0 | OK |
| `residual_const_Pe_degree` | 487 | 0 | 0 | OK |
| `residual_const_cannot_vanish_on_Fp_star` | 491 | 0 | 0 | OK |
| `pin_Fq_star_length` | 516 | 0 | 0 | OK |
| `forall_pin_Fq_star` | 519 | 0 | 0 | OK |
| `pin_Fq_star_distinct_mod_17` | 529 | 0 | 0 | OK |
| `pin_1_16_coprime_N` | 535 | 0 | 0 | OK |
| `pin_crt_lift_11_spec` | 550 | 0 | 0 | OK |
| `pin_N_divides_11` | 556 | 0 | 0 | OK |
| `pin_N_divides_17` | 561 | 0 | 0 | OK |
| `pin_11_17_divides_N` | 566 | 0 | 0 | OK |
| `residual_ZN_units_vanish_at_Fq` | 575 | 0 | 0 | OK |
| `residual_low_degree_ZN_units_divides_17` | 597 | 0 | 0 | OK |
| `residual_low_degree_ZN_units_divides_N` | 612 | 0 | 0 | OK |
| `residual_nodiv_low_degree_ZN_units_divides_N` | 626 | 0 | 0 | OK |
| `residual_identity_cannot_vanish_on_ZN_units` | 644 | 0 | 0 | OK |
| `residual_const_cannot_vanish_on_ZN_units` | 659 | 0 | 0 | OK |
| `residual_nodiv_bound_le3_Q_lt10` | 684 | 0 | 0 | OK |
| `residual_nodiv_short_ZN_units_divides_N` | 699 | 0 | 0 | OK |
| `residual_identity_bound_is_1` | 715 | 0 | 0 | OK |
| `residual_square_bound_is_2` | 719 | 0 | 0 | OK |
| `residual_x3_bound_is_3` | 723 | 0 | 0 | OK |
| `residual_two_squarings_bound_is_4` | 727 | 0 | 0 | OK |
| `residual_two_squarings_outside_window` | 731 | 0 | 0 | OK |
| `residual_trapdoor_deg27_outside_window` | 735 | 0 | 0 | OK |
| `residual_square_denotes_X2` | 751 | 0 | 0 | OK |
| `residual_square_degree_eq_bound` | 756 | 0 | 0 | OK |
| `residual_square_eval` | 766 | 0 | 0 | OK |
| `residual_square_Q_degree_is_6` | 775 | 0 | 0 | OK |
| `residual_square_Q_nth1` | 783 | 0 | 0 | OK |
| `residual_square_cannot_vanish_on_ZN_units` | 791 | 0 | 0 | OK |
| `residual_square_unit_2_not_root` | 811 | 0 | 0 | OK |
| `residual_cube_is_nodiv` | 821 | 0 | 0 | OK |
| `residual_cube_denotes_X3` | 825 | 0 | 0 | OK |
| `residual_cube_degree_eq_bound` | 830 | 0 | 0 | OK |
| `residual_cube_eval` | 842 | 0 | 0 | OK |
| `residual_cube_Q_degree_is_9` | 853 | 0 | 0 | OK |
| `residual_cube_Q_nth1` | 861 | 0 | 0 | OK |
| `residual_cube_cannot_vanish_on_ZN_units` | 869 | 0 | 0 | OK |
| `residual_cube_unit_2_not_root` | 893 | 0 | 0 | OK |
| `residual_trapdoor_inverts_pin` | 905 | 0 | 0 | OK |
| `residual_trapdoor_not_a_low_degree_identity` | 909 | 0 | 0 | OK |

## SrsaRootPoly.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `cong_1_mod_p_0_mod_q_gcd` | 59 | 0 | 0 | OK |
| `crt_binomial_eval` | 93 | 0 | 0 | OK |
| `crt_binomial_mod_p` | 106 | 0 | 0 | OK |
| `crt_binomial_mod_q` | 127 | 0 | 0 | OK |
| `local_eth_root` | 148 | 0 | 0 | OK |
| `crt_binomial_inverts_units` | 176 | 0 | 0 | OK |
| `pin_root_ca_mod` | 219 | 0 | 0 | OK |
| `pin_root_cb_mod` | 223 | 0 | 0 | OK |
| `pin_inv3_local` | 227 | 0 | 0 | OK |
| `pin_root_ca_splits` | 232 | 0 | 0 | OK |
| `pin_root_cb_splits` | 245 | 0 | 0 | OK |
| `pin_crt_binomial_inverts_units` | 258 | 0 | 0 | OK |
| `pin_crt_binomial_eval_unit` | 281 | 0 | 0 | OK |
| `pin_ed_minus_1_divides_lam` | 294 | 0 | 0 | OK |
| `pin_powm_ed` | 303 | 0 | 0 | OK |
| `pin_unique_unit_eth_root` | 319 | 0 | 0 | OK |
| `pin_crt_binomial_at_y` | 331 | 0 | 0 | OK |
| `pin_crt_binomial_residual` | 343 | 0 | 0 | OK |
| `pin_crt_binomial_degree` | 350 | 0 | 0 | OK |
| `pin_crt_binomial_outside_window` | 354 | 0 | 0 | OK |
| `pin_crt_binomial_coeff_da` | 359 | 0 | 0 | OK |
| `pin_crt_binomial_coeff_db` | 363 | 0 | 0 | OK |
| `pin_trapdoor_monomial_eval` | 371 | 0 | 0 | OK |
| `pin_trapdoor_ed_inv` | 379 | 0 | 0 | OK |
| `pin_powm_de` | 383 | 0 | 0 | OK |
| `pin_trapdoor_monomial_inverts_units` | 400 | 0 | 0 | OK |
| `pin_trapdoor_monomial_at_y` | 408 | 0 | 0 | OK |
| `pin_trapdoor_monomial_degree` | 412 | 0 | 0 | OK |
| `pin_trapdoor_monomial_leading` | 416 | 0 | 0 | OK |
| `pin_trapdoor_degree_is_d` | 426 | 0 | 0 | OK |
| `pin_trapdoor_monomial_outside_window` | 433 | 0 | 0 | OK |
| `pin_root_polys_agree_on_units` | 440 | 0 | 0 | OK |
| `root_poly_eval_coprime` | 460 | 0 | 0 | OK |
| `all_units_root_poly_is_trapdoor_map` | 474 | 0 | 0 | OK |
| `all_units_root_poly_eval_g` | 495 | 0 | 0 | OK |
| `pin_trapdoor_monomial_is_trapdoor_map` | 505 | 0 | 0 | OK |
| `pin_crt_binomial_neq_monomial` | 515 | 0 | 0 | OK |
| `pin_crt_binomial_inverts_2` | 525 | 0 | 0 | OK |
| `unique_eth_root_mod_prime` | 548 | 0 | 0 | OK |
| `pin_Fq_units_of_N_length` | 572 | 0 | 0 | OK |
| `pairwise_distinct_mod_filter` | 576 | 0 | 0 | OK |
| `pin_Fq_units_of_N_distinct` | 594 | 0 | 0 | OK |
| `pin_Fq_units_of_N_coprime` | 601 | 0 | 0 | OK |
| `pin_inv3_q_lt_window` | 618 | 0 | 0 | OK |
| `nth_poly_sub` | 622 | 0 | 0 | OK |
| `poly_degree_sub_le` | 630 | 0 | 0 | OK |
| `mod_product_r` | 641 | 0 | 0 | OK |
| `mod_product_l` | 653 | 0 | 0 | OK |
| `short_root_local_mod_q` | 659 | 0 | 0 | OK |
| `short_root_diff_vanishes` | 699 | 0 | 0 | OK |
| `short_root_q_divides_diff` | 721 | 0 | 0 | OK |
| `poly_eval_all_div` | 740 | 0 | 0 | OK |
| `poly_eval_single_support` | 754 | 0 | 0 | OK |
| `pin_two_pow_dbe_neq_2` | 786 | 0 | 0 | OK |
| `gcd_q_not_p` | 790 | 0 | 0 | OK |
| `powm_div_cong` | 817 | 0 | 0 | OK |
| `finite_support_cases` | 831 | 0 | 0 | OK |
| `short_root_poly_some_coeff_splits` | 855 | 0 | 0 | OK |
| `pin_crt_root_poly_is_short` | 939 | 0 | 0 | OK |
| `pin_crt_root_poly_short_splits` | 943 | 0 | 0 | OK |
| `no_root_poly_deg_lt_dq` | 955 | 0 | 0 | OK |
| `pin_Xn_dp_does_not_invert_all_units` | 972 | 0 | 0 | OK |
| `nodiv_gra_short_dq_splits` | 983 | 0 | 0 | OK |
| `nodiv_identity_bound_lt_dq` | 1005 | 0 | 0 | OK |
| `nodiv_square_bound_lt_dq` | 1010 | 0 | 0 | OK |
| `trapdoor_monomial_inverts_all_units` | 1026 | 0 | 0 | OK |
| `monomial_all_units_invert_is_trapdoor` | 1054 | 0 | 0 | OK |
| `pin_d_monomial_is_trapdoor` | 1095 | 0 | 0 | OK |
| `pin_dp_monomial_not_trapdoor` | 1099 | 0 | 0 | OK |
| `pin_dq_monomial_not_trapdoor` | 1103 | 0 | 0 | OK |
| `pin_d_plus_lam_is_trapdoor` | 1107 | 0 | 0 | OK |
| `pin_d_plus_2lam_is_trapdoor` | 1111 | 0 | 0 | OK |
| `pin_trapdoor_k_M_pos` | 1115 | 0 | 0 | OK |
| `monomial_all_units_invert_miller` | 1128 | 0 | 0 | OK |
| `pin_miller_from_d_plus_lam` | 1159 | 0 | 0 | OK |
| `pin_base2_height_p_at_35` | 1181 | 0 | 0 | OK |
| `pin_base2_height_q_at_35` | 1189 | 0 | 0 | OK |
| `pin_odd_part_d_plus_2lam` | 1199 | 0 | 0 | OK |
| `pin_miller_from_d_plus_2lam` | 1203 | 0 | 0 | OK |
| `pin_d_mod_pminus1` | 1227 | 0 | 0 | OK |
| `pin_d_mod_qminus1` | 1231 | 0 | 0 | OK |
| `pin_inv3_p_is_crt_dp` | 1235 | 0 | 0 | OK |
| `pin_inv3_q_is_crt_dq` | 1239 | 0 | 0 | OK |
| `pin_local_inverses_recover_d` | 1243 | 0 | 0 | OK |
| `pin_local_inv_unique_p` | 1261 | 0 | 0 | OK |
| `pin_local_inv_unique_q` | 1273 | 0 | 0 | OK |
| `pin_mid_root_poly_degree` | 1294 | 0 | 0 | OK |
| `pin_mid_root_poly_in_window` | 1298 | 0 | 0 | OK |
| `pin_mid_root_poly_inverts_units` | 1302 | 0 | 0 | OK |
| `pin_mid_root_poly_splits` | 1316 | 0 | 0 | OK |

## SrsaWriteE.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `emap_phi_y_even` | 21 | 0 | 0 | OK |
| `emap_hamming_even` | 26 | 0 | 0 | OK |
| `emap_lsb_y_even` | 31 | 0 | 0 | OK |
| `emap_e25_shares_lambda` | 35 | 0 | 0 | OK |
| `emap_lambda_y_even` | 40 | 0 | 0 | OK |
| `emap_bitlength_even` | 45 | 0 | 0 | OK |
| `emap_tau_leftover_e9` | 50 | 0 | 0 | OK |
| `emap_sigma_leftover` | 54 | 0 | 0 | OK |
| `emap_rad_even` | 58 | 0 | 0 | OK |
| `emap_omega_even` | 63 | 0 | 0 | OK |
| `emap_Omega_even` | 67 | 0 | 0 | OK |
| `emap_lpf_hits_cube` | 71 | 0 | 0 | OK |
| `emap_y_plus_1_is_nextprime` | 75 | 0 | 0 | OK |
| `emap_odd_part_e9` | 81 | 0 | 0 | OK |
| `emap_odd_hamming_shares` | 86 | 0 | 0 | OK |
| `emap_gcd_yminus1_Nminus1` | 91 | 0 | 0 | OK |
| `emap_phi3_y_leftover_shaped` | 95 | 0 | 0 | OK |
| `emap_v2_yminus1` | 105 | 0 | 0 | OK |
| `emap_mersenne_leftover` | 111 | 0 | 0 | OK |
| `emap_N_mod_y_hits_e7` | 115 | 0 | 0 | OK |
| `emap_fermatish_leftover` | 119 | 0 | 0 | OK |
| `emap_smooth_even` | 123 | 0 | 0 | OK |
| `emap_e_eq_N` | 128 | 0 | 0 | OK |
| `emap_e_eq_Nminus2` | 133 | 0 | 0 | OK |
| `emap_e_y_minus_1_shares` | 138 | 0 | 0 | OK |
| `emap_e_two_y_plus_1` | 143 | 0 | 0 | OK |
| `emap_e_two_y_minus_1` | 147 | 0 | 0 | OK |
| `emap_prevprime_e31` | 151 | 0 | 0 | OK |
| `emap_dedekind_psi_even` | 155 | 0 | 0 | OK |
| `emap_ord_y_even` | 160 | 0 | 0 | OK |
| `emap_phi_N_even` | 165 | 0 | 0 | OK |
| `emap_aliquot_shares` | 169 | 0 | 0 | OK |
| `emap_e17_leftover` | 174 | 0 | 0 | OK |
| `emap_e_N_plus_1_even` | 178 | 0 | 0 | OK |
| `emap_e_N_minus_1_even` | 182 | 0 | 0 | OK |
| `emap_e_lam_minus_1` | 186 | 0 | 0 | OK |
| `emap_phi_y_plus_1` | 190 | 0 | 0 | OK |
| `emap_digit_sum_e9` | 194 | 0 | 0 | OK |
| `emap_repunit_111` | 198 | 0 | 0 | OK |
| `emap_primorial_even` | 202 | 0 | 0 | OK |
| `emap_fermat_5_shares` | 207 | 0 | 0 | OK |
| `emap_collatz_e21` | 212 | 0 | 0 | OK |
| `emap_squarefree_core_e9` | 216 | 0 | 0 | OK |
| `emap_e47_second_leftover` | 221 | 0 | 0 | OK |
| `emap_e23_ninth` | 225 | 0 | 0 | OK |
| `emap_e19_leftover` | 229 | 0 | 0 | OK |
| `emap_e_eq_x` | 233 | 0 | 0 | OK |
| `emap_e_N_minus_lam` | 237 | 0 | 0 | OK |
| `emap_e_nextprime_N` | 241 | 0 | 0 | OK |
| `emap_prevprime_even_peel` | 246 | 0 | 0 | OK |
| `emap_e_prime` | 250 | 0 | 0 | OK |
| `emap_prime_e7` | 255 | 0 | 0 | OK |

## SrsaWriteX.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `xmap_odd_monomial` | 27 | 0 | 0 | OK |
| `xmap_associate` | 31 | 0 | 0 | OK |
| `xmap_midpoint` | 36 | 0 | 0 | OK |
| `xmap_encrypt_as_decrypt` | 45 | 0 | 0 | OK |
| `xmap_not_coppersmith_small` | 50 | 0 | 0 | OK |
| `xmap_odd_monomial_y5` | 55 | 0 | 0 | OK |
| `xmap_y_to_the_y` | 61 | 0 | 0 | OK |
| `xmap_y_to_the_N` | 66 | 0 | 0 | OK |
| `xmap_y_to_Nminus1` | 70 | 0 | 0 | OK |
| `xmap_y_to_Nplus1` | 75 | 0 | 0 | OK |
| `xmap_floor_sqrt_y` | 80 | 0 | 0 | OK |
| `xmap_half_y` | 85 | 0 | 0 | OK |
| `xmap_bitrev_36_is_9` | 91 | 0 | 0 | OK |
| `xmap_triangular` | 95 | 0 | 0 | OK |
| `xmap_nextprime_as_x` | 100 | 0 | 0 | OK |
| `xmap_fibonacci_y` | 105 | 0 | 0 | OK |
| `xmap_exp_base2` | 109 | 0 | 0 | OK |
| `xmap_exp_base3` | 113 | 0 | 0 | OK |
| `xmap_phi3_of_y` | 118 | 0 | 0 | OK |
| `xmap_inv_then_cube` | 123 | 0 | 0 | OK |
| `xmap_cube_then_inv` | 127 | 0 | 0 | OK |
| `xmap_hybrid_crt` | 131 | 0 | 0 | OK |
| `xmap_mismatched_crt_splits` | 138 | 0 | 0 | OK |
| `xmap_integer_jnt` | 146 | 0 | 0 | OK |
| `xmap_y2_plus_1` | 151 | 0 | 0 | OK |
| `xmap_x_eq_Nminus1` | 156 | 0 | 0 | OK |
| `xmap_floor_sqrt_N` | 161 | 0 | 0 | OK |
| `xmap_phi3_of_N` | 165 | 0 | 0 | OK |
| `xmap_y7_onesided` | 169 | 0 | 0 | OK |
| `xmap_y9_cubes_to_root` | 173 | 0 | 0 | OK |
| `xmap_y11_onesided` | 180 | 0 | 0 | OK |
| `xmap_floor_y_div_3` | 184 | 0 | 0 | OK |
| `xmap_floor_N_div_y` | 190 | 0 | 0 | OK |
| `xmap_three_y_onesided` | 196 | 0 | 0 | OK |
| `xmap_y_minus_1` | 200 | 0 | 0 | OK |
| `xmap_y_plus_1_as_x` | 205 | 0 | 0 | OK |
| `xmap_two_y_plus_1` | 211 | 0 | 0 | OK |
| `xmap_y2_minus_1` | 217 | 0 | 0 | OK |
| `xmap_gray_code` | 223 | 0 | 0 | OK |
| `xmap_nibble_swap_nonunit` | 229 | 0 | 0 | OK |
| `xmap_popcount_as_x` | 237 | 0 | 0 | OK |
| `xmap_catalan_C5` | 243 | 0 | 0 | OK |
| `xmap_lucas_L8` | 253 | 0 | 0 | OK |
| `xmap_floor_y_three_halves` | 258 | 0 | 0 | OK |
| `xmap_shift_left_2_onesided` | 264 | 0 | 0 | OK |
| `xmap_y_mod_16` | 268 | 0 | 0 | OK |
| `xmap_eightbit_palindrome` | 274 | 0 | 0 | OK |
| `xmap_partition_p10` | 279 | 0 | 0 | OK |
| `xmap_catalan_C6_nonunit` | 287 | 0 | 0 | OK |
| `xmap_y_inv_sq` | 295 | 0 | 0 | OK |
| `xmap_x_eq_phi` | 301 | 0 | 0 | OK |
| `xmap_x_bitlength_N` | 306 | 0 | 0 | OK |
| `xmap_nextprime_mod_N` | 311 | 0 | 0 | OK |
| `xmap_identity_not_root` | 317 | 0 | 0 | OK |
| `xmap_y35_onesided` | 322 | 0 | 0 | OK |
| `xmap_inv_lam_minus_1` | 330 | 0 | 0 | OK |
| `xmap_pkcs_pad` | 334 | 0 | 0 | OK |
| `xmap_sqrt_then_n_nplus1` | 340 | 0 | 0 | OK |
| `xmap_integer_sqrt_unit` | 352 | 0 | 0 | OK |
| `xmap_binary_encrypt` | 356 | 0 | 0 | OK |
| `xmap_mont_form` | 362 | 0 | 0 | OK |

## StrongPrimes.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `two_not_safe` | 31 | 0 | 0 | OK |
| `safe_prime_pminus1` | 38 | 0 | 0 | OK |
| `safe_prime_resists_p1` | 60 | 0 | 0 | OK |
| `large_factor_blocks_smooth_claim` | 78 | 0 | 0 | OK |
| `safe_prime_blocks_smooth_claim` | 87 | 0 | 0 | OK |
| `safe_pair_lambda` | 98 | 0 | 0 | OK |
| `strong_prime_resists_both` | 131 | 0 | 0 | OK |
| `prime_5` | 142 | 0 | 0 | OK |
| `five_is_safe` | 150 | 0 | 0 | OK |
| `five_resists_B1` | 156 | 0 | 0 | OK |

## StrongRSAPeel.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `srsa_unit_y_forces_unit_x` | 31 | 0 | 0 | OK |
| `srsa_gcd_proper_is_factor` | 44 | 0 | 0 | OK |
| `srsa_nonunit_x_pin` | 58 | 0 | 0 | OK |
| `srsa_jacobi_minus1_forces_odd_e` | 70 | 0 | 0 | OK |
| `srsa_jacobi_two_is_minus1` | 89 | 0 | 0 | OK |
| `srsa_lambda_type_on_jacobi_minus1` | 93 | 0 | 0 | OK |
| `srsa_even_e_is_square_root` | 103 | 0 | 0 | OK |
| `srsa_even_e_pin` | 115 | 0 | 0 | OK |
| `srsa_associate_neg6_does_not_split` | 119 | 0 | 0 | OK |
| `srsa_mixed_root_of_36_factors` | 124 | 0 | 0 | OK |
| `srsa_even_e_nonassociate_factors` | 134 | 0 | 0 | OK |
| `srsa_x_eq_y_annihilates` | 151 | 0 | 0 | OK |
| `srsa_lambda_type_annihilator_pin` | 181 | 0 | 0 | OK |
| `srsa_lambda_type_miller_splits` | 191 | 0 | 0 | OK |
| `srsa_lambda_type_miller_factors` | 201 | 0 | 0 | OK |
| `prime_7` | 212 | 0 | 0 | OK |
| `srsa_safeprime_lambda_30` | 220 | 0 | 0 | OK |
| `srsa_safeprime_lambda_type` | 224 | 0 | 0 | OK |
| `srsa_safeprime_g0_square` | 229 | 0 | 0 | OK |
| `srsa_safeprime_miller_gcd` | 233 | 0 | 0 | OK |
| `srsa_safeprime_miller_factors` | 237 | 0 | 0 | OK |
| `srsa_residual_pin` | 253 | 0 | 0 | OK |
| `srsa_residual_pin187` | 264 | 0 | 0 | OK |
| `srsa_fixed_e_rerand` | 291 | 0 | 0 | OK |
| `srsa_fixed_e_rerand_pin` | 304 | 0 | 0 | OK |
| `srsa_poly_e_not_rerand_invariant` | 311 | 0 | 0 | OK |
| `srsa_related_y_square` | 317 | 0 | 0 | OK |
| `srsa_related_pin` | 333 | 0 | 0 | OK |
| `srsa_sagm_handle_unit` | 339 | 0 | 0 | OK |
| `srsa_sagm_lambda_type_peel` | 344 | 0 | 0 | OK |
| `srsa_sagm_product_reused` | 349 | 0 | 0 | OK |
| `srsa_sqrt1_120_splits` | 359 | 0 | 0 | OK |
| `srsa_minus1_no_split` | 365 | 0 | 0 | OK |
| `srsa_120_plus_1` | 370 | 0 | 0 | OK |
| `srsa_miller_66` | 374 | 0 | 0 | OK |
| `srsa_four_sqrt1` | 378 | 0 | 0 | OK |

## Succinct.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `poly_eval_app` | 45 | 0 | 0 | OK |
| `nn_app` | 62 | 0 | 0 | OK |
| `nn_firstn` | 71 | 0 | 0 | OK |
| `nn_skipn` | 83 | 0 | 0 | OK |
| `nn_map_mul_nonneg` | 95 | 0 | 0 | OK |
| `nn_poly_add` | 104 | 0 | 0 | OK |
| `nn_succ_fold` | 116 | 0 | 0 | OK |
| `poly_eval_succ_fold` | 125 | 0 | 0 | OK |
| `succ_round_pack_length` | 200 | 0 | 0 | OK |
| `succ_prove_cons_length` | 206 | 0 | 0 | OK |
| `succ_prove_rounds_log` | 213 | 0 | 0 | OK |
| `succ_proof_len_is_log` | 264 | 0 | 0 | OK |
| `succ_proof_len_n4` | 275 | 0 | 0 | OK |
| `succ_proof_len_n16` | 285 | 0 | 0 | OK |
| `succ_proof_len_bound_pin` | 295 | 0 | 0 | OK |
| `succ_pin_n2_accepts` | 305 | 0 | 0 | OK |
| `succ_pin_n2_rejects_group_mul` | 317 | 0 | 0 | OK |
| `succ_pin_n2_sum_neq_prod` | 327 | 0 | 0 | OK |
| `succ_pin_qap` | 334 | 0 | 0 | OK |

## Takagi.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `fermat_minus_one_divides` | 26 | 0 | 0 | OK |
| `euler_p2` | 41 | 0 | 0 | OK |
| `sqrt1_mod_p2_is_pm1` | 66 | 0 | 0 | OK |
| `carmichael_takagi` | 127 | 0 | 0 | OK |
| `lambda_divides_phi_takagi` | 177 | 0 | 0 | OK |
| `lambda_p2_divides_lambda_takagi` | 186 | 0 | 0 | OK |
| `takagi_ed_is_id_p2` | 191 | 0 | 0 | OK |
| `takagi_mixed_sqrt1_splits` | 237 | 0 | 0 | OK |

## ThresholdRSA.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `additive_share_combines` | 21 | 0 | 0 | OK |
| `additive_three_shares` | 33 | 0 | 0 | OK |
| `mediated_rsa_is_two_shares` | 47 | 0 | 0 | OK |
| `share_refresh_by_zero` | 61 | 0 | 0 | OK |
| `shamir_two_of_three` | 82 | 0 | 0 | OK |
| `powm_ed_is_base` | 105 | 0 | 0 | OK |
| `shoup_extract_from_kd` | 145 | 0 | 0 | OK |

## TimeLock.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `timelock_trapdoor_reduces_exp` | 17 | 0 | 0 | OK |

## Torus.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `lucasU_0` | 33 | 0 | 0 | OK |
| `lucasU_1` | 36 | 0 | 0 | OK |
| `lp_of_nat_0` | 49 | 0 | 0 | OK |
| `lp_inv_inv` | 52 | 0 | 0 | OK |
| `torus_order_divides_product` | 59 | 0 | 0 | OK |
| `pq_plus_one_is_not_torus_order` | 66 | 0 | 0 | OK |
| `N_plus_one_misses_p_plus_q` | 71 | 0 | 0 | OK |
| `lucas_eval_annihilator_is_none` | 94 | 0 | 0 | OK |
| `lucas_eval_annihilator_is_not_N_plus_one` | 98 | 0 | 0 | OK |
| `lucas_eval_id_is_V0` | 102 | 0 | 0 | OK |
| `typeB_on_torus_is_williams` | 106 | 0 | 0 | OK |
| `williams_onesided_gcd` | 114 | 0 | 0 | OK |
| `williams_onesided_not_full_N` | 129 | 0 | 0 | OK |
| `fermat_gives_torus_order` | 151 | 0 | 0 | OK |
| `fermat_leak_is_torus_period` | 161 | 0 | 0 | OK |
| `constructible_torus_is_V_eq_2` | 174 | 0 | 0 | OK |

## TranscriptOracle.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `powm_mul_l_mod` | 20 | 0 | 0 | OK |
| `mod_mod_factor` | 30 | 0 | 0 | OK |
| `powm_mod_factor` | 43 | 0 | 0 | OK |
| `powm_exp_mod_factor` | 54 | 0 | 0 | OK |
| `even_pow_neg1_is_one` | 67 | 0 | 0 | OK |
| `odd_pow_neg1` | 83 | 0 | 0 | OK |
| `euler_odd_power` | 110 | 0 | 0 | OK |
| `rsa_cipher_euler_eq_message` | 132 | 0 | 0 | OK |
| `rsa_cipher_euler_eq_message_q` | 151 | 0 | 0 | OK |
| `sign_homomorphism` | 173 | 0 | 0 | OK |
| `sign_of_one` | 185 | 0 | 0 | OK |
| `sign_inverse` | 194 | 0 | 0 | OK |
| `decrypt_blinding` | 212 | 0 | 0 | OK |
| `decrypt_double_is_double` | 234 | 0 | 0 | OK |
| `lsb_double_decides_half` | 254 | 0 | 0 | OK |
| `lsb_double_decides_half_ge` | 284 | 0 | 0 | OK |
| `pow2_nat_pos` | 301 | 0 | 0 | OK |
| `pow2_nat_succ` | 304 | 0 | 0 | OK |
| `recover_interval_correct` | 321 | 0 | 0 | OK |
| `recover_from_half_tests` | 336 | 0 | 0 | OK |
| `common_modulus_identity` | 344 | 0 | 0 | OK |
| `common_modulus_recovers` | 364 | 0 | 0 | OK |
| `coprime_to_nonneg_bezout` | 385 | 0 | 0 | OK |
| `bellcore_factors` | 415 | 0 | 0 | OK |
| `bellcore_is_factor` | 445 | 0 | 0 | OK |
| `one_sided_congruence_factors` | 466 | 0 | 0 | OK |
| `prime_5` | 499 | 0 | 0 | OK |
| `williams_N_mod8` | 507 | 0 | 0 | OK |
| `non_williams_N_mod8_5` | 517 | 0 | 0 | OK |
| `williams_two_is_shape` | 521 | 0 | 0 | OK |
| `non_williams_two_chars` | 535 | 0 | 0 | OK |
| `sign_neg1_odd` | 547 | 0 | 0 | OK |
| `odd_exp_preserves_minus1` | 559 | 0 | 0 | OK |
| `rsa_inverter_recovers_message` | 591 | 0 | 0 | OK |
| `sign_hom_3` | 623 | 0 | 0 | OK |
| `sign_of_msg_product_one` | 639 | 0 | 0 | OK |
| `sign_weighted_commute` | 656 | 0 | 0 | OK |
| `sign_weighted_product` | 670 | 0 | 0 | OK |
| `euler_sign_of_pm1` | 697 | 0 | 0 | OK |
| `euler_sign_sq` | 714 | 0 | 0 | OK |
| `other_legendre_from_product` | 725 | 0 | 0 | OK |
| `cipher_jacobi_eq_message` | 738 | 0 | 0 | OK |
| `onesided_plain_one_factors` | 773 | 0 | 0 | OK |
| `ctor_slot_mod_r_need_not_factor` | 788 | 0 | 0 | OK |
| `cube_below_N` | 808 | 0 | 0 | OK |
| `e3_small_cube_verifies` | 823 | 0 | 0 | OK |
| `bleiche_wrap_interval` | 838 | 0 | 0 | OK |
| `pkcs15_prefix_is_type2` | 864 | 0 | 0 | OK |
| `manger_is_stricter_than_type2` | 874 | 0 | 0 | OK |

## TwoPartyPair.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `two_party_root_is_eth` | 27 | 0 | 0 | OK |
| `two_party_root_is_dstar_power` | 42 | 0 | 0 | OK |
| `two_party_root_hom` | 57 | 0 | 0 | OK |
| `two_party_next_forces_dstar` | 91 | 0 | 0 | OK |

## TwoPrimary.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `pow2n_pos` | 30 | 0 | 0 | OK |
| `pow2n_succ` | 33 | 0 | 0 | OK |
| `gcd2_of_odd` | 41 | 0 | 0 | OK |
| `val2_of_odd` | 53 | 0 | 0 | OK |
| `val2_two_times_odd` | 67 | 0 | 0 | OK |
| `odd_prime_val2_ge1` | 91 | 0 | 0 | OK |
| `blum_val2_is_1` | 113 | 0 | 0 | OK |
| `mod4_1_val2_ge2` | 125 | 0 | 0 | OK |
| `rw_pair_val2_11` | 151 | 0 | 0 | OK |
| `crt2_mod` | 165 | 0 | 0 | OK |
| `square_mod_one_of_pm1` | 182 | 0 | 0 | OK |
| `powm_square_one_of_pm1` | 199 | 0 | 0 | OK |
| `four_sqrt1` | 208 | 0 | 0 | OK |
| `mod_mod_of_factor` | 252 | 0 | 0 | OK |
| `mixed_pm_not_one` | 259 | 0 | 0 | OK |
| `mixed_pm_not_minus1` | 275 | 0 | 0 | OK |
| `mixed_sqrt1_splits` | 297 | 0 | 0 | OK |
| `two_height_unique` | 327 | 0 | 0 | OK |
| `height_mismatch_splits` | 340 | 0 | 0 | OK |
| `rw_is_blum_2adic` | 375 | 0 | 0 | OK |
| `unbalanced_not_matched` | 379 | 0 | 0 | OK |
| `lambda_val2_is_max` | 389 | 0 | 0 | OK |
| `mod8_3_val2_is_1` | 395 | 0 | 0 | OK |
| `mod8_7_val2_is_1` | 402 | 0 | 0 | OK |
| `mod8_5_val2_is_2` | 410 | 0 | 0 | OK |
| `mod8_1_val2_ge3` | 427 | 0 | 0 | OK |
| `val2_ge_of_mod_pow2` | 450 | 0 | 0 | OK |
| `dist_forced_2adic_both_deep` | 482 | 0 | 0 | OK |
| `matched_deep_is_both_deep` | 495 | 0 | 0 | OK |
| `find_least_spec` | 517 | 0 | 0 | OK |
| `find_least_le` | 547 | 0 | 0 | OK |
| `find_least_min` | 551 | 0 | 0 | OK |
| `find_least_hits` | 556 | 0 | 0 | OK |
| `two_height_exists` | 570 | 0 | 0 | OK |
| `two_height_exists_fermat` | 593 | 0 | 0 | OK |
| `two_height_scale_forward` | 626 | 0 | 0 | OK |
| `two_height_of_odd_multiple` | 643 | 0 | 0 | OK |
| `unit_pow_pm1` | 677 | 0 | 0 | OK |
| `min_from_spec` | 691 | 0 | 0 | OK |
| `unit_has_min_order` | 720 | 0 | 0 | OK |
| `powm_order_divides` | 759 | 0 | 0 | OK |
| `odd_part_of_divisor` | 789 | 0 | 0 | OK |
| `pow2_divides_pow2` | 802 | 0 | 0 | OK |
| `pow2_cancel_odd` | 834 | 0 | 0 | OK |
| `cyclic_units_holds` | 848 | 0 | 0 | OK |
| `cyclic_same_t` | 888 | 0 | 0 | OK |

## TwoSylow.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `powm_2_mod_prime_pm1` | 22 | 0 | 0 | OK |
| `sqrt1_is_crt_pm1` | 29 | 0 | 0 | OK |
| `four_divides_lambda_iff_deep` | 53 | 0 | 0 | OK |
| `no_order_4_when_lambda_val2_1` | 87 | 0 | 0 | OK |
| `blum_has_no_order_4` | 103 | 0 | 0 | OK |
| `sqrt1_pm_translates_square` | 121 | 0 | 0 | OK |

## UnknownOrder.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `trapdoor_gives_inverse` | 33 | 0 | 0 | OK |
| `lambda_solves_RSA_on_units` | 81 | 0 | 0 | OK |
| `d_yields_annihilator` | 96 | 0 | 0 | OK |

## Wiener.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `wiener_relation` | 28 | 0 | 0 | OK |
| `N_minus_phi` | 35 | 0 | 0 | OK |
| `wiener_numerator` | 40 | 0 | 0 | OK |
| `small_d_small_k` | 51 | 0 | 0 | OK |
| `wiener_abs_numerator` | 72 | 0 | 0 | OK |
| `wiener_basin_from_gap` | 84 | 0 | 0 | OK |
| `k_lt_d_of_e_lt_phi` | 107 | 0 | 0 | OK |
| `wiener_classical_sufficient` | 123 | 0 | 0 | OK |

## WireEq.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `wire_eq_sat` | 18 | 0 | 0 | OK |
| `wire_eq_complete` | 27 | 0 | 0 | OK |
| `wire_eq_same_encoding` | 41 | 0 | 0 | OK |

## WirePoK.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `wire_slots_assemble` | 36 | 0 | 0 | OK |
| `wire_slot_eqdl` | 49 | 0 | 0 | OK |
| `wire_slot_extracts` | 71 | 0 | 0 | OK |
| `three_wire_assemble` | 93 | 0 | 0 | OK |
