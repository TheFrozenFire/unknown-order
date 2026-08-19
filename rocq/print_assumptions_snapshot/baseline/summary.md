# Print Assumptions snapshot — UnknownOrder

**Headline:** all 1098 named results are **Closed under the global context** — **0 load-bearing axioms** across the whole corpus.

Captured for 1098 results across 68 files.

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

## BlindRSA.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `chaum_sign_blinded_is_raw_times_r` | 25 | 0 | 0 | OK |
| `chaum_unblind_is_raw_sign` | 46 | 0 | 0 | OK |

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

## ChallengePrime.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `ch_encode_odd` | 30 | 0 | 0 | OK |
| `ch_accept_is_prime` | 37 | 0 | 0 | OK |
| `ch_encode_not_slot_residue` | 41 | 0 | 0 | OK |
| `ch_image_is_not_slot_image` | 45 | 0 | 0 | OK |
| `ch_encode_not_roca_on_cas28` | 56 | 0 | 0 | OK |

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
| `cubing_invertible_on_units` | 27 | 0 | 0 | OK |
| `cube_root_map_is_cube` | 56 | 0 | 0 | OK |
| `cube_euler_one_direction` | 70 | 0 | 0 | OK |
| `three_divides_lambda_forbids_e3` | 109 | 0 | 0 | OK |

## CyclicCount.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `sum_up_ext` | 42 | 0 | 0 | OK |
| `cyclic_count_agree_below` | 54 | 0 | 0 | OK |
| `cyclic_count_top` | 69 | 0 | 0 | OK |
| `cyclic_count_sum` | 79 | 0 | 0 | OK |
| `cyclic_mismatch_11_17` | 110 | 0 | 0 | OK |
| `miller_150_of_158` | 117 | 0 | 0 | OK |
| `cyclic_mismatch_14_is_15_16` | 122 | 0 | 0 | OK |
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
| `eval_pair_stays_in_mu` | 26 | 0 | 0 | OK |
| `eval_pair_add` | 43 | 0 | 0 | OK |
| `eval_pair_mul_base` | 56 | 0 | 0 | OK |
| `eval_pair_reduce_mod_n` | 71 | 0 | 0 | OK |
| `eval_pair_image_divides_n` | 94 | 0 | 0 | OK |
| `eval_pair_mu2` | 104 | 0 | 0 | OK |
| `eval_pair_mu2_on_mixed` | 119 | 0 | 0 | OK |
| `omega_cube_is_one` | 134 | 0 | 0 | OK |
| `eval_pair_mu3` | 154 | 0 | 0 | OK |
| `mu2_is_mu6` | 167 | 0 | 0 | OK |
| `mu3_is_mu6` | 182 | 0 | 0 | OK |
| `eval_pair_mu6` | 197 | 0 | 0 | OK |

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

## Hardness.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `rsa_units_are_eth_powers` | 37 | 0 | 0 | OK |
| `trapdoor_inverts_RSA` | 48 | 0 | 0 | OK |
| `rsa_solution_is_strong_RSA` | 68 | 0 | 0 | OK |
| `lambda_solves_strong_RSA` | 82 | 0 | 0 | OK |
| `strong_RSA_trivial_at_one` | 106 | 0 | 0 | OK |
| `rsa_trivial_at_one` | 114 | 0 | 0 | OK |
| `order_divides_annihilator` | 123 | 0 | 0 | OK |
| `order_divides_lambda` | 152 | 0 | 0 | OK |
| `one_sided_low_order_factors` | 180 | 0 | 0 | OK |
| `one_sided_low_order_is_factor` | 212 | 0 | 0 | OK |
| `adaptive_root_is_strong_RSA` | 225 | 0 | 0 | OK |
| `order_is_annihilator` | 236 | 0 | 0 | OK |
| `low_order_is_annihilator` | 245 | 0 | 0 | OK |
| `lambda_is_annihilator_on_units` | 254 | 0 | 0 | OK |
| `annihilator_plus_one_is_strong_RSA` | 267 | 0 | 0 | OK |
| `rsa_is_fractional_root` | 284 | 0 | 0 | OK |
| `strong_RSA_is_fractional_root` | 300 | 0 | 0 | OK |
| `annihilator_is_fractional_root_of_one` | 315 | 0 | 0 | OK |
| `ar_C_implies_strong_RSA` | 344 | 0 | 0 | OK |
| `ar_C_requires_C` | 353 | 0 | 0 | OK |
| `strong_RSA_is_ar_C_iff` | 358 | 0 | 0 | OK |
| `lambda_plus_one_11_17` | 369 | 0 | 0 | OK |
| `lambda_plus_one_11_17_not_prime` | 373 | 0 | 0 | OK |
| `lambda_solves_search_11_17` | 381 | 0 | 0 | OK |
| `search_lambda_plus_one_misses_prime_AR` | 392 | 0 | 0 | OK |
| `adaptive_root_known_product_breaks` | 410 | 0 | 0 | OK |
| `adaptive_root_smooth_power_breaks` | 426 | 0 | 0 | OK |

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
| `rsa_test_base2_g0` | 114 | 0 | 0 | OK |
| `rsa_test_base2_chain` | 119 | 0 | 0 | OK |
| `rsa_test_base2_splits` | 125 | 0 | 0 | OK |

## MillerHeight.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `miller_t_pos` | 23 | 0 | 0 | OK |
| `miller_t_odd` | 29 | 0 | 0 | OK |
| `miller_t_multiple_of_lambda_odd` | 35 | 0 | 0 | OK |
| `powm_one_mod_factor` | 53 | 0 | 0 | OK |
| `miller_height_exists` | 66 | 0 | 0 | OK |
| `miller_from_d` | 103 | 0 | 0 | OK |
| `rsa_test_base2_heights` | 126 | 0 | 0 | OK |
| `rsa_test_miller_from_d` | 141 | 0 | 0 | OK |

## MillerRabin.v

| Theorem | Line | total | load-bearing | status |
|---|---:|---:|---:|---|
| `mr_split` | 28 | 0 | 0 | OK |
| `miller_mr_same_engine` | 48 | 0 | 0 | OK |
| `mr_nontrivial_sqrt_factors` | 63 | 0 | 0 | OK |
| `mr_fermat_on_prime` | 84 | 0 | 0 | OK |

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
| `is_order_unique` | 28 | 0 | 0 | OK |
| `powm_one_of_divide` | 41 | 0 | 0 | OK |
| `order_iff_divides` | 57 | 0 | 0 | OK |
| `order_exists_from_annihilator` | 79 | 0 | 0 | OK |
| `order_exists_prime` | 129 | 0 | 0 | OK |
| `order_exists_semiprime` | 143 | 0 | 0 | OK |
| `order_of_power` | 160 | 0 | 0 | OK |
| `lcm_orders_divides_lambda` | 222 | 0 | 0 | OK |
| `is_order_2_of` | 249 | 0 | 0 | OK |
| `minus1_order_2_rsa_test` | 263 | 0 | 0 | OK |
| `mixed67_order_2_rsa_test` | 269 | 0 | 0 | OK |
| `lcm_two_order2_not_lambda` | 275 | 0 | 0 | OK |
| `powm_eq_1_iff_order_divides` | 287 | 0 | 0 | OK |
| `pow2_divides_pow2` | 298 | 0 | 0 | OK |
| `two_height_is_val2_ord` | 321 | 0 | 0 | OK |
| `order_2_mod_11` | 380 | 0 | 0 | OK |
| `order_2_mod_17` | 391 | 0 | 0 | OK |
| `two_height_independent_of_odd_multiple` | 404 | 0 | 0 | OK |
| `height_is_val2_ord_textbook` | 420 | 0 | 0 | OK |

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
| `rsa_N_gt_1` | 37 | 0 | 0 | OK |
| `rsa_lambda_pos` | 44 | 0 | 0 | OK |
| `rsa_lambda_gt_1` | 50 | 0 | 0 | OK |
| `rsa_phi_pos` | 69 | 0 | 0 | OK |
| `rsa_lambda_divides_phi` | 75 | 0 | 0 | OK |
| `rsa_ed_minus_1_divides` | 78 | 0 | 0 | OK |
| `rsa_ed_gt_1` | 87 | 0 | 0 | OK |
| `rsa_dec_enc_units` | 100 | 0 | 0 | OK |
| `rsa_enc_dec_units` | 124 | 0 | 0 | OK |
| `rsa_d_is_cube_root_map` | 151 | 0 | 0 | OK |
| `prime_11` | 161 | 0 | 0 | OK |
| `prime_17` | 170 | 0 | 0 | OK |
| `rsa_test_lambda` | 180 | 0 | 0 | OK |
| `rsa_test_phi` | 183 | 0 | 0 | OK |
| `rsa_test_inv` | 186 | 0 | 0 | OK |
| `rsa_test_coprime_e` | 189 | 0 | 0 | OK |
| `rsa_test_N` | 204 | 0 | 0 | OK |
| `rsa_test_vector` | 207 | 0 | 0 | OK |
| `rsa_test_roundtrip` | 211 | 0 | 0 | OK |
| `rsa_test_annihilator` | 215 | 0 | 0 | OK |
| `N_cong_q_mod_pminus1` | 230 | 0 | 0 | OK |
| `gcd_polyN_pminus1_is_gcd_at_q` | 241 | 0 | 0 | OK |

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
| `rabin_oracle_nonassociate_factors` | 268 | 0 | 0 | OK |
| `rw_verify_of_root` | 304 | 0 | 0 | OK |
| `kg_rw_implies_blum` | 315 | 0 | 0 | OK |
| `kg_rw_pminus1_almost_odd` | 323 | 0 | 0 | OK |

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
| `product_carries_component_keygen` | 528 | 0 | 0 | OK |
| `product_common_e_inverts` | 534 | 0 | 0 | OK |
| `product_refuses_shared_prime` | 544 | 0 | 0 | OK |
| `d_star_gt_lambda_div_e` | 550 | 0 | 0 | OK |
| `carmichael_shared3` | 588 | 0 | 0 | OK |
| `d_star_unique_mod_lambda` | 648 | 0 | 0 | OK |
| `d_star_inverts_on_A` | 664 | 0 | 0 | OK |
| `d_star_inverts_on_B` | 678 | 0 | 0 | OK |
| `d_star_ed_minus_1_divides_lambda` | 692 | 0 | 0 | OK |
| `d_star_annihilates_shared` | 705 | 0 | 0 | OK |
| `d_star_decrypts_B` | 729 | 0 | 0 | OK |
| `d_star_decrypts_A` | 744 | 0 | 0 | OK |
| `coprime_powm` | 769 | 0 | 0 | OK |
| `shared_N_gt_1` | 795 | 0 | 0 | OK |
| `dstar_power_crs_is_powm` | 804 | 0 | 0 | OK |
| `shared_dec_is_eth_root` | 846 | 0 | 0 | OK |
| `srs_first_checks` | 873 | 0 | 0 | OK |
| `srs_step_checks` | 895 | 0 | 0 | OK |
| `srs_first_is_rsa` | 936 | 0 | 0 | OK |
| `srs_first_is_strong_rsa` | 951 | 0 | 0 | OK |
| `lambda_plus_one_is_other_strong_rsa` | 967 | 0 | 0 | OK |
| `dstar_inverts_every_unit` | 986 | 0 | 0 | OK |
| `powm_eq_implies_abs_annihilator` | 1010 | 0 | 0 | OK |
| `dlog_of_srs_agrees_mod_order` | 1054 | 0 | 0 | OK |
| `dlog_at_full_order_inverts_e` | 1077 | 0 | 0 | OK |

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
| `rsa_inverter_recovers_message` | 586 | 0 | 0 | OK |
| `sign_hom_3` | 618 | 0 | 0 | OK |
| `sign_of_msg_product_one` | 634 | 0 | 0 | OK |
| `sign_weighted_commute` | 651 | 0 | 0 | OK |
| `sign_weighted_product` | 665 | 0 | 0 | OK |
| `euler_sign_of_pm1` | 692 | 0 | 0 | OK |
| `euler_sign_sq` | 709 | 0 | 0 | OK |
| `other_legendre_from_product` | 720 | 0 | 0 | OK |
| `cipher_jacobi_eq_message` | 733 | 0 | 0 | OK |
| `onesided_plain_one_factors` | 768 | 0 | 0 | OK |
| `ctor_slot_mod_r_need_not_factor` | 783 | 0 | 0 | OK |
| `cube_below_N` | 803 | 0 | 0 | OK |
| `e3_small_cube_verifies` | 818 | 0 | 0 | OK |
| `bleiche_wrap_interval` | 833 | 0 | 0 | OK |
| `pkcs15_prefix_is_type2` | 859 | 0 | 0 | OK |
| `manger_is_stricter_than_type2` | 869 | 0 | 0 | OK |

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
