# Coverage table of contents

Generated from `(** * *)` section comments and named results
in the Rocq tree.  Do not edit by hand.

## `Accumulator.v`

- L13: Accumulator membership as the RSA-shaped map
  - L151: Shamir's trick, and why same-bit-length members do not restore soundness
  - L346: Li–Li–Xue non-membership
  - L652: Integer commitment binding (FO/DF relation)

| Kind | Name | Line |
|---|---|---:|
| Theorem | `membership_witness_is_root` | 34 |
| Theorem | `forged_mem_is_adaptive_root` | 45 |
| Theorem | `rsa_acc_add_is_powm` | 56 |
| Theorem | `rsa_mem_wit_is_powm` | 61 |
| Theorem | `cl_acc_add_is_exp` | 72 |
| Theorem | `cl_has_no_trapdoor_update` | 79 |
| Theorem | `rsa_public_has_no_trapdoor_update` | 83 |
| Theorem | `rsa_acc_forge_from_lambda` | 87 |
| Theorem | `cl_odd_invertible_mod_two` | 102 |
| Theorem | `cl_no_trapdoor_from_two` | 111 |
| Theorem | `rsa_composite_member_splits_witness` | 125 |
| Lemma | `powm_mul_l_mod` | 158 |
| Lemma | `powm_inv_cancels` | 168 |
| Lemma | `mul_pow_mod_cong` | 184 |
| Lemma | `zmul_nonneg_eq_1` | 200 |
| Lemma | `shamir_neg_beta` | 207 |
| Lemma | `shamir_trick` | 248 |
| Theorem | `bdm_coprime_gives_product_witness` | 304 |
| Theorem | `bdm_same_bits_still_splits` | 326 |
| Theorem | `llx_complete_nonneg` | 357 |
| Theorem | `llx_complete` | 379 |
| Lemma | `llx_Bx_eq_g_times_inv` | 415 |
| Lemma | `g_times_inv_succ` | 450 |
| Theorem | `llx_extract_root` | 466 |
| Lemma | `bezout3` | 529 |
| Theorem | `llx_lambda_forges_nonmem` | 543 |
| Theorem | `rsa_trapdoor_add` | 596 |
| Theorem | `peng_bao_member_still_forges` | 631 |
| Theorem | `icomm_cancel_h` | 663 |
| Theorem | `icomm_binding_is_fractional_root` | 707 |
| Theorem | `icomm_same_msg_is_annihilator` | 723 |
| Theorem | `lipmaa_cl_membership_is_P_Root` | 748 |

## `AddGate.v`

- L13: Addition as a QAP

| Kind | Name | Line |
|---|---|---:|
| Theorem | `add_gate_sat` | 32 |
| Theorem | `add_gate_complete` | 43 |
| Theorem | `add_is_public_sum` | 63 |

## `AllBits.v`

- L16: Every limb is a bit, and the value encoding unfolds

| Kind | Name | Line |
|---|---|---:|
| Lemma | `all_bits_nn` | 28 |
| Theorem | `all_bits_value_nonneg` | 36 |
| Theorem | `all_bits_qap` | 42 |
| Theorem | `three_bit_encoding` | 53 |

## `ArithShape.v`

- L17: Twelve arith, peel-gap, and modulus-shape inroads
  - L26: 1. Newton iteration in [(Z/NZ)]
  - L37: 2. [e | (y−1)]
  - L51: 3. [x=y] with [e = ord(y)+1] (missing peel leaf)
  - L61: 4. Fermat-on-the-witness [gcd(x−y, N)]
  - L67: 5. Takagi [N=p²q], Hensel tape
  - L83: 6. Public scaling [x = 2y]
  - L89: 7. [e = nextprime(y)]
  - L120: 8. Continued fraction of [y/N]
  - L130: 9. Same [x], two coprime moduli
  - L141: 10. Multiprime [N=pqr], mixed [√1]
  - L160: 11. Factored composite [e = 15]
  - L168: 12. DL of [y] in public base [2]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `arith_newton_inv3` | 28 |
| Theorem | `arith_newton_from_one` | 32 |
| Theorem | `arith_e5_divides_yminus1` | 39 |
| Theorem | `arith_e7_divides_yminus1` | 43 |
| Theorem | `arith_e7_residual` | 47 |
| Theorem | `arith_xy_period_residual` | 53 |
| Theorem | `arith_xy_period_no_split` | 57 |
| Theorem | `arith_witness_gap_no_split` | 63 |
| Theorem | `arith_takagi_shape` | 69 |
| Theorem | `arith_takagi_euler_p2` | 75 |
| Theorem | `arith_takagi_p_on_tape` | 79 |
| Theorem | `arith_double_y_not_root` | 85 |
| Lemma | `prime_37` | 91 |
| Theorem | `arith_nextprime_e37` | 106 |
| Theorem | `arith_nextprime_residual` | 112 |
| Theorem | `arith_nextprime_root_is_49` | 116 |
| Theorem | `arith_cf_euclidean` | 122 |
| Theorem | `arith_cf_convergents_not_root` | 126 |
| Theorem | `arith_two_moduli_coprime` | 132 |
| Theorem | `arith_two_moduli_same_x` | 136 |
| Lemma | `three_prime_357` | 143 |
| Theorem | `arith_mixed_pqr_is_factor` | 150 |
| Theorem | `arith_composite_e15_shares_lambda` | 162 |
| Theorem | `arith_36_not_in_ltwo` | 178 |
| Theorem | `arith_two_and_thirtysix_same_order_period` | 182 |

## `AuxBil.v`

- L10: Self-bilinear with auxiliary public data

| Kind | Name | Line |
|---|---|---:|
| Lemma | `aux_is_self_bil` | 30 |
| Theorem | `aux_self_bil_checks_pot` | 40 |
| Theorem | `aux_self_bil_evaluates_pot` | 54 |
| Theorem | `aux_eval_publishes_next` | 72 |
| Theorem | `forget_aux_is_self_bil` | 82 |

## `BGH.v`

- L14: Cocks / Boneh–Gentry–Hamburg — 1-bit pairing catalog

| Kind | Name | Line |
|---|---|---:|
| Theorem | `jacobi_additive_pairing` | 29 |
| Theorem | `jacobi_neg1_on_blum` | 58 |
| Theorem | `jacobi_one_mul_closed` | 73 |
| Theorem | `cocks_pair_first_decrypts` | 95 |
| Theorem | `cocks_pair_second_decrypts` | 118 |
| Theorem | `cocks_pair_covers_blum` | 141 |

## `BatchOrder.v`

- L11: Type D without a shared prime: a common one-sided annihilator

| Kind | Name | Line |
|---|---|---:|
| Lemma | `shared_pminus1_divides_gcd` | 27 |
| Lemma | `gcd_pminus1_pos` | 36 |
| Theorem | `distinct_semiprimes_coprime` | 46 |
| Theorem | `batch_p1_splits_pair` | 64 |
| Lemma | `shared_pminus1_is_ap` | 91 |

## `BinForms.v`

- L9: Primitive binary quadratic forms of discriminant [Δ]
  - L166: SL2 action and proper equivalence
  - L335: Represented values: a reduced form with [a > 1] is not principal
  - L419: Dirichlet composition
  - L832: Ambiguous forms from a divisor of [Δ]
  - L883: Catalog: [Δ ∈ {−23, −47, −87, −403, −455}]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `bqf_inv_disc` | 44 |
| Lemma | `bqf_inv_primitive` | 48 |
| Lemma | `bqf_inv_inv` | 56 |
| Lemma | `bqf_id_a` | 63 |
| Lemma | `four_times_div4` | 69 |
| Lemma | `one_minus_D_mod4` | 78 |
| Theorem | `bqf_id_disc` | 89 |
| Lemma | `bqf_id_primitive` | 107 |
| Theorem | `bqf_id_of_disc` | 114 |
| Theorem | `bqf_id_disc_neg4` | 118 |
| Theorem | `bqf_id_disc_neg47` | 121 |
| Theorem | `bqf_id_disc_neg23` | 124 |
| Theorem | `bqf_id_of_disc_neg47` | 127 |
| Lemma | `of_disc_a_nz` | 131 |
| Lemma | `bqf_id_ambiguous_mod0` | 152 |
| Theorem | `disc_neg47` | 158 |
| Lemma | `sl2_I_ok` | 204 |
| Lemma | `sl2_T_ok` | 207 |
| Lemma | `sl2_S_ok` | 210 |
| Lemma | `bqf_act_I` | 213 |
| Lemma | `bqf_equiv_refl` | 220 |
| Lemma | `sl2_mul_det` | 235 |
| Lemma | `sl2_mul_ok` | 243 |
| Lemma | `sl2_inverse_ok` | 249 |
| Lemma | `bqf_act_mul` | 261 |
| Theorem | `bqf_equiv_trans` | 271 |
| Lemma | `bqf_act_disc` | 280 |
| Lemma | `bqf_act_disc_sl2` | 289 |
| Lemma | `bqf_act_T` | 295 |
| Lemma | `bqf_act_S` | 306 |
| Theorem | `ambiguous_equiv_inv` | 317 |
| Lemma | `bqf_act_eval` | 340 |
| Lemma | `bqf_id_eval_1` | 350 |
| Lemma | `z_le_abs` | 357 |
| Lemma | `reduced_eval_ge_a` | 360 |
| Theorem | `reduced_a_gt_1_not_principal` | 399 |
| Lemma | `compose_gcd_id_l` | 449 |
| Lemma | `dirichlet_B_id_l` | 456 |
| Theorem | `compose_id_left` | 463 |
| Lemma | `compose_inv_gcd` | 489 |
| Theorem | `compose_inv_leading_one` | 497 |
| Lemma | `dirichlet_B_inv_plus_2` | 507 |
| Lemma | `four_divides_B2_minus_disc_inv` | 520 |
| Lemma | `reconstruct_disc_div4` | 530 |
| Lemma | `compose_inv_c` | 537 |
| Lemma | `compose_inv_primitive` | 550 |
| Theorem | `compose_inv_of_disc` | 561 |
| Theorem | `form_a_one_equiv_id` | 581 |
| Theorem | `compose_inv_equiv_id` | 658 |
| Lemma | `ambiguous_div_is_ambiguous` | 684 |
| Lemma | `solve_cong_target_0` | 688 |
| Lemma | `compose_self_gcd_div` | 699 |
| Lemma | `dirichlet_B_self_div` | 716 |
| Theorem | `compose_self_leading_one` | 725 |
| Lemma | `compose_self_b` | 737 |
| Lemma | `compose_self_c` | 743 |
| Lemma | `four_divides_b2_minus_disc` | 759 |
| Theorem | `compose_self_of_disc` | 766 |
| Theorem | `compose_self_ambiguous_equiv_id` | 788 |
| Theorem | `compose_assoc_id_inv` | 818 |
| Lemma | `amb_from_div_ambiguous` | 840 |
| Lemma | `amb_from_div_disc_mod0` | 848 |
| Lemma | `amb_from_div_disc_mod1` | 866 |
| Lemma | `iq_neg23` | 906 |
| Lemma | `iq_neg47` | 909 |
| Lemma | `iq_neg87` | 912 |
| Lemma | `iq_neg403` | 915 |
| Lemma | `iq_neg455` | 918 |
| Theorem | `form_neg87_amb_of_disc` | 921 |
| Theorem | `form_neg403_amb_of_disc` | 924 |
| Theorem | `form_neg403_amb_red_of_disc` | 927 |
| Theorem | `form_neg455_5_of_disc` | 930 |
| Theorem | `form_neg455_7_of_disc` | 933 |
| Theorem | `form_neg455_13_red_of_disc` | 936 |
| Theorem | `form_neg87_amb_reduced` | 939 |
| Theorem | `form_neg403_amb_red_reduced` | 942 |
| Theorem | `form_neg455_5_reduced` | 945 |
| Theorem | `form_neg455_7_reduced` | 948 |
| Theorem | `form_neg455_13_red_reduced` | 951 |
| Theorem | `form_neg87_amb_is_ambiguous` | 954 |
| Theorem | `form_neg403_amb_is_ambiguous` | 957 |
| Theorem | `form_neg403_amb_red_is_ambiguous` | 960 |
| Theorem | `form_neg455_5_is_ambiguous` | 963 |
| Theorem | `form_neg455_7_is_ambiguous` | 966 |
| Theorem | `form_neg455_13_red_is_ambiguous` | 969 |
| Theorem | `form_neg87_not_principal` | 972 |
| Theorem | `form_neg403_not_principal` | 981 |
| Theorem | `form_neg455_5_not_principal` | 990 |
| Theorem | `form_neg455_7_not_principal` | 999 |
| Theorem | `form_neg455_13_not_principal` | 1008 |
| Theorem | `catalog_compose_inv_is_principal` | 1026 |
| Theorem | `catalog_wins_LowOrder_B2` | 1037 |
| Lemma | `bqf_exp_0` | 1070 |
| Lemma | `bqf_exp_1` | 1073 |
| Lemma | `bqf_exp_2` | 1083 |
| Theorem | `bqf_exp_2_ambiguous_div` | 1093 |

## `BitLeak.v`

- L9: Partial bits / thin arithmetic progressions

| Kind | Name | Line |
|---|---|---:|
| Lemma | `high_bits_unknown_is_x` | 37 |
| Lemma | `roca_unknown_is_k` | 43 |
| Lemma | `bitleak_poly_divides_N` | 59 |

## `BitLogic.v`

- L15: Bit operations from the mul and add gates

| Kind | Name | Line |
|---|---|---:|
| Theorem | `bit_and_is_mul` | 31 |
| Theorem | `bit_and_closed` | 41 |
| Theorem | `bit_or_table` | 48 |
| Theorem | `bit_or_closed` | 57 |
| Theorem | `bit_xor_table` | 64 |
| Theorem | `bit_xor_closed` | 72 |
| Theorem | `bit_or_from_and` | 79 |
| Theorem | `bit_xor_from_and` | 84 |

## `BitLt.v`

- L15: Bit less-than: [lt x y = (1−x)·y]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `bit_lt_table` | 24 |
| Theorem | `bit_lt_closed` | 35 |
| Theorem | `bit_lt_is_and` | 42 |
| Theorem | `bit_lt_mul` | 46 |

## `BitSum.v`

- L15: Little-endian bit-sum: [v = b0 + 2 v_rest]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `bit_value_nil` | 28 |
| Lemma | `bit_value_cons` | 31 |
| Theorem | `bit_value_nonneg` | 35 |
| Theorem | `bit_value_cons_encoding` | 50 |
| Theorem | `bit_value_range2` | 66 |
| Theorem | `nested_square` | 70 |

## `BlindRSA.v`

- L11: Chaum blinded RSA

| Kind | Name | Line |
|---|---|---:|
| Theorem | `chaum_sign_blinded_is_raw_times_r` | 25 |
| Theorem | `chaum_unblind_is_raw_sign` | 46 |

## `BonehVenkatesan.v`

- L17: Boneh–Venkatesan unwind of a low-[e] algebraic reduction

| Kind | Name | Line |
|---|---|---:|
| Theorem | `bv_two_is_integer_cube` | 26 |
| Theorem | `bv_36_is_not_integer_cube` | 30 |
| Theorem | `cube_is_powm3_pin` | 34 |
| Theorem | `integer_cube_root_8` | 38 |
| Theorem | `bv_groot_8_is_2` | 42 |
| Theorem | `bv_root_gate_is_not_rsa_inverter` | 46 |
| Theorem | `bv_groot_handle_is_2` | 75 |
| Theorem | `bv_unwound_handle_is_2` | 79 |
| Theorem | `bv_with_root_outputs_11` | 83 |
| Theorem | `bv_unwound_outputs_11` | 87 |
| Theorem | `bv_unwind_one_cube` | 91 |
| Theorem | `bv_few_query_low_e_drops_oracle` | 96 |
| Theorem | `bv_factor_from_root_handle` | 102 |
| Theorem | `bv_42_cube_in_Z_is_not_36` | 108 |
| Theorem | `bv_query_leak_already_factors` | 112 |

## `BrownSLP.v`

- L17: Brown SLP-solver: identity vs functional-on-units

| Kind | Name | Line |
|---|---|---:|
| Theorem | `slp_carmichael_is_functional` | 27 |
| Theorem | `slp_solver_not_poly_identity_linear` | 31 |
| Theorem | `slp_solver_not_poly_identity_last` | 35 |
| Theorem | `X81_minus_X_leading_not_zero_mod_11` | 39 |
| Theorem | `brown_low_degree_identity_forbids_N_dividing_minus1` | 43 |
| Theorem | `two_pow_81_is_two_mod_N` | 47 |
| Theorem | `brown_dual_pow27_fst` | 60 |
| Theorem | `brown_dual_not_identity` | 64 |
| Theorem | `brown_dual_tangent_mod_N` | 68 |
| Theorem | `brown_dual_gcd_pin` | 72 |
| Theorem | `brown_ed_minus_1_is_80` | 76 |

## `CPP17.v`

- L14: Couteau–Peters–Pointcheval (EUROCRYPT 2017) shape

| Kind | Name | Line |
|---|---|---:|
| Theorem | `cpp17_witness_is_rsa` | 21 |
| Theorem | `cpp17_complete_pin` | 25 |
| Theorem | `cpp17_second_transcript` | 32 |
| Theorem | `cpp17_shamir_gcd_pin` | 39 |
| Theorem | `cpp17_extract_is_fixed_e` | 43 |
| Theorem | `cpp17_protocol_e_is_three` | 51 |
| Theorem | `cpp17_srsa_other_pair` | 55 |
| Theorem | `cpp17_sigma_does_not_output_that_pair` | 62 |

## `CRTRSA.v`

- L12: CRT-RSA: a small [d_p] is a short one-sided annihilator
  - L146: Garner CRT decrypt equals [c^d]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `lambda_gt_1_of` | 27 |
| Lemma | `ed_one_mod_pminus1_of` | 43 |
| Lemma | `dp_congruent_d` | 64 |
| Theorem | `crt_dp_annihilates` | 68 |
| Lemma | `short_dp_short_annihilator` | 105 |
| Lemma | `lambda_semiprime_comm` | 118 |
| Theorem | `crt_dq_annihilates` | 122 |
| Lemma | `short_dq_short_annihilator` | 135 |
| Lemma | `powm_reduce_pminus1` | 151 |
| Theorem | `crt_decrypt_eq_rsa_dec` | 179 |

## `ChallengePrime.v`

- L12: Challenge / member encoding: odd integers, not the constructor AP

| Kind | Name | Line |
|---|---|---:|
| Theorem | `ch_encode_odd` | 30 |
| Theorem | `ch_accept_is_prime` | 37 |
| Theorem | `ch_encode_not_slot_residue` | 41 |
| Theorem | `ch_image_is_not_slot_image` | 45 |
| Theorem | `ch_encode_not_roca_on_cas28` | 56 |

## `Circuit.v`

- L15: A two-gate circuit: [z = x·y + t]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `prod_add_sat` | 24 |
| Theorem | `prod_add_complete` | 39 |
| Theorem | `mul_public_first` | 64 |

## `ClassGroupWall.v`

- L13: The wall between Type B and adaptive root
  - L85: Restricted low-order
  - L162: Restricted low-order after excluding [Cl[2]]
  - L328: Families: constructible torsion is not always [Cl[2]]
  - L428: Class number is an AR-search trapdoor

| Kind | Name | Line |
|---|---|---:|
| Theorem | `adaptive_root_trivial_from_lambda` | 35 |
| Theorem | `typeB_pminus1_is_cyc1` | 48 |
| Theorem | `typeB_pplus1_is_cyc2` | 52 |
| Theorem | `typeB_leak_needs_modulus` | 70 |
| Theorem | `iq_disc_agrees` | 81 |
| Theorem | `rsa_minus1_is_constructible` | 103 |
| Theorem | `unrestricted_LowOrder_won_by_Cl2` | 107 |
| Theorem | `restricted_LowOrder_excludes_Cl2` | 111 |
| Theorem | `catalog_ambiguous_is_constructible` | 119 |
| Theorem | `public_2_annihilator_hits_ambiguous` | 139 |
| Theorem | `disc_mod1_is_odd` | 145 |
| Theorem | `adaptive_root_relation_is_presentation_blind` | 157 |
| Theorem | `iq_neg31` | 180 |
| Theorem | `form_neg31_ord3_of_disc` | 183 |
| Theorem | `form_neg31_ord3_reduced` | 189 |
| Theorem | `form_neg31_ord3_not_ambiguous` | 192 |
| Theorem | `form_neg31_ord3_not_principal` | 197 |
| Theorem | `form_neg31_sq_compute` | 206 |
| Theorem | `form_neg31_cube_compute` | 210 |
| Theorem | `form_neg31_exp2` | 214 |
| Theorem | `form_neg31_exp3` | 221 |
| Theorem | `form_neg31_sq_equiv_inv` | 230 |
| Theorem | `form_neg31_inv_reduced` | 237 |
| Theorem | `form_neg31_inv_of_disc` | 240 |
| Theorem | `form_neg31_inv_not_principal` | 247 |
| Theorem | `form_neg31_actS_inv_is_sq` | 256 |
| Theorem | `form_neg31_sq_not_principal` | 260 |
| Theorem | `sl2_reduce_cube_ok` | 274 |
| Theorem | `form_neg31_cube_equiv_id` | 277 |
| Theorem | `form_neg31_exp3_equiv_id` | 284 |
| Theorem | `form_neg31_exp1` | 288 |
| Theorem | `mersenne31_wins_restricted_LowOrder` | 307 |
| Theorem | `mersenne31_is_odd_order` | 324 |
| Theorem | `shanks_disc_2` | 340 |
| Theorem | `shanks_form_2` | 343 |
| Theorem | `shanks_form_disc` | 346 |
| Theorem | `shanks_disc_3` | 356 |
| Theorem | `iq_neg107` | 359 |
| Theorem | `shanks_u3_of_disc` | 362 |
| Theorem | `shanks_u3_not_ambiguous` | 369 |
| Theorem | `shanks_u3_exp3_compute` | 380 |
| Theorem | `shanks_u3_cube_equiv_id` | 388 |
| Theorem | `shanks_u3_exp3_equiv_id` | 395 |
| Theorem | `shanks_family_has_3` | 399 |
| Theorem | `mersenne31_shanks_in_family_H` | 417 |
| Theorem | `mersenne31_shanks_not_ordinary_H` | 424 |
| Theorem | `bqf_exp_id` | 437 |
| Theorem | `neg31_id_annihilated_by_h` | 448 |
| Theorem | `form_neg31_inv_exp2` | 455 |
| Theorem | `form_neg31_inv_sq_equiv_f` | 462 |
| Theorem | `shanks_inv_square_is_shanks` | 469 |
| Theorem | `shanks_annihilated_by_h` | 477 |

## `Cocks.v`

- L13: Cocks 2001 IBE — algebra only

| Kind | Name | Line |
|---|---|---:|
| Theorem | `cocks_carefully_chosen` | 39 |
| Lemma | `cocks_ct_times_t` | 53 |
| Lemma | `euler_sign_cong_mod` | 84 |
| Lemma | `jacobi_cong` | 100 |
| Lemma | `jacobi_mul` | 124 |
| Lemma | `jacobi_sq_one` | 143 |
| Lemma | `jacobi_self_sq` | 163 |
| Theorem | `cocks_decrypt_jacobi` | 180 |

## `CoeffPoK.v`

- L15: Knowledge of coefficients of a committed evaluation

| Kind | Name | Line |
|---|---|---:|
| Lemma | `coeff_slot_eval` | 41 |
| Lemma | `slots_from_i` | 56 |
| Theorem | `slots_assemble` | 84 |
| Theorem | `two_coeff_assemble` | 98 |
| Theorem | `coeff_slot_eqdl` | 118 |
| Theorem | `coeff_slot_extracts` | 142 |

## `CondSwap.v`

- L13: Conditional swap: on bit [s], swap [a] and [b] or not

| Kind | Name | Line |
|---|---|---:|
| Theorem | `cswap_off` | 24 |
| Theorem | `cswap_on` | 32 |
| Theorem | `cswap_select` | 40 |
| Theorem | `cswap_involution` | 52 |

## `CramerShoup.v`

- L12: Cramer–Shoup 2000 Strong RSA signatures, verification algebra

| Kind | Name | Line |
|---|---|---:|
| Lemma | `powm_mul_base` | 24 |
| Theorem | `cs_verify_is_rsa` | 34 |
| Theorem | `cs_verify_is_strong_rsa` | 44 |
| Theorem | `cs_same_e_ratio` | 55 |

## `CubicResidue.v`

- L15: Cubic residuosity when cubing is not a permutation
  - L612: Mixed cube roots of 1 split [N]; diagonal leftover does not

| Kind | Name | Line |
|---|---|---:|
| Theorem | `cubing_invertible_on_units` | 46 |
| Theorem | `cube_root_map_is_cube` | 75 |
| Theorem | `cube_euler_one_direction` | 89 |
| Theorem | `three_divides_lambda_forbids_e3` | 128 |
| Theorem | `cube_euler_converse` | 146 |
| Theorem | `cube_euler_iff` | 186 |
| Lemma | `cube_N_implies_local` | 199 |
| Lemma | `cube_N_of_local` | 224 |
| Theorem | `cube_N_iff_both` | 251 |
| Lemma | `cube_root_coprime` | 263 |
| Theorem | `cube_euler_lambda_necessary` | 293 |
| Lemma | `prime_7_cubic` | 320 |
| Lemma | `prime_13` | 328 |
| Lemma | `prime_19` | 338 |
| Theorem | `cube_mixed_5_not_global` | 349 |
| Theorem | `cube_euler_lambda_not_sufficient_247` | 368 |
| Theorem | `pin_units_are_cubes` | 383 |
| Lemma | `omega_from_primitive_root` | 399 |
| Lemma | `primitive_3rd_root_cyclotomic` | 412 |
| Lemma | `cube_char_cubed_one` | 437 |
| Lemma | `cube_char_mul` | 457 |
| Lemma | `mu3_N_iff_locals` | 470 |
| Lemma | `mu3_unique_one_prime` | 491 |
| Theorem | `pin_cube_kernel_trivial` | 516 |
| Theorem | `cube_kernel_three` | 534 |
| Theorem | `omega_13_order_3` | 579 |
| Theorem | `mixed_kernel_pin_91` | 587 |
| Lemma | `cube_minus_one_fact` | 623 |
| Theorem | `mixed_mu3_gcd_xminus1` | 631 |
| Theorem | `mixed_mu3_gcd_phi3` | 652 |
| Theorem | `mixed_mu3_splits` | 687 |
| Theorem | `diagonal_mu3_gcd_xminus1` | 704 |
| Theorem | `diagonal_mu3_gcd_phi3` | 729 |
| Theorem | `mixed_kernel_pin_91_splits` | 752 |
| Theorem | `gq_kernel_pin_91_splits` | 757 |
| Theorem | `diagonal_pin_91_no_split` | 762 |
| Theorem | `phi3_small_omega_is_prime` | 767 |
| Theorem | `pin_mu3_gcd_is_N` | 771 |

## `CyclicCount.v`

- L9: Cyclic-model 2-height counts

| Kind | Name | Line |
|---|---|---:|
| Lemma | `sum_up_ext` | 43 |
| Lemma | `cyclic_count_agree_below` | 55 |
| Lemma | `cyclic_count_top` | 70 |
| Theorem | `cyclic_count_sum` | 80 |
| Theorem | `cyclic_mismatch_11_17` | 111 |
| Theorem | `miller_150_of_158` | 116 |
| Theorem | `cyclic_mismatch_14_is_15_16` | 121 |
| Theorem | `cyclic_mismatch_blum_11_19` | 127 |
| Theorem | `blum_mismatch_is_half` | 132 |
| Theorem | `cyclic_mismatch_33` | 137 |
| Theorem | `cyclic_mismatch_33_is_21_32` | 142 |

## `Cyclotomic.v`

- L10: Type B beyond [p±1]: cyclotomic periods [Φ_n(p)]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `cyc_p2_minus_1` | 32 |
| Lemma | `cyc_p3_minus_1` | 36 |
| Lemma | `cyc_p4_minus_1` | 40 |
| Lemma | `cyc_p6_minus_1` | 44 |
| Lemma | `cyc1_divides_p2_minus_1` | 50 |
| Lemma | `cyc2_divides_p2_minus_1` | 54 |
| Lemma | `cyc3_divides_p3_minus_1` | 58 |
| Lemma | `cyc1_divides_p3_minus_1` | 62 |
| Lemma | `cyc1_handle_is_p1` | 72 |
| Lemma | `cyc2_handle_is_williams` | 76 |
| Lemma | `cyc1_resistant_iff_p1` | 83 |
| Lemma | `cyc2_resistant_iff_pp1` | 87 |
| Lemma | `strong_prime_is_partial_cyc` | 104 |
| Lemma | `cyc3_pos` | 110 |
| Lemma | `cyc4_pos` | 114 |
| Lemma | `cyc6_pos_ge3` | 118 |

## `DamgardJurik.v`

- L10: Damgård–Jurik: the [s = 2] binomial on [N³]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `one_plus_N_pow_N3` | 19 |
| Theorem | `one_plus_N_pow_N3_div` | 31 |
| Theorem | `dj_add` | 47 |

## `Dark.v`

- L9: DARK-style openings in unknown order — exponent identities

| Kind | Name | Line |
|---|---|---:|
| Lemma | `poly1_factor` | 46 |
| Lemma | `poly2_factor` | 51 |
| Theorem | `dark_deg1_open` | 57 |
| Theorem | `dark_deg2_open` | 79 |
| Theorem | `dark_deg1_commit_is_powm` | 106 |
| Theorem | `dark_deg2_commit_is_powm` | 111 |

## `Derive.v`

- L17: Secure derivation into the no-handle class
  - L31: Area 1. The slice [S_b] and the index bijection
  - L171: Area 2. Unbiased index; biased shortcuts
  - L266: Area 3. Increment is not resample
  - L304: Area 4. A public map into one AP leaks [M]
  - L360: Area 5. Seeded auxiliaries: splitting conditions and domain sep
  - L405: Area 6. Reuse is publication
  - L436: Area 7. Placement as an interval on the second index
  - L499: Area 8. [e], [d], and a successful derivation
  - L588: Area 9. Named distributions

| Kind | Name | Line |
|---|---|---:|
| Lemma | `pow_pos_ge1` | 48 |
| Lemma | `range_lo_lt_hi` | 55 |
| Theorem | `in_S_b_is_ap` | 64 |
| Theorem | `ctor_in_S_b_iff_k` | 75 |
| Lemma | `div_ge_if_prod` | 91 |
| Theorem | `k_min_lower` | 102 |
| Theorem | `k_max_upper` | 121 |
| Theorem | `k_in_slice_of_S_b` | 137 |
| Theorem | `residue_in_range_is_k_zero` | 151 |
| Theorem | `regime_512_card_vs_M` | 164 |
| Theorem | `index_of_seed_in_interval` | 177 |
| Theorem | `index_of_seed_injective` | 183 |
| Theorem | `index_of_seed_surjective` | 189 |
| Theorem | `derive_candidate_in_S_b` | 195 |
| Theorem | `mod_hits_differ` | 215 |
| Theorem | `mod_bias_example` | 223 |
| Lemma | `two_hits_zero_one_hit_five` | 229 |
| Theorem | `force_residue_leaves_range_example` | 236 |
| Theorem | `slot_encode_unbounded_not_in_S_b` | 249 |
| Theorem | `increment_hits_first` | 276 |
| Theorem | `increment_from_min_skips_later` | 287 |
| Theorem | `resample_includes_every_slice_prime` | 298 |
| Theorem | `public_map_difference_divides` | 306 |
| Theorem | `public_two_outputs_leak_multiple` | 314 |
| Theorem | `gcd_of_index_diffs_divides_output_gcd` | 322 |
| Theorem | `no_public_hidden_class` | 334 |
| Theorem | `public_derive_is_roca` | 347 |
| Theorem | `domain_tag_separates` | 367 |
| Theorem | `cas28_aux_split_ready` | 375 |
| Theorem | `empty_slice_example` | 392 |
| Theorem | `reuse_gives_public_ap` | 409 |
| Theorem | `reuse_recovers_residue` | 420 |
| Theorem | `placement_implies_balanced` | 452 |
| Theorem | `placement_hi_enforces_far` | 466 |
| Theorem | `cas28_same_slot_not_placeable` | 481 |
| Theorem | `far_can_empty_placement` | 485 |
| Theorem | `derive_e_not_tiny` | 503 |
| Theorem | `derive_success_has_e` | 527 |
| Theorem | `large_d_if_not_wiener` | 533 |
| Theorem | `pocklington_needs_R_gt_sqrt` | 542 |
| Theorem | `B160_not_sqrt_of_512bit` | 549 |
| Theorem | `aux_at_B_not_pocklington_size` | 556 |
| Theorem | `rw_p_is_blum` | 573 |
| Theorem | `derive_e_fixed` | 585 |
| Theorem | `dist_public_slot_is_roca` | 593 |
| Theorem | `dist_reused_slot_leaks_M` | 606 |
| Theorem | `dist_force_residue_can_leave_range` | 621 |
| Theorem | `dist_seeded_slot_balanced` | 633 |
| Theorem | `long_seed_hits_every_index` | 649 |

## `DozenInroads.v`

- L20: Twelve algorithm-class inroads on Strong RSA
  - L27: 1. GRA plus a Jacobi gate
  - L39: 2. SAGM on both [x] and [y] in base [g=3]
  - L51: 3. Related queries with coprime exponents (Shamir)
  - L64: 4. Higher residue: 5th-power Euler on [p=11]
  - L74: 5. One-sided [a^{e-1}]
  - L88: 6. Short [e] vs long [e] on this pin
  - L98: 7. Bounded advice on [N]
  - L111: 8. Blum modulus [N=11·23], [λ=110]
  - L139: 9. Census: every unit is an [e=3] residual witness
  - L157: 10. GQ extract is residual, not a factor
  - L168: 11. Integer polynomial in [N]
  - L178: 12. [gcd(e−1, λ)] proper, not [λ] and not [2]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `dozen_jacobi_gate_minus1` | 31 |
| Theorem | `dozen_jacobi_gate_forces_odd` | 35 |
| Theorem | `dozen_sagm_both_pin` | 41 |
| Theorem | `dozen_sagm_ae_eq_c_mod_lambda` | 46 |
| Theorem | `dozen_related_coprime_exps` | 53 |
| Theorem | `dozen_related_shamir_gcd` | 58 |
| Theorem | `dozen_fifth_divides_pminus1` | 66 |
| Theorem | `dozen_fifth_power_euler` | 70 |
| Theorem | `dozen_onesided_e11` | 76 |
| Theorem | `dozen_e11_residual_shaped` | 84 |
| Theorem | `dozen_short_e3` | 90 |
| Theorem | `dozen_short_e_is_residual_cube` | 94 |
| Theorem | `dozen_advice_bit_no_split` | 100 |
| Theorem | `dozen_advice_div_splits` | 104 |
| Lemma | `prime_23` | 113 |
| Theorem | `dozen_blum_shape` | 125 |
| Theorem | `dozen_blum_e5_names_p` | 130 |
| Theorem | `dozen_blum_e11_names_q` | 134 |
| Theorem | `dozen_phi_160` | 141 |
| Theorem | `dozen_every_unit_is_cube` | 145 |
| Theorem | `dozen_gq_extract_is_residual` | 159 |
| Theorem | `dozen_gq_complete_still` | 164 |
| Theorem | `dozen_N_cong_q` | 170 |
| Theorem | `dozen_gcd_Nminus1_pminus1` | 174 |
| Theorem | `dozen_e11_minus1_shares_lambda` | 180 |

## `Endo.v`

- L14: Endomorphisms of [(Z/NZ)*] and of [Cl(Δ)]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `rsa_inverse_is_constructible` | 36 |
| Theorem | `cl_inverse_is_constructible` | 43 |
| Theorem | `rsa_gii_search_empty` | 52 |
| Theorem | `power_endo_hom` | 62 |
| Theorem | `power_endo_on_dlog` | 77 |
| Theorem | `power_endo_not_product_of_dlogs` | 90 |
| Theorem | `power_endo_next_forces_k` | 115 |

## `EulerQuotient.v`

- L10: The Euler quotient: [a^{N+1} ≡ a^{p+q} (mod N)]
  - L22: Reduction of [powm] along a factor
  - L238: Bits of [s] that are functions of [N], not of the quotient

| Kind | Name | Line |
|---|---|---:|
| Lemma | `powm_mod_divisor` | 24 |
| Lemma | `powm_mod_prime_factor` | 43 |
| Lemma | `powm_multiple` | 53 |
| Lemma | `not_coprime_prime_divides` | 69 |
| Lemma | `fermat_powm` | 82 |
| Lemma | `powm_Nplus1_mod_p` | 99 |
| Lemma | `powm_s_mod_p` | 116 |
| Lemma | `powm_Nplus1_eq_s_mod_p` | 131 |
| Lemma | `phi_plus_sum` | 140 |
| Theorem | `euler_quotient_units` | 144 |
| Theorem | `euler_quotient` | 162 |
| Lemma | `powm_reduce_to_qminus1` | 178 |
| Lemma | `powm_Nminus1_mod_p` | 212 |
| Theorem | `euler_quotient_pred` | 222 |
| Lemma | `prime_2` | 240 |
| Lemma | `odd_prime_mod2` | 247 |
| Theorem | `odd_primes_sum_even` | 258 |
| Lemma | `odd_prime_mod4` | 269 |
| Theorem | `sum_mod4_of_N` | 286 |
| Theorem | `euler_quotient_rsa` | 309 |

## `EvalPairing.v`

- L14: Evaluation pairing on [μ_n]: [e(x,k) = x^k]
  - L232: Alternating bilinear maps on cyclic [μ₃] are trivial
  - L476: Determinant pairing on [μ₃(Z/NZ)* ≅ C₃×C₃]
  - L550: Local [μ₃]-logs are additive, so [mu3N_det] is bilinear

| Kind | Name | Line |
|---|---|---:|
| Theorem | `eval_pair_stays_in_mu` | 44 |
| Theorem | `eval_pair_add` | 61 |
| Theorem | `eval_pair_mul_base` | 74 |
| Theorem | `eval_pair_reduce_mod_n` | 89 |
| Theorem | `eval_pair_image_divides_n` | 112 |
| Theorem | `eval_pair_mu2` | 122 |
| Theorem | `eval_pair_mu2_on_mixed` | 137 |
| Theorem | `omega_cube_is_one` | 152 |
| Theorem | `eval_pair_mu3` | 172 |
| Theorem | `mu2_is_mu6` | 185 |
| Theorem | `mu3_is_mu6` | 200 |
| Theorem | `eval_pair_mu6` | 215 |
| Lemma | `in_mu3_one` | 247 |
| Lemma | `in_mu3_mod` | 254 |
| Lemma | `pairing_one_left` | 262 |
| Lemma | `pairing_one_right` | 288 |
| Lemma | `two_omega_is_sq` | 314 |
| Lemma | `in_mu3_omega` | 326 |
| Lemma | `in_mu3_omega2` | 345 |
| Lemma | `pairing_omega_omega2` | 369 |
| Lemma | `pairing_omega2_omega` | 384 |
| Lemma | `pairing_omega2_omega2` | 399 |
| Theorem | `alternating_bilinear_mu3_trivial` | 412 |
| Theorem | `eval_pair_omega_13_not_alternating` | 464 |
| Theorem | `pin_mu3_only_one` | 468 |
| Lemma | `mu3_log_range` | 494 |
| Theorem | `mu3N_det_alternating` | 501 |
| Theorem | `gp_pin_91_order_3` | 515 |
| Theorem | `gq_pin_91_order_3` | 523 |
| Theorem | `mu3N_det_gp_gq` | 531 |
| Theorem | `mu3N_det_gq_gp` | 535 |
| Theorem | `mu3_pin_91_kernel_not_cyclic` | 540 |
| Lemma | `mu3_order_coprime` | 557 |
| Lemma | `mu3_order_divides_pminus1` | 577 |
| Lemma | `mu3_prime_ne_2` | 589 |
| Lemma | `mu3_pow_1_ne_2` | 600 |
| Lemma | `mu3_log_of_pow` | 624 |
| Lemma | `mu3_is_omega_power` | 660 |
| Lemma | `mu3_log_reconstructs` | 723 |
| Lemma | `mu3_log_mul` | 745 |
| Lemma | `zmod3_mul` | 786 |
| Lemma | `zmod3_mul_l` | 796 |
| Lemma | `det_exp_left_add` | 803 |
| Lemma | `det_exp_right_add` | 818 |
| Lemma | `mu3_log_mod_reduce` | 833 |
| Lemma | `mu3_log_base_mod` | 847 |
| Theorem | `omega_7_order_3` | 856 |
| Theorem | `pin_mu3_log_one` | 864 |
| Theorem | `mu3N_det_left_bilinear` | 867 |
| Theorem | `mu3N_det_right_bilinear` | 929 |
| Theorem | `mu3N_det_skew` | 991 |

## `EvalProduct.v`

- L12: Product of two committed evaluations at [τ]
  - L27: Coefficient polynomials, low term first
  - L104: The encoding [g^{f(τ)}]
  - L201: Monomials: the CRS already publishes [τ^i · τ^j]
  - L286: Self-bilinear map is a public product of encodings
  - L327: Two-wire witness encoding: [∏ U_j^{w_j} = g^{(w0 A0 + w1 A1)(τ)}]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `poly_eval_nonneg` | 39 |
| Lemma | `poly_eval_map_mul` | 52 |
| Lemma | `poly_eval_add` | 67 |
| Lemma | `poly_eval_shift` | 81 |
| Theorem | `poly_eval_conv` | 92 |
| Theorem | `pot_poly_is_eval` | 109 |
| Theorem | `pot_poly_add` | 114 |
| Theorem | `pot_poly_scale` | 128 |
| Theorem | `pot_poly_shift` | 143 |
| Theorem | `pot_poly_conv_raise` | 160 |
| Theorem | `pot_poly_conv_raise_comm` | 174 |
| Theorem | `pot_poly_mul_is_add` | 190 |
| Lemma | `nn_Xn` | 209 |
| Lemma | `poly_eval_Xn` | 216 |
| Theorem | `pot_poly_Xn` | 232 |
| Theorem | `monomial_eval_product` | 244 |
| Theorem | `monomial_conv_is_later_slot` | 258 |
| Theorem | `monomial_group_mul_is_sum` | 273 |
| Theorem | `self_bil_committed_product` | 288 |
| Theorem | `self_bil_monomial_product` | 310 |
| Theorem | `two_wire_commit` | 329 |
| Theorem | `two_wire_product_raise` | 347 |

## `ExpProof.v`

- L14: Proof of exponentiation, algebra only
  - L121: Presentation-level Wesolowski and Pietrzak

| Kind | Name | Line |
|---|---|---:|
| Theorem | `wesolowski_correct_is_root` | 34 |
| Theorem | `wesolowski_pi_is_ell_th_root` | 56 |
| Theorem | `pietrzak_mid_squares_to_y` | 75 |
| Theorem | `pietrzak_y_is_fourth_power` | 85 |
| Theorem | `pietrzak_forgery_is_low_order_shape` | 95 |
| Theorem | `pietrzak_on_Cl_may_be_constructible` | 111 |
| Theorem | `pietrzak_restricted_ignores_Cl2` | 115 |
| Theorem | `wesolowski_verify_rsa_agrees` | 127 |
| Theorem | `wesolowski_correct_is_PRoot` | 138 |
| Theorem | `verifying_pi_is_adaptive_root` | 158 |
| Theorem | `pietrzak_quotient_squares_to_one_rsa` | 175 |
| Theorem | `pietrzak_quotient_on_Cl_may_be_ambiguous` | 196 |
| Theorem | `form_neg87_ord3_of_disc` | 210 |
| Theorem | `wesolowski_on_Cl_exp` | 216 |
| Theorem | `wesolowski_root_does_not_need_prime_ell` | 227 |
| Theorem | `wesolowski_verify_does_not_need_prime_ell` | 236 |
| Lemma | `powm_opp_odd` | 257 |
| Theorem | `wesolowski_odd_challenge_accepts_negation` | 273 |
| Theorem | `wesolowski_soundness_fails_on_units_odd_challenge` | 303 |

## `ExtraRelations.v`

- L14: Extra search relations: one-more RSA, GHR prime-[e], φ-hiding
  - L19: One-more RSA
  - L48: GHR: prime public [e]
  - L87: φ-hiding: [e | λ(N)], a relation, not a PPT game

| Kind | Name | Line |
|---|---|---:|
| Theorem | `one_more_pin` | 30 |
| Theorem | `one_more_queried_is_not_extra` | 41 |
| Lemma | `prime_3` | 53 |
| Theorem | `ghr_pin` | 61 |
| Theorem | `ghr_is_rsa` | 68 |
| Theorem | `ghr_prime_e_shamir_gcd` | 72 |
| Theorem | `ghr_shamir_gcd_pin` | 83 |
| Theorem | `phi_hiding_lambda_80` | 92 |
| Theorem | `phi_hiding_pin_e5` | 96 |
| Theorem | `phi_hiding_public_e3_misses` | 103 |

## `FactorEnum.v`

- L10: Multiplier enumeration: factor [N] from [(e,d)] when [e] is small

| Kind | Name | Line |
|---|---|---:|
| Lemma | `enum_recovers_when_phi` | 32 |
| Lemma | `enum_k_from_phi_multiple` | 47 |
| Lemma | `phi_divides_ed_minus_1_if_d_inv_mod_phi` | 65 |
| Theorem | `rsa_test_enum_from_phi` | 88 |
| Theorem | `rsa_test_ed_minus_1_is_lambda` | 96 |

## `FermatFactor.v`

- L10: Fermat factoring: close primes make [N] a near-square

| Kind | Name | Line |
|---|---|---:|
| Lemma | `odd_prime_ge_3` | 21 |
| Lemma | `odd_add_even` | 26 |
| Lemma | `odd_sub_even` | 35 |
| Lemma | `prime_odd_if_ne_2` | 44 |
| Theorem | `fermat_identity` | 57 |
| Theorem | `fermat_square_gap` | 76 |
| Lemma | `ceil_sqrt_ge` | 92 |
| Lemma | `ceil_sqrt_le_of_square` | 102 |
| Lemma | `fermat_sum_ge_ceil_sqrt` | 116 |
| Theorem | `fermat_recovers` | 144 |
| Lemma | `fermat_diff_abs` | 171 |
| Theorem | `far_apart_large_diff` | 184 |
| Theorem | `fermat_square_gap_from_diff` | 195 |

## `FiatShamir.v`

- L17: Fiat–Shamir compilation of the public-coin Sigma
  - L30: Deterministic challenge map (not a hash oracle)
  - L161: Slot Sigma of the proving system
  - L195: Representative pin: challenge depends on the first message

| Kind | Name | Line |
|---|---|---:|
| Lemma | `fs_step_nonneg` | 43 |
| Lemma | `fs_fold_nonneg` | 52 |
| Lemma | `fs_challenge_nonneg` | 65 |
| Lemma | `fs_eqdl_challenge_nonneg` | 79 |
| Lemma | `eqdl_verifyb_iff` | 114 |
| Lemma | `fs_eqdl_verifyb_iff` | 124 |
| Theorem | `fs_eqdl_complete` | 133 |
| Theorem | `fs_eqdl_complete_b` | 148 |
| Theorem | `fs_slot_complete` | 163 |
| Theorem | `fs_wire_complete` | 180 |
| Theorem | `fs_pin_accepts` | 209 |
| Theorem | `fs_pin_rejects_wrong_challenge` | 213 |
| Theorem | `fs_pin_challenge_depends_on_commit` | 222 |
| Theorem | `fs_pin_second_accepts` | 229 |
| Theorem | `fs_pin_commits_distinct` | 233 |

## `FilterShape.v`

- L15: Twelve partial-root, public-stand-in, and filter inroads
  - L23: 1. One-sided local root as an integer
  - L41: 2. [x = −y]
  - L51: 3. Euclid on [(y±1, N)]
  - L61: 4. Nontrivial [e]-th root of 1 at [gcd(e,λ)>1]
  - L76: 5. Public period [N+1]
  - L85: 6. Extra output [φ]
  - L101: 7. 2-adic Hensel: [v₂(y)] not divisible by 3
  - L111: 8. Locally constant [X] ([y] modulo [m])
  - L117: 9. Branch on Jacobi to [λ+1]
  - L127: 10. Public coprimality filter [gcd(e, N−1)=1]
  - L147: 11. Low-bit [e = 2(y mod 2^k)+1]
  - L163: 12. Trace [x + x^{-1}]
  - L173: Public tests of [e] vs residual tests that mention [λ]
  - L245: Public tests of leftover [x]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `filter_onesided_local_mod_p` | 25 |
| Theorem | `filter_onesided_not_global` | 29 |
| Theorem | `filter_onesided_integer_splits` | 33 |
| Theorem | `filter_neg_y_not_cube_root` | 43 |
| Theorem | `filter_y_square_not_minus1` | 47 |
| Theorem | `filter_euclid_y_minus_1` | 53 |
| Theorem | `filter_euclid_y_plus_1` | 57 |
| Theorem | `filter_fifth_shares_lambda` | 63 |
| Theorem | `filter_fifth_root_of_1_splits` | 68 |
| Theorem | `filter_Nplus1_does_not_annihilate` | 78 |
| Theorem | `filter_phi_gives_sum` | 87 |
| Theorem | `filter_phi_enum_factors` | 92 |
| Theorem | `filter_phi_is_factor` | 97 |
| Theorem | `filter_val2_36` | 103 |
| Theorem | `filter_val2_not_div_by_3` | 107 |
| Theorem | `filter_locally_constant_clash` | 113 |
| Theorem | `filter_jacobi_branch_lambda_type` | 119 |
| Theorem | `filter_jacobi_branch_not_residual` | 123 |
| Theorem | `filter_cube_fails_public_e` | 131 |
| Theorem | `filter_e11_passes_public_e` | 135 |
| Theorem | `filter_public_e11_miller_splits` | 139 |
| Theorem | `filter_lowbit_e9` | 151 |
| Theorem | `filter_lowbit_e9_residual` | 155 |
| Theorem | `filter_lowbit_root_is_70` | 159 |
| Theorem | `filter_trace_not_root` | 165 |
| Theorem | `filter_torus_order_not_Nplus1` | 169 |
| Theorem | `filter_residual_tests_on_cube` | 180 |
| Theorem | `filter_e5_shares_lambda` | 190 |
| Theorem | `filter_e15_odd_shares_lambda` | 195 |
| Theorem | `filter_e7_residual_shaped` | 200 |
| Theorem | `filter_e5_passes_public_e` | 210 |
| Theorem | `filter_e7_passes_public_e` | 214 |
| Theorem | `filter_e_coprime_N_cube_passes` | 218 |
| Theorem | `filter_e_coprime_N_accepts_nonresidual` | 222 |
| Theorem | `filter_e_coprime_N_does_not_certify` | 227 |
| Theorem | `filter_phi_y_of_36` | 232 |
| Theorem | `filter_e_coprime_phi_y_rejects_cube` | 240 |
| Theorem | `filter_jacobi_x_plus` | 252 |
| Theorem | `filter_jacobi_10_plus_not_leftover` | 257 |
| Theorem | `filter_jacobi_2_minus` | 261 |
| Theorem | `filter_x_cube_check_is_rsa_e3` | 266 |

## `Fp2.v`

- L13: [F_p[√D]] and [V_{p+1} ≡ 2] when [D] is a QNR
  - L356: Binomial coefficients and Freshman's dream

| Kind | Name | Line |
|---|---|---:|
| Lemma | `fp2_eq_refl` | 48 |
| Lemma | `fp2_mul_embed_l` | 51 |
| Lemma | `fp2_add_conj` | 57 |
| Lemma | `fp2_mul_conj` | 61 |
| Lemma | `inv2_exists` | 66 |
| Lemma | `alpha_plus_beta` | 92 |
| Lemma | `alpha_mul_beta` | 97 |
| Lemma | `alpha_beta_is_one` | 104 |
| Lemma | `alpha_plus_beta_is_P` | 124 |
| Lemma | `fp2_pow_0` | 144 |
| Lemma | `fp2_pow_1` | 147 |
| Lemma | `fp2_mul_one_r` | 150 |
| Lemma | `fp2_mul_comm` | 154 |
| Lemma | `fp2_eq_trans` | 158 |
| Lemma | `fp2_eq_sym` | 163 |
| Lemma | `opp_mod_compat` | 167 |
| Lemma | `fp2_eq_opp` | 178 |
| Lemma | `fp2_pow_succ` | 192 |
| Lemma | `fp2_eq_mul` | 196 |
| Lemma | `fp2_eq_opp_mul` | 226 |
| Lemma | `fp2_eq_add` | 236 |
| Lemma | `fp2_mul_assoc` | 250 |
| Lemma | `fp2_mul_add_r` | 258 |
| Lemma | `fp2_mul_add_l` | 266 |
| Lemma | `fp2_pow_add_r` | 274 |
| Lemma | `fp2_pow_SS` | 283 |
| Lemma | `alpha_beta_rec` | 288 |
| Lemma | `lucasV_as_fp2` | 312 |
| Lemma | `binom_n_0` | 368 |
| Lemma | `binom_0_S` | 371 |
| Lemma | `binom_gt` | 374 |
| Lemma | `binom_n_n` | 382 |
| Lemma | `binom_n_1` | 388 |
| Lemma | `binom_S_S_expand` | 394 |
| Lemma | `binom_mul_row` | 398 |
| Lemma | `prime_divides_binom` | 418 |
| Lemma | `fp2_scale_as_mul` | 444 |
| Lemma | `fp2_scale_add` | 451 |
| Lemma | `fp2_eq_scale` | 459 |
| Lemma | `fp2_eq_scale_mod` | 469 |
| Lemma | `fp2_scale_p_zero` | 483 |
| Lemma | `fp2_scale_mul_div` | 493 |
| Lemma | `fp2_eq_sum` | 512 |
| Lemma | `fp2_sum_zero` | 524 |
| Lemma | `fermat_pow_id` | 541 |
| Lemma | `fp2_pow_sqrt_even` | 568 |
| Lemma | `fp2_pow_sqrt_odd` | 583 |
| Lemma | `nat_odd_prime` | 596 |
| Lemma | `fp2_pow_sqrt_p` | 613 |
| Lemma | `fp2_mul_embed_embed` | 630 |
| Lemma | `fp2_mul_embed_comm` | 637 |
| Lemma | `fp2_embed_pow` | 642 |
| Lemma | `fp2_scale_pow` | 654 |
| Lemma | `zsum_ext` | 677 |
| Lemma | `zsum_mod` | 688 |
| Lemma | `zsum_zero_mod` | 700 |
| Lemma | `gamma_split` | 719 |
| Lemma | `alpha_as_scale` | 723 |
| Lemma | `beta_as_scale` | 730 |
| Lemma | `zsum_uncons` | 737 |
| Lemma | `zsum_mul_l` | 746 |
| Lemma | `zsum_add` | 754 |
| Lemma | `zsum_shift` | 762 |
| Lemma | `zsum_pad` | 771 |
| Lemma | `z_binom` | 777 |
| Lemma | `z_freshman` | 807 |
| Lemma | `fp2_sum_uncons` | 854 |
| Lemma | `fp2_sum_shift` | 867 |
| Lemma | `fp2_sum_pad` | 876 |
| Lemma | `fp2_sum_add` | 883 |
| Lemma | `fp2_mul_scale` | 895 |
| Lemma | `fp2_scale_zero` | 903 |
| Lemma | `fp2_sum_ext_eq` | 910 |
| Lemma | `fp2_sum_scale_mul` | 921 |
| Lemma | `fp2_binterm_gt` | 930 |
| Lemma | `fp2_binom` | 939 |
| Lemma | `fp2_scale_one` | 989 |
| Lemma | `fp2_freshman` | 993 |
| Lemma | `fp2_eq_embed` | 1043 |
| Lemma | `fp2_pow_S_to_nat` | 1050 |
| Lemma | `euler_pow_half` | 1061 |
| Lemma | `fp2_conj_mul_ok` | 1068 |
| Lemma | `fp2_pow_conj` | 1075 |
| Lemma | `gamma_pow_p` | 1084 |
| Lemma | `alpha_pow_p_is_beta` | 1116 |
| Lemma | `beta_is_conj_alpha` | 1145 |
| Lemma | `fp2_conj_one` | 1149 |
| Lemma | `fp2_eq_conj` | 1153 |
| Theorem | `williams_eval_of_qnr` | 1165 |

## `GQ.v`

- L14: Guillou–Quisquater: PoK of an [e]-th root

| Kind | Name | Line |
|---|---|---:|
| Theorem | `gq_complete` | 31 |
| Lemma | `gq_ratio_is_delta_power` | 51 |
| Theorem | `gq_extract` | 91 |
| Theorem | `publishing_mixed_sqrt1_factors` | 123 |
| Theorem | `gq_on_one_with_mixed_sqrt_is_factorization` | 141 |
| Theorem | `gq_e2_complete` | 161 |
| Theorem | `gq_e2_odd_delta_extracts_sqrt` | 173 |

## `GenericGroup.v`

- L15: Unknown-order generic group interpreter

| Kind | Name | Line |
|---|---|---:|
| Theorem | `ggm_add_uninhabited` | 48 |
| Theorem | `ggm_step_is_mul_inv_or_eq` | 52 |
| Theorem | `ggm_init_is_one_and_y` | 72 |
| Theorem | `ggm_pow10_handle` | 76 |
| Theorem | `ggm_eq_leak_from_tape` | 80 |
| Theorem | `ggm_eq_leak_factors` | 84 |
| Theorem | `ggm_yyy_pin` | 93 |

## `GenericRing.v`

- L18: Generic ring algorithms (GRA) on [Z/NZ]
  - L26: The machine
  - L101: Wave 0 — equality leak and the tape
  - L188: Division-free tapes denote polynomials
  - L341: Degree bound of a nodiv tape
  - L489: Wave 1 — Leander–Rupp, no division, low [e]
  - L531: Wave 2a — AM09 inversion leak and leading term
  - L583: Wave 2b — AMS flexible [e]; [λ+1] is a constant, not a ring op on [y]
  - L620: Wave 6a — Damgård–Koprowski signature contrast

| Kind | Name | Line |
|---|---|---:|
| Theorem | `gra_eq_tape_88` | 115 |
| Theorem | `gra_eq_tape_zero` | 119 |
| Theorem | `gra_eq_leak_pin` | 123 |
| Theorem | `gra_eq_leak_factors` | 127 |
| Theorem | `gra_eq_leak_onesided` | 135 |
| Theorem | `gra_eq_N_is_not_a_split` | 139 |
| Theorem | `gra_mul_y_pin` | 143 |
| Theorem | `gra_const42` | 147 |
| Theorem | `slp_init_eval` | 172 |
| Theorem | `slp_to_poly_mul_pin` | 183 |
| Lemma | `nth_app_last` | 201 |
| Lemma | `nth_app_lt` | 208 |
| Lemma | `step_length` | 216 |
| Lemma | `step_poly_length` | 220 |
| Lemma | `step_nodiv_prefix` | 224 |
| Lemma | `step_nodiv_new` | 238 |
| Lemma | `step_nodiv_overflow` | 258 |
| Lemma | `step_nodiv_agree` | 271 |
| Lemma | `gra_run_nodiv_agree` | 291 |
| Lemma | `slp_init_length` | 308 |
| Lemma | `gra_init_length` | 311 |
| Lemma | `gra_init_agrees` | 314 |
| Theorem | `gra_nodiv_denotes` | 327 |
| Lemma | `slp_init_deg_le` | 366 |
| Lemma | `step_deg_bound_length` | 378 |
| Lemma | `step_nodiv_degree_le` | 382 |
| Lemma | `gra_run_poly_length` | 413 |
| Lemma | `gra_nodiv_degree_le` | 421 |
| Theorem | `gra_deg_bound_identity` | 446 |
| Theorem | `gra_deg_bound_square` | 450 |
| Theorem | `gra_deg_bound_x3` | 454 |
| Theorem | `gra_deg_bound_x4` | 458 |
| Theorem | `gra_nodiv_mul_is_nodiv` | 462 |
| Theorem | `gra_nodiv_mul_denotes_square` | 466 |
| Theorem | `gra_nodiv_integer_eth_root_forbidden` | 473 |
| Theorem | `gra_nodiv_const42_inverts_36` | 491 |
| Theorem | `gra_nodiv_const42_fails_on_8` | 495 |
| Theorem | `gra_identity_not_cube_root_at_2` | 499 |
| Theorem | `gra_identity_at_one` | 503 |
| Theorem | `gra_identity_gcd_at_2` | 507 |
| Theorem | `gra_nodiv_identical_X3_linear` | 511 |
| Theorem | `gra_nodiv_N_does_not_divide_minus1` | 515 |
| Theorem | `gra_nodiv_identical_root_impossible_X3` | 519 |
| Theorem | `Pe_minus_X_eval2_is_six_on_X` | 527 |
| Theorem | `gra_inv_nonunit_pin` | 540 |
| Theorem | `gra_inv_nonunit_factors` | 544 |
| Theorem | `gra_inv_22_from_tape` | 551 |
| Theorem | `gra_inv_unit_gcd` | 555 |
| Theorem | `gra_inv_unit_from_tape` | 559 |
| Theorem | `gra_fixed_e_leading_const` | 563 |
| Theorem | `gra_fixed_e_leading` | 567 |
| Theorem | `rsa_inverter_is_not_a_GRA_comment` | 573 |
| Theorem | `powm_d_inverts_cube_pin` | 579 |
| Theorem | `gra_const_81` | 585 |
| Theorem | `gra_const_lambda_plus_one_solves_sRSA_without_factoring` | 590 |
| Theorem | `gra_const_81_does_not_factor` | 600 |
| Theorem | `lambda_plus_one_is_81` | 604 |
| Theorem | `gra_add_mul_of_36_is_not_81` | 608 |
| Theorem | `am09_fixed_e_is_a_parameter` | 614 |
| Theorem | `gadd_is_not_a_ggm_op` | 630 |
| Theorem | `gsub_is_not_a_ggm_op` | 634 |
| Theorem | `gconst_is_not_a_ggm_op` | 638 |
| Theorem | `gra_poly_construction_needs_add` | 642 |
| Theorem | `generic_group_does_not_separate_rsa_from_srsa` | 646 |
| Theorem | `ggm_mul_pin` | 653 |

## `Hardness.v`

- L12: Relation-level structure of the named problems
  - L28: Factoring as a relation
  - L33: RSA is a one-way permutation on units, not a predicate
  - L62: RSA vs strong RSA (relations)
  - L136: Order divides the exponent
  - L183: One-sided small exponent (the Type-B winning condition)
  - L245: Order assumption and fractional root
  - L459: Order → Strong RSA by invert in the cyclic (equality / multiply)

| Kind | Name | Line |
|---|---|---:|
| Theorem | `rsa_units_are_eth_powers` | 39 |
| Theorem | `trapdoor_inverts_RSA` | 50 |
| Theorem | `rsa_solution_is_strong_RSA` | 83 |
| Theorem | `lambda_solves_strong_RSA` | 97 |
| Lemma | `strong_RSA_trivial_at_one` | 121 |
| Lemma | `rsa_trivial_at_one` | 129 |
| Lemma | `order_divides_annihilator` | 138 |
| Theorem | `order_divides_lambda` | 167 |
| Theorem | `one_sided_low_order_factors` | 195 |
| Theorem | `one_sided_low_order_is_factor` | 227 |
| Lemma | `adaptive_root_is_strong_RSA` | 240 |
| Theorem | `order_is_annihilator` | 251 |
| Theorem | `low_order_is_annihilator` | 260 |
| Theorem | `lambda_is_annihilator_on_units` | 269 |
| Theorem | `annihilator_plus_one_is_strong_RSA` | 282 |
| Theorem | `rsa_is_fractional_root` | 299 |
| Theorem | `strong_RSA_is_fractional_root` | 315 |
| Theorem | `annihilator_is_fractional_root_of_one` | 330 |
| Theorem | `ar_C_implies_strong_RSA` | 359 |
| Theorem | `ar_C_requires_C` | 368 |
| Theorem | `strong_RSA_is_ar_C_iff` | 373 |
| Theorem | `lambda_plus_one_11_17` | 384 |
| Theorem | `lambda_plus_one_11_17_not_prime` | 388 |
| Theorem | `lambda_solves_search_11_17` | 397 |
| Theorem | `search_lambda_plus_one_misses_prime_AR` | 408 |
| Theorem | `adaptive_root_known_product_breaks` | 426 |
| Theorem | `adaptive_root_smooth_power_breaks` | 442 |
| Theorem | `order_inverts_in_cyclic` | 465 |
| Theorem | `order_yields_strong_RSA` | 490 |
| Lemma | `gcd_powm_minus_1` | 513 |
| Theorem | `leftover_mismatch_factors` | 526 |

## `HashSlot.v`

- L14: Slot encoding: the generator lands only on the constructor AP
  - L120: Placement is not the encoding
  - L156: Try-and-increment is a filter spec, not a program

| Kind | Name | Line |
|---|---|---:|
| Theorem | `slot_encode_in_image` | 34 |
| Theorem | `slot_encode_rulers` | 39 |
| Theorem | `slot_accept_implies_rulers` | 55 |
| Theorem | `slot_reject_is_composite` | 69 |
| Theorem | `slot_encode_public_ap` | 82 |
| Theorem | `public_slot_encode_is_roca` | 91 |
| Theorem | `public_encode_admits_ap_test` | 103 |
| Theorem | `public_slot_encode_ap_budget` | 108 |
| Theorem | `cas28_seeds_not_balanced` | 125 |
| Theorem | `slot_encode_does_not_place` | 129 |
| Theorem | `pair_encode_does_not_force_balance` | 144 |
| Theorem | `slot_try_sound` | 163 |
| Theorem | `slot_try_complete` | 183 |

## `Inner2.v`

- L15: Inner product of two pairs: [s = x0·y0 + x1·y1]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `inner2_sat` | 24 |
| Theorem | `inner2_complete` | 46 |
| Theorem | `inner2_public_sum` | 67 |

## `JagerSchwenk.v`

- L17: Jager–Schwenk: Jacobi is standard-easy and not a GRA polynomial

| Kind | Name | Line |
|---|---|---:|
| Theorem | `jacobi_one_pin` | 27 |
| Theorem | `jacobi_two_pin` | 31 |
| Theorem | `jacobi_two_values` | 35 |
| Theorem | `jacobi_is_standard_easy` | 39 |
| Theorem | `jacobi_is_not_a_constant_polynomial` | 43 |
| Theorem | `jacobi_is_not_a_ring_polynomial` | 51 |
| Theorem | `jacobi_three_pin` | 56 |
| Theorem | `jacobi_five_pin` | 60 |
| Theorem | `lagrange_125_at_1` | 73 |
| Theorem | `lagrange_125_at_2` | 76 |
| Theorem | `lagrange_125_at_5` | 79 |
| Theorem | `lagrange_125_at_3` | 82 |
| Theorem | `gra_jacobi_not_deg2_fit` | 85 |

## `JouxNaccacheThome.v`

- L10: Joux–Naccache–Thomé affine-root oracle

| Kind | Name | Line |
|---|---|---:|
| Theorem | `jnt_roots_affine` | 19 |
| Theorem | `jnt_affine_is_plain_cube` | 23 |
| Theorem | `jnt_not_a_general_root` | 27 |
| Theorem | `jnt_general_roots_plain_cubes` | 31 |
| Theorem | `jnt_c0_is_general` | 35 |

## `KeyGen.v`

- L15: Key-generation intent-spec
  - L111: Refusal lemmas: each generation obligation blocks one leak.

| Kind | Name | Line |
|---|---|---:|
| Lemma | `balanced_sum_bound` | 69 |
| Lemma | `balanced_q_le_sqrt` | 77 |
| Theorem | `balanced_sum_vs_sqrt` | 91 |
| Lemma | `balanced_implies_odd_candidates` | 102 |
| Theorem | `keygen_refuses_wiener` | 113 |
| Theorem | `keygen_refuses_smooth_p` | 121 |
| Theorem | `keygen_refuses_smooth_q` | 131 |
| Theorem | `p1_resistant_not_smooth` | 141 |
| Theorem | `keygen_p1_not_smooth` | 151 |
| Theorem | `keygen_far_large_fermat_diff` | 164 |
| Theorem | `small_prime_le_sqrt` | 185 |
| Theorem | `tiny_e_is_degree` | 199 |
| Theorem | `balanced_wiener_sufficient` | 206 |

## `KeyGenCtor.v`

- L17: A constructor whose image is the no-handle set
  - L329: Raw pair (CRT walk only) and placed pair (keygen)
  - L398: Key: placed pair plus [e,d]
  - L482: Discriminators
  - L543: Parameter statement (AP enumeration, not NFS)

| Kind | Name | Line |
|---|---|---:|
| Lemma | `sa_prime_ge_2` | 61 |
| Lemma | `sa_mod_pos` | 64 |
| Lemma | `sa_r_divides_mod` | 74 |
| Lemma | `sa_s_divides_mod` | 77 |
| Lemma | `sa_u_divides_mod` | 80 |
| Lemma | `sa_v_divides_mod` | 83 |
| Lemma | `sa_w_divides_mod` | 86 |
| Lemma | `four_divides_mod` | 89 |
| Lemma | `ctor_plus_mod` | 107 |
| Lemma | `ctor_prime_mod_r` | 118 |
| Lemma | `ctor_prime_mod_s` | 129 |
| Lemma | `ctor_prime_mod_4` | 141 |
| Theorem | `ctor_r_divides_pminus1` | 151 |
| Theorem | `ctor_s_divides_pplus1` | 164 |
| Theorem | `ctor_is_blum_mod4` | 177 |
| Lemma | `cyc3_of_ctor` | 181 |
| Lemma | `cyc4_of_ctor` | 189 |
| Lemma | `cyc6_of_ctor` | 196 |
| Theorem | `ctor_u_divides_phi3` | 203 |
| Theorem | `ctor_v_divides_phi4` | 215 |
| Theorem | `ctor_w_divides_phi6` | 227 |
| Theorem | `ctor_p1_resistant` | 239 |
| Theorem | `ctor_pp1_resistant` | 251 |
| Theorem | `ctor_p3_resistant` | 263 |
| Theorem | `ctor_p4_resistant` | 276 |
| Theorem | `ctor_p6_resistant` | 289 |
| Theorem | `ctor_cyc_strong` | 302 |
| Theorem | `ctor_strong` | 318 |
| Theorem | `placed_p1_strong` | 364 |
| Theorem | `placed_pp1_strong` | 374 |
| Theorem | `placed_cyc_strong` | 384 |
| Theorem | `ctor_rsa_p` | 432 |
| Theorem | `ctor_key_satisfies` | 443 |
| Theorem | `ctor_key_satisfies_filter` | 475 |
| Theorem | `in_slot_image_on_ap` | 487 |
| Theorem | `slot_image_is_public_ap` | 506 |
| Theorem | `slot_image_has_secret_aux` | 529 |
| Theorem | `ap_candidates_bound` | 547 |
| Theorem | `public_ap_div_le_shift` | 560 |
| Theorem | `public_ap_search_bits` | 576 |
| Theorem | `regime_1024_ap_budget` | 599 |

## `KeyGenGeom.v`

- L11: Type A geometries that modern keygens actually commit

| Kind | Name | Line |
|---|---|---:|
| Theorem | `shared_high_bits_bound` | 30 |
| Theorem | `shared_high_bits_fails_far` | 45 |
| Theorem | `increment_window_bound` | 62 |
| Theorem | `increment_window_fails_far` | 70 |
| Theorem | `adjacent_fermat_diff` | 86 |
| Theorem | `adjacent_fails_far_ge2` | 98 |

## `KeyGenSampler.v`

- L19: Named key-generation distributions, measured against the rulers

| Kind | Name | Line |
|---|---|---:|
| Theorem | `dist_close_pair_fails_far` | 31 |
| Theorem | `dist_twin_odd_fails_far` | 45 |
| Theorem | `dist_shared_prefix_fails_far` | 58 |
| Theorem | `dist_increment_fails_far` | 73 |
| Theorem | `dist_safe_p_resists_p1` | 89 |
| Theorem | `dist_shared_pool_gcd` | 104 |
| Theorem | `dist_smooth_has_public_annihilator` | 118 |
| Lemma | `dist_cyc3_leak_not_p3_resistant` | 136 |
| Theorem | `dist_small_d_fails_large_d` | 149 |
| Theorem | `dist_independent_passes_geom` | 163 |

## `Lattice.v`

- L11: Lattice / Coron–May interface

| Kind | Name | Line |
|---|---|---:|
| Theorem | `lattice_phi_factors` | 28 |
| Theorem | `lattice_sum_factors` | 39 |
| Lemma | `phi_from_k_correct` | 54 |

## `Lucas.v`

- L10: Lucas [V] and the Williams [p+1] period

| Kind | Name | Line |
|---|---|---:|
| Lemma | `lucasV_0` | 32 |
| Lemma | `lucasV_1` | 35 |
| Lemma | `lucasV_rec` | 38 |
| Lemma | `lucasV_2` | 43 |
| Lemma | `lucasV_succ` | 47 |
| Theorem | `lucasV_add` | 59 |
| Theorem | `lucasV_double` | 106 |
| Theorem | `lucasV_double_Q1` | 116 |
| Theorem | `lucasV_double_Q1_table` | 125 |
| Theorem | `williams_handle_is_cyc2` | 139 |
| Theorem | `safe_prime_refuses_pminus1_only` | 143 |
| Theorem | `lucas_period_is_cyc2` | 155 |
| Lemma | `lucasV_add_Q1` | 167 |
| Theorem | `williams_eval_k_times` | 177 |
| Theorem | `williams_eval_on_multiples` | 202 |
| Theorem | `pp1_resistant_is_torus_period` | 219 |
| Theorem | `typeB_n2_is_williams_period` | 223 |

## `Miller.v`

- L12: Miller successive-squaring: factor [N] from a multiple of [λ(N)]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `miller_M_pos` | 26 |
| Lemma | `miller_M_split` | 29 |
| Lemma | `miller_t_nonneg` | 36 |
| Lemma | `miller_M_annihilates` | 42 |
| Theorem | `miller_witness_factors` | 73 |
| Theorem | `rsa_test_miller_split` | 104 |
| Theorem | `rsa_test_miller_t` | 107 |
| Theorem | `rsa_test_miller_s` | 110 |
| Theorem | `rsa_test_base2_splits` | 114 |

## `MillerHeight.v`

- L13: Miller-from-[d] as 2-heights on an odd multiple of [odd_part(λ)]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `miller_t_pos` | 24 |
| Lemma | `miller_t_odd` | 30 |
| Lemma | `miller_t_multiple_of_lambda_odd` | 36 |
| Lemma | `powm_one_mod_factor` | 54 |
| Theorem | `miller_height_exists` | 67 |
| Theorem | `miller_from_d` | 104 |
| Theorem | `miller_from_d_q` | 125 |
| Theorem | `rsa_test_base2_heights` | 148 |
| Theorem | `rsa_test_miller_from_d` | 168 |

## `MillerRabin.v`

- L11: Miller–Rabin polarity

| Kind | Name | Line |
|---|---|---:|
| Lemma | `mr_split` | 28 |
| Lemma | `miller_mr_same_engine` | 48 |
| Theorem | `mr_nontrivial_sqrt_factors` | 63 |
| Theorem | `mr_fermat_on_prime` | 84 |

## `MulGate.v`

- L13: One multiplication gate as a QAP

| Kind | Name | Line |
|---|---|---:|
| Lemma | `mul_Aw` | 39 |
| Lemma | `mul_Bw` | 47 |
| Lemma | `mul_Cw` | 55 |
| Lemma | `mul_eval_Aw` | 63 |
| Lemma | `mul_eval_Bw` | 68 |
| Lemma | `mul_eval_Cw` | 73 |
| Theorem | `mul_gate_sat` | 78 |
| Theorem | `mul_gate_complete` | 92 |
| Lemma | `mul_wires_nn` | 115 |
| Theorem | `bit_sat` | 141 |
| Theorem | `bit_complete` | 154 |

## `MultiPrime.v`

- L13: Multi-prime stress test: [N = pqr] has eight roots of [1]
  - L249: Constructive eight roots
  - L388: [λ(pqr)] annihilates units; a one-sided period still splits

| Kind | Name | Line |
|---|---|---:|
| Theorem | `two_prime_sqrt1_is_pm1_each` | 25 |
| Theorem | `three_prime_sqrt1_is_pm1_each` | 33 |
| Theorem | `eight_pats_length` | 77 |
| Theorem | `two_prime_arity_is_four` | 80 |
| Theorem | `two_sylow_is_two_prime` | 88 |
| Lemma | `prime_gcd_1` | 95 |
| Lemma | `crt_coprime_exists` | 104 |
| Lemma | `crt2_exists` | 129 |
| Lemma | `mod_mod_product` | 143 |
| Lemma | `three_prime_pq_coprime_r` | 157 |
| Lemma | `crt3_exists` | 166 |
| Theorem | `mixed_triple_splits` | 198 |
| Lemma | `crt3_mod` | 257 |
| Lemma | `sign_residue_pm1` | 290 |
| Lemma | `square_mod_one_of_pm1` | 294 |
| Lemma | `eight_sqrt1_mod` | 310 |
| Theorem | `eight_sqrt1_squares` | 323 |
| Theorem | `mixed_pqr_splits` | 364 |
| Lemma | `lambda_threeprime_divides_pminus1` | 393 |
| Lemma | `lambda_threeprime_divides_qminus1` | 402 |
| Lemma | `lambda_threeprime_divides_rminus1` | 411 |
| Lemma | `lambda_threeprime_pos` | 415 |
| Lemma | `crt_one_three` | 430 |
| Theorem | `carmichael_threeprime` | 458 |
| Theorem | `onesided_period_splits_triple` | 500 |

## `Mux.v`

- L16: Select: [mux s a b = s·a + (1−s)·b]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `mux_on_zero` | 25 |
| Theorem | `mux_on_one` | 29 |
| Theorem | `mux_select` | 33 |
| Theorem | `mux_nonneg` | 44 |
| Theorem | `mux_gates` | 55 |
| Theorem | `mux_complete` | 77 |

## `NamedSkips.v`

- L6: First-class skips and live targets

## `OkamotoUchiyama.v`

- L10: Okamoto–Uchiyama, as a neighbour of Takagi

| Kind | Name | Line |
|---|---|---:|
| Theorem | `one_plus_p_pow` | 22 |
| Theorem | `ou_L_of_plain` | 33 |
| Theorem | `ou_L_of_scaled` | 48 |
| Theorem | `ou_L_of_base` | 69 |
| Theorem | `ou_rand_vanishes` | 81 |

## `Order.v`

- L16: Orders of units, as objects
  - L34: Uniqueness and the divide criterion
  - L123: Existence from a positive annihilator
  - L207: [ord(a^k) = ord(a) / gcd(ord(a), k)]
  - L269: [lcm] of orders divides [λ]
  - L351: 2-height is [v₂(ord)] at a common odd multiple of [odd_part(ord)]
  - L495: A unit of order [λ] for general [N = pq]
  - L1024: A primitive root generates [𝔽_p*]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `is_order_unique` | 36 |
| Lemma | `no_smaller_order_sound` | 55 |
| Lemma | `is_order_by_vm` | 78 |
| Lemma | `powm_one_of_divide` | 90 |
| Theorem | `order_iff_divides` | 106 |
| Lemma | `order_exists_from_annihilator` | 128 |
| Theorem | `order_exists_prime` | 178 |
| Theorem | `order_exists_semiprime` | 192 |
| Theorem | `order_of_power` | 209 |
| Theorem | `lcm_orders_divides_lambda` | 271 |
| Lemma | `is_order_2_of` | 298 |
| Theorem | `minus1_order_2_rsa_test` | 312 |
| Theorem | `mixed67_order_2_rsa_test` | 318 |
| Theorem | `lcm_two_order2_not_lambda` | 324 |
| Lemma | `is_order_pin_g_p` | 335 |
| Lemma | `is_order_pin_g_q` | 340 |
| Theorem | `pin_unit_3_coprime` | 347 |
| Lemma | `powm_eq_1_iff_order_divides` | 353 |
| Lemma | `pow2_divides_pow2` | 364 |
| Theorem | `two_height_is_val2_ord` | 387 |
| Theorem | `order_2_mod_11` | 446 |
| Theorem | `order_2_mod_17` | 451 |
| Theorem | `two_height_independent_of_odd_multiple` | 458 |
| Theorem | `height_is_val2_ord_textbook` | 474 |
| Lemma | `zseq_length` | 510 |
| Lemma | `zseq_In_bounds` | 517 |
| Lemma | `zseq_Forall_distinct_head` | 530 |
| Lemma | `zseq_pairwise_distinct` | 550 |
| Lemma | `units_mod_prime_length` | 566 |
| Lemma | `units_mod_prime_In` | 570 |
| Lemma | `units_mod_prime_coprime` | 580 |
| Lemma | `units_mod_prime_distinct` | 592 |
| Lemma | `units_mod_prime_nonnil` | 602 |
| Lemma | `order_mul_coprime` | 610 |
| Lemma | `order_of_divisor_power` | 681 |
| Lemma | `order_lcm_attained` | 710 |
| Lemma | `exists_max_order_in` | 741 |
| Lemma | `zseq_In_interval` | 775 |
| Lemma | `unit_mod_in_list` | 788 |
| Lemma | `is_order_mod_base` | 809 |
| Lemma | `is_order_of_mod` | 823 |
| Lemma | `is_order_eq_mod` | 837 |
| Theorem | `primitive_root_exists` | 850 |
| Lemma | `order_semiprime_from_locals` | 916 |
| Theorem | `exists_unit_order_lambda` | 959 |
| Theorem | `is_order_pin_3_80` | 995 |
| Theorem | `exists_unit_order_lambda_pin` | 1004 |
| Theorem | `pin_attains_lambda` | 1010 |
| Theorem | `orders_generate_lambda_pin` | 1019 |
| Lemma | `mul_cancel_unit_mod` | 1029 |
| Lemma | `powm_eq_pow_cancel` | 1044 |
| Lemma | `powm_inj_lt_order` | 1068 |
| Lemma | `nodup_incl_le` | 1097 |
| Lemma | `powers_upto_length` | 1126 |
| Lemma | `powers_upto_In` | 1132 |
| Lemma | `powers_upto_NoDup` | 1145 |
| Theorem | `primitive_root_generates` | 1165 |

## `Paillier.v`

- L9: Paillier, as a neighbour of RSA

| Kind | Name | Line |
|---|---|---:|
| Lemma | `powm_mul_base` | 23 |
| Theorem | `one_plus_N_pow` | 33 |
| Theorem | `paillier_L_of_plain` | 44 |
| Theorem | `paillier_L_recovers_exp` | 56 |
| Theorem | `paillier_add` | 68 |
| Theorem | `one_plus_N_order_N` | 86 |

## `PhiLambda.v`

- L9: [φ = λ · gcd] on a semiprime

| Kind | Name | Line |
|---|---|---:|
| Theorem | `phi_eq_lambda_times_gcd` | 17 |
| Theorem | `phi_div_lambda_is_gcd` | 29 |

## `Pin.v`

- L41: Campaign pin — numerical source of truth
  - L66: Default semiprime
  - L131: Residual pair on the default pin
  - L137: Mixed square roots of 1 on [pin_N]
  - L142: Named extra moduli (p, q, N, λ, and shared witnesses)
  - L201: Dixon / QS witnesses on [pin_N]
  - L220: NFS quadratics on [pin_N]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `Zprime_sqrt` | 10 |
| Lemma | `pin_N_pos` | 99 |
| Lemma | `pin_N_gt_1` | 102 |
| Lemma | `pin_p_neq_q` | 105 |
| Lemma | `pin_p_lt_q` | 108 |
| Lemma | `pin_p_prime` | 111 |
| Lemma | `pin_q_prime` | 121 |

## `PollardP1.v`

- L9: Pollard's [p−1]: a one-sided annihilator

| Kind | Name | Line |
|---|---|---:|
| Lemma | `fermat_on_multiple` | 30 |
| Lemma | `gcd_onesided_semiprime` | 46 |
| Theorem | `pollard_p1_splits` | 62 |
| Theorem | `smooth_implies_public_annihilator` | 101 |

## `PotCheck.v`

- L11: Public check of a [τ]-update, equal-DL algebra

| Kind | Name | Line |
|---|---|---:|
| Theorem | `contribute_slot_one_is_rho_power` | 22 |
| Theorem | `update_first_is_old_first_to_rho` | 35 |
| Theorem | `update_pok_complete` | 50 |
| Theorem | `extracted_contributor_agrees` | 73 |

## `PotCl.v`

- L13: The same [τ]-string on a presentation

| Kind | Name | Line |
|---|---|---:|
| Theorem | `potP_rsa_is_pot` | 38 |
| Theorem | `potP_cl_is_bqf_exp` | 50 |
| Theorem | `potP_rsa_at_zero` | 56 |
| Theorem | `potP_rsa_at_one` | 66 |
| Theorem | `potP_cl_at_zero` | 77 |
| Theorem | `potP_cl_at_one` | 88 |
| Theorem | `potP_rsa_contribute_multiplies` | 96 |
| Theorem | `potP_rsa_succ` | 119 |
| Theorem | `pot_cl_no_lambda` | 132 |
| Theorem | `pot_cl_inv_is_public` | 142 |
| Theorem | `pot_cl_contribute_slot0` | 147 |
| Theorem | `pot_cl_neg31_at_zero` | 158 |
| Theorem | `pot_cl_neg31_at_one` | 166 |

## `PotLadder.v`

- L11: Equal-DL ladder: extra CRS powers are a proven [ρ^i]-update
  - L104: Slot 2 is two ladder steps

| Kind | Name | Line |
|---|---|---:|
| Lemma | `rho_ladder_0` | 30 |
| Lemma | `rho_ladder_succ` | 34 |
| Theorem | `rho_ladder_succ_is_power` | 39 |
| Theorem | `ladder_realizes_update` | 58 |
| Theorem | `contribution_ladder_step` | 75 |
| Theorem | `slot2_aux_is_ladder_one` | 109 |
| Theorem | `slot2_new_is_rho_sq` | 117 |
| Theorem | `slot2_aux_then_rho` | 129 |
| Theorem | `slot2_new_is_ladder_two` | 144 |
| Theorem | `slot2_leg1_complete` | 155 |
| Theorem | `slot2_leg2_complete` | 182 |

## `PowersOfTau.v`

- L11: Powers of a sampled [τ] in [(Z/NZ)*]
  - L46: The string is [g^{τ^i}]; the next element is a [τ]-power
  - L92: Contribution multiplies the secret
  - L141: One honest contribution changes the string
  - L261: The only backward walker is [τ⁻¹] modulo the order
  - L352: Equal discrete logs: completeness and two-transcript extraction
  - L431: Self-bilinear maps evaluate the sampled-[τ] string

| Kind | Name | Line |
|---|---|---:|
| Lemma | `pot_at_zero` | 48 |
| Lemma | `pot_at_one` | 57 |
| Theorem | `pot_succ_is_tau_power` | 66 |
| Theorem | `pot_first_is_dlog` | 81 |
| Theorem | `pot_contribute_multiplies_tau` | 94 |
| Theorem | `two_contributors_product` | 110 |
| Theorem | `three_contributors_product` | 123 |
| Lemma | `coprime_powm` | 143 |
| Lemma | `powm_eq_implies_abs_annihilator` | 169 |
| Theorem | `honest_contribution_moves_string` | 213 |
| Theorem | `honest_tau_one_if_coprime` | 242 |
| Lemma | `powm_reduce_mod_order` | 263 |
| Theorem | `tau_inv_walks_backward` | 285 |
| Theorem | `backward_walker_is_tau_inv` | 314 |
| Theorem | `eqdl_complete` | 367 |
| Theorem | `eqdl_extracts_tau` | 392 |
| Theorem | `self_bil_checks_pot` | 446 |
| Theorem | `self_bil_evaluates_pot` | 465 |

## `Pratt.v`

- L11: Pratt certificates, dual to Miller-from-[λ]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `pratt_2_prime` | 48 |
| Theorem | `pratt_fermat_side` | 53 |
| Theorem | `duality_unique_order_2_on_prime` | 66 |

## `PreprocessGRA.v`

- L15: Preprocessing GRA (Dachman-Soled–Loss–O'Neill shape)

| Kind | Name | Line |
|---|---|---:|
| Theorem | `prep_advice_depends_on_N` | 27 |
| Theorem | `prep_advice_ignores_y` | 31 |
| Theorem | `prep_factor_advice` | 35 |
| Theorem | `prep_id_advice_not_a_split` | 43 |
| Theorem | `prep_ginv_of_factor_advice` | 55 |
| Theorem | `prep_then_gra_factors` | 59 |

## `Presentation.v`

- L14: A presentation of a group of unknown order
  - L80: RSA, public view: no annihilator, constructible torsion is [±1]
  - L104: [Cl(Δ)]: public 2-annihilator, constructible torsion is ambiguous forms
  - L128: Sentence 1 — units have an order, which divides every annihilator
  - L142: Sentence 2 — low-order for [B = 2] is a public construction
  - L299: Sentence 3 — adaptive root is trivial from public data on RSA
  - L322: Week 8 — same mechanics, no modulus

| Kind | Name | Line |
|---|---|---:|
| Theorem | `rsa_order_divides_lambda` | 130 |
| Theorem | `cl_constructible_order_divides_2` | 138 |
| Theorem | `rsa_public_annihilator_is_none` | 145 |
| Theorem | `cl_public_annihilator_is_two` | 149 |
| Theorem | `rsa_minus1_constructible` | 153 |
| Theorem | `cl_unrestricted_LowOrder_B2` | 157 |
| Theorem | `cl_restricted_excludes_ambiguous` | 161 |
| Theorem | `mersenne31_wins_P_LowOrderOutside` | 170 |
| Theorem | `mersenne31_family_excludes_shanks` | 188 |
| Theorem | `ordinary_vs_mersenne_H` | 198 |
| Theorem | `mersenne_family_at_2` | 207 |
| Theorem | `class_number_solves_AR_neg31_id` | 211 |
| Theorem | `class_number_solves_AR_neg31_f` | 222 |
| Theorem | `class_number_solves_AR_neg31_sq` | 232 |
| Theorem | `class_number_solves_AR_neg31` | 247 |
| Theorem | `shanks_is_annihilator` | 260 |
| Theorem | `shanks_AR_is_fractional_root` | 269 |
| Theorem | `cl_AR_C_broken_when_two_in_C` | 283 |
| Theorem | `rsa_trapdoor_annihilator_is_lambda` | 302 |
| Theorem | `rsa_lambda_solves_adaptive_root` | 306 |
| Theorem | `cl_has_no_lambda_plus_one` | 315 |
| Theorem | `no_crt_split_from_disc` | 335 |
| Theorem | `cl_exp_0_is_id` | 341 |
| Theorem | `cl_exp_1_is_f` | 345 |
| Theorem | `cl_inv_is_bqf_inv` | 352 |
| Theorem | `cl_mul_inv_equiv_id` | 356 |
| Theorem | `unit_inverse_exists` | 373 |
| Theorem | `rsa_trapdoor_inv_is_root` | 389 |
| Theorem | `Pexp_0` | 411 |
| Theorem | `Pexp_S_rsa` | 418 |

## `PublicQuad.v`

- L17: Public quadratic check of two committed evaluations
  - L42: Bounded exponent search against a public base
  - L140: Recover a coefficient list from slot encodings vs CRS
  - L161: Public CRS list [P_0,…,P_{n-1}]
  - L259: Bilinear combine [∏_{i,j} P_{i+j}^{a_i b_j}]
  - L366: The public check: encodings and CRS only
  - L447: Representative pin: the check is not the group law

| Kind | Name | Line |
|---|---|---:|
| Lemma | `find_exp_from_sound` | 55 |
| Lemma | `find_exp_from_complete` | 85 |
| Lemma | `find_exp_complete` | 108 |
| Lemma | `find_exp_sound` | 124 |
| Lemma | `pot_crs_from_length` | 172 |
| Lemma | `pot_crs_length` | 182 |
| Lemma | `pot_crs_from_nth` | 189 |
| Lemma | `pot_crs_nth` | 206 |
| Lemma | `recover_honest` | 231 |
| Lemma | `quad_row_spec` | 278 |
| Lemma | `quad_combine_spec` | 314 |
| Theorem | `quad_combine_is_product` | 349 |
| Lemma | `first_exps_nn` | 379 |
| Theorem | `public_quad_complete` | 391 |
| Theorem | `public_quad_qap` | 421 |
| Theorem | `public_quad_pin_accepts` | 455 |
| Theorem | `public_quad_pin_rejects_group_mul` | 466 |
| Theorem | `public_quad_pin_sum_neq_prod` | 478 |
| Theorem | `public_quad_pin_qap` | 484 |

## `QAP.v`

- L15: QAP completeness on committed evaluations
  - L126: Specialized CRS: [∏ U_j^{w_j} = g^{(Σ w_j A_j)(τ)}]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `poly_eval_sub` | 34 |
| Theorem | `qap_rem_eval` | 51 |
| Theorem | `qap_at_iff_rem_zero` | 63 |
| Theorem | `qap_complete_at_tau` | 70 |
| Theorem | `qap_point_sound` | 91 |
| Theorem | `qap_sound_at_tau` | 109 |
| Lemma | `poly_eval_lincomb` | 151 |
| Lemma | `wires_nn_lincomb_nonneg` | 166 |
| Theorem | `pot_wires_is_lincomb` | 178 |
| Theorem | `same_witness_two_families` | 198 |
| Theorem | `qap_witness_complete` | 210 |
| Lemma | `pot_wires_bounded` | 232 |
| Theorem | `pot_wires_app` | 246 |

## `QRModN.v`

- L15: Quadratic residuosity modulo [N = pq]
  - L465: Jacobi degeneracy: [(g^k/N)] sees [k] only modulo 2
  - L706: Shamir at [(2,3)]: a square root and a cube root yield a sixth root
  - L743: Obstruction: Jacobi is an additive pairing into [{±1}]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `euler_crit_agree` | 39 |
| Lemma | `mod_pq_to_p` | 46 |
| Lemma | `qr_N_implies_local` | 57 |
| Lemma | `qr_N_of_local` | 77 |
| Theorem | `qr_N_iff_both` | 102 |
| Lemma | `euler_sign_of_pm1` | 115 |
| Lemma | `euler_sign_of_qr` | 132 |
| Theorem | `jacobi_of_qr_N` | 146 |
| Theorem | `euler_one_implies_qr_blum` | 166 |
| Lemma | `euler_sign_one_is_crit_one` | 188 |
| Lemma | `euler_sign_minus_is_crit_pm1` | 205 |
| Lemma | `euler_sign_one_implies_qr_blum` | 220 |
| Lemma | `euler_sign_minus_implies_qnr` | 234 |
| Lemma | `coprime_neg1` | 247 |
| Lemma | `coprime_opp` | 255 |
| Lemma | `euler_sign_neg1_blum` | 259 |
| Lemma | `euler_crit_mul` | 276 |
| Lemma | `euler_sign_mul` | 291 |
| Lemma | `euler_sign_neg_a` | 335 |
| Theorem | `jacobi_neg1_blum` | 350 |
| Theorem | `neg1_not_qr_N_blum` | 365 |
| Theorem | `blum_jacobi_one_exactly_one_pm` | 385 |
| Theorem | `williams_both_qr_is_qr_N` | 436 |
| Lemma | `coprime_powm_prime` | 467 |
| Lemma | `coprime_powm_N_prime` | 483 |
| Theorem | `jacobi_even_power` | 504 |
| Theorem | `jacobi_odd_power` | 534 |
| Theorem | `jacobi_sees_only_parity` | 610 |
| Lemma | `even_pow_succ` | 635 |
| Lemma | `odd_pow_pos` | 652 |
| Theorem | `pot_jacobi_tail_constant` | 674 |
| Theorem | `sixth_root_from_square_and_cube` | 708 |
| Theorem | `cubic_decision_vacuous` | 731 |

## `QuadResidue.v`

- L10: Quadratic residues and the [p ≡ 3 (mod 4)] square-root formula

| Kind | Name | Line |
|---|---|---:|
| Lemma | `odd_prime_minus1_even` | 22 |
| Lemma | `p_mod4_3_decomp` | 38 |
| Lemma | `p_mod8_decomp` | 44 |
| Lemma | `mod8_3_is_mod4_3` | 50 |
| Lemma | `mod8_7_is_mod4_3` | 59 |
| Lemma | `blum_prime_pminus1_form` | 69 |
| Lemma | `two_times_div4` | 82 |
| Lemma | `half_plus_one` | 95 |
| Theorem | `euler_qr_is_one` | 110 |
| Theorem | `sqrt_mod4_3_correct` | 151 |
| Lemma | `pow_neg1_even` | 179 |
| Lemma | `pow_neg1_odd` | 189 |
| Theorem | `neg1_euler_mod4_3` | 200 |

## `RSA.v`

- L11: RSA: instance, private exponent [d], and the RSA problem
  - L226: Why a polynomial in [N] cannot be a handle

| Kind | Name | Line |
|---|---|---:|
| Lemma | `rsa_N_gt_1` | 39 |
| Lemma | `rsa_lambda_pos` | 46 |
| Lemma | `rsa_lambda_gt_1` | 52 |
| Lemma | `rsa_phi_pos` | 71 |
| Lemma | `rsa_lambda_divides_phi` | 77 |
| Lemma | `rsa_ed_minus_1_divides` | 80 |
| Lemma | `rsa_ed_gt_1` | 89 |
| Theorem | `rsa_dec_enc_units` | 102 |
| Theorem | `rsa_enc_dec_units` | 126 |
| Lemma | `rsa_d_is_cube_root_map` | 153 |
| Lemma | `prime_11` | 164 |
| Lemma | `prime_17` | 173 |
| Lemma | `rsa_test_lambda` | 183 |
| Lemma | `rsa_test_phi` | 186 |
| Lemma | `rsa_test_inv` | 189 |
| Lemma | `rsa_test_coprime_e` | 192 |
| Theorem | `rsa_test_N` | 207 |
| Theorem | `rsa_test_vector` | 210 |
| Theorem | `rsa_test_roundtrip` | 214 |
| Theorem | `rsa_test_annihilator` | 218 |
| Theorem | `N_cong_q_mod_pminus1` | 233 |
| Theorem | `gcd_polyN_pminus1_is_gcd_at_q` | 244 |

## `RabinWilliams.v`

- L12: Rabin–Williams: squaring in [(Z/NZ)*] with the Williams tweak
  - L31: The Rabin problem
  - L41: Prime shape
  - L107: Williams tweak: among [{±a, ±2a}] exactly one Legendre pair
  - L210: Rabin reduction: two non-associated square roots factor [N]
  - L294: Verification shape: [s²] is one of the four tweaks of [H].
  - L312: Keygen obligation on top of the RSA rulers: the mod-8 split.

| Kind | Name | Line |
|---|---|---:|
| Lemma | `rabin_of_square` | 37 |
| Lemma | `rw_p_is_blum` | 51 |
| Lemma | `rw_q_is_blum` | 57 |
| Lemma | `rw_pair_odd` | 63 |
| Lemma | `lcm_even_of_even_l` | 72 |
| Theorem | `lambda_even_odd_primes` | 81 |
| Theorem | `two_not_rsa_exponent` | 92 |
| Lemma | `pm1_cases` | 123 |
| Theorem | `williams_tweak_exists` | 129 |
| Theorem | `williams_tweak_unique` | 143 |
| Theorem | `williams_which_correct` | 175 |
| Theorem | `williams_two_symbol_p` | 191 |
| Theorem | `williams_two_symbol_q` | 195 |
| Theorem | `williams_neg1_on_blum` | 199 |
| Theorem | `rabin_roots_split` | 218 |
| Theorem | `rabin_oracle_nonassociate_factors` | 269 |
| Lemma | `rw_verify_of_root` | 305 |
| Lemma | `kg_rw_implies_blum` | 316 |
| Lemma | `kg_rw_pminus1_almost_odd` | 324 |

## `Range2.v`

- L14: Two-bit value from bits

| Kind | Name | Line |
|---|---|---:|
| Theorem | `range2_bits` | 24 |
| Theorem | `range2_bit_qap` | 34 |
| Theorem | `range2_encoding` | 51 |
| Theorem | `range2_eval_commit` | 67 |

## `SAGM.v`

- L10: Strong algebraic group model (representation)

| Kind | Name | Line |
|---|---|---:|
| Theorem | `sagm_eval_21` | 31 |
| Theorem | `sagm_product_adds_exponents` | 36 |
| Theorem | `sagm_mul_exps` | 44 |

## `SameW.v`

- L13: Same witness on two specialized CRSs

| Kind | Name | Line |
|---|---|---:|
| Lemma | `zip_scale_eval` | 32 |
| Lemma | `zip_wires_nn` | 55 |
| Theorem | `same_w_check` | 76 |

## `SharedKey.v`

- L17: Shared RSA key from two KeyGen-valid parts
  - L50: Layer 1 — Carmichael of a coprime product
  - L152: Layer 2 — CRT of inverses of a common [e]
  - L328: Layer 3 — local decrypt + CRT = global [c^{d*}]
  - L427: Layer 4 — one local [d] does not determine [d*]
  - L518: Layer 5 — lifted KeyGen spec
  - L574: Layer 6 — arity 3
  - L628: Unassembled [d*] is not ZK; it is a trapdoor
  - L837: SRS checks: each next value is the [e]-th root of the last
  - L920: Relations: discrete log of the SRS is not strong RSA

| Kind | Name | Line |
|---|---|---:|
| Lemma | `lambda_A_divides_product` | 52 |
| Lemma | `lambda_B_divides_product` | 56 |
| Lemma | `lambda_product_pos` | 60 |
| Lemma | `lambda_product_gt_1` | 73 |
| Lemma | `coprime_product_split` | 83 |
| Lemma | `crt_mod_eq_coprime` | 89 |
| Lemma | `crt_one_coprime_moduli` | 106 |
| Theorem | `carmichael_shared` | 127 |
| Lemma | `gcd_of_divisor` | 154 |
| Lemma | `inverses_agree_mod_gcd` | 172 |
| Lemma | `rsa_e_gcd_lambda` | 203 |
| Lemma | `crt_exists_gcd` | 207 |
| Theorem | `d_star_exists` | 254 |
| Theorem | `d_star_exists_nonneg` | 274 |
| Theorem | `d_star_inverts` | 302 |
| Lemma | `powm_mod_lambda` | 330 |
| Lemma | `shared_dec_mod_A` | 358 |
| Lemma | `shared_dec_mod_B` | 372 |
| Theorem | `shared_dec_eq_powm` | 384 |
| Lemma | `prime_5` | 429 |
| Lemma | `prime_23` | 437 |
| Lemma | `prime_41` | 449 |
| Theorem | `rsa_5_23_N` | 489 |
| Theorem | `rsa_5_41_N` | 492 |
| Theorem | `d_star_depends_on_both` | 495 |
| Theorem | `two_partners_two_dstars` | 505 |
| Theorem | `product_carries_component_keygen` | 526 |
| Theorem | `product_common_e_inverts` | 532 |
| Theorem | `product_refuses_shared_prime` | 542 |
| Theorem | `d_star_gt_lambda_div_e` | 548 |
| Theorem | `carmichael_shared3` | 586 |
| Theorem | `d_star_unique_mod_lambda` | 646 |
| Theorem | `d_star_inverts_on_A` | 662 |
| Theorem | `d_star_inverts_on_B` | 676 |
| Theorem | `d_star_ed_minus_1_divides_lambda` | 690 |
| Theorem | `d_star_annihilates_shared` | 703 |
| Theorem | `d_star_decrypts_B` | 727 |
| Theorem | `d_star_decrypts_A` | 742 |
| Lemma | `coprime_powm` | 767 |
| Lemma | `shared_N_gt_1` | 793 |
| Theorem | `dstar_power_crs_is_powm` | 802 |
| Theorem | `shared_dec_is_eth_root` | 844 |
| Theorem | `srs_first_checks` | 871 |
| Theorem | `srs_step_checks` | 893 |
| Theorem | `srs_first_is_rsa` | 934 |
| Theorem | `srs_first_is_strong_rsa` | 949 |
| Theorem | `lambda_plus_one_is_other_strong_rsa` | 965 |
| Theorem | `dstar_inverts_every_unit` | 984 |
| Lemma | `powm_eq_implies_abs_annihilator` | 1008 |
| Theorem | `dlog_of_srs_agrees_mod_order` | 1052 |
| Theorem | `dlog_at_full_order_inverts_e` | 1075 |

## `SharedModulus.v`

- L12: Shared-modulus DKG algebra (Boneh–Franklin shape)

| Kind | Name | Line |
|---|---|---:|
| Theorem | `dkg_N_is_product` | 29 |
| Theorem | `dkg_N_cross_terms` | 34 |
| Theorem | `published_sum_is_phi_plus_one` | 40 |
| Theorem | `two_prime_four_roots_triprime_eight` | 45 |
| Theorem | `triprime_mixed_root_refutes_biprime` | 70 |

## `SharedPrime.v`

- L9: Shared primes: [gcd(N₁, N₂)] *is* the common CRT component

| Kind | Name | Line |
|---|---|---:|
| Theorem | `gcd_shared_prime` | 14 |
| Theorem | `gcd_shared_prime_divides_both` | 29 |

## `SieveRelation.v`

- L16: Sieve relations: the algebraic engine of QS and NFS
  - L28: Even exponents make a square
  - L198: NFS setup: common root and homogenised remainder
  - L297: Two-sided combination

| Kind | Name | Line |
|---|---|---:|
| Lemma | `even_nonneg_pow_square` | 30 |
| Lemma | `square_times_square` | 44 |
| Theorem | `even_exp_2_3_5_square` | 51 |
| Lemma | `mul_mod_cong` | 61 |
| Lemma | `not_div_mod` | 75 |
| Theorem | `dixon_two_relations` | 85 |
| Theorem | `dixon_combination_splits` | 99 |
| Theorem | `dixon_pin_residue_factors` | 118 |
| Theorem | `dixon_pin_cong` | 122 |
| Lemma | `dixon_pin_not_assoc` | 138 |
| Theorem | `dixon_pin_splits` | 147 |
| Theorem | `dixon_pin_gcd` | 163 |
| Theorem | `dixon_pin_b_splits` | 168 |
| Theorem | `asquare_pin_splits` | 187 |
| Theorem | `hom_quad_remainder` | 206 |
| Theorem | `hom_quad_cong` | 213 |
| Lemma | `poly_eval_quad` | 236 |
| Theorem | `nfs_eval_irr` | 241 |
| Theorem | `nfs_eval_red` | 245 |
| Theorem | `nfs_common_root_irr` | 249 |
| Theorem | `nfs_common_root_red` | 253 |
| Theorem | `nfs_irr_disc_neg` | 257 |
| Theorem | `nfs_neg_not_square` | 265 |
| Theorem | `nfs_red_splits_Z` | 272 |
| Theorem | `nfs_F_cong_GH_irr` | 277 |
| Theorem | `nfs_F_cong_GH_red` | 287 |
| Theorem | `nfs_two_sided_product` | 299 |
| Theorem | `nfs_two_sided_pin_squares` | 318 |
| Theorem | `nfs_two_sided_pin_sqrt1` | 351 |
| Theorem | `nfs_two_sided_splits` | 361 |
| Theorem | `nfs_two_sided_gcd` | 374 |
| Theorem | `nfs_onesided_no_split` | 379 |

## `SixthType.v`

- L10: Directed sixth-type leftovers (Methods 3–8)
  - L16: Method 3: [(N, 0, 1)] of disc [−4N] is the principal class
  - L96: Method 11: every factorization [4N = αβ] gives
  - L110: Polynomial characters collapse: [D(N) ≡ D(0) (mod p)]
  - L142: [Δ=−4N]: non-principal [Cl[2]] *is* the factorization

| Kind | Name | Line |
|---|---|---:|
| Theorem | `form_N01_disc` | 21 |
| Lemma | `minus4N_mod4` | 27 |
| Lemma | `minus4N_div4` | 33 |
| Theorem | `form_N01_equiv_principal` | 42 |
| Theorem | `Nsq_minus_4_factors` | 63 |
| Theorem | `gcd_N_minus_2_N` | 67 |
| Theorem | `odd_N_gcd_Nminus2` | 78 |
| Theorem | `factor_4N_gives_square_disc` | 100 |
| Theorem | `N_plus_one_powm` | 115 |
| Theorem | `N_plus_one_euler_is_one` | 130 |
| Theorem | `form_p0q_disc` | 151 |
| Theorem | `form_p0q_ambiguous` | 157 |
| Theorem | `form_p0q_reduced_when_ordered` | 161 |
| Theorem | `williams_N_mod4` | 182 |
| Theorem | `both_1_mod4_N_mod4` | 190 |
| Theorem | `mixed_mod4_N_mod4` | 198 |

## `SmallExponent.v`

- L10: Small public [e]: the RSA map is a low-degree polynomial

| Kind | Name | Line |
|---|---|---:|
| Lemma | `rsa_poly_degree_is_e` | 21 |
| Lemma | `cube_is_powm3` | 26 |
| Lemma | `unique_nonneg_rep` | 34 |
| Lemma | `three_moduli_divide` | 49 |
| Theorem | `hastad_cube_if_small` | 74 |
| Lemma | `related_message_common_root` | 97 |
| Theorem | `fr_cube_gap` | 110 |
| Theorem | `fr_cube_gap_mod` | 116 |

## `SolverRestrict.v`

- L18: Algorithm restrictions: SAGM-only, safeprime residual, polynomial [e(y)]
  - L25: SAGM-only: known exponents of public bases
  - L73: Safeprime residual on [N = pin_77], [λ = 30 = 2 p' q']
  - L102: Polynomial [e] of the challenge
  - L125: Degree-[≥2] polynomial [e = P(y)], rejection sample, write-[e] then [x]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `sagm_powm_mul_exp` | 30 |
| Theorem | `sagm_root_of_generator_pin` | 41 |
| Theorem | `sagm_ae_minus_one_is_lambda` | 45 |
| Theorem | `sagm_generator_annihilated` | 49 |
| Theorem | `sagm_only_miller_splits` | 53 |
| Theorem | `sagm_scale_eval_pin` | 61 |
| Theorem | `sagm_scale_lambda_type` | 67 |
| Theorem | `safeprime_e3_names_p` | 75 |
| Theorem | `safeprime_e5_names_q` | 81 |
| Theorem | `safeprime_e3_not_residual` | 87 |
| Theorem | `safeprime_residual_e7` | 91 |
| Theorem | `poly_e_constant` | 104 |
| Theorem | `poly_e_constant_is_fixed_e` | 108 |
| Theorem | `poly_e_X_two_points` | 113 |
| Theorem | `poly_e_X_not_rerand` | 117 |
| Theorem | `poly_e_nonconstant_not_fixed_parameter` | 121 |
| Theorem | `poly_e_quadratic` | 135 |
| Theorem | `poly_e_quadratic_residual_shaped` | 139 |
| Theorem | `poly_e_quadratic_leftover_with_period` | 146 |
| Theorem | `poly_e_quadratic_encrypt_not_leftover` | 150 |
| Theorem | `poly_e_square_even_peel` | 154 |
| Theorem | `reject_sample_public_e_emits_5` | 165 |
| Theorem | `reject_sample_emits_nonresidual` | 169 |

## `SolverShape.v`

- L23: Twelve solver-shape inroads on Strong RSA
  - L30: 1. Monomial [x = y^k], [k] even
  - L51: 2. Inverse [x = y^{-1}]
  - L70: 3. Affine identity [x = a y + b] for all [y]
  - L89: 4. Two outputs at the same coprime [e]
  - L148: 5. Franklin–Reiter: additive related at fixed [e]
  - L168: 6. Chaum-blind: sees [y r^e], returns [x r]
  - L188: 7. Jacobi-discrete [e(y) ∈ {3,5}]
  - L204: 8. Extra annihilator output [M] with [y^M ≡ 1]
  - L218: 9. Extra [d] with [e d ≡ 1 (mod λ)]
  - L233: 10. Euler inverse modulo [N−1], not [λ]
  - L244: 11. CRT-tape: [x = CRT(x_p, x_q)]
  - L259: 12. Miller on [e−1] against the challenge [y]
  - L273: Public addition chain, polynomial [X], short bases, gcd-free multiply

| Kind | Name | Line |
|---|---|---:|
| Theorem | `shape_even_ndiv_odd` | 32 |
| Theorem | `shape_monomial_k2_period_obstruction` | 39 |
| Theorem | `shape_monomial_k2_pin` | 47 |
| Theorem | `shape_inverse_of_36_residual_shaped` | 53 |
| Theorem | `shape_inverse_of_generator` | 57 |
| Theorem | `shape_inverse_generator_miller` | 62 |
| Theorem | `shape_affine_identity_forbidden` | 72 |
| Theorem | `shape_affine_eval_not_zero` | 81 |
| Theorem | `shape_affine_pointwise_const_residual` | 85 |
| Theorem | `shape_eth_root_of_1` | 91 |
| Theorem | `shape_unique_eth_root` | 107 |
| Theorem | `shape_two_unit_cube_roots_agree` | 120 |
| Theorem | `shape_unique_unit_cube_root_of_36` | 135 |
| Theorem | `shape_fr_small_integer` | 150 |
| Theorem | `shape_fr_cube_gap_small` | 154 |
| Theorem | `shape_fr_residual_not_integer_cube` | 159 |
| Theorem | `shape_fr_reduced_offset_not_integer` | 163 |
| Theorem | `shape_chaum_unblind` | 170 |
| Theorem | `shape_chaum_recovers_cube_root` | 180 |
| Theorem | `shape_chaum_e_is_protocol` | 184 |
| Theorem | `shape_jacobi_e_on_square` | 193 |
| Theorem | `shape_jacobi_e_on_nonsquare` | 198 |
| Theorem | `shape_short_period_of_y_no_split` | 206 |
| Theorem | `shape_lambda_quality_miller` | 210 |
| Theorem | `shape_ed_minus_one_is_lambda` | 220 |
| Theorem | `shape_ed_miller` | 225 |
| Theorem | `shape_e3_not_invertible_mod_Nminus1` | 235 |
| Theorem | `shape_wrong_euler_inv` | 240 |
| Theorem | `shape_crt_residues` | 246 |
| Theorem | `shape_crt_recovers_root` | 251 |
| Theorem | `shape_crt_moduli_are_factors` | 255 |
| Theorem | `shape_miller_e11_on_y_splits` | 261 |
| Theorem | `shape_miller_e3_on_y_survives` | 269 |
| Theorem | `shape_public_chain_e3` | 281 |
| Theorem | `shape_trapdoor_chain_d27` | 285 |
| Theorem | `shape_poly_x_quadratic` | 289 |
| Theorem | `shape_public_bases_2_3` | 293 |
| Theorem | `shape_gcdfree_bounded_from_y` | 297 |
| Theorem | `shape_public_exp_not_membership` | 301 |

## `SrsaDict.v`

- L14: Residual dictionary, cubing cycles, SAGM on [y]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `dict_e_eq_d` | 21 |
| Theorem | `dict_e43_same_x_leaf` | 25 |
| Theorem | `dict_N_mod_40_is_d` | 29 |
| Theorem | `dict_public_N_mod_40` | 33 |
| Theorem | `dict_y_to_d` | 37 |
| Theorem | `dict_x93_e67` | 41 |
| Theorem | `dict_x25_e11` | 45 |
| Theorem | `dict_x25_e51` | 49 |
| Theorem | `dict_x15_e29` | 53 |
| Theorem | `dict_x15_e69` | 57 |
| Theorem | `dict_x168_e61` | 61 |
| Theorem | `dict_x104_e57` | 65 |
| Theorem | `dict_x185_e53` | 69 |
| Theorem | `dict_xy_e41` | 73 |
| Theorem | `dict_y_lambda_type` | 77 |
| Theorem | `dict_e_plus_80` | 81 |
| Theorem | `dict_phi80` | 85 |
| Theorem | `dict_phi40` | 89 |
| Theorem | `dict_two_e_per_x` | 93 |
| Theorem | `dict_e_mod_40` | 97 |
| Theorem | `dict_kernel_1_41` | 101 |
| Theorem | `dict_cube_bij_on_cyc` | 107 |
| Theorem | `dict_27th_is_inverse_auto` | 111 |
| Theorem | `dict_compose_autos` | 115 |
| Theorem | `dict_ae_is_lambda_plus_1` | 120 |
| Theorem | `dict_bits_of_27` | 124 |
| Theorem | `dict_binary_product` | 128 |
| Theorem | `dict_add_chain_y6` | 132 |
| Theorem | `dict_add_chain_y12` | 136 |
| Theorem | `dict_add_chain_y24` | 140 |
| Theorem | `dict_k_odd` | 144 |
| Theorem | `dict_hamming_27` | 148 |
| Theorem | `dict_naf_shape` | 152 |
| Theorem | `dict_y25` | 156 |
| Theorem | `dict_y16_is_g5sq` | 160 |
| Theorem | `dict_sagm_on_y` | 164 |
| Theorem | `dict_y81` | 168 |
| Theorem | `dict_ae_lambda_plus_1` | 172 |
| Theorem | `dict_e43_same_x` | 176 |
| Theorem | `dict_e83_same_x` | 180 |
| Theorem | `dict_e43_minus_3` | 184 |
| Theorem | `dict_e83_minus_3` | 188 |
| Theorem | `dict_e67_coprime` | 192 |
| Theorem | `dict_e51_coprime` | 196 |
| Theorem | `dict_e61_coprime` | 200 |
| Theorem | `dict_e57_coprime` | 204 |
| Theorem | `dict_e29_coprime` | 208 |
| Theorem | `dict_e39_coprime` | 212 |
| Theorem | `dict_x26_e39` | 216 |
| Theorem | `dict_self_inverse_11` | 220 |
| Theorem | `dict_sagm_ae_minus_1` | 224 |
| Theorem | `dict_inv_mod_40` | 228 |
| Theorem | `dict_inv_mod_lam` | 232 |
| Theorem | `dict_cycle_70_cube` | 236 |
| Theorem | `dict_cycle_42_cube` | 240 |
| Theorem | `dict_cycle_36_cube` | 244 |
| Theorem | `dict_cycle_93_cube` | 248 |
| Theorem | `dict_three_order_4_mod_40` | 252 |
| Theorem | `dict_27_order_4_mod_40` | 256 |
| Theorem | `dict_cycle2_9` | 260 |
| Theorem | `dict_cycle2_168` | 264 |
| Theorem | `dict_cycle2_15` | 268 |
| Theorem | `dict_k27_coords` | 272 |
| Theorem | `dict_e3_coords` | 277 |
| Theorem | `dict_3_order_4_mod_40` | 282 |
| Theorem | `dict_cube_root_of_2` | 287 |
| Theorem | `dict_sagm_of_3` | 291 |
| Theorem | `dict_75_not_42` | 295 |
| Theorem | `dict_cycle2_60` | 299 |
| Theorem | `dict_cycle3_25` | 303 |
| Theorem | `dict_cycle3_104` | 307 |
| Theorem | `dict_cycle3_59` | 311 |
| Theorem | `dict_cycle3_53` | 315 |
| Theorem | `dict_cycle4_49` | 319 |
| Theorem | `dict_cycle4_26` | 323 |
| Theorem | `dict_cycle4_185` | 327 |
| Theorem | `dict_cycle4_179` | 331 |
| Theorem | `dict_cbrt_2_in_ltwo` | 335 |
| Theorem | `dict_cbrt_3_in_lthree` | 339 |
| Theorem | `dict_cbrt_36_in_ly` | 343 |
| Theorem | `dict_three_x_for_k27` | 348 |

## `SrsaEngines.v`

- L14: Named factoring engines as solvers

| Kind | Name | Line |
|---|---|---:|
| Theorem | `engine_pollard_p1` | 21 |
| Theorem | `engine_rho_walk` | 31 |
| Theorem | `engine_bsgs_wrong_order` | 37 |
| Theorem | `engine_fermat_splits` | 42 |
| Theorem | `engine_trial_division` | 56 |
| Theorem | `engine_williams_pplus1` | 64 |
| Theorem | `engine_index_calculus_Nminus1` | 72 |
| Theorem | `engine_F9_splits` | 76 |
| Theorem | `engine_F10_splits` | 84 |
| Theorem | `engine_mersenne_255` | 92 |
| Theorem | `engine_pminus1_B8` | 100 |
| Theorem | `engine_rho_x2_minus_1` | 104 |
| Theorem | `engine_williams_P3_no_split` | 110 |
| Theorem | `engine_factorial_trial` | 114 |
| Theorem | `engine_hart_square` | 118 |
| Theorem | `engine_fermat_recovers` | 124 |
| Theorem | `engine_trial_13_then_11` | 136 |
| Theorem | `engine_fibonacci_gcd_engine` | 146 |
| Theorem | `engine_mersenne_engine` | 154 |
| Theorem | `engine_shor_period_of_2` | 162 |
| Theorem | `engine_lam_ne_Nminus1` | 167 |

## `SrsaExtra.v`

- L14: Extra tapes and related challenges

| Kind | Name | Line |
|---|---|---:|
| Theorem | `extra_shamir_two_leftovers` | 20 |
| Theorem | `extra_crt_dp` | 24 |
| Theorem | `extra_fermat_difference` | 29 |
| Theorem | `extra_sqrt_splits` | 34 |
| Theorem | `extra_order_is_lambda` | 42 |
| Theorem | `extra_factor_e_minus_1` | 46 |
| Theorem | `extra_factor_N_minus_1` | 50 |
| Theorem | `extra_wiener_d_not_small` | 54 |
| Theorem | `extra_sequential_square_period` | 58 |
| Theorem | `extra_height_mismatch` | 62 |
| Theorem | `extra_primitive_root_mod_p` | 67 |
| Theorem | `extra_half_bits` | 72 |
| Theorem | `extra_cubic_symbol_vacuous` | 77 |
| Theorem | `extra_inverse_challenge` | 81 |
| Theorem | `extra_neg_y` | 85 |
| Theorem | `extra_two_y` | 89 |
| Theorem | `extra_three_powers_gcd` | 93 |
| Theorem | `extra_y_plus_1_root` | 97 |
| Theorem | `extra_batch_gcd_of_roots` | 101 |
| Theorem | `extra_adaptive_lambda_plus_one` | 105 |
| Theorem | `extra_same_y_two_moduli` | 109 |
| Theorem | `extra_twin_exponents` | 114 |
| Theorem | `extra_product_of_leftovers` | 118 |
| Theorem | `extra_rerand_forces_fixed_e` | 122 |
| Theorem | `extra_coins_independent_fixed_e` | 126 |
| Theorem | `extra_squaring_only` | 131 |
| Theorem | `extra_advice_on_y_lsb` | 135 |
| Theorem | `extra_streaming_first_bit` | 139 |
| Theorem | `extra_dl_base3` | 143 |
| Theorem | `extra_p_plus_q` | 147 |
| Theorem | `extra_torus_order_is_y` | 151 |
| Theorem | `extra_hamming_N` | 155 |
| Theorem | `extra_digit_reverse_splits` | 159 |
| Theorem | `extra_digits_of_N` | 167 |
| Theorem | `extra_N_mod_100` | 171 |
| Theorem | `extra_nextprime_N` | 175 |
| Theorem | `extra_prevprime_associate` | 179 |
| Theorem | `extra_xor_leftovers` | 183 |
| Theorem | `extra_related_y_cube` | 187 |
| Theorem | `extra_leftover_pair_splits` | 191 |
| Theorem | `extra_first_nibble` | 199 |
| Theorem | `extra_two_bit_advice` | 203 |
| Theorem | `extra_dl_base5` | 207 |
| Theorem | `extra_dl_base9` | 211 |
| Theorem | `extra_gen_pair_42_9` | 215 |
| Theorem | `extra_gen_pair_42_53` | 223 |
| Theorem | `extra_gen_pair_42_93` | 231 |
| Theorem | `extra_y_minus_x` | 239 |
| Theorem | `extra_advice_five_div_lam` | 243 |
| Theorem | `extra_advice_local_9` | 247 |
| Theorem | `extra_euclid_x_minus_y` | 251 |
| Theorem | `extra_low_bits_y` | 255 |
| Theorem | `extra_hensel_p2` | 259 |
| Theorem | `extra_dp` | 263 |
| Theorem | `extra_edp_minus_1` | 267 |
| Theorem | `extra_dq` | 271 |
| Theorem | `extra_edq_minus_1` | 275 |
| Theorem | `extra_shamir_3_7` | 279 |
| Theorem | `extra_rerand_fixed_e` | 283 |

## `SrsaModulus.v`

- L18: Different group or modulus

| Kind | Name | Line |
|---|---|---:|
| Theorem | `modulus_paillier_carrier` | 24 |
| Theorem | `modulus_williams_Ve` | 32 |
| Theorem | `modulus_ou_carrier` | 37 |
| Theorem | `modulus_dj_carrier` | 46 |
| Theorem | `modulus_cocks_jacobi` | 50 |
| Theorem | `modulus_prime_power_field` | 54 |
| Theorem | `modulus_two_safeprimes` | 60 |
| Theorem | `modulus_rw_shape_odd_e` | 71 |
| Theorem | `modulus_twins` | 76 |
| Theorem | `modulus_unbalanced` | 81 |
| Theorem | `modulus_triprime_cube_not_residual` | 91 |
| Theorem | `modulus_prime_field` | 102 |
| Theorem | `modulus_N55_cube_residual_shaped` | 108 |
| Theorem | `modulus_N119_cube_shares` | 114 |
| Theorem | `modulus_N209_cube_shares` | 120 |
| Theorem | `modulus_N221_cube_shares` | 126 |
| Theorem | `modulus_N323_cube_shares` | 132 |
| Theorem | `modulus_prime_cube` | 138 |

## `SrsaOrderArrows.v`

- L14: Order / residual Strong RSA / Factor arrows
  - L24: Order of the pin challenge
  - L79: Mismatch ⇒ Factor; matching local orders do not

| Kind | Name | Line |
|---|---|---:|
| Theorem | `is_order_pin_y_40` | 26 |
| Theorem | `order_yields_residual_sRSA` | 36 |
| Theorem | `order_yields_residual_pin` | 58 |
| Theorem | `order_invert_pin_is_cube_root` | 74 |
| Theorem | `residual_mismatch_factors` | 85 |
| Theorem | `leftover_x_one_sided_pin` | 97 |
| Theorem | `leftover_x_mismatch_factors_pin` | 106 |
| Theorem | `residual_mismatch_factors_pin` | 115 |
| Theorem | `leftover_y_one_sided_pin` | 127 |
| Theorem | `order_mismatch_factors_pin` | 136 |
| Theorem | `leftover_77_one_sided` | 145 |
| Theorem | `leftover_77_mismatch_factors` | 154 |
| Theorem | `matching_247_not_one_sided` | 167 |
| Theorem | `matching_247_gcd_not_proper` | 175 |
| Theorem | `matching_247_two_sided_gcd_is_N` | 185 |

## `SrsaPeriod.v`

- L13: Period: gcd vs multiply
  - L423: KeyGen shape: leftover [x] splits iff local orders mismatch
  - L487: Public exponent lattice [N−1], [N+1] vs trapdoor period
  - L534: Annihilator quality short of [λ]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `period_base3_period` | 22 |
| Theorem | `period_y32_splits` | 30 |
| Theorem | `period_y5_minus_1_splits` | 38 |
| Theorem | `period_y8_minus_1_splits` | 46 |
| Theorem | `period_y10_minus_1_splits` | 54 |
| Theorem | `period_phi8_y_splits` | 62 |
| Theorem | `period_y2_plus_1_gcd` | 70 |
| Theorem | `period_phi5_y_splits` | 74 |
| Theorem | `period_x2_minus_1_int` | 82 |
| Theorem | `period_full_period_no_split` | 86 |
| Theorem | `period_miller_on_period2` | 90 |
| Theorem | `period_local_orders` | 98 |
| Theorem | `period_gcd_pminus1_qminus1` | 105 |
| Theorem | `period_public_d5_pohlig` | 109 |
| Theorem | `period_mismatched_local_orders` | 117 |
| Theorem | `period_lcm_local_orders` | 122 |
| Theorem | `period_v2_local_orders` | 126 |
| Theorem | `period_gcd_path_splits` | 131 |
| Theorem | `period_exp_path_leftover` | 139 |
| Theorem | `period_eq_order_40` | 147 |
| Theorem | `period_eq_not_8` | 151 |
| Theorem | `period_eq_not_5` | 155 |
| Theorem | `period_eq_y40` | 159 |
| Theorem | `period_eq_y20` | 163 |
| Theorem | `period_eq_y8` | 167 |
| Theorem | `period_eq_y5` | 171 |
| Theorem | `period_gcd_y5_splits` | 175 |
| Theorem | `period_gcd_y8_splits` | 183 |
| Theorem | `period_gcd_full_period` | 191 |
| Theorem | `period_after_ord_invert` | 195 |
| Theorem | `period_v2_ord_p` | 203 |
| Theorem | `period_v2_ord_q` | 207 |
| Theorem | `period_v2_ord_N` | 211 |
| Theorem | `period_v2_lam_bigger` | 216 |
| Theorem | `period_x5_minus_1_splits` | 221 |
| Theorem | `period_x8_minus_1_splits` | 229 |
| Theorem | `period_x10_minus_1_splits` | 237 |
| Theorem | `period_x16_minus_1_splits` | 245 |
| Theorem | `period_x4_minus_1` | 253 |
| Theorem | `period_x2_minus_1` | 257 |
| Theorem | `period_same_oracle` | 261 |
| Theorem | `period_ten_order_16` | 265 |
| Theorem | `period_ten_pow8_miller` | 270 |
| Theorem | `period_ten_pow8_splits` | 274 |
| Theorem | `period_ten_pow16` | 282 |
| Theorem | `period_21_order_4` | 286 |
| Theorem | `period_21_sq_splits` | 290 |
| Theorem | `period_89_order_4` | 298 |
| Theorem | `period_77_pminus1` | 302 |
| Theorem | `period_77_qminus1` | 310 |
| Theorem | `period_77_leftover_pohlig` | 318 |
| Theorem | `period_77_ord2_is_lam` | 326 |
| Theorem | `period_two_subgroups_split` | 331 |
| Theorem | `period_three_pohlig_5` | 339 |
| Theorem | `period_three_pohlig_16` | 347 |
| Theorem | `period_three_pow8_no_split` | 355 |
| Theorem | `period_cbrt2_cbrt36_split` | 359 |
| Theorem | `period_cbrt3_cbrt36_split` | 367 |
| Theorem | `period_cbrt3_cbrt2` | 375 |
| Theorem | `period_five_max_order` | 379 |
| Theorem | `period_five_pohlig_5` | 383 |
| Theorem | `period_five_pohlig_16` | 391 |
| Theorem | `period_ord16_to_miller` | 399 |
| Theorem | `period_77_51_is_2_pow7` | 403 |
| Theorem | `period_77_lambda` | 407 |
| Theorem | `period_77_two_pow3` | 411 |
| Theorem | `period_77_two_pow5` | 419 |
| Theorem | `period_187_mismatch_gcd` | 431 |
| Theorem | `period_77_mismatch_gcd` | 435 |
| Theorem | `period_247_match_gcd` | 439 |
| Theorem | `period_247_leftover_pair` | 445 |
| Theorem | `period_247_residual_leaf` | 451 |
| Theorem | `period_247_local_residues` | 462 |
| Theorem | `period_247_matching_local_orders` | 467 |
| Theorem | `period_247_x5_minus_1_no_split` | 474 |
| Theorem | `period_247_x8_minus_1_no_split` | 478 |
| Theorem | `period_247_x6_minus_1_is_N` | 482 |
| Theorem | `period_Nminus1_factors` | 493 |
| Theorem | `period_pohlig_ndiv_Nminus1` | 497 |
| Theorem | `period_ord_ndiv_Nminus1` | 504 |
| Theorem | `period_Nminus1_divisors_no_split` | 510 |
| Theorem | `period_y_Nminus1_no_annihilator` | 514 |
| Theorem | `period_x_Nminus1_no_membership` | 518 |
| Theorem | `period_Nplus1_factors` | 522 |
| Theorem | `period_Nplus1_divisors_no_split` | 526 |
| Theorem | `period_y_Nplus1_no_annihilator` | 530 |
| Theorem | `period_lam_v2_odd_part` | 541 |
| Theorem | `period_M2_no_split` | 546 |
| Theorem | `period_M4_no_split` | 550 |
| Theorem | `period_advice_odd_part_splits` | 554 |
| Theorem | `period_advice_v2_8_splits` | 562 |
| Theorem | `period_advice_v2_16_splits` | 570 |
| Theorem | `period_advice_ord_invert_no_proper` | 578 |
| Theorem | `period_advice_lam_miller` | 582 |

## `SrsaPrimary.v`

- L14: Primary decomposition of [⟨y⟩]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `primary_y20_miller` | 20 |
| Theorem | `primary_y16_five_torsion` | 25 |
| Theorem | `primary_y8_five_torsion` | 30 |
| Theorem | `primary_y5_order8` | 35 |
| Theorem | `primary_y10_order4` | 40 |
| Theorem | `primary_y4_order10` | 44 |
| Theorem | `primary_x_to_8_is_five_torsion` | 48 |
| Theorem | `primary_C8_generator` | 53 |
| Theorem | `primary_C8_squares` | 57 |
| Theorem | `primary_C5_generator` | 61 |
| Theorem | `primary_C5_elements` | 65 |
| Theorem | `primary_cube_bij_C5` | 70 |
| Theorem | `primary_cube_bij_C8` | 74 |
| Theorem | `primary_reconstruct_y` | 78 |
| Theorem | `primary_bezout_5_8` | 82 |
| Theorem | `primary_C8_order2_is_miller` | 86 |
| Theorem | `primary_eight_div_ord` | 90 |
| Theorem | `primary_five_div_ord` | 96 |
| Theorem | `primary_C8_is_y5` | 102 |
| Theorem | `primary_order4_in_C8` | 106 |
| Theorem | `primary_C8_pow6` | 110 |
| Theorem | `primary_C8_pow3` | 114 |
| Theorem | `primary_C8_pow5` | 118 |
| Theorem | `primary_C8_pow7` | 122 |
| Theorem | `primary_C5_pow3` | 126 |
| Theorem | `primary_ker_squaring_C8` | 130 |
| Theorem | `primary_C8_order` | 134 |
| Theorem | `primary_C5_order` | 139 |
| Theorem | `primary_lcm_primaries` | 144 |
| Theorem | `primary_coprime_primaries` | 148 |
| Theorem | `primary_cube_bij_primaries` | 152 |
| Theorem | `primary_x5_generates_C8` | 157 |
| Theorem | `primary_x8_in_C5` | 162 |
| Theorem | `primary_reconstruct_x` | 166 |
| Theorem | `primary_69_generates_C5` | 170 |
| Theorem | `primary_111_generates_C8` | 174 |

## `SrsaResidual.v`

- L14: Residual leftover language
  - L24: Pin geometry of [N] and of [⟨2⟩]
  - L77: Leftover [x] generates [⟨y⟩]
  - L405: Public search slack and forbidden cosets

| Kind | Name | Line |
|---|---|---:|
| Theorem | `residual_phi_over_lambda` | 26 |
| Theorem | `residual_N_mod_8` | 30 |
| Theorem | `residual_bitlength_N` | 34 |
| Theorem | `residual_v2_N_minus_1` | 38 |
| Theorem | `residual_units_not_cyclic` | 43 |
| Theorem | `residual_mod4_shape` | 48 |
| Theorem | `residual_N_mod_8_two_sylow` | 53 |
| Theorem | `residual_y_to_lambda` | 57 |
| Theorem | `residual_y_to_phi` | 61 |
| Theorem | `residual_ord2_is_40` | 65 |
| Theorem | `residual_phi_is_product` | 69 |
| Theorem | `residual_y_to_lam_identity` | 73 |
| Theorem | `residual_x_in_cyc_y` | 79 |
| Theorem | `residual_x_generates` | 83 |
| Theorem | `residual_x_is_y_to_27` | 87 |
| Theorem | `residual_cube_root_of_1` | 91 |
| Theorem | `residual_unique_unit_cube` | 95 |
| Theorem | `residual_e_inv_mod_16` | 99 |
| Theorem | `residual_e_inv_mod_5` | 103 |
| Theorem | `residual_crt_e_inverse` | 107 |
| Theorem | `residual_five_divides_lambda` | 113 |
| Theorem | `residual_local_squares` | 118 |
| Theorem | `residual_qr_both_sides` | 125 |
| Theorem | `residual_not_in_ltwo` | 130 |
| Theorem | `residual_in_lthree_and_lfive` | 134 |
| Theorem | `residual_local_cube_mod_p` | 138 |
| Theorem | `residual_local_x_mod_q` | 144 |
| Theorem | `residual_crt_locals` | 148 |
| Theorem | `residual_bits_of_x` | 153 |
| Theorem | `residual_x_mod_8` | 157 |
| Theorem | `residual_x_minus_1_prime` | 161 |
| Theorem | `residual_x_plus_1_prime` | 165 |
| Theorem | `residual_sixteen_generators` | 169 |
| Theorem | `residual_even_k_not_generator` | 173 |
| Theorem | `residual_y_inv_generator` | 181 |
| Theorem | `residual_x_inv_generator` | 185 |
| Theorem | `residual_y29` | 189 |
| Theorem | `residual_y3_generator` | 193 |
| Theorem | `residual_y9_generator` | 197 |
| Theorem | `residual_five_divides_ord` | 201 |
| Theorem | `residual_eight_divides_ord` | 205 |
| Theorem | `residual_three_index_two` | 209 |
| Theorem | `residual_dl_even` | 213 |
| Theorem | `residual_y_in_square_subgroup` | 217 |
| Theorem | `residual_v2_lambda` | 221 |
| Theorem | `residual_ord_divides_lam` | 226 |
| Theorem | `residual_y_to_ord` | 230 |
| Theorem | `residual_phi_over_lam` | 234 |
| Theorem | `residual_ord_div_lam` | 238 |
| Theorem | `residual_e_coprime_10_16` | 242 |
| Theorem | `residual_five_ndiv_e` | 247 |
| Theorem | `residual_y_local_qr` | 252 |
| Theorem | `residual_bitlength_lam` | 259 |
| Theorem | `residual_lambda_lcm` | 263 |
| Theorem | `residual_y_to_e_inv` | 267 |
| Theorem | `residual_k1_is_y` | 277 |
| Theorem | `residual_k3_is_y_cube` | 281 |
| Theorem | `residual_even_k_shares_ord` | 285 |
| Theorem | `residual_crt_is_residual_x` | 290 |
| Theorem | `residual_ratio_five_torsion` | 294 |
| Theorem | `residual_ratio_y4` | 298 |
| Theorem | `residual_ord_5_smooth` | 302 |
| Theorem | `residual_index_lam_over_ord` | 306 |
| Theorem | `residual_x_order_40_not_20` | 310 |
| Theorem | `residual_three_not_in_cyc_y` | 314 |
| Theorem | `residual_three_full_lambda` | 318 |
| Theorem | `residual_y_even_power_of_3` | 322 |
| Theorem | `residual_product_primaries` | 326 |
| Theorem | `residual_cube_of_x` | 330 |
| Theorem | `residual_y_to_27` | 334 |
| Theorem | `residual_jacobi_x_vs_2` | 338 |
| Theorem | `residual_x_not_in_lten` | 342 |
| Theorem | `residual_pminus1_qminus1` | 346 |
| Theorem | `residual_phi_product` | 351 |
| Theorem | `residual_index_four` | 355 |
| Theorem | `residual_x_order_40` | 359 |
| Theorem | `residual_v2_ord_x` | 363 |
| Theorem | `residual_v2_lam` | 368 |
| Theorem | `residual_x_generates_5_sylow` | 373 |
| Theorem | `residual_N_mod_8_for_2` | 377 |
| Theorem | `residual_ten_jacobi_plus` | 381 |
| Theorem | `residual_ten_not_ord40` | 385 |
| Theorem | `residual_21_mod_8` | 389 |
| Theorem | `residual_ltwo_ord40` | 393 |
| Theorem | `residual_two_ne_y` | 397 |
| Theorem | `residual_four_cosets` | 401 |
| Theorem | `residual_jacobi_plus_count` | 411 |
| Theorem | `residual_phi40_generators` | 416 |
| Theorem | `residual_coset_10_no_split` | 424 |
| Theorem | `residual_coset_2_no_split` | 428 |
| Theorem | `residual_x16_not_1` | 432 |
| Theorem | `residual_x8_not_1` | 436 |
| Theorem | `residual_lam_bitlength` | 440 |
| Theorem | `residual_x_local_qr` | 444 |
| Theorem | `residual_161_mod_8` | 449 |
| Theorem | `residual_x_not_ord16` | 454 |
| Theorem | `residual_x_not_ord10` | 458 |

## `SrsaResidualGRA.v`

- L19: Residual GRA dichotomy
  - L35: Residual-shaped exponents
  - L63: [λ+1] is outside the residual class
  - L101: Constant leftover inverts one [y], not every unit
  - L120: Degree / leading-coefficient fork for residual-shaped [e]
  - L185: Division-free tape denotes a polynomial; integer [P^e = X]
  - L228: Low-degree vanishing on units
  - L395: Roots bound: low-degree + vanish on [1..10] ⇒ [11] | coeffs
  - L507: CRT lift: vanish on [(Z/NZ)*] + low degree ⇒ [N] | coeffs
  - L675: Nodiv tape degree bound
  - L739: Exact degree; square and cube tapes miss units

| Kind | Name | Line |
|---|---|---:|
| Theorem | `residual_shaped_e_3` | 43 |
| Theorem | `residual_shaped_e_lam_minus_1` | 53 |
| Theorem | `not_residual_shaped_e_lam_plus_1` | 65 |
| Theorem | `lambda_plus_one_witness_not_residual` | 73 |
| Theorem | `residual_gra_const81_independent_of_y` | 81 |
| Theorem | `residual_gra_const81_gcd_is_1` | 86 |
| Theorem | `residual_gra_const81_solves_sRSA_not_residual` | 90 |
| Theorem | `residual_gra_const42_inverts_pin_not_8` | 103 |
| Theorem | `residual_gra_const42_misses_unit_2` | 115 |
| Theorem | `residual_shaped_forbids_rational_Pe_XQe` | 122 |
| Theorem | `residual_shaped_e3_leading` | 131 |
| Theorem | `residual_shaped_elam_leading` | 139 |
| Theorem | `residual_gra_Xe_minus_X_N_ndiv_linear` | 147 |
| Theorem | `residual_gra_X3_minus_X_N_ndiv_linear` | 158 |
| Theorem | `residual_gra_X7_minus_X_N_ndiv_linear` | 163 |
| Theorem | `residual_gra_eq_leak_factors` | 171 |
| Theorem | `residual_gra_inv_nonunit_factors` | 181 |
| Theorem | `residual_gra_nodiv_empty_is_nodiv` | 189 |
| Theorem | `residual_gra_identity_tape_is_y` | 193 |
| Theorem | `residual_gra_identity_tape_not_cube` | 197 |
| Theorem | `residual_gra_nodiv_integer_identity_forbidden` | 201 |
| Theorem | `residual_gra_nodiv_cube_identity_forbidden` | 213 |
| Theorem | `residual_gra_mul_denotes_square` | 224 |
| Theorem | `residual_identity_is_low_degree` | 243 |
| Lemma | `residual_X3_eval` | 249 |
| Lemma | `cube_minus_id_factor` | 253 |
| Lemma | `prime_divides_cube_minus_id` | 257 |
| Lemma | `residual_X3_roots_mod_prime` | 273 |
| Theorem | `residual_X3_roots_mod_11` | 306 |
| Theorem | `residual_X3_unit_2_not_root_mod_11` | 316 |
| Theorem | `residual_X3_unit_2_not_root_mod_17` | 326 |
| Theorem | `residual_X3_roots_mod_17` | 336 |
| Theorem | `residual_const_Pe_minus_X_nth1` | 346 |
| Theorem | `residual_const_N_ndiv_linear` | 350 |
| Theorem | `residual_nodiv_identity_denotes_X` | 356 |
| Theorem | `residual_identity_cube_minus_y` | 360 |
| Theorem | `residual_nodiv_const_is_nodiv` | 370 |
| Theorem | `residual_nodiv_const_denotes` | 374 |
| Theorem | `residual_low_degree_identity_not_all_Fp_units` | 385 |
| Lemma | `pin_Fp_star_length` | 406 |
| Lemma | `forall_pin_Fp_star` | 409 |
| Lemma | `pin_Fp_star_coprime` | 419 |
| Lemma | `pin_Fp_star_distinct_mod_11` | 432 |
| Theorem | `residual_low_degree_units_divides_11` | 438 |
| Theorem | `residual_nodiv_low_degree_units_divides_11` | 452 |
| Theorem | `residual_identity_nth1_ndiv_11` | 470 |
| Theorem | `residual_identity_cannot_vanish_on_Fp_star` | 474 |
| Lemma | `residual_const_Pe_degree` | 487 |
| Theorem | `residual_const_cannot_vanish_on_Fp_star` | 491 |
| Lemma | `pin_Fq_star_length` | 516 |
| Lemma | `forall_pin_Fq_star` | 519 |
| Lemma | `pin_Fq_star_distinct_mod_17` | 529 |
| Lemma | `pin_1_16_coprime_N` | 535 |
| Lemma | `pin_crt_lift_11_spec` | 550 |
| Lemma | `pin_N_divides_11` | 556 |
| Lemma | `pin_N_divides_17` | 561 |
| Lemma | `pin_11_17_divides_N` | 566 |
| Lemma | `residual_ZN_units_vanish_at_Fq` | 575 |
| Theorem | `residual_low_degree_ZN_units_divides_17` | 597 |
| Theorem | `residual_low_degree_ZN_units_divides_N` | 612 |
| Theorem | `residual_nodiv_low_degree_ZN_units_divides_N` | 626 |
| Theorem | `residual_identity_cannot_vanish_on_ZN_units` | 644 |
| Theorem | `residual_const_cannot_vanish_on_ZN_units` | 659 |
| Theorem | `residual_nodiv_bound_le3_Q_lt10` | 684 |
| Theorem | `residual_nodiv_short_ZN_units_divides_N` | 699 |
| Theorem | `residual_identity_bound_is_1` | 715 |
| Theorem | `residual_square_bound_is_2` | 719 |
| Theorem | `residual_x3_bound_is_3` | 723 |
| Theorem | `residual_two_squarings_bound_is_4` | 727 |
| Theorem | `residual_two_squarings_outside_window` | 731 |
| Theorem | `residual_trapdoor_deg27_outside_window` | 735 |
| Theorem | `residual_square_denotes_X2` | 751 |
| Theorem | `residual_square_degree_eq_bound` | 756 |
| Theorem | `residual_square_eval` | 766 |
| Theorem | `residual_square_Q_degree_is_6` | 775 |
| Theorem | `residual_square_Q_nth1` | 783 |
| Theorem | `residual_square_cannot_vanish_on_ZN_units` | 791 |
| Theorem | `residual_square_unit_2_not_root` | 811 |
| Theorem | `residual_cube_is_nodiv` | 821 |
| Theorem | `residual_cube_denotes_X3` | 825 |
| Theorem | `residual_cube_degree_eq_bound` | 830 |
| Theorem | `residual_cube_eval` | 842 |
| Theorem | `residual_cube_Q_degree_is_9` | 853 |
| Theorem | `residual_cube_Q_nth1` | 861 |
| Theorem | `residual_cube_cannot_vanish_on_ZN_units` | 869 |
| Theorem | `residual_cube_unit_2_not_root` | 893 |
| Theorem | `residual_trapdoor_inverts_pin` | 905 |
| Theorem | `residual_trapdoor_not_a_low_degree_identity` | 909 |

## `SrsaRootPoly.v`

- L20: Two writings of an [e]-th root polynomial on units
  - L48: Coefficient of a mixed CRT monomial splits
  - L78: CRT binomial
  - L205: Pin CRT binomial: coefficients split
  - L358: Trapdoor monomial [X^d]: degree is [d], coefficients do not split
  - L429: They agree on units and differ as polynomials
  - L470: Short [e]-th-root polynomials: a coefficient splits [N]
  - L899: The window is sharp; nodiv GRA in it splits

| Kind | Name | Line |
|---|---|---:|
| Lemma | `cong_1_mod_p_0_mod_q_gcd` | 50 |
| Lemma | `crt_binomial_eval` | 84 |
| Lemma | `crt_binomial_mod_p` | 97 |
| Lemma | `crt_binomial_mod_q` | 118 |
| Lemma | `local_eth_root` | 139 |
| Theorem | `crt_binomial_inverts_units` | 167 |
| Theorem | `pin_root_ca_mod` | 210 |
| Theorem | `pin_root_cb_mod` | 214 |
| Theorem | `pin_inv3_local` | 218 |
| Theorem | `pin_root_ca_splits` | 223 |
| Theorem | `pin_root_cb_splits` | 236 |
| Theorem | `pin_crt_binomial_inverts_units` | 249 |
| Theorem | `pin_crt_binomial_eval_unit` | 272 |
| Lemma | `pin_ed_minus_1_divides_lam` | 285 |
| Lemma | `pin_powm_ed` | 294 |
| Theorem | `pin_unique_unit_eth_root` | 310 |
| Theorem | `pin_crt_binomial_at_y` | 322 |
| Theorem | `pin_crt_binomial_residual` | 334 |
| Theorem | `pin_crt_binomial_degree` | 341 |
| Theorem | `pin_crt_binomial_outside_window` | 345 |
| Theorem | `pin_crt_binomial_coeff_da` | 350 |
| Theorem | `pin_crt_binomial_coeff_db` | 354 |
| Theorem | `pin_trapdoor_monomial_eval` | 362 |
| Theorem | `pin_trapdoor_ed_inv` | 370 |
| Lemma | `pin_powm_de` | 374 |
| Theorem | `pin_trapdoor_monomial_inverts_units` | 391 |
| Theorem | `pin_trapdoor_monomial_at_y` | 399 |
| Theorem | `pin_trapdoor_monomial_degree` | 403 |
| Theorem | `pin_trapdoor_monomial_leading` | 407 |
| Theorem | `pin_trapdoor_degree_is_d` | 417 |
| Theorem | `pin_trapdoor_monomial_outside_window` | 424 |
| Theorem | `pin_root_polys_agree_on_units` | 431 |
| Theorem | `pin_crt_binomial_neq_monomial` | 451 |
| Theorem | `pin_crt_binomial_inverts_2` | 461 |
| Lemma | `unique_eth_root_mod_prime` | 480 |
| Lemma | `pin_Fq_units_of_N_length` | 504 |
| Lemma | `pairwise_distinct_mod_filter` | 508 |
| Lemma | `pin_Fq_units_of_N_distinct` | 526 |
| Lemma | `pin_Fq_units_of_N_coprime` | 533 |
| Lemma | `pin_inv3_q_lt_window` | 550 |
| Lemma | `nth_poly_sub` | 554 |
| Lemma | `poly_degree_sub_le` | 562 |
| Lemma | `mod_product_r` | 573 |
| Lemma | `mod_product_l` | 585 |
| Lemma | `short_root_local_mod_q` | 591 |
| Lemma | `short_root_diff_vanishes` | 631 |
| Lemma | `short_root_q_divides_diff` | 653 |
| Lemma | `poly_eval_all_div` | 671 |
| Lemma | `poly_eval_single_support` | 685 |
| Lemma | `pin_two_pow_db_mod_p` | 717 |
| Lemma | `gcd_q_not_p` | 727 |
| Lemma | `powm_div_cong` | 754 |
| Lemma | `finite_support_cases` | 768 |
| Theorem | `short_root_poly_some_coeff_splits` | 792 |
| Theorem | `pin_crt_root_poly_is_short` | 887 |
| Theorem | `pin_crt_root_poly_short_splits` | 891 |
| Theorem | `no_root_poly_deg_lt_dq` | 901 |
| Theorem | `pin_Xn_dp_does_not_invert_all_units` | 918 |
| Theorem | `nodiv_gra_short_dq_splits` | 929 |
| Theorem | `nodiv_identity_bound_lt_dq` | 949 |
| Theorem | `nodiv_square_bound_lt_dq` | 954 |

## `SrsaWriteE.v`

- L15: Public maps of leftover [e]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `emap_phi_y_even` | 21 |
| Theorem | `emap_hamming_even` | 26 |
| Theorem | `emap_lsb_y_even` | 31 |
| Theorem | `emap_e25_shares_lambda` | 35 |
| Theorem | `emap_lambda_y_even` | 39 |
| Theorem | `emap_bitlength_even` | 44 |
| Theorem | `emap_tau_leftover_e9` | 49 |
| Theorem | `emap_sigma_leftover` | 53 |
| Theorem | `emap_rad_even` | 57 |
| Theorem | `emap_omega_even` | 62 |
| Theorem | `emap_Omega_even` | 66 |
| Theorem | `emap_lpf_hits_cube` | 70 |
| Theorem | `emap_y_plus_1_is_nextprime` | 74 |
| Theorem | `emap_odd_part_e9` | 80 |
| Theorem | `emap_odd_hamming_shares` | 84 |
| Theorem | `emap_gcd_yminus1_Nminus1` | 89 |
| Theorem | `emap_phi3_y_leftover_shaped` | 93 |
| Theorem | `emap_v2_yminus1` | 103 |
| Theorem | `emap_mersenne_leftover` | 109 |
| Theorem | `emap_N_mod_y_hits_e7` | 113 |
| Theorem | `emap_fermatish_leftover` | 117 |
| Theorem | `emap_smooth_even` | 121 |
| Theorem | `emap_e_eq_N` | 126 |
| Theorem | `emap_e_eq_Nminus2` | 130 |
| Theorem | `emap_e_y_minus_1_shares` | 134 |
| Theorem | `emap_e_two_y_plus_1` | 138 |
| Theorem | `emap_e_two_y_minus_1` | 142 |
| Theorem | `emap_prevprime_e31` | 146 |
| Theorem | `emap_dedekind_psi_even` | 150 |
| Theorem | `emap_ord_y_even` | 155 |
| Theorem | `emap_phi_N_even` | 159 |
| Theorem | `emap_aliquot_shares` | 163 |
| Theorem | `emap_e17_leftover` | 168 |
| Theorem | `emap_e_N_plus_1_even` | 172 |
| Theorem | `emap_e_N_minus_1_even` | 176 |
| Theorem | `emap_e_lam_minus_1` | 180 |
| Theorem | `emap_phi_y_plus_1` | 184 |
| Theorem | `emap_digit_sum_e9` | 188 |
| Theorem | `emap_repunit_111` | 192 |
| Theorem | `emap_primorial_even` | 196 |
| Theorem | `emap_fermat_5_shares` | 201 |
| Theorem | `emap_collatz_e21` | 206 |
| Theorem | `emap_squarefree_core_e9` | 210 |
| Theorem | `emap_e47_second_leftover` | 214 |
| Theorem | `emap_e23_ninth` | 218 |
| Theorem | `emap_e19_leftover` | 222 |
| Theorem | `emap_e_eq_x` | 226 |
| Theorem | `emap_e_N_minus_lam` | 230 |
| Theorem | `emap_e_nextprime_N` | 234 |
| Theorem | `emap_prevprime_even_peel` | 239 |
| Theorem | `emap_e_prime` | 243 |
| Theorem | `emap_prime_e7` | 248 |

## `SrsaWriteX.v`

- L15: Public maps of leftover [x]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `xmap_odd_monomial` | 27 |
| Theorem | `xmap_associate` | 31 |
| Theorem | `xmap_midpoint` | 35 |
| Theorem | `xmap_encrypt_as_decrypt` | 44 |
| Theorem | `xmap_not_coppersmith_small` | 48 |
| Theorem | `xmap_odd_monomial_y5` | 53 |
| Theorem | `xmap_y_to_the_y` | 57 |
| Theorem | `xmap_y_to_the_N` | 61 |
| Theorem | `xmap_y_to_Nminus1` | 65 |
| Theorem | `xmap_y_to_Nplus1` | 69 |
| Theorem | `xmap_floor_sqrt_y` | 73 |
| Theorem | `xmap_half_y` | 78 |
| Theorem | `xmap_bitrev_36_is_9` | 82 |
| Theorem | `xmap_triangular` | 86 |
| Theorem | `xmap_nextprime_as_x` | 90 |
| Theorem | `xmap_fibonacci_y` | 94 |
| Theorem | `xmap_exp_base2` | 98 |
| Theorem | `xmap_exp_base3` | 102 |
| Theorem | `xmap_phi3_of_y` | 106 |
| Theorem | `xmap_inv_then_cube` | 110 |
| Theorem | `xmap_cube_then_inv` | 114 |
| Theorem | `xmap_hybrid_crt` | 118 |
| Theorem | `xmap_mismatched_crt_splits` | 122 |
| Theorem | `xmap_integer_jnt` | 130 |
| Theorem | `xmap_y2_plus_1` | 135 |
| Theorem | `xmap_x_eq_Nminus1` | 139 |
| Theorem | `xmap_floor_sqrt_N` | 143 |
| Theorem | `xmap_phi3_of_N` | 147 |
| Theorem | `xmap_y7_onesided` | 151 |
| Theorem | `xmap_y9_cubes_to_root` | 155 |
| Theorem | `xmap_y11_onesided` | 159 |
| Theorem | `xmap_floor_y_div_3` | 163 |
| Theorem | `xmap_floor_N_div_y` | 167 |
| Theorem | `xmap_three_y_onesided` | 171 |
| Theorem | `xmap_y_minus_1` | 175 |
| Theorem | `xmap_y_plus_1_as_x` | 179 |
| Theorem | `xmap_two_y_plus_1` | 183 |
| Theorem | `xmap_y2_minus_1` | 187 |
| Theorem | `xmap_gray_code` | 191 |
| Theorem | `xmap_nibble_swap_nonunit` | 195 |
| Theorem | `xmap_popcount_as_x` | 203 |
| Theorem | `xmap_catalan_C5` | 207 |
| Theorem | `xmap_lucas_L8` | 217 |
| Theorem | `xmap_floor_y_three_halves` | 221 |
| Theorem | `xmap_shift_left_2_onesided` | 225 |
| Theorem | `xmap_y_mod_16` | 229 |
| Theorem | `xmap_eightbit_palindrome` | 233 |
| Theorem | `xmap_partition_p10` | 237 |
| Theorem | `xmap_catalan_C6_nonunit` | 245 |
| Theorem | `xmap_y_inv_sq` | 253 |
| Theorem | `xmap_x_eq_phi` | 257 |
| Theorem | `xmap_x_bitlength_N` | 261 |
| Theorem | `xmap_nextprime_mod_N` | 265 |
| Theorem | `xmap_identity_not_root` | 269 |
| Theorem | `xmap_y35_onesided` | 273 |
| Theorem | `xmap_inv_lam_minus_1` | 281 |
| Theorem | `xmap_pkcs_pad` | 285 |
| Theorem | `xmap_sqrt_then_n_nplus1` | 289 |
| Theorem | `xmap_integer_sqrt_unit` | 301 |
| Theorem | `xmap_binary_encrypt` | 305 |
| Theorem | `xmap_mont_form` | 309 |

## `StrongPrimes.v`

- L9: Safe / strong primes: generation-side refusal of one-sided annihilators

| Kind | Name | Line |
|---|---|---:|
| Lemma | `two_not_safe` | 31 |
| Lemma | `safe_prime_pminus1` | 38 |
| Theorem | `safe_prime_resists_p1` | 60 |
| Theorem | `large_factor_blocks_smooth_claim` | 78 |
| Theorem | `safe_prime_blocks_smooth_claim` | 87 |
| Theorem | `safe_pair_lambda` | 98 |
| Theorem | `strong_prime_resists_both` | 131 |
| Lemma | `prime_5` | 142 |
| Theorem | `five_is_safe` | 150 |
| Theorem | `five_resists_B1` | 156 |

## `StrongRSAPeel.v`

- L17: Standard-model Strong-RSA witness peel
  - L29: Non-unit [x]
  - L68: Jacobi [−1] forces odd [e]
  - L101: Even [e] is a square root
  - L149: [λ]-type: [x = y] is an annihilator
  - L244: Residual leaf (open: solver ⇒ factor is the live target)
  - L278: Self-randomization and related queries
  - L326: SAGM handle still peels
  - L346: Four square roots of 1; mixed splits, [−1] does not

| Kind | Name | Line |
|---|---|---:|
| Theorem | `srsa_unit_y_forces_unit_x` | 31 |
| Theorem | `srsa_gcd_proper_is_factor` | 44 |
| Theorem | `srsa_nonunit_x_pin` | 58 |
| Theorem | `srsa_jacobi_minus1_forces_odd_e` | 70 |
| Theorem | `srsa_jacobi_two_is_minus1` | 89 |
| Theorem | `srsa_lambda_type_on_jacobi_minus1` | 93 |
| Theorem | `srsa_even_e_is_square_root` | 103 |
| Theorem | `srsa_even_e_pin` | 115 |
| Theorem | `srsa_associate_neg6_does_not_split` | 119 |
| Theorem | `srsa_mixed_root_of_36_factors` | 124 |
| Theorem | `srsa_even_e_nonassociate_factors` | 134 |
| Theorem | `srsa_x_eq_y_annihilates` | 151 |
| Theorem | `srsa_lambda_type_annihilator_pin` | 181 |
| Theorem | `srsa_lambda_type_miller_splits` | 191 |
| Theorem | `srsa_lambda_type_miller_factors` | 201 |
| Lemma | `prime_7` | 212 |
| Theorem | `srsa_safeprime_lambda_30` | 220 |
| Theorem | `srsa_safeprime_lambda_type` | 224 |
| Theorem | `srsa_safeprime_g0_square` | 229 |
| Theorem | `srsa_safeprime_miller_gcd` | 233 |
| Theorem | `srsa_safeprime_miller_factors` | 237 |
| Theorem | `srsa_residual_pin` | 253 |
| Theorem | `srsa_fixed_e_rerand` | 280 |
| Theorem | `srsa_fixed_e_rerand_pin` | 293 |
| Theorem | `srsa_poly_e_not_rerand_invariant` | 300 |
| Theorem | `srsa_related_y_square` | 306 |
| Theorem | `srsa_related_pin` | 322 |
| Theorem | `srsa_sagm_handle_unit` | 328 |
| Theorem | `srsa_sagm_lambda_type_peel` | 333 |
| Theorem | `srsa_sagm_product_reused` | 338 |
| Theorem | `srsa_sqrt1_120_splits` | 348 |
| Theorem | `srsa_minus1_no_split` | 354 |
| Theorem | `srsa_120_plus_1` | 359 |
| Theorem | `srsa_miller_66` | 363 |
| Theorem | `srsa_four_sqrt1` | 367 |

## `Succinct.v`

- L17: Logarithmic fold of the bilinear CRS combine
  - L36: List halves and the fold [a_L + 2 a_R]
  - L136: One round of the posted proof (13 residues)
  - L147: Prover
  - L228: Verifier: no slot list, no per-slot bound search
  - L262: Size: [13 log2 n + 2]
  - L300: Completeness on the pin family and QAP

| Kind | Name | Line |
|---|---|---:|
| Lemma | `poly_eval_app` | 45 |
| Lemma | `nn_app` | 62 |
| Lemma | `nn_firstn` | 71 |
| Lemma | `nn_skipn` | 83 |
| Lemma | `nn_map_mul_nonneg` | 95 |
| Lemma | `nn_poly_add` | 104 |
| Lemma | `nn_succ_fold` | 116 |
| Lemma | `poly_eval_succ_fold` | 125 |
| Lemma | `succ_round_pack_length` | 200 |
| Lemma | `succ_prove_cons_length` | 206 |
| Lemma | `succ_prove_rounds_log` | 213 |
| Theorem | `succ_proof_len_is_log` | 264 |
| Theorem | `succ_proof_len_n4` | 275 |
| Theorem | `succ_proof_len_n16` | 285 |
| Theorem | `succ_proof_len_bound_pin` | 295 |
| Theorem | `succ_pin_n2_accepts` | 305 |
| Theorem | `succ_pin_n2_rejects_group_mul` | 317 |
| Theorem | `succ_pin_n2_sum_neq_prod` | 327 |
| Theorem | `succ_pin_qap` | 334 |

## `Takagi.v`

- L9: Takagi multi-power RSA: [N = p² q]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `fermat_minus_one_divides` | 26 |
| Theorem | `euler_p2` | 41 |
| Theorem | `sqrt1_mod_p2_is_pm1` | 66 |
| Theorem | `carmichael_takagi` | 127 |
| Theorem | `lambda_divides_phi_takagi` | 177 |
| Theorem | `lambda_p2_divides_lambda_takagi` | 186 |
| Theorem | `takagi_ed_is_id_p2` | 191 |
| Theorem | `takagi_mixed_sqrt1_splits` | 237 |

## `ThresholdRSA.v`

- L10: Threshold / mediated RSA, as exponent algebra

| Kind | Name | Line |
|---|---|---:|
| Theorem | `additive_share_combines` | 21 |
| Theorem | `additive_three_shares` | 33 |
| Theorem | `mediated_rsa_is_two_shares` | 47 |
| Theorem | `share_refresh_by_zero` | 61 |
| Theorem | `shamir_two_of_three` | 82 |
| Lemma | `powm_ed_is_base` | 105 |
| Theorem | `shoup_extract_from_kd` | 145 |

## `TimeLock.v`

- L10: Rivest–Shamir–Wagner time-lock, trapdoor side

| Kind | Name | Line |
|---|---|---:|
| Theorem | `timelock_trapdoor_reduces_exp` | 17 |

## `Torus.v`

- L15: The Williams torus mod [N]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `lucasU_0` | 33 |
| Lemma | `lucasU_1` | 36 |
| Lemma | `lp_of_nat_0` | 49 |
| Lemma | `lp_inv_inv` | 52 |
| Theorem | `torus_order_divides_product` | 59 |
| Theorem | `pq_plus_one_is_not_torus_order` | 66 |
| Theorem | `N_plus_one_misses_p_plus_q` | 71 |
| Theorem | `lucas_eval_annihilator_is_none` | 94 |
| Theorem | `lucas_eval_annihilator_is_not_N_plus_one` | 98 |
| Theorem | `lucas_eval_id_is_V0` | 102 |
| Theorem | `typeB_on_torus_is_williams` | 106 |
| Theorem | `williams_onesided_gcd` | 114 |
| Theorem | `williams_onesided_not_full_N` | 129 |
| Theorem | `fermat_gives_torus_order` | 151 |
| Theorem | `fermat_leak_is_torus_period` | 161 |
| Theorem | `constructible_torus_is_V_eq_2` | 174 |

## `TranscriptOracle.v`

- L13: Transcripts and oracles (bit leakage after the key is used)
  - L18: Shared algebra
  - L104: T5 — [(c/N) = (m/N)] for odd [e]
  - L171: T24 / T25 — sign homomorphism and decrypt blinding
  - L246: T12 — LSB of [2m mod N] is the half-interval bit
  - L299: T11 — a comparison oracle recovers [m] by interval halving
  - L342: T4 — common modulus, coprime exponents
  - L413: T29 — Bellcore / CRT-fault signature
  - L464: K1 — one-sided vanishing predicate factors
  - L493: K5 — Williams [(2/p)] is the KeyGen shape, not a transcript bit
  - L545: K13 / T6 — odd [d] sends [−1] to [−1]; no extra 2-height
  - L574: RSA inverter vs Rabin inverter
  - L617: T7 — finite products of raw signatures
  - L689: T16 — a [(·/p)] oracle plus the public product is [(·/q)]
  - L768: Constructor slot vs K1
  - L806: T8 — [e=3], a cube below [N] *is* a raw signature of that cube
  - L836: T10 — Bleichenbacher wrap: a residue in [0, B) pins an interval

| Kind | Name | Line |
|---|---|---:|
| Lemma | `powm_mul_l_mod` | 20 |
| Lemma | `mod_mod_factor` | 30 |
| Lemma | `powm_mod_factor` | 43 |
| Lemma | `powm_exp_mod_factor` | 54 |
| Lemma | `even_pow_neg1_is_one` | 67 |
| Lemma | `odd_pow_neg1` | 83 |
| Theorem | `euler_odd_power` | 110 |
| Theorem | `rsa_cipher_euler_eq_message` | 132 |
| Theorem | `rsa_cipher_euler_eq_message_q` | 151 |
| Theorem | `sign_homomorphism` | 173 |
| Theorem | `sign_of_one` | 185 |
| Theorem | `sign_inverse` | 194 |
| Theorem | `decrypt_blinding` | 212 |
| Theorem | `decrypt_double_is_double` | 234 |
| Theorem | `lsb_double_decides_half` | 254 |
| Theorem | `lsb_double_decides_half_ge` | 284 |
| Lemma | `pow2_nat_pos` | 301 |
| Lemma | `pow2_nat_succ` | 304 |
| Theorem | `recover_interval_correct` | 321 |
| Theorem | `recover_from_half_tests` | 336 |
| Theorem | `common_modulus_identity` | 344 |
| Theorem | `common_modulus_recovers` | 364 |
| Lemma | `coprime_to_nonneg_bezout` | 385 |
| Theorem | `bellcore_factors` | 415 |
| Theorem | `bellcore_is_factor` | 445 |
| Theorem | `one_sided_congruence_factors` | 466 |
| Lemma | `prime_5` | 499 |
| Theorem | `williams_N_mod8` | 507 |
| Theorem | `non_williams_N_mod8_5` | 517 |
| Theorem | `williams_two_is_shape` | 521 |
| Theorem | `non_williams_two_chars` | 535 |
| Theorem | `sign_neg1_odd` | 547 |
| Theorem | `odd_exp_preserves_minus1` | 559 |
| Theorem | `rsa_inverter_recovers_message` | 591 |
| Theorem | `sign_hom_3` | 623 |
| Theorem | `sign_of_msg_product_one` | 639 |
| Theorem | `sign_weighted_commute` | 656 |
| Theorem | `sign_weighted_product` | 670 |
| Lemma | `euler_sign_of_pm1` | 697 |
| Lemma | `euler_sign_sq` | 714 |
| Theorem | `other_legendre_from_product` | 725 |
| Theorem | `cipher_jacobi_eq_message` | 738 |
| Theorem | `onesided_plain_one_factors` | 773 |
| Theorem | `ctor_slot_mod_r_need_not_factor` | 788 |
| Theorem | `cube_below_N` | 808 |
| Theorem | `e3_small_cube_verifies` | 823 |
| Theorem | `bleiche_wrap_interval` | 838 |
| Theorem | `pkcs15_prefix_is_type2` | 864 |
| Theorem | `manger_is_stricter_than_type2` | 874 |

## `TwoPartyPair.v`

- L14: 2-of-2 root oracle is not a pairing of two group elements

| Kind | Name | Line |
|---|---|---:|
| Theorem | `two_party_root_is_eth` | 27 |
| Theorem | `two_party_root_is_dstar_power` | 42 |
| Theorem | `two_party_root_hom` | 57 |
| Theorem | `two_party_next_forces_dstar` | 91 |

## `TwoPrimary.v`

- L14: The 2-primary part of [(Z/NZ)*]
  - L39: [v₂] on odds and on [2 · odd]
  - L161: Four square roots of 1
  - L312: 2-height of a unit, and mismatch splits [N]
  - L387: [v₂(λ)] is the max, and the residue table mod 8
  - L503: Existence of a 2-height

| Kind | Name | Line |
|---|---|---:|
| Lemma | `pow2n_pos` | 30 |
| Lemma | `pow2n_succ` | 33 |
| Lemma | `gcd2_of_odd` | 41 |
| Lemma | `val2_of_odd` | 53 |
| Lemma | `val2_two_times_odd` | 67 |
| Lemma | `odd_prime_val2_ge1` | 91 |
| Theorem | `blum_val2_is_1` | 113 |
| Lemma | `mod4_1_val2_ge2` | 125 |
| Theorem | `rw_pair_val2_11` | 151 |
| Lemma | `crt2_mod` | 165 |
| Lemma | `square_mod_one_of_pm1` | 182 |
| Lemma | `powm_square_one_of_pm1` | 199 |
| Theorem | `four_sqrt1` | 208 |
| Lemma | `mod_mod_of_factor` | 252 |
| Lemma | `mixed_pm_not_one` | 259 |
| Lemma | `mixed_pm_not_minus1` | 275 |
| Theorem | `mixed_sqrt1_splits` | 297 |
| Lemma | `two_height_unique` | 327 |
| Theorem | `height_mismatch_splits` | 340 |
| Theorem | `rw_is_blum_2adic` | 375 |
| Theorem | `unbalanced_not_matched` | 379 |
| Theorem | `lambda_val2_is_max` | 389 |
| Theorem | `mod8_3_val2_is_1` | 395 |
| Theorem | `mod8_7_val2_is_1` | 402 |
| Theorem | `mod8_5_val2_is_2` | 410 |
| Theorem | `mod8_1_val2_ge3` | 427 |
| Lemma | `val2_ge_of_mod_pow2` | 450 |
| Theorem | `dist_forced_2adic_both_deep` | 482 |
| Theorem | `matched_deep_is_both_deep` | 495 |
| Lemma | `find_least_spec` | 517 |
| Lemma | `find_least_le` | 547 |
| Lemma | `find_least_min` | 551 |
| Lemma | `find_least_hits` | 556 |
| Theorem | `two_height_exists` | 570 |
| Theorem | `two_height_exists_fermat` | 593 |
| Lemma | `two_height_scale_forward` | 626 |
| Theorem | `two_height_of_odd_multiple` | 643 |
| Lemma | `unit_pow_pm1` | 677 |
| Lemma | `min_from_spec` | 691 |
| Lemma | `unit_has_min_order` | 720 |
| Lemma | `powm_order_divides` | 759 |
| Lemma | `odd_part_of_divisor` | 789 |
| Lemma | `pow2_divides_pow2` | 802 |
| Lemma | `pow2_cancel_odd` | 834 |
| Theorem | `cyclic_units_holds` | 848 |
| Theorem | `cyclic_same_t` | 888 |

## `TwoSylow.v`

- L14: Structure of the 2-Sylow of [(Z/NZ)*]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `powm_2_mod_prime_pm1` | 22 |
| Theorem | `sqrt1_is_crt_pm1` | 29 |
| Theorem | `four_divides_lambda_iff_deep` | 53 |
| Theorem | `no_order_4_when_lambda_val2_1` | 87 |
| Theorem | `blum_has_no_order_4` | 103 |
| Theorem | `sqrt1_pm_translates_square` | 121 |

## `UnknownOrder.v`

- L10: Computational problems in a group of unknown order
  - L39: The named problems
  - L79: What the trapdoor actually buys

| Kind | Name | Line |
|---|---|---:|
| Lemma | `trapdoor_gives_inverse` | 33 |
| Theorem | `lambda_solves_RSA_on_units` | 81 |
| Theorem | `d_yields_annihilator` | 96 |

## `Wiener.v`

- L10: Small [d]: [e/N] approximates [k/d]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `wiener_relation` | 28 |
| Lemma | `N_minus_phi` | 35 |
| Lemma | `wiener_numerator` | 40 |
| Lemma | `small_d_small_k` | 51 |
| Lemma | `wiener_abs_numerator` | 72 |
| Theorem | `wiener_basin_from_gap` | 84 |
| Lemma | `k_lt_d_of_e_lt_phi` | 107 |
| Theorem | `wiener_classical_sufficient` | 123 |

## `WireEq.v`

- L14: Wire equality: [w0 = w1] is [w0 + 0 = w1]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `wire_eq_sat` | 18 |
| Theorem | `wire_eq_complete` | 27 |
| Theorem | `wire_eq_same_encoding` | 41 |

## `WirePoK.v`

- L17: Knowledge of a QAP witness against a specialized CRS

| Kind | Name | Line |
|---|---|---:|
| Theorem | `wire_slots_assemble` | 36 |
| Theorem | `wire_slot_eqdl` | 49 |
| Theorem | `wire_slot_extracts` | 71 |
| Theorem | `three_wire_assemble` | 93 |

_2436 theorems/lemmas/corollaries/examples across 119 files._
