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

- L12: Cubic residuosity when cubing is not a permutation

| Kind | Name | Line |
|---|---|---:|
| Theorem | `cubing_invertible_on_units` | 27 |
| Theorem | `cube_root_map_is_cube` | 56 |
| Theorem | `cube_euler_one_direction` | 70 |
| Theorem | `three_divides_lambda_forbids_e3` | 109 |

## `CyclicCount.v`

- L8: Cyclic-model 2-height counts

| Kind | Name | Line |
|---|---|---:|
| Lemma | `sum_up_ext` | 42 |
| Lemma | `cyclic_count_agree_below` | 54 |
| Lemma | `cyclic_count_top` | 69 |
| Theorem | `cyclic_count_sum` | 79 |
| Theorem | `cyclic_mismatch_11_17` | 110 |
| Theorem | `miller_150_of_158` | 117 |
| Theorem | `cyclic_mismatch_14_is_15_16` | 122 |
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

- L10: Evaluation pairing on [μ_n]: [e(x,k) = x^k]

| Kind | Name | Line |
|---|---|---:|
| Theorem | `eval_pair_stays_in_mu` | 26 |
| Theorem | `eval_pair_add` | 43 |
| Theorem | `eval_pair_mul_base` | 56 |
| Theorem | `eval_pair_reduce_mod_n` | 71 |
| Theorem | `eval_pair_image_divides_n` | 94 |
| Theorem | `eval_pair_mu2` | 104 |
| Theorem | `eval_pair_mu2_on_mixed` | 119 |
| Theorem | `omega_cube_is_one` | 134 |
| Theorem | `eval_pair_mu3` | 154 |
| Theorem | `mu2_is_mu6` | 167 |
| Theorem | `mu3_is_mu6` | 182 |
| Theorem | `eval_pair_mu6` | 197 |

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

## `Hardness.v`

- L12: Relation-level structure of the named problems
  - L26: Factoring as a relation
  - L31: RSA is a one-way permutation on units, not a predicate
  - L60: RSA vs strong RSA (relations)
  - L121: Order divides the exponent
  - L168: One-sided small exponent (the Type-B winning condition)
  - L230: Order assumption and fractional root

| Kind | Name | Line |
|---|---|---:|
| Theorem | `rsa_units_are_eth_powers` | 37 |
| Theorem | `trapdoor_inverts_RSA` | 48 |
| Theorem | `rsa_solution_is_strong_RSA` | 68 |
| Theorem | `lambda_solves_strong_RSA` | 82 |
| Lemma | `strong_RSA_trivial_at_one` | 106 |
| Lemma | `rsa_trivial_at_one` | 114 |
| Lemma | `order_divides_annihilator` | 123 |
| Theorem | `order_divides_lambda` | 152 |
| Theorem | `one_sided_low_order_factors` | 180 |
| Theorem | `one_sided_low_order_is_factor` | 212 |
| Lemma | `adaptive_root_is_strong_RSA` | 225 |
| Theorem | `order_is_annihilator` | 236 |
| Theorem | `low_order_is_annihilator` | 245 |
| Theorem | `lambda_is_annihilator_on_units` | 254 |
| Theorem | `annihilator_plus_one_is_strong_RSA` | 267 |
| Theorem | `rsa_is_fractional_root` | 284 |
| Theorem | `strong_RSA_is_fractional_root` | 300 |
| Theorem | `annihilator_is_fractional_root_of_one` | 315 |
| Theorem | `ar_C_implies_strong_RSA` | 344 |
| Theorem | `ar_C_requires_C` | 353 |
| Theorem | `strong_RSA_is_ar_C_iff` | 358 |
| Theorem | `lambda_plus_one_11_17` | 369 |
| Theorem | `lambda_plus_one_11_17_not_prime` | 373 |
| Theorem | `lambda_solves_search_11_17` | 381 |
| Theorem | `search_lambda_plus_one_misses_prime_AR` | 392 |
| Theorem | `adaptive_root_known_product_breaks` | 410 |
| Theorem | `adaptive_root_smooth_power_breaks` | 426 |

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
| Theorem | `rsa_test_base2_g0` | 114 |
| Theorem | `rsa_test_base2_chain` | 119 |
| Theorem | `rsa_test_base2_splits` | 125 |

## `MillerHeight.v`

- L12: Miller-from-[d] as 2-heights on an odd multiple of [odd_part(λ)]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `miller_t_pos` | 23 |
| Lemma | `miller_t_odd` | 29 |
| Lemma | `miller_t_multiple_of_lambda_odd` | 35 |
| Lemma | `powm_one_mod_factor` | 53 |
| Theorem | `miller_height_exists` | 66 |
| Theorem | `miller_from_d` | 103 |
| Theorem | `rsa_test_base2_heights` | 126 |
| Theorem | `rsa_test_miller_from_d` | 141 |

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

- L6: First-class skips

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

- L13: Orders of units, as objects
  - L26: Uniqueness and the divide criterion
  - L74: Existence from a positive annihilator
  - L158: [ord(a^k) = ord(a) / gcd(ord(a), k)]
  - L220: [lcm] of orders divides [λ]
  - L285: 2-height is [v₂(ord)] at a common odd multiple of [odd_part(ord)]

| Kind | Name | Line |
|---|---|---:|
| Lemma | `is_order_unique` | 28 |
| Lemma | `powm_one_of_divide` | 41 |
| Theorem | `order_iff_divides` | 57 |
| Lemma | `order_exists_from_annihilator` | 79 |
| Theorem | `order_exists_prime` | 129 |
| Theorem | `order_exists_semiprime` | 143 |
| Theorem | `order_of_power` | 160 |
| Theorem | `lcm_orders_divides_lambda` | 222 |
| Lemma | `is_order_2_of` | 249 |
| Theorem | `minus1_order_2_rsa_test` | 263 |
| Theorem | `mixed67_order_2_rsa_test` | 269 |
| Theorem | `lcm_two_order2_not_lambda` | 275 |
| Lemma | `powm_eq_1_iff_order_divides` | 287 |
| Lemma | `pow2_divides_pow2` | 298 |
| Theorem | `two_height_is_val2_ord` | 321 |
| Theorem | `order_2_mod_11` | 380 |
| Theorem | `order_2_mod_17` | 391 |
| Theorem | `two_height_independent_of_odd_multiple` | 404 |
| Theorem | `height_is_val2_ord_textbook` | 420 |

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

- L9: RSA: instance, private exponent [d], and the RSA problem
  - L223: Why a polynomial in [N] cannot be a handle

| Kind | Name | Line |
|---|---|---:|
| Lemma | `rsa_N_gt_1` | 37 |
| Lemma | `rsa_lambda_pos` | 44 |
| Lemma | `rsa_lambda_gt_1` | 50 |
| Lemma | `rsa_phi_pos` | 69 |
| Lemma | `rsa_lambda_divides_phi` | 75 |
| Lemma | `rsa_ed_minus_1_divides` | 78 |
| Lemma | `rsa_ed_gt_1` | 87 |
| Theorem | `rsa_dec_enc_units` | 100 |
| Theorem | `rsa_enc_dec_units` | 124 |
| Lemma | `rsa_d_is_cube_root_map` | 151 |
| Lemma | `prime_11` | 161 |
| Lemma | `prime_17` | 170 |
| Lemma | `rsa_test_lambda` | 180 |
| Lemma | `rsa_test_phi` | 183 |
| Lemma | `rsa_test_inv` | 186 |
| Lemma | `rsa_test_coprime_e` | 189 |
| Theorem | `rsa_test_N` | 204 |
| Theorem | `rsa_test_vector` | 207 |
| Theorem | `rsa_test_roundtrip` | 211 |
| Theorem | `rsa_test_annihilator` | 215 |
| Theorem | `N_cong_q_mod_pminus1` | 230 |
| Theorem | `gcd_polyN_pminus1_is_gcd_at_q` | 241 |

## `RabinWilliams.v`

- L12: Rabin–Williams: squaring in [(Z/NZ)*] with the Williams tweak
  - L31: The Rabin problem
  - L41: Prime shape
  - L107: Williams tweak: among [{±a, ±2a}] exactly one Legendre pair
  - L210: Rabin reduction: two non-associated square roots factor [N]
  - L293: Verification shape: [s²] is one of the four tweaks of [H].
  - L311: Keygen obligation on top of the RSA rulers: the mod-8 split.

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
| Theorem | `rabin_oracle_nonassociate_factors` | 268 |
| Lemma | `rw_verify_of_root` | 304 |
| Lemma | `kg_rw_implies_blum` | 315 |
| Lemma | `kg_rw_pminus1_almost_odd` | 323 |

## `Range2.v`

- L14: Two-bit value from bits

| Kind | Name | Line |
|---|---|---:|
| Theorem | `range2_bits` | 24 |
| Theorem | `range2_bit_qap` | 34 |
| Theorem | `range2_encoding` | 51 |
| Theorem | `range2_eval_commit` | 67 |

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
  - L520: Layer 5 — lifted KeyGen spec
  - L576: Layer 6 — arity 3
  - L630: Unassembled [d*] is not ZK; it is a trapdoor
  - L839: SRS checks: each next value is the [e]-th root of the last
  - L922: Relations: discrete log of the SRS is not strong RSA

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
| Theorem | `product_carries_component_keygen` | 528 |
| Theorem | `product_common_e_inverts` | 534 |
| Theorem | `product_refuses_shared_prime` | 544 |
| Theorem | `d_star_gt_lambda_div_e` | 550 |
| Theorem | `carmichael_shared3` | 588 |
| Theorem | `d_star_unique_mod_lambda` | 648 |
| Theorem | `d_star_inverts_on_A` | 664 |
| Theorem | `d_star_inverts_on_B` | 678 |
| Theorem | `d_star_ed_minus_1_divides_lambda` | 692 |
| Theorem | `d_star_annihilates_shared` | 705 |
| Theorem | `d_star_decrypts_B` | 729 |
| Theorem | `d_star_decrypts_A` | 744 |
| Lemma | `coprime_powm` | 769 |
| Lemma | `shared_N_gt_1` | 795 |
| Theorem | `dstar_power_crs_is_powm` | 804 |
| Theorem | `shared_dec_is_eth_root` | 846 |
| Theorem | `srs_first_checks` | 873 |
| Theorem | `srs_step_checks` | 895 |
| Theorem | `srs_first_is_rsa` | 936 |
| Theorem | `srs_first_is_strong_rsa` | 951 |
| Theorem | `lambda_plus_one_is_other_strong_rsa` | 967 |
| Theorem | `dstar_inverts_every_unit` | 986 |
| Lemma | `powm_eq_implies_abs_annihilator` | 1010 |
| Theorem | `dlog_of_srs_agrees_mod_order` | 1054 |
| Theorem | `dlog_at_full_order_inverts_e` | 1077 |

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
  - L612: T7 — finite products of raw signatures
  - L684: T16 — a [(·/p)] oracle plus the public product is [(·/q)]
  - L763: Constructor slot vs K1
  - L801: T8 — [e=3], a cube below [N] *is* a raw signature of that cube
  - L831: T10 — Bleichenbacher wrap: a residue in [0, B) pins an interval

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
| Theorem | `rsa_inverter_recovers_message` | 586 |
| Theorem | `sign_hom_3` | 618 |
| Theorem | `sign_of_msg_product_one` | 634 |
| Theorem | `sign_weighted_commute` | 651 |
| Theorem | `sign_weighted_product` | 665 |
| Lemma | `euler_sign_of_pm1` | 692 |
| Lemma | `euler_sign_sq` | 709 |
| Theorem | `other_legendre_from_product` | 720 |
| Theorem | `cipher_jacobi_eq_message` | 733 |
| Theorem | `onesided_plain_one_factors` | 768 |
| Theorem | `ctor_slot_mod_r_need_not_factor` | 783 |
| Theorem | `cube_below_N` | 803 |
| Theorem | `e3_small_cube_verifies` | 818 |
| Theorem | `bleiche_wrap_interval` | 833 |
| Theorem | `pkcs15_prefix_is_type2` | 859 |
| Theorem | `manger_is_stricter_than_type2` | 869 |

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

_1216 theorems/lemmas/corollaries/examples across 86 files._
