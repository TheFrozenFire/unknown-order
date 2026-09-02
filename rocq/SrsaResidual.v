From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import SolverShape.

Open Scope Z_scope.

(** * Residual leftover language

    What a residual pair [(x,e)] on this pin is allowed to be:
    [x] generates [⟨y⟩] ([ord=40], [φ(40)=16] generators), [e]
    invertible mod [16] and mod [5], unique unit cube, local CRT,
    Jacobi [+1].  A solver that writes outside this set is not
    residual.  Does not inhabit [srsa_residual_leaf] as
    [Problem_Factor]. *)

(** ** Pin geometry of [N] and of [⟨2⟩] *)

Theorem residual_phi_over_lambda :
  160 / 80 = 2.
Proof. reflexivity. Qed.

Theorem residual_N_mod_8 :
  187 mod 8 = 3.
Proof. reflexivity. Qed.

Theorem residual_bitlength_N :
  2 ^ 7 <= 187 < 2 ^ 8.
Proof. split; lia. Qed.

Theorem residual_v2_N_minus_1 :
  Z.even 186 = true /\
  Z.odd (186 / 2) = true.
Proof. split; reflexivity. Qed.

Theorem residual_units_not_cyclic :
  Z.gcd 10 16 = 2 /\
  80 <> 160.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem residual_mod4_shape :
  11 mod 4 = 3 /\
  17 mod 4 = 1.
Proof. split; reflexivity. Qed.

Theorem residual_N_mod_8_two_sylow :
  187 mod 8 = 3.
Proof. reflexivity. Qed.

Theorem residual_y_to_lambda :
  powm 36 80 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_y_to_phi :
  powm 36 160 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_ord2_is_40 :
  powm 2 40 187 = 1 /\
  powm 2 20 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem residual_phi_is_product :
  (11 - 1) * (17 - 1) = 160.
Proof. reflexivity. Qed.

Theorem residual_y_to_lam_identity :
  powm 36 80 187 = 1 /\
  1 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

(** ** Leftover [x] generates [⟨y⟩] *)

Theorem residual_x_in_cyc_y :
  powm 42 40 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_x_generates :
  powm 42 40 187 = 1 /\
  powm 42 20 187 = 67 /\
  67 <> 1.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem residual_x_is_y_to_27 :
  powm 36 27 187 = 42 /\
  Z.gcd 27 40 = 1.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem residual_cube_root_of_1 :
  powm 1 3 187 = 1 /\
  powm 67 3 187 = 67 /\
  67 <> 1.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem residual_unique_unit_cube :
  powm 42 3 187 = 36 /\
  (forall z, Z.coprime z 187 -> powm z 3 187 = 36 -> z mod 187 = 42).
Proof.
  split; [vm_compute; reflexivity|].
  exact shape_unique_unit_cube_root_of_36.
Qed.

Theorem residual_e_inv_mod_16 :
  Z.gcd 3 16 = 1.
Proof. reflexivity. Qed.

Theorem residual_e_inv_mod_5 :
  Z.gcd 3 5 = 1.
Proof. reflexivity. Qed.

Theorem residual_crt_e_inverse :
  27 mod 16 = 11 /\
  27 mod 5 = 2 /\
  11 + 16 * 1 = 27.
Proof. repeat split; reflexivity. Qed.

Theorem residual_five_divides_lambda :
  Z.gcd 5 80 = 5 /\
  Z.gcd 5 80 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem residual_local_squares :
  42 mod 11 = 9 /\
  3 * 3 = 9 /\
  42 mod 17 = 8 /\
  5 * 5 mod 17 = 8.
Proof. repeat split; reflexivity. Qed.

Theorem residual_qr_both_sides :
  42 mod 11 = 9 /\
  42 mod 17 = 8.
Proof. split; reflexivity. Qed.

Theorem residual_not_in_ltwo :
  powm 2 40 187 = 1 /\
  powm 2 1 187 <> 42 /\
  powm 2 20 187 <> 42.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem residual_in_lthree_and_lfive :
  powm 3 42 187 = 42 /\
  powm 5 34 187 = 42.
Proof. vm_compute. split; reflexivity. Qed.

Theorem residual_local_cube_mod_p :
  42 mod 11 = 9 /\
  powm 9 3 11 = 3 /\
  36 mod 11 = 3.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem residual_local_x_mod_q :
  42 mod 17 = 8.
Proof. reflexivity. Qed.

Theorem residual_crt_locals :
  9 + 11 * 3 = 42 /\
  42 mod 17 = 8.
Proof. split; reflexivity. Qed.

Theorem residual_bits_of_x :
  32 + 8 + 2 = 42.
Proof. reflexivity. Qed.

Theorem residual_x_mod_8 :
  42 mod 8 = 2.
Proof. reflexivity. Qed.

Theorem residual_x_minus_1_prime :
  Z.gcd 41 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_x_plus_1_prime :
  Z.gcd 43 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_sixteen_generators :
  40 / 2 * 4 / 5 = 16.
Proof. reflexivity. Qed.

Theorem residual_even_k_not_generator :
  Z.gcd 2 40 = 2 /\
  powm 36 2 187 = 174 /\
  powm 174 3 187 = 47 /\
  Z.gcd (47 - 36) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem residual_y_inv_generator :
  powm 36 39 187 = 26 /\
  (36 * 26) mod 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem residual_x_inv_generator :
  powm 36 13 187 = 49 /\
  (42 * 49) mod 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem residual_y29 :
  powm 36 29 187 = 15.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_y3_generator :
  powm 36 3 187 = 93 /\
  Z.gcd 3 40 = 1.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem residual_y9_generator :
  powm 36 9 187 = 70 /\
  Z.gcd 9 40 = 1.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem residual_five_divides_ord :
  (5 | 40).
Proof. exists 8. reflexivity. Qed.

Theorem residual_eight_divides_ord :
  (8 | 40).
Proof. exists 5. reflexivity. Qed.

Theorem residual_three_index_two :
  powm 3 80 187 = 1 /\
  powm 3 40 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem residual_dl_even :
  Z.even 46 = true.
Proof. reflexivity. Qed.

Theorem residual_y_in_square_subgroup :
  powm 3 46 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_v2_lambda :
  80 = 16 * 5 /\
  Z.even 16 = true.
Proof. split; reflexivity. Qed.

Theorem residual_ord_divides_lam :
  (40 | 80).
Proof. exists 2. reflexivity. Qed.

Theorem residual_y_to_ord :
  powm 36 40 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_phi_over_lam :
  160 / 80 = 2.
Proof. reflexivity. Qed.

Theorem residual_ord_div_lam :
  (40 | 80).
Proof. exists 2. reflexivity. Qed.

Theorem residual_e_coprime_10_16 :
  Z.gcd 3 10 = 1 /\
  Z.gcd 3 16 = 1.
Proof. split; reflexivity. Qed.

Theorem residual_five_ndiv_e :
  3 mod 5 = 3 /\
  3 <> 0.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem residual_y_local_qr :
  36 mod 11 = 3 /\
  5 * 5 mod 11 = 3 /\
  36 mod 17 = 2 /\
  6 * 6 mod 17 = 2.
Proof. repeat split; reflexivity. Qed.

Theorem residual_bitlength_lam :
  2 ^ 6 <= 80 < 2 ^ 7.
Proof. split; lia. Qed.

Theorem residual_lambda_lcm :
  Z.lcm 10 16 = 80.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_y_to_e_inv :
  powm 36 27 187 = 42 /\
  Z.gcd 27 40 = 1 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [vm_compute; reflexivity|].
  split; [reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem residual_k1_is_y :
  powm 36 1 187 = 36 /\
  36 <> 42.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem residual_k3_is_y_cube :
  powm 36 3 187 = 93 /\
  93 <> 42.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem residual_even_k_shares_ord :
  Z.gcd 2 40 = 2 /\
  Z.gcd 2 40 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem residual_crt_is_residual_x :
  9 + 11 * 3 = 42 /\
  powm 42 3 187 = 36.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem residual_ratio_five_torsion :
  (42 * 15) mod 187 = 69 /\
  powm 69 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem residual_ratio_y4 :
  (42 * 53) mod 187 = 169 /\
  powm 36 4 187 = 169.
Proof. vm_compute. split; reflexivity. Qed.

Theorem residual_ord_5_smooth :
  8 * 5 = 40.
Proof. reflexivity. Qed.

Theorem residual_index_lam_over_ord :
  80 / 40 = 2.
Proof. reflexivity. Qed.

Theorem residual_x_order_40_not_20 :
  powm 42 40 187 = 1 /\
  powm 42 20 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem residual_three_not_in_cyc_y :
  powm 3 40 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem residual_three_full_lambda :
  powm 3 80 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_y_even_power_of_3 :
  Z.even 46 = true.
Proof. reflexivity. Qed.

Theorem residual_product_primaries :
  (155 * 69) mod 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_cube_of_x :
  powm 42 3 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_y_to_27 :
  powm 36 27 187 = 42.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_jacobi_x_vs_2 :
  187 mod 8 = 3 /\
  42 mod 11 = 9 /\
  3 * 3 = 9.
Proof. repeat split; reflexivity. Qed.

Theorem residual_x_not_in_lten :
  powm 10 1 187 <> 42 /\
  powm 10 8 187 <> 42.
Proof. vm_compute. split; discriminate. Qed.

Theorem residual_pminus1_qminus1 :
  11 - 1 = 10 /\
  17 - 1 = 16.
Proof. split; reflexivity. Qed.

Theorem residual_phi_product :
  10 * 16 = 160.
Proof. reflexivity. Qed.

Theorem residual_index_four :
  160 / 40 = 4.
Proof. reflexivity. Qed.

Theorem residual_x_order_40 :
  powm 42 40 187 = 1 /\
  powm 42 16 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem residual_v2_ord_x :
  40 = 8 * 5 /\
  8 = 2 ^ 3.
Proof. split; reflexivity. Qed.

Theorem residual_v2_lam :
  80 = 16 * 5 /\
  16 = 2 ^ 4.
Proof. split; reflexivity. Qed.

Theorem residual_x_generates_5_sylow :
  powm 42 8 187 = 69 /\
  powm 69 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem residual_N_mod_8_for_2 :
  187 mod 8 = 3.
Proof. reflexivity. Qed.

Theorem residual_ten_jacobi_plus :
  10 mod 8 = 2.
Proof. reflexivity. Qed.

Theorem residual_ten_not_ord40 :
  powm 10 16 187 = 1 /\
  powm 10 8 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem residual_21_mod_8 :
  21 mod 8 = 5.
Proof. reflexivity. Qed.

Theorem residual_ltwo_ord40 :
  powm 2 40 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_two_ne_y :
  2 <> 36.
Proof. discriminate. Qed.

Theorem residual_four_cosets :
  160 / 40 = 4.
Proof. reflexivity. Qed.

Theorem residual_x16_not_1 :
  powm 42 16 187 = 86 /\
  86 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem residual_x8_not_1 :
  powm 42 8 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem residual_lam_bitlength :
  2 ^ 6 <= 80 < 2 ^ 7.
Proof. split; lia. Qed.

Theorem residual_x_local_qr :
  42 mod 11 = 9 /\
  42 mod 17 = 8.
Proof. split; reflexivity. Qed.

Theorem residual_161_mod_8 :
  161 mod 8 = 1 /\
  2 mod 8 = 2.
Proof. split; reflexivity. Qed.

Theorem residual_x_not_ord16 :
  powm 42 16 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem residual_x_not_ord10 :
  powm 42 10 187 <> 1.
Proof. vm_compute. discriminate. Qed.
