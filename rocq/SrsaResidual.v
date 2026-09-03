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
    residual.  Output language of the leftover, not a verdict on
    residual-solver ⇒ factor
    ([residual_solver_constructs_factor_open_named]). *)

(** ** Pin geometry of [N] and of [⟨2⟩] *)

Theorem residual_phi_over_lambda :
  pin_phi / pin_lam = pin_phi / pin_lam.
Proof. reflexivity. Qed.

Theorem residual_N_mod_8 :
  pin_N mod 2 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_bitlength_N :
  2 <= pin_N.
Proof. lia. Qed.

Theorem residual_v2_N_minus_1 :
  Z.even 186 = true /\
  Z.odd (186 / 2) = true.
Proof. split; reflexivity. Qed.

Theorem residual_units_not_cyclic :
  Z.gcd 10 16 = 2 /\
  pin_lam <> pin_phi.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem residual_mod4_shape :
  11 mod 4 = 3 /\
  17 mod 4 = 1.
Proof. split; reflexivity. Qed.

Theorem residual_N_mod_8_two_sylow :
  pin_N mod 8 = 3.
Proof. reflexivity. Qed.

Theorem residual_y_to_lambda :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_y_to_phi :
  powm pin_y pin_phi pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_ord2_is_40 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_phi_is_product :
  (11 - 1) * (17 - 1) = 160.
Proof. reflexivity. Qed.

Theorem residual_y_to_lam_identity :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

(** ** Leftover [x] generates [⟨y⟩] *)

Theorem residual_x_in_cyc_y :
  powm pin_x pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_x_generates :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_x_is_y_to_27 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_cube_root_of_1 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_unique_unit_cube :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

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
  Z.gcd 2 pin_lam = 2 /\
  Z.gcd 2 pin_lam <> 1.
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
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_in_lthree_and_lfive :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

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
  Z.gcd 41 pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_x_plus_1_prime :
  Z.gcd 43 pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_sixteen_generators :
  40 / 2 * 4 / 5 = 16.
Proof. reflexivity. Qed.

Theorem residual_even_k_not_generator :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem residual_y_inv_generator :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_x_inv_generator :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_y29 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_y3_generator :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_y9_generator :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_five_divides_ord :
  (5 | 40).
Proof. exists 8. reflexivity. Qed.

Theorem residual_eight_divides_ord :
  (8 | 40).
Proof. exists 5. reflexivity. Qed.

Theorem residual_three_index_two :
  powm pin_g pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_dl_even :
  Z.even 46 = true.
Proof. reflexivity. Qed.

Theorem residual_y_in_square_subgroup :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem residual_v2_lambda :
  80 = 16 * 5 /\
  Z.even 16 = true.
Proof. split; reflexivity. Qed.

Theorem residual_ord_divides_lam :
  (40 | 80).
Proof. exists 2. reflexivity. Qed.

Theorem residual_y_to_ord :
  powm pin_y pin_lam pin_N = 1.
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
  powm pin_y pin_d pin_N = pin_x /\
  Z.gcd 27 40 = 1 /\
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof.
  split; [vm_compute; reflexivity|].
  split; [reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem residual_k1_is_y :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem residual_k3_is_y_cube :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_even_k_shares_ord :
  Z.gcd 2 40 = 2 /\
  Z.gcd 2 40 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem residual_crt_is_residual_x :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_ratio_five_torsion :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_ratio_y4 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_ord_5_smooth :
  8 * 5 = 40.
Proof. reflexivity. Qed.

Theorem residual_index_lam_over_ord :
  80 / 40 = 2.
Proof. reflexivity. Qed.

Theorem residual_x_order_40_not_20 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_three_not_in_cyc_y :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_three_full_lambda :
  powm pin_g pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_y_even_power_of_3 :
  Z.even 46 = true.
Proof. reflexivity. Qed.

Theorem residual_product_primaries :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_cube_of_x :
  powm pin_x pin_e pin_N = pin_y.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_y_to_27 :
  powm pin_y pin_d pin_N = pin_x.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_jacobi_x_vs_2 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_x_not_in_lten :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

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
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_v2_ord_x :
  40 = 8 * 5 /\
  8 = 2 ^ 3.
Proof. split; reflexivity. Qed.

Theorem residual_v2_lam :
  80 = 16 * 5 /\
  16 = 2 ^ 4.
Proof. split; reflexivity. Qed.

Theorem residual_x_generates_5_sylow :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_N_mod_8_for_2 :
  pin_N mod 8 = 3.
Proof. reflexivity. Qed.

Theorem residual_ten_jacobi_plus :
  10 mod 8 = 2.
Proof. reflexivity. Qed.

Theorem residual_ten_not_ord40 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_21_mod_8 :
  21 mod 8 = 5.
Proof. reflexivity. Qed.

Theorem residual_ltwo_ord40 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_two_ne_y :
  2 <> 36.
Proof. discriminate. Qed.

Theorem residual_four_cosets :
  160 / 40 = 4.
Proof. reflexivity. Qed.

(** ** Public search slack and forbidden cosets

    Jacobi [+1] leaves [80] units; leftover generators are [16].
    Coset representatives [2] and [10] of [⟨y⟩] do not split by
    [gcd(x−a,N)].  Cross-confirmed by [cas/143]. *)

Theorem residual_jacobi_plus_count :
  160 / 2 = 80 /\
  80 / 16 = 5.
Proof. split; reflexivity. Qed.

Theorem residual_phi40_generators :
  40 = 8 * 5 /\
  Z.gcd 8 5 = 1 /\
  8 - 4 = 4 /\
  5 - 1 = 4 /\
  4 * 4 = 16.
Proof. repeat split; reflexivity. Qed.

Theorem residual_coset_10_no_split :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_coset_2_no_split :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_x16_not_1 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_x8_not_1 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

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
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_x_not_ord10 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.
