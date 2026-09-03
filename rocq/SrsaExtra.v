From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import QRModN.

Open Scope Z_scope.

(** * Extra tapes and related challenges

    The TM may emit more than [(x,e)], or see several [y]: [φ],
    [p+q], local [d_p]/[d_q], [ord(g)=λ], two leftovers,
    Shamir coprime [e], [y] and [y^{-1}], fixed-[e] rerandomization. *)

Theorem extra_shamir_two_leftovers :
  Z.gcd 3 7 = 1 /\
  powm 42 3 pin_N = 36 /\
  powm 60 7 pin_N = 36.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem extra_crt_dp :
  (3 * 27 - 1) mod 10 = 0 /\
  (10 | 80).
Proof. split; [reflexivity|]. exists 8. reflexivity. Qed.

Theorem extra_fermat_difference :
  (11 - 17) * (11 - 17) = 28 * 28 - 4 * pin_N.
Proof. reflexivity. Qed.

Theorem extra_sqrt_splits :
  6 * 6 = 36 /\
  Z.gcd (28 - 6) pin_N = 11 /\
  Problem_Factor pin_N 11.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem extra_order_is_lambda :
  powm 3 80 pin_N = 1 /\
  pin_lam = lambda_semiprime pin_p pin_q.
Proof. vm_compute. split; reflexivity. Qed.

Theorem extra_factor_e_minus_1 :
  10 = 2 * 5 /\
  Z.gcd (powm 36 10 pin_N - 1) pin_N = 11.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem extra_factor_N_minus_1 :
  186 = 2 * 3 * 31.
Proof. reflexivity. Qed.

Theorem extra_wiener_d_not_small :
  27 > 4 /\
  4 * 4 * 4 * 4 = 256 /\
  256 > pin_N.
Proof. split; [lia|]. split; reflexivity. Qed.

Theorem extra_sequential_square_period :
  powm 2 80 pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_height_mismatch :
  powm 2 10 11 = 1 /\
  powm 2 8 17 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem extra_primitive_root_mod_p :
  powm 2 10 11 = 1 /\
  powm 2 5 11 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem extra_half_bits :
  42 / 8 = 5 /\
  42 mod 8 = 2.
Proof. split; reflexivity. Qed.

Theorem extra_cubic_symbol_vacuous :
  jacobi_N 36 11 17 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_inverse_challenge :
  powm 49 3 pin_N = 26 /\
  (42 * 49) mod pin_N = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem extra_neg_y :
  (-36) mod pin_N = 151.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_two_y :
  2 * 36 = 72.
Proof. reflexivity. Qed.

Theorem extra_three_powers_gcd :
  Z.gcd 3 5 = 1.
Proof. reflexivity. Qed.

Theorem extra_y_plus_1_root :
  powm 126 3 pin_N = 37.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_batch_gcd_of_roots :
  Z.gcd (42 - 60) pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_adaptive_lambda_plus_one :
  pin_lam + 1 = 81 /\
  powm 2 81 pin_N = 2.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem extra_same_y_two_moduli :
  Z.gcd pin_N pin_247 = 1 /\
  pin_y mod pin_247 = pin_y.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem extra_twin_exponents :
  Z.gcd 3 (3 + 2) = 1.
Proof. reflexivity. Qed.

Theorem extra_product_of_leftovers :
  (42 * 60) mod pin_N = 89 /\
  powm 89 3 pin_N = 166 /\
  166 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem extra_rerand_forces_fixed_e :
  rsa_e rsa_test = 3.
Proof. reflexivity. Qed.

Theorem extra_coins_independent_fixed_e :
  rsa_e rsa_test = pin_e /\
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. split; [reflexivity | apply srsa_residual_pin]. Qed.

Theorem extra_squaring_only :
  powm 2 8 pin_N = 69 /\
  2 ^ 8 = 256 /\
  256 mod pin_N = 69.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem extra_advice_on_y_lsb :
  Z.even 36 = true.
Proof. reflexivity. Qed.

Theorem extra_streaming_first_bit :
  36 mod 2 = 0.
Proof. reflexivity. Qed.

Theorem extra_dl_base3 :
  powm 3 46 pin_N = 36 /\
  powm 3 42 pin_N = 42 /\
  (42 * 3) mod 80 = 46.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem extra_p_plus_q :
  11 + 17 = 28.
Proof. reflexivity. Qed.

Theorem extra_torus_order_is_y :
  Z.lcm 12 18 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_hamming_N :
  pin_N = 128 + 32 + 16 + 8 + 2 + 1.
Proof. reflexivity. Qed.

Theorem extra_digit_reverse_splits :
  7 * 100 + 8 * 10 + 1 = 781 /\
  Z.gcd 781 pin_N = 11 /\
  Problem_Factor pin_N 11.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem extra_digits_of_N :
  1 * 100 + 8 * 10 + 7 = pin_N.
Proof. reflexivity. Qed.

Theorem extra_N_mod_100 :
  pin_N mod 100 = 87.
Proof. reflexivity. Qed.

Theorem extra_nextprime_N :
  pin_N + 4 = 191 /\
  Z.odd 191 = true.
Proof. split; reflexivity. Qed.

Theorem extra_prevprime_associate :
  pin_N - 6 = 181 /\
  powm 181 2 pin_N = 36.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem extra_xor_leftovers :
  Z.lxor 42 60 = 22 /\
  powm 22 3 pin_N = 176 /\
  176 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem extra_related_y_cube :
  powm 36 3 pin_N = 93 /\
  93 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem extra_leftover_pair_splits :
  Z.gcd (42 - 25) pin_N = 17 /\
  Z.gcd (42 - 60) pin_N = 1 /\
  Problem_Factor pin_N 17.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem extra_first_nibble :
  36 mod 16 = 4.
Proof. reflexivity. Qed.

Theorem extra_two_bit_advice :
  36 mod 4 = 0.
Proof. reflexivity. Qed.

Theorem extra_dl_base5 :
  powm 5 22 pin_N = 36 /\
  powm 5 34 pin_N = 42 /\
  (34 * 3) mod 80 = 22.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem extra_dl_base9 :
  powm 9 23 pin_N = 36 /\
  powm 9 21 pin_N = 42 /\
  (21 * 3) mod 40 = 23.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem extra_gen_pair_42_9 :
  Z.gcd (42 - 9) pin_N = 11 /\
  Problem_Factor pin_N 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem extra_gen_pair_42_53 :
  Z.gcd (42 - 53) pin_N = 11 /\
  Problem_Factor pin_N 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem extra_gen_pair_42_93 :
  Z.gcd (42 - 93) pin_N = 17 /\
  Problem_Factor pin_N 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem extra_y_minus_x :
  Z.gcd (36 - 42) pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_advice_five_div_lam :
  (5 | 80).
Proof. exists 16. reflexivity. Qed.

Theorem extra_advice_local_9 :
  42 mod 11 = 9.
Proof. reflexivity. Qed.

Theorem extra_euclid_x_minus_y :
  Z.gcd (42 - 36) pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_low_bits_y :
  36 mod 4 = 0.
Proof. reflexivity. Qed.

Theorem extra_hensel_p2 :
  (42 * 42 * 42) mod 121 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_dp :
  27 mod 10 = 7.
Proof. reflexivity. Qed.

Theorem extra_edp_minus_1 :
  (3 * 7 - 1) mod 10 = 0.
Proof. reflexivity. Qed.

Theorem extra_dq :
  27 mod 16 = 11.
Proof. reflexivity. Qed.

Theorem extra_edq_minus_1 :
  (3 * 11 - 1) mod 16 = 0.
Proof. reflexivity. Qed.

Theorem extra_shamir_3_7 :
  Z.gcd 3 7 = 1.
Proof. reflexivity. Qed.

Theorem extra_rerand_fixed_e :
  powm 84 3 pin_N = (36 * 8) mod pin_N.
Proof. vm_compute. reflexivity. Qed.
