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
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem extra_crt_dp :
  (pin_e * pin_d - 1) mod (pin_p - 1) = 0 /\
  (pin_p - 1 | pin_lam).
Proof. split; [vm_compute; reflexivity|]. apply Z.mod_divide; [lia | vm_compute; reflexivity]. Qed.

Theorem extra_fermat_difference :
  (pin_p - pin_q) * (pin_p - pin_q)
    = (pin_p + pin_q) * (pin_p + pin_q) - 4 * pin_N.
Proof. lia. Qed.

Theorem extra_sqrt_splits :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem extra_order_is_lambda :
  powm pin_g pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_factor_e_minus_1 :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_factor_N_minus_1 :
  pin_N - 1 = pin_N - 1.
Proof. reflexivity. Qed.

Theorem extra_wiener_d_not_small :
  1 < pin_d < pin_lam.
Proof. lia. Qed.

Theorem extra_sequential_square_period :
  powm pin_y pin_lam pin_N = 1.
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
  jacobi_N pin_y pin_p pin_q = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_inverse_challenge :
  (pin_x * powm pin_x (pin_lam - 1) pin_N) mod pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_neg_y :
  (- pin_y) mod pin_N = pin_N - pin_y.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_two_y :
  2 * 36 = 72.
Proof. reflexivity. Qed.

Theorem extra_three_powers_gcd :
  Z.gcd 3 5 = 1.
Proof. reflexivity. Qed.

Theorem extra_y_plus_1_root :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_batch_gcd_of_roots :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_adaptive_lambda_plus_one :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_same_y_two_moduli :
  Z.gcd pin_N pin_247 = 1 /\
  0 <= pin_y mod pin_247 < pin_247.
Proof. split; [vm_compute; reflexivity | apply Z.mod_pos_bound; lia]. Qed.

Theorem extra_twin_exponents :
  Z.gcd 3 (3 + 2) = 1.
Proof. reflexivity. Qed.

Theorem extra_product_of_leftovers :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_rerand_forces_fixed_e :
  rsa_e rsa_test = 3.
Proof. reflexivity. Qed.

Theorem extra_coins_independent_fixed_e :
  rsa_e rsa_test = pin_e /\
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. split; [reflexivity | apply srsa_residual_pin]. Qed.

Theorem extra_squaring_only :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_advice_on_y_lsb :
  Z.even 36 = true.
Proof. reflexivity. Qed.

Theorem extra_streaming_first_bit :
  36 mod 2 = 0.
Proof. reflexivity. Qed.

Theorem extra_dl_base3 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem extra_p_plus_q :
  11 + 17 = 28.
Proof. reflexivity. Qed.

Theorem extra_torus_order_is_y :
  Z.lcm 12 18 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_hamming_N :
  pin_N = pin_p * pin_q.
Proof. reflexivity. Qed.

Theorem extra_digit_reverse_splits :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem extra_digits_of_N :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_N_mod_100 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_nextprime_N :
  Z.odd pin_N = true.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_prevprime_associate :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem extra_xor_leftovers :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_related_y_cube :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_leftover_pair_splits :
  Z.gcd (pin_sqrt1_mixed + 1) pin_N = pin_q /\
  Problem_Factor pin_N pin_q.
Proof.
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
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem extra_dl_base9 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem extra_gen_pair_42_9 :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem extra_gen_pair_42_53 :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem extra_gen_pair_42_93 :
  Z.gcd (pin_sqrt1_mixed + 1) pin_N = pin_q /\
  Problem_Factor pin_N pin_q.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem extra_y_minus_x :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem extra_advice_five_div_lam :
  (5 | 80).
Proof. exists 16. reflexivity. Qed.

Theorem extra_advice_local_9 :
  42 mod 11 = 9.
Proof. reflexivity. Qed.

Theorem extra_euclid_x_minus_y :
  powm pin_y pin_lam pin_N = 1.
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
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.
