From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import Zmod.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import TwoPrimary.

Open Scope Z_scope.

(** * Public maps of leftover [x]

    Restrictions on the TM that writes [X(N,y)].  Fate is inhabit /
    one-sided split / leftover by pin accident.  None of these is a
    general residual solver. *)

Fixpoint xmap_fib_iter (n : nat) (a b : Z) : Z :=
  match n with
  | O => a
  | S n' => xmap_fib_iter n' b (a + b)
  end.

Theorem xmap_odd_monomial :
  Z.gcd (pin_sqrt1_mixed + 1) pin_N = pin_q.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_associate :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_midpoint :
  0 < pin_N / 2 < pin_N.
Proof.
  pose proof pin_N_gt_1.
  split.
  - apply Z.div_str_pos; lia.
  - apply Z.div_lt; lia.
Qed.

Theorem xmap_encrypt_as_decrypt :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_not_coppersmith_small :
  pin_x >= 2 /\
  ~ (pin_x ^ 2 < 0).
Proof. split; [lia|]. intros Hle. lia. Qed.

Theorem xmap_odd_monomial_y5 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y_to_the_y :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y_to_the_N :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem xmap_y_to_Nminus1 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y_to_Nplus1 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_floor_sqrt_y :
  Z.sqrt 36 = 6 /\
  6 * 6 = 36.
Proof. split; reflexivity. Qed.

Theorem xmap_half_y :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_bitrev_36_is_9 :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_triangular :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_nextprime_as_x :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_fibonacci_y :
  Z.gcd (pin_sqrt1_mixed + 1) pin_N = pin_q.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_exp_base2 :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_exp_base3 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_phi3_of_y :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_inv_then_cube :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_cube_then_inv :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_hybrid_crt :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_mismatched_crt_splits :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem xmap_integer_jnt :
  36 + 28 = 64 /\
  4 * 4 * 4 = 64.
Proof. split; reflexivity. Qed.

Theorem xmap_y2_plus_1 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_x_eq_Nminus1 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_floor_sqrt_N :
  0 < pin_N.
Proof. lia. Qed.

Theorem xmap_phi3_of_N :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y7_onesided :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y9_cubes_to_root :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y11_onesided :
  Z.gcd (pin_sqrt1_mixed + 1) pin_N = pin_q.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_floor_y_div_3 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_floor_N_div_y :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_three_y_onesided :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y_minus_1 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y_plus_1_as_x :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_two_y_plus_1 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y2_minus_1 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_gray_code :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_nibble_swap_nonunit :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem xmap_popcount_as_x :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_catalan_C5 :
  252 / 6 = 42 /\
  powm pin_x pin_e pin_N = pin_y /\
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem xmap_lucas_L8 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_floor_y_three_halves :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_shift_left_2_onesided :
  Z.gcd (pin_sqrt1_mixed + 1) pin_N = pin_q.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y_mod_16 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_eightbit_palindrome :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_partition_p10 :
  powm pin_x pin_e pin_N = pin_y /\
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof.
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem xmap_catalan_C6_nonunit :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem xmap_y_inv_sq :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_x_eq_phi :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_x_bitlength_N :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_nextprime_mod_N :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_identity_not_root :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y35_onesided :
  Z.gcd (pin_sqrt1_mixed + 1) pin_N = pin_q /\
  Problem_Factor pin_N pin_q.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem xmap_inv_lam_minus_1 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem xmap_pkcs_pad :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_sqrt_then_n_nplus1 :
  6 * 6 = 36 /\
  6 * 7 = 42 /\
  powm pin_x pin_e pin_N = pin_y /\
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem xmap_integer_sqrt_unit :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem xmap_binary_encrypt :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_mont_form :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.
