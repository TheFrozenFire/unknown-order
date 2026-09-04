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
  Z.gcd (pin187_sqrt1_mixed + 1) pin187_N = pin187_q.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_associate :
  powm (pin187_N - pin187_x) pin187_e pin187_N = 151 /\
  151 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_midpoint :
  0 < pin_N / 2 < pin_N.
Proof.
  pose proof pin_N_gt_1.
  split.
  - apply Z.div_str_pos; lia.
  - apply Z.div_lt; lia.
Qed.

Theorem xmap_encrypt_as_decrypt :
  powm pin187_y pin187_e pin187_N = 93 /\
  93 <> pin187_x.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_not_coppersmith_small :
  pin_x >= 2 /\
  ~ (pin_x ^ 2 < 0).
Proof. split; [lia|]. intros Hle. lia. Qed.

Theorem xmap_odd_monomial_y5 :
  powm pin187_y 5 pin187_N = 100 /\
  powm 100 pin187_e pin187_N = 111 /\
  111 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_y_to_the_y :
  powm pin187_y pin187_y pin187_N = 135 /\
  135 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_y_to_the_N :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem xmap_y_to_Nminus1 :
  powm pin187_y (pin187_N - 1) pin187_N = 157 /\
  157 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_y_to_Nplus1 :
  powm pin187_y (pin187_N + 1) pin187_N = 16 /\
  16 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_floor_sqrt_y :
  Z.sqrt 36 = 6 /\
  6 * 6 = 36.
Proof. split; reflexivity. Qed.

Theorem xmap_half_y :
  pin187_y / 2 = 18 /\
  powm 18 pin187_e pin187_N = 35 /\
  35 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_bitrev_36_is_9 :
  Z.gcd (pin187_sqrt1_mixed - 1) pin187_N = pin187_p.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_triangular :
  (pin187_y * 35 / 2) mod pin187_N = 69 /\
  powm 69 5 pin187_N = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem xmap_nextprime_as_x :
  powm 37 pin187_e pin187_N = 163 /\
  163 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_fibonacci_y :
  Z.gcd (pin187_sqrt1_mixed + 1) pin187_N = pin187_q.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_exp_base2 :
  Z.gcd (pin187_sqrt1_mixed - 1) pin187_N = pin187_p.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_exp_base3 :
  powm pin187_g pin187_y pin187_N = 47 /\
  47 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_phi3_of_y :
  (pin187_y * pin187_y + pin187_y + 1) mod pin187_N = 24 /\
  24 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_inv_then_cube :
  Z.gcd (pin187_sqrt1_mixed - 1) pin187_N = pin187_p.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_cube_then_inv :
  Z.gcd (pin187_sqrt1_mixed - 1) pin187_N = pin187_p.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_hybrid_crt :
  crt2 pin187_p pin187_q 1 pin187_y = 155 /\
  Z.gcd 155 pin187_N = 1 /\
  powm 155 pin187_e pin187_N = 144 /\
  144 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_mismatched_crt_splits :
  Z.gcd (pin187_sqrt1_mixed - 1) pin187_N = pin187_p /\
  Problem_Factor pin187_N pin187_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin187_q. reflexivity.
Qed.

Theorem xmap_integer_jnt :
  36 + 28 = 64 /\
  4 * 4 * 4 = 64.
Proof. split; reflexivity. Qed.

Theorem xmap_y2_plus_1 :
  (pin187_y * pin187_y + 1) mod pin187_N = 175 /\
  175 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_x_eq_Nminus1 :
  powm (-1) pin187_e pin187_N = (pin187_N - 1) /\
  (pin187_N - 1) <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_floor_sqrt_N :
  0 < pin187_N.
Proof. lia. Qed.

Theorem xmap_phi3_of_N :
  Z.gcd (pin187_N * pin187_N + pin187_N + 1) pin187_lam = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y7_onesided :
  Z.gcd (pin187_sqrt1_mixed - 1) pin187_N = pin187_p.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y9_cubes_to_root :
  powm pin187_y 9 pin187_N = 70 /\
  powm 70 pin187_e pin187_N = pin187_x /\
  pin187_x <> pin187_y /\
  Z.gcd (pin187_x - pin187_y) pin187_N = 1.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem xmap_y11_onesided :
  Z.gcd (pin187_sqrt1_mixed + 1) pin187_N = pin187_q.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_floor_y_div_3 :
  pin187_y / 3 = 12 /\
  powm 12 pin187_e pin187_N = 45 /\
  45 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_floor_N_div_y :
  pin187_N / pin187_y = 5 /\
  powm 5 pin187_e pin187_N = 125 /\
  125 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_three_y_onesided :
  Z.gcd (pin187_sqrt1_mixed - 1) pin187_N = pin187_p.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y_minus_1 :
  powm 35 pin187_e pin187_N = 52 /\
  52 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_y_plus_1_as_x :
  pin187_y + 1 = 37 /\
  powm 37 pin187_e pin187_N = 163 /\
  163 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_two_y_plus_1 :
  2 * pin187_y + 1 = 73 /\
  powm 73 pin187_e pin187_N = 57 /\
  57 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_y2_minus_1 :
  (pin187_y * pin187_y - 1) mod pin187_N = 173 /\
  powm 173 pin187_e pin187_N = 61 /\
  61 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_gray_code :
  Z.lxor pin187_y 18 = 54 /\
  powm 54 pin187_e pin187_N = 10 /\
  10 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_nibble_swap_nonunit :
  Z.gcd (pin187_sqrt1_mixed - 1) pin187_N = pin187_p /\
  Problem_Factor pin187_N pin187_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin187_q. reflexivity.
Qed.

Theorem xmap_popcount_as_x :
  pin187_y = 2 ^ 5 + 2 ^ 2 /\
  powm 2 pin187_e pin187_N = 8 /\
  8 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_catalan_C5 :
  252 / 6 = 42 /\
  powm pin187_x pin187_e pin187_N = pin187_y /\
  srsa_residual_leaf pin187_N pin187_lam pin187_y pin187_x pin187_e.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin187.
Qed.

Theorem xmap_lucas_L8 :
  powm 47 pin187_e pin187_N = 38 /\
  38 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_floor_y_three_halves :
  216 mod pin187_N = 29 /\
  powm 29 pin187_e pin187_N = 79 /\
  79 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_shift_left_2_onesided :
  Z.gcd (pin187_sqrt1_mixed + 1) pin187_N = pin187_q.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y_mod_16 :
  pin187_y mod 16 = 4 /\
  powm 4 pin187_e pin187_N = 64 /\
  64 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_eightbit_palindrome :
  powm pin187_y pin187_e pin187_N = 93 /\
  93 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_partition_p10 :
  powm pin187_x pin187_e pin187_N = pin187_y /\
  srsa_residual_leaf pin187_N pin187_lam pin187_y pin187_x pin187_e.
Proof.
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin187.
Qed.

Theorem xmap_catalan_C6_nonunit :
  Z.gcd (pin187_sqrt1_mixed - 1) pin187_N = pin187_p /\
  Problem_Factor pin187_N pin187_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin187_q. reflexivity.
Qed.

Theorem xmap_y_inv_sq :
  powm 26 2 pin187_N = 115 /\
  powm 115 pin187_e pin187_N = 4 /\
  4 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_x_eq_phi :
  powm pin187_phi pin187_e pin187_N = 139 /\
  139 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_x_bitlength_N :
  powm 8 pin187_e pin187_N = 138 /\
  138 <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_nextprime_mod_N :
  191 mod pin187_N = 4 /\
  powm 4 pin187_e pin187_N = 64 /\
  64 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_identity_not_root :
  powm 1 pin_e pin_N = 1 /\
  1 <> pin_y.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem xmap_y35_onesided :
  Z.gcd (pin187_sqrt1_mixed + 1) pin187_N = pin187_q /\
  Problem_Factor pin187_N pin187_q.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin187_p. reflexivity.
Qed.

Theorem xmap_inv_lam_minus_1 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem xmap_pkcs_pad :
  (256 + pin187_y) mod pin187_N = 105 /\
  powm 105 pin187_e pin187_N = 95 /\
  95 <> pin187_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_sqrt_then_n_nplus1 :
  6 * 6 = 36 /\
  6 * 7 = 42 /\
  powm pin187_x pin187_e pin187_N = pin187_y /\
  srsa_residual_leaf pin187_N pin187_lam pin187_y pin187_x pin187_e.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin187.
Qed.

Theorem xmap_integer_sqrt_unit :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem xmap_binary_encrypt :
  powm pin187_y 2 pin187_N = 174 /\
  powm pin187_y pin187_e pin187_N = 93 /\
  93 <> pin187_x.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_mont_form :
  (pin187_y * 256) mod pin187_N = 53.
Proof. vm_compute. reflexivity. Qed.
