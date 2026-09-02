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
  powm 36 3 187 = 93 /\
  powm 93 3 187 = 70 /\
  70 <> 36 /\
  Z.gcd (70 - 36) 187 = 17.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem xmap_associate :
  powm (187 - 42) 3 187 = 151 /\
  151 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_midpoint :
  187 / 2 = 93 /\
  Z.abs (36 - 93) = 57 /\
  powm 57 3 187 = 63 /\
  63 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_encrypt_as_decrypt :
  powm 36 3 187 = 93 /\
  93 <> 42.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_not_coppersmith_small :
  2 ^ 9 > 187 /\
  42 >= 2 /\
  ~ (42 ^ 9 < 187).
Proof.
  change (2 ^ 9) with 512.
  split; [lia|].
  split; [lia|].
  intros Hle. vm_compute in Hle. discriminate.
Qed.

Theorem xmap_odd_monomial_y5 :
  powm 36 5 187 = 100 /\
  powm 100 3 187 = 111 /\
  111 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_y_to_the_y :
  powm 36 36 187 = 135 /\
  135 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_y_to_the_N :
  powm 36 187 187 = 42 /\
  187 mod 40 = 27 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [vm_compute; reflexivity|].
  split; [reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem xmap_y_to_Nminus1 :
  powm 36 (187 - 1) 187 = 157 /\
  157 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_y_to_Nplus1 :
  powm 36 (187 + 1) 187 = 16 /\
  16 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_floor_sqrt_y :
  Z.sqrt 36 = 6 /\
  6 * 6 = 36.
Proof. split; reflexivity. Qed.

Theorem xmap_half_y :
  36 / 2 = 18 /\
  powm 18 3 187 = 35 /\
  35 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_bitrev_36_is_9 :
  powm 9 3 187 = 168 /\
  168 <> 36 /\
  Z.gcd (168 - 36) 187 = 11 /\
  powm 53 3 187 = 25 /\
  25 <> 36.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem xmap_triangular :
  (36 * 35 / 2) mod 187 = 69 /\
  powm 69 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem xmap_nextprime_as_x :
  powm 37 3 187 = 163 /\
  163 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_fibonacci_y :
  xmap_fib_iter 36%nat 0 1 = 14930352 /\
  14930352 mod 187 = 85 /\
  Z.gcd 85 187 = 17 /\
  powm 85 3 187 = 17 /\
  17 <> 36.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem xmap_exp_base2 :
  powm 2 36 187 = 152 /\
  152 <> 36 /\
  powm 152 3 187 = 135 /\
  Z.gcd (135 - 36) 187 = 11.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem xmap_exp_base3 :
  powm 3 36 187 = 47 /\
  47 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_phi3_of_y :
  (36 * 36 + 36 + 1) mod 187 = 24 /\
  24 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_inv_then_cube :
  powm 26 3 187 = 185 /\
  185 <> 36 /\
  powm 185 3 187 = 179 /\
  Z.gcd (179 - 36) 187 = 11.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem xmap_cube_then_inv :
  (93 * 185) mod 187 = 1 /\
  185 <> 36 /\
  powm 185 3 187 = 179 /\
  Z.gcd (179 - 36) 187 = 11.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem xmap_hybrid_crt :
  crt2 11 17 1 36 = 155 /\
  Z.gcd 155 187 = 1 /\
  powm 155 3 187 = 144 /\
  144 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_mismatched_crt_splits :
  crt2 11 17 9 1 = 86 /\
  Z.gcd (powm 86 3 187 - 36) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem xmap_integer_jnt :
  36 + 28 = 64 /\
  4 * 4 * 4 = 64.
Proof. split; reflexivity. Qed.

Theorem xmap_y2_plus_1 :
  (36 * 36 + 1) mod 187 = 175 /\
  175 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_x_eq_Nminus1 :
  powm (-1) 3 187 = 186 /\
  186 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_floor_sqrt_N :
  Z.sqrt 187 = 13 /\
  powm 13 3 187 = 140 /\
  140 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_phi3_of_N :
  Z.gcd (187 * 187 + 187 + 1) 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem xmap_y7_onesided :
  powm 36 7 187 = 9 /\
  powm 9 3 187 = 168 /\
  168 <> 36 /\
  Z.gcd (168 - 36) 187 = 11.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem xmap_y9_cubes_to_root :
  powm 36 9 187 = 70 /\
  powm 70 3 187 = 42 /\
  42 <> 36 /\
  Z.gcd (42 - 36) 187 = 1.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem xmap_y11_onesided :
  powm 36 11 187 = 25 /\
  powm 25 3 187 = 104 /\
  104 <> 36 /\
  Z.gcd (104 - 36) 187 = 17.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem xmap_floor_y_div_3 :
  36 / 3 = 12 /\
  powm 12 3 187 = 45 /\
  45 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_floor_N_div_y :
  187 / 36 = 5 /\
  powm 5 3 187 = 125 /\
  125 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_three_y_onesided :
  3 * 36 = 108 /\
  powm 108 3 187 = 80 /\
  80 <> 36 /\
  Z.gcd (80 - 36) 187 = 11.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem xmap_y_minus_1 :
  powm 35 3 187 = 52 /\
  52 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_y_plus_1_as_x :
  36 + 1 = 37 /\
  powm 37 3 187 = 163 /\
  163 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_two_y_plus_1 :
  2 * 36 + 1 = 73 /\
  powm 73 3 187 = 57 /\
  57 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_y2_minus_1 :
  (36 * 36 - 1) mod 187 = 173 /\
  powm 173 3 187 = 61 /\
  61 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_gray_code :
  Z.lxor 36 18 = 54 /\
  powm 54 3 187 = 10 /\
  10 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_nibble_swap_nonunit :
  4 * 16 + 2 = 66 /\
  Z.gcd 66 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem xmap_popcount_as_x :
  36 = 2 ^ 5 + 2 ^ 2 /\
  powm 2 3 187 = 8 /\
  8 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_catalan_C5 :
  252 / 6 = 42 /\
  powm 42 3 187 = 36 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem xmap_lucas_L8 :
  powm 47 3 187 = 38 /\
  38 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_floor_y_three_halves :
  216 mod 187 = 29 /\
  powm 29 3 187 = 79 /\
  79 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_shift_left_2_onesided :
  (36 * 4) mod 187 = 144 /\
  powm 144 3 187 = 155 /\
  155 <> 36 /\
  Z.gcd (155 - 36) 187 = 17.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem xmap_y_mod_16 :
  36 mod 16 = 4 /\
  powm 4 3 187 = 64 /\
  64 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_eightbit_palindrome :
  powm 36 3 187 = 93 /\
  93 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_partition_p10 :
  powm 42 3 187 = 36 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem xmap_catalan_C6_nonunit :
  924 / 7 = 132 /\
  Z.gcd 132 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem xmap_y_inv_sq :
  powm 26 2 187 = 115 /\
  powm 115 3 187 = 4 /\
  4 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_x_eq_phi :
  powm 160 3 187 = 139 /\
  139 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_x_bitlength_N :
  powm 8 3 187 = 138 /\
  138 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem xmap_nextprime_mod_N :
  191 mod 187 = 4 /\
  powm 4 3 187 = 64 /\
  64 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_identity_not_root :
  powm 1 3 187 = 1 /\
  1 <> 36.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem xmap_y35_onesided :
  powm 36 35 187 = 144 /\
  powm 144 3 187 = 155 /\
  Z.gcd (155 - 36) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem xmap_inv_lam_minus_1 :
  powm 26 79 187 = 36 /\
  srsa_residual_leaf 187 80 36 26 79.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 39; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem xmap_pkcs_pad :
  (256 + 36) mod 187 = 105 /\
  powm 105 3 187 = 95 /\
  95 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_sqrt_then_n_nplus1 :
  6 * 6 = 36 /\
  6 * 7 = 42 /\
  powm 42 3 187 = 36 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem xmap_integer_sqrt_unit :
  Z.gcd 6 187 = 1 /\
  powm 6 2 187 = 36.
Proof. split; [vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

Theorem xmap_binary_encrypt :
  powm 36 2 187 = 174 /\
  powm 36 3 187 = 93 /\
  93 <> 42.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem xmap_mont_form :
  (36 * 256) mod 187 = 53.
Proof. vm_compute. reflexivity. Qed.
