From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes I (101–120)

    Further [x = f(y)] maps.  Cross-confirmed by [cas/135]. *)

Theorem hun_101_y7_onesided :
  powm 36 7 187 = 9 /\
  powm 9 3 187 = 168 /\
  168 <> 36 /\
  Z.gcd (168 - 36) 187 = 11.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem hun_102_y9_cubes_to_root :
  powm 36 9 187 = 70 /\
  powm 70 3 187 = 42 /\
  42 <> 36 /\
  Z.gcd (42 - 36) 187 = 1.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem hun_103_y11_onesided :
  powm 36 11 187 = 25 /\
  powm 25 3 187 = 104 /\
  104 <> 36 /\
  Z.gcd (104 - 36) 187 = 17.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem hun_104_floor_y_div_3 :
  36 / 3 = 12 /\
  powm 12 3 187 = 45 /\
  45 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_105_floor_N_div_y :
  187 / 36 = 5 /\
  powm 5 3 187 = 125 /\
  125 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_106_three_y_onesided :
  3 * 36 = 108 /\
  powm 108 3 187 = 80 /\
  80 <> 36 /\
  Z.gcd (80 - 36) 187 = 11.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem hun_107_y_minus_1 :
  powm 35 3 187 = 52 /\
  52 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_108_y_plus_1_as_x :
  36 + 1 = 37 /\
  powm 37 3 187 = 163 /\
  163 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_109_two_y_plus_1 :
  2 * 36 + 1 = 73 /\
  powm 73 3 187 = 57 /\
  57 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_110_y2_minus_1 :
  (36 * 36 - 1) mod 187 = 173 /\
  powm 173 3 187 = 61 /\
  61 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_111_gray_code :
  Z.lxor 36 18 = 54 /\
  powm 54 3 187 = 10 /\
  10 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_112_nibble_swap_nonunit :
  4 * 16 + 2 = 66 /\
  Z.gcd 66 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_113_popcount_as_x :
  36 = 2 ^ 5 + 2 ^ 2 /\
  powm 2 3 187 = 8 /\
  8 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_114_catalan_C5 :
  252 / 6 = 42 /\
  powm 42 3 187 = 36 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem hun_115_lucas_L8 :
  powm 47 3 187 = 38 /\
  38 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_116_floor_y_three_halves :
  216 mod 187 = 29 /\
  powm 29 3 187 = 79 /\
  79 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_117_shift_left_2_onesided :
  (36 * 4) mod 187 = 144 /\
  powm 144 3 187 = 155 /\
  155 <> 36 /\
  Z.gcd (155 - 36) 187 = 17.
Proof. vm_compute. repeat split; try discriminate; reflexivity. Qed.

Theorem hun_118_y_mod_16 :
  36 mod 16 = 4 /\
  powm 4 3 187 = 64 /\
  64 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_119_eightbit_palindrome :
  powm 36 3 187 = 93 /\
  93 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_120_partition_p10 :
  powm 42 3 187 = 36 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.
