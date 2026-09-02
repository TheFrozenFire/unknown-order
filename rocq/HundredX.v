From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes X (401–420)

    Leftover [x] is a Pohlig oracle.  Cubing the generators is four
    4-cycles.  Cross-confirmed by [cas/138]. *)

Theorem hun_401_x5_minus_1_splits :
  Z.gcd (powm 42 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_402_x8_minus_1_splits :
  Z.gcd (powm 42 8 187 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_403_x10_minus_1_splits :
  Z.gcd (powm 42 10 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_404_x16_minus_1_splits :
  Z.gcd (powm 42 16 187 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_405_x4_minus_1 :
  Z.gcd (powm 42 4 187 - 1) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_406_x2_minus_1 :
  Z.gcd (powm 42 2 187 - 1) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_407_x5_generates_C8 :
  powm 42 5 187 = 111 /\
  powm 111 8 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_408_x8_in_C5 :
  powm 42 8 187 = 69 /\
  powm 69 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_409_reconstruct_x :
  (powm 111 5 187 * powm 69 2 187) mod 187 = 42.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_410_same_oracle :
  Z.gcd (powm 36 5 187 - 1) 187 = 11 /\
  Z.gcd (powm 42 5 187 - 1) 187 = 11.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_411_cycle_70_cube :
  powm 70 3 187 = 42.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_412_cycle_42_cube :
  powm 42 3 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_413_cycle_36_cube :
  powm 36 3 187 = 93.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_414_cycle_93_cube :
  powm 93 3 187 = 70.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_415_three_order_4_mod_40 :
  (3 * 3 * 3 * 3) mod 40 = 1.
Proof. reflexivity. Qed.

Theorem hun_416_27_order_4_mod_40 :
  (27 * 27 * 27 * 27) mod 40 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_417_cycle2_9 :
  powm 9 3 187 = 168.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_418_cycle2_168 :
  powm 168 3 187 = 60.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_419_cycle2_15 :
  powm 15 3 187 = 9.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_420_jacobi_x_vs_2 :
  187 mod 8 = 3 /\
  42 mod 11 = 9 /\
  3 * 3 = 9.
Proof. repeat split; reflexivity. Qed.
