From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes Y (421–440)

    Order-16 / order-4 units leak via [g^{ord/2}−1].  Leftover [x]
    has order 40, not 16.  Four square roots of 1.  Cross-confirmed
    by [cas/138]. *)

Theorem hun_421_ten_order_16 :
  powm 10 16 187 = 1 /\
  powm 10 8 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_422_ten_pow8_miller :
  powm 10 8 187 = 67.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_423_ten_pow8_splits :
  Z.gcd (powm 10 8 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_424_ten_pow16 :
  powm 10 16 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_425_x_not_in_lten :
  powm 10 1 187 <> 42 /\
  powm 10 8 187 <> 42.
Proof. vm_compute. split; discriminate. Qed.

Theorem hun_426_21_order_4 :
  powm 21 4 187 = 1 /\
  powm 21 2 187 = 67.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_427_21_sq_splits :
  Z.gcd (powm 21 2 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_428_89_order_4 :
  powm 36 10 187 = 89 /\
  powm 89 4 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_429_120_mixed :
  powm 120 2 187 = 1 /\
  Z.gcd (120 - 1) 187 = 17 /\
  Z.gcd (120 + 1) 187 = 11.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem hun_430_minus1_no_split :
  powm 186 2 187 = 1 /\
  Z.gcd (186 - 1) 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_431_pminus1_qminus1 :
  11 - 1 = 10 /\
  17 - 1 = 16.
Proof. split; reflexivity. Qed.

Theorem hun_432_lambda_lcm :
  Z.lcm 10 16 = 80.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_433_phi_product :
  10 * 16 = 160.
Proof. reflexivity. Qed.

Theorem hun_434_index_four :
  160 / 40 = 4.
Proof. reflexivity. Qed.

Theorem hun_435_x_order_40 :
  powm 42 40 187 = 1 /\
  powm 42 16 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_436_v2_ord_x :
  40 = 8 * 5 /\
  8 = 2 ^ 3.
Proof. split; reflexivity. Qed.

Theorem hun_437_v2_lam :
  80 = 16 * 5 /\
  16 = 2 ^ 4.
Proof. split; reflexivity. Qed.

Theorem hun_438_69_generates_C5 :
  powm 69 5 187 = 1 /\
  powm 69 1 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_439_111_generates_C8 :
  powm 111 8 187 = 1 /\
  powm 111 4 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_440_x_generates_5_sylow :
  powm 42 8 187 = 69 /\
  powm 69 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.
