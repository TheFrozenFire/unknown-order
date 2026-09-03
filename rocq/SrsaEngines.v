From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import Lucas.

Open Scope Z_scope.

(** * Named factoring engines as solvers

    Pollard [p−1], rho, Fermat / Hart, trial, Williams [p+1],
    Fibonacci gcd, Mersenne, BSGS treating [N] as prime.  They split
    this pin because [N] is tiny or [p−1] is smooth, not because they
    inverted [y]. *)

Theorem engine_pollard_p1 :
  Z.gcd (powm 2 60 pin_N - 1) pin_N = 11 /\
  (10 | 60) /\
  ~ (16 | 60) /\
  Problem_Factor pin_N 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [exists 6; reflexivity|].
  split; [intros [k Hk]; nia|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_rho_walk :
  2 * 2 + 1 = 5 /\
  5 * 5 + 1 = 26 /\
  (26 * 26 + 1) mod pin_N = 116 /\
  (116 * 116 + 1) mod pin_N = 180 /\
  Z.gcd (26 - 180) pin_N = 11 /\
  Problem_Factor pin_N 11.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_bsgs_wrong_order :
  lambda_semiprime pin_p pin_q = pin_lam /\
  pin_N - 1 = 186 /\
  80 <> 186.
Proof. split; [vm_compute; reflexivity|]. split; [reflexivity | discriminate]. Qed.

Theorem engine_fermat_splits :
  14 * 14 - pin_N = 9 /\
  3 * 3 = 9 /\
  14 - 3 = 11 /\
  14 + 3 = 17 /\
  Problem_Factor pin_N 11.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_trial_division :
  (11 | pin_N) /\
  Problem_Factor pin_N 11.
Proof.
  split; [exists pin_q; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_williams_pplus1 :
  Z.gcd (lucasV 5 1 12%nat - 2) pin_N = 11 /\
  Problem_Factor pin_N 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_index_calculus_Nminus1 :
  Z.gcd (powm 2 186 pin_N - 1) pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem engine_F9_splits :
  Z.gcd 34 pin_N = 17 /\
  Problem_Factor pin_N 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem engine_F10_splits :
  Z.gcd 55 pin_N = 11 /\
  Problem_Factor pin_N 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_mersenne_255 :
  2 ^ 8 - 1 = 255 /\
  Z.gcd 255 pin_N = 17 /\
  Problem_Factor pin_N 17.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem engine_pminus1_B8 :
  Z.gcd (powm 2 840 pin_N - 1) pin_N = pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem engine_rho_x2_minus_1 :
  2 * 2 - 1 = 3 /\
  3 * 3 - 1 = 8 /\
  Z.gcd (8 - 41) pin_N = 11 /\
  Problem_Factor pin_N 11.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_williams_P3_no_split :
  Z.gcd (103682 - 2) pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem engine_factorial_trial :
  Z.gcd 3628800 pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem engine_hart_square :
  14 * 14 - pin_N = 9 /\
  3 * 3 = 9.
Proof. split; reflexivity. Qed.

Theorem engine_fermat_recovers :
  14 - 3 = 11 /\
  14 + 3 = 17 /\
  Problem_Factor pin_N 11.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_trial_13_then_11 :
  (pin_N mod 13 <> 0) /\
  (11 | pin_N) /\
  Problem_Factor pin_N 11.
Proof.
  split; [vm_compute; discriminate|].
  split; [exists pin_q; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_fibonacci_gcd_engine :
  Z.gcd 34 pin_N = 17 /\
  Problem_Factor pin_N 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem engine_mersenne_engine :
  Z.gcd (2 ^ 8 - 1) pin_N = 17 /\
  Problem_Factor pin_N 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem engine_shor_period_of_2 :
  powm 2 40 pin_N = 1 /\
  40 <> 80.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem engine_lam_ne_Nminus1 :
  80 <> 186.
Proof. discriminate. Qed.
