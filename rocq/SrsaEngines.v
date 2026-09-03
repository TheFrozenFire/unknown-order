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
  Z.gcd (powm 2 (pin_p - 1) pin_N - 1) pin_N = pin_p /\
  (pin_ord2_p | pin_p - 1) /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  split; [apply Z.mod_divide; [lia | vm_compute; reflexivity]|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_rho_walk :
  Problem_Factor pin_N pin_p.
Proof.
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_bsgs_wrong_order :
  lambda_semiprime pin_p pin_q = pin_lam /\
  pin_lam <> pin_N - 1.
Proof. split; [vm_compute; reflexivity | discriminate]. Qed.

Theorem engine_fermat_splits :
  let a := (pin_p + pin_q) / 2 in
  let b := (pin_q - pin_p) / 2 in
  a - b = pin_p /\
  a + b = pin_q /\
  a * a - b * b = pin_N /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_trial_division :
  (pin_p | pin_N) /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [exists pin_q; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_williams_pplus1 :
  (Z.gcd (lucasV 5 1 (Z.to_nat (pin_p + 1)) - 2) pin_N | pin_N) /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [apply Z.gcd_divide_r|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_index_calculus_Nminus1 :
  Z.gcd (powm 2 (pin_N - 1) pin_N - 1) pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem engine_F9_splits :
  Z.gcd (2 * pin_q) pin_N = pin_q /\
  Problem_Factor pin_N pin_q.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem engine_F10_splits :
  Z.gcd (5 * pin_p) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_mersenne_255 :
  Z.gcd (powm 2 pin_ord2_q pin_N - 1) pin_N = pin_q /\
  Problem_Factor pin_N pin_q.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem engine_pminus1_B8 :
  Z.gcd (powm 2 pin_lam pin_N - 1) pin_N = pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem engine_rho_x2_minus_1 :
  Problem_Factor pin_N pin_p.
Proof.
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_williams_P3_no_split :
  Z.gcd (lucasV 5 1 3%nat - 2) pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem engine_factorial_trial :
  Z.gcd 3628800 pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem engine_hart_square :
  let a := (pin_p + pin_q) / 2 in
  let b := (pin_q - pin_p) / 2 in
  a * a - pin_N = b * b.
Proof. vm_compute. reflexivity. Qed.

Theorem engine_fermat_recovers :
  let a := (pin_p + pin_q) / 2 in
  let b := (pin_q - pin_p) / 2 in
  a - b = pin_p /\
  a + b = pin_q /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_trial_13_then_11 :
  (pin_N mod 13 <> 0) /\
  (pin_p | pin_N) /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; discriminate|].
  split; [exists pin_q; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem engine_fibonacci_gcd_engine :
  Z.gcd (2 * pin_q) pin_N = pin_q /\
  Problem_Factor pin_N pin_q.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem engine_mersenne_engine :
  Z.gcd (powm 2 pin_ord2_q pin_N - 1) pin_N = pin_q /\
  Problem_Factor pin_N pin_q.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem engine_shor_period_of_2 :
  powm 2 pin_lam pin_N = 1 /\
  pin_lam <> pin_N - 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem engine_lam_ne_Nminus1 :
  pin_lam <> pin_N - 1.
Proof. discriminate. Qed.
