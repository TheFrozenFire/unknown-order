From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import FilterShape.
Require Import ArithShape.

Open Scope Z_scope.

(** * Hundred classes C (33–50)

    Further [e = f(y)] arithmetic functions.  Cross-confirmed by
    [cas/133]. *)

Theorem hun_33_lambda_y_even :
  Z.lcm 2 6 = 6 /\
  Z.even 6 = true.
Proof. split; reflexivity. Qed.

Theorem hun_34_bitlength_even :
  1 + 5 = 6 /\
  Z.even 6 = true.
Proof. split; reflexivity. Qed.

Theorem hun_35_tau_leftover_e9 :
  Z.gcd 9 80 = 1 /\
  srsa_residual_leaf 187 80 36 (powm 36 9 187) 9.
Proof. split; [reflexivity|]. apply filter_lowbit_e9_residual. Qed.

Theorem hun_36_sigma_leftover :
  Z.gcd 91 80 = 1 /\
  powm 25 91 187 = 36 /\
  srsa_residual_leaf 187 80 36 25 91.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 45; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_37_rad_even :
  2 * 3 = 6 /\
  Z.even 6 = true.
Proof. split; reflexivity. Qed.

Theorem hun_38_omega_even :
  Z.even 2 = true.
Proof. reflexivity. Qed.

Theorem hun_39_Omega_even :
  Z.even 4 = true.
Proof. reflexivity. Qed.

Theorem hun_40_lpf_hits_cube :
  srsa_residual_leaf 187 80 36 42 3.
Proof. apply srsa_residual_pin. Qed.

Theorem hun_41_y_plus_1_is_nextprime :
  36 + 1 = 37 /\
  36 < 37 /\
  Z.gcd 37 80 = 1.
Proof. split; [reflexivity|]. split; [lia | reflexivity]. Qed.

Theorem hun_42_odd_part_e9 :
  36 / 4 = 9 /\
  Z.gcd 9 80 = 1.
Proof. split; reflexivity. Qed.

Theorem hun_43_odd_hamming_shares :
  2 * 2 + 1 = 5 /\
  Z.gcd 5 80 = 5.
Proof. split; reflexivity. Qed.

Theorem hun_44_gcd_yminus1_Nminus1 :
  Z.gcd (36 - 1) (187 - 1) = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_45_phi3_y_leftover_shaped :
  Z.gcd 1333 80 = 1 /\
  Z.odd 1333 = true /\
  ~ (80 | 1332).
Proof.
  split; [vm_compute; reflexivity|].
  split; [reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_46_v2_yminus1 :
  35 mod 2 = 1 /\
  2 * 2 + 1 = 5 /\
  Z.gcd 5 80 = 5.
Proof. split; [reflexivity|]. split; reflexivity. Qed.

Theorem hun_47_mersenne_leftover :
  Z.gcd 63 80 = 1 /\
  powm 9 63 187 = 36 /\
  srsa_residual_leaf 187 80 36 9 63.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 31; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_48_N_mod_y_hits_e7 :
  187 mod 36 = 7 /\
  srsa_residual_leaf 187 80 36 60 7.
Proof. split; [reflexivity|]. apply arith_e7_residual. Qed.

Theorem hun_49_fermatish_leftover :
  2 ^ 5 + 1 = 33 /\
  Z.gcd 33 80 = 1 /\
  powm 53 33 187 = 36.
Proof. split; [reflexivity|]. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem hun_50_smooth_even :
  2 * 3 * 5 = 30 /\
  Z.even 30 = true.
Proof. split; reflexivity. Qed.
