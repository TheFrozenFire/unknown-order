From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import FilterShape.

Open Scope Z_scope.

(** * Hundred classes J (121–140)

    Further [e = f(y)] / [e = f(N)] maps.  Cross-confirmed by [cas/135]. *)

Theorem hun_121_e_y_minus_1_shares :
  Z.gcd 35 80 = 5 /\
  Z.gcd 35 80 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem hun_122_e_two_y_plus_1 :
  Z.gcd 73 80 = 1 /\
  powm 53 73 187 = 36 /\
  srsa_residual_leaf 187 80 36 53 73.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 36; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_123_e_two_y_minus_1 :
  Z.gcd 71 80 = 1 /\
  powm 179 71 187 = 36 /\
  srsa_residual_leaf 187 80 36 179 71.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 35; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_124_prevprime_e31 :
  Z.gcd 31 80 = 1 /\
  powm 179 31 187 = 36 /\
  srsa_residual_leaf 187 80 36 179 31.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 15; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_125_dedekind_psi_even :
  36 * 3 / 2 * 4 / 3 = 72 /\
  Z.even 72 = true.
Proof. split; reflexivity. Qed.

Theorem hun_126_ord_y_even :
  powm 36 40 187 = 1 /\
  Z.even 40 = true.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem hun_127_phi_N_even :
  Z.even 160 = true.
Proof. reflexivity. Qed.

Theorem hun_128_e_eq_d :
  Z.gcd 27 80 = 1 /\
  powm 93 27 187 = 36 /\
  srsa_residual_leaf 187 80 36 93 27.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 13; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_129_aliquot_shares :
  91 - 36 = 55 /\
  Z.gcd 55 80 = 5.
Proof. split; reflexivity. Qed.

Theorem hun_130_e17_leftover :
  Z.gcd 17 80 = 1 /\
  powm 104 17 187 = 36 /\
  srsa_residual_leaf 187 80 36 104 17.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 8; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_131_e_N_plus_1_even :
  Z.even (187 + 1) = true.
Proof. reflexivity. Qed.

Theorem hun_132_e_N_minus_1_even :
  Z.even (187 - 1) = true.
Proof. reflexivity. Qed.

Theorem hun_133_e_lam_minus_1 :
  Z.gcd 79 80 = 1 /\
  powm 26 79 187 = 36 /\
  srsa_residual_leaf 187 80 36 26 79.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 39; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_134_phi_y_plus_1 :
  Z.gcd 13 80 = 1 /\
  powm 185 13 187 = 36 /\
  srsa_residual_leaf 187 80 36 185 13.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 6; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_135_digit_sum_e9 :
  3 + 6 = 9 /\
  Z.gcd 9 80 = 1 /\
  srsa_residual_leaf 187 80 36 (powm 36 9 187) 9.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  apply filter_lowbit_e9_residual.
Qed.

Theorem hun_136_repunit_111 :
  Z.gcd 111 80 = 1 /\
  powm 179 111 187 = 36 /\
  srsa_residual_leaf 187 80 36 179 111.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 55; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_137_primorial_even :
  2 * 3 * 5 * 7 = 210 /\
  Z.even 210 = true.
Proof. split; reflexivity. Qed.

Theorem hun_138_fermat_5_shares :
  Z.gcd 5 80 = 5 /\
  Z.gcd 5 80 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem hun_139_collatz_e21 :
  Z.gcd 21 80 = 1 /\
  powm 168 21 187 = 36 /\
  srsa_residual_leaf 187 80 36 168 21.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 10; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_140_squarefree_core_e9 :
  36 / 4 = 9 /\
  Z.gcd 9 80 = 1.
Proof. split; reflexivity. Qed.
