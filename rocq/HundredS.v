From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import ArithShape.

Open Scope Z_scope.

(** * Hundred classes S (301–320)

    Residual dictionary: each generator of [⟨y⟩] is leftover [x] for
    two exponents [e, e+40].  Cubing is an automorphism of [⟨y⟩].
    Cross-confirmed by [cas/137]. *)

Theorem hun_301_x93_e67 :
  powm 93 67 187 = 36 /\
  srsa_residual_leaf 187 80 36 93 67.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 33; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_302_x25_e11 :
  powm 25 11 187 = 36 /\
  srsa_residual_leaf 187 80 36 25 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 5; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_303_x25_e51 :
  powm 25 51 187 = 36 /\
  srsa_residual_leaf 187 80 36 25 51.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 25; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_304_x15_e29 :
  powm 15 29 187 = 36 /\
  srsa_residual_leaf 187 80 36 15 29.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 14; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_305_x15_e69 :
  powm 15 69 187 = 36 /\
  srsa_residual_leaf 187 80 36 15 69.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 34; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_306_x168_e61 :
  powm 168 61 187 = 36 /\
  srsa_residual_leaf 187 80 36 168 61.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 30; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_307_x104_e57 :
  powm 104 57 187 = 36 /\
  srsa_residual_leaf 187 80 36 104 57.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 28; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_308_x185_e53 :
  powm 185 53 187 = 36 /\
  srsa_residual_leaf 187 80 36 185 53.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 26; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_309_xy_e41 :
  powm 36 41 187 = 36 /\
  srsa_residual_leaf 187 80 36 36 41.
Proof.
  split; [vm_compute; reflexivity|].
  apply arith_xy_period_residual.
Qed.

Theorem hun_310_y_lambda_type :
  powm 36 81 187 = 36 /\
  (80 | 81 - 1).
Proof. split; [vm_compute; reflexivity|]. exists 1. reflexivity. Qed.

Theorem hun_311_e_plus_80 :
  powm 42 83 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_312_phi80 :
  80 / 2 * 4 / 5 = 32.
Proof. reflexivity. Qed.

Theorem hun_313_phi40 :
  40 / 2 * 4 / 5 = 16.
Proof. reflexivity. Qed.

Theorem hun_314_two_e_per_x :
  32 / 16 = 2.
Proof. reflexivity. Qed.

Theorem hun_315_e_mod_40 :
  powm 42 3 187 = 36 /\
  powm 42 43 187 = 36.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_316_kernel_1_41 :
  1 mod 40 = 1 /\
  41 mod 40 = 1 /\
  Z.gcd 41 80 = 1.
Proof. repeat split; reflexivity. Qed.

Theorem hun_317_cube_bij_on_cyc :
  Z.gcd 3 40 = 1.
Proof. reflexivity. Qed.

Theorem hun_318_27th_is_inverse_auto :
  Z.gcd 27 40 = 1 /\
  (3 * 27) mod 40 = 1.
Proof. split; reflexivity. Qed.

Theorem hun_319_compose_autos :
  powm 36 27 187 = 42 /\
  powm 42 3 187 = 36.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_320_ae_is_lambda_plus_1 :
  27 * 3 = 80 + 1.
Proof. reflexivity. Qed.
