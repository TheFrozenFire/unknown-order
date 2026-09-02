From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes L (161–180)

    Related queries, leftover exponents, bit advice.  Cross-confirmed
    by [cas/135]. *)

Theorem hun_161_xor_leftovers :
  Z.lxor 42 60 = 22 /\
  powm 22 3 187 = 176 /\
  176 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_162_related_y_cube :
  powm 36 3 187 = 93 /\
  93 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_163_e43_same_x :
  Z.gcd 43 80 = 1 /\
  powm 42 43 187 = 36 /\
  srsa_residual_leaf 187 80 36 42 43.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 21; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_164_e47_second_leftover :
  Z.gcd 47 80 = 1 /\
  powm 60 47 187 = 36 /\
  srsa_residual_leaf 187 80 36 60 47.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 23; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_165_e23_ninth :
  Z.gcd 23 80 = 1 /\
  powm 9 23 187 = 36 /\
  srsa_residual_leaf 187 80 36 9 23.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 11; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_166_e19_leftover :
  Z.gcd 19 80 = 1 /\
  powm 59 19 187 = 36 /\
  srsa_residual_leaf 187 80 36 59 19.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 9; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_167_e_eq_x :
  Z.gcd 59 80 = 1 /\
  powm 59 59 187 = 36 /\
  srsa_residual_leaf 187 80 36 59 59.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 29; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_168_F9_splits :
  Z.gcd 34 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_169_F10_splits :
  Z.gcd 55 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_170_mersenne_255 :
  2 ^ 8 - 1 = 255 /\
  Z.gcd 255 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_171_catalan_C6_nonunit :
  924 / 7 = 132 /\
  Z.gcd 132 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_172_y_inv_sq :
  powm 26 2 187 = 115 /\
  powm 115 3 187 = 4 /\
  4 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_173_y_to_lam_identity :
  powm 36 80 187 = 1 /\
  1 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_174_x_eq_phi :
  powm 160 3 187 = 139 /\
  139 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_175_x_bitlength_N :
  powm 8 3 187 = 138 /\
  138 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_176_leftover_pair_splits :
  Z.gcd (42 - 25) 187 = 17 /\
  Z.gcd (42 - 60) 187 = 1 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_177_e_N_minus_lam :
  Z.gcd 107 80 = 1 /\
  powm 93 107 187 = 36 /\
  srsa_residual_leaf 187 80 36 93 107.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 53; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_178_first_nibble :
  36 mod 16 = 4.
Proof. reflexivity. Qed.

Theorem hun_179_two_bit_advice :
  36 mod 4 = 0.
Proof. reflexivity. Qed.

Theorem hun_180_nextprime_mod_N :
  191 mod 187 = 4 /\
  powm 4 3 187 = 64 /\
  64 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.
