From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes U (341–360)

    Binary expansion / addition chain of [k=27], then the gcd-path vs
    exp-path dichotomy and SAGM on the challenge.
    Cross-confirmed by [cas/137]. *)

Theorem hun_341_bits_of_27 :
  16 + 8 + 2 + 1 = 27.
Proof. reflexivity. Qed.

Theorem hun_342_binary_product :
  powm 36 16 187 = 69 /\
  powm 36 8 187 = 137 /\
  powm 36 2 187 = 174 /\
  (69 * 137 * 174 * 36) mod 187 = 42.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem hun_343_add_chain_y6 :
  powm 36 6 187 = 47.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_344_add_chain_y12 :
  powm 36 12 187 = 152.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_345_add_chain_y24 :
  powm 36 24 187 = 103.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_346_k_odd :
  Z.odd 27 = true.
Proof. reflexivity. Qed.

Theorem hun_347_hamming_27 :
  27 = 2 ^ 0 + 2 ^ 1 + 2 ^ 3 + 2 ^ 4.
Proof. reflexivity. Qed.

Theorem hun_348_naf_shape :
  32 - 4 - 1 = 27 /\
  powm 36 32 187 = 86 /\
  powm 36 4 187 = 169.
Proof. split; [reflexivity|]. vm_compute. split; reflexivity. Qed.

Theorem hun_349_y25 :
  powm 36 25 187 = 155.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_350_y16_is_g5sq :
  powm 36 16 187 = 69 /\
  powm 137 2 187 = 69.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_351_gcd_path_splits :
  Z.gcd (powm 36 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_352_exp_path_leftover :
  powm 36 27 187 = 42 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem hun_353_eq_order_40 :
  powm 36 40 187 = 1 /\
  powm 36 20 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_354_eq_not_8 :
  powm 36 8 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem hun_355_eq_not_5 :
  powm 36 5 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem hun_356_sagm_on_y :
  27 * 3 - 1 = 80.
Proof. reflexivity. Qed.

Theorem hun_357_y81 :
  powm 36 81 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_358_ae_lambda_plus_1 :
  27 * 3 = 80 + 1.
Proof. reflexivity. Qed.

Theorem hun_359_e43_same_x :
  powm 42 43 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_360_e83_same_x :
  powm 42 83 187 = 36.
Proof. vm_compute. reflexivity. Qed.
