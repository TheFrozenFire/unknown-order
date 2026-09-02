From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes W (381–400)

    After equality-only order-finding, [x=y^{27}] leftover-inhabits.
    Residual cube is SAGM [(a,e)=(27,3)] on the challenge.  Missing
    [C₂] in [⟨y⟩] vs [λ].  Cross-confirmed by [cas/137]. *)

Theorem hun_381_after_ord_invert :
  powm 36 27 187 = 42 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem hun_382_sagm_ae_minus_1 :
  27 * 3 - 1 = 80.
Proof. reflexivity. Qed.

Theorem hun_383_inv_mod_40 :
  (3 * 27) mod 40 = 1.
Proof. reflexivity. Qed.

Theorem hun_384_inv_mod_lam :
  (3 * 27) mod 80 = 1.
Proof. reflexivity. Qed.

Theorem hun_385_x_generates :
  powm 42 40 187 = 1 /\
  powm 42 20 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_386_C8_order :
  powm 100 8 187 = 1 /\
  powm 100 4 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_387_C5_order :
  powm 137 5 187 = 1 /\
  powm 137 1 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_388_lcm_primaries :
  Z.lcm 8 5 = 40.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_389_coprime_primaries :
  Z.gcd 8 5 = 1.
Proof. reflexivity. Qed.

Theorem hun_390_v2_ord_p :
  Z.even 5 = false.
Proof. reflexivity. Qed.

Theorem hun_391_v2_ord_q :
  8 = 2 ^ 3.
Proof. reflexivity. Qed.

Theorem hun_392_v2_ord_N :
  40 = 8 * 5 /\
  8 = 2 ^ 3.
Proof. split; reflexivity. Qed.

Theorem hun_393_v2_lam_bigger :
  80 = 16 * 5 /\
  16 = 2 ^ 4.
Proof. split; reflexivity. Qed.

Theorem hun_394_three_not_in_cyc_y :
  powm 3 40 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem hun_395_three_full_lambda :
  powm 3 80 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_396_y_even_power_of_3 :
  Z.even 46 = true.
Proof. reflexivity. Qed.

Theorem hun_397_product_primaries :
  (155 * 69) mod 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_398_cube_of_x :
  powm 42 3 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_399_y_to_27 :
  powm 36 27 187 = 42.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_400_cube_bij_primaries :
  Z.gcd 3 8 = 1 /\
  Z.gcd 3 5 = 1.
Proof. split; reflexivity. Qed.
