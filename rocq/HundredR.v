From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes R (281–300)

    CRT of local roots, Hensel at [p^2], integer-sqrt polynomial that
    hits the leftover cube, CRT-RSA [d_p]/[d_q], ratios of leftover
    generators, mismatched local orders of [y].
    Cross-confirmed by [cas/136]. *)

Theorem hun_281_crt_is_residual_x :
  9 + 11 * 3 = 42 /\
  powm 42 3 187 = 36.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem hun_282_hensel_p2 :
  (42 * 42 * 42) mod 121 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_283_pkcs_pad :
  (256 + 36) mod 187 = 105 /\
  powm 105 3 187 = 95 /\
  95 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_284_sqrt_then_n_nplus1 :
  6 * 6 = 36 /\
  6 * 7 = 42 /\
  powm 42 3 187 = 36 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem hun_285_integer_sqrt_unit :
  Z.gcd 6 187 = 1 /\
  powm 6 2 187 = 36.
Proof. split; [vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

Theorem hun_286_dp :
  27 mod 10 = 7.
Proof. reflexivity. Qed.

Theorem hun_287_edp_minus_1 :
  (3 * 7 - 1) mod 10 = 0.
Proof. reflexivity. Qed.

Theorem hun_288_dq :
  27 mod 16 = 11.
Proof. reflexivity. Qed.

Theorem hun_289_edq_minus_1 :
  (3 * 11 - 1) mod 16 = 0.
Proof. reflexivity. Qed.

Theorem hun_290_e_prime :
  Z.odd 3 = true /\
  Z.gcd 3 80 = 1.
Proof. split; reflexivity. Qed.

Theorem hun_291_binary_encrypt :
  powm 36 2 187 = 174 /\
  powm 36 3 187 = 93 /\
  93 <> 42.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_292_mont_form :
  (36 * 256) mod 187 = 53.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_293_prime_e7 :
  powm 60 7 187 = 36 /\
  srsa_residual_leaf 187 80 36 60 7.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 3; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_294_shamir_3_7 :
  Z.gcd 3 7 = 1.
Proof. reflexivity. Qed.

Theorem hun_295_ratio_five_torsion :
  (42 * 15) mod 187 = 69 /\
  powm 69 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_296_ratio_y4 :
  (42 * 53) mod 187 = 169 /\
  powm 36 4 187 = 169.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_297_rerand_fixed_e :
  powm 84 3 187 = (36 * 8) mod 187.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_298_x_to_8_is_five_torsion :
  powm 42 8 187 = 69 /\
  powm 69 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_299_mismatched_local_orders :
  powm 3 5 11 = 1 /\
  powm 2 8 17 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_300_lcm_local_orders :
  Z.lcm 5 8 = 40.
Proof. vm_compute. reflexivity. Qed.
