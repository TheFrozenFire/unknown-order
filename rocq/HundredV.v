From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes V (361–380)

    [e] and [e+40] name the same residual [x].  Equality-only order
    tests vs gcd-Pohlig.  Cross-confirmed by [cas/137]. *)

Theorem hun_361_e43_minus_3 :
  (43 - 3) mod 40 = 0.
Proof. reflexivity. Qed.

Theorem hun_362_e83_minus_3 :
  (83 - 3) mod 80 = 0.
Proof. reflexivity. Qed.

Theorem hun_363_e67_coprime :
  Z.gcd 67 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_364_e51_coprime :
  Z.gcd 51 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_365_e61_coprime :
  Z.gcd 61 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_366_e57_coprime :
  Z.gcd 57 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_367_e29_coprime :
  Z.gcd 29 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_368_e39_coprime :
  Z.gcd 39 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_369_x26_e39 :
  powm 26 39 187 = 36 /\
  srsa_residual_leaf 187 80 36 26 39.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 19; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem hun_370_self_inverse_11 :
  (11 * 11) mod 40 = 1.
Proof. reflexivity. Qed.

Theorem hun_371_ord_5_smooth :
  8 * 5 = 40.
Proof. reflexivity. Qed.

Theorem hun_372_ord_div_lam :
  (40 | 80).
Proof. exists 2. reflexivity. Qed.

Theorem hun_373_index_two :
  80 / 40 = 2.
Proof. reflexivity. Qed.

Theorem hun_374_eq_y40 :
  powm 36 40 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_375_eq_y20 :
  powm 36 20 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem hun_376_eq_y8 :
  powm 36 8 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem hun_377_eq_y5 :
  powm 36 5 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem hun_378_gcd_y5_splits :
  Z.gcd (powm 36 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_379_gcd_y8_splits :
  Z.gcd (powm 36 8 187 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_380_gcd_full_period :
  Z.gcd (powm 36 40 187 - 1) 187 = 187.
Proof. vm_compute. reflexivity. Qed.
