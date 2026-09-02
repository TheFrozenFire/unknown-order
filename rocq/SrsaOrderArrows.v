From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import Order.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Order / residual Strong RSA / Factor arrows

    Invert in [⟨y⟩] from [ord(y)] always (equality / multiply).
    A leftover pair factors [N] only under KeyGen mismatch
    ([one_sided_low_order]).  Matching local orders on [N=247] do
    not yield a proper factor.  None inhabits [srsa_residual_leaf]
    as [Problem_Factor] without mismatch.  Not RSA ≡ or ≢ factoring.
    Cross-confirmed by [cas/145]. *)

(** ** Order of the pin challenge *)

Theorem is_order_pin_y_40 :
  is_order 187 36 40.
Proof.
  unfold is_order. split; [lia|]. split.
  - vm_compute. reflexivity.
  - intros k' [Hk' Hk'lt] Hk'1.
    assert (
      k' = 1 \/ k' = 2 \/ k' = 3 \/ k' = 4 \/ k' = 5 \/
      k' = 6 \/ k' = 7 \/ k' = 8 \/ k' = 9 \/ k' = 10 \/
      k' = 11 \/ k' = 12 \/ k' = 13 \/ k' = 14 \/ k' = 15 \/
      k' = 16 \/ k' = 17 \/ k' = 18 \/ k' = 19 \/ k' = 20 \/
      k' = 21 \/ k' = 22 \/ k' = 23 \/ k' = 24 \/ k' = 25 \/
      k' = 26 \/ k' = 27 \/ k' = 28 \/ k' = 29 \/ k' = 30 \/
      k' = 31 \/ k' = 32 \/ k' = 33 \/ k' = 34 \/ k' = 35 \/
      k' = 36 \/ k' = 37 \/ k' = 38 \/ k' = 39) by lia.
    repeat (destruct H as [H | H]; [subst k'; vm_compute in Hk'1; discriminate|]).
    subst k'. vm_compute in Hk'1. discriminate.
Qed.

Theorem order_yields_residual_sRSA :
  forall N y k e d lam,
    1 < N ->
    0 <= y < N ->
    is_order N y k ->
    Z.coprime y N ->
    1 < e ->
    0 <= d ->
    (e * d) mod k = 1 ->
    Z.Odd e ->
    Z.gcd e lam = 1 ->
    ~ (lam | e - 1) ->
    srsa_residual_leaf N lam y (powm y d N) e.
Proof.
  intros N y k e d lam HN Hy Hord Hcop He Hd Hinv Hodd Hgcd Hndiv.
  unfold srsa_residual_leaf.
  split; [exact Hcop|].
  split; [apply (order_yields_strong_RSA N y k e d); assumption|].
  split; [exact Hodd|].
  split; [exact Hgcd | exact Hndiv].
Qed.

Theorem order_yields_residual_pin :
  srsa_residual_leaf 187 80 36 (powm 36 27 187) 3.
Proof.
  apply (order_yields_residual_sRSA 187 36 40 3 27 80).
  - lia.
  - lia.
  - apply is_order_pin_y_40.
  - vm_compute; reflexivity.
  - lia.
  - lia.
  - reflexivity.
  - exists 1; lia.
  - reflexivity.
  - intros [t Ht]. nia.
Qed.

Theorem order_invert_pin_is_cube_root :
  powm 36 27 187 = 42 /\
  powm 42 3 187 = 36.
Proof. vm_compute. split; reflexivity. Qed.

(** ** Mismatch ⇒ Factor; matching local orders do not *)

(** The residual leaf is unused: mismatch is the load-bearing
    hypothesis.  The leaf is in the type so the arrow is not
    [srsa_residual_leaf] as [Problem_Factor] on its own. *)
Theorem residual_mismatch_factors :
  forall p q y x e k lam,
    Z.prime p -> Z.prime q -> p <> q ->
    srsa_residual_leaf (p * q) lam y x e ->
    one_sided_low_order p q x k ->
    Problem_Factor (p * q) p.
Proof.
  intros p q y x e k lam Hp Hq Hneq _ Hone.
  apply leftover_mismatch_factors with (x := x) (k := k); assumption.
Qed.

Theorem leftover_x_one_sided_pin :
  one_sided_low_order 11 17 42 5.
Proof.
  unfold one_sided_low_order.
  split; [vm_compute; reflexivity|].
  split; [lia|].
  split; [vm_compute; reflexivity | vm_compute; discriminate].
Qed.

Theorem leftover_x_mismatch_factors_pin :
  Problem_Factor 187 11.
Proof.
  change 187 with (11 * 17).
  apply leftover_mismatch_factors with (x := 42) (k := 5);
    [apply prime_11 | apply prime_17 | discriminate | apply leftover_x_one_sided_pin].
Qed.

Theorem residual_mismatch_factors_pin :
  srsa_residual_leaf 187 80 36 42 3 ->
  one_sided_low_order 11 17 42 5 ->
  Problem_Factor 187 11.
Proof.
  intros _ Hone.
  change 187 with (11 * 17).
  apply leftover_mismatch_factors with (x := 42) (k := 5);
    [apply prime_11 | apply prime_17 | discriminate | exact Hone].
Qed.

Theorem leftover_y_one_sided_pin :
  one_sided_low_order 11 17 36 5.
Proof.
  unfold one_sided_low_order.
  split; [vm_compute; reflexivity|].
  split; [lia|].
  split; [vm_compute; reflexivity | vm_compute; discriminate].
Qed.

Theorem order_mismatch_factors_pin :
  Problem_Factor 187 11.
Proof.
  change 187 with (11 * 17).
  apply leftover_mismatch_factors with (x := 36) (k := 5);
    [apply prime_11 | apply prime_17 | discriminate | apply leftover_y_one_sided_pin].
Qed.

Theorem leftover_77_one_sided :
  one_sided_low_order 7 11 2 3.
Proof.
  unfold one_sided_low_order.
  split; [vm_compute; reflexivity|].
  split; [lia|].
  split; [vm_compute; reflexivity | vm_compute; discriminate].
Qed.

Theorem leftover_77_mismatch_factors :
  Problem_Factor 77 7.
Proof.
  change 77 with (7 * 11).
  apply leftover_mismatch_factors with (x := 2) (k := 3);
    [apply prime_7 | apply prime_11 | discriminate | apply leftover_77_one_sided].
Qed.

(** Matching local orders: the [k=5] that splits leftover [x] on
    [N=187] is not one-sided on [N=247], and the gcd is not a
    proper factor. *)

Theorem matching_247_not_one_sided :
  ~ one_sided_low_order 13 19 179 5.
Proof.
  unfold one_sided_low_order.
  intros [_ [_ [Hp Hq]]].
  vm_compute in Hp. discriminate.
Qed.

Theorem matching_247_gcd_not_proper :
  Z.gcd (powm 179 5 247 - 1) 247 = 1 /\
  ~ Problem_Factor 247 (Z.gcd (powm 179 5 247 - 1) 247).
Proof.
  assert (Hg : Z.gcd (powm 179 5 247 - 1) 247 = 1)
    by (vm_compute; reflexivity).
  split; [exact Hg|].
  intros [Hlt _]. rewrite Hg in Hlt. lia.
Qed.

Theorem matching_247_two_sided_gcd_is_N :
  Z.gcd (powm 179 6 247 - 1) 247 = 247 /\
  ~ Problem_Factor 247 247.
Proof.
  split; [vm_compute; reflexivity|].
  intros [Hlt _]. lia.
Qed.
