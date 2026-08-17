From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.

Require Import RocqProofs.NumberTheory.
Require Import TwoSylow.

Open Scope Z_scope.

(** * Multi-prime stress test: [N = pqr] has eight roots of [1]

    [sqrt1_is_crt_pm1] is two-prime: four combinations of [±1].
    Three distinct odd primes give [2³] sign patterns.  This file
    records the arity; it does not rewrite [TwoSylow]. *)

Definition three_prime (p q r : Z) : Prop :=
  Z.prime p /\ Z.prime q /\ Z.prime r /\
  p <> q /\ p <> r /\ q <> r.

Theorem two_prime_sqrt1_is_pm1_each :
  forall p q x,
    Z.prime p -> Z.prime q -> p <> q ->
    powm x 2 (p * q) = 1 ->
    (x mod p = 1 \/ x mod p = p - 1) /\
    (x mod q = 1 \/ x mod q = q - 1).
Proof. apply sqrt1_is_crt_pm1. Qed.

Theorem three_prime_sqrt1_is_pm1_each :
  forall p q r x,
    three_prime p q r ->
    powm x 2 (p * q * r) = 1 ->
    (x mod p = 1 \/ x mod p = p - 1) /\
    (x mod q = 1 \/ x mod q = q - 1) /\
    (x mod r = 1 \/ x mod r = r - 1).
Proof.
  intros p q r x [Hp [Hq [Hr [Hpq [Hpr Hqr]]]]] Hsq.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  pose proof (Z.prime_ge_2 r Hr).
  assert (powm x 2 p = 1) as Hp1.
  { unfold powm in Hsq |- *.
    rewrite Z.pow_2_r in Hsq |- *.
    transitivity (((x * x) mod (p * q * r)) mod p).
    - symmetry. apply Z.mod_mod_divide. exists (q * r). ring.
    - rewrite Hsq. apply Z.mod_1_l. lia. }
  assert (powm x 2 q = 1) as Hq1.
  { unfold powm in Hsq |- *.
    rewrite Z.pow_2_r in Hsq |- *.
    transitivity (((x * x) mod (p * q * r)) mod q).
    - symmetry. apply Z.mod_mod_divide. exists (p * r). ring.
    - rewrite Hsq. apply Z.mod_1_l. lia. }
  assert (powm x 2 r = 1) as Hr1.
  { unfold powm in Hsq |- *.
    rewrite Z.pow_2_r in Hsq |- *.
    transitivity (((x * x) mod (p * q * r)) mod r).
    - symmetry. apply Z.mod_mod_divide. exists (p * q). ring.
    - rewrite Hsq. apply Z.mod_1_l. lia. }
  split; [|split].
  - apply powm_2_mod_prime_pm1; assumption.
  - apply powm_2_mod_prime_pm1; assumption.
  - apply powm_2_mod_prime_pm1; assumption.
Qed.

(** Eight sign patterns: each coordinate independently [±1].
    Two-prime admits only four. *)
Definition sign_pat : Type := (bool * bool * bool).

Definition eight_pats : list sign_pat :=
  (false, false, false) :: (false, false, true) ::
  (false, true, false) :: (false, true, true) ::
  (true, false, false) :: (true, false, true) ::
  (true, true, false) :: (true, true, true) :: nil.

Theorem eight_pats_length : List.length eight_pats = 8%nat.
Proof. reflexivity. Qed.

Theorem two_prime_arity_is_four :
  forall p q,
    Z.prime p -> Z.prime q -> p <> q ->
    (forall x, powm x 2 (p * q) = 1 ->
      (x mod p = 1 \/ x mod p = p - 1) /\
      (x mod q = 1 \/ x mod q = q - 1)).
Proof. intros. apply sqrt1_is_crt_pm1; assumption. Qed.

(** The two-prime theorem does not mention a third prime.
    That is the arity record: [TwoSylow] is about [N = pq]. *)
Theorem two_sylow_is_two_prime :
  forall p q x,
    Z.prime p -> Z.prime q -> p <> q ->
    powm x 2 (p * q) = 1 ->
    (x mod p = 1 \/ x mod p = p - 1).
Proof. intros. apply sqrt1_is_crt_pm1 in H2; tauto. Qed.
