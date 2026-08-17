From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import Hardness.
Require Import BinForms.
Require Import Presentation.

Open Scope Z_scope.

(** * Accumulator membership as the RSA-shaped map

    [A ↦ A^x].  A membership witness for [x] is a root: [W] with
    [W^x = A].  A forged witness for a non-member, given a random
    base, is adaptive root / strong RSA.

    Instantiated on [rsa_presentation]; stated on [cl_presentation]
    (no trapdoor to update with [λ]).  Hash-to-prime is a named
    skip.  No pairings, no Merkle. *)

Definition acc_add (P : Presentation) (A : Pcar P) (x : nat) : Pcar P :=
  Pexp P A x.

Definition acc_mem_wit (P : Presentation) (A W : Pcar P) (x : nat) : Prop :=
  Peq P (Pexp P W x) A.

Theorem membership_witness_is_root :
  forall P A W x,
    (x > 0)%nat ->
    acc_mem_wit P A W x ->
    P_Root P x A W.
Proof.
  intros P A W x Hx H.
  unfold P_Root, acc_mem_wit in *.
  split; assumption.
Qed.

Theorem forged_mem_is_adaptive_root :
  forall P A W e,
    (e > 1)%nat ->
    acc_mem_wit P A W e ->
    P_AdaptiveRoot P A W e.
Proof.
  intros P A W e He H.
  unfold P_AdaptiveRoot, acc_mem_wit in *.
  split; assumption.
Qed.

Theorem rsa_acc_add_is_powm :
  forall N A x,
    acc_add (rsa_presentation N) A x = powm A (Z.of_nat x) N.
Proof. intros. reflexivity. Qed.

Theorem rsa_mem_wit_is_powm :
  forall N A W x,
    1 < N ->
    acc_mem_wit (rsa_presentation N) A W x <->
    powm W (Z.of_nat x) N = A mod N.
Proof.
  intros N A W x HN.
  unfold acc_mem_wit, rsa_presentation. simpl.
  unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem cl_acc_add_is_exp :
  forall D A x,
    acc_add (cl_presentation D) A x = bqf_exp D A x.
Proof. intros. reflexivity. Qed.

(** Updating an RSA accumulator with the trapdoor is exponentiation
    by [x]; there is no [λ] to update a class-group accumulator. *)
Theorem cl_has_no_trapdoor_update :
  forall D, Pannihilator (cl_presentation D) = Some 2.
Proof. intros. apply cl_public_annihilator_is_two. Qed.

Theorem rsa_public_has_no_trapdoor_update :
  forall N, Pannihilator (rsa_presentation N) = None.
Proof. intros. apply rsa_public_annihilator_is_none. Qed.
