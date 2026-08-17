From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * Primitive binary quadratic forms of discriminant [Δ]

    The carrier of [Cl(Δ)] for [Δ < 0].  Composition of arbitrary
    forms is not in this file; identity, inverse, and preservation
    of the discriminant are.  Cross-confirmed by [cas/23_class_group.gp]. *)

Record bqf : Type := {
  bqf_a : Z;
  bqf_b : Z;
  bqf_c : Z
}.

Definition bqf_disc (f : bqf) : Z :=
  bqf_b f * bqf_b f - 4 * bqf_a f * bqf_c f.

Definition bqf_primitive (f : bqf) : Prop :=
  Z.gcd (Z.gcd (bqf_a f) (bqf_b f)) (bqf_c f) = 1.

Definition iq_disc (D : Z) : Prop :=
  D < 0 /\ (D mod 4 = 0 \/ D mod 4 = 1).

Definition of_disc (f : bqf) (D : Z) : Prop :=
  bqf_disc f = D /\ bqf_primitive f.

(** Principal form of discriminant [D]. *)
Definition bqf_id (D : Z) : bqf :=
  if D mod 4 =? 0
  then {| bqf_a := 1; bqf_b := 0; bqf_c := -(D / 4) |}
  else {| bqf_a := 1; bqf_b := 1; bqf_c := (1 - D) / 4 |}.

Definition bqf_inv (f : bqf) : bqf :=
  {| bqf_a := bqf_a f; bqf_b := - bqf_b f; bqf_c := bqf_c f |}.

Lemma bqf_inv_disc :
  forall f, bqf_disc (bqf_inv f) = bqf_disc f.
Proof. intros f. unfold bqf_disc, bqf_inv. simpl. ring. Qed.

Lemma bqf_inv_primitive :
  forall f, bqf_primitive f -> bqf_primitive (bqf_inv f).
Proof.
  intros f. unfold bqf_primitive, bqf_inv. simpl.
  rewrite (Z.gcd_opp_r (bqf_a f) (bqf_b f)).
  intros H. exact H.
Qed.

Lemma bqf_inv_inv :
  forall f, bqf_inv (bqf_inv f) = f.
Proof.
  intros [a b c]. unfold bqf_inv. simpl.
  rewrite Z.opp_involutive. reflexivity.
Qed.

Theorem bqf_id_disc_neg4 : bqf_disc (bqf_id (-4)) = -4.
Proof. vm_compute. reflexivity. Qed.

Theorem bqf_id_disc_neg47 : bqf_disc (bqf_id (-47)) = -47.
Proof. vm_compute. reflexivity. Qed.

Theorem bqf_id_disc_neg23 : bqf_disc (bqf_id (-23)) = -23.
Proof. vm_compute. reflexivity. Qed.

Lemma bqf_id_primitive :
  forall D, bqf_primitive (bqf_id D).
Proof.
  intros D. unfold bqf_primitive, bqf_id, bqf_a, bqf_b, bqf_c.
  destruct (D mod 4 =? 0); rewrite !Z.gcd_1_l; reflexivity.
Qed.

Theorem bqf_id_of_disc_neg47 :
  of_disc (bqf_id (-47)) (-47).
Proof. split; [apply bqf_id_disc_neg47 | apply bqf_id_primitive]. Qed.

(** Reduced (Gauss): [|b| ≤ a ≤ c], and [b ≥ 0] if either equality holds. *)
Definition bqf_reduced (f : bqf) : Prop :=
  Z.abs (bqf_b f) <= bqf_a f <= bqf_c f /\
  (bqf_b f < 0 -> bqf_a f <> Z.abs (bqf_b f) /\ bqf_a f <> bqf_c f).

(** Ambiguous forms (order dividing 2): [b = 0], or [a = b], or [a = −b]. *)
Definition bqf_ambiguous (f : bqf) : Prop :=
  bqf_b f = 0 \/ bqf_a f = bqf_b f \/ bqf_a f = - bqf_b f.

Lemma bqf_id_ambiguous_mod0 :
  forall D, D mod 4 = 0 -> bqf_ambiguous (bqf_id D).
Proof.
  intros D Hm. unfold bqf_ambiguous, bqf_id. rewrite Hm. simpl. now left.
Qed.

Theorem disc_neg47 :
  iq_disc (-47) /\ bqf_disc (bqf_id (-47)) = -47.
Proof.
  split.
  - unfold iq_disc. split; [lia|]. right. vm_compute. reflexivity.
  - apply bqf_id_disc_neg47.
Qed.
