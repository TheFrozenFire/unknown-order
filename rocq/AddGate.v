From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import EvalProduct.
Require Import QAP.

Open Scope Z_scope.

(** * Addition as a QAP

    [w0 + w1 = w2] is [(w0+w1) · 1 = w2].  [B] is the public
    constant [1]; [Z = X].  The identity holds at every point
    iff the gate does.

    Cross-confirmed by [cas/101_add_gate.gp]. *)

Definition add_A (w0 w1 : Z) : list Z :=
  (w0 + w1) :: nil.

Definition add_B : list Z := 1 :: nil.

Definition add_C (w2 : Z) : list Z := w2 :: nil.

Definition add_H : list Z := 0 :: nil.

Definition add_van : list Z := 0 :: 1 :: nil.

Theorem add_gate_sat :
  forall w0 w1 w2 x,
    w0 + w1 = w2 ->
    qap_at (add_A w0 w1) add_B (add_C w2) add_H add_van x.
Proof.
  intros w0 w1 w2 x Hw.
  unfold qap_at, add_A, add_B, add_C, add_H, add_van, poly_eval.
  replace (x * 0) with 0 by lia.
  cbn. lia.
Qed.

Theorem add_gate_complete :
  forall N g tau w0 w1 w2,
    1 < N ->
    0 <= w0 ->
    0 <= w1 ->
    0 <= w2 ->
    w0 + w1 = w2 ->
    pot_poly N g tau (poly_conv (add_A w0 w1) add_B) =
      (pot_poly N g tau (add_C w2) *
         pot_poly N g tau (poly_conv add_H add_van)) mod N.
Proof.
  intros N g tau w0 w1 w2 Hn H0 H1 H2 Hsat.
  apply qap_complete_at_tau.
  - exact Hn.
  - apply add_gate_sat. exact Hsat.
  - unfold add_C. simpl. nia.
  - unfold add_H, add_van.
    rewrite poly_eval_conv. simpl. nia.
Qed.

Theorem add_is_public_sum :
  forall N g tau w0 w1,
    1 < N ->
    0 <= w0 ->
    0 <= w1 ->
    pot_poly N g tau (add_A w0 w1) =
      (powm g w0 N * powm g w1 N) mod N.
Proof.
  intros N g tau w0 w1 Hn H0 H1.
  unfold pot_poly, add_A. simpl.
  replace (w0 + w1 + tau * 0) with (w0 + w1) by lia.
  apply powm_add_r; lia.
Qed.
