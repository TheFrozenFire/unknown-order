From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import EvalProduct.
Require Import QAP.
Require Import AddGate.

Open Scope Z_scope.

(** * Wire equality: [w0 = w1] is [w0 + 0 = w1]

    Cross-confirmed by [cas/106_wire_eq.gp]. *)

Theorem wire_eq_sat :
  forall w0 w1 u,
    w0 = w1 ->
    qap_at (add_A w0 0) add_B (add_C w1) add_H add_van u.
Proof.
  intros w0 w1 u Heq.
  apply add_gate_sat. lia.
Qed.

Theorem wire_eq_complete :
  forall N g tau w0 w1,
    1 < N ->
    0 <= w0 ->
    0 <= w1 ->
    w0 = w1 ->
    pot_poly N g tau (poly_conv (add_A w0 0) add_B) =
      (pot_poly N g tau (add_C w1) *
         pot_poly N g tau (poly_conv add_H add_van)) mod N.
Proof.
  intros N g tau w0 w1 Hn H0 H1 Heq.
  apply add_gate_complete; try assumption; lia.
Qed.

Theorem wire_eq_same_encoding :
  forall (N g w0 w1 : Z),
    1 < N ->
    0 <= w0 ->
    w0 = w1 ->
    powm g w0 N = powm g w1 N.
Proof.
  intros N g w0 w1 Hn H0 Heq. subst. reflexivity.
Qed.
