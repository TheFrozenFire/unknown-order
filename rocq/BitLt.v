From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import EvalProduct.
Require Import QAP.
Require Import MulGate.
Require Import BitLogic.

Open Scope Z_scope.

(** * Bit less-than: [lt x y = (1−x)·y]

    On bits this is [1] iff [x=0] and [y=1].  It is [y − x·y],
    so one mul (AND) and a public subtraction of encodings.

    Cross-confirmed by [cas/109_bit_lt.gp]. *)

Definition bit_lt (x y : Z) : Z := (1 - x) * y.

Theorem bit_lt_table :
  forall x y,
    is_bit x ->
    is_bit y ->
    (bit_lt x y = 1 <-> (x = 0 /\ y = 1)) /\
    (bit_lt x y = 0 <-> (x = 1 \/ y = 0)).
Proof.
  intros x y Hx Hy. unfold is_bit, bit_lt in *.
  destruct Hx, Hy; subst; split; split; intros; try lia; try reflexivity.
Qed.

Theorem bit_lt_closed :
  forall x y, is_bit x -> is_bit y -> is_bit (bit_lt x y).
Proof.
  intros x y Hx Hy. unfold is_bit, bit_lt in *.
  destruct Hx, Hy; subst; simpl; (left; reflexivity) || (right; reflexivity).
Qed.

Theorem bit_lt_is_and :
  forall x y, bit_lt x y = y - bit_and x y.
Proof. intros. unfold bit_lt, bit_and. ring. Qed.

Theorem bit_lt_mul :
  forall x y u,
    qap_at (poly_lincomb (mul_w (1 - x) y (bit_lt x y)) mul_As)
           (poly_lincomb (mul_w (1 - x) y (bit_lt x y)) mul_Bs)
           (poly_lincomb (mul_w (1 - x) y (bit_lt x y)) mul_Cs)
           mul_H mul_van u.
Proof.
  intros. unfold bit_lt. apply mul_gate_sat. reflexivity.
Qed.
