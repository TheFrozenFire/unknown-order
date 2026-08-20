From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import EvalProduct.
Require Import QAP.
Require Import MulGate.
Require Import AddGate.

Open Scope Z_scope.

(** * Bit operations from the mul and add gates

    AND is multiplication.  OR is [x + y − xy].  XOR is
    [x + y − 2xy].  On [{0,1}] these stay in [{0,1}] and
    match the truth tables.

    Cross-confirmed by [cas/103_bit_logic.gp]. *)

Definition bit_and (x y : Z) : Z := x * y.

Definition bit_or (x y : Z) : Z := x + y - x * y.

Definition bit_xor (x y : Z) : Z := x + y - 2 * x * y.

Definition is_bit (w : Z) : Prop := w = 0 \/ w = 1.

Theorem bit_and_is_mul :
  forall x y u,
    qap_at (poly_lincomb (mul_w x y (bit_and x y)) mul_As)
           (poly_lincomb (mul_w x y (bit_and x y)) mul_Bs)
           (poly_lincomb (mul_w x y (bit_and x y)) mul_Cs)
           mul_H mul_van u.
Proof.
  intros. unfold bit_and. apply mul_gate_sat. reflexivity.
Qed.

Theorem bit_and_closed :
  forall x y, is_bit x -> is_bit y -> is_bit (bit_and x y).
Proof.
  intros x y Hx Hy. unfold is_bit, bit_and in *.
  destruct Hx, Hy; subst; (left; reflexivity) || (right; reflexivity).
Qed.

Theorem bit_or_table :
  forall x y, is_bit x -> is_bit y ->
    (x = 0 /\ y = 0 -> bit_or x y = 0) /\
    (x = 1 \/ y = 1 -> bit_or x y = 1).
Proof.
  intros x y Hx Hy. unfold bit_or, is_bit in *.
  destruct Hx, Hy; subst; split; intros; try reflexivity; try lia.
Qed.

Theorem bit_or_closed :
  forall x y, is_bit x -> is_bit y -> is_bit (bit_or x y).
Proof.
  intros x y Hx Hy. unfold is_bit, bit_or in *.
  destruct Hx, Hy; subst; simpl; (left; reflexivity) || (right; reflexivity).
Qed.

Theorem bit_xor_table :
  forall x y, is_bit x -> is_bit y ->
    bit_xor x y = (x + y) mod 2.
Proof.
  intros x y Hx Hy. unfold bit_xor, is_bit in *.
  destruct Hx, Hy; subst; simpl; reflexivity.
Qed.

Theorem bit_xor_closed :
  forall x y, is_bit x -> is_bit y -> is_bit (bit_xor x y).
Proof.
  intros x y Hx Hy. unfold is_bit, bit_xor in *.
  destruct Hx, Hy; subst; simpl; (left; reflexivity) || (right; reflexivity).
Qed.

Theorem bit_or_from_and :
  forall x y,
    bit_or x y = x + y - bit_and x y.
Proof. intros. unfold bit_or, bit_and. reflexivity. Qed.

Theorem bit_xor_from_and :
  forall x y,
    bit_xor x y = x + y - 2 * bit_and x y.
Proof. intros. unfold bit_xor, bit_and. ring. Qed.
