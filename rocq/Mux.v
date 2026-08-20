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
Require Import BitLogic.

Open Scope Z_scope.

(** * Select: [mux s a b = s·a + (1−s)·b]

    On a bit [s] this is [a] or [b].  Gates: two muls
    [s·a], [s·b], and the add [s·a + b = out + s·b].

    Cross-confirmed by [cas/105_mux.gp]. *)

Definition mux (s a b : Z) : Z := s * a + (1 - s) * b.

Theorem mux_on_zero :
  forall a b, mux 0 a b = b.
Proof. intros. unfold mux. ring. Qed.

Theorem mux_on_one :
  forall a b, mux 1 a b = a.
Proof. intros. unfold mux. ring. Qed.

Theorem mux_select :
  forall s a b,
    is_bit s ->
    (s = 0 /\ mux s a b = b) \/ (s = 1 /\ mux s a b = a).
Proof.
  intros s a b Hs. unfold is_bit in Hs.
  destruct Hs as [Hs0 | Hs1].
  - left. subst. split. reflexivity. apply mux_on_zero.
  - right. subst. split. reflexivity. apply mux_on_one.
Qed.

Theorem mux_nonneg :
  forall s a b,
    is_bit s ->
    0 <= a ->
    0 <= b ->
    0 <= mux s a b.
Proof.
  intros s a b Hs Ha Hb. unfold is_bit in Hs.
  destruct Hs; subst; unfold mux; nia.
Qed.

Theorem mux_gates :
  forall s a b out u,
    is_bit s ->
    out = mux s a b ->
    qap_at (poly_lincomb (mul_w s a (s * a)) mul_As)
           (poly_lincomb (mul_w s a (s * a)) mul_Bs)
           (poly_lincomb (mul_w s a (s * a)) mul_Cs)
           mul_H mul_van u /\
    qap_at (poly_lincomb (mul_w s b (s * b)) mul_As)
           (poly_lincomb (mul_w s b (s * b)) mul_Bs)
           (poly_lincomb (mul_w s b (s * b)) mul_Cs)
           mul_H mul_van u /\
    qap_at (add_A (s * a) b) add_B (add_C (out + s * b))
           add_H add_van u.
Proof.
  intros s a b out u Hs Hout.
  split; [|split].
  - apply mul_gate_sat. reflexivity.
  - apply mul_gate_sat. reflexivity.
  - apply add_gate_sat. unfold mux in Hout. lia.
Qed.

Theorem mux_complete :
  forall N g tau s a b out,
    1 < N ->
    0 <= tau ->
    is_bit s ->
    0 <= a ->
    0 <= b ->
    0 <= out ->
    out = mux s a b ->
    pot_poly N g tau
      (poly_conv (poly_lincomb (mul_w s a (s * a)) mul_As)
                 (poly_lincomb (mul_w s a (s * a)) mul_Bs)) =
      (pot_poly N g tau (poly_lincomb (mul_w s a (s * a)) mul_Cs) *
         pot_poly N g tau (poly_conv mul_H mul_van)) mod N.
Proof.
  intros N g tau s a b out Hn Ht Hs Ha Hb Ho Hout.
  apply mul_gate_complete; try assumption.
  - unfold is_bit in Hs. destruct Hs; subst; lia.
  - unfold is_bit in Hs. destruct Hs; subst; nia.
  - reflexivity.
Qed.
