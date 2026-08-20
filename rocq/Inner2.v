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

(** * Inner product of two pairs: [s = x0·y0 + x1·y1]

    Two muls sharing nothing, then one add.  Completeness is
    the pair of mul encodings plus the add encoding.

    Cross-confirmed by [cas/108_inner2.gp]. *)

Definition inner2 (x0 y0 x1 y1 : Z) : Z := x0 * y0 + x1 * y1.

Theorem inner2_sat :
  forall x0 y0 x1 y1 s u,
    s = inner2 x0 y0 x1 y1 ->
    qap_at (poly_lincomb (mul_w x0 y0 (x0 * y0)) mul_As)
           (poly_lincomb (mul_w x0 y0 (x0 * y0)) mul_Bs)
           (poly_lincomb (mul_w x0 y0 (x0 * y0)) mul_Cs)
           mul_H mul_van u /\
    qap_at (poly_lincomb (mul_w x1 y1 (x1 * y1)) mul_As)
           (poly_lincomb (mul_w x1 y1 (x1 * y1)) mul_Bs)
           (poly_lincomb (mul_w x1 y1 (x1 * y1)) mul_Cs)
           mul_H mul_van u /\
    qap_at (add_A (x0 * y0) (x1 * y1)) add_B (add_C s)
           add_H add_van u.
Proof.
  intros x0 y0 x1 y1 s u Hs.
  unfold inner2 in Hs.
  split; [|split].
  - apply mul_gate_sat. reflexivity.
  - apply mul_gate_sat. reflexivity.
  - apply add_gate_sat. lia.
Qed.

Theorem inner2_complete :
  forall N g tau x0 y0 x1 y1 s,
    1 < N ->
    0 <= tau ->
    0 <= x0 ->
    0 <= y0 ->
    0 <= x1 ->
    0 <= y1 ->
    0 <= x0 * y0 ->
    0 <= x1 * y1 ->
    0 <= s ->
    s = inner2 x0 y0 x1 y1 ->
    pot_poly N g tau (poly_conv (add_A (x0 * y0) (x1 * y1)) add_B) =
      (pot_poly N g tau (add_C s) *
         pot_poly N g tau (poly_conv add_H add_van)) mod N.
Proof.
  intros N g tau x0 y0 x1 y1 s Hn Ht Hx0 Hy0 Hx1 Hy1 Hp0 Hp1 Hs Heq.
  apply add_gate_complete; try assumption.
  unfold inner2 in Heq. lia.
Qed.

Theorem inner2_public_sum :
  forall (N g x0 y0 x1 y1 : Z),
    1 < N ->
    0 <= x0 * y0 ->
    0 <= x1 * y1 ->
    powm g (inner2 x0 y0 x1 y1) N =
      (powm g (x0 * y0) N * powm g (x1 * y1) N) mod N.
Proof.
  intros N g x0 y0 x1 y1 Hn Hp0 Hp1.
  unfold inner2.
  apply powm_add_r; lia.
Qed.
