From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import EvalProduct.
Require Import QAP.

Open Scope Z_scope.

(** * One multiplication gate as a QAP

    Constraint [w0 · w1 = w2].  Selector families are constants
    that pick the three wires; [Z = X] vanishes at [0], and with
    constant [A_w, B_w, C_w] the identity holds at every point
    iff the gate does.  Completeness of the encodings is
    [mul_gate_complete].

    Cross-confirmed by [cas/98_mul_gate.gp]. *)

Definition mul_As : list (list Z) :=
  (1 :: nil) :: (0 :: nil) :: (0 :: nil) :: nil.

Definition mul_Bs : list (list Z) :=
  (0 :: nil) :: (1 :: nil) :: (0 :: nil) :: nil.

Definition mul_Cs : list (list Z) :=
  (0 :: nil) :: (0 :: nil) :: (1 :: nil) :: nil.

Definition mul_H : list Z := 0 :: nil.

Definition mul_van : list Z := 0 :: 1 :: nil.

Definition mul_w (w0 w1 w2 : Z) : list Z :=
  w0 :: w1 :: w2 :: nil.

Lemma mul_Aw :
  forall w0 w1 w2,
    poly_lincomb (mul_w w0 w1 w2) mul_As = w0 :: nil.
Proof.
  intros. unfold mul_w, mul_As, poly_lincomb, map_mul, poly_add.
  simpl. replace (w0 * 1 + (w1 * 0 + w2 * 0)) with w0 by ring. reflexivity.
Qed.

Lemma mul_Bw :
  forall w0 w1 w2,
    poly_lincomb (mul_w w0 w1 w2) mul_Bs = w1 :: nil.
Proof.
  intros. unfold mul_w, mul_Bs, poly_lincomb, map_mul, poly_add.
  simpl. replace (w0 * 0 + (w1 * 1 + w2 * 0)) with w1 by ring. reflexivity.
Qed.

Lemma mul_Cw :
  forall w0 w1 w2,
    poly_lincomb (mul_w w0 w1 w2) mul_Cs = w2 :: nil.
Proof.
  intros. unfold mul_w, mul_Cs, poly_lincomb, map_mul, poly_add.
  simpl. replace (w0 * 0 + (w1 * 0 + w2 * 1)) with w2 by ring. reflexivity.
Qed.

Lemma mul_eval_Aw :
  forall w0 w1 w2 x,
    poly_eval (poly_lincomb (mul_w w0 w1 w2) mul_As) x = w0.
Proof. intros. rewrite mul_Aw. simpl. lia. Qed.

Lemma mul_eval_Bw :
  forall w0 w1 w2 x,
    poly_eval (poly_lincomb (mul_w w0 w1 w2) mul_Bs) x = w1.
Proof. intros. rewrite mul_Bw. simpl. lia. Qed.

Lemma mul_eval_Cw :
  forall w0 w1 w2 x,
    poly_eval (poly_lincomb (mul_w w0 w1 w2) mul_Cs) x = w2.
Proof. intros. rewrite mul_Cw. simpl. lia. Qed.

Theorem mul_gate_sat :
  forall w0 w1 w2 x,
    w0 * w1 = w2 ->
    qap_at (poly_lincomb (mul_w w0 w1 w2) mul_As)
           (poly_lincomb (mul_w w0 w1 w2) mul_Bs)
           (poly_lincomb (mul_w w0 w1 w2) mul_Cs)
           mul_H mul_van x.
Proof.
  intros w0 w1 w2 x Hw.
  unfold qap_at, mul_H, mul_van.
  rewrite mul_eval_Aw, mul_eval_Bw, mul_eval_Cw.
  simpl. lia.
Qed.

Theorem mul_gate_complete :
  forall N g tau w0 w1 w2,
    1 < N ->
    0 <= tau ->
    0 <= w0 ->
    0 <= w1 ->
    0 <= w2 ->
    w0 * w1 = w2 ->
    pot_poly N g tau
      (poly_conv (poly_lincomb (mul_w w0 w1 w2) mul_As)
                 (poly_lincomb (mul_w w0 w1 w2) mul_Bs)) =
      (pot_poly N g tau (poly_lincomb (mul_w w0 w1 w2) mul_Cs) *
         pot_poly N g tau (poly_conv mul_H mul_van)) mod N.
Proof.
  intros N g tau w0 w1 w2 Hn Ht Hw0 Hw1 Hw2 Hsat.
  apply qap_complete_at_tau.
  - exact Hn.
  - apply mul_gate_sat. exact Hsat.
  - rewrite mul_eval_Cw. exact Hw2.
  - unfold mul_H, mul_van.
    rewrite poly_eval_conv. simpl. nia.
Qed.

Lemma mul_wires_nn :
  forall tau w0 w1 w2,
    0 <= w0 ->
    0 <= w1 ->
    0 <= w2 ->
    wires_nn tau (mul_w w0 w1 w2) mul_As /\
    wires_nn tau (mul_w w0 w1 w2) mul_Bs /\
    wires_nn tau (mul_w w0 w1 w2) mul_Cs.
Proof.
  intros tau w0 w1 w2 H0 H1 H2.
  unfold mul_w, mul_As, mul_Bs, mul_Cs.
  split; [|split].
  - constructor; [exact H0 | cbn [poly_eval]; nia |].
    constructor; [exact H1 | cbn [poly_eval]; nia |].
    constructor; [exact H2 | cbn [poly_eval]; nia |].
    constructor.
  - constructor; [exact H0 | cbn [poly_eval]; nia |].
    constructor; [exact H1 | cbn [poly_eval]; nia |].
    constructor; [exact H2 | cbn [poly_eval]; nia |].
    constructor.
  - constructor; [exact H0 | cbn [poly_eval]; nia |].
    constructor; [exact H1 | cbn [poly_eval]; nia |].
    constructor; [exact H2 | cbn [poly_eval]; nia |].
    constructor.
Qed.

Theorem bit_sat :
  forall w x,
    (w = 0 \/ w = 1) ->
    qap_at (poly_lincomb (mul_w w w w) mul_As)
           (poly_lincomb (mul_w w w w) mul_Bs)
           (poly_lincomb (mul_w w w w) mul_Cs)
           mul_H mul_van x.
Proof.
  intros w x Hw.
  apply mul_gate_sat.
  destruct Hw; subst; ring.
Qed.

Theorem bit_complete :
  forall N g tau w,
    1 < N ->
    0 <= tau ->
    (w = 0 \/ w = 1) ->
    pot_poly N g tau
      (poly_conv (poly_lincomb (mul_w w w w) mul_As)
                 (poly_lincomb (mul_w w w w) mul_Bs)) =
      (pot_poly N g tau (poly_lincomb (mul_w w w w) mul_Cs) *
         pot_poly N g tau (poly_conv mul_H mul_van)) mod N.
Proof.
  intros N g tau w Hn Ht Hw.
  apply mul_gate_complete; try assumption.
  - destruct Hw; subst; lia.
  - destruct Hw; subst; lia.
  - destruct Hw; subst; lia.
  - destruct Hw; subst; ring.
Qed.
