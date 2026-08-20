From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import EvalProduct.
Require Import QAP.
Require Import MulGate.

Open Scope Z_scope.

(** * Two-bit value from bits

    [v = b0 + 2 b1] with [b0, b1 ∈ {0,1}].  Each bit is a mul
    gate on [(b,b,b)].  The encoding of [v] is public from the
    bit encodings: [g^v = g^{b0} · (g^{b1})²].

    Cross-confirmed by [cas/104_range2.gp]. *)

Definition range2 (b0 b1 : Z) : Z := b0 + 2 * b1.

Theorem range2_bits :
  forall b0 b1,
    (b0 = 0 \/ b0 = 1) ->
    (b1 = 0 \/ b1 = 1) ->
    0 <= range2 b0 b1 <= 3.
Proof.
  intros b0 b1 H0 H1. unfold range2.
  destruct H0, H1; subst; lia.
Qed.

Theorem range2_bit_qap :
  forall b0 b1 u,
    (b0 = 0 \/ b0 = 1) ->
    (b1 = 0 \/ b1 = 1) ->
    qap_at (poly_lincomb (mul_w b0 b0 b0) mul_As)
           (poly_lincomb (mul_w b0 b0 b0) mul_Bs)
           (poly_lincomb (mul_w b0 b0 b0) mul_Cs)
           mul_H mul_van u /\
    qap_at (poly_lincomb (mul_w b1 b1 b1) mul_As)
           (poly_lincomb (mul_w b1 b1 b1) mul_Bs)
           (poly_lincomb (mul_w b1 b1 b1) mul_Cs)
           mul_H mul_van u.
Proof.
  intros b0 b1 u H0 H1.
  split; apply bit_sat; assumption.
Qed.

Theorem range2_encoding :
  forall (N g b0 b1 : Z),
    1 < N ->
    0 <= b0 ->
    0 <= b1 ->
    powm g (range2 b0 b1) N =
      (powm g b0 N * powm (powm g b1 N) 2 N) mod N.
Proof.
  intros N g b0 b1 Hn H0 H1.
  unfold range2.
  rewrite <- powm_mul_r by lia.
  replace (b1 * 2) with (2 * b1) by lia.
  rewrite <- powm_add_r by nia.
  reflexivity.
Qed.

Theorem range2_eval_commit :
  forall N g tau b0 b1,
    1 < N ->
    0 <= tau ->
    0 <= b0 ->
    0 <= b1 ->
    pot_poly N g tau (range2 b0 b1 :: nil) =
      (powm g b0 N * powm (powm g b1 N) 2 N) mod N.
Proof.
  intros N g tau b0 b1 Hn Ht H0 H1.
  unfold pot_poly. cbn [poly_eval].
  replace (range2 b0 b1 + tau * 0) with (range2 b0 b1) by lia.
  apply range2_encoding; [exact Hn | exact H0 | exact H1].
Qed.
