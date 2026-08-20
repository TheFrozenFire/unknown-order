From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import EvalProduct.
Require Import QAP.
Require Import MulGate.
Require Import Range2.

Open Scope Z_scope.

(** * Little-endian bit-sum: [v = b0 + 2 v_rest]

    Recursive encoding [g^v = g^{b0} · (g^{v_rest})²].  Each
    bit is a mul gate.  Two-bit range is the first unfolding.

    Cross-confirmed by [cas/107_bit_sum.gp]. *)

Fixpoint bit_value (bs : list Z) : Z :=
  match bs with
  | nil => 0
  | b :: rest => b + 2 * bit_value rest
  end.

Lemma bit_value_nil : bit_value nil = 0.
Proof. reflexivity. Qed.

Lemma bit_value_cons :
  forall b rest, bit_value (b :: rest) = b + 2 * bit_value rest.
Proof. intros. reflexivity. Qed.

Theorem bit_value_nonneg :
  forall bs, nn bs -> 0 <= bit_value bs.
Proof.
  intros bs Hnn.
  induction Hnn as [|b rest Hb Hrest IH].
  - simpl. lia.
  - simpl.
    change (match bit_value rest with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0
            | Z.neg y' => Z.neg y'~0
            end) with (2 * bit_value rest).
    nia.
Qed.

Theorem bit_value_cons_encoding :
  forall N g b rest,
    1 < N ->
    0 <= b ->
    0 <= bit_value rest ->
    powm g (bit_value (b :: rest)) N =
      (powm g b N * powm (powm g (bit_value rest) N) 2 N) mod N.
Proof.
  intros N g b rest Hn Hb Hv.
  simpl.
  rewrite <- powm_mul_r by lia.
  replace (bit_value rest * 2) with (2 * bit_value rest) by lia.
  rewrite <- powm_add_r by nia.
  reflexivity.
Qed.

Theorem bit_value_range2 :
  forall b0 b1, bit_value (b0 :: b1 :: nil) = range2 b0 b1.
Proof. intros. unfold range2. cbn [bit_value]. ring. Qed.

Theorem nested_square :
  forall N g tau x,
    1 < N ->
    0 <= tau ->
    0 <= x ->
    0 <= x * x ->
    pot_poly N g tau
      (poly_conv (poly_lincomb (mul_w x x (x * x)) mul_As)
                 (poly_lincomb (mul_w x x (x * x)) mul_Bs)) =
      (pot_poly N g tau (poly_lincomb (mul_w x x (x * x)) mul_Cs) *
         pot_poly N g tau (poly_conv mul_H mul_van)) mod N.
Proof.
  intros N g tau x Hn Ht Hx Hsq.
  apply mul_gate_complete; try assumption. reflexivity.
Qed.
