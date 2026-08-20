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
Require Import BitSum.

Open Scope Z_scope.

(** * Every limb is a bit, and the value encoding unfolds

    [all_bits] is [is_bit] on each limb.  Each bit is the mul
    gate [(b,b,b)].  Three-bit values use two [bit_value_cons]
    steps.

    Cross-confirmed by [cas/111_all_bits.gp]. *)

Inductive all_bits : list Z -> Prop :=
  | ab_nil : all_bits nil
  | ab_cons : forall b rest, is_bit b -> all_bits rest -> all_bits (b :: rest).

Lemma all_bits_nn :
  forall bs, all_bits bs -> nn bs.
Proof.
  intros bs H. induction H.
  - constructor.
  - unfold is_bit in H. destruct H; subst; constructor; try lia; assumption.
Qed.

Theorem all_bits_value_nonneg :
  forall bs, all_bits bs -> 0 <= bit_value bs.
Proof.
  intros bs H. apply bit_value_nonneg. apply all_bits_nn. exact H.
Qed.

Theorem all_bits_qap :
  forall (b u : Z),
    is_bit b ->
    qap_at (poly_lincomb (mul_w b b b) mul_As)
           (poly_lincomb (mul_w b b b) mul_Bs)
           (poly_lincomb (mul_w b b b) mul_Cs)
           mul_H mul_van u.
Proof.
  intros b u Hb. apply bit_sat. exact Hb.
Qed.

Theorem three_bit_encoding :
  forall N g b0 b1 b2,
    1 < N ->
    0 <= b0 ->
    0 <= b1 ->
    0 <= b2 ->
    powm g (bit_value (b0 :: b1 :: b2 :: nil)) N =
      (powm g b0 N *
         powm (powm g b1 N * powm (powm g b2 N) 2 N) 2 N) mod N.
Proof.
  intros N g b0 b1 b2 Hn H0 H1 H2.
  assert (0 <= bit_value (b1 :: b2 :: nil)) as Hv.
  { simpl.
    change (match b2 + 0 with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0
            | Z.neg y' => Z.neg y'~0
            end) with (2 * (b2 + 0)).
    nia. }
  pose proof (bit_value_cons_encoding N g b0 (b1 :: b2 :: nil) Hn H0 Hv) as Hhd.
  rewrite Hhd.
  assert (0 <= bit_value (b2 :: nil)) as Hr by (simpl; lia).
  pose proof (bit_value_cons_encoding N g b1 (b2 :: nil) Hn H1 Hr) as Htl.
  cbn [bit_value] in Htl.
  rewrite Z.mul_0_r, Z.add_0_r in Htl.
  cbn [bit_value].
  rewrite Z.mul_0_r, Z.add_0_r.
  change (match b2 with
          | 0 => 0
          | Z.pos y' => Z.pos y'~0
          | Z.neg y' => Z.neg y'~0
          end) with (2 * b2).
  rewrite Htl.
  rewrite powm_mod_base by lia.
  reflexivity.
Qed.
