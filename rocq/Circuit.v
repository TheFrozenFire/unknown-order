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

(** * A two-gate circuit: [z = x·y + t]

    Intermediate wire [m = x·y], then [z = m + t].  Each gate
    is already a QAP; the circuit is the pair, sharing [m].

    Cross-confirmed by [cas/102_circuit.gp]. *)

Definition prod_add_m (x y : Z) : Z := x * y.

Theorem prod_add_sat :
  forall x y t z u,
    z = x * y + t ->
    qap_at (poly_lincomb (mul_w x y (x * y)) mul_As)
           (poly_lincomb (mul_w x y (x * y)) mul_Bs)
           (poly_lincomb (mul_w x y (x * y)) mul_Cs)
           mul_H mul_van u /\
    qap_at (add_A (x * y) t) add_B (add_C z) add_H add_van u.
Proof.
  intros x y t z u Hz.
  split.
  - apply mul_gate_sat. reflexivity.
  - apply add_gate_sat. lia.
Qed.

Theorem prod_add_complete :
  forall N g tau x y t z,
    1 < N ->
    0 <= tau ->
    0 <= x ->
    0 <= y ->
    0 <= t ->
    0 <= z ->
    0 <= x * y ->
    z = x * y + t ->
    pot_poly N g tau
      (poly_conv (poly_lincomb (mul_w x y (x * y)) mul_As)
                 (poly_lincomb (mul_w x y (x * y)) mul_Bs)) =
      (pot_poly N g tau (poly_lincomb (mul_w x y (x * y)) mul_Cs) *
         pot_poly N g tau (poly_conv mul_H mul_van)) mod N /\
    pot_poly N g tau (poly_conv (add_A (x * y) t) add_B) =
      (pot_poly N g tau (add_C z) *
         pot_poly N g tau (poly_conv add_H add_van)) mod N.
Proof.
  intros N g tau x y t z Hn Ht Hx Hy Htm Hz Hm Heq.
  split.
  - apply mul_gate_complete; try assumption. reflexivity.
  - apply add_gate_complete; try assumption; lia.
Qed.

Theorem mul_public_first :
  forall N g tau w0 w1 w2,
    1 < N ->
    0 <= w0 ->
    0 <= w1 ->
    0 <= w2 ->
    pot_wires N g tau (mul_w w0 w1 w2) mul_As =
      (powm (pot_poly N g tau (1 :: nil)) w0 N *
         pot_wires N g tau (w1 :: w2 :: nil)
           ((0 :: nil) :: (0 :: nil) :: nil)) mod N.
Proof.
  intros N g tau w0 w1 w2 Hn H0 H1 H2.
  unfold mul_w, mul_As.
  change (w0 :: w1 :: w2 :: nil)
    with ((w0 :: nil) ++ (w1 :: w2 :: nil)).
  change ((1 :: nil) :: (0 :: nil) :: (0 :: nil) :: nil)
    with (((1 :: nil) :: nil) ++ ((0 :: nil) :: (0 :: nil) :: nil)).
  rewrite (pot_wires_app N g tau (w0 :: nil) (w1 :: w2 :: nil)
             ((1 :: nil) :: nil)
             ((0 :: nil) :: (0 :: nil) :: nil));
    [| exact Hn | | reflexivity].
  - simpl. rewrite Z.mod_1_l by lia. rewrite Z.mul_1_r.
    rewrite Z.mul_mod_idemp_r by lia.
    rewrite Z.mul_mod_idemp_l by lia.
    rewrite Z.mul_mod_idemp_r by lia.
    reflexivity.
  - constructor; [exact H0 | cbn [poly_eval]; nia | constructor].
Qed.
