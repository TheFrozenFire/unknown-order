From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import EvalProduct.
Require Import QAP.

Open Scope Z_scope.

(** * Same witness on two specialized CRSs

    If [C_A = ∏ U_j^{w_j}] and [C_B = ∏ V_j^{w_j}] use the *same*
    [w], then for a public [r]

    [C_A · C_B^r = ∏ (U_j · V_j^r)^{w_j}].

    The right-hand side is a wire commit against [A_j + r B_j]
    ([same_w_check]).

    Cross-confirmed by [cas/99_same_w.gp]. *)

Fixpoint zip_scale_add (r : Z) (As Bs : list (list Z)) : list (list Z) :=
  match As, Bs with
  | A :: As', B :: Bs' =>
      poly_add A (map_mul r B) :: zip_scale_add r As' Bs'
  | _, _ => nil
  end.

Lemma zip_scale_eval :
  forall w r As Bs x,
    length w = length As ->
    length w = length Bs ->
    poly_eval (poly_lincomb w (zip_scale_add r As Bs)) x =
      poly_eval (poly_lincomb w As) x +
        r * poly_eval (poly_lincomb w Bs) x.
Proof.
  intros w r.
  induction w as [|ww w IH]; intros As Bs x Hla Hlb.
  - simpl in Hla, Hlb. destruct As; destruct Bs; simpl in *; try discriminate; lia.
  - destruct As as [|A As]; [discriminate|].
    destruct Bs as [|B Bs]; [discriminate|].
    simpl in Hla, Hlb.
    cbn [zip_scale_add].
    rewrite !poly_eval_lincomb.
    rewrite poly_eval_add, !poly_eval_map_mul.
    rewrite <- (poly_eval_lincomb w (zip_scale_add r As Bs) x).
    rewrite (IH As Bs x ltac:(lia) ltac:(lia)).
    rewrite !poly_eval_lincomb.
    ring.
Qed.

Lemma zip_wires_nn :
  forall tau r w As Bs,
    0 <= r ->
    wires_nn tau w As ->
    wires_nn tau w Bs ->
    wires_nn tau w (zip_scale_add r As Bs).
Proof.
  intros tau r w As Bs Hr HAs.
  revert Bs.
  induction HAs; intros Bs HBs.
  - constructor.
  - constructor.
  - destruct Bs as [|B Bs].
    + constructor.
    + inversion HBs; subst.
      constructor.
      * exact H.
      * rewrite poly_eval_add, poly_eval_map_mul. nia.
      * apply IHHAs. assumption.
Qed.

Theorem same_w_check :
  forall N g tau w r As Bs,
    1 < N ->
    0 <= r ->
    length w = length As ->
    length w = length Bs ->
    wires_nn tau w As ->
    wires_nn tau w Bs ->
    (pot_wires N g tau w As *
       powm (pot_wires N g tau w Bs) r N) mod N =
      pot_wires N g tau w (zip_scale_add r As Bs).
Proof.
  intros N g tau w r As Bs Hn Hr Hla Hlb HAs HBs.
  assert (Hzip : wires_nn tau w (zip_scale_add r As Bs)).
  { apply zip_wires_nn; assumption. }
  rewrite (pot_wires_is_lincomb N g tau w As Hn HAs).
  rewrite (pot_wires_is_lincomb N g tau w Bs Hn HBs).
  rewrite (pot_wires_is_lincomb N g tau w (zip_scale_add r As Bs) Hn Hzip).
  unfold pot_poly.
  rewrite (zip_scale_eval w r As Bs tau Hla Hlb).
  pose proof (wires_nn_lincomb_nonneg tau w As HAs) as HA.
  pose proof (wires_nn_lincomb_nonneg tau w Bs HBs) as HB.
  rewrite <- powm_mul_r by nia.
  rewrite (Z.mul_comm (poly_eval (poly_lincomb w Bs) tau) r).
  rewrite <- powm_add_r by nia.
  reflexivity.
Qed.


