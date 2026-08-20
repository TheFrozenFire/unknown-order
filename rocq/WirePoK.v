From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import Hardness.
Require Import PowersOfTau.
Require Import EvalProduct.
Require Import QAP.
Require Import CoeffPoK.

Open Scope Z_scope.

(** * Knowledge of a QAP witness against a specialized CRS

    [U_j = g^{A_j(τ)}].  Slot [j] is [U_j^{w_j}].  Assembling
    the slots is the wire commit ([wire_slots_assemble]).  Schnorr
    on a single [U_j] extracts [w_j] modulo [ord(U_j)].

    Cross-confirmed by [cas/100_wire_pok.gp]. *)

Definition wire_slot (N g tau : Z) (A : list Z) (w : Z) : Z :=
  powm (pot_poly N g tau A) w N.

Fixpoint wire_slots (N g tau : Z) (ws : list Z) (As : list (list Z))
  : list Z :=
  match ws, As with
  | w :: ws', A :: As' =>
      wire_slot N g tau A w :: wire_slots N g tau ws' As'
  | _, _ => nil
  end.

Theorem wire_slots_assemble :
  forall N g tau ws As,
    1 < N ->
    wires_nn tau ws As ->
    gprod N (wire_slots N g tau ws As) = pot_wires N g tau ws As.
Proof.
  intros N g tau ws As Hn Hnn.
  induction Hnn.
  - simpl. reflexivity.
  - destruct ws; simpl; reflexivity.
  - simpl. rewrite IHHnn. reflexivity.
Qed.

Theorem wire_slot_eqdl :
  forall N g tau A w s c,
    1 < N ->
    0 <= w ->
    0 <= s ->
    0 <= c ->
    let U := pot_poly N g tau A in
    let Q := wire_slot N g tau A w in
    eqdl_verify N U Q U Q
      (fst (eqdl_commit N U U s))
      (snd (eqdl_commit N U U s))
      c (eqdl_response s c w).
Proof.
  intros N g tau A w s c Hn Hw Hs Hc U Q.
  subst U Q.
  unfold wire_slot.
  pose proof (eqdl_complete N (pot_poly N g tau A) (pot_poly N g tau A)
                w s c Hn Hw Hs Hc) as H.
  cbv zeta in H.
  exact H.
Qed.

Theorem wire_slot_extracts :
  forall N g tau A w t1 c c' z z' ord,
    1 < N ->
    0 <= w ->
    0 <= c' ->
    c' < c ->
    0 <= z' ->
    z' <= z ->
    Z.coprime (pot_poly N g tau A) N ->
    is_order N (pot_poly N g tau A) ord ->
    powm (pot_poly N g tau A) z N =
      (t1 * powm (wire_slot N g tau A w) c N) mod N ->
    powm (pot_poly N g tau A) z' N =
      (t1 * powm (wire_slot N g tau A w) c' N) mod N ->
    (ord | (z - z') - w * (c - c')).
Proof.
  intros N g tau A w t1 c c' z z' ord Hn Hw Hc' Hcc Hz' Hzle Hcop Hord Hv Hv'.
  unfold wire_slot in Hv, Hv'.
  apply (eqdl_extracts_tau N (pot_poly N g tau A) w t1 c c' z z' ord);
    assumption.
Qed.

Theorem three_wire_assemble :
  forall N g tau w0 w1 w2 A0 A1 A2,
    1 < N ->
    0 <= w0 ->
    0 <= w1 ->
    0 <= w2 ->
    0 <= poly_eval A0 tau ->
    0 <= poly_eval A1 tau ->
    0 <= poly_eval A2 tau ->
    gprod N (wire_slot N g tau A0 w0
               :: wire_slot N g tau A1 w1
               :: wire_slot N g tau A2 w2 :: nil) =
      pot_wires N g tau (w0 :: w1 :: w2 :: nil)
                (A0 :: A1 :: A2 :: nil).
Proof.
  intros N g tau w0 w1 w2 A0 A1 A2 Hn H0 H1 H2 Ha0 Ha1 Ha2.
  change (wire_slot N g tau A0 w0
            :: wire_slot N g tau A1 w1
            :: wire_slot N g tau A2 w2 :: nil)
    with (wire_slots N g tau (w0 :: w1 :: w2 :: nil) (A0 :: A1 :: A2 :: nil)).
  apply wire_slots_assemble; [exact Hn |].
  constructor; [exact H0 | exact Ha0 |].
  constructor; [exact H1 | exact Ha1 |].
  constructor; [exact H2 | exact Ha2 |].
  constructor.
Qed.
