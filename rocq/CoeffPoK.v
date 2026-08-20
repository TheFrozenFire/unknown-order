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

Open Scope Z_scope.

(** * Knowledge of coefficients of a committed evaluation

    [C = g^{f(τ)} = ∏ P_i^{a_i}].  A Schnorr transcript on a
    *single* base [P_i] extracts that slot's [a_i]
    ([coeff_slot_extracts]).  Assembling the slots recovers the
    encoding ([slots_assemble]).  Extraction is modulo [ord(P_i)],
    the same algebra as [eqdl_extracts_tau].

    Cross-confirmed by [cas/97_coeff_pok.gp]. *)

Definition coeff_slot (N g tau : Z) (i a : Z) : Z :=
  powm (pot N g tau i) a N.

Fixpoint coeff_slots (N g tau : Z) (cs : list Z) (i : nat) : list Z :=
  match cs with
  | nil => nil
  | a :: rest =>
      coeff_slot N g tau (Z.of_nat i) a :: coeff_slots N g tau rest (S i)
  end.

Fixpoint gprod (N : Z) (qs : list Z) : Z :=
  match qs with
  | nil => 1 mod N
  | q :: rest => (q * gprod N rest) mod N
  end.

Lemma coeff_slot_eval :
  forall N g tau i a,
    1 < N ->
    0 <= tau ->
    0 <= i ->
    0 <= a ->
    coeff_slot N g tau i a = powm g (a * (tau ^ i)) N.
Proof.
  intros N g tau i a Hn Ht Hi Ha.
  unfold coeff_slot, pot.
  rewrite <- powm_mul_r by (try apply Z.pow_nonneg; lia).
  rewrite (Z.mul_comm (tau ^ i)).
  reflexivity.
Qed.

Lemma slots_from_i :
  forall N g tau cs i,
    1 < N ->
    0 <= tau ->
    nn cs ->
    gprod N (coeff_slots N g tau cs i) =
      powm g (poly_eval cs tau * (tau ^ Z.of_nat i)) N.
Proof.
  intros N g tau cs i Hn Ht Hnn.
  revert i.
  induction Hnn as [|a rest Ha Hrest IH]; intros i.
  - simpl. unfold poly_eval.
    symmetry. apply powm_0_r. lia.
  - simpl.
    rewrite coeff_slot_eval by (try apply Nat2Z.is_nonneg; lia).
    rewrite (IH (S i)).
    rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by (apply Nat2Z.is_nonneg || lia).
    assert (0 <= poly_eval rest tau) by (apply poly_eval_nonneg; assumption).
    assert (0 <= tau ^ Z.of_nat i) by (apply Z.pow_nonneg; lia).
    assert (0 <= a * (tau ^ Z.of_nat i)) by nia.
    assert (0 <= poly_eval rest tau * (tau * tau ^ Z.of_nat i)) by nia.
    rewrite <- powm_add_r by lia.
    f_equal.
    simpl.
    ring.
Qed.

Theorem slots_assemble :
  forall N g tau cs,
    1 < N ->
    0 <= tau ->
    nn cs ->
    gprod N (coeff_slots N g tau cs 0) = pot_poly N g tau cs.
Proof.
  intros N g tau cs Hn Ht Hnn.
  unfold pot_poly.
  rewrite (slots_from_i N g tau cs 0 Hn Ht Hnn).
  rewrite Z.pow_0_r, Z.mul_1_r.
  reflexivity.
Qed.

Theorem two_coeff_assemble :
  forall N g tau a0 a1,
    1 < N ->
    0 <= tau ->
    0 <= a0 ->
    0 <= a1 ->
    (coeff_slot N g tau 0 a0 * coeff_slot N g tau 1 a1) mod N =
      pot_poly N g tau (a0 :: a1 :: nil).
Proof.
  intros N g tau a0 a1 Hn Ht H0 H1.
  transitivity (gprod N (coeff_slots N g tau (a0 :: a1 :: nil) 0)).
  - simpl.
    rewrite Z.mod_1_l by lia.
    rewrite Z.mul_1_r.
    rewrite Z.mul_mod_idemp_r by lia.
    reflexivity.
  - apply slots_assemble; [exact Hn | exact Ht |].
    constructor; [exact H0 | constructor; [exact H1 | constructor]].
Qed.

Theorem coeff_slot_eqdl :
  forall N g tau i a s c,
    1 < N ->
    0 <= tau ->
    0 <= i ->
    0 <= a ->
    0 <= s ->
    0 <= c ->
    let Pi := pot N g tau i in
    let Qi := coeff_slot N g tau i a in
    eqdl_verify N Pi Qi Pi Qi
      (fst (eqdl_commit N Pi Pi s))
      (snd (eqdl_commit N Pi Pi s))
      c (eqdl_response s c a).
Proof.
  intros N g tau i a s c Hn Ht Hi Ha Hs Hc Pi Qi.
  subst Pi Qi.
  unfold coeff_slot.
  pose proof (eqdl_complete N (pot N g tau i) (pot N g tau i)
                a s c Hn Ha Hs Hc) as H.
  cbv zeta in H.
  exact H.
Qed.

Theorem coeff_slot_extracts :
  forall N g tau i a t1 c c' z z' ord,
    1 < N ->
    0 <= tau ->
    0 <= i ->
    0 <= a ->
    0 <= c' ->
    c' < c ->
    0 <= z' ->
    z' <= z ->
    Z.coprime (pot N g tau i) N ->
    is_order N (pot N g tau i) ord ->
    powm (pot N g tau i) z N =
      (t1 * powm (coeff_slot N g tau i a) c N) mod N ->
    powm (pot N g tau i) z' N =
      (t1 * powm (coeff_slot N g tau i a) c' N) mod N ->
    (ord | (z - z') - a * (c - c')).
Proof.
  intros N g tau i a t1 c c' z z' ord Hn Ht Hi Ha Hc' Hcc Hz' Hzle Hcop Hord Hv Hv'.
  unfold coeff_slot in Hv, Hv'.
  apply (eqdl_extracts_tau N (pot N g tau i) a t1 c c' z z' ord);
    assumption.
Qed.
