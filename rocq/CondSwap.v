From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import Mux.
Require Import BitLogic.

Open Scope Z_scope.

(** * Conditional swap: on bit [s], swap [a] and [b] or not

    [a' = mux s b a], [b' = mux s a b].  If [s=0] then
    [(a,b)]; if [s=1] then [(b,a)].

    Cross-confirmed by [cas/110_cond_swap.gp]. *)

Definition cswap_a (s a b : Z) : Z := mux s b a.

Definition cswap_b (s a b : Z) : Z := mux s a b.

Theorem cswap_off :
  forall a b,
    cswap_a 0 a b = a /\ cswap_b 0 a b = b.
Proof.
  intros. unfold cswap_a, cswap_b.
  rewrite mux_on_zero, mux_on_zero. split; reflexivity.
Qed.

Theorem cswap_on :
  forall a b,
    cswap_a 1 a b = b /\ cswap_b 1 a b = a.
Proof.
  intros. unfold cswap_a, cswap_b.
  rewrite mux_on_one, mux_on_one. split; reflexivity.
Qed.

Theorem cswap_select :
  forall s a b,
    is_bit s ->
    (s = 0 /\ cswap_a s a b = a /\ cswap_b s a b = b) \/
    (s = 1 /\ cswap_a s a b = b /\ cswap_b s a b = a).
Proof.
  intros s a b Hs. unfold is_bit in Hs.
  destruct Hs as [H0 | H1]; subst.
  - left. split; [reflexivity|]. apply cswap_off.
  - right. split; [reflexivity|]. apply cswap_on.
Qed.

Theorem cswap_involution :
  forall s a b,
    is_bit s ->
    cswap_a s (cswap_a s a b) (cswap_b s a b) = a /\
    cswap_b s (cswap_a s a b) (cswap_b s a b) = b.
Proof.
  intros s a b Hs. unfold is_bit in Hs.
  destruct Hs; subst; unfold cswap_a, cswap_b;
    rewrite !mux_on_zero || rewrite !mux_on_one;
    split; reflexivity.
Qed.
