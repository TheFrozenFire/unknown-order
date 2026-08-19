From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import PowersOfTau.

Open Scope Z_scope.

(** * Public check of a [τ]-update, equal-DL algebra

    A contributor with [ρ] replaces [P_i] by [P_i^{ρ^i}], producing
    the string for [τρ].  Consecutive new elements step by the
    *same* [ρ], and that [ρ] is the discrete log of the new [P'_1]
    base the old [P_1].  Equal-DL completeness is the pairing-free
    check of that.  Extraction of [ρ] from two transcripts is
    [eqdl_extracts_tau].  Simulation stays [pot_hvzk_eqdl_named].

    Cross-confirmed by [cas/85_pot_check.gp]. *)

Theorem contribute_slot_one_is_rho_power :
  forall N g tau rho,
    1 < N ->
    0 <= tau ->
    0 <= rho ->
    pot_contribute N (pot N g tau 1) rho 1 = powm (pot N g tau 1) rho N.
Proof.
  intros N g tau rho Hn Ht Hr.
  unfold pot_contribute, pot.
  rewrite !Z.pow_1_r.
  reflexivity.
Qed.

Theorem update_first_is_old_first_to_rho :
  forall N g tau rho,
    1 < N ->
    0 <= tau ->
    0 <= rho ->
    pot N g (tau * rho) 1 = powm (pot N g tau 1) rho N.
Proof.
  intros N g tau rho Hn Ht Hr.
  rewrite <- (pot_contribute_multiplies_tau N g tau rho 1 Hn Ht Hr ltac:(lia)).
  apply contribute_slot_one_is_rho_power; assumption.
Qed.

(** A Chaum–Pedersen transcript on [(P_1, P'_1)] is a proof of
    knowledge of the contribution [ρ].  Two transcripts extract
    [ρ] modulo [ord(P_1)]. *)
Theorem update_pok_complete :
  forall N g tau rho w c,
    1 < N ->
    0 <= tau ->
    0 <= rho ->
    0 <= w ->
    0 <= c ->
    let P1 := pot N g tau 1 in
    let P'1 := pot N g (tau * rho) 1 in
    eqdl_verify N P1 P'1 P1 P'1
      (fst (eqdl_commit N P1 P1 w))
      (snd (eqdl_commit N P1 P1 w))
      c (eqdl_response w c rho).
Proof.
  intros N g tau rho w c Hn Ht Hr Hw Hc P1 P'1.
  subst P1 P'1.
  pose proof (eqdl_complete N (pot N g tau 1) (pot N g tau 1)
                rho w c Hn Hr Hw Hc) as H.
  cbv zeta in H.
  rewrite <- update_first_is_old_first_to_rho in H by assumption.
  exact H.
Qed.

Theorem extracted_contributor_agrees :
  forall N g tau rho t1 c c' z z' ord,
    1 < N ->
    0 <= tau ->
    0 <= rho ->
    0 <= c' ->
    c' < c ->
    0 <= z' ->
    z' <= z ->
    Z.coprime (pot N g tau 1) N ->
    is_order N (pot N g tau 1) ord ->
    powm (pot N g tau 1) z N =
      (t1 * powm (powm (pot N g tau 1) rho N) c N) mod N ->
    powm (pot N g tau 1) z' N =
      (t1 * powm (powm (pot N g tau 1) rho N) c' N) mod N ->
    (ord | (z - z') - rho * (c - c')).
Proof.
  intros N g tau rho t1 c c' z z' ord Hn Ht Hr Hc' Hcc Hz' Hzle Hcop Hord Hv Hv'.
  apply (eqdl_extracts_tau N (pot N g tau 1) rho t1 c c' z z' ord);
    assumption.
Qed.
