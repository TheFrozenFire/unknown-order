From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import PowersOfTau.
Require Import PotCheck.

Open Scope Z_scope.

(** * Equal-DL ladder: extra CRS powers are a proven [ρ^i]-update

    Slot 1 is [P'_1 = P_1^ρ] ([update_first_is_old_first_to_rho]).
    Slot [i] asks for exponent [ρ^i].  Publish the intermediates
    [A_{k+1} = A_k^ρ] on base [P_i], each step an equal-DL of the
    *same* [ρ] against [(P_1, P'_1)].  After [i] steps
    [A_i = P_i^{ρ^i} = P'_i], so the new string is [g^{(τρ)^i}].

    Slot 2 is two steps and one auxiliary [A = P_2^ρ].
    Simulation stays [pot_hvzk_eqdl_named].

    Cross-confirmed by [cas/94_pot_ladder.gp]. *)

Fixpoint rho_ladder (N P rho : Z) (k : nat) : Z :=
  match k with
  | O => P
  | S k' => powm (rho_ladder N P rho k') rho N
  end.

Lemma rho_ladder_0 :
  forall N P rho, rho_ladder N P rho 0%nat = P.
Proof. reflexivity. Qed.

Lemma rho_ladder_succ :
  forall N P rho k,
    rho_ladder N P rho (S k) = powm (rho_ladder N P rho k) rho N.
Proof. reflexivity. Qed.

Theorem rho_ladder_succ_is_power :
  forall N P rho k,
    1 < N ->
    0 <= rho ->
    rho_ladder N P rho (S k) = powm P (rho ^ Z.of_nat (S k)) N.
Proof.
  intros N P rho k Hn Hr.
  induction k as [|k IH].
  - simpl. change (Z.pow_pos rho 1) with (rho ^ 1).
    rewrite Z.pow_1_r. reflexivity.
  - rewrite rho_ladder_succ.
    rewrite IH.
    rewrite <- powm_mul_r by (try apply Z.pow_nonneg; lia).
    rewrite Nat2Z.inj_succ with (n := S k).
    rewrite Z.pow_succ_r by lia.
    rewrite (Z.mul_comm (rho ^ Z.of_nat (S k)) rho).
    reflexivity.
Qed.

Theorem ladder_realizes_update :
  forall N g tau rho i,
    1 < N ->
    0 <= tau ->
    0 <= rho ->
    rho_ladder N (pot N g tau (Z.of_nat i)) rho i =
      pot N g (tau * rho) (Z.of_nat i).
Proof.
  intros N g tau rho i Hn Ht Hr.
  destruct i as [|i].
  - simpl. rewrite !pot_at_zero by lia. reflexivity.
  - rewrite rho_ladder_succ_is_power by assumption.
    rewrite <- (pot_contribute_multiplies_tau N g tau rho (Z.of_nat (S i))
                 Hn Ht Hr ltac:(apply Nat2Z.is_nonneg)).
    unfold pot_contribute. reflexivity.
Qed.

Theorem contribution_ladder_step :
  forall N g tau rho i k w c,
    1 < N ->
    0 <= tau ->
    0 <= rho ->
    0 <= w ->
    0 <= c ->
    let P1 := pot N g tau 1 in
    let Pp1 := pot N g (tau * rho) 1 in
    let Pi := pot N g tau (Z.of_nat i) in
    eqdl_verify N P1 Pp1
      (rho_ladder N Pi rho k)
      (rho_ladder N Pi rho (S k))
      (fst (eqdl_commit N P1 (rho_ladder N Pi rho k) w))
      (snd (eqdl_commit N P1 (rho_ladder N Pi rho k) w))
      c (eqdl_response w c rho).
Proof.
  intros N g tau rho i k w c Hn Ht Hr Hw Hc P1 Pp1 Pi.
  subst P1 Pp1 Pi.
  pose proof (eqdl_complete N (pot N g tau 1)
                (rho_ladder N (pot N g tau (Z.of_nat i)) rho k)
                rho w c Hn Hr Hw Hc) as H.
  cbv zeta in H.
  rewrite <- update_first_is_old_first_to_rho in H by assumption.
  unfold eqdl_verify in H.
  rewrite <- rho_ladder_succ in H.
  exact H.
Qed.

(** ** Slot 2 is two ladder steps *)

Definition slot2_aux (N g tau rho : Z) : Z :=
  powm (pot N g tau 2) rho N.

Theorem slot2_aux_is_ladder_one :
  forall N g tau rho,
    slot2_aux N g tau rho =
      rho_ladder N (pot N g tau 2) rho 1%nat.
Proof.
  intros. unfold slot2_aux. simpl. reflexivity.
Qed.

Theorem slot2_new_is_rho_sq :
  forall N g tau rho,
    1 < N ->
    0 <= tau ->
    0 <= rho ->
    pot N g (tau * rho) 2 = powm (pot N g tau 2) (rho ^ 2) N.
Proof.
  intros N g tau rho Hn Ht Hr.
  rewrite <- (pot_contribute_multiplies_tau N g tau rho 2 Hn Ht Hr ltac:(lia)).
  unfold pot_contribute. reflexivity.
Qed.

Theorem slot2_aux_then_rho :
  forall N g tau rho,
    1 < N ->
    0 <= tau ->
    0 <= rho ->
    powm (slot2_aux N g tau rho) rho N = pot N g (tau * rho) 2.
Proof.
  intros N g tau rho Hn Ht Hr.
  unfold slot2_aux.
  rewrite <- powm_mul_r by lia.
  rewrite <- Z.pow_2_r.
  symmetry.
  apply slot2_new_is_rho_sq; assumption.
Qed.

Theorem slot2_new_is_ladder_two :
  forall N g tau rho,
    1 < N ->
    0 <= tau ->
    0 <= rho ->
    rho_ladder N (pot N g tau 2) rho 2%nat = pot N g (tau * rho) 2.
Proof.
  intros N g tau rho Hn Ht Hr.
  apply (ladder_realizes_update N g tau rho 2%nat Hn Ht Hr).
Qed.

Theorem slot2_leg1_complete :
  forall N g tau rho w c,
    1 < N ->
    0 <= tau ->
    0 <= rho ->
    0 <= w ->
    0 <= c ->
    let P1 := pot N g tau 1 in
    let Pp1 := pot N g (tau * rho) 1 in
    let P2 := pot N g tau 2 in
    let A := slot2_aux N g tau rho in
    eqdl_verify N P1 Pp1 P2 A
      (fst (eqdl_commit N P1 P2 w))
      (snd (eqdl_commit N P1 P2 w))
      c (eqdl_response w c rho).
Proof.
  intros N g tau rho w c Hn Ht Hr Hw Hc P1 Pp1 P2 A.
  subst P1 Pp1 P2 A.
  pose proof (contribution_ladder_step N g tau rho 2%nat 0%nat w c
                Hn Ht Hr Hw Hc) as H.
  cbv zeta in H.
  unfold slot2_aux in *.
  simpl in H.
  change (Z.of_nat 2) with 2 in H.
  exact H.
Qed.

Theorem slot2_leg2_complete :
  forall N g tau rho w c,
    1 < N ->
    0 <= tau ->
    0 <= rho ->
    0 <= w ->
    0 <= c ->
    let P1 := pot N g tau 1 in
    let Pp1 := pot N g (tau * rho) 1 in
    let A := slot2_aux N g tau rho in
    let Pp2 := pot N g (tau * rho) 2 in
    eqdl_verify N P1 Pp1 A Pp2
      (fst (eqdl_commit N P1 A w))
      (snd (eqdl_commit N P1 A w))
      c (eqdl_response w c rho).
Proof.
  intros N g tau rho w c Hn Ht Hr Hw Hc P1 Pp1 A Pp2.
  subst P1 Pp1 A Pp2.
  pose proof (contribution_ladder_step N g tau rho 2%nat 1%nat w c
                Hn Ht Hr Hw Hc) as H.
  cbv zeta in H.
  unfold slot2_aux in *.
  simpl in H.
  change (Z.of_nat 2) with 2 in H.
  replace (powm (powm (pot N g tau 2) rho N) rho N)
    with (pot N g (tau * rho) 2) in H
    by (rewrite <- slot2_aux_then_rho by assumption; unfold slot2_aux; reflexivity).
  exact H.
Qed.
