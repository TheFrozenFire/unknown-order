From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import Hardness.
Require Import TwoPrimary.
Require Import Presentation.
Require Import Accumulator.

Open Scope Z_scope.

(** * Guillou–Quisquater: PoK of an [e]-th root

    Completeness and two-transcript special soundness.  Extraction
    is Shamir: [gcd(c−c', e)=1] yields an [e]-th root of [z].
    Simulation is [Refuse_HVZK_simulation] / [Refuse_ROM].

    Publishing a mixed [√1] is a proof of factorization that is
    *not* zero-knowledge ([mixed_sqrt1_splits]). *)

Definition gq_commit (k e N : Z) : Z := powm k e N.

Definition gq_response (k x c N : Z) : Z :=
  (k * powm x c N) mod N.

Definition gq_verify (z e t c r N : Z) : Prop :=
  powm r e N = (t * powm z c N) mod N.

Theorem gq_complete :
  forall N e x z k c,
    1 < N ->
    0 <= e ->
    0 <= c ->
    0 <= k ->
    0 <= x ->
    powm x e N = z ->
    gq_verify z e (gq_commit k e N) c (gq_response k x c N) N.
Proof.
  intros N e x z k c Hn He Hc Hk Hx Hz.
  unfold gq_verify, gq_commit, gq_response.
  rewrite powm_mod_base by lia.
  rewrite powm_mul_l_mod by lia.
  rewrite <- powm_mul_r by lia.
  rewrite (Z.mul_comm c e), powm_mul_r by lia.
  rewrite Hz.
  unfold powm. rewrite Z.mul_mod by lia. reflexivity.
Qed.

Lemma gq_ratio_is_delta_power :
  forall N e z t c c' r r' rinv,
    1 < N ->
    0 <= e ->
    0 <= c' ->
    c' < c ->
    (r' * rinv) mod N = 1 ->
    gq_verify z e t c r N ->
    gq_verify z e t c' r' N ->
    powm ((r * rinv) mod N) e N = powm z (c - c') N.
Proof.
  intros N e z t c c' r r' rinv Hn He Hc' Hcc Hrinv Hv Hv'.
  unfold gq_verify in Hv, Hv'.
  rewrite powm_mod_base by lia.
  rewrite powm_mul_l_mod by lia.
  pose proof (powm_inv_cancels r' rinv e N Hn He Hrinv) as Hinvp.
  destruct (inverse_is_coprime (powm r' e N) (powm rinv e N) N Hn Hinvp)
    as [Hu _].
  assert (powm z (c - c') N = powm z (c - c') N mod N) as Hred.
  { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
  rewrite Hred.
  apply (mul_cancel_r_coprime (powm r e N * powm rinv e N)
           (powm z (c - c') N) (powm r' e N) N Hn Hu).
  rewrite <- Z.mul_assoc.
  rewrite (Z.mul_comm (powm rinv e N)).
  rewrite <- Z.mul_mod_idemp_r by lia.
  rewrite Hinvp, Z.mul_1_r.
  rewrite Hv.
  rewrite Z.mod_mod by lia.
  rewrite Hv'.
  rewrite Z.mul_mod_idemp_r by lia.
  rewrite (Z.mul_comm (powm z (c - c') N)).
  rewrite <- Z.mul_assoc.
  rewrite <- (Z.mul_mod_idemp_r t (powm z c' N * powm z (c - c') N) N)
    by lia.
  rewrite <- powm_add_r by lia.
  replace (c' + (c - c')) with c by lia.
  reflexivity.
Qed.

Theorem gq_extract :
  forall N e z t c c' r r',
    1 < N ->
    0 < e ->
    0 <= c' ->
    c' < c ->
    Z.coprime r N ->
    Z.coprime r' N ->
    Z.coprime z N ->
    Z.gcd (c - c') e = 1 ->
    gq_verify z e t c r N ->
    gq_verify z e t c' r' N ->
    exists w, powm w e N = z mod N.
Proof.
  intros N e z t c c' r r' Hn He Hc' Hcc Hr Hr' Hz Hgcd Hv Hv'.
  unfold Z.coprime in Hr'.
  destruct (unit_inverse_exists r' N Hn Hr') as [rinv Hrinv].
  set (v := (r * rinv) mod N).
  rewrite Z.gcd_comm in Hgcd.
  apply (shamir_trick N e (c - c') v z);
    try (assumption || lia).
  - unfold v.
    destruct (inverse_is_coprime r' rinv N Hn Hrinv) as [_ Hinvc].
    apply coprime_mod_n; [lia|].
    apply Z.coprime_mul_l; [exact Hr | exact Hinvc].
  - unfold v.
    apply (gq_ratio_is_delta_power N e z t c c' r r' rinv);
      try (assumption || lia).
Qed.

(** Sending a mixed [√1] proves factorization and reveals a factor.
    That is knowledge, not zero-knowledge. *)
Theorem publishing_mixed_sqrt1_factors :
  forall p q,
    Z.prime p -> Z.prime q -> p <> q -> p <> 2 -> q <> 2 ->
    let N := p * q in
    let mu := sqrt1_pm p q in
    powm mu 2 N = 1 /\
    let g := Z.gcd (mu - 1) N in
    1 < g < N /\ (g | N).
Proof.
  intros p q Hp Hq Hneq Hp2 Hq2 N mu.
  subst N mu.
  pose proof (four_sqrt1 p q Hp Hq Hneq) as [_ [_ [Hsq _]]].
  split; [exact Hsq|].
  pose proof (mixed_sqrt1_splits p q Hp Hq Hneq Hp2 Hq2) as H.
  cbn in H. destruct H as [H1 [H2 H3]].
  split; [lia|exact H3].
Qed.

Theorem gq_on_one_with_mixed_sqrt_is_factorization :
  forall p q,
    Z.prime p -> Z.prime q -> p <> q -> p <> 2 -> q <> 2 ->
    let N := p * q in
    let x := sqrt1_pm p q in
    powm x 2 N = 1 /\
    exists g, 1 < g < N /\ (g | N).
Proof.
  intros p q Hp Hq Hneq Hp2 Hq2 N x.
  pose proof (publishing_mixed_sqrt1_factors p q Hp Hq Hneq Hp2 Hq2) as H.
  cbn in H. destruct H as [Hsq [Hg Hdiv]].
  subst N x. split; [exact Hsq|].
  exists (Z.gcd (sqrt1_pm p q - 1) (p * q)).
  split; [lia|exact Hdiv].
Qed.
