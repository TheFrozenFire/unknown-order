From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import MultiPrime.
Require Import TwoPrimary.

Open Scope Z_scope.

(** * Shared-modulus DKG algebra (Boneh–Franklin shape)

    Parties hold additive shares of candidate primes and publish
    [N = (∑ pᵢ)(∑ qᵢ)].  The product identity is public.  Publishing
    [p+q] as well *is* factoring ([sum_from_phi] / [FactorEnum]).
    The Boneh–Franklin *protocol* (OT, proofs of knowledge) is
    [Refuse_DKG_MPC].

    Biprimality as algebra: two odd primes give four [√1]; three
    give eight.  A mixed triple-root is a witness that [N] is not
    an RSA modulus.

    Cross-confirmed by [cas/68_shared_modulus.gp]. *)

Definition dkg_N (p1 p2 q1 q2 : Z) : Z :=
  (p1 + p2) * (q1 + q2).

Theorem dkg_N_is_product :
  forall p1 p2 q1 q2,
    dkg_N p1 p2 q1 q2 = (p1 + p2) * (q1 + q2).
Proof. intros. reflexivity. Qed.

Theorem dkg_N_cross_terms :
  forall p1 p2 q1 q2,
    dkg_N p1 p2 q1 q2 =
      p1 * q1 + p1 * q2 + p2 * q1 + p2 * q2.
Proof. intros. unfold dkg_N. ring. Qed.

Theorem published_sum_is_phi_plus_one :
  forall p q,
    (p * q) - (p + q) + 1 = (p - 1) * (q - 1).
Proof. intros. ring. Qed.

Theorem two_prime_four_roots_triprime_eight :
  forall p q r,
    three_prime p q r ->
    q <> 2 ->
    let N2 := p * q in
    let N3 := p * q * r in
    powm 1 2 N2 = 1 /\
    powm (p * q - 1) 2 N2 = 1 /\
    powm (sqrt1_pm p q) 2 N2 = 1 /\
    powm (sqrt1_mp p q) 2 N2 = 1 /\
    powm (mixed_pqr p q r) 2 N3 = 1.
Proof.
  intros p q r H3 Hq2 N2 N3.
  destruct H3 as [Hp [Hq [Hr [Hpq [Hpr Hqr]]]]].
  pose proof (four_sqrt1 p q Hp Hq Hpq) as H4.
  cbn in H4. destruct H4 as [Hpp [Hmm [Hpm Hmp]]].
  split; [| split; [| split; [| split]]].
  - exact Hpp.
  - exact Hmm.
  - exact Hpm.
  - exact Hmp.
  - apply eight_sqrt1_squares.
    unfold three_prime. tauto.
Qed.

Theorem triprime_mixed_root_refutes_biprime :
  forall p q r,
    three_prime p q r ->
    q <> 2 ->
    let N := p * q * r in
    let x := mixed_pqr p q r in
    let g := Z.gcd (x - 1) N in
    1 < g /\ g < N /\ (g | N).
Proof.
  intros p q r H3 Hq2 N x g.
  pose proof (mixed_pqr_splits p q r H3 Hq2) as H.
  cbn in H. destruct H as [_ Hg].
  unfold N, x, g, mixed_pqr, eight_sqrt1, sign_residue in *.
  cbn in Hg. exact Hg.
Qed.
