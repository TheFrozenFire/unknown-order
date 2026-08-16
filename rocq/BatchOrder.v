From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import PollardP1.
Require Import SharedPrime.

Open Scope Z_scope.

(** * Type D without a shared prime: a common one-sided annihilator

    Batch GCD requires [gcd(N₁, N₂) > 1].  Two moduli can still share
    an annihilator when the primes are all distinct: if [p−1] and
    [p'−1] are both [B]-smooth, the *same* public [M = lcm(1..B)]
    splits both.  Euclid on the moduli returns 1.

    A shared prime factor [r | gcd(p−1, p'−1)] that is itself large
    is a different handle: [p ≡ 1 (mod r)] is a public AP once [r]
    is known (Type A), and is invisible to batch GCD.

    Cross-confirmed by [cas/15_batch_order.gp]. *)

Definition shares_pminus1_prime (p p' r : Z) : Prop :=
  Z.prime r /\ (r | p - 1) /\ (r | p' - 1).

Lemma shared_pminus1_divides_gcd :
  forall p p' r,
    shares_pminus1_prime p p' r ->
    (r | Z.gcd (p - 1) (p' - 1)).
Proof.
  intros p p' r [_ [Hp Hp']].
  apply Z.gcd_greatest; assumption.
Qed.

Lemma gcd_pminus1_pos :
  forall p p', 2 <= p -> 2 <= p' -> 0 < Z.gcd (p - 1) (p' - 1).
Proof.
  intros p p' Hp Hp'.
  pose proof (Z.gcd_nonneg (p - 1) (p' - 1)).
  pose proof (Z.gcd_eq_0 (p - 1) (p' - 1)). lia.
Qed.

(** Four distinct primes ⇒ the two products are coprime.
    This is the "batch GCD sees nothing" half. *)
Theorem distinct_semiprimes_coprime :
  forall p q p' q',
    Z.prime p -> Z.prime q -> Z.prime p' -> Z.prime q' ->
    p <> q -> p <> p' -> p <> q' ->
    q <> p' -> q <> q' -> p' <> q' ->
    Z.gcd (p * q) (p' * q') = 1.
Proof.
  intros p q p' q' Hp Hq Hp' Hq' Hpq Hpp Hpq' Hqp Hqq Hppq.
  change (Z.coprime (p * q) (p' * q')).
  rewrite coprime_comm.
  apply coprime_mul_iff. split.
  - rewrite coprime_comm. apply coprime_mul_iff. split;
      apply prime_coprime_distinct; assumption.
  - rewrite coprime_comm. apply coprime_mul_iff. split;
      apply prime_coprime_distinct; assumption.
Qed.

(** The same public [M] splits two moduli that share no prime. *)
Theorem batch_p1_splits_pair :
  forall p q p' q' a M,
    Z.prime p -> Z.prime q -> Z.prime p' -> Z.prime q' ->
    p <> q -> p <> p' -> p <> q' ->
    q <> p' -> q <> q' -> p' <> q' ->
    Z.coprime a (p * q) ->
    Z.coprime a (p' * q') ->
    annihilates_p p M ->
    annihilates_p p' M ->
    powm a M q <> 1 ->
    powm a M q' <> 1 ->
    Z.gcd (a ^ M - 1) (p * q) = p /\
    Z.gcd (a ^ M - 1) (p' * q') = p' /\
    Z.gcd (p * q) (p' * q') = 1.
Proof.
  intros p q p' q' a M
         Hp Hq Hp' Hq' Hpq Hpp Hpq' Hqp Hqq Hppq
         Ha Ha' Hann Hann' Hnq Hnq'.
  split; [| split].
  - apply pollard_p1_splits; assumption.
  - apply pollard_p1_splits; assumption.
  - apply distinct_semiprimes_coprime; assumption.
Qed.

(** A large shared factor of [p−1] and [p'−1] puts both primes on
    the public AP [X ≡ 1 (mod r)] once [r] is known.  That is a
    Type-A geometry, not a Type-D gcd. *)
Lemma shared_pminus1_is_ap :
  forall p r,
    (r | p - 1) ->
    exists k, p = k * r + 1.
Proof.
  intros p r [k Hk].
  exists k. lia.
Qed.
