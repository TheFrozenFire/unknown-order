From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * Shared primes: [gcd(N₁, N₂)] *is* the common CRT component

    If two moduli share a prime and their other primes differ, Euclid
    names that prime.  No search.  Cross-confirmed by [cas/09_shared_prime.gp]. *)

Theorem gcd_shared_prime :
  forall p q1 q2,
    Z.prime p -> Z.prime q1 -> Z.prime q2 ->
    p <> q1 -> p <> q2 -> q1 <> q2 ->
    Z.gcd (p * q1) (p * q2) = p.
Proof.
  intros p q1 q2 Hp Hq1 Hq2 Hpq1 Hpq2 Hq.
  pose proof (Z.prime_ge_2 p Hp).
  rewrite Z.gcd_mul_mono_l_nonneg by lia.
  assert (Z.gcd q1 q2 = 1).
  { apply Z.coprime_prime_l_iff; [exact Hq1|].
    intro Hdiv. apply Z.divide_prime_prime in Hdiv; [lia | exact Hq1 | exact Hq2]. }
  rewrite H0. lia.
Qed.

Theorem gcd_shared_prime_divides_both :
  forall p q1 q2,
    Z.prime p -> Z.prime q1 -> Z.prime q2 ->
    p <> q1 -> p <> q2 -> q1 <> q2 ->
    let g := Z.gcd (p * q1) (p * q2) in
    (g | p * q1) /\ (g | p * q2) /\ g = p.
Proof.
  intros p q1 q2 Hp Hq1 Hq2 H1 H2 H3 g.
  unfold g. split; [| split].
  - apply Z.gcd_divide_l.
  - apply Z.gcd_divide_r.
  - apply gcd_shared_prime; assumption.
Qed.


