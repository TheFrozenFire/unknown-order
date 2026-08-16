From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import Miller.

Open Scope Z_scope.

(** * Miller–Rabin polarity

    The same successive-squaring engine underlies the Miller–Rabin
    primality test and Miller-from-[d] factoring.  They differ only in
    the exponent they feed the engine:

    - Primality: exponent [n−1].  Misbehaviour proves compositeness
      (and sometimes supplies a factor).
    - Factoring from [d]: exponent [M = ed−1], a known annihilator of
      [(Z/NZ)*].  A non-trivial square root of 1 splits [N].

    Miller 1976 already notes the factoring direction; RSA 1978 cites it.
    Cross-confirmed by [cas/07_miller_rabin.gp]. *)

Definition mr_s (n : Z) : nat := val2 (n - 1).
Definition mr_t (n : Z) : Z := odd_part (n - 1).

Lemma mr_split :
  forall n, 1 < n -> n - 1 = 2 ^ Z.of_nat (mr_s n) * mr_t n.
Proof.
  intros n Hn. unfold mr_s, mr_t. apply split2_of_reconstructs. lia.
Qed.

(** A base [a] is a *Miller–Rabin witness of compositeness* for [n]
    when the sequence starting at [a^t] never hits [−1] immediately
    before [1], and is not already [1]. *)
Definition mr_strong_liar (a n : Z) : Prop :=
  powm a (n - 1) n = 1 /\
  (powm a (mr_t n) n = 1 \/
   exists i, (i < mr_s n)%nat /\
             powm a (2 ^ Z.of_nat i * mr_t n) n = n - 1).

Definition mr_composite_witness (a n : Z) : Prop :=
  1 < a < n /\ Z.coprime a n /\ ~ mr_strong_liar a n.

(** Polarity: the Miller factoring sequence on [M] is the Miller–Rabin
    sequence on a number whose [n−1] equals [M]. *)
Lemma miller_mr_same_engine :
  forall R,
    miller_t R = mr_t (miller_M R + 1) /\
    miller_s R = mr_s (miller_M R + 1).
Proof.
  intros R. unfold miller_t, miller_s, mr_t, mr_s, miller_M.
  replace (rsa_e R * rsa_d R - 1 + 1) with (rsa_e R * rsa_d R) by ring.
  replace (rsa_e R * rsa_d R - 1) with (rsa_e R * rsa_d R - 1) by reflexivity.
  (* mr_* looks at (M+1)−1 = M, so the splits coincide. *)
  unfold miller_M. split; reflexivity.
Qed.

(** If a Miller–Rabin sequence on a composite [N = pq] produces a
    non-trivial square root of 1, it factors [N] — the "free factor"
    mentioned in the seed conversation. *)
Theorem mr_nontrivial_sqrt_factors :
  forall R g,
    powm g 2 (rsa_N R) = 1 ->
    g mod rsa_N R <> 1 ->
    g mod rsa_N R <> rsa_N R - 1 ->
    let f := Z.gcd (g - 1) (rsa_N R) in
    1 < f /\ f < rsa_N R /\ (f | rsa_N R).
Proof.
  intros R g Hsq Hn1 Hnm1.
  unfold rsa_N.
  apply nontrivial_sqrt1_splits.
  - apply rsa_p_prime.
  - apply rsa_q_prime.
  - apply rsa_distinct.
  - exact Hsq.
  - exact Hn1.
  - exact Hnm1.
Qed.

(** On a prime, Fermat forces [a^{p−1} ≡ 1], so the MR sequence always
    reaches 1.  This is the "must behave" side of the polarity. *)
Theorem mr_fermat_on_prime :
  forall p a,
    Z.prime p -> Z.coprime a p ->
    powm a (p - 1) p = 1.
Proof. intros. apply fermat_coprime; assumption. Qed.
