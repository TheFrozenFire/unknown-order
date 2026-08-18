From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * Safe / strong primes: generation-side refusal of one-sided annihilators

    A safe prime [p = 2r+1] with [r] prime makes [p−1 = 2r].  The only
    way [p−1] is [B]-smooth is [r ≤ B].  A strong prime asks the same
    of [p+1] (Williams) and of [(p−1)/2].  Cross-confirmed by
    [cas/10_pollard_p1.gp] (safe prime resists a [B]-smooth [M]). *)

Definition safe_prime (p : Z) : Prop :=
  Z.prime p /\ Z.prime ((p - 1) / 2).

Definition has_large_prime_factor (n B : Z) : Prop :=
  exists r, Z.prime r /\ (r | n) /\ B < r.

Definition p1_resistant (p B : Z) : Prop :=
  has_large_prime_factor (p - 1) B.

Definition pp1_resistant (p B : Z) : Prop :=
  has_large_prime_factor (p + 1) B.

Definition strong_prime (p B : Z) : Prop :=
  Z.prime p /\ p1_resistant p B /\ pp1_resistant p B.

Lemma two_not_safe : ~ safe_prime 2.
Proof.
  intros [Hp Hr].
  change ((2 - 1) / 2) with 0 in Hr.
  exact (Z.not_prime_0 Hr).
Qed.

Lemma safe_prime_pminus1 :
  forall p, safe_prime p -> p - 1 = 2 * ((p - 1) / 2).
Proof.
  intros p [Hp Hr].
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 ((p - 1) / 2) Hr).
  assert (Z.Even (p - 1)) as Heven.
  { destruct (Z.eq_dec p 2) as [Heq | Hne].
    - subst p. exact (False_ind _ (two_not_safe (conj Hp Hr))).
    - destruct (Z.even p) eqn:Hev.
      + apply Z.even_spec in Hev. destruct Hev as [k Hk].
        assert (2 | p) as H2p by (exists k; lia).
        apply Z.divide_prime_prime in H2p;
          [lia | exact Z.prime_2 | exact Hp].
      + assert (Z.odd p = true) as Hodd
          by (rewrite <- Z.negb_even, Hev; reflexivity).
        apply Z.odd_spec in Hodd. destruct Hodd as [k Hk].
        exists k. lia. }
  destruct Heven as [k Hk].
  rewrite Hk. rewrite Z.mul_comm, Z.div_mul by lia. ring.
Qed.

Theorem safe_prime_resists_p1 :
  forall p B,
    safe_prime p ->
    (p - 1) / 2 > B ->
    p1_resistant p B.
Proof.
  intros p B Hsafe HB.
  unfold p1_resistant, has_large_prime_factor.
  exists ((p - 1) / 2).
  destruct Hsafe as [Hp Hr].
  split; [exact Hr|]. split; [| lia].
  exists 2. exact (safe_prime_pminus1 p (conj Hp Hr)).
Qed.

(** A large prime factor is exactly the negation of [B]-smoothness
    (every prime factor [≤ B]).  Stated here without importing
    [PollardP1], so the generation predicate does not depend on the
    attack file. *)
Theorem large_factor_blocks_smooth_claim :
  forall n B r,
    Z.prime r -> (r | n) -> B < r ->
    ~ (forall s, Z.prime s -> (s | n) -> s <= B).
Proof.
  intros n B r Hr Hdiv HB Hall.
  specialize (Hall r Hr Hdiv). lia.
Qed.

Theorem safe_prime_blocks_smooth_claim :
  forall p B,
    safe_prime p ->
    (p - 1) / 2 > B ->
    ~ (forall s, Z.prime s -> (s | p - 1) -> s <= B).
Proof.
  intros p B Hsafe HB.
  destruct (safe_prime_resists_p1 p B Hsafe HB) as [r [Hr [Hdiv Hgt]]].
  eapply large_factor_blocks_smooth_claim; eassumption.
Qed.

Theorem strong_prime_resists_both :
  forall p B, strong_prime p B -> p1_resistant p B /\ pp1_resistant p B.
Proof. intros p B [_ H]. exact H. Qed.

(** Williams [p+1] is the Lucas-sequence analogue: a cheap public [M]
    with [p+1 | M] annihilates a rank-2 recurrence modulo [p]
    ([Lucas.v], [Torus.v]).  The generation-side refusal is
    [pp1_resistant] — the same shape as [p1_resistant], other side. *)
Definition williams_handle (p M : Z) : Prop :=
  0 <= M /\ (p + 1 | M).

Lemma prime_5 : Z.prime 5.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
  intuition subst; reflexivity.
Qed.

Theorem five_is_safe : safe_prime 5.
Proof.
  split; [exact prime_5|].
  change ((5 - 1) / 2) with 2. exact Z.prime_2.
Qed.

Theorem five_resists_B1 : p1_resistant 5 1.
Proof.
  apply (safe_prime_resists_p1 5 1).
  - exact five_is_safe.
  - vm_compute. reflexivity.
Qed.


