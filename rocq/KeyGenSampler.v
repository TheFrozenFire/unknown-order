From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import FermatFactor.
Require Import StrongPrimes.
Require Import Wiener.
Require Import PollardP1.
Require Import SharedPrime.
Require Import KeyGen.
Require Import Cyclotomic.
Require Import KeyGenGeom.
Require Import BatchOrder.

Open Scope Z_scope.

(** * Named key-generation distributions, measured against the rulers

    Each [dist_*] is a generation choice that honest-looking code
    actually makes.  The theorems say which ruler it fails.  Concrete
    frequencies live in [cas/13_keygen_sampler.gp]. *)

(** Nextprime-adjacent: [q] is the next prime after [p].  We capture
    the checkable core — they are consecutive in the primes and odd —
    via [adjacent_odd] when [|p−q| = 2], or a bounded gap otherwise. *)
Definition dist_close_pair (p q gap : Z) : Prop :=
  Z.prime p /\ Z.prime q /\ 0 < Z.abs (p - q) <= gap.

Theorem dist_close_pair_fails_far :
  forall p q gap want,
    dist_close_pair p q gap ->
    0 <= want ->
    gap < 2 ^ want ->
    ~ kg_far p q want.
Proof.
  intros p q gap want [_ [_ [_ Hle]]] Hwant Hlt [_ Habs].
  lia.
Qed.

Definition dist_twin_odd (p q : Z) : Prop :=
  Z.prime p /\ Z.prime q /\ adjacent_odd p q.

Theorem dist_twin_odd_fails_far :
  forall p q,
    dist_twin_odd p q ->
    ~ kg_far p q 2.
Proof.
  intros p q [_ [_ Hadj]].
  apply adjacent_fails_far_ge2; [exact Hadj | lia].
Qed.

(** Shared-prefix generation: pick the top half, then two lows. *)
Definition dist_shared_prefix (p q s : Z) : Prop :=
  Z.prime p /\ Z.prime q /\ shared_high_bits p q s.

Theorem dist_shared_prefix_fails_far :
  forall p q s,
    dist_shared_prefix p q s ->
    0 <= s ->
    ~ kg_far p q s.
Proof.
  intros p q s [_ [_ Hsh]] Hs.
  eapply shared_high_bits_fails_far; [exact Hsh | exact Hs |].
  apply Z.le_refl.
Qed.

(** Increment-from-a-common-start with window [W]. *)
Definition dist_increment_window (p q x W : Z) : Prop :=
  Z.prime p /\ Z.prime q /\ increment_window p q x W.

Theorem dist_increment_fails_far :
  forall p q x W gap,
    dist_increment_window p q x W ->
    0 <= gap ->
    W <= 2 ^ gap ->
    ~ kg_far p q gap.
Proof.
  intros p q x W gap [_ [_ Hwin]].
  apply (increment_window_fails_far p q x W gap); assumption.
Qed.

(** Safe [p], arbitrary [q]: refuses Pollard on [p], says nothing
    about [Φ_3(p)] or about [q−1]. *)
Definition dist_safe_p_only (p q : Z) : Prop :=
  safe_prime p /\ Z.prime q /\ p <> q.

Theorem dist_safe_p_resists_p1 :
  forall p q B,
    dist_safe_p_only p q ->
    (p - 1) / 2 > B ->
    p1_resistant p B.
Proof.
  intros p q B [Hsafe _] HB.
  apply safe_prime_resists_p1; assumption.
Qed.

(** Shared-prime pool: two moduli reuse [p].  Batch GCD is Euclid. *)
Definition dist_shared_pool (p q1 q2 : Z) : Prop :=
  Z.prime p /\ Z.prime q1 /\ Z.prime q2 /\
  p <> q1 /\ p <> q2 /\ q1 <> q2.

Theorem dist_shared_pool_gcd :
  forall p q1 q2,
    dist_shared_pool p q1 q2 ->
    Z.gcd (p * q1) (p * q2) = p.
Proof.
  intros p q1 q2 [Hp [Hq1 [Hq2 [H1 [H2 H3]]]]].
  apply gcd_shared_prime; assumption.
Qed.

(** Smooth [p−1] construction: [p = 2r+1] is *not* required; any
    [B]-smooth [p−1] is the Pollard handle. *)
Definition dist_smooth_pminus1 (p B : Z) : Prop :=
  Z.prime p /\ is_B_smooth B (p - 1).

Theorem dist_smooth_has_public_annihilator :
  forall p B,
    dist_smooth_pminus1 p B ->
    annihilates_p p (p - 1).
Proof.
  intros p B [Hp Hsm].
  eapply smooth_implies_public_annihilator; eassumption.
Qed.

(** Higher-cyclotomic leak: [p−1] is *not* [B]-smooth ([p1_resistant]),
    but [Φ_3(p)] has no prime factor [> B].  Strong-prime checks miss
    this.  Existence of such primes is CAS. *)
Definition dist_cyc3_leak (p B : Z) : Prop :=
  Z.prime p /\
  p1_resistant p B /\
  1 < cyc3 p /\
  (forall s, Z.prime s -> (s | cyc3 p) -> s <= B).

Lemma dist_cyc3_leak_not_p3_resistant :
  forall p B,
    dist_cyc3_leak p B ->
    ~ p3_resistant p B.
Proof.
  intros p B [_ [_ [_ Hall]]] [r [Hr [Hdiv Hgt]]].
  specialize (Hall r Hr Hdiv). lia.
Qed.

(** Small-[d] generation (decrypt-fast). *)
Definition dist_small_d (d N : Z) : Prop :=
  wiener_small_d d N.

Theorem dist_small_d_fails_large_d :
  forall d N, dist_small_d d N -> ~ kg_large_d d N.
Proof.
  intros d N H [Hd Hn]. exact (Hn H).
Qed.

(** Independent balanced far primes: the baseline that *should*
    discharge the geometric rulers.  Not a proof that a random
    sampler produces this — only that this shape passes [kg_far]
    and [kg_balanced]. *)
Definition dist_independent_far (p q gap : Z) : Prop :=
  Z.prime p /\ Z.prime q /\
  kg_balanced p q /\ kg_far p q gap.

Theorem dist_independent_passes_geom :
  forall p q gap,
    dist_independent_far p q gap ->
    kg_balanced p q /\ kg_far p q gap.
Proof. intros p q gap [_ [_ H]]. exact H. Qed.

(** Generation obligation beyond "strong primes": refuse [Φ_3],
    [Φ_4], and [Φ_6] too. *)
Definition kg_cyc_strong (p q B : Z) : Prop :=
  p3_resistant p B /\ p3_resistant q B /\
  p4_resistant p B /\ p4_resistant q B /\
  p6_resistant p B /\ p6_resistant q B.
