From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import FermatFactor.
Require Import StrongPrimes.
Require Import Wiener.
Require Import PollardP1.
Require Import CRTRSA.

Open Scope Z_scope.

(** * Key-generation intent-spec

    Each field refuses one leak from [notes/keygen-weaknesses.md].
    A generator that discharges these is allowed to use smaller [N] because
    it is not spending bits to hide a short or one-sided annihilator. *)

Definition bits_ge (n min : Z) : Prop := 2 ^ min <= n.

(** Bit-balanced: [q ≤ p ≤ 2q].  Refuses ECM-on-the-small-prime. *)
Definition kg_balanced (p q : Z) : Prop :=
  0 < q /\ q <= p /\ p <= 2 * q.

(** Far apart relative to [√N]: [|p−q|] is not Fermat-food.
    We use [|p−q| ≥ 2^gap] as the generation-side knob. *)
Definition kg_far (p q gap : Z) : Prop :=
  0 <= gap /\ 2 ^ gap <= Z.abs (p - q).

(** Large private exponent.  Conservative integer stand-in for
    [d > N^{1/4}].  Refuses Wiener. *)
Definition kg_large_d (d N : Z) : Prop :=
  0 < d /\ ~ wiener_small_d d N.

(** [p−1] and [q−1] each have a prime factor [> B].  Refuses Pollard. *)
Definition kg_p1_strong (p q B : Z) : Prop :=
  p1_resistant p B /\ p1_resistant q B.

Definition kg_pp1_strong (p q B : Z) : Prop :=
  pp1_resistant p B /\ pp1_resistant q B.

(** Public exponent not a tiny degree, unless the application pads. *)
Definition kg_e_not_tiny (e : Z) : Prop := 65537 <= e.

(** CRT exponents not tiny.  A short [d_p] is a short one-sided
    annihilator ([CRTRSA.crt_dp_annihilates]). *)
Definition kg_dp_not_tiny (d p : Z) : Prop :=
  1 < p - 1 /\ (p - 1) / 4 <= crt_dp d p.

Record KeyGenSpec : Type := {
  kg_min_bits : Z;
  kg_fermat_gap : Z;
  kg_smooth_bound : Z
}.

Definition satisfies_keygen (S : KeyGenSpec) (R : RSAInstance) : Prop :=
  kg_balanced (rsa_p R) (rsa_q R) /\
  kg_far (rsa_p R) (rsa_q R) (kg_fermat_gap S) /\
  bits_ge (rsa_p R) (kg_min_bits S) /\
  bits_ge (rsa_q R) (kg_min_bits S) /\
  kg_large_d (rsa_d R) (rsa_N R) /\
  kg_p1_strong (rsa_p R) (rsa_q R) (kg_smooth_bound S) /\
  kg_pp1_strong (rsa_p R) (rsa_q R) (kg_smooth_bound S).

(** Balanced primes give the [p+q < 3√N]-class bound used by Wiener,
    via [p ≤ 2q]. *)
Lemma balanced_sum_bound :
  forall p q,
    kg_balanced p q ->
    p + q <= 3 * q.
Proof.
  intros p q [Hq [Hle Hge]]. lia.
Qed.

Lemma balanced_q_le_sqrt :
  forall p q,
    kg_balanced p q ->
    q <= Z.sqrt (p * q).
Proof.
  intros p q [Hq [Hle Hge]].
  assert (q * q <= p * q) by nia.
  pose proof (Z.sqrt_spec (p * q) ltac:(nia)) as Hsp. cbn in Hsp.
  destruct (Z.lt_ge_cases (Z.sqrt (p * q)) q) as [Hlt | Hge']; [| exact Hge'].
  assert (Z.sqrt (p * q) + 1 <= q) by lia.
  assert ((Z.sqrt (p * q) + 1) * (Z.sqrt (p * q) + 1) <= q * q) by nia.
  nia.
Qed.

Theorem balanced_sum_vs_sqrt :
  forall p q,
    kg_balanced p q ->
    p + q <= 3 * Z.sqrt (p * q).
Proof.
  intros p q Hbal.
  pose proof (balanced_sum_bound p q Hbal) as Hs.
  pose proof (balanced_q_le_sqrt p q Hbal) as Hq.
  lia.
Qed.

Lemma balanced_implies_odd_candidates :
  forall p q,
    Z.prime p -> Z.prime q -> p <> 2 -> q <> 2 ->
    Z.odd p = true /\ Z.odd q = true.
Proof.
  intros p q Hp Hq Hnp Hnq.
  split; apply prime_odd_if_ne_2; assumption.
Qed.

(** ** Refusal lemmas: each generation obligation blocks one leak. *)

Theorem keygen_refuses_wiener :
  forall S R, satisfies_keygen S R -> ~ wiener_small_d (rsa_d R) (rsa_N R).
Proof.
  intros S R H. unfold satisfies_keygen in H.
  destruct H as [_ [_ [_ [_ [Hd _]]]]].
  unfold kg_large_d in Hd. exact (proj2 Hd).
Qed.

Theorem keygen_refuses_smooth_p :
  forall S R,
    satisfies_keygen S R ->
    has_large_prime_factor (rsa_p R - 1) (kg_smooth_bound S).
Proof.
  intros S R H. unfold satisfies_keygen in H.
  destruct H as [_ [_ [_ [_ [_ [Hp1 _]]]]]].
  unfold kg_p1_strong, p1_resistant in Hp1. exact (proj1 Hp1).
Qed.

Theorem keygen_refuses_smooth_q :
  forall S R,
    satisfies_keygen S R ->
    has_large_prime_factor (rsa_q R - 1) (kg_smooth_bound S).
Proof.
  intros S R H. unfold satisfies_keygen in H.
  destruct H as [_ [_ [_ [_ [_ [Hp1 _]]]]]].
  unfold kg_p1_strong, p1_resistant in Hp1. exact (proj2 Hp1).
Qed.

Theorem p1_resistant_not_smooth :
  forall p B,
    p1_resistant p B ->
    ~ is_B_smooth B (p - 1).
Proof.
  intros p B [r [Hr [Hdiv Hgt]]] [Hpos Hall].
  unfold prime_factor_le in Hall.
  specialize (Hall r Hr Hdiv). lia.
Qed.

Theorem keygen_p1_not_smooth :
  forall S R,
    satisfies_keygen S R ->
    ~ is_B_smooth (kg_smooth_bound S) (rsa_p R - 1) /\
    ~ is_B_smooth (kg_smooth_bound S) (rsa_q R - 1).
Proof.
  intros S R H.
  unfold satisfies_keygen in H.
  destruct H as [_ [_ [_ [_ [_ [Hp1 _]]]]]].
  destruct Hp1 as [Hp Hq].
  split; eapply p1_resistant_not_smooth; eassumption.
Qed.

Theorem keygen_far_large_fermat_diff :
  forall S R,
    satisfies_keygen S R ->
    rsa_p R <> 2 -> rsa_q R <> 2 ->
    2 ^ kg_fermat_gap S <=
      2 * Z.abs (fermat_diff (rsa_p R) (rsa_q R)).
Proof.
  intros S R H Hp2 Hq2.
  unfold satisfies_keygen in H.
  destruct H as [Hbal [Hfar _]].
  unfold kg_far in Hfar. destruct Hfar as [Hgap Habs].
  pose proof (rsa_p_prime R) as Hpp.
  pose proof (rsa_q_prime R) as Hqp.
  pose proof (prime_odd_if_ne_2 (rsa_p R) Hpp Hp2) as Hop.
  pose proof (prime_odd_if_ne_2 (rsa_q R) Hqp Hq2) as Hoq.
  apply far_apart_large_diff; assumption.
Qed.

(** Unbalanced generation: the small prime *is* the secret.  If
    [p ≤ q] then [p ≤ √N], so trial / ECM cost is governed by [p]
    rather than by the bit length of [N]. *)
Theorem small_prime_le_sqrt :
  forall p q,
    0 < p -> 0 < q -> p <= q ->
    p <= Z.sqrt (p * q).
Proof.
  intros p q Hp Hq Hle.
  assert (p * p <= p * q) by nia.
  pose proof (Z.sqrt_spec (p * q) ltac:(nia)) as Hsp. cbn in Hsp.
  destruct (Z.lt_ge_cases (Z.sqrt (p * q)) p) as [Hlt | Hge]; [| exact Hge].
  assert (Z.sqrt (p * q) + 1 <= p) by lia.
  assert ((Z.sqrt (p * q) + 1) * (Z.sqrt (p * q) + 1) <= p * p) by nia.
  nia.
Qed.

Theorem tiny_e_is_degree :
  forall R, rsa_e R = 3 ->
    forall m, rsa_enc R m = powm m 3 (rsa_N R).
Proof. intros R He m. unfold rsa_enc. rewrite He. reflexivity. Qed.

(** Balanced primes plug into the classical Wiener sufficient
    criterion: [p+q ≤ 3 √N]. *)
Theorem balanced_wiener_sufficient :
  forall e d k p q,
    kg_balanced p q ->
    0 < d -> 0 < k -> k <= d ->
    2 <= p -> 2 <= q ->
    e * d = 1 + k * phi_semiprime p q ->
    36 * d * d * d * d < p * q ->
    in_wiener_basin e d k (p * q).
Proof.
  intros e d k p q Hbal Hd Hk Hkd Hp Hq Heq Htrig.
  apply (wiener_classical_sufficient e d k p q); try assumption.
  pose proof (balanced_sum_vs_sqrt p q Hbal) as Hs.
  lia.
Qed.
