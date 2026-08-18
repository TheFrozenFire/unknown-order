From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import StrongPrimes.

Open Scope Z_scope.

(** * Type B beyond [p±1]: cyclotomic periods [Φ_n(p)]

    Pollard [p−1] is the [n=1] cyclotomic method: the period is
    [Φ_1(p) = p−1].  Williams [p+1] is [n=2]: [Φ_2(p) = p+1].  The
    same shape in [F_{p^k}] uses [Φ_n(p)] for [n | k] —

      [Φ_3(p) = p²+p+1],   [Φ_4(p) = p²+1],   [Φ_6(p) = p²−p+1].

    These are not a new leak *type*.  They are Type B with a different
    recurrence.  A generator that only refuses a smooth [p−1] (or only
    a smooth [p+1]) still leaks if [Φ_3(p)] is smooth.

    Identities are proved by [ring].  Lucas / [F_{p²}] evaluation is
    [Lucas.v] / [Fp2.v] / [williams_eval_of_qnr].  Cross-confirmed by
    [cas/14_cyclotomic.gp]. *)

Definition cyc1 (p : Z) : Z := p - 1.
Definition cyc2 (p : Z) : Z := p + 1.
Definition cyc3 (p : Z) : Z := p * p + p + 1.
Definition cyc4 (p : Z) : Z := p * p + 1.
Definition cyc6 (p : Z) : Z := p * p - p + 1.

Lemma cyc_p2_minus_1 :
  forall p, p * p - 1 = cyc1 p * cyc2 p.
Proof. intros. unfold cyc1, cyc2. ring. Qed.

Lemma cyc_p3_minus_1 :
  forall p, p * p * p - 1 = cyc1 p * cyc3 p.
Proof. intros. unfold cyc1, cyc3. ring. Qed.

Lemma cyc_p4_minus_1 :
  forall p, p * p * p * p - 1 = cyc1 p * cyc2 p * cyc4 p.
Proof. intros. unfold cyc1, cyc2, cyc4. ring. Qed.

Lemma cyc_p6_minus_1 :
  forall p,
    p * p * p * p * p * p - 1 =
      cyc1 p * cyc2 p * cyc3 p * cyc6 p.
Proof. intros. unfold cyc1, cyc2, cyc3, cyc6. ring. Qed.

Lemma cyc1_divides_p2_minus_1 :
  forall p, (cyc1 p | p * p - 1).
Proof. intros. rewrite cyc_p2_minus_1. exists (cyc2 p). ring. Qed.

Lemma cyc2_divides_p2_minus_1 :
  forall p, (cyc2 p | p * p - 1).
Proof. intros. rewrite cyc_p2_minus_1. exists (cyc1 p). ring. Qed.

Lemma cyc3_divides_p3_minus_1 :
  forall p, (cyc3 p | p * p * p - 1).
Proof. intros. rewrite cyc_p3_minus_1. exists (cyc1 p). ring. Qed.

Lemma cyc1_divides_p3_minus_1 :
  forall p, (cyc1 p | p * p * p - 1).
Proof. intros. rewrite cyc_p3_minus_1. exists (cyc3 p). ring. Qed.

(** A cheap public [M] with [Φ_n(p) | M] is the generation-side handle
    for the [n]-th cyclotomic method — the analogue of
    [annihilates_p] / [williams_handle]. *)
Definition cyc_handle (Phi M : Z) : Prop :=
  0 <= M /\ (Phi | M).

Lemma cyc1_handle_is_p1 :
  forall p M, cyc_handle (cyc1 p) M <-> 0 <= M /\ (p - 1 | M).
Proof. intros. unfold cyc_handle, cyc1. reflexivity. Qed.

Lemma cyc2_handle_is_williams :
  forall p M, cyc_handle (cyc2 p) M <-> 0 <= M /\ (p + 1 | M).
Proof. intros. unfold cyc_handle, cyc2. reflexivity. Qed.

Definition cyc_resistant (Phi B : Z) : Prop :=
  has_large_prime_factor Phi B.

Lemma cyc1_resistant_iff_p1 :
  forall p B, cyc_resistant (cyc1 p) B <-> p1_resistant p B.
Proof. intros. unfold cyc_resistant, cyc1, p1_resistant. reflexivity. Qed.

Lemma cyc2_resistant_iff_pp1 :
  forall p B, cyc_resistant (cyc2 p) B <-> pp1_resistant p B.
Proof. intros. unfold cyc_resistant, cyc2, pp1_resistant. reflexivity. Qed.

Definition p3_resistant (p B : Z) : Prop := cyc_resistant (cyc3 p) B.
Definition p4_resistant (p B : Z) : Prop := cyc_resistant (cyc4 p) B.
Definition p6_resistant (p B : Z) : Prop := cyc_resistant (cyc6 p) B.

(** Strong primes refuse [n=1] and [n=2].  They do not mention
    [Φ_3], [Φ_4], [Φ_6].  That is the generation gap this file names. *)
Definition cyc_strong (p B : Z) : Prop :=
  p1_resistant p B /\
  pp1_resistant p B /\
  p3_resistant p B /\
  p4_resistant p B /\
  p6_resistant p B.

Lemma strong_prime_is_partial_cyc :
  forall p B,
    strong_prime p B ->
    p1_resistant p B /\ pp1_resistant p B.
Proof. intros p B H. apply strong_prime_resists_both; exact H. Qed.

Lemma cyc3_pos :
  forall p, 2 <= p -> 1 < cyc3 p.
Proof. intros. unfold cyc3. nia. Qed.

Lemma cyc4_pos :
  forall p, p <> 0 -> 1 < cyc4 p.
Proof. intros. unfold cyc4. nia. Qed.

Lemma cyc6_pos_ge3 :
  forall p, 3 <= p -> 1 < cyc6 p.
Proof. intros. unfold cyc6. nia. Qed.
