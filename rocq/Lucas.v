From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.

Require Import StrongPrimes.
Require Import Cyclotomic.

Open Scope Z_scope.

(** * Lucas [V] and the Williams [p+1] period

    Pollard [p−1] is exponentiation in [F_p]* (order [p−1]).
    Williams [p+1] is the same idea in the order-[p+1] torus of
    [F_{p²}]*, evaluated with a Lucas sequence so the arithmetic
    stays in [Z/NZ].  That is Type B at [n = 2]: the period is
    [Φ₂(p) = p+1], already named [cyc2] / [pp1_resistant].

    This file proves the addition formula
    [V_{m+n} = V_m V_n − Q^n V_{m−n}] ([n ≤ m]) and doubling as
    a corollary.  The QNR evaluation [V_{p+1} ≡ 2 (mod p)] is
    named and CAS-pinned.  Cross-confirmed by [cas/22_lucas.gp]. *)

Fixpoint lucasV (P Q : Z) (n : nat) : Z :=
  match n with
  | O => 2
  | S O => P
  | S (S n' as n1) => P * lucasV P Q n1 - Q * lucasV P Q n'
  end.

Lemma lucasV_0 : forall P Q, lucasV P Q 0 = 2.
Proof. reflexivity. Qed.

Lemma lucasV_1 : forall P Q, lucasV P Q 1 = P.
Proof. reflexivity. Qed.

Lemma lucasV_rec :
  forall P Q n,
    lucasV P Q (S (S n)) = P * lucasV P Q (S n) - Q * lucasV P Q n.
Proof. intros. reflexivity. Qed.

Lemma lucasV_2 :
  forall P Q, lucasV P Q 2%nat = P * P - Q * 2.
Proof. intros. reflexivity. Qed.

Lemma lucasV_succ :
  forall P Q m,
    (1 <= m)%nat ->
    lucasV P Q (S m) = P * lucasV P Q m - Q * lucasV P Q (m - 1).
Proof.
  intros P Q m Hm.
  destruct m as [| m']; [lia|].
  replace (S m' - 1)%nat with m' by lia.
  apply lucasV_rec.
Qed.

(** [V_{m+n} = V_m V_n − Q^n V_{m−n}] when [n ≤ m]. *)
Theorem lucasV_add :
  forall P Q m n,
    (n <= m)%nat ->
    lucasV P Q (m + n) =
      lucasV P Q m * lucasV P Q n
        - Q ^ Z.of_nat n * lucasV P Q (m - n).
Proof.
  intros P Q m n.
  revert m.
  induction n as [n IH] using (well_founded_ind lt_wf).
  intros m Hle.
  destruct n as [| n'].
  - rewrite Nat.add_0_r, Nat.sub_0_r, lucasV_0, Z.pow_0_r. ring.
  - destruct n' as [| n''].
    + destruct m as [| m']; [lia|].
      rewrite Nat.add_comm. simpl plus.
      rewrite lucasV_rec, lucasV_1, Z.pow_1_r.
      replace (S m' - 1)%nat with m' by lia. ring.
    + assert (n'' < S (S n''))%nat by lia.
      assert (S n'' < S (S n''))%nat by lia.
      assert (n'' <= m)%nat by lia.
      assert (S n'' <= m)%nat by lia.
      replace (m + S (S n''))%nat with (S (S (m + n''))) by lia.
      rewrite lucasV_rec.
      replace (S (m + n'')) with (m + S n'')%nat by lia.
      rewrite (IH (S n'') ltac:(lia) m ltac:(lia)).
      rewrite (IH n'' ltac:(lia) m ltac:(lia)).
      rewrite (lucasV_rec P Q n'').
      set (k := (m - n'')%nat).
      assert (2 <= k)%nat by (unfold k; lia).
      replace (m - S n'')%nat with (k - 1)%nat by (unfold k; lia).
      replace (m - S (S n''))%nat with (k - 2)%nat by (unfold k; lia).
      replace (lucasV P Q k)
        with (P * lucasV P Q (k - 1) - Q * lucasV P Q (k - 2)).
      * replace (Z.of_nat (S n'')) with (Z.succ (Z.of_nat n'')) by lia.
        rewrite Z.pow_succ_r by lia.
        replace (Z.of_nat (S (S n'')))
          with (Z.succ (Z.succ (Z.of_nat n''))) by lia.
        rewrite !Z.pow_succ_r by lia. ring.
      * replace k with (S (S (k - 2))) by lia.
        rewrite lucasV_rec.
        replace (S (k - 2)) with (k - 1)%nat by lia.
        replace (S (k - 1) - 1)%nat with (k - 1)%nat by lia.
        replace (S (k - 1) - 2)%nat with (k - 2)%nat by lia.
        reflexivity.
Qed.

Theorem lucasV_double :
  forall P Q n,
    lucasV P Q (n + n) =
      lucasV P Q n * lucasV P Q n - Q ^ Z.of_nat n * 2.
Proof.
  intros P Q n.
  rewrite (lucasV_add P Q n n ltac:(lia)), Nat.sub_diag, lucasV_0.
  reflexivity.
Qed.

Theorem lucasV_double_Q1 :
  forall P n,
    lucasV P 1 (n + n) = lucasV P 1 n * lucasV P 1 n - 2.
Proof.
  intros P n.
  rewrite lucasV_double, Z.pow_1_l by lia. ring.
Qed.

(** The computed table is now a corollary. *)
Theorem lucasV_double_Q1_table :
  (forall P, lucasV P 1 0%nat = lucasV P 1 0%nat * lucasV P 1 0%nat - 2) /\
  (forall P, lucasV P 1 2%nat = lucasV P 1 1%nat * lucasV P 1 1%nat - 2) /\
  (forall P, lucasV P 1 4%nat = lucasV P 1 2%nat * lucasV P 1 2%nat - 2) /\
  (forall P, lucasV P 1 6%nat = lucasV P 1 3%nat * lucasV P 1 3%nat - 2).
Proof.
  repeat split; intros P;
    (replace 2%nat with (1 + 1)%nat by reflexivity; apply lucasV_double_Q1)
    || (replace 4%nat with (2 + 2)%nat by reflexivity; apply lucasV_double_Q1)
    || (replace 6%nat with (3 + 3)%nat by reflexivity; apply lucasV_double_Q1)
    || (replace 0%nat with (0 + 0)%nat by reflexivity; apply lucasV_double_Q1).
Qed.

(** The Williams handle is exactly the [n=2] cyclotomic handle. *)
Theorem williams_handle_is_cyc2 :
  forall p M, cyc_handle (cyc2 p) M <-> 0 <= M /\ (p + 1 | M).
Proof. intros. apply cyc2_handle_is_williams. Qed.

Theorem safe_prime_refuses_pminus1_only :
  forall p B,
    safe_prime p ->
    (p - 1) / 2 > B ->
    p1_resistant p B.
Proof. intros. apply safe_prime_resists_p1; assumption. Qed.

(** A safe prime need not refuse [p+1].  [p = 2r+1] makes
    [p+1 = 2(r+1)], and [r+1] may be smooth.  That is why
    "strong" asks for a large prime factor of [p+1] as well. *)
Definition lucas_period (p : Z) : Z := p + 1.

Theorem lucas_period_is_cyc2 :
  forall p, lucas_period p = cyc2 p.
Proof. reflexivity. Qed.

(** Williams evaluation [V_{p+1} ≡ 2 (mod p)] when [P²−4] is a QNR
    is a named hypothesis: it needs [V_n(a+a⁻¹) = a^n+a⁻ⁿ] in
    [F_{p²}].  Multiples of the period are a theorem from addition.
    CAS [cas/22] checks the evaluation on Blum and safe primes. *)

Definition williams_eval (P p : Z) : Prop :=
  2 < p /\ lucasV P 1 (Z.to_nat (p + 1)) mod p = 2.

Lemma lucasV_add_Q1 :
  forall P m n,
    (n <= m)%nat ->
    lucasV P 1 (m + n) =
      lucasV P 1 m * lucasV P 1 n - lucasV P 1 (m - n).
Proof.
  intros P m n H.
  rewrite (lucasV_add P 1 m n H), Z.pow_1_l by lia. ring.
Qed.

Theorem williams_eval_k_times :
  forall P p k,
    williams_eval P p ->
    lucasV P 1 (k * Z.to_nat (p + 1)) mod p = 2.
Proof.
  intros P p k [Hp Hev].
  set (t := Z.to_nat (p + 1)) in *.
  assert (Ht : (0 < t)%nat).
  { unfold t. apply Nat2Z.inj_lt. rewrite Z2Nat.id; lia. }
  induction k as [k IH] using (well_founded_ind lt_wf).
  destruct k as [| k'].
  - rewrite Nat.mul_0_l, lucasV_0. apply Z.mod_small. lia.
  - destruct k' as [| k''].
    + rewrite Nat.mul_1_l. exact Hev.
    + replace (S (S k'') * t)%nat with (S k'' * t + t)%nat by lia.
      rewrite lucasV_add_Q1 by (apply Nat.le_trans with (S k'' * t)%nat; nia).
      replace (S k'' * t - t)%nat with (k'' * t)%nat by lia.
      rewrite Zminus_mod, Z.mul_mod by lia.
      rewrite (IH (S k'') ltac:(lia)), (IH k'' ltac:(lia)), Hev.
      change (2 * 2) with 4.
      rewrite <- (Z.mod_small 2 p ltac:(lia)) at 1.
      rewrite <- Zminus_mod.
      apply Z.mod_small; lia.
Qed.

Theorem williams_eval_on_multiples :
  forall P p M,
    williams_eval P p ->
    0 <= M ->
    (p + 1 | M) ->
    lucasV P 1 (Z.to_nat M) mod p = 2.
Proof.
  intros P p M Hev HM [k Hk].
  pose proof Hev as [Hp _].
  assert (0 <= k) by nia.
  rewrite Hk.
  assert (Z.to_nat (k * (p + 1)) = Z.to_nat k * Z.to_nat (p + 1))%nat.
  { apply Z2Nat.inj_mul; lia. }
  rewrite H0.
  apply williams_eval_k_times. exact Hev.
Qed.

Theorem pp1_resistant_is_torus_period :
  forall p B, pp1_resistant p B <-> has_large_prime_factor (p + 1) B.
Proof. intros. reflexivity. Qed.

Theorem typeB_n2_is_williams_period :
  forall p M, cyc_handle (cyc2 p) M <-> 0 <= M /\ (p + 1 | M).
Proof. intros. apply williams_handle_is_cyc2. Qed.
