From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import PollardP1.

Open Scope Z_scope.

(** * CRT-RSA: a small [d_p] is a short one-sided annihilator

    Implementations store [d_p = d mod (p−1)] for CRT decryption.
    Because [p−1 | λ(N)] and [e d ≡ 1 (mod λ)], one has
    [e d_p ≡ 1 (mod p−1)].  Then [e d_p − 1] is a multiple of [p−1]:
    exactly [annihilates_p], with cofactor bounded by [e] when [d_p]
    is short.  This is Pollard [p−1] and Wiener at once.

    Cross-confirmed by [cas/10_pollard_p1.gp] (one-sided gcd) and
    [cas/11_wiener.gp] (short cofactor). *)

Definition crt_dp (d p : Z) : Z := d mod (p - 1).

(** Restricted to [p ≥ 3], so [p−1 ≥ 2] and "≡ 1 (mod p−1)" is
    meaningful.  [p = 2] makes the CRT exponent live modulo 1. *)
Lemma lambda_gt_1_of :
  forall p q, Z.prime p -> Z.prime q -> 3 <= p ->
    1 < lambda_semiprime p q.
Proof.
  intros p q Hp Hq Hp3.
  unfold lambda_semiprime.
  apply Z.lt_le_trans with (p - 1); [lia|].
  apply Z.divide_pos_le.
  - pose proof (Z.lcm_nonneg (p - 1) (q - 1)).
    assert (Z.lcm (p - 1) (q - 1) <> 0) as Hnz.
    { intro Hz. pose proof (proj1 (Z.lcm_eq_0 (p - 1) (q - 1)) Hz) as Hor.
      pose proof (Z.prime_ge_2 q Hq). lia. }
    lia.
  - apply Z.divide_lcm_l.
Qed.

Lemma ed_one_mod_pminus1_of :
  forall e d p q,
    Z.prime p -> Z.prime q -> 3 <= p ->
    (e * d) mod (lambda_semiprime p q) = 1 ->
    (e * d) mod (p - 1) = 1.
Proof.
  intros e d p q Hp Hq Hp3 Hinv.
  pose proof (Z.prime_ge_2 p Hp).
  assert (1 < p - 1) by lia.
  pose proof (lambda_gt_1_of p q Hp Hq Hp3) as Hlam.
  assert (p - 1 | e * d - 1) as Hdiv.
  { apply (Z.divide_trans _ (lambda_semiprime p q)).
    - apply lambda_divides_pminus1.
    - apply mods_eq_iff_divides; [lia|].
      rewrite Hinv. rewrite Z.mod_1_l by lia. reflexivity. }
  transitivity (1 mod (p - 1)).
  - apply (proj2 (mods_eq_iff_divides (e * d) 1 (p - 1) ltac:(lia))).
    exact Hdiv.
  - apply Z.mod_1_l; lia.
Qed.

Lemma dp_congruent_d :
  forall d p, p - 1 <> 0 -> d mod (p - 1) = crt_dp d p.
Proof. intros. unfold crt_dp. reflexivity. Qed.

Theorem crt_dp_annihilates :
  forall e d p q,
    Z.prime p -> Z.prime q -> 3 <= p ->
    0 <= e ->
    (e * d) mod (lambda_semiprime p q) = 1 ->
    annihilates_p p (e * crt_dp d p - 1).
Proof.
  intros e d p q Hp Hq Hp3 He Hinv.
  pose proof (ed_one_mod_pminus1_of e d p q Hp Hq Hp3 Hinv) as Hed.
  unfold crt_dp, annihilates_p.
  assert (1 < p - 1) by lia.
  pose proof (Z.mod_pos_bound d (p - 1) ltac:(lia)) as Hbd.
  split.
  - (* d_p ≠ 0 because e d ≡ 1 (mod p−1) and p−1 > 1 *)
    assert (d mod (p - 1) <> 0) as Hnz.
    { intro Hz.
      assert ((e * d) mod (p - 1) = 0) as Hz0.
      { rewrite Z.mul_mod by lia. rewrite Hz, Z.mul_0_r, Z.mod_0_l by lia.
        reflexivity. }
      lia. }
    assert (0 < e) as Hepos.
    { destruct (Z.eq_dec e 0) as [Hez | Hene]; [| lia].
      subst e. rewrite Z.mul_0_l, Z.mod_0_l in Hed by lia. lia. }
    assert (1 <= d mod (p - 1)) by lia.
    nia.
  - apply mods_eq_iff_divides; [lia|].
    transitivity ((e * d) mod (p - 1)).
    + rewrite Z.mul_mod by lia.
      rewrite (Z.mod_mod d (p - 1)) by lia.
      rewrite <- Z.mul_mod by lia.
      reflexivity.
    + rewrite Hed. rewrite Z.mod_1_l by lia. reflexivity.
Qed.

(** Short [d_p] makes the cofactor of that one-sided annihilator
    short: [e d_p − 1 < e (p−1)], and if [d_p < B] then
    [e d_p − 1 < e B]. *)
Lemma short_dp_short_annihilator :
  forall e d p B,
    0 < e -> 0 < B ->
    0 < p - 1 ->
    crt_dp d p < B ->
    e * crt_dp d p - 1 < e * B.
Proof.
  intros e d p B He HB Hp Hdp.
  unfold crt_dp in *. nia.
Qed.

Definition crt_dq (d q : Z) : Z := d mod (q - 1).

Lemma lambda_semiprime_comm :
  forall p q, lambda_semiprime p q = lambda_semiprime q p.
Proof. intros p q. unfold lambda_semiprime. apply Z.lcm_comm. Qed.

Theorem crt_dq_annihilates :
  forall e d p q,
    Z.prime p -> Z.prime q -> 3 <= q ->
    0 <= e ->
    (e * d) mod (lambda_semiprime p q) = 1 ->
    annihilates_p q (e * crt_dq d q - 1).
Proof.
  intros e d p q Hp Hq Hq3 He Hinv.
  apply (crt_dp_annihilates e d q p Hq Hp Hq3 He).
  rewrite lambda_semiprime_comm in Hinv.
  exact Hinv.
Qed.

Lemma short_dq_short_annihilator :
  forall e d q B,
    0 < e -> 0 < B ->
    0 < q - 1 ->
    crt_dq d q < B ->
    e * crt_dq d q - 1 < e * B.
Proof.
  intros e d q B He HB Hq Hdq.
  unfold crt_dq in *. nia.
Qed.
