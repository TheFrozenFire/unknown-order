From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import Zmod.

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

(** ** Garner CRT decrypt equals [c^d]

    [c^{d_p} (mod p)] is [c^d (mod p)] by Fermat.  CRT recombination
    is then [c^d (mod pq)].  Quisquater–Couvreur is this map. *)

Lemma powm_reduce_pminus1 :
  forall p a d,
    Z.prime p ->
    Z.coprime a p ->
    0 <= d ->
    powm a d p = powm a (d mod (p - 1)) p.
Proof.
  intros p a d Hp Hcop Hd.
  pose proof (Z.prime_ge_2 p Hp).
  assert (0 < p - 1) by lia.
  pose proof (Z.div_mod d (p - 1) ltac:(lia)) as Hdm.
  rewrite Hdm at 1.
  assert (0 <= d mod (p - 1)) by (apply Z.mod_pos_bound; lia).
  assert (0 <= d / (p - 1)) by (apply Z.div_pos; lia).
  rewrite powm_add_r by nia.
  rewrite powm_mul_r by nia.
  rewrite (fermat_coprime p a Hp Hcop).
  rewrite powm_1_pow by nia.
  unfold powm.
  rewrite Z.mod_1_l by lia.
  rewrite Z.mul_1_l, Z.mod_mod by lia. reflexivity.
Qed.

Definition crt_decrypt (R : RSAInstance) (c : Z) : Z :=
  let mp := powm c (crt_dp (rsa_d R) (rsa_p R)) (rsa_p R) in
  let mq := powm c (crt_dq (rsa_d R) (rsa_q R)) (rsa_q R) in
  Z.combinecong (rsa_p R) (rsa_q R) mp mq.

Theorem crt_decrypt_eq_rsa_dec :
  forall R c,
    Z.coprime c (rsa_N R) ->
    3 <= rsa_p R ->
    3 <= rsa_q R ->
    crt_decrypt R c mod rsa_N R = rsa_dec R c.
Proof.
  intros R c Hcop Hp3 Hq3.
  pose proof (rsa_p_prime R) as Hp.
  pose proof (rsa_q_prime R) as Hq.
  pose proof (rsa_distinct R) as Hneq.
  pose proof (rsa_d_pos R).
  pose proof (rsa_N_gt_1 R).
  pose proof (Z.prime_ge_2 (rsa_p R) Hp).
  pose proof (Z.prime_ge_2 (rsa_q R) Hq).
  unfold crt_decrypt, rsa_N.
  set (mp := powm c (crt_dp (rsa_d R) (rsa_p R)) (rsa_p R)).
  set (mq := powm c (crt_dq (rsa_d R) (rsa_q R)) (rsa_q R)).
  set (x := Z.combinecong (rsa_p R) (rsa_q R) mp mq).
  assert (Z.coprime (rsa_p R) (rsa_q R)) as Hpq
    by (apply prime_coprime_distinct; assumption).
  pose proof (Z.combinecong_sound_coprime (rsa_p R) (rsa_q R) mp mq Hpq)
    as [Hxp Hxq].
  apply coprime_semiprime in Hcop; [| exact Hp | exact Hq | exact Hneq].
  destruct Hcop as [Hcp Hcq].
  assert (rsa_dec R c mod rsa_p R = mp mod rsa_p R) as Hdp.
  { unfold mp, rsa_dec, crt_dp, rsa_N.
    rewrite <- (powm_reduce_pminus1 (rsa_p R) c (rsa_d R))
      by (try assumption; lia).
    unfold powm.
    rewrite Z.mod_mod by lia.
    apply Z.mod_mod_divide. exists (rsa_q R). ring. }
  assert (rsa_dec R c mod rsa_q R = mq mod rsa_q R) as Hdq.
  { unfold mq, rsa_dec, crt_dq, rsa_N.
    rewrite <- (powm_reduce_pminus1 (rsa_q R) c (rsa_d R))
      by (try assumption; lia).
    unfold powm.
    rewrite Z.mod_mod by lia.
    apply Z.mod_mod_divide. exists (rsa_p R). ring. }
  unfold x.
  rewrite <- (Z.combinecong_complete_coprime_nonneg
                (rsa_dec R c) (rsa_p R) (rsa_q R) mp mq Hpq).
  - unfold rsa_dec, powm, rsa_N.
    now rewrite !(Z.mod_mod _ (rsa_p R * rsa_q R)) by nia.
  - rewrite Hdp. unfold mp. unfold powm. rewrite Z.mod_mod by lia. reflexivity.
  - rewrite Hdq. unfold mq. unfold powm. rewrite Z.mod_mod by lia. reflexivity.
  - nia.
Qed.

(** ** CRT of local inverses recovers [d] mod [λ]

    [d_p = d mod (p−1)] and [d_q = d mod (q−1)] are the CRT-RSA
    local exponents.  Any [x] with those two residues is
    [x ≡ d (mod λ)].  A TM that writes both local inverses of [e]
    wrote the trapdoor.  Not
    [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/174]. *)

Lemma cong_mod_lcm :
  forall a b m n,
    0 < m ->
    0 < n ->
    a mod m = b mod m ->
    a mod n = b mod n ->
    a mod (Z.lcm m n) = b mod (Z.lcm m n).
Proof.
  intros a b m n Hm Hn Hm_eq Hn_eq.
  assert (0 < Z.lcm m n) as Hlcm.
  { pose proof (Z.lcm_nonneg m n).
    pose proof (proj1 (Z.lcm_eq_0 m n)). lia. }
  apply mods_eq_iff_divides; [lia|].
  apply Z.lcm_least.
  - apply mods_eq_iff_divides; [lia | exact Hm_eq].
  - apply mods_eq_iff_divides; [lia | exact Hn_eq].
Qed.

Theorem crt_dp_dq_recover_d :
  forall p q d x,
    Z.prime p ->
    Z.prime q ->
    3 <= p ->
    3 <= q ->
    x mod (p - 1) = crt_dp d p ->
    x mod (q - 1) = crt_dq d q ->
    x mod (lambda_semiprime p q) = d mod (lambda_semiprime p q).
Proof.
  intros p q d x Hp Hq Hp3 Hq3 Hxp Hxq.
  unfold crt_dp, crt_dq, lambda_semiprime in *.
  apply cong_mod_lcm; [lia | lia | exact Hxp | exact Hxq].
Qed.

Lemma inverse_unique_mod :
  forall e x y m,
    1 < m ->
    (e * x) mod m = 1 ->
    (e * y) mod m = 1 ->
    x mod m = y mod m.
Proof.
  intros e x y m Hm Hx Hy.
  assert (Z.gcd e m = 1) as Hcop.
  { pose proof (Z.gcd_divide_l e m) as Hel.
    pose proof (Z.gcd_divide_r e m) as Hem.
    assert (Z.gcd e m | 1) as H1.
    { assert (Hex : (Z.gcd e m | e * x)) by (apply Z.divide_mul_l; exact Hel).
      assert (Hmx : (m | e * x - 1)).
      { apply Z.mod_divide; [lia|].
        rewrite Zminus_mod, Hx, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
        reflexivity. }
      assert (Hgx : (Z.gcd e m | e * x - 1))
        by (apply Z.divide_trans with m; [exact Hem | exact Hmx]).
      replace 1 with (e * x - (e * x - 1)) by ring.
      apply Z.divide_sub_r; [exact Hex | exact Hgx]. }
    apply Z.divide_1_r in H1.
    pose proof (Z.gcd_nonneg e m). lia. }
  apply (mul_cancel_r_coprime x y e m Hm Hcop).
  rewrite Z.mul_comm, Hx, Z.mul_comm, Hy. reflexivity.
Qed.

Theorem local_inv_is_crt_dp :
  forall e d da p q,
    Z.prime p ->
    Z.prime q ->
    3 <= p ->
    (e * d) mod (lambda_semiprime p q) = 1 ->
    (e * da) mod (p - 1) = 1 ->
    da mod (p - 1) = crt_dp d p.
Proof.
  intros e d da p q Hp Hq Hp3 Hinv Hda.
  pose proof (ed_one_mod_pminus1_of e d p q Hp Hq Hp3 Hinv) as Hed.
  unfold crt_dp.
  apply inverse_unique_mod with e; [lia | exact Hda | exact Hed].
Qed.

Theorem local_inv_is_crt_dq :
  forall e d db p q,
    Z.prime p ->
    Z.prime q ->
    3 <= q ->
    (e * d) mod (lambda_semiprime p q) = 1 ->
    (e * db) mod (q - 1) = 1 ->
    db mod (q - 1) = crt_dq d q.
Proof.
  intros e d db p q Hp Hq Hq3 Hinv Hdb.
  rewrite lambda_semiprime_comm in Hinv.
  pose proof (local_inv_is_crt_dp e d db q p Hq Hp Hq3 Hinv Hdb) as H.
  unfold crt_dp, crt_dq in *. exact H.
Qed.
