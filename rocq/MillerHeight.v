From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import Miller.
Require Import TwoPrimary.

Open Scope Z_scope.

(** * Miller-from-[d] as 2-heights on an odd multiple of [odd_part(λ)]

    [miller_t] is the odd part of a known multiple of [λ], hence an
    odd multiple of [odd_part(λ)].  A base splits [N] exactly when
    the 2-heights at [p] and [q], read at this common [t], disagree
    ([height_mismatch_splits]).  Existence of those heights is
    [a^M ≡ 1].

    Cross-confirmed by [cas/04_miller_factor.gp] and
    [cas/20_two_primary.gp]. *)

Lemma miller_t_pos : forall R, 0 < miller_t R.
Proof.
  intros R. unfold miller_t.
  apply odd_part_pos. apply miller_M_pos.
Qed.

Lemma miller_t_odd : forall R, Z.Odd (miller_t R).
Proof.
  intros R. unfold miller_t.
  apply odd_part_odd. apply miller_M_pos.
Qed.

Lemma miller_t_multiple_of_lambda_odd :
  forall R, Z.divide (odd_part (rsa_lambda R)) (miller_t R).
Proof.
  intros R.
  pose proof (rsa_ed_minus_1_divides R) as [k Hk].
  pose proof (miller_M_pos R) as HMpos.
  pose proof (rsa_lambda_pos R) as Hlpos.
  unfold miller_M in HMpos.
  assert (0 < k).
  { destruct (Z.lt_trichotomy k 0) as [Hkneg | [Hkz | Hkpos]].
    - nia.
    - subst k. rewrite Z.mul_0_l in Hk. lia.
    - exact Hkpos. }
  unfold miller_t, miller_M.
  rewrite Hk, odd_part_mul by lia.
  exists (odd_part k). ring.
Qed.

Lemma powm_one_mod_factor :
  forall a e p q,
    1 < p -> 0 < q ->
    powm a e (p * q) = 1 ->
    powm a e p = 1.
Proof.
  intros a e p q Hp Hq H1.
  unfold powm in *.
  transitivity ((a ^ e mod (p * q)) mod p).
  - symmetry. apply Z.mod_mod_divide. exists q. ring.
  - rewrite H1. apply Z.mod_1_l. lia.
Qed.

Theorem miller_height_exists :
  forall R a,
    Z.coprime a (rsa_N R) ->
    exists kp kq,
      (kp <= miller_s R)%nat /\
      two_height a (miller_t R) (rsa_p R) kp /\
      (kq <= miller_s R)%nat /\
      two_height a (miller_t R) (rsa_q R) kq.
Proof.
  intros R a Hcop.
  pose proof (miller_M_annihilates R a Hcop) as Hann.
  pose proof (rsa_N_gt_1 R).
  pose proof (Z.prime_ge_2 _ (rsa_p_prime R)).
  pose proof (Z.prime_ge_2 _ (rsa_q_prime R)).
  pose proof (miller_M_split R) as Hsplit.
  rewrite Hsplit, (Z.mul_comm (2 ^ Z.of_nat (miller_s R))) in Hann.
  unfold rsa_N in Hann.
  assert (powm a (miller_t R * pow2n (miller_s R)) (rsa_p R) = 1) as Hp1.
  { unfold pow2n. apply (powm_one_mod_factor _ _ (rsa_p R) (rsa_q R));
      [lia | lia | exact Hann]. }
  assert (powm a (miller_t R * pow2n (miller_s R)) (rsa_q R) = 1) as Hq1.
  { unfold pow2n.
    rewrite (Z.mul_comm (rsa_p R)) in Hann.
    apply (powm_one_mod_factor _ _ (rsa_q R) (rsa_p R));
      [lia | lia | exact Hann]. }
  pose proof (miller_t_pos R).
  destruct (two_height_exists a (miller_t R) (rsa_p R) (miller_s R)
              ltac:(lia) ltac:(lia) Hp1) as [kp [Hlep Hpht]].
  destruct (two_height_exists a (miller_t R) (rsa_q R) (miller_s R)
              ltac:(lia) ltac:(lia) Hq1) as [kq [Hleq Hqht]].
  exists kp, kq.
  split; [exact Hlep|].
  split; [exact Hpht|].
  split; [exact Hleq|].
  exact Hqht.
Qed.

Theorem miller_from_d :
  forall R a kp kq,
    Z.coprime a (rsa_N R) ->
    two_height a (miller_t R) (rsa_p R) kp ->
    two_height a (miller_t R) (rsa_q R) kq ->
    (kp < kq)%nat ->
    Z.gcd (a ^ (miller_t R * pow2n kp) - 1) (rsa_N R) = rsa_p R.
Proof.
  intros R a kp kq Hcop Hpht Hqht Hlt.
  unfold rsa_N.
  apply (height_mismatch_splits (rsa_p R) (rsa_q R) a (miller_t R) kp kq).
  - apply rsa_p_prime.
  - apply rsa_q_prime.
  - apply rsa_distinct.
  - exact Hcop.
  - pose proof (miller_t_pos R). lia.
  - exact Hpht.
  - exact Hqht.
  - exact Hlt.
Qed.

(** Textbook instance: [M = 80 = 16·5], heights of [2] at
    [11] and [17] disagree ([cas/20]: [1] vs [3]). *)
Theorem rsa_test_base2_heights :
  two_height 2 (miller_t rsa_test) (rsa_p rsa_test) 1%nat /\
  two_height 2 (miller_t rsa_test) (rsa_q rsa_test) 3%nat.
Proof.
  rewrite rsa_test_miller_t.
  unfold rsa_test, two_height, pow2n, powm. cbn.
  split.
  - split; [vm_compute; reflexivity|].
    intros j Hj. destruct j; [| lia]. vm_compute. discriminate.
  - split; [vm_compute; reflexivity|].
    intros j Hj.
    destruct j as [| j]; [| destruct j as [| j]; [| destruct j; [| lia]]];
      vm_compute; discriminate.
Qed.

Theorem rsa_test_miller_from_d :
  Z.gcd (2 ^ (miller_t rsa_test * pow2n 1) - 1) (rsa_N rsa_test)
    = rsa_p rsa_test.
Proof.
  apply (miller_from_d rsa_test 2 1%nat 3%nat).
  - vm_compute. reflexivity.
  - apply rsa_test_base2_heights.
  - apply rsa_test_base2_heights.
  - lia.
Qed.
