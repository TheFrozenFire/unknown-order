From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import Miller.
Require Import TwoPrimary.
Require Import Order.

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

Theorem miller_from_d_q :
  forall R a kp kq,
    Z.coprime a (rsa_N R) ->
    two_height a (miller_t R) (rsa_p R) kp ->
    two_height a (miller_t R) (rsa_q R) kq ->
    (kq < kp)%nat ->
    Z.gcd (a ^ (miller_t R * pow2n kq) - 1) (rsa_N R) = rsa_q R.
Proof.
  intros R a kp kq Hcop Hpht Hqht Hlt.
  unfold rsa_N. rewrite (Z.mul_comm (rsa_p R) (rsa_q R)).
  apply (height_mismatch_splits (rsa_q R) (rsa_p R) a (miller_t R) kq kp).
  - apply rsa_q_prime.
  - apply rsa_p_prime.
  - apply not_eq_sym, rsa_distinct.
  - unfold rsa_N in Hcop. rewrite Z.mul_comm. exact Hcop.
  - pose proof (miller_t_pos R). lia.
  - exact Hqht.
  - exact Hpht.
  - exact Hlt.
Qed.

(** Textbook instance: [M = 80 = 16·5], heights of [2] at
    [11] and [17] disagree ([cas/20]: [1] vs [3]). *)
Theorem rsa_test_base2_heights :
  two_height 2 (miller_t rsa_test) (rsa_p rsa_test) (val2 pin_ord2_p) /\
  two_height 2 (miller_t rsa_test) (rsa_q rsa_test) (val2 pin_ord2_q).
Proof.
  rewrite rsa_test_miller_t.
  split.
  - apply (proj2 (two_height_is_val2_ord pin_p 2 pin_ord2_p (odd_part pin_lam)
                    (val2 pin_ord2_p) pin_p_prime order_2_mod_11
                    ltac:(apply odd_part_pos; lia)
                    ltac:(apply odd_part_odd; lia)
                    ltac:(apply Z.mod_divide; [vm_compute; discriminate|]; vm_compute; reflexivity))).
    reflexivity.
  - apply (proj2 (two_height_is_val2_ord pin_q 2 pin_ord2_q (odd_part pin_lam)
                    (val2 pin_ord2_q) pin_q_prime order_2_mod_17
                    ltac:(apply odd_part_pos; lia)
                    ltac:(apply odd_part_odd; lia)
                    ltac:(apply Z.mod_divide; [vm_compute; discriminate|]; vm_compute; reflexivity))).
    reflexivity.
Qed.

Theorem rsa_test_miller_from_d :
  let kp := val2 pin_ord2_p in
  let kq := val2 pin_ord2_q in
  (if (kp <? kq)%nat
   then Z.gcd (2 ^ (miller_t rsa_test * pow2n kp) - 1) (rsa_N rsa_test)
          = rsa_p rsa_test
   else Z.gcd (2 ^ (miller_t rsa_test * pow2n kq) - 1) (rsa_N rsa_test)
          = rsa_q rsa_test).
Proof.
  intros kp kq.
  destruct (Nat.ltb_spec kp kq) as [Hlt | Hge].
  - apply (miller_from_d rsa_test 2 kp kq);
      [vm_compute; reflexivity | apply rsa_test_base2_heights
       | apply rsa_test_base2_heights | exact Hlt].
  - assert (kq < kp)%nat as Hlt.
    { unfold kp, kq in Hge |- *. vm_compute in Hge. vm_compute. lia. }
    apply (miller_from_d_q rsa_test 2 kp kq);
      [vm_compute; reflexivity | apply rsa_test_base2_heights
       | apply rsa_test_base2_heights | exact Hlt].
Qed.

(** ** Miller from any multiple of [λ], including [e k − 1]

    [miller_from_d] is the [M = e d − 1] case.  Any invert-all-units
    monomial [X^k] gives [e k ≡ 1 (mod λ)], so [M = e k − 1] is
    another multiple of [λ].  Heights are read at [odd_part(M)],
    which may differ from [odd_part(λ)] ([k = d + 2λ] on this pin).
    Mismatch still splits.  Not
    [residual_solver_constructs_factor_open_named]: writing [k]
    wrote a multiple of [λ].
    Cross-confirmed by [cas/173]. *)

Theorem miller_multiple_annihilates :
  forall R M a,
    0 < M ->
    Z.divide (rsa_lambda R) M ->
    Z.coprime a (rsa_N R) ->
    powm a M (rsa_N R) = 1.
Proof.
  intros R M a HMpos Hdiv Hcop.
  unfold rsa_N.
  apply annihilates_units.
  - apply rsa_p_prime.
  - apply rsa_q_prime.
  - apply rsa_distinct.
  - exact Hcop.
  - lia.
  - exact Hdiv.
Qed.

Theorem miller_height_exists_multiple :
  forall R M a,
    0 < M ->
    Z.divide (rsa_lambda R) M ->
    Z.coprime a (rsa_N R) ->
    exists kp kq,
      (kp <= val2 M)%nat /\
      two_height a (odd_part M) (rsa_p R) kp /\
      (kq <= val2 M)%nat /\
      two_height a (odd_part M) (rsa_q R) kq.
Proof.
  intros R M a HMpos Hdiv Hcop.
  pose proof (miller_multiple_annihilates R M a HMpos Hdiv Hcop) as Hann.
  pose proof (Z.prime_ge_2 _ (rsa_p_prime R)).
  pose proof (Z.prime_ge_2 _ (rsa_q_prime R)).
  pose proof (split2_of_reconstructs M ltac:(lia)) as Hsplit.
  rewrite Hsplit, (Z.mul_comm (2 ^ Z.of_nat (val2 M))) in Hann.
  unfold rsa_N in Hann.
  assert (powm a (odd_part M * pow2n (val2 M)) (rsa_p R) = 1) as Hp1.
  { unfold pow2n. apply (powm_one_mod_factor _ _ (rsa_p R) (rsa_q R));
      [lia | lia | exact Hann]. }
  assert (powm a (odd_part M * pow2n (val2 M)) (rsa_q R) = 1) as Hq1.
  { unfold pow2n.
    rewrite (Z.mul_comm (rsa_p R)) in Hann.
    apply (powm_one_mod_factor _ _ (rsa_q R) (rsa_p R));
      [lia | lia | exact Hann]. }
  pose proof (odd_part_nonneg M ltac:(lia)).
  destruct (two_height_exists a (odd_part M) (rsa_p R) (val2 M)
              ltac:(lia) ltac:(lia) Hp1) as [kp [Hlep Hpht]].
  destruct (two_height_exists a (odd_part M) (rsa_q R) (val2 M)
              ltac:(lia) ltac:(lia) Hq1) as [kq [Hleq Hqht]].
  exists kp, kq.
  split; [exact Hlep|].
  split; [exact Hpht|].
  split; [exact Hleq|].
  exact Hqht.
Qed.

Theorem miller_from_multiple :
  forall R M a kp kq,
    0 < M ->
    Z.divide (rsa_lambda R) M ->
    Z.coprime a (rsa_N R) ->
    two_height a (odd_part M) (rsa_p R) kp ->
    two_height a (odd_part M) (rsa_q R) kq ->
    (kp < kq)%nat ->
    Z.gcd (a ^ (odd_part M * pow2n kp) - 1) (rsa_N R) = rsa_p R.
Proof.
  intros R M a kp kq HMpos Hdiv Hcop Hpht Hqht Hlt.
  unfold rsa_N.
  apply (height_mismatch_splits (rsa_p R) (rsa_q R) a (odd_part M) kp kq).
  - apply rsa_p_prime.
  - apply rsa_q_prime.
  - apply rsa_distinct.
  - exact Hcop.
  - apply odd_part_nonneg. lia.
  - exact Hpht.
  - exact Hqht.
  - exact Hlt.
Qed.

Theorem miller_from_multiple_q :
  forall R M a kp kq,
    0 < M ->
    Z.divide (rsa_lambda R) M ->
    Z.coprime a (rsa_N R) ->
    two_height a (odd_part M) (rsa_p R) kp ->
    two_height a (odd_part M) (rsa_q R) kq ->
    (kq < kp)%nat ->
    Z.gcd (a ^ (odd_part M * pow2n kq) - 1) (rsa_N R) = rsa_q R.
Proof.
  intros R M a kp kq HMpos Hdiv Hcop Hpht Hqht Hlt.
  unfold rsa_N. rewrite (Z.mul_comm (rsa_p R) (rsa_q R)).
  apply (height_mismatch_splits (rsa_q R) (rsa_p R) a (odd_part M) kq kp).
  - apply rsa_q_prime.
  - apply rsa_p_prime.
  - apply not_eq_sym, rsa_distinct.
  - unfold rsa_N in Hcop. rewrite Z.mul_comm. exact Hcop.
  - apply odd_part_nonneg. lia.
  - exact Hqht.
  - exact Hpht.
  - exact Hlt.
Qed.

Lemma trapdoor_exponent_divides_lambda :
  forall R k,
    (rsa_e R * k) mod (rsa_lambda R) = 1 ->
    (rsa_lambda R | rsa_e R * k - 1).
Proof.
  intros R k Hinv.
  pose proof (rsa_lambda_gt_1 R).
  apply mods_eq_iff_divides; [lia|].
  rewrite Hinv. symmetry. apply Z.mod_1_l. lia.
Qed.

Theorem miller_from_trapdoor_exponent :
  forall R k a kp kq,
    0 < rsa_e R * k - 1 ->
    (rsa_e R * k) mod (rsa_lambda R) = 1 ->
    Z.coprime a (rsa_N R) ->
    two_height a (odd_part (rsa_e R * k - 1)) (rsa_p R) kp ->
    two_height a (odd_part (rsa_e R * k - 1)) (rsa_q R) kq ->
    (kp < kq)%nat ->
    Z.gcd (a ^ (odd_part (rsa_e R * k - 1) * pow2n kp) - 1) (rsa_N R)
      = rsa_p R.
Proof.
  intros R k a kp kq HMpos Hinv Hcop Hpht Hqht Hlt.
  apply (miller_from_multiple R (rsa_e R * k - 1) a kp kq);
    [lia | apply trapdoor_exponent_divides_lambda; exact Hinv
     | exact Hcop | exact Hpht | exact Hqht | exact Hlt].
Qed.

Theorem miller_from_trapdoor_exponent_q :
  forall R k a kp kq,
    0 < rsa_e R * k - 1 ->
    (rsa_e R * k) mod (rsa_lambda R) = 1 ->
    Z.coprime a (rsa_N R) ->
    two_height a (odd_part (rsa_e R * k - 1)) (rsa_p R) kp ->
    two_height a (odd_part (rsa_e R * k - 1)) (rsa_q R) kq ->
    (kq < kp)%nat ->
    Z.gcd (a ^ (odd_part (rsa_e R * k - 1) * pow2n kq) - 1) (rsa_N R)
      = rsa_q R.
Proof.
  intros R k a kp kq HMpos Hinv Hcop Hpht Hqht Hlt.
  apply (miller_from_multiple_q R (rsa_e R * k - 1) a kp kq);
    [lia | apply trapdoor_exponent_divides_lambda; exact Hinv
     | exact Hcop | exact Hpht | exact Hqht | exact Hlt].
Qed.
