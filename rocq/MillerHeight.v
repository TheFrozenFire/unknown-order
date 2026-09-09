From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
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

(** ** Square-chain Miller: [miller_walk] does not take [kp]

    The construction walks successive squares of [a^{odd_part(M)}]
    and gcd-splits at the first mixed [√1].  Height mismatch is a
    hypothesis on the *proof*, not an argument of [miller_walk].
    [M] is a given λ-multiple.  Not
    [residual_solver_constructs_factor_open_named].
    Not [rsa_inverter_constructs_factor_open_named].
    Not [strong_rsa_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/245]. *)

Lemma miller_walk_from_S_eq1 :
  forall N g fuel,
    powm g 2 N = 1 ->
    g <> 1 ->
    g <> N - 1 ->
    miller_walk_from N g (S fuel) = Some (Z.gcd (g - 1) N).
Proof.
  intros N g fuel Hng Hg1 Hgn1.
  cbn [miller_walk_from].
  destruct (powm g 2 N =? 1) eqn:Heq.
  - destruct (g =? 1) eqn:E1.
    + apply Z.eqb_eq in E1. congruence.
    + destruct (g =? N - 1) eqn:E2.
      * apply Z.eqb_eq in E2. congruence.
      * reflexivity.
  - apply Z.eqb_neq in Heq. congruence.
Qed.

Lemma miller_walk_from_S_neq1 :
  forall N g fuel,
    powm g 2 N <> 1 ->
    miller_walk_from N g (S fuel) = miller_walk_from N (powm g 2 N) fuel.
Proof.
  intros N g fuel Hng.
  cbn [miller_walk_from].
  destruct (powm g 2 N =? 1) eqn:Heq.
  - apply Z.eqb_eq in Heq. congruence.
  - reflexivity.
Qed.

Lemma pow2n_add :
  forall k d, pow2n (k + d) = pow2n k * pow2n d.
Proof.
  intros k d. induction d as [|d IH].
  - unfold pow2n. rewrite Nat.add_0_r, Z.pow_0_r, Z.mul_1_r. reflexivity.
  - rewrite Nat.add_succ_r, pow2n_succ, IH, pow2n_succ. ring.
Qed.

Lemma miller_walk_square_powm :
  forall a t k N,
    N <> 0 ->
    0 <= t ->
    powm (powm a (t * pow2n k) N) 2 N = powm a (t * pow2n (S k)) N.
Proof.
  intros a t k N HN Ht.
  rewrite pow2n_succ.
  replace (t * (2 * pow2n k)) with (2 * (t * pow2n k)) by ring.
  symmetry.
  apply powm_square; [exact HN|].
  apply Z.mul_nonneg_nonneg; [exact Ht | pose proof (pow2n_pos k); lia].
Qed.

Lemma miller_walk_powm_t0 :
  forall a t N, powm a (t * pow2n 0) N = powm a t N.
Proof.
  intros. unfold pow2n. rewrite Z.pow_0_r, Z.mul_1_r. reflexivity.
Qed.

Lemma miller_walk_pos :
  forall N M a,
    0 < M ->
    miller_walk N M a =
      miller_walk_from N (powm a (odd_part M) N) (val2 M).
Proof.
  intros N M a HM.
  unfold miller_walk.
  destruct (M <=? 0) eqn:Hle.
  - apply Z.leb_le in Hle. lia.
  - reflexivity.
Qed.

Lemma two_height_ge :
  forall a t n k k',
    1 < n ->
    0 <= t ->
    two_height a t n k ->
    (k <= k')%nat ->
    powm a (t * pow2n k') n = 1.
Proof.
  intros a t n k k' Hn Ht [Hpow _] Hle.
  induction Hle as [|k' Hle IH].
  - exact Hpow.
  - rewrite pow2n_succ.
    replace (t * (2 * pow2n k')) with (2 * (t * pow2n k')) by ring.
    rewrite powm_square by (pose proof (pow2n_pos k'); nia).
    rewrite IH.
    rewrite powm_1_pow by lia.
    apply Z.mod_1_l. lia.
Qed.

Lemma powm_one_of_factors :
  forall a e p q,
    Z.prime p -> Z.prime q -> p <> q ->
    powm a e p = 1 ->
    powm a e q = 1 ->
    powm a e (p * q) = 1.
Proof.
  intros a e p q Hp Hq Hneq Hp1 Hq1.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  assert (Hpdiv : (p | a ^ e - 1)).
  { apply Z.mod_divide; [lia|].
    unfold powm in Hp1.
    rewrite Zminus_mod, Hp1, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity. }
  assert (Hqdiv : (q | a ^ e - 1)).
  { apply Z.mod_divide; [lia|].
    unfold powm in Hq1.
    rewrite Zminus_mod, Hq1, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity. }
  assert (HNdiv : (p * q | a ^ e - 1)).
  { apply divide_by_coprime_product; [| exact Hpdiv | exact Hqdiv].
    apply prime_coprime_distinct; assumption. }
  unfold powm.
  pose proof (Z.div_mod (a ^ e) (p * q) ltac:(nia)) as Hdm.
  set (x := a ^ e mod (p * q)) in *.
  set (quot := a ^ e / (p * q)) in *.
  destruct HNdiv as [k Hk].
  assert (x - 1 = (k - quot) * (p * q)) as Hlin.
  { lia. }
  pose proof (Z.mod_pos_bound (a ^ e) (p * q) ltac:(nia)) as Hb.
  fold x in Hb.
  assert (x - 1 = 0) as Hx.
  { destruct (Z.eq_dec (k - quot) 0) as [Hz | Hnz].
    - lia.
    - assert (Z.abs (x - 1) >= p * q).
      { rewrite Hlin, Z.abs_mul, (Z.abs_eq (p * q)) by nia.
        pose proof (Z.abs_pos (k - quot)). nia. }
      lia. }
  lia.
Qed.

Lemma miller_walk_from_at :
  forall fuel k kmax a t N,
    N <> 0 ->
    0 <= t ->
    (k < kmax)%nat ->
    (kmax <= k + fuel)%nat ->
    powm a (t * pow2n kmax) N = 1 ->
    (forall j, (k < j < kmax)%nat -> powm a (t * pow2n j) N <> 1) ->
    powm a (t * pow2n (kmax - 1)%nat) N <> 1 ->
    powm a (t * pow2n (kmax - 1)%nat) N <> N - 1 ->
    miller_walk_from N (powm a (t * pow2n k) N) fuel =
      Some (Z.gcd (powm a (t * pow2n (kmax - 1)%nat) N - 1) N).
Proof.
  induction fuel as [|fuel IH]; intros k kmax a t N HN Ht Hlt Hfuel Hhit Hmiss Hg1 Hgn1.
  - lia.
  - destruct (Nat.eq_dec (S k) kmax) as [Heq | Hneq].
    + subst kmax.
      rewrite miller_walk_from_S_eq1.
      * replace (S k - 1)%nat with k by lia. reflexivity.
      * rewrite miller_walk_square_powm by (exact HN || exact Ht). exact Hhit.
      * replace (S k - 1)%nat with k in Hg1 by lia. exact Hg1.
      * replace (S k - 1)%nat with k in Hgn1 by lia. exact Hgn1.
    + assert (Hsk : (S k < kmax)%nat) by lia.
      rewrite miller_walk_from_S_neq1.
      * rewrite miller_walk_square_powm by (exact HN || exact Ht).
        apply (IH (S k) kmax a t N).
        -- exact HN.
        -- exact Ht.
        -- exact Hsk.
        -- lia.
        -- exact Hhit.
        -- intros j Hj. apply Hmiss. lia.
        -- exact Hg1.
        -- exact Hgn1.
      * rewrite miller_walk_square_powm by (exact HN || exact Ht).
        apply Hmiss. lia.
Qed.

Lemma miller_walk_powm_neq1_of_local :
  forall a e p q,
    1 < p -> 1 < q ->
    powm a e q <> 1 ->
    powm a e (p * q) <> 1.
Proof.
  intros a e p q Hp Hq Hloc Hn.
  apply Hloc.
  apply (powm_one_mod_factor a e q p); [lia | lia |].
  rewrite Z.mul_comm. exact Hn.
Qed.

Lemma pq_minus_1_mod_p :
  forall p q, 1 < p -> 0 < q -> (p * q - 1) mod p = p - 1.
Proof.
  intros p q Hp Hq.
  replace (p * q - 1) with ((p - 1) + (q - 1) * p) by ring.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

Lemma miller_walk_from_mismatch :
  forall a t p q kmin kmax fuel,
    Z.prime p -> Z.prime q -> p <> q ->
    p <> 2 ->
    0 <= t ->
    two_height a t p kmin ->
    two_height a t q kmax ->
    (kmin < kmax)%nat ->
    (kmax <= fuel)%nat ->
    miller_walk_from (p * q) (powm a t (p * q)) fuel =
      Some (Z.gcd (powm a (t * pow2n (kmax - 1)%nat) (p * q) - 1)
                  (p * q)).
Proof.
  intros a t p q kmin kmax fuel Hp Hq Hneq Hp2 Ht Hpht Hqht Hlt Hfuel.
  pose proof (Z.prime_ge_2 p Hp) as Hpg.
  pose proof (Z.prime_ge_2 q Hq) as Hqg.
  assert (HN : 1 < p * q) by nia.
  set (N := p * q).
  assert (H1N : powm a (t * pow2n kmax) N = 1).
  { unfold N.
    apply powm_one_of_factors; [exact Hp | exact Hq | exact Hneq | |].
    - apply (two_height_ge a t p kmin kmax); [lia | exact Ht | exact Hpht | lia].
    - destruct Hqht as [Hq1 _]. exact Hq1. }
  assert (Hmiss : forall j, (0 < j < kmax)%nat ->
                     powm a (t * pow2n j) N <> 1).
  { intros j Hj.
    unfold N.
    apply miller_walk_powm_neq1_of_local; [lia | lia |].
    destruct Hqht as [_ Hqmin].
    apply Hqmin. lia. }
  assert (Hg1 : powm a (t * pow2n (kmax - 1)%nat) N <> 1).
  { unfold N.
    apply miller_walk_powm_neq1_of_local; [lia | lia |].
    destruct Hqht as [_ Hqmin].
    apply Hqmin. lia. }
  assert (Hgn1 : powm a (t * pow2n (kmax - 1)%nat) N <> N - 1).
  { intro Heq.
    assert (powm a (t * pow2n (kmax - 1)%nat) p = 1) as Hp1.
    { apply (two_height_ge a t p kmin (kmax - 1)%nat);
        [lia | exact Ht | exact Hpht | lia]. }
    assert (powm a (t * pow2n (kmax - 1)%nat) p = p - 1) as Hpm1.
    { unfold powm in Heq |- *.
      transitivity (((a ^ (t * pow2n (kmax - 1)%nat)) mod N) mod p).
      - unfold N. symmetry. apply Z.mod_mod_divide. exists q. ring.
      - rewrite Heq. unfold N. apply pq_minus_1_mod_p; lia. }
    lia. }
  unfold N.
  rewrite <- miller_walk_powm_t0.
  apply (miller_walk_from_at fuel 0 kmax a t (p * q));
    try lia; try assumption.
Qed.

Theorem miller_walk_factors :
  forall R M a kp kq,
    0 < M ->
    Z.divide (rsa_lambda R) M ->
    Z.coprime a (rsa_N R) ->
    rsa_p R <> 2 ->
    rsa_q R <> 2 ->
    two_height a (odd_part M) (rsa_p R) kp ->
    two_height a (odd_part M) (rsa_q R) kq ->
    kp <> kq ->
    exists f,
      miller_walk (rsa_N R) M a = Some f /\
      1 < f /\ f < rsa_N R /\ (f | rsa_N R).
Proof.
  intros R M a kp kq HMpos Hdiv Hcop Hp2 Hq2 Hpht Hqht Hneq.
  pose proof (rsa_N_gt_1 R) as HN.
  pose proof (odd_part_nonneg M ltac:(lia)) as Ht.
  pose proof (miller_height_exists_multiple R M a HMpos Hdiv Hcop)
    as [kp' [kq' [Hlep [Hpht' [Hleq Hqht']]]]].
  pose proof (two_height_unique _ _ _ _ _ Hpht Hpht') as Hpeq.
  pose proof (two_height_unique _ _ _ _ _ Hqht Hqht') as Hqeq.
  subst kp' kq'.
  rewrite miller_walk_pos by exact HMpos.
  destruct (Nat.lt_trichotomy kp kq) as [Hlt | [Heq | Hgt]].
  - unfold rsa_N.
    set (ghit := powm a (odd_part M * pow2n (kq - 1)%nat)
                       (rsa_p R * rsa_q R)).
    rewrite (miller_walk_from_mismatch a (odd_part M)
               (rsa_p R) (rsa_q R) kp kq (val2 M));
      try assumption; try apply rsa_p_prime; try apply rsa_q_prime;
      try apply rsa_distinct; try lia.
    exists (Z.gcd (ghit - 1) (rsa_p R * rsa_q R)).
    split; [unfold ghit; reflexivity|].
    pose proof (miller_witness_factors R a ghit Hcop) as Hw.
    unfold rsa_N in Hw.
    apply Hw.
    unfold miller_splits, ghit.
    split.
    + rewrite miller_walk_square_powm by
        (exact Ht || (unfold rsa_N in HN; lia)).
      replace (S (kq - 1)) with kq by lia.
      apply powm_one_of_factors;
        [apply rsa_p_prime | apply rsa_q_prime | apply rsa_distinct | |].
      * apply (two_height_ge a (odd_part M) (rsa_p R) kp kq);
          [pose proof (Z.prime_ge_2 _ (rsa_p_prime R)); lia
          | exact Ht | exact Hpht | lia].
      * destruct Hqht as [Hq1 _]. exact Hq1.
    + split.
      * intro Hg.
        unfold ghit, powm in Hg.
        rewrite Z.mod_mod in Hg
          by (pose proof (Z.prime_ge_2 _ (rsa_p_prime R));
              pose proof (Z.prime_ge_2 _ (rsa_q_prime R)); nia).
        assert (powm a (odd_part M * pow2n (kq - 1)%nat)
                     (rsa_p R * rsa_q R) <> 1) as Hne.
        { apply miller_walk_powm_neq1_of_local;
            [pose proof (Z.prime_ge_2 _ (rsa_p_prime R)); lia
            | pose proof (Z.prime_ge_2 _ (rsa_q_prime R)); lia |].
          destruct Hqht as [_ Hqmin]. apply Hqmin. lia. }
        unfold powm in Hne. congruence.
      * intro Hg.
        unfold ghit, powm in Hg.
        rewrite Z.mod_mod in Hg
          by (pose proof (Z.prime_ge_2 _ (rsa_p_prime R));
              pose proof (Z.prime_ge_2 _ (rsa_q_prime R)); nia).
        assert (powm a (odd_part M * pow2n (kq - 1)%nat) (rsa_p R) = 1)
          as Hp1.
        { apply (two_height_ge a (odd_part M) (rsa_p R) kp (kq - 1)%nat);
            [pose proof (Z.prime_ge_2 _ (rsa_p_prime R)); lia
            | exact Ht | exact Hpht | lia]. }
        assert (powm a (odd_part M * pow2n (kq - 1)%nat) (rsa_p R) =
                  rsa_p R - 1) as Hpm1.
        { unfold powm in Hg |- *.
          transitivity
            (((a ^ (odd_part M * pow2n (kq - 1)%nat))
                mod (rsa_p R * rsa_q R)) mod rsa_p R).
          - symmetry. apply Z.mod_mod_divide. exists (rsa_q R). ring.
          - rewrite Hg. apply pq_minus_1_mod_p;
              [pose proof (Z.prime_ge_2 _ (rsa_p_prime R)); lia
              | pose proof (Z.prime_ge_2 _ (rsa_q_prime R)); lia]. }
        lia.
  - congruence.
  - unfold rsa_N.
    set (ghit := powm a (odd_part M * pow2n (kp - 1)%nat)
                       (rsa_p R * rsa_q R)).
    rewrite (Z.mul_comm (rsa_p R) (rsa_q R)).
    rewrite (miller_walk_from_mismatch a (odd_part M)
               (rsa_q R) (rsa_p R) kq kp (val2 M));
      try assumption; try apply rsa_q_prime; try apply rsa_p_prime;
      try (apply not_eq_sym, rsa_distinct); try lia.
    exists (Z.gcd (ghit - 1) (rsa_p R * rsa_q R)).
    split; [unfold ghit;
            rewrite (Z.mul_comm (rsa_q R) (rsa_p R)),
                    (Z.mul_comm (odd_part M) (pow2n (kp - 1)%nat));
            reflexivity|].
    pose proof (miller_witness_factors R a ghit Hcop) as Hw.
    unfold rsa_N in Hw.
    rewrite (Z.mul_comm (rsa_q R) (rsa_p R)).
    apply Hw.
    unfold miller_splits, ghit.
    split.
    + rewrite miller_walk_square_powm by
        (exact Ht || (unfold rsa_N in HN; lia)).
      replace (S (kp - 1)) with kp by lia.
      apply powm_one_of_factors;
        [apply rsa_p_prime | apply rsa_q_prime | apply rsa_distinct | |].
      * destruct Hpht as [Hp1 _]. exact Hp1.
      * apply (two_height_ge a (odd_part M) (rsa_q R) kq kp);
          [pose proof (Z.prime_ge_2 _ (rsa_q_prime R)); lia
          | exact Ht | exact Hqht | lia].
    + split.
      * intro Hg.
        unfold ghit, powm in Hg.
        rewrite Z.mod_mod in Hg
          by (pose proof (Z.prime_ge_2 _ (rsa_p_prime R));
              pose proof (Z.prime_ge_2 _ (rsa_q_prime R)); nia).
        assert (powm a (odd_part M * pow2n (kp - 1)%nat)
                     (rsa_q R * rsa_p R) <> 1) as Hne.
        { apply miller_walk_powm_neq1_of_local;
            [pose proof (Z.prime_ge_2 _ (rsa_q_prime R)); lia
            | pose proof (Z.prime_ge_2 _ (rsa_p_prime R)); lia |].
          destruct Hpht as [_ Hpmin]. apply (Hpmin (kp - 1)%nat). lia. }
        unfold powm in Hne.
        rewrite (Z.mul_comm (rsa_q R) (rsa_p R)) in Hne.
        congruence.
      * intro Hg.
        unfold ghit, powm in Hg.
        rewrite Z.mod_mod in Hg
          by (pose proof (Z.prime_ge_2 _ (rsa_p_prime R));
              pose proof (Z.prime_ge_2 _ (rsa_q_prime R)); nia).
        assert (powm a (odd_part M * pow2n (kp - 1)%nat) (rsa_q R) = 1)
          as Hq1loc.
        { apply (two_height_ge a (odd_part M) (rsa_q R) kq (kp - 1)%nat);
            [pose proof (Z.prime_ge_2 _ (rsa_q_prime R)); lia
            | exact Ht | exact Hqht | lia]. }
        assert (powm a (odd_part M * pow2n (kp - 1)%nat) (rsa_q R) =
                  rsa_q R - 1) as Hqm1.
        { unfold powm in Hg |- *.
          transitivity
            (((a ^ (odd_part M * pow2n (kp - 1)%nat))
                mod (rsa_p R * rsa_q R)) mod rsa_q R).
          - symmetry. apply Z.mod_mod_divide. exists (rsa_p R). ring.
          - rewrite Hg. rewrite (Z.mul_comm (rsa_p R) (rsa_q R)).
            apply pq_minus_1_mod_p;
              [pose proof (Z.prime_ge_2 _ (rsa_q_prime R)); lia
              | pose proof (Z.prime_ge_2 _ (rsa_p_prime R)); lia]. }
        lia.
Qed.

(** ** Miller for distinct odd primes, without an [RSAInstance]

    [e = λ+1], [d = 1] is a dummy instance so [miller_walk_factors]
    applies.  Mixed [√1] is a hitting miller base for every even
    [M]: [g₀] is already mixed, so the first square splits.
    [miller_search] therefore returns [Some] without hardcoding
    base 2.  Not the extraction nameds: miller-from-[λ] still
    ignores Solve.  Cross-confirmed by [cas/255]. *)

Lemma odd_prime_pred_even :
  forall p, Z.prime p -> p <> 2 -> Z.Even (p - 1).
Proof.
  intros p Hp Hp2.
  pose proof (Z.prime_ge_2 p Hp).
  destruct (Z.Even_or_Odd p) as [[k Hk] | [k Hk]].
  - subst p.
    pose proof Hp as Hpr. apply prime_alt in Hpr.
    destruct Hpr as [_ Hn].
    assert (1 < 2 < 2 * k) by lia.
    specialize (Hn 2 ltac:(lia)).
    apply rel_prime_iff_coprime in Hn.
    unfold Z.coprime in Hn.
    rewrite (Z.gcd_mul_diag_l 2 k) in Hn by lia.
    lia.
  - exists k. lia.
Qed.

Lemma lambda_odd_primes_even :
  forall p q,
    Z.prime p -> Z.prime q -> p <> 2 -> q <> 2 ->
    Z.Even (lambda_semiprime p q).
Proof.
  intros p q Hp Hq Hp2 Hq2.
  pose proof (odd_prime_pred_even p Hp Hp2) as [k Hk].
  unfold lambda_semiprime.
  assert (2 | p - 1) by (exists k; lia).
  assert (2 | Z.lcm (p - 1) (q - 1)).
  { apply Z.divide_trans with (p - 1); [exact H | apply Z.divide_lcm_l]. }
  destruct H0 as [t Ht]. exists t. lia.
Qed.

Lemma divide_even_even :
  forall lam M,
    Z.Even lam ->
    Z.divide lam M ->
    Z.Even M.
Proof.
  intros lam M [k Hk] [t Ht].
  subst lam. exists (t * k). lia.
Qed.

Lemma lambda_odd_primes_gt_1 :
  forall p q,
    Z.prime p -> Z.prime q -> p <> 2 -> q <> 2 ->
    1 < lambda_semiprime p q.
Proof.
  intros p q Hp Hq Hp2 Hq2.
  unfold lambda_semiprime.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  assert (2 <= p - 1) by lia.
  apply Z.lt_le_trans with (p - 1); [lia|].
  apply Z.divide_pos_le.
  - pose proof (lambda_semiprime_pos p q Hp Hq).
    unfold lambda_semiprime in H2. lia.
  - apply Z.divide_lcm_l.
Qed.

Lemma rsa_instance_of_odd_primes :
  forall p q,
    Z.prime p -> Z.prime q -> p <> q ->
    p <> 2 -> q <> 2 ->
    { R : RSAInstance | rsa_p R = p /\ rsa_q R = q }.
Proof.
  intros p q Hp Hq Hneq Hp2 Hq2.
  pose proof (lambda_semiprime_pos p q Hp Hq) as Hlam.
  pose proof (lambda_odd_primes_gt_1 p q Hp Hq Hp2 Hq2) as Hgt.
  unshelve eexists.
  - refine {| rsa_p := p; rsa_q := q;
              rsa_e := lambda_semiprime p q + 1;
              rsa_d := 1;
              rsa_p_prime := Hp; rsa_q_prime := Hq;
              rsa_distinct := Hneq |}.
    + unfold Z.coprime.
      rewrite Z.gcd_comm.
      rewrite <- (Z.gcd_mod (lambda_semiprime p q + 1)
                            (lambda_semiprime p q)) by lia.
      replace (lambda_semiprime p q + 1)
        with (1 + 1 * lambda_semiprime p q) by lia.
      rewrite Z.mod_add, Z.mod_1_l by lia.
      apply Z.gcd_1_l.
    + rewrite Z.mul_1_r.
      replace (lambda_semiprime p q + 1)
        with (1 + 1 * lambda_semiprime p q) by lia.
      rewrite Z.mod_add, Z.mod_1_l by lia.
      reflexivity.
    + lia.
    + lia.
  - split; reflexivity.
Qed.

Theorem miller_walk_factors_semiprime :
  forall p q M a kp kq,
    Z.prime p -> Z.prime q -> p <> q ->
    p <> 2 -> q <> 2 ->
    0 < M ->
    Z.divide (lambda_semiprime p q) M ->
    Z.coprime a (p * q) ->
    two_height a (odd_part M) p kp ->
    two_height a (odd_part M) q kq ->
    kp <> kq ->
    exists f,
      miller_walk (p * q) M a = Some f /\
      Problem_Factor (p * q) f.
Proof.
  intros p q M a kp kq Hp Hq Hneq Hp2 Hq2 HMpos Hdiv Hcop Hpht Hqht Hneqk.
  destruct (rsa_instance_of_odd_primes p q Hp Hq Hneq Hp2 Hq2)
    as [R [HRp HRq]].
  assert (HlamR : rsa_lambda R = lambda_semiprime p q).
  { unfold rsa_lambda. rewrite HRp, HRq. reflexivity. }
  assert (HNR : rsa_N R = p * q).
  { unfold rsa_N. rewrite HRp, HRq. reflexivity. }
  destruct (miller_walk_factors R M a kp kq HMpos)
    as [f [Hwalk [Hf1 [Hf2 Hfd]]]].
  - rewrite HlamR. exact Hdiv.
  - rewrite HNR. exact Hcop.
  - rewrite HRp. exact Hp2.
  - rewrite HRq. exact Hq2.
  - rewrite HRp. exact Hpht.
  - rewrite HRq. exact Hqht.
  - exact Hneqk.
  - exists f.
    rewrite HNR in Hwalk, Hf2, Hfd.
    split; [exact Hwalk|].
    unfold Problem_Factor. split; [lia | exact Hfd].
Qed.

Lemma even_pos_val2_ge_1 :
  forall M, 0 < M -> Z.Even M -> (1 <= val2 M)%nat.
Proof.
  intros M HM Hev.
  destruct (val2 M) as [|s] eqn:Hs; [| lia].
  pose proof (split2_of_reconstructs M ltac:(lia)) as Hr.
  rewrite Hs, Z.pow_0_r, Z.mul_1_l in Hr.
  pose proof (odd_part_odd_or_zero M ltac:(lia)) as [Hodd | Hz].
  - rewrite <- Hr in Hodd.
    pose proof (proj2 (Z.even_spec M) Hev) as He.
    rewrite <- Z.negb_odd in He.
    rewrite Hodd in He.
    discriminate.
  - rewrite <- Hr in Hz. lia.
Qed.

Lemma sqrt1_pm_mod_range :
  forall p q,
    Z.prime p -> Z.prime q -> p <> q ->
    p <> 2 -> q <> 2 ->
    let N := p * q in
    let a := sqrt1_pm p q mod N in
    2 <= a <= N - 2.
Proof.
  intros p q Hp Hq Hneq Hp2 Hq2 N a.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  assert (HN : 1 < N) by (unfold N; nia).
  unfold a, N.
  pose proof (Z.mod_pos_bound (sqrt1_pm p q) (p * q) ltac:(nia)) as [Hlo Hhi].
  pose proof (mixed_pm_not_one p q Hp Hq Hneq Hq2) as Hn1.
  pose proof (mixed_pm_not_minus1 p q Hp Hq Hneq Hp2) as Hnm1.
  assert (sqrt1_pm p q mod (p * q) <> 0) as Hnz.
  { intro Hz.
    pose proof (crt2_mod p q 1 (q - 1) Hp Hq Hneq) as [Hp1 _].
    unfold sqrt1_pm in Hp1, Hz.
    rewrite <- (mod_mod_of_factor (crt2 p q 1 (q - 1)) q p) in Hp1 by lia.
    rewrite Z.mul_comm, Hz, Z.mod_0_l in Hp1 by lia.
    rewrite Z.mod_1_l in Hp1 by lia. lia. }
  lia.
Qed.

Theorem miller_walk_mixed_sqrt1 :
  forall p q M,
    Z.prime p -> Z.prime q -> p <> q ->
    p <> 2 -> q <> 2 ->
    0 < M ->
    Z.Even M ->
    let N := p * q in
    let a := sqrt1_pm p q mod N in
    exists f,
      miller_walk N M a = Some f /\
      Problem_Factor N f.
Proof.
  intros p q M Hp Hq Hneq Hp2 Hq2 HM Hev N a.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  assert (HN : 1 < N) by (unfold N; nia).
  pose proof (four_sqrt1 p q Hp Hq Hneq) as [_ [_ [Hsq _]]].
  pose proof (odd_part_nonneg M ltac:(lia)) as Ht.
  pose proof (odd_part_odd_or_zero M ltac:(lia)) as [Hodd | Hz].
  2: { pose proof (odd_part_pos M HM). lia. }
  pose proof (even_pos_val2_ge_1 M HM Hev) as Hs.
  pose proof (sqrt1_pm_mod_range p q Hp Hq Hneq Hp2 Hq2) as Hrng.
  unfold N, a in Hrng.
  set (ar := sqrt1_pm p q mod (p * q)).
  fold ar in Hrng.
  assert (Hsqa : powm ar 2 (p * q) = 1).
  { unfold ar. rewrite powm_mod_base by lia. exact Hsq. }
  assert (Hg0 : powm ar (odd_part M) (p * q) = ar).
  { transitivity (ar mod (p * q)).
    - apply powm_odd_of_square_one;
        [lia | exact Ht | apply (proj1 (Z.odd_spec _)); exact Hodd | exact Hsqa].
    - apply Z.mod_small. unfold ar. apply Z.mod_pos_bound. lia. }
  assert (Har1 : ar <> 1).
  { unfold ar. apply mixed_pm_not_one; assumption. }
  assert (Harn1 : ar <> p * q - 1).
  { unfold ar. apply mixed_pm_not_minus1; assumption. }
  assert (Hwalk : miller_walk (p * q) M ar =
                    Some (Z.gcd (ar - 1) (p * q))).
  { rewrite miller_walk_pos by exact HM.
    rewrite Hg0.
    destruct (val2 M) as [|s] eqn:Hsval; [lia|].
    apply miller_walk_from_S_eq1; [exact Hsqa | exact Har1 | exact Harn1]. }
  unfold N, a.
  fold ar.
  exists (Z.gcd (ar - 1) (p * q)).
  split; [exact Hwalk|].
  pose proof (miller_walk_some_factors p q M ar
                (Z.gcd (ar - 1) (p * q)) Hp Hq Hneq Hwalk) as Hfac.
  destruct Hfac as [H1 [H2 H3]].
  unfold Problem_Factor. split; [lia | exact H3].
Qed.

Theorem miller_search_hits_semiprime :
  forall p q M,
    Z.prime p -> Z.prime q -> p <> q ->
    p <> 2 -> q <> 2 ->
    0 < M ->
    Z.Even M ->
    exists a f,
      miller_search (p * q) M = Some (a, f) /\
      2 <= a <= p * q - 2 /\
      Problem_Factor (p * q) f.
Proof.
  intros p q M Hp Hq Hneq Hp2 Hq2 HM Hev.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  assert (HN : 3 < p * q) by nia.
  destruct (miller_walk_mixed_sqrt1 p q M Hp Hq Hneq Hp2 Hq2 HM Hev)
    as [f [Hwalk _Hf]].
  pose proof (sqrt1_pm_mod_range p q Hp Hq Hneq Hp2 Hq2) as Hrng.
  destruct (miller_search_hits_if (p * q) M
              (sqrt1_pm p q mod (p * q)) f Hwalk Hrng HN)
    as [a [f' [Hs Hle]]].
  exists a, f'.
  split; [exact Hs|].
  split; [destruct Hle; destruct Hrng; lia|].
  unfold miller_search in Hs.
  apply miller_search_from_some_walk in Hs.
  pose proof (miller_walk_some_factors p q M a f' Hp Hq Hneq Hs) as Hfac.
  destruct Hfac as [H1 [H2 H3]].
  unfold Problem_Factor. split; [lia | exact H3].
Qed.

