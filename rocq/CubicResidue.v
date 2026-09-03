From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.QuadRecip.
Require Import RSA.
Require Import Hardness.
Require Import Order.

Open Scope Z_scope.

(** * Cubic residuosity when cubing is not a permutation

    If [gcd(3, p−1) = 1] then [x ↦ x³] is invertible on [(Z/pZ)*]
    (Bézout).  If [3 | p−1] then a cube [x³] satisfies
    [a^{(p−1)/3} ≡ 1 (mod p)] by Fermat.  That is the cubic
    analogue of Euler's criterion in one direction.  The converse
    ([a^{(p−1)/3} ≡ 1] ⇒ cube) uses a primitive root
    ([primitive_root_generates], [cas/154]).  On an RSA instance
    [e = 3] is *forbidden* precisely when [3 | λ], so the cubic
    decision problem is live exactly when textbook RSA at [e = 3]
    is not.

    Cubic residuosity of [N = pq] is CRT of the local cubes
    ([cube_N_iff_both]).  [a^{λ/3} ≡ 1] is necessary when [3 | λ]
    and not sufficient: [7^{12} ≡ 1 (mod 247)] but [7] is not a
    cube ([cas/155], named extra [13×19]).  On the pin, [gcd(3,λ)=1]
    so every unit is a cube.

    Cross-confirmed by [cas/86_cubic_residue.gp],
    [cas/154_cube_euler.gp], and [cas/155_cube_modn.gp]. *)

Definition is_cube (a p : Z) : Prop :=
  exists x, powm x 3 p = a mod p.

Theorem cubing_invertible_on_units :
  forall a p d,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    (3 * d) mod (p - 1) = 1 ->
    0 <= d ->
    powm (powm a d p) 3 p = a mod p.
Proof.
  intros a p d Hp Hne Hcop Hinv Hd.
  pose proof (Z.prime_ge_2 p Hp).
  assert (1 < p - 1) by lia.
  assert (0 <= (3 * d) / (p - 1)) by (apply Z.div_pos; nia).
  rewrite <- powm_mul_r by lia.
  rewrite (Z.mul_comm d 3).
  pose proof (Z.div_mod (3 * d) (p - 1) ltac:(lia)) as Hdm.
  rewrite Hinv in Hdm.
  rewrite Hdm.
  rewrite powm_add_r by nia.
  rewrite Z.mul_comm.
  rewrite powm_mul_r by nia.
  rewrite fermat_coprime by assumption.
  rewrite powm_1_pow by nia.
  rewrite powm_1_r by lia.
  rewrite Z.mod_1_l by lia.
  rewrite Z.mul_1_r.
  apply Z.mod_mod; lia.
Qed.

Theorem cube_root_map_is_cube :
  forall a p d,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    (3 * d) mod (p - 1) = 1 ->
    0 <= d ->
    is_cube a p.
Proof.
  intros a p d Hp Hne Hcop Hinv Hd.
  exists (powm a d p).
  apply cubing_invertible_on_units; assumption.
Qed.

Theorem cube_euler_one_direction :
  forall a p x,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    (3 | p - 1) ->
    powm x 3 p = a mod p ->
    powm a ((p - 1) / 3) p = 1.
Proof.
  intros a p x Hp Hne Hcop Hdiv Hcube.
  pose proof (Z.prime_ge_2 p Hp).
  assert (0 <= (p - 1) / 3) as Hn.
  { destruct Hdiv as [k Hk].
    assert (0 < k) by nia.
    rewrite Hk. rewrite Z.div_mul by lia. lia. }
  unfold powm in Hcube |- *.
  rewrite <- (Z.mod_pow_l a ((p - 1) / 3) p) by lia.
  rewrite <- Hcube.
  rewrite Z.mod_pow_l by lia.
  replace ((x ^ 3) ^ ((p - 1) / 3)) with (x ^ (p - 1)).
  2:{ symmetry. rewrite <- Z.pow_mul_r by lia.
      destruct Hdiv as [k Hk].
      assert (0 <= k) by nia.
      rewrite Hk. rewrite (Z.div_mul k 3) by lia.
      f_equal. apply Z.mul_comm. }
  fold (powm x (p - 1) p).
  assert (Z.coprime x p) as Hxp.
  { rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hp|].
    intro Hpx.
    apply mods_eq_iff_divides in Hcube; [| lia].
    assert (p | x * x * x) by (eapply Z.divide_mul_l; eapply Z.divide_mul_l; exact Hpx).
    assert (p | a).
    { destruct Hcube as [t Ht]. destruct H0 as [s Hs]. exists (s - t). lia. }
    unfold Z.coprime in Hcop.
    assert (p | Z.gcd a p) by (apply Z.gcd_greatest; [exact H1 | apply Z.divide_refl]).
    rewrite Hcop in H2. apply Z.divide_1_r in H2. lia. }
  apply fermat_coprime; assumption.
Qed.

Theorem three_divides_lambda_forbids_e3 :
  forall p q,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    (3 | lambda_semiprime p q) ->
    ~ Z.coprime 3 (lambda_semiprime p q).
Proof.
  intros p q Hp Hq Hp2 Hq2 Hdiv Hcop.
  unfold Z.coprime in Hcop.
  destruct Hdiv as [k Hk].
  rewrite Hk, Z.mul_comm in Hcop.
  assert (3 | Z.gcd 3 (3 * k)).
  { apply Z.gcd_greatest; [apply Z.divide_refl | exists k; ring]. }
  rewrite Hcop in H. apply Z.divide_1_r in H. lia.
Qed.

Theorem cube_euler_converse :
  forall a p,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    (3 | p - 1) ->
    powm a ((p - 1) / 3) p = 1 ->
    is_cube a p.
Proof.
  intros a p Hp Hne Hcop Hdiv Heul.
  pose proof (Z.prime_ge_2 p Hp).
  destruct Hdiv as [t Ht].
  assert (0 < t) as Htpos by nia.
  assert ((p - 1) / 3 = t) as Hquot.
  { rewrite Ht. apply Z.div_mul. lia. }
  destruct (primitive_root_exists p Hp) as [g [Hg Hor]].
  destruct (primitive_root_generates p g a Hp Hg Hor Hcop)
    as [k [Hk Hkpow]].
  assert (0 <= (p - 1) / 3) as Hn by (rewrite Hquot; lia).
  assert (powm g (k * ((p - 1) / 3)) p = 1) as Hg1.
  { rewrite powm_mul_r by lia.
    rewrite Hkpow.
    rewrite powm_mod_base by lia.
    exact Heul. }
  assert ((p - 1 | k * ((p - 1) / 3))) as Hdivk.
  { apply (proj2 (order_iff_divides p g (p - 1) (k * ((p - 1) / 3))
                    ltac:(lia) ltac:(nia) Hor)).
    exact Hg1. }
  rewrite Hquot in Hdivk.
  destruct Hdivk as [q Hq].
  assert (k = 3 * q) as Hk3.
  { enough (k * t = (3 * q) * t) by nia.
    rewrite Hq. nia. }
  assert (0 <= q) as Hqpos by nia.
  exists (powm g q p).
  rewrite <- powm_mul_r by lia.
  rewrite Z.mul_comm, <- Hk3.
  rewrite Hkpow. reflexivity.
Qed.

Theorem cube_euler_iff :
  forall a p,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    (3 | p - 1) ->
    is_cube a p <-> powm a ((p - 1) / 3) p = 1.
Proof.
  intros a p Hp Hne Hcop Hdiv. split.
  - intros [x Hx]. apply (cube_euler_one_direction a p x); assumption.
  - apply cube_euler_converse; assumption.
Qed.

Lemma cube_N_implies_local :
  forall a p q,
    Z.prime p ->
    Z.prime q ->
    is_cube a (p * q) ->
    is_cube a p /\ is_cube a q.
Proof.
  intros a p q Hp Hq [x Hx].
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  split.
  - exists x.
    pose proof (powm_reduce_factor x 3 p q ltac:(lia) ltac:(lia) ltac:(lia)) as Hr.
    rewrite Hx in Hr.
    assert ((a mod (p * q)) mod p = a mod p) as Hred.
    { apply Z.mod_mod_divide. exists q. ring. }
    rewrite Hred in Hr. symmetry; exact Hr.
  - exists x.
    pose proof (powm_reduce_factor x 3 q p ltac:(lia) ltac:(lia) ltac:(lia)) as Hr.
    rewrite Z.mul_comm in Hr.
    rewrite Hx in Hr.
    assert ((a mod (p * q)) mod q = a mod q) as Hred.
    { apply Z.mod_mod_divide. exists p. ring. }
    rewrite Hred in Hr. symmetry; exact Hr.
Qed.

Lemma cube_N_of_local :
  forall a p q,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    is_cube a p ->
    is_cube a q ->
    is_cube a (p * q).
Proof.
  intros a p q Hp Hq Hneq [xp Hxp] [xq Hxq].
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  pose proof (prime_coprime_distinct p q Hp Hq Hneq) as Hcop.
  set (x := Z.combinecong p q xp xq).
  pose proof (Z.combinecong_sound_coprime p q xp xq Hcop) as [Hxp' Hxq'].
  exists x.
  unfold powm.
  apply crt_mod_eq; [exact Hp | exact Hq | exact Hneq | | ].
  - rewrite <- Z.mod_pow_l by lia.
    unfold x. rewrite Hxp'.
    rewrite Z.mod_pow_l by lia.
    fold (powm xp 3 p). exact Hxp.
  - rewrite <- Z.mod_pow_l by lia.
    unfold x. rewrite Hxq'.
    rewrite Z.mod_pow_l by lia.
    fold (powm xq 3 q). exact Hxq.
Qed.

Theorem cube_N_iff_both :
  forall a p q,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    is_cube a (p * q) <-> (is_cube a p /\ is_cube a q).
Proof.
  intros a p q Hp Hq Hneq. split.
  - apply cube_N_implies_local; assumption.
  - intros [Hp3 Hq3]. apply cube_N_of_local; assumption.
Qed.

Lemma cube_root_coprime :
  forall x a n,
    1 < n ->
    Z.coprime a n ->
    powm x 3 n = a mod n ->
    Z.coprime x n.
Proof.
  intros x a n Hn Ha Hx.
  unfold Z.coprime in *.
  unfold powm in Hx.
  apply mods_eq_iff_divides in Hx; [| lia].
  assert (Z.gcd x n | a).
  { assert (x ^ 3 = x * x * x) as Hcube.
    { change 3 with (Z.succ (Z.succ 1)).
      rewrite !Z.pow_succ_r by lia.
      rewrite Z.pow_1_r. ring. }
    assert (Z.gcd x n | (x * x * x)).
    { apply Z.divide_mul_l. apply Z.divide_mul_l. apply Z.gcd_divide_l. }
    rewrite <- Hcube in H.
    assert (Z.gcd x n | n) by apply Z.gcd_divide_r.
    assert (Z.gcd x n | (x ^ 3 - a)).
    { apply Z.divide_trans with n; [exact H0 | exact Hx]. }
    destruct H as [u Hu]. destruct H1 as [v Hv].
    exists (u - v). nia. }
  assert (Z.gcd x n | Z.gcd a n).
  { apply Z.gcd_greatest; [exact H | apply Z.gcd_divide_r]. }
  rewrite Ha in H0. apply Z.divide_1_r in H0.
  pose proof (Z.gcd_nonneg x n). lia.
Qed.

Theorem cube_euler_lambda_necessary :
  forall a p q,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    Z.coprime a (p * q) ->
    (3 | lambda_semiprime p q) ->
    is_cube a (p * q) ->
    powm a (lambda_semiprime p q / 3) (p * q) = 1.
Proof.
  intros a p q Hp Hq Hneq Hcop Hdiv [x Hx].
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  pose proof (lambda_semiprime_pos p q Hp Hq).
  assert (1 < p * q) by nia.
  assert (Z.coprime x (p * q)) as Hcx.
  { apply (cube_root_coprime x a (p * q)); [lia | exact Hcop | exact Hx]. }
  destruct Hdiv as [t Ht].
  assert (lambda_semiprime p q / 3 = t) as Hquot.
  { rewrite Ht. apply Z.div_mul. lia. }
  rewrite Hquot.
  rewrite <- (powm_mod_base a t (p * q)) by lia.
  rewrite <- Hx.
  rewrite <- powm_mul_r by (try lia; nia).
  replace (3 * t) with (lambda_semiprime p q) by (rewrite Ht; ring).
  apply carmichael_semiprime; assumption.
Qed.

Lemma prime_7_cubic : Z.prime 7.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6) by lia.
  intuition subst; reflexivity.
Qed.

Lemma prime_13 : Z.prime 13.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/
          n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
          n = 11 \/ n = 12) by lia.
  intuition subst; reflexivity.
Qed.

Lemma prime_19 : Z.prime 19.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/
          n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
          n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/
          n = 16 \/ n = 17 \/ n = 18) by lia.
  intuition subst; reflexivity.
Qed.

Theorem cube_mixed_5_not_global :
  is_cube 5 13 /\ ~ is_cube 5 7 /\ ~ is_cube 5 91.
Proof.
  split.
  - apply cube_euler_converse; [exact prime_13 | lia | vm_compute; reflexivity | exists 4; lia |].
    vm_compute. reflexivity.
  - split.
    + intro Hc.
      apply (proj1 (cube_euler_iff 5 7 prime_7_cubic ltac:(lia)
                      ltac:(vm_compute; reflexivity) ltac:(exists 2; lia))) in Hc.
      vm_compute in Hc. discriminate.
    + intro Hc. change 91 with (13 * 7) in Hc.
      apply cube_N_implies_local in Hc; [| exact prime_13 | exact prime_7_cubic].
      destruct Hc as [_ Hq5].
      apply (proj1 (cube_euler_iff 5 7 prime_7_cubic ltac:(lia)
                      ltac:(vm_compute; reflexivity) ltac:(exists 2; lia))) in Hq5.
      vm_compute in Hq5. discriminate.
Qed.

Theorem cube_euler_lambda_not_sufficient_247 :
  Z.coprime 7 247 /\
  powm 7 (lambda_semiprime 13 19 / 3) 247 = 1 /\
  ~ is_cube 7 247.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  intro Hc. change 247 with (13 * 19) in Hc.
  apply cube_N_implies_local in Hc; [| exact prime_13 | exact prime_19].
  destruct Hc as [Hp7 _].
  apply (proj1 (cube_euler_iff 7 13 prime_13 ltac:(lia)
                  ltac:(vm_compute; reflexivity) ltac:(exists 4; lia))) in Hp7.
  vm_compute in Hp7. discriminate.
Qed.

Theorem pin_units_are_cubes :
  forall a, Z.coprime a 187 -> is_cube a 187.
Proof.
  intros a Hcop.
  change 187 with (11 * 17) in Hcop |- *.
  apply coprime_semiprime in Hcop; [| exact prime_11 | exact prime_17 | lia].
  destruct Hcop as [Hap Haq].
  apply cube_N_of_local; [exact prime_11 | exact prime_17 | lia | | ].
  - apply (cube_root_map_is_cube a 11 7 prime_11 ltac:(lia) Hap);
      [vm_compute; reflexivity | lia].
  - apply (cube_root_map_is_cube a 17 11 prime_17 ltac:(lia) Haq);
      [vm_compute; reflexivity | lia].
Qed.
