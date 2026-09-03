From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.QuadRecip.
Require Import RSA.
Require Import Hardness.
Require Import UnknownOrder.
Require Import Order.
Require Import PollardP1.

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

    The cubic character [a^{(p−1)/3}] takes values in [μ₃]; the
    kernel of cubing is [{1, ω, ω²}] locally and CRT of those
    pairs on [N=pq] ([cas/156]).  Pin kernel is trivial.
    Mixed kernel elements split [N] via [(x−1)] and [Φ₃(x)];
    diagonal leftover does not ([mixed_mu3_splits], [cas/160]).

    Cross-confirmed by [cas/86_cubic_residue.gp],
    [cas/154_cube_euler.gp], [cas/155_cube_modn.gp],
    [cas/156_cube_char.gp], and [cas/160_mu3_split.gp]. *)

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

Definition cube_char (a p : Z) : Z := powm a ((p - 1) / 3) p.

Lemma omega_from_primitive_root :
  forall p g,
    Z.prime p ->
    Z.coprime g p ->
    is_order p g (p - 1) ->
    (3 | p - 1) ->
    is_order p (powm g ((p - 1) / 3) p) 3.
Proof.
  intros p g Hp Hg Hor Hdiv.
  pose proof (Z.prime_ge_2 p Hp).
  apply (order_of_divisor_power p g (p - 1) 3); [lia | lia | exact Hdiv | exact Hor].
Qed.

Lemma primitive_3rd_root_cyclotomic :
  forall omega p,
    Z.prime p ->
    powm omega 3 p = 1 ->
    omega mod p <> 1 ->
    (omega * omega + omega + 1) mod p = 0.
Proof.
  intros omega p Hp Hmu Hne.
  pose proof (Z.prime_ge_2 p Hp).
  unfold powm in Hmu.
  rewrite <- (Z.mod_1_l p) in Hmu by lia.
  apply mods_eq_iff_divides in Hmu; [| lia].
  assert (omega ^ 3 - 1 = (omega - 1) * (omega * omega + omega + 1)) as Hfact.
  { change 3 with (Z.succ (Z.succ 1)).
    rewrite !Z.pow_succ_r by lia. rewrite Z.pow_1_r. ring. }
  rewrite Hfact in Hmu.
  apply Z.gauss in Hmu.
  2: { change (Z.coprime p (omega - 1)).
       apply Z.coprime_prime_l_iff; [exact Hp|].
       intro Hdiv. apply Hne.
       rewrite <- (Z.mod_1_l p) by lia.
       apply mods_eq_iff_divides; [lia | exact Hdiv]. }
  apply Z.mod_divide in Hmu; [| lia]. exact Hmu.
Qed.

Lemma cube_char_cubed_one :
  forall a p,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    (3 | p - 1) ->
    powm (cube_char a p) 3 p = 1.
Proof.
  intros a p Hp Hne Hcop Hdiv.
  pose proof (Z.prime_ge_2 p Hp).
  unfold cube_char.
  destruct Hdiv as [t Ht].
  assert ((p - 1) / 3 = t) as Hquot.
  { rewrite Ht. apply Z.div_mul. lia. }
  rewrite Hquot.
  rewrite <- powm_mul_r by (try lia; nia).
  rewrite <- Ht.
  apply fermat_coprime; assumption.
Qed.

Lemma cube_char_mul :
  forall a b p,
    1 < p ->
    (3 | p - 1) ->
    cube_char (a * b) p = (cube_char a p * cube_char b p) mod p.
Proof.
  intros a b p Hp Hdiv.
  unfold cube_char.
  destruct Hdiv as [t Ht].
  assert (0 <= (p - 1) / 3) by (rewrite Ht; apply Z.div_pos; nia).
  apply powm_mul_base; lia.
Qed.

Lemma mu3_N_iff_locals :
  forall x p q,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    powm x 3 (p * q) = 1 <-> powm x 3 p = 1 /\ powm x 3 q = 1.
Proof.
  intros x p q Hp Hq Hneq.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  split.
  - intros H1. split.
    + pose proof (powm_reduce_factor x 3 p q ltac:(lia) ltac:(lia) ltac:(lia)) as Hr.
      rewrite H1, Z.mod_1_l in Hr by lia. symmetry; exact Hr.
    + pose proof (powm_reduce_factor x 3 q p ltac:(lia) ltac:(lia) ltac:(lia)) as Hr.
      rewrite Z.mul_comm in Hr.
      rewrite H1, Z.mod_1_l in Hr by lia. symmetry; exact Hr.
  - intros [Hp1 Hq1].
    unfold powm in Hp1, Hq1 |- *.
    apply crt_one; try assumption.
Qed.

Lemma mu3_unique_one_prime :
  forall p x,
    Z.prime p ->
    p <> 2 ->
    Z.gcd 3 (p - 1) = 1 ->
    Z.coprime x p ->
    powm x 3 p = 1 ->
    x mod p = 1.
Proof.
  intros p x Hp Hne Hgcd Hcop Hmu.
  pose proof (Z.prime_ge_2 p Hp).
  destruct (order_exists_from_annihilator x p 3 ltac:(lia) ltac:(lia) Hmu)
    as [k [Hord Hk3]].
  assert (k | p - 1) as Hkpm.
  { apply (order_divides_annihilator p x k (p - 1));
      [lia | lia | exact Hord | apply fermat_coprime; assumption]. }
  assert (k | 1) as Hk1.
  { apply Z.gcd_greatest with (a := 3) (b := p - 1) in Hk3; [| exact Hkpm].
    rewrite Hgcd in Hk3. exact Hk3. }
  apply Z.divide_1_r in Hk1.
  assert (k = 1) by (destruct Hord as [Hkpos _]; lia).
  subst k. destruct Hord as [_ [H1 _]].
  rewrite powm_1_r in H1 by lia. exact H1.
Qed.

Theorem pin_cube_kernel_trivial :
  forall x, Z.coprime x 187 -> powm x 3 187 = 1 -> x mod 187 = 1.
Proof.
  intros x Hcop Hmu.
  destruct (order_exists_from_annihilator x 187 3 ltac:(lia) ltac:(lia) Hmu)
    as [k [Hord Hk3]].
  assert (k | 80) as Hk80.
  { change 187 with (11 * 17) in Hcop, Hord.
    apply (order_divides_lambda 11 17 x k prime_11 prime_17 ltac:(lia) Hcop Hord). }
  assert (k | 1) as Hk1.
  { apply Z.gcd_greatest with (a := 3) (b := 80) in Hk3; [| exact Hk80].
    vm_compute in Hk3. exact Hk3. }
  apply Z.divide_1_r in Hk1.
  assert (k = 1) by (destruct Hord as [Hkpos _]; lia).
  subst k. destruct Hord as [_ [H1 _]].
  rewrite powm_1_r in H1 by lia. exact H1.
Qed.

Theorem cube_kernel_three :
  forall p g x,
    Z.prime p ->
    p <> 2 ->
    Z.coprime g p ->
    is_order p g (p - 1) ->
    (3 | p - 1) ->
    Z.coprime x p ->
    powm x 3 p = 1 <->
    exists m, 0 <= m < 3 /\ powm g (m * ((p - 1) / 3)) p = x mod p.
Proof.
  intros p g x Hp Hne Hg Hor Hdiv Hcx.
  pose proof (Z.prime_ge_2 p Hp).
  destruct Hdiv as [t Ht].
  assert (0 < t) as Htpos by nia.
  assert ((p - 1) / 3 = t) as Hquot.
  { rewrite Ht. apply Z.div_mul. lia. }
  split.
  - intros Hmu.
    destruct (primitive_root_generates p g x Hp Hg Hor Hcx) as [k [Hk Hkpow]].
    assert ((p - 1 | 3 * k)) as Hdivk.
    { apply (proj2 (order_iff_divides p g (p - 1) (3 * k)
                      ltac:(lia) ltac:(nia) Hor)).
      rewrite (Z.mul_comm 3 k), powm_mul_r by nia.
      rewrite Hkpow, powm_mod_base by lia.
      exact Hmu. }
    destruct Hdivk as [q Hq].
    assert (k = q * t) as Hkqt.
    { rewrite Ht in Hq. nia. }
    exists q. split.
    + split; [nia|].
      assert (q * t < t * 3) by nia. nia.
    + rewrite Hquot, <- Hkqt. exact Hkpow.
  - intros [m [Hm Heq]].
    rewrite <- (powm_mod_base x 3 p) by lia.
    rewrite <- Heq.
    rewrite <- powm_mul_r by (try lia; nia).
    rewrite Hquot.
    replace ((m * t) * 3) with ((p - 1) * m) by (rewrite Ht; ring).
    rewrite powm_mul_r by nia.
    destruct Hor as [_ [H1 _]].
    rewrite H1, powm_1_pow by nia.
    apply Z.mod_1_l; lia.
Qed.

Theorem omega_13_order_3 : is_order 13 3 3.
Proof.
  split; [lia|]. split; [vm_compute; reflexivity|].
  intros k' [Hk' Hk'lt] Hpow.
  assert (k' = 1 \/ k' = 2) by lia.
  destruct H as [H | H]; subst k'; vm_compute in Hpow; discriminate.
Qed.

Theorem mixed_kernel_91 :
  let x := Z.combinecong 13 7 3 1 in
  powm x 3 91 = 1 /\ x mod 13 = 3 /\ x mod 7 = 1 /\ x mod 91 <> 1.
Proof.
  intros x.
  pose proof (prime_coprime_distinct 13 7 prime_13 prime_7_cubic ltac:(lia)) as Hcop.
  pose proof (Z.combinecong_sound_coprime 13 7 3 1 Hcop) as [Hp Hq].
  unfold x. split.
  - change 91 with (13 * 7).
    apply (proj2 (mu3_N_iff_locals (Z.combinecong 13 7 3 1) 13 7
                    prime_13 prime_7_cubic ltac:(lia))).
    split.
    + rewrite <- (powm_mod_base (Z.combinecong 13 7 3 1) 3 13) by lia.
      rewrite Hp, Z.mod_small by lia. vm_compute. reflexivity.
    + rewrite <- (powm_mod_base (Z.combinecong 13 7 3 1) 3 7) by lia.
      rewrite Hq, Z.mod_small by lia. vm_compute. reflexivity.
  - split.
    + rewrite Hp. apply Z.mod_small. lia.
    + split.
      * rewrite Hq. apply Z.mod_small. lia.
      * vm_compute. discriminate.
Qed.

(** ** Mixed cube roots of 1 split [N]; diagonal leftover does not

    [x³ − 1 = (x − 1) Φ₃(x)].  A mixed kernel element ([x ≡ 1 (mod q)],
    [x ≢ 1 (mod p)]) puts [q] in [(x − 1)] and [p] in [Φ₃(x)].  A
    diagonal one ([x ≢ 1] both locally) has [gcd(x − 1, N) = 1] and
    [N | Φ₃(x)].  One mixed sample is a factoring query; the pairing
    formula is not required.  Cross-confirmed by
    [cas/160_mu3_split.gp]. *)

Definition phi3 (x : Z) : Z := x * x + x + 1.

Lemma cube_minus_one_fact :
  forall x, x ^ 3 - 1 = (x - 1) * phi3 x.
Proof.
  intros x. unfold phi3.
  change 3 with (Z.succ (Z.succ 1)).
  rewrite !Z.pow_succ_r by lia. rewrite Z.pow_1_r. ring.
Qed.

Theorem mixed_mu3_gcd_xminus1 :
  forall p q x,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    x mod q = 1 ->
    x mod p <> 1 ->
    Z.gcd (x - 1) (p * q) = q.
Proof.
  intros p q x Hp Hq Hneq Hq1 Hpne.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  rewrite (Z.mul_comm p q).
  apply gcd_onesided_semiprime; try assumption.
  - apply not_eq_sym. exact Hneq.
  - apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Hq1, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia. reflexivity.
  - intro Hdiv. apply Hpne.
    rewrite <- (Z.mod_1_l p) by lia.
    apply mods_eq_iff_divides; [lia | exact Hdiv].
Qed.

Theorem mixed_mu3_gcd_phi3 :
  forall p q x,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    q <> 3 ->
    powm x 3 p = 1 ->
    x mod p <> 1 ->
    x mod q = 1 ->
    Z.gcd (phi3 x) (p * q) = p.
Proof.
  intros p q x Hp Hq Hneq Hq3 Hmu Hpne Hq1.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  apply gcd_onesided_semiprime; try assumption.
  - apply Z.mod_divide; [lia|].
    unfold phi3.
    pose proof (primitive_3rd_root_cyclotomic x p Hp Hmu Hpne) as Hphi.
    exact Hphi.
  - intro Hdiv.
    assert (q | (x - 1)) as Hxm1.
    { apply Z.mod_divide; [lia|].
      rewrite Zminus_mod, Hq1, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia. reflexivity. }
    assert (q | (phi3 x - 3)) as Hm3.
    { unfold phi3. replace (x * x + x + 1 - 3) with ((x - 1) * (x + 2)) by ring.
      apply Z.divide_mul_l. exact Hxm1. }
    destruct Hdiv as [a Ha]. destruct Hm3 as [b Hb].
    rewrite Ha in Hb.
    assert (3 = (a - b) * q) as H3eq.
    { replace ((a - b) * q) with (a * q - b * q) by ring.
      rewrite <- Hb. ring. }
    assert (a - b = 1) as Hab by nia.
    rewrite Hab, Z.mul_1_l in H3eq.
    lia.
Qed.

Theorem mixed_mu3_splits :
  forall p q x,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    q <> 3 ->
    powm x 3 p = 1 ->
    x mod p <> 1 ->
    x mod q = 1 ->
    Z.gcd (x - 1) (p * q) = q /\ Z.gcd (phi3 x) (p * q) = p.
Proof.
  intros p q x Hp Hq Hneq Hq3 Hmu Hpne Hq1.
  split.
  - apply mixed_mu3_gcd_xminus1; assumption.
  - apply mixed_mu3_gcd_phi3; assumption.
Qed.

Theorem diagonal_mu3_gcd_xminus1 :
  forall p q x,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    x mod p <> 1 ->
    x mod q <> 1 ->
    Z.gcd (x - 1) (p * q) = 1.
Proof.
  intros p q x Hp Hq Hneq Hpne Hqne.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  apply coprime_semiprime; try assumption.
  split.
  - unfold Z.coprime. rewrite Z.gcd_comm.
    apply Z.coprime_prime_l_iff; [exact Hp|].
    intro Hdiv. apply Hpne.
    rewrite <- (Z.mod_1_l p) by lia.
    apply mods_eq_iff_divides; [lia | exact Hdiv].
  - unfold Z.coprime. rewrite Z.gcd_comm.
    apply Z.coprime_prime_l_iff; [exact Hq|].
    intro Hdiv. apply Hqne.
    rewrite <- (Z.mod_1_l q) by lia.
    apply mods_eq_iff_divides; [lia | exact Hdiv].
Qed.

Theorem diagonal_mu3_gcd_phi3 :
  forall p q x,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    powm x 3 (p * q) = 1 ->
    x mod p <> 1 ->
    x mod q <> 1 ->
    Z.gcd (phi3 x) (p * q) = p * q.
Proof.
  intros p q x Hp Hq Hneq Hmu Hpne Hqne.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  pose proof (diagonal_mu3_gcd_xminus1 p q x Hp Hq Hneq Hpne Hqne) as Hg1.
  unfold powm in Hmu.
  rewrite <- (Z.mod_1_l (p * q)) in Hmu by nia.
  apply mods_eq_iff_divides in Hmu; [| nia].
  rewrite cube_minus_one_fact in Hmu.
  apply Z.gauss in Hmu.
  2: { unfold Z.coprime. rewrite Z.gcd_comm. exact Hg1. }
  destruct Hmu as [k Hk].
  rewrite Hk, (Z.mul_comm k), Z.gcd_comm, Z.gcd_mul_diag_l; nia.
Qed.

Theorem mixed_kernel_91_splits :
  Z.gcd (29 - 1) 91 = 7 /\ Z.gcd (phi3 29) 91 = 13.
Proof. split; vm_compute; reflexivity. Qed.

Theorem gq_kernel_91_splits :
  Z.gcd (79 - 1) 91 = 13 /\ Z.gcd (phi3 79) 91 = 7.
Proof. split; vm_compute; reflexivity. Qed.

Theorem diagonal_16_91_no_split :
  Z.gcd (16 - 1) 91 = 1 /\ Z.gcd (phi3 16) 91 = 91.
Proof. split; vm_compute; reflexivity. Qed.

Theorem phi3_small_omega_is_prime :
  phi3 3 = 13 /\ phi3 2 = 7.
Proof. split; vm_compute; reflexivity. Qed.

Theorem pin_mu3_gcd_is_N :
  forall x,
    Z.coprime x 187 ->
    powm x 3 187 = 1 ->
    Z.gcd (x - 1) 187 = 187.
Proof.
  intros x Hcop Hmu.
  pose proof (pin_cube_kernel_trivial x Hcop Hmu) as H1.
  rewrite <- (Z.mod_1_l 187) in H1 by lia.
  apply mods_eq_iff_divides in H1; [| lia].
  destruct H1 as [k Hk].
  rewrite Hk, (Z.mul_comm k), Z.gcd_comm, Z.gcd_mul_diag_l; lia.
Qed.
