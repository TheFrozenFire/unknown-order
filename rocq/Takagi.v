From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * Takagi multi-power RSA: [N = p² q]

    [λ(p²) = p(p−1)] for odd [p]; [λ(p²q) = lcm(p(p−1), q−1)].
    Squaring on [(Z/p²Z)*] has only [±1] as roots of [1] ([p] odd).
    Combined with [q] that is still four [√1], not the eight of a
    triprime.  Hensel / Euler on [p²] is the nilpotent binomial
    [powm_one_plus_nilpotent].

    Cross-confirmed by [cas/72_takagi.gp]. *)

Definition takagi_N (p q : Z) : Z := p * p * q.

Definition lambda_p2 (p : Z) : Z := p * (p - 1).

Definition lambda_takagi (p q : Z) : Z :=
  Z.lcm (lambda_p2 p) (q - 1).

Lemma fermat_minus_one_divides :
  forall p a,
    Z.prime p ->
    Z.coprime a p ->
    (p | a ^ (p - 1) - 1).
Proof.
  intros p a Hp Hcop.
  pose proof (Z.prime_ge_2 p Hp).
  apply Z.mod_divide; [lia|].
  pose proof (fermat_coprime p a Hp Hcop) as Hf.
  unfold powm in Hf.
  rewrite Zminus_mod, Hf, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
  reflexivity.
Qed.

Theorem euler_p2 :
  forall p a,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    powm a (lambda_p2 p) (p * p) = 1.
Proof.
  intros p a Hp Hp2 Hcop.
  pose proof (Z.prime_ge_2 p Hp) as Hpge.
  unfold lambda_p2.
  destruct (fermat_minus_one_divides p a Hp Hcop) as [t Ht].
  assert (a ^ (p - 1) = 1 + t * p) as Ha by lia.
  assert ((t * p * (t * p)) mod (p * p) = 0) as Hnil.
  { replace (t * p * (t * p)) with ((t * t) * (p * p)) by ring.
    rewrite Z.mod_mul by nia. reflexivity. }
  unfold powm.
  rewrite (Z.mul_comm p (p - 1)), Z.pow_mul_r by lia.
  rewrite Ha.
  fold (powm (1 + t * p) p (p * p)).
  rewrite (powm_one_plus_nilpotent (t * p) (p * p) p ltac:(nia) ltac:(lia) Hnil).
  replace (1 + p * (t * p)) with (1 + t * (p * p)) by ring.
  rewrite Z.mod_add, Z.mod_1_l by nia.
  reflexivity.
Qed.

Theorem sqrt1_mod_p2_is_pm1 :
  forall p x,
    Z.prime p ->
    p <> 2 ->
    powm x 2 (p * p) = 1 ->
    x mod (p * p) = 1 \/ x mod (p * p) = p * p - 1.
Proof.
  intros p x Hp Hp2 Hsq.
  pose proof (Z.prime_ge_2 p Hp).
  assert (p * p | x * x - 1) as Hdiv.
  { apply mods_eq_iff_divides; [nia|].
    unfold powm in Hsq. rewrite Z.pow_2_r in Hsq.
    rewrite Hsq, Z.mod_1_l by nia. reflexivity. }
  replace (x * x - 1) with ((x - 1) * (x + 1)) in Hdiv by ring.
  assert (~ (p | x - 1) \/ ~ (p | x + 1)) as Hor.
  { destruct (Z.eq_dec (x mod p) 1) as [H1 | Hn1].
    - right. intro Hpp.
      apply Z.mod_divide in Hpp; [|lia].
      rewrite Zplus_mod, H1, Z.mod_1_l in Hpp by lia.
      rewrite Z.mod_small in Hpp by lia. discriminate.
    - left. intro Hpm.
      apply Z.mod_divide in Hpm; [|lia].
      apply Hn1.
      replace (x mod p) with (((x - 1) + 1) mod p) by (f_equal; lia).
      rewrite Zplus_mod, Hpm, Z.add_0_l.
      rewrite Z.mod_1_l by lia.
      rewrite Z.mod_small by lia.
      reflexivity. }
  destruct Hor as [Hn1 | Hnp1].
  - right.
    assert (Z.gcd (p * p) (x - 1) = 1) as Hg.
    { fold (Z.coprime (p * p) (x - 1)). rewrite coprime_comm.
      apply coprime_mul_iff.
      split; (rewrite coprime_comm; apply Z.coprime_prime_l_iff;
              [exact Hp | exact Hn1]). }
    assert (p * p | x + 1) as Hp1.
    { apply Z.gauss with (m := x - 1); [exact Hdiv | exact Hg]. }
    destruct Hp1 as [k Hk].
    replace x with (k * (p * p) + (-1)) by lia.
    rewrite (Z.add_comm (k * (p * p))), Z.mod_add by nia.
    replace (-1) with (- (1)) by lia.
    rewrite (Z.mod_opp_l_nz 1 (p * p))
      by (nia || (rewrite Z.mod_1_l by nia; discriminate)).
    rewrite Z.mod_1_l by nia.
    reflexivity.
  - left.
    assert (Z.gcd (p * p) (x + 1) = 1) as Hg.
    { fold (Z.coprime (p * p) (x + 1)). rewrite coprime_comm.
      apply coprime_mul_iff.
      split; (rewrite coprime_comm; apply Z.coprime_prime_l_iff;
              [exact Hp | exact Hnp1]). }
    assert (p * p | x - 1) as Hm1.
    { apply Z.gauss with (m := x + 1);
      [rewrite (Z.mul_comm (x + 1)); exact Hdiv | exact Hg]. }
    destruct Hm1 as [k Hk].
    replace x with (k * (p * p) + 1) by lia.
    rewrite (Z.add_comm (k * (p * p))), Z.mod_add by nia.
    rewrite Z.mod_1_l by nia.
    reflexivity.
Qed.

Theorem carmichael_takagi :
  forall p q a,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    p <> q ->
    Z.coprime a (takagi_N p q) ->
    powm a (lambda_takagi p q) (takagi_N p q) = 1.
Proof.
  intros p q a Hp Hq Hp2 Hneq Hcop.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  unfold takagi_N, lambda_takagi, lambda_p2 in *.
  assert (Z.coprime a p /\ Z.coprime a q) as [Hap Haq].
  { apply coprime_mul_iff in Hcop. destruct Hcop as [Hap2 Haq].
    apply coprime_mul_iff in Hap2. destruct Hap2 as [Hap _].
    split; assumption. }
  assert (0 < Z.lcm (p * (p - 1)) (q - 1)) as Hlam.
  { pose proof (Z.lcm_nonneg (p * (p - 1)) (q - 1)).
    destruct (Z.eq_dec (Z.lcm (p * (p - 1)) (q - 1)) 0) as [Hz | Hnz].
    - apply Z.lcm_eq_0 in Hz. nia.
    - lia. }
  destruct (Z.divide_lcm_l (p * (p - 1)) (q - 1)) as [kp Hkp].
  destruct (Z.divide_lcm_r (p * (p - 1)) (q - 1)) as [kq Hkq].
  assert (0 <= kp) by nia.
  assert (0 <= kq) by nia.
  assert (powm a (Z.lcm (p * (p - 1)) (q - 1)) (p * p) = 1) as Hp2a.
  { rewrite Hkp, Z.mul_comm.
    rewrite (powm_one_mul a (p * (p - 1)) kp (p * p));
      [apply Z.mod_small; nia | nia | nia | nia |].
    apply euler_p2; assumption. }
  assert (powm a (Z.lcm (p * (p - 1)) (q - 1)) q = 1) as Hqa.
  { rewrite Hkq, Z.mul_comm.
    rewrite (powm_one_mul a (q - 1) kq q);
      [apply Z.mod_small; lia | lia | lia | lia |].
    apply fermat_coprime; assumption. }
  unfold powm in Hp2a, Hqa |- *.
  transitivity (1 mod (p * p * q)); [| apply Z.mod_small; nia].
  apply mods_eq_iff_divides; [nia|].
  apply divide_by_coprime_product.
  - apply coprime_comm. apply coprime_mul_iff.
    split; apply coprime_comm; apply prime_coprime_distinct; assumption.
  - apply mods_eq_iff_divides; [nia|].
    rewrite Hp2a, Z.mod_1_l by nia. reflexivity.
  - apply mods_eq_iff_divides; [lia|].
    rewrite Hqa, Z.mod_1_l by lia. reflexivity.
Qed.

Definition phi_takagi (p q : Z) : Z := p * (p - 1) * (q - 1).

Theorem lambda_divides_phi_takagi :
  forall p q, (lambda_takagi p q | phi_takagi p q).
Proof.
  intros p q. unfold lambda_takagi, lambda_p2, phi_takagi.
  apply Z.lcm_least.
  - exists (q - 1). ring.
  - exists (p * (p - 1)). ring.
Qed.

(** A √1 that is [+1] on [p²] and [−1] on [q] splits [N = p²q]. *)
Theorem takagi_mixed_sqrt1_splits :
  forall p q x,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    q <> 2 ->
    powm x 2 (takagi_N p q) = 1 ->
    x mod (p * p) = 1 ->
    x mod q = q - 1 ->
    let g := Z.gcd (x - 1) (takagi_N p q) in
    1 < g /\ g < takagi_N p q /\ (g | takagi_N p q).
Proof.
  intros p q x Hp Hq Hneq Hq2 Hsq Hp1 Hq1 g.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  unfold g, takagi_N.
  assert (p * p | x - 1) as Hpx.
  { apply Z.mod_divide; [nia|].
    rewrite Zminus_mod, Hp1, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by nia.
    reflexivity. }
  assert (~ (q | x - 1)) as Hqn.
  { intro Hdiv. apply Z.mod_divide in Hdiv; [|lia].
    rewrite Zminus_mod, Hq1, Z.mod_1_l in Hdiv by lia.
    replace ((q - 1 - 1) mod q) with ((q - 2) mod q) in Hdiv
      by (f_equal; ring).
    rewrite Z.mod_small in Hdiv by lia. lia. }
  pose proof (Z.gcd_divide_l (x - 1) (p * p * q)) as Hgx.
  pose proof (Z.gcd_divide_r (x - 1) (p * p * q)) as HgN.
  split; [| split].
  - pose proof (Z.gcd_nonneg (x - 1) (p * p * q)).
    destruct (Z.le_gt_cases (Z.gcd (x - 1) (p * p * q)) 1) as [Hle | Hgt];
      [| exact Hgt].
    assert (Z.gcd (x - 1) (p * p * q) <> 0) as Hgnz.
    { intro Hz. apply Z.gcd_eq_0 in Hz. nia. }
    assert (Z.gcd (x - 1) (p * p * q) = 1) as Hg1 by lia.
    assert (p | Z.gcd (x - 1) (p * p * q)) as Hpg.
    { apply Z.gcd_greatest; [eapply Z.divide_trans; [|exact Hpx];
        exists p; ring | exists (p * q); ring]. }
    rewrite Hg1 in Hpg. apply Z.divide_1_r in Hpg. lia.
  - destruct (Z.lt_ge_cases (Z.gcd (x - 1) (p * p * q)) (p * p * q))
      as [Hlt | Hge]; [exact Hlt|].
    assert (Z.gcd (x - 1) (p * p * q) = p * p * q) as Hgeq.
    { pose proof (Z.divide_pos_le (Z.gcd (x - 1) (p * p * q)) (p * p * q)
                    ltac:(nia) HgN). lia. }
    assert (q | x - 1).
    { rewrite Hgeq in Hgx.
      apply (Z.divide_trans q (p * p * q) (x - 1)); [| exact Hgx].
      exists (p * p). ring. }
    contradiction.
  - exact HgN.
Qed.
