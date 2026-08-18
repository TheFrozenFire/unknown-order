From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.

Open Scope Z_scope.

(** * Threshold / mediated RSA, as exponent algebra

    Additive shares: [d = d₁ + d₂] gives [m^d = m^{d₁} m^{d₂}].
    Mediated RSA / SEM is the two-party case.  Shoup's extraction
    from a raised share [y = x^{k d}] uses Bézout
    [k a = 1 + e t] (the [4Δ²] clearing factor is such a [k],
    coprime to prime [e]).  Feldman VSS and robustness stay
    [Refuse_threshold_robustness].

    Cross-confirmed by [cas/67_threshold_rsa.gp]. *)

Theorem additive_share_combines :
  forall N m d1 d2,
    N <> 0 ->
    0 <= d1 ->
    0 <= d2 ->
    powm m (d1 + d2) N =
      (powm m d1 N * powm m d2 N) mod N.
Proof.
  intros N m d1 d2 HN H1 H2.
  apply powm_add_r; lia.
Qed.

Theorem additive_three_shares :
  forall N m d1 d2 d3,
    N <> 0 ->
    0 <= d1 -> 0 <= d2 -> 0 <= d3 ->
    powm m (d1 + d2 + d3) N =
      (powm m d1 N * powm m d2 N * powm m d3 N) mod N.
Proof.
  intros N m d1 d2 d3 HN H1 H2 H3.
  rewrite (powm_add_r m (d1 + d2) d3 N) by lia.
  rewrite (powm_add_r m d1 d2 N) by lia.
  rewrite Z.mul_mod_idemp_l by lia.
  reflexivity.
Qed.

Theorem mediated_rsa_is_two_shares :
  forall R m du ds,
    0 <= du ->
    0 <= ds ->
    du + ds = rsa_d R ->
    powm m (rsa_d R) (rsa_N R) =
      (powm m du (rsa_N R) * powm m ds (rsa_N R)) mod rsa_N R.
Proof.
  intros R m du ds Hu Hs Heq.
  pose proof (rsa_N_gt_1 R).
  rewrite <- Heq.
  apply additive_share_combines; lia.
Qed.

Theorem share_refresh_by_zero :
  forall N m d1 d2 z,
    N <> 0 ->
    0 <= d1 ->
    0 <= d2 ->
    0 <= z ->
    powm m ((d1 + z) + (d2 - z)) N =
      powm m (d1 + d2) N.
Proof.
  intros N m d1 d2 z HN H1 H2 Hz.
  assert (0 <= d2 - z \/ d2 - z < 0) by lia.
  (* keep the identity on the exponents; powm needs a nonneg exp
     only in powm_add_r.  Reduce to the sum. *)
  replace ((d1 + z) + (d2 - z)) with (d1 + d2) by ring.
  reflexivity.
Qed.

(** Shoup extract.  [y = x^{k d}], [k a = 1 + e t], units,
    [e d ≡ 1 (mod λ)].  Then [y^a · x^{-t} = x^d]. *)

Lemma powm_ed_is_base :
  forall p q x e d,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    Z.coprime x (p * q) ->
    0 <= e ->
    0 <= d ->
    (e * d) mod (lambda_semiprime p q) = 1 ->
    powm x (e * d) (p * q) = x mod (p * q).
Proof.
  intros p q x e d Hp Hq Hneq Hcop He Hd Hinv.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  pose proof (lambda_semiprime_pos p q Hp Hq) as Hlam.
  assert (1 <= e * d) as Hed.
  { destruct (Z.eq_dec (e * d) 0) as [Hz | Hnz].
    - rewrite Hz, Z.mod_0_l in Hinv by lia. lia.
    - nia. }
  replace (e * d) with ((e * d - 1) + 1) by lia.
  rewrite powm_add_r by lia.
  rewrite powm_1_r by lia.
  assert (1 < lambda_semiprime p q) as Hlam1.
  { unfold lambda_semiprime.
    assert (2 <= p - 1 \/ 2 <= q - 1) as Hor by lia.
    pose proof (Z.divide_lcm_l (p - 1) (q - 1)).
    pose proof (Z.divide_lcm_r (p - 1) (q - 1)).
    destruct Hor as [Hor | Hor]; unfold lambda_semiprime in Hlam.
    - pose proof (Z.divide_pos_le (p - 1) (Z.lcm (p - 1) (q - 1))
                    Hlam H1). lia.
    - pose proof (Z.divide_pos_le (q - 1) (Z.lcm (p - 1) (q - 1))
                    Hlam H2). lia. }
  assert (lambda_semiprime p q | e * d - 1) as Hdiv.
  { apply mods_eq_iff_divides; [lia |].
    rewrite Hinv, Z.mod_1_l by lia. reflexivity. }
  rewrite (annihilates_units p q x (e * d - 1)
             Hp Hq Hneq Hcop ltac:(lia) Hdiv).
  rewrite Z.mul_1_l. unfold powm. rewrite Z.mod_mod by nia. reflexivity.
Qed.

Theorem shoup_extract_from_kd :
  forall p q x d e k a t xinv y,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    Z.coprime x (p * q) ->
    0 <= d ->
    0 <= e ->
    0 <= k ->
    0 <= a ->
    0 <= t ->
    (e * d) mod (lambda_semiprime p q) = 1 ->
    k * a = 1 + e * t ->
    y = powm x (k * d) (p * q) ->
    (x * xinv) mod (p * q) = 1 ->
    (powm y a (p * q) * powm xinv t (p * q)) mod (p * q) =
      powm x d (p * q).
Proof.
  intros p q x d e k a t xinv y Hp Hq Hneq Hcop Hd He Hk Ha Ht Hinv Hka Hy Hxinv.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  assert (1 < p * q) by nia.
  subst y.
  rewrite <- powm_mul_r by lia.
  replace (k * d * a) with (d * (k * a)) by ring.
  rewrite Hka.
  rewrite Z.mul_add_distr_l, Z.mul_1_r.
  assert (0 <= d * (e * t)) by nia.
  rewrite powm_add_r by nia.
  replace (d * (e * t)) with (e * d * t) by ring.
  assert (powm x (e * d * t) (p * q) = powm x t (p * q)) as Hred.
  { destruct (Z.eq_dec t 0) as [Ht0 | Htnz].
    - subst t. rewrite !Z.mul_0_r. reflexivity.
    - rewrite (powm_mul_r x (e * d) t (p * q)) by nia.
      rewrite (powm_ed_is_base p q x e d Hp Hq Hneq Hcop He Hd Hinv).
      unfold powm. rewrite Z.mod_pow_l by lia. reflexivity. }
  rewrite Hred.
  rewrite Z.mul_mod_idemp_l by lia.
  rewrite <- Z.mul_assoc.
  unfold powm.
  set (N := p * q) in *.
  assert ((x ^ t mod N * (xinv ^ t mod N)) mod N = 1 mod N) as Hone.
  { rewrite <- Z.mul_mod by lia.
    rewrite <- Z.pow_mul_l.
    rewrite <- Z.mod_pow_l by lia.
    rewrite Hxinv, Z.pow_1_l by lia. reflexivity. }
  rewrite <- (Z.mul_mod_idemp_r (x ^ d mod N)
               (x ^ t mod N * (xinv ^ t mod N)) N) by lia.
  rewrite Hone, Z.mod_1_l, Z.mul_1_r, Z.mod_mod by lia.
  reflexivity.
Qed.
