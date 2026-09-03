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

    Cross-confirmed by [cas/86_cubic_residue.gp] and
    [cas/154_cube_euler.gp]. *)

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
