From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.

Open Scope Z_scope.

(** * Cramer–Shoup 2000 Strong RSA signatures, verification algebra

    [y^e ≡ x · h^m (mod N)] is an [e]-th root of a public product.
    Two signatures at the *same* [e] give [(y/y')^e = h^{m−m'}].
    Hash-to-prime and the EUF game stay [Refuse_hash_as_oracle] /
    [Refuse_PPT_advantage].

    Cross-confirmed by [cas/74_cramer_shoup.gp]. *)

Definition cs_verify (N x h e y m : Z) : Prop :=
  powm y e N = (x * powm h m N) mod N.

Lemma powm_mul_base :
  forall a b e n,
    n <> 0 ->
    0 <= e ->
    powm (a * b) e n = (powm a e n * powm b e n) mod n.
Proof.
  intros a b e n Hn He.
  unfold powm. rewrite Z.pow_mul_l. apply Z.mul_mod; lia.
Qed.

Theorem cs_verify_is_rsa :
  forall N x h e y m,
    cs_verify N x h e y m ->
    Problem_RSA N e ((x * powm h m N) mod N) y.
Proof.
  intros N x h e y m Hv.
  unfold Problem_RSA, rsa_problem, cs_verify in *.
  exact Hv.
Qed.

Theorem cs_verify_is_strong_rsa :
  forall N x h e y m,
    1 < e ->
    cs_verify N x h e y m ->
    Problem_StrongRSA N ((x * powm h m N) mod N) y e.
Proof.
  intros N x h e y m He Hv.
  unfold Problem_StrongRSA, cs_verify in *.
  split; [exact He | exact Hv].
Qed.

Theorem cs_same_e_ratio :
  forall N x h e y y' m m' yinv,
    1 < N ->
    0 <= e ->
    0 <= m' <= m ->
    (y' * yinv) mod N = 1 ->
    cs_verify N x h e y m ->
    cs_verify N x h e y' m' ->
    powm ((y * yinv) mod N) e N = powm h (m - m') N.
Proof.
  intros N x h e y y' m m' yinv HN He Hm Hyinv Hv Hv'.
  unfold cs_verify in Hv, Hv'.
  rewrite powm_mod_base by lia.
  rewrite powm_mul_base by lia.
  assert ((powm y' e N * powm yinv e N) mod N = 1) as Hinvp.
  { rewrite <- powm_mul_base by lia.
    rewrite <- powm_mod_base by lia.
    rewrite Hyinv.
    unfold powm. rewrite Z.pow_1_l by lia. apply Z.mod_1_l; lia. }
  rewrite Hv' in Hinvp.
  rewrite Hv.
  rewrite Z.mul_mod_idemp_l by lia.
  rewrite Z.mul_mod_idemp_l in Hinvp by lia.
  replace (powm h m N) with (powm h (m' + (m - m')) N) by (f_equal; lia).
  rewrite powm_add_r by lia.
  rewrite <- Z.mul_mod_idemp_l by lia.
  rewrite Z.mul_mod_idemp_r by lia.
  rewrite Z.mul_mod_idemp_l by lia.
  rewrite <- (Z.mul_assoc x).
  replace (x * (powm h m' N * powm h (m - m') N * powm yinv e N))
    with (x * powm h m' N * powm yinv e N * powm h (m - m') N) by ring.
  rewrite <- Z.mul_mod_idemp_l by lia.
  rewrite Hinvp, Z.mul_1_l.
  unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.
