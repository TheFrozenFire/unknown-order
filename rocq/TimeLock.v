From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.

Open Scope Z_scope.

(** * Rivest–Shamir–Wagner time-lock, trapdoor side

    [a^{2^T} ≡ a^{2^T mod λ}] on units.  Sequentiality of repeated
    squaring is [Refuse_this_is_a_VDF].

    Cross-confirmed by [cas/69_timelock.gp]. *)

Theorem timelock_trapdoor_reduces_exp :
  forall p q a T,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    Z.coprime a (p * q) ->
    0 <= T ->
    powm a (2 ^ T) (p * q) =
      powm a ((2 ^ T) mod (lambda_semiprime p q)) (p * q).
Proof.
  intros p q a T Hp Hq Hneq Hcop HT.
  pose proof (lambda_semiprime_pos p q Hp Hq) as Hlam.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  assert (0 < 2 ^ T) by (apply Z.pow_pos_nonneg; lia).
  set (lam := lambda_semiprime p q) in *.
  pose proof (Z.div_mod (2 ^ T) lam ltac:(lia)) as Hdm.
  rewrite Hdm at 1.
  assert (0 <= 2 ^ T mod lam) by (apply Z.mod_pos_bound; lia).
  assert (0 <= 2 ^ T / lam) by (apply Z.div_pos; lia).
  assert (0 <= lam * (2 ^ T / lam)) by nia.
  rewrite powm_add_r by nia.
  rewrite powm_mul_r by nia.
  unfold lam. rewrite (carmichael_semiprime p q a Hp Hq Hneq Hcop).
  rewrite powm_1_pow by (try exact H3; nia).
  unfold powm.
  rewrite Z.mod_1_l by nia.
  rewrite Z.mul_1_l, Z.mod_mod by nia. reflexivity.
Qed.
