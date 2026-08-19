From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import Takagi.

Open Scope Z_scope.

(** * Okamoto–Uchiyama, as a neighbour of Takagi

    Same modulus [N = p² q].  The map is [m ↦ (1+p)^m] on
    [(Z/p²Z)*], not RSA on [(Z/NZ)*].  [L(x) = (x−1)/p] recovers
    the discrete log of [1+p].  A unit randomizer raised to
    [N(p−1)] vanishes mod [p²] because [p(p−1) | N(p−1)].
    Decisional p-subgroup residuosity is [Refuse_PPT_advantage].

    Cross-confirmed by [cas/76_okamoto_uchiyama.gp]. *)

Definition ou_L (x p : Z) : Z := (x - 1) / p.

Theorem one_plus_p_pow :
  forall p m,
    1 < p ->
    0 <= m ->
    powm (1 + p) m (p * p) = (1 + m * p) mod (p * p).
Proof.
  intros p m Hp Hm.
  apply powm_one_plus_nilpotent; [nia | exact Hm |].
  rewrite Z.mod_same by nia. reflexivity.
Qed.

Theorem ou_L_of_plain :
  forall p m,
    1 < p ->
    0 <= m < p ->
    ou_L (1 + m * p) p = m.
Proof.
  intros p m Hp Hm.
  unfold ou_L.
  rewrite Z.add_comm, Z.add_simpl_r, Z.div_mul by lia.
  reflexivity.
Qed.

(** Reduced [(1+p)^{m(p−1)}] is [1 − m p] mod [p²], whose [L]
    is [p − m] for [0 < m < p].  In [F_p] that is [−m], so the
    ratio of two [L] values recovers [m]. *)
Theorem ou_L_of_scaled :
  forall p m,
    Z.prime p ->
    0 < m < p ->
    ou_L (powm (1 + p) (m * (p - 1)) (p * p)) p = p - m.
Proof.
  intros p m Hp Hm.
  pose proof (Z.prime_ge_2 p Hp).
  rewrite one_plus_p_pow by nia.
  replace (1 + m * (p - 1) * p) with (1 - m * p + m * (p * p)) by ring.
  rewrite (Z.mod_add (1 - m * p) m (p * p)) by nia.
  assert (0 <= 1 - m * p + p * p < p * p) as Hbd by nia.
  replace ((1 - m * p) mod (p * p)) with (1 - m * p + p * p).
  2:{ rewrite <- (Z.mod_small (1 - m * p + p * p) (p * p) Hbd).
      replace (1 - m * p + p * p) with (1 - m * p + 1 * (p * p)) by ring.
      rewrite (Z.mod_add (1 - m * p) 1 (p * p)) by nia. reflexivity. }
  unfold ou_L.
  replace (1 - m * p + p * p - 1) with ((p - m) * p) by ring.
  apply Z.div_mul. lia.
Qed.

Theorem ou_L_of_base :
  forall p,
    Z.prime p ->
    p <> 2 ->
    ou_L (powm (1 + p) (p - 1) (p * p)) p = p - 1.
Proof.
  intros p Hp Hp2.
  pose proof (Z.prime_ge_2 p Hp).
  rewrite <- (Z.mul_1_l (p - 1)) at 1.
  apply ou_L_of_scaled; [exact Hp | lia].
Qed.

Theorem ou_rand_vanishes :
  forall p q x,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    p <> q ->
    Z.coprime x p ->
    powm x (takagi_N p q * (p - 1)) (p * p) = 1.
Proof.
  intros p q x Hp Hq Hp2 Hneq Hcop.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  unfold takagi_N.
  replace (p * p * q * (p - 1)) with (p * (p - 1) * (p * q)) by ring.
  rewrite (powm_one_mul x (p * (p - 1)) (p * q) (p * p));
    [apply Z.mod_small; nia | nia | nia | nia |].
  apply euler_p2; assumption.
Qed.
