From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import TwoPrimary.

Open Scope Z_scope.

(** * Evaluation pairing on [μ_n]: [e(x,k) = x^k]

    If [x^n ≡ 1] then [x^k] stays in [μ_n] and depends on [k]
    only modulo [n].  The target has order dividing [n].  For
    [n ∈ {2,3,4,6}] that is at most six elements.  One argument
    is an integer, so this is RSA-shaped exponentiation, not a
    pairing of two hidden discrete logs.

    Cross-confirmed by [cas/87_eval_pairing.gp]. *)

Definition mu (n x N : Z) : Prop :=
  powm x n N = 1.

Definition eval_pair (x k N : Z) : Z :=
  powm x k N.

Theorem eval_pair_stays_in_mu :
  forall n x k N,
    1 < N ->
    0 <= k ->
    0 <= n ->
    mu n x N ->
    mu n (eval_pair x k N) N.
Proof.
  intros n x k N Hn Hk Hnn Hmu.
  unfold mu, eval_pair in *.
  rewrite <- powm_mul_r by lia.
  rewrite (Z.mul_comm k), powm_mul_r by lia.
  rewrite Hmu.
  rewrite powm_1_pow by lia.
  apply Z.mod_1_l; lia.
Qed.

Theorem eval_pair_add :
  forall x a b N,
    1 < N ->
    0 <= a ->
    0 <= b ->
    eval_pair x (a + b) N =
      (eval_pair x a N * eval_pair x b N) mod N.
Proof.
  intros x a b N Hn Ha Hb.
  unfold eval_pair.
  apply powm_add_r; lia.
Qed.

Theorem eval_pair_mul_base :
  forall x y k N,
    1 < N ->
    0 <= k ->
    eval_pair ((x * y) mod N) k N =
      (eval_pair x k N * eval_pair y k N) mod N.
Proof.
  intros x y k N Hn Hk.
  unfold eval_pair.
  rewrite powm_mod_base by lia.
  unfold powm.
  rewrite Z.pow_mul_l.
  apply Z.mul_mod; lia.
Qed.

Theorem eval_pair_reduce_mod_n :
  forall n x k N,
    1 < N ->
    0 < n ->
    0 <= k ->
    mu n x N ->
    eval_pair x k N = eval_pair x (k mod n) N.
Proof.
  intros n x k N Hn Hnn Hk Hmu.
  unfold eval_pair, mu in *.
  assert (0 <= k / n) by (apply Z.div_pos; lia).
  assert (0 <= k mod n) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod k n ltac:(lia)) as Hdm.
  rewrite Hdm at 1.
  rewrite powm_add_r by nia.
  rewrite powm_mul_r by nia.
  rewrite Hmu.
  rewrite powm_1_pow by nia.
  rewrite Z.mod_1_l by lia.
  rewrite Z.mul_1_l.
  unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem eval_pair_image_divides_n :
  forall n x k N,
    1 < N ->
    0 <= k ->
    0 <= n ->
    mu n x N ->
    powm (eval_pair x k N) n N = 1.
Proof. apply eval_pair_stays_in_mu. Qed.

(** [n = 2]: the four square roots of 1.  [x^k] is [1] or [x]. *)
Theorem eval_pair_mu2 :
  forall p q x k,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    0 <= k ->
    powm x 2 (p * q) = 1 ->
    eval_pair x k (p * q) = eval_pair x (k mod 2) (p * q).
Proof.
  intros p q x k Hp Hq Hneq Hk Hx.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  apply eval_pair_reduce_mod_n; try lia.
  exact Hx.
Qed.

Theorem eval_pair_mu2_on_mixed :
  forall p q k,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    0 <= k ->
    eval_pair (sqrt1_pm p q) k (p * q) =
      eval_pair (sqrt1_pm p q) (k mod 2) (p * q).
Proof.
  intros p q k Hp Hq Hneq Hk.
  pose proof (four_sqrt1 p q Hp Hq Hneq) as [_ [_ [Hsq _]]].
  apply eval_pair_mu2; assumption.
Qed.

(** [n = 3]: a root of [X² + X + 1] is a primitive cube root of 1. *)
Theorem omega_cube_is_one :
  forall omega N,
    1 < N ->
    (omega * omega + omega + 1) mod N = 0 ->
    mu 3 omega N.
Proof.
  intros omega N Hn Hpoly.
  unfold mu, powm.
  change 3 with (Z.succ 2).
  rewrite Z.pow_succ_r, Z.pow_2_r by lia.
  rewrite <- (Z.mod_1_l N) by lia.
  apply mods_eq_iff_divides; [lia|].
  apply Z.mod_divide in Hpoly; [| lia].
  destruct Hpoly as [t Ht].
  exists ((omega - 1) * t).
  replace (omega * (omega * omega) - 1)
    with ((omega - 1) * (omega * omega + omega + 1)) by ring.
  rewrite Ht. ring.
Qed.

Theorem eval_pair_mu3 :
  forall omega k N,
    1 < N ->
    0 <= k ->
    (omega * omega + omega + 1) mod N = 0 ->
    eval_pair omega k N = eval_pair omega (k mod 3) N.
Proof.
  intros omega k N Hn Hk Hpoly.
  apply eval_pair_reduce_mod_n; try lia.
  apply omega_cube_is_one; assumption.
Qed.

(** [n = 6]: [x^6 = (x^2)^3 = (x^3)^2], so [μ_2 ∪ μ_3 ⊂ μ_6]. *)
Theorem mu2_is_mu6 :
  forall x N,
    1 < N ->
    mu 2 x N ->
    mu 6 x N.
Proof.
  intros x N Hn H2.
  unfold mu in *.
  change 6 with (2 * 3).
  rewrite powm_mul_r by lia.
  rewrite H2.
  rewrite powm_1_pow by lia.
  apply Z.mod_1_l; lia.
Qed.

Theorem mu3_is_mu6 :
  forall x N,
    1 < N ->
    mu 3 x N ->
    mu 6 x N.
Proof.
  intros x N Hn H3.
  unfold mu in *.
  change 6 with (3 * 2).
  rewrite powm_mul_r by lia.
  rewrite H3.
  rewrite powm_1_pow by lia.
  apply Z.mod_1_l; lia.
Qed.

Theorem eval_pair_mu6 :
  forall x k N,
    1 < N ->
    0 <= k ->
    mu 6 x N ->
    eval_pair x k N = eval_pair x (k mod 6) N.
Proof.
  intros x k N Hn Hk H6.
  apply eval_pair_reduce_mod_n; try lia.
  exact H6.
Qed.

(** The integer argument is in the clear.  This pairing cannot
    take two CRS group elements and return a check of [τ]. *)
Definition eval_pair_needs_integer_named : Prop :=
  forall (x k N : Z), mu 2 x N -> False.
