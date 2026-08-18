From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import PollardP1.

Open Scope Z_scope.

(** * Relation-level structure of the named problems

    A hardness *claim* is a statement about algorithms and a KeyGen
    distribution ([THEORY.md] §9).  This file does not make one.  It
    records the arrows that hold for the *winning conditions*:
    trapdoor ⇒ roots, RSA-solution ⇒ strong-RSA solution for that
    [e], [λ] ⇒ a trivial strong-RSA witness, order divides [λ],
    one-sided small exponent splits [N].  Adaptive root with a
    known-finite or [B]-smooth challenge space is broken
    ([adaptive_root_known_product_breaks];
    [notes/paper-overlaps.md] row 3).  Public [λ] is row 7.

    Cross-confirmed by [cas/18_hardness.gp]. *)

(** ** Factoring as a relation *)

Definition Problem_Factor (N f : Z) : Prop :=
  1 < f < N /\ (f | N).

(** ** RSA is a one-way permutation on units, not a predicate

    When [gcd(e, λ) = 1] every unit is an [e]-th power (of a unit).
    Decisional "is [y] an [e]-th residue?" is then vacuous on
    [(Z/NZ)*].  The assumption is *inversion*, not decision. *)

Theorem rsa_units_are_eth_powers :
  forall R y,
    Z.coprime y (rsa_N R) ->
    powm (powm y (rsa_d R) (rsa_N R)) (rsa_e R) (rsa_N R) =
      y mod rsa_N R.
Proof.
  intros R y Hcop.
  pose proof (rsa_enc_dec_units R y Hcop) as Henc.
  unfold rsa_enc, rsa_dec in Henc. exact Henc.
Qed.

Theorem trapdoor_inverts_RSA :
  forall R y,
    Z.coprime y (rsa_N R) ->
    Problem_RSA (rsa_N R) (rsa_e R) (y mod rsa_N R)
      (rsa_dec R y).
Proof.
  intros R y Hcop.
  unfold Problem_RSA, rsa_problem.
  pose proof (rsa_enc_dec_units R y Hcop) as H.
  unfold rsa_enc in H. exact H.
Qed.

(** ** RSA vs strong RSA (relations)

    A prescribed-[e] root is a strong-RSA witness for that [e].
    The converse is false as a relation: strong RSA may choose [e].
    Hardness therefore runs the other way from solvability:
    strong-RSA-hard ⇒ RSA-hard (informal, [THEORY.md] §9.6). *)

Theorem rsa_solution_is_strong_RSA :
  forall N e y x,
    1 < e ->
    Problem_RSA N e y x ->
    Problem_StrongRSA N y x e.
Proof.
  intros N e y x He H.
  unfold Problem_StrongRSA, Problem_RSA, rsa_problem in *.
  split; assumption.
Qed.

(** Knowing [λ] makes strong RSA trivial on every unit: [(y, λ+1)]
    is a witness, because [y^λ ≡ 1].  Adaptive root in a group of
    *known* order is the same triviality. *)
Theorem lambda_solves_strong_RSA :
  forall p q y,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime y (p * q) ->
    let N := p * q in
    let lam := lambda_semiprime p q in
    Problem_StrongRSA N (y mod N) (y mod N) (lam + 1).
Proof.
  intros p q y Hp Hq Hneq Hcop N lam.
  unfold Problem_StrongRSA, N, lam.
  pose proof (lambda_semiprime_pos p q Hp Hq) as Hlam.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  split; [lia|].
  rewrite powm_mod_base by nia.
  replace (lambda_semiprime p q + 1)
    with (lambda_semiprime p q + 1) by reflexivity.
  rewrite powm_add_r; [| nia | lia | lia].
  rewrite (carmichael_semiprime p q y Hp Hq Hneq Hcop).
  rewrite Z.mul_1_l, powm_1_r, Z.mod_mod by nia.
  reflexivity.
Qed.

(** Strong RSA as a bare relation is inhabited at [y = 1]:
    [1^2 ≡ 1].  The assumption is about *random* [y], not existence. *)
Lemma strong_RSA_trivial_at_one :
  forall N, 1 < N -> Problem_StrongRSA N 1 1 2.
Proof.
  intros N HN. unfold Problem_StrongRSA, powm.
  split; [lia|].
  rewrite Z.pow_1_l, Z.mod_1_l by lia. reflexivity.
Qed.

Lemma rsa_trivial_at_one :
  forall N e, 1 < N -> 0 <= e -> Problem_RSA N e (1 mod N) 1.
Proof.
  intros N e HN He. unfold Problem_RSA, rsa_problem, powm.
  rewrite Z.pow_1_l by lia. reflexivity.
Qed.

(** ** Order divides the exponent *)

Lemma order_divides_annihilator :
  forall N a k M,
    1 < N ->
    0 <= M ->
    is_order N a k ->
    powm a M N = 1 ->
    (k | M).
Proof.
  intros N a k M HN HM [Hk [Hank Hmin]] HannM.
  pose proof (Z.div_mod M k ltac:(lia)) as Hdm.
  set (q := M / k) in *.
  set (r := M mod k) in *.
  assert (0 <= r < k) by (apply Z.mod_pos_bound; lia).
  assert (0 <= q).
  { apply Z.div_pos; lia. }
  rewrite Hdm in HannM.
  rewrite powm_add_r in HannM by lia.
  assert (powm a (k * q) N = 1) as Hmul.
  { rewrite (powm_one_mul a k q N);
      [apply Z.mod_small; lia | lia | lia | lia | exact Hank]. }
  rewrite Hmul, Z.mul_1_l in HannM.
  unfold powm in HannM.
  rewrite Z.mod_mod in HannM by lia.
  fold (powm a r N) in HannM.
  destruct (Z.eq_dec r 0) as [Hr0 | Hrn].
  - subst r. exists q. lia.
  - exfalso. apply (Hmin r); [lia | exact HannM].
Qed.

Theorem order_divides_lambda :
  forall p q a k,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime a (p * q) ->
    is_order (p * q) a k ->
    (k | lambda_semiprime p q).
Proof.
  intros p q a k Hp Hq Hneq Hcop Hord.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  apply (order_divides_annihilator (p * q) a k (lambda_semiprime p q)).
  - nia.
  - pose proof (lambda_semiprime_pos p q Hp Hq). lia.
  - exact Hord.
  - apply carmichael_semiprime; assumption.
Qed.

(** ** One-sided small exponent (the Type-B winning condition)

    [Problem_LowOrder] asks for small order *in* [(Z/NZ)*], which
    does not split [N] ([a^k ≡ 1 (mod N)] is two-sided).  A
    one-sided relation [a^k ≡ 1 (mod p)] and not [(mod q)] does. *)

Definition one_sided_low_order (p q a k : Z) : Prop :=
  Z.coprime a (p * q) /\
  0 <= k /\
  powm a k p = 1 /\
  powm a k q <> 1.

Theorem one_sided_low_order_factors :
  forall p q a k,
    Z.prime p -> Z.prime q -> p <> q ->
    one_sided_low_order p q a k ->
    Z.gcd (a ^ k - 1) (p * q) = p.
Proof.
  intros p q a k Hp Hq Hneq [Hcop [Hk [Hp1 Hnq]]].
  apply coprime_semiprime in Hcop; [| assumption | assumption | assumption].
  destruct Hcop as [Hap Haq].
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  apply gcd_onesided_semiprime; try assumption.
  - unfold powm in Hp1.
    apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Hp1, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity.
  - intro Hdiv.
    apply Z.mod_divide in Hdiv; [| lia].
    unfold powm in Hnq.
    rewrite Zminus_mod, Z.mod_1_l in Hdiv by lia.
    pose proof (Z.mod_pos_bound (a ^ k) q ltac:(lia)) as Hbd.
    pose proof (Z.div_mod (a ^ k mod q - 1) q ltac:(lia)) as Hdm.
    rewrite Hdiv, Z.add_0_r in Hdm.
    assert ((a ^ k mod q - 1) / q = 0) as Hz.
    { set (t := (a ^ k mod q - 1) / q) in *.
      destruct (Z.eq_dec t 0); [assumption|].
      assert (Z.abs (q * t) >= q).
      { rewrite Z.abs_mul, Z.abs_eq by lia.
        pose proof (Z.abs_pos t). nia. }
      lia. }
    rewrite Hz in Hdm. lia.
Qed.

Theorem one_sided_low_order_is_factor :
  forall p q a k,
    Z.prime p -> Z.prime q -> p <> q ->
    one_sided_low_order p q a k ->
    Problem_Factor (p * q) p.
Proof.
  intros p q a k Hp Hq Hneq Hone.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  split; [nia|]. exists q. apply Z.mul_comm.
Qed.

(** Adaptive root is the same *relation* as strong RSA.  The name
    changes with the group (no trapdoor in a class group). *)
Lemma adaptive_root_is_strong_RSA :
  forall N y x e,
    Problem_AdaptiveRoot N y x e <-> Problem_StrongRSA N y x e.
Proof. intros. reflexivity. Qed.

(** Adaptive root with a *known finite* challenge space is broken as
    a relation: A1 publishes [h^{c·rest}], A2 returns [h^{rest}].
    This is 2024/505 Remark 9 / BBF24, algebra only — no ROM.  If
    every challenge is [B]-smooth and the primes up to [B] are
    public and few, the same construction uses [rest] equal to a
    high enough power of those primes. *)
Theorem adaptive_root_known_product_breaks :
  forall N h c rest,
    1 < N ->
    0 <= h ->
    1 < c ->
    0 <= rest ->
    Problem_AdaptiveRoot N (powm h (c * rest) N) (powm h rest N) c.
Proof.
  intros N h c rest Hn Hh Hc Hr.
  unfold Problem_AdaptiveRoot, Problem_StrongRSA.
  split; [lia|].
  rewrite <- powm_mul_r by lia.
  rewrite Z.mul_comm.
  reflexivity.
Qed.

Theorem adaptive_root_smooth_power_breaks :
  forall N h p k,
    1 < N ->
    0 <= h ->
    1 < p ->
    0 <= k ->
    Problem_AdaptiveRoot N (powm h (p ^ (k + 1)) N)
      (powm h (p ^ k) N) p.
Proof.
  intros N h p k Hn Hh Hp Hk.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  rewrite Z.mul_comm.
  apply adaptive_root_known_product_breaks; [assumption | assumption | assumption |].
  apply Z.pow_nonneg; lia.
Qed.
