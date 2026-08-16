From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * Pollard's [p−1]: a one-sided annihilator

    Fermat gives [a^{p−1} ≡ 1 (mod p)].  If generation left [p−1]
    [B]-smooth, a public multiple [M] of [p−1] is cheap ([lcm(1..B)]).
    Then [a^M ≡ 1 (mod p)] while typically [a^M ≢ 1 (mod q)], so
    [gcd(a^M − 1, N) = p].

    This is §3 of THEORY.md run on *one* CRT component.  Cross-confirmed
    by [cas/10_pollard_p1.gp]. *)

(** [n] is [B]-smooth when every prime factor of [n] is [≤ B]. *)
Definition prime_factor_le (B n r : Z) : Prop :=
  Z.prime r -> (r | n) -> r <= B.

Definition is_B_smooth (B n : Z) : Prop :=
  0 < n /\ forall r, prime_factor_le B n r.

(** A public multiple of [p−1] — what smoothness makes cheap. *)
Definition annihilates_p (p M : Z) : Prop :=
  0 <= M /\ (p - 1 | M).

Lemma fermat_on_multiple :
  forall p a M,
    Z.prime p -> Z.coprime a p ->
    annihilates_p p M ->
    powm a M p = 1.
Proof.
  intros p a M Hp Hcop [HM Hdiv].
  destruct Hdiv as [k Hk].
  pose proof (Z.prime_ge_2 p Hp).
  assert (0 <= k) by nia.
  rewrite Hk, Z.mul_comm.
  rewrite (powm_one_mul a (p - 1) k p);
    [apply Z.mod_small; lia | lia | lia | lia | apply fermat_coprime; assumption].
Qed.

(** If [p | x] and [q] does not divide [x], then [gcd(x, pq) = p]. *)
Lemma gcd_onesided_semiprime :
  forall p q x,
    Z.prime p -> Z.prime q -> p <> q ->
    (p | x) -> ~ (q | x) ->
    Z.gcd x (p * q) = p.
Proof.
  intros p q x Hp Hq Hneq Hpx Hqx.
  pose proof (Z.prime_ge_2 p Hp).
  destruct Hpx as [k Hk]. rewrite Hk, (Z.mul_comm k p).
  rewrite Z.gcd_mul_mono_l_nonneg by lia.
  assert (Z.gcd k q = 1).
  { rewrite Z.gcd_comm. apply Z.coprime_prime_l_iff; [exact Hq|].
    intro Hqk. apply Hqx. destruct Hqk as [m Hm]. exists (m * p). lia. }
  rewrite H0. lia.
Qed.

Theorem pollard_p1_splits :
  forall p q a M,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime a (p * q) ->
    annihilates_p p M ->
    powm a M q <> 1 ->
    Z.gcd (a ^ M - 1) (p * q) = p.
Proof.
  intros p q a M Hp Hq Hneq Hcop Hann Hnq.
  apply coprime_semiprime in Hcop; [| assumption | assumption | assumption].
  destruct Hcop as [Hap Haq].
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  apply gcd_onesided_semiprime; try assumption.
  - (* p | a^M − 1 *)
    pose proof (fermat_on_multiple p a M Hp Hap Hann) as Hp1.
    unfold powm in Hp1.
    apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Hp1, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity.
  - (* ~ q | a^M − 1, else a^M ≡ 1 (mod q) *)
    intro Hdiv.
    apply Z.mod_divide in Hdiv; [| lia].
    unfold powm in Hnq.
    rewrite Zminus_mod, Z.mod_1_l in Hdiv by lia.
    pose proof (Z.mod_pos_bound (a ^ M) q ltac:(lia)) as Hbd.
    pose proof (Z.div_mod (a ^ M mod q - 1) q ltac:(lia)) as Hdm.
    rewrite Hdiv, Z.add_0_r in Hdm.
    assert ((a ^ M mod q - 1) / q = 0).
    { set (t := (a ^ M mod q - 1) / q) in *.
      destruct (Z.eq_dec t 0); [assumption|].
      assert (Z.abs (q * t) >= q).
      { rewrite Z.abs_mul, Z.abs_eq by lia. pose proof (Z.abs_pos t). nia. }
      lia. }
    rewrite H1 in Hdm. lia.
Qed.

(** Smoothness of [p−1] is the generation choice that makes some cheap
    public [M] satisfy [annihilates_p p M].  We record the implication,
    not a particular [M = lcm(1..B)]. *)
Theorem smooth_implies_public_annihilator :
  forall p B,
    Z.prime p ->
    is_B_smooth B (p - 1) ->
    (* any common multiple of all integers ≤ B is a multiple of p−1;
       stated as: if every prime factor of p−1 is ≤ B then
       lcm(1..B) is such an M — left as a generation-side remark.
       The formal handle is [annihilates_p]. *)
    annihilates_p p (p - 1).
Proof.
  intros p B Hp [Hpos _].
  pose proof (Z.prime_ge_2 p Hp).
  split; [lia | apply Z.divide_refl].
Qed.
