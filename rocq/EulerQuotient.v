From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.

Open Scope Z_scope.

(** * The Euler quotient: [a^{N+1} ≡ a^{p+q} (mod N)]

    Public object: the map [a ↦ a^{N+1} (mod N)].  Secret linear form:
    [s = p+q].  Algebra: [N + 1 = φ(N) + s], so on units this is Euler.
    Off units it is Fermat on each CRT side.

    Cross-confirmed by [cas/43_euler_quotient.gp].  That witness also
    runs the cheap bit-extraction battery.  Outcome: the only cheap
    readings of [s] are facts already functions of [N] ([s] even;
    [s mod 4] from [N mod 4]) and Fermat-in-the-exponent on close
    primes (Type A).  See [notes/sixth-type-plan.md] Method 2. *)

(** ** Reduction of [powm] along a factor *)

Lemma powm_mod_divisor :
  forall a e m n,
    0 < m -> 0 < n ->
    powm a e (m * n) mod n = powm a e n.
Proof.
  intros a e m n Hm Hn.
  unfold powm.
  set (x := a ^ e).
  set (mn := m * n).
  assert (mn | x - x mod mn) as Hmn.
  { apply Z.mod_divide; [nia|].
    rewrite Zminus_mod, Z.mod_mod by nia.
    rewrite Z.sub_diag, Z.mod_0_l by nia. reflexivity. }
  apply mods_eq_iff_divides; [lia|].
  replace (x mod mn - x) with (- (x - x mod mn)) by lia.
  apply Z.divide_opp_r.
  apply Z.divide_trans with mn; [apply Z.divide_factor_r | exact Hmn].
Qed.

Lemma powm_mod_prime_factor :
  forall a e p q,
    0 < p -> 0 < q ->
    powm a e (p * q) mod p = powm a e p.
Proof.
  intros a e p q Hp Hq.
  rewrite (Z.mul_comm p q).
  apply powm_mod_divisor; lia.
Qed.

Lemma powm_multiple :
  forall a e n,
    0 < n -> (n | a) -> 0 < e ->
    powm a e n = 0.
Proof.
  intros a e n Hn Hd He.
  unfold powm.
  apply Z.mod_divide; [lia|].
  destruct Hd as [k Hk]. rewrite Hk.
  rewrite Z.pow_mul_l, Z.mul_comm.
  apply Z.divide_mul_l.
  replace e with (1 + (e - 1)) by lia.
  rewrite Z.pow_add_r, Z.pow_1_r by lia.
  apply Z.divide_factor_l.
Qed.

Lemma not_coprime_prime_divides :
  forall a p,
    Z.prime p -> ~ Z.coprime a p -> (p | a).
Proof.
  intros a p Hp Hnc.
  pose proof (Z.prime_ge_2 p Hp).
  destruct (Z.eq_dec (a mod p) 0) as [Hz|Hnz].
  - apply Z.mod_divide; [lia | exact Hz].
  - exfalso. apply Hnc.
    rewrite coprime_comm, Z.coprime_prime_l_iff by exact Hp.
    intro Hd. apply Z.mod_divide in Hd; lia.
Qed.

Lemma fermat_powm :
  forall p a, Z.prime p -> powm a p p = a mod p.
Proof.
  intros p a Hp.
  pose proof (Z.prime_ge_2 p Hp).
  destruct (Z.eq_dec (Z.gcd a p) 1) as [Hc|Hnc].
  - assert (powm a p p = powm a (p - 1 + 1) p) as Hp1 by (f_equal; lia).
    rewrite Hp1, powm_add_r by lia.
    rewrite fermat_coprime by (exact Hp || exact Hc).
    rewrite powm_1_r, Z.mul_1_l, Z.mod_mod by lia. reflexivity.
  - assert (p | a) as Hd.
    { apply not_coprime_prime_divides; [exact Hp|].
      unfold Z.coprime. exact Hnc. }
    rewrite powm_multiple by (lia || exact Hd).
    symmetry. apply Z.mod_divide; [lia | exact Hd].
Qed.

Lemma powm_Nplus1_mod_p :
  forall p q a,
    Z.prime p -> 0 < q ->
    powm a (p * q + 1) p = powm a (q + 1) p.
Proof.
  intros p q a Hp Hq.
  pose proof (Z.prime_ge_2 p Hp).
  rewrite powm_add_r by nia.
  rewrite powm_1_r by lia.
  rewrite powm_mul_r by nia.
  rewrite fermat_powm by exact Hp.
  rewrite powm_mod_base by lia.
  rewrite (powm_add_r a q 1 p) by nia.
  rewrite powm_1_r by lia.
  reflexivity.
Qed.

Lemma powm_s_mod_p :
  forall p q a,
    Z.prime p -> 0 < q ->
    powm a (p + q) p = powm a (q + 1) p.
Proof.
  intros p q a Hp Hq.
  pose proof (Z.prime_ge_2 p Hp).
  rewrite (powm_add_r a p q p) by nia.
  rewrite fermat_powm by exact Hp.
  rewrite (powm_add_r a q 1 p) by nia.
  rewrite powm_1_r by lia.
  rewrite (Z.mul_comm (a mod p)).
  reflexivity.
Qed.

Lemma powm_Nplus1_eq_s_mod_p :
  forall p q a,
    Z.prime p -> 0 < q ->
    powm a (p * q + 1) p = powm a (p + q) p.
Proof.
  intros p q a Hp Hq.
  rewrite powm_Nplus1_mod_p, powm_s_mod_p by assumption. reflexivity.
Qed.

Lemma phi_plus_sum :
  forall p q, phi_semiprime p q + (p + q) = p * q + 1.
Proof. intros. unfold phi_semiprime. lia. Qed.

Theorem euler_quotient_units :
  forall p q a,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime a (p * q) ->
    powm a (p * q + 1) (p * q) = powm a (p + q) (p * q).
Proof.
  intros p q a Hp Hq Hneq Hcop.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  pose proof (phi_semiprime_pos p q Hp Hq).
  replace (p * q + 1) with (phi_semiprime p q + (p + q))
    by (rewrite phi_plus_sum; reflexivity).
  rewrite powm_add_r by nia.
  rewrite euler_semiprime by assumption.
  rewrite Z.mul_1_l.
  unfold powm at 1. rewrite Z.mod_mod by nia.
  reflexivity.
Qed.

Theorem euler_quotient :
  forall p q a,
    Z.prime p -> Z.prime q -> p <> q ->
    powm a (p * q + 1) (p * q) = powm a (p + q) (p * q).
Proof.
  intros p q a Hp Hq Hneq.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  unfold powm. apply crt_mod_eq; try assumption.
  - fold (powm a (p * q + 1) p). fold (powm a (p + q) p).
    apply powm_Nplus1_eq_s_mod_p; [exact Hp | lia].
  - replace (p * q + 1) with (q * p + 1) by lia.
    replace (p + q) with (q + p) by lia.
    fold (powm a (q * p + 1) q). fold (powm a (q + p) q).
    apply powm_Nplus1_eq_s_mod_p; [exact Hq | lia].
Qed.

Lemma powm_reduce_to_qminus1 :
  forall p q a,
    Z.prime p -> 1 < q ->
    powm a (p * q - 1) p = powm a (q - 1) p /\
    powm a (p + q - 2) p = powm a (q - 1) p.
Proof.
  intros p q a Hp Hq.
  pose proof (Z.prime_ge_2 p Hp).
  destruct (Z.eq_dec (Z.gcd a p) 1) as [Hc|Hnc].
  - split.
    + replace (p * q - 1) with (p * (q - 1) + (p - 1)) by lia.
      rewrite powm_add_r by nia.
      rewrite fermat_coprime by (exact Hp || exact Hc).
      rewrite Z.mul_1_r.
      unfold powm at 1. rewrite Z.mod_mod by lia.
      fold (powm a (p * (q - 1)) p).
      rewrite powm_mul_r by nia.
      rewrite fermat_powm by exact Hp.
      apply powm_mod_base; lia.
    + replace (p + q - 2) with ((q - 1) + (p - 1)) by lia.
      rewrite powm_add_r by nia.
      rewrite fermat_coprime by (exact Hp || exact Hc).
      rewrite Z.mul_1_r.
      unfold powm at 1. rewrite Z.mod_mod by lia.
      reflexivity.
  - assert (p | a) as Hd.
    { apply not_coprime_prime_divides; [exact Hp|].
      unfold Z.coprime. exact Hnc. }
    split;
      rewrite powm_multiple by (lia || exact Hd);
      rewrite powm_multiple by (lia || exact Hd);
      reflexivity.
Qed.

Lemma powm_Nminus1_mod_p :
  forall p q a,
    Z.prime p -> 1 < q ->
    powm a (p * q - 1) p = powm a (p + q - 2) p.
Proof.
  intros p q a Hp Hq.
  destruct (powm_reduce_to_qminus1 p q a Hp Hq) as [H1 H2].
  rewrite H1, H2. reflexivity.
Qed.

Theorem euler_quotient_pred :
  forall p q a,
    Z.prime p -> Z.prime q -> p <> q ->
    powm a (p * q - 1) (p * q) = powm a (p + q - 2) (p * q).
Proof.
  intros p q a Hp Hq Hneq.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  unfold powm. apply crt_mod_eq; try assumption.
  - fold (powm a (p * q - 1) p). fold (powm a (p + q - 2) p).
    apply powm_Nminus1_mod_p; [exact Hp | lia].
  - replace (p * q - 1) with (q * p - 1) by lia.
    replace (p + q - 2) with (q + p - 2) by lia.
    fold (powm a (q * p - 1) q). fold (powm a (q + p - 2) q).
    apply powm_Nminus1_mod_p; [exact Hq | lia].
Qed.

(** ** Bits of [s] that are functions of [N], not of the quotient *)

Lemma prime_2 : Z.prime 2.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1) by lia. subst. reflexivity.
Qed.

Lemma odd_prime_mod2 :
  forall p, Z.prime p -> 2 < p -> p mod 2 = 1.
Proof.
  intros p Hp Hp2.
  pose proof (Z.mod_pos_bound p 2 ltac:(lia)).
  assert (p mod 2 = 0 \/ p mod 2 = 1) by lia.
  destruct H0 as [He|Ho]; [| exact Ho].
  apply Z.mod_divide in He; [| lia].
  apply Z.divide_prime_prime in He; [lia | exact prime_2 | exact Hp].
Qed.

Theorem odd_primes_sum_even :
  forall p q,
    Z.prime p -> Z.prime q -> 2 < p -> 2 < q ->
    (p + q) mod 2 = 0.
Proof.
  intros p q Hp Hq Hpt Hqt.
  rewrite Z.add_mod by lia.
  rewrite (odd_prime_mod2 p Hp Hpt), (odd_prime_mod2 q Hq Hqt).
  reflexivity.
Qed.

Lemma odd_prime_mod4 :
  forall p, Z.prime p -> 2 < p -> p mod 4 = 1 \/ p mod 4 = 3.
Proof.
  intros p Hp Hp2.
  pose proof (Z.mod_pos_bound p 4 ltac:(lia)).
  assert (p mod 4 = 0 \/ p mod 4 = 1 \/ p mod 4 = 2 \/ p mod 4 = 3) by lia.
  destruct H0 as [H0|[H1|[H2|H3]]]; try tauto.
  - apply Z.mod_divide in H0; [| lia].
    assert (2 | p) as H2p.
    { destruct H0 as [k Hk]. exists (2 * k). lia. }
    apply Z.divide_prime_prime in H2p; [lia | exact prime_2 | exact Hp].
  - assert (2 | p) as H2p.
    { rewrite (Z.div_mod p 4 ltac:(lia)), H2.
      exists (2 * (p / 4) + 1). lia. }
    apply Z.divide_prime_prime in H2p; [lia | exact prime_2 | exact Hp].
Qed.

Theorem sum_mod4_of_N :
  forall p q,
    Z.prime p -> Z.prime q -> 2 < p -> 2 < q ->
    (p * q) mod 4 = 1 /\ (p + q) mod 4 = 2 \/
    (p * q) mod 4 = 3 /\ (p + q) mod 4 = 0.
Proof.
  intros p q Hp Hq Hpt Hqt.
  destruct (odd_prime_mod4 p Hp Hpt) as [Hp1|Hp3];
  destruct (odd_prime_mod4 q Hq Hqt) as [Hq1|Hq3].
  - left. split.
    + rewrite Z.mul_mod, Hp1, Hq1 by lia. reflexivity.
    + rewrite Z.add_mod, Hp1, Hq1 by lia. reflexivity.
  - right. split.
    + rewrite Z.mul_mod, Hp1, Hq3 by lia. reflexivity.
    + rewrite Z.add_mod, Hp1, Hq3 by lia. reflexivity.
  - right. split.
    + rewrite Z.mul_mod, Hp3, Hq1 by lia. reflexivity.
    + rewrite Z.add_mod, Hp3, Hq1 by lia. reflexivity.
  - left. split.
    + rewrite Z.mul_mod, Hp3, Hq3 by lia. reflexivity.
    + rewrite Z.add_mod, Hp3, Hq3 by lia. reflexivity.
Qed.

Theorem euler_quotient_rsa :
  forall R a,
    powm a (rsa_N R + 1) (rsa_N R) = powm a (rsa_p R + rsa_q R) (rsa_N R).
Proof.
  intros R a. unfold rsa_N.
  apply euler_quotient;
    [apply rsa_p_prime | apply rsa_q_prime | apply rsa_distinct].
Qed.
