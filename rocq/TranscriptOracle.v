From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.QuadRecip.
Require Import RSA.
Require Import PollardP1.

Open Scope Z_scope.

(** * Transcripts and oracles (bit leakage after the key is used)

    Catalog: [notes/transcript-oracle-plan.md].  CAS [57].
    Each lemma is a named interface, not a PPT game. *)

(** ** Shared algebra *)

Lemma powm_mul_l_mod :
  forall a b e n,
    n <> 0 ->
    0 <= e ->
    powm (a * b) e n = (powm a e n * powm b e n) mod n.
Proof.
  intros a b e n Hn He.
  unfold powm. rewrite Z.pow_mul_l. apply Z.mul_mod; lia.
Qed.

Lemma mod_mod_factor :
  forall x p q,
    0 < p -> 0 < q ->
    (x mod (p * q)) mod p = x mod p.
Proof.
  intros x p q Hp Hq.
  pose proof (Z.div_mod x (p * q) ltac:(nia)) as Hx.
  assert (x = x mod (p * q) + (x / (p * q) * q) * p) by nia.
  rewrite H at 2.
  rewrite Z.mod_add by lia.
  reflexivity.
Qed.

Lemma powm_mod_factor :
  forall a e p q,
    0 < p -> 0 < q -> 0 <= e ->
    powm a e (p * q) mod p = powm a e p.
Proof.
  intros a e p q Hp Hq He.
  unfold powm.
  rewrite (mod_mod_factor (a ^ e) p q Hp Hq).
  reflexivity.
Qed.

Lemma powm_exp_mod_factor :
  forall a e k p q,
    0 < p -> 0 < q -> 0 <= e -> 0 <= k ->
    powm (powm a e (p * q)) k p = powm (powm a e p) k p.
Proof.
  intros a e k p q Hp Hq He Hk.
  unfold powm.
  rewrite <- (Z.mod_pow_l (a ^ e mod (p * q)) k p) by lia.
  rewrite (mod_mod_factor (a ^ e) p q Hp Hq).
  rewrite (Z.mod_pow_l (a ^ e) k p) by lia.
  reflexivity.
Qed.

Lemma even_pow_neg1_is_one :
  forall t N,
    1 < N ->
    0 <= t ->
    powm (N - 1) (2 * t) N = 1.
Proof.
  intros t N HN Ht.
  unfold powm.
  rewrite Z.pow_mul_r, Z.pow_2_r by lia.
  replace ((N - 1) * (N - 1)) with (1 + (N - 2) * N) by ring.
  rewrite <- Z.mod_pow_l by lia.
  rewrite Z.mod_add, Z.mod_1_l by lia.
  rewrite Z.pow_1_l by lia.
  apply Z.mod_1_l; lia.
Qed.

Lemma odd_pow_neg1 :
  forall k N,
    1 < N ->
    0 <= k ->
    Z.Odd k ->
    powm (N - 1) k N = N - 1.
Proof.
  intros k N HN Hk [t Ht].
  assert (0 <= t) by lia.
  unfold powm. rewrite Ht.
  replace (2 * t + 1) with (Z.succ (2 * t)) by lia.
  rewrite Z.pow_succ_r by lia.
  rewrite (Z.mul_comm (N - 1)).
  rewrite <- Z.mul_mod_idemp_l by lia.
  replace ((N - 1) ^ (2 * t) mod N) with 1.
  2:{ change ((N - 1) ^ (2 * t) mod N) with (powm (N - 1) (2 * t) N).
      symmetry. apply even_pow_neg1_is_one; lia. }
  rewrite Z.mul_1_l, Z.mod_small by lia.
  reflexivity.
Qed.

(** ** T5 — [(c/N) = (m/N)] for odd [e]

    Euler on each prime: [m^e] has the same criterion as [m].
    Jacobi of the ciphertext is therefore a public bit of [m],
    not a query.  Contrast T12 (LSB of [m] is not public). *)

Theorem euler_odd_power :
  forall a e p,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    0 <= e ->
    Z.Odd e ->
    euler_crit (powm a e p) p = euler_crit a p.
Proof.
  intros a e p Hp Hne Hcop He Hodd.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (half_pm1_nonneg p Hp Hne).
  unfold euler_crit.
  rewrite <- powm_mul_r by lia.
  rewrite (Z.mul_comm e), powm_mul_r by lia.
  pose proof (euler_is_pm1 a p Hp Hne Hcop) as Hpm.
  unfold euler_crit in Hpm.
  destruct Hpm as [H1 | Hm1].
  - rewrite H1, powm_1_pow by lia. apply Z.mod_small; lia.
  - rewrite Hm1. apply odd_pow_neg1; [lia | lia | exact Hodd].
Qed.

Theorem rsa_cipher_euler_eq_message :
  forall R m,
    Z.Odd (rsa_e R) ->
    rsa_p R <> 2 ->
    Z.coprime m (rsa_p R) ->
    euler_crit (rsa_enc R m) (rsa_p R) = euler_crit m (rsa_p R).
Proof.
  intros R m He Hp2 Hcop.
  pose proof (Z.prime_ge_2 _ (rsa_p_prime R)).
  pose proof (Z.prime_ge_2 _ (rsa_q_prime R)).
  pose proof (rsa_e_pos R).
  pose proof (half_pm1_nonneg (rsa_p R) (rsa_p_prime R) Hp2).
  unfold rsa_enc, rsa_N, euler_crit.
  rewrite powm_exp_mod_factor by lia.
  fold (euler_crit (powm m (rsa_e R) (rsa_p R)) (rsa_p R)).
  fold (euler_crit m (rsa_p R)).
  apply euler_odd_power; [apply rsa_p_prime | exact Hp2 | exact Hcop | lia | exact He].
Qed.

Theorem rsa_cipher_euler_eq_message_q :
  forall R m,
    Z.Odd (rsa_e R) ->
    rsa_q R <> 2 ->
    Z.coprime m (rsa_q R) ->
    euler_crit (rsa_enc R m) (rsa_q R) = euler_crit m (rsa_q R).
Proof.
  intros R m He Hq2 Hcop.
  pose proof (Z.prime_ge_2 _ (rsa_p_prime R)).
  pose proof (Z.prime_ge_2 _ (rsa_q_prime R)).
  pose proof (rsa_e_pos R).
  pose proof (half_pm1_nonneg (rsa_q R) (rsa_q_prime R) Hq2).
  unfold rsa_enc, rsa_N, euler_crit.
  rewrite (Z.mul_comm (rsa_p R)).
  rewrite powm_exp_mod_factor by lia.
  fold (euler_crit (powm m (rsa_e R) (rsa_q R)) (rsa_q R)).
  fold (euler_crit m (rsa_q R)).
  apply euler_odd_power; [apply rsa_q_prime | exact Hq2 | exact Hcop | lia | exact He].
Qed.

(** ** T24 / T25 — sign homomorphism and decrypt blinding *)

Theorem sign_homomorphism :
  forall R m1 m2,
    powm (m1 * m2) (rsa_d R) (rsa_N R) =
      (powm m1 (rsa_d R) (rsa_N R) *
       powm m2 (rsa_d R) (rsa_N R)) mod rsa_N R.
Proof.
  intros R m1 m2.
  pose proof (rsa_N_gt_1 R).
  pose proof (rsa_d_pos R).
  apply powm_mul_l_mod; lia.
Qed.

Theorem sign_of_one :
  forall R, powm 1 (rsa_d R) (rsa_N R) = 1.
Proof.
  intros R.
  pose proof (rsa_N_gt_1 R).
  pose proof (rsa_d_pos R).
  unfold powm. rewrite Z.pow_1_l by lia. apply Z.mod_small; lia.
Qed.

Theorem sign_inverse :
  forall R m w,
    Z.coprime m (rsa_N R) ->
    (m * w) mod rsa_N R = 1 ->
    (powm m (rsa_d R) (rsa_N R) * powm w (rsa_d R) (rsa_N R))
      mod rsa_N R = 1.
Proof.
  intros R m w Hcop Hinv.
  pose proof (rsa_N_gt_1 R).
  pose proof (rsa_d_pos R).
  rewrite <- sign_homomorphism.
  unfold powm.
  rewrite <- Z.mod_pow_l by lia.
  rewrite Hinv.
  rewrite Z.pow_1_l by lia.
  apply Z.mod_small; lia.
Qed.

Theorem decrypt_blinding :
  forall R c r,
    Z.coprime c (rsa_N R) ->
    Z.coprime r (rsa_N R) ->
    rsa_dec R ((c * rsa_enc R r) mod rsa_N R) =
      (rsa_dec R c * r) mod rsa_N R.
Proof.
  intros R c r Hc Hr.
  pose proof (rsa_N_gt_1 R).
  pose proof (rsa_d_pos R).
  pose proof (rsa_e_pos R).
  unfold rsa_dec, rsa_enc.
  rewrite powm_mod_base by lia.
  rewrite powm_mul_l_mod by lia.
  fold (rsa_dec R c).
  fold (rsa_enc R r).
  fold (rsa_dec R (rsa_enc R r)).
  rewrite (rsa_dec_enc_units R r Hr).
  rewrite Z.mul_mod_idemp_r by lia.
  reflexivity.
Qed.

Theorem decrypt_double_is_double :
  forall R c,
    Z.coprime c (rsa_N R) ->
    Z.coprime 2 (rsa_N R) ->
    rsa_dec R ((c * rsa_enc R 2) mod rsa_N R) =
      (2 * rsa_dec R c) mod rsa_N R.
Proof.
  intros R c Hc H2.
  rewrite decrypt_blinding by assumption.
  rewrite Z.mul_comm. reflexivity.
Qed.

(** ** T12 — LSB of [2m mod N] is the half-interval bit

    [N] odd ⇒ [lsb((2m) mod N) = 0] iff [m < N/2].  That is the
    MSB/Manger bit, implemented by an LSB oracle after a
    multiplicative double (T25 with [r = 2]). *)

Definition lsb (x : Z) : Z := x mod 2.

Theorem lsb_double_decides_half :
  forall m N,
    0 <= m < N ->
    N mod 2 = 1 ->
    (lsb ((2 * m) mod N) = 0 <-> 2 * m < N).
Proof.
  intros m N Hm Hodd.
  unfold lsb.
  assert (0 < N) by lia.
  destruct (Z.lt_ge_cases (2 * m) N) as [Hlt | Hge].
  - assert (H2m : 0 <= 2 * m < N) by lia.
    rewrite (Z.mod_small (2 * m) N H2m).
    rewrite (Z.mul_comm 2 m), Z.mod_mul by lia.
    split; intros; lia.
  - assert (0 <= 2 * m - N < N) by lia.
    rewrite (Z.mod_eq (2 * m) N) by lia.
    replace (2 * m / N) with 1.
    2:{ pose proof (Z.div_mod (2 * m) N ltac:(lia)).
        pose proof (Z.mod_pos_bound (2 * m) N ltac:(lia)).
        assert (2 * m < 2 * N) by lia.
        assert (1 <= 2 * m / N < 2) by nia.
        lia. }
    replace (2 * m - N * 1) with (2 * m - N) by lia.
    replace ((2 * m - N) mod 2) with 1.
    2:{ rewrite Zminus_mod.
        rewrite (Z.mul_comm 2 m), Z.mod_mul, Hodd by lia.
        reflexivity. }
    split; [discriminate | lia].
Qed.

Theorem lsb_double_decides_half_ge :
  forall m N,
    0 <= m < N ->
    N mod 2 = 1 ->
    (lsb ((2 * m) mod N) = 1 <-> N <= 2 * m).
Proof.
  intros m N Hm Hodd.
  pose proof (lsb_double_decides_half m N Hm Hodd) as H.
  unfold lsb in *.
  assert ((2 * m) mod N mod 2 = 0 \/ (2 * m) mod N mod 2 = 1).
  { pose proof (Z.mod_pos_bound ((2 * m) mod N) 2 ltac:(lia)). lia. }
  destruct H0 as [H0 | H0]; split; intro Hm1; try lia;
    try (rewrite H0 in Hm1; discriminate).
Qed.

(** ** T11 — a comparison oracle recovers [m] by interval halving *)

Lemma pow2_nat_pos : forall k, 0 < 2 ^ Z.of_nat k.
Proof. intros k. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow2_nat_succ :
  forall k, 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k.
Proof.
  intros k.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  reflexivity.
Qed.

Fixpoint recover_interval (k : nat) (lo : Z) (ltB : Z -> bool) : Z :=
  match k with
  | O => lo
  | S k' =>
      let mid := lo + 2 ^ Z.of_nat k' in
      if ltB mid then recover_interval k' lo ltB
      else recover_interval k' mid ltB
  end.

Theorem recover_interval_correct :
  forall k lo m,
    lo <= m < lo + 2 ^ Z.of_nat k ->
    recover_interval k lo (fun B => m <? B) = m.
Proof.
  induction k as [| k IH]; intros lo m Hm.
  - simpl in *. lia.
  - simpl.
    pose proof (pow2_nat_pos k).
    rewrite pow2_nat_succ in Hm.
    destruct (m <? lo + 2 ^ Z.of_nat k) eqn:Hcmp.
    + apply Z.ltb_lt in Hcmp. apply IH. lia.
    + apply Z.ltb_ge in Hcmp. apply IH. lia.
Qed.

Theorem recover_from_half_tests :
  forall k m,
    0 <= m < 2 ^ Z.of_nat k ->
    recover_interval k 0 (fun B => m <? B) = m.
Proof. intros k m Hm. apply recover_interval_correct. lia. Qed.

(** ** T4 — common modulus, coprime exponents *)

Theorem common_modulus_identity :
  forall m e1 e2 a k N,
    N <> 0 ->
    0 <= e1 ->
    0 <= e2 ->
    0 <= a ->
    0 <= k ->
    e1 * a = 1 + e2 * k ->
    powm (powm m e1 N) a N = (m * powm (powm m e2 N) k N) mod N.
Proof.
  intros m e1 e2 a k N HN He1 He2 Ha Hk Hrel.
  rewrite <- powm_mul_r by lia.
  rewrite Hrel.
  rewrite powm_add_r by lia.
  rewrite powm_1_r by lia.
  rewrite <- powm_mul_r by lia.
  rewrite Z.mul_mod_idemp_l by lia.
  reflexivity.
Qed.

Theorem common_modulus_recovers :
  forall m e1 e2 a k N w,
    1 < N ->
    0 <= e1 ->
    0 <= e2 ->
    0 <= a ->
    0 <= k ->
    e1 * a = 1 + e2 * k ->
    (powm (powm m e2 N) k N * w) mod N = 1 ->
    (powm (powm m e1 N) a N * w) mod N = m mod N.
Proof.
  intros m e1 e2 a k N w HN He1 He2 Ha Hk Hrel Hinv.
  rewrite (common_modulus_identity m e1 e2 a k N) by lia.
  rewrite Z.mul_mod_idemp_l by lia.
  rewrite <- Z.mul_assoc.
  rewrite <- Z.mul_mod_idemp_r by lia.
  rewrite Hinv.
  rewrite Z.mul_1_r.
  reflexivity.
Qed.

Lemma coprime_to_nonneg_bezout :
  forall e1 e2,
    0 < e1 ->
    1 < e2 ->
    Z.gcd e1 e2 = 1 ->
    exists a k, 0 <= a < e2 /\ 0 <= k /\ e1 * a = 1 + e2 * k.
Proof.
  intros e1 e2 He1 He2 Hg.
  destruct (Z.gcd_bezout e1 e2 1 Hg) as [s' [t' Hlin]].
  set (a := s' mod e2).
  assert (0 <= a < e2) by (subst a; apply Z.mod_pos_bound; lia).
  assert (s' = e2 * (s' / e2) + a) as Hs.
  { subst a. apply Z.div_mod; lia. }
  rewrite Hs in Hlin.
  set (u := s' / e2 * e1 + t').
  assert (a <> 0).
  { intro Hz. rewrite Hz, Z.add_0_r in Hlin.
    replace ((e2 * (s' / e2)) * e1 + t' * e2)
      with (e2 * (s' / e2 * e1 + t')) in Hlin by ring.
    assert (e2 | 1) by (exists (s' / e2 * e1 + t'); lia).
    apply Z.divide_1_r in H0. lia. }
  replace ((e2 * (s' / e2) + a) * e1 + t' * e2)
    with (a * e1 + e2 * u) in Hlin by (subst u; ring).
  exists a, (- u).
  split; [lia|].
  split; [nia | nia].
Qed.

(** ** T29 — Bellcore / CRT-fault signature *)

Theorem bellcore_factors :
  forall p q e sig m,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    0 <= e ->
    powm sig e p = m mod p ->
    powm sig e q <> m mod q ->
    Z.gcd (powm sig e (p * q) - m) (p * q) = p.
Proof.
  intros p q e sig m Hp Hq Hneq He Hp1 Hnq.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  apply gcd_onesided_semiprime; try assumption.
  - apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, powm_mod_factor, Hp1, Zminus_mod, Z.sub_diag, Z.mod_0_l
      by lia.
    reflexivity.
  - intro Hdiv.
    apply Z.mod_divide in Hdiv; [| lia].
    rewrite Zminus_mod, Z.mul_comm, powm_mod_factor in Hdiv by lia.
    apply Hnq.
    assert (Hq1 : 0 <= powm sig e q < q) by (unfold powm; apply Z.mod_pos_bound; lia).
    assert (Hq2 : 0 <= m mod q < q) by (apply Z.mod_pos_bound; lia).
    assert (q | powm sig e q - m mod q) by (apply Z.mod_divide; [lia | exact Hdiv]).
    destruct H1 as [k Hk].
    assert (k = 0) by nia.
    lia.
Qed.

Theorem bellcore_is_factor :
  forall p q e sig m,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    0 <= e ->
    powm sig e p = m mod p ->
    powm sig e q <> m mod q ->
    let g := Z.gcd (powm sig e (p * q) - m) (p * q) in
    1 < g < p * q /\ (g | p * q).
Proof.
  intros p q e sig m Hp Hq Hneq He Hp1 Hnq g.
  pose proof (bellcore_factors p q e sig m Hp Hq Hneq He Hp1 Hnq) as Hg.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  subst g. rewrite Hg.
  split; [nia | exists q; ring].
Qed.

(** ** K1 — one-sided vanishing predicate factors *)

Theorem one_sided_congruence_factors :
  forall p q m a,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    m mod p = a mod p ->
    m mod q <> a mod q ->
    Z.gcd (m - a) (p * q) = p.
Proof.
  intros p q m a Hp Hq Hneq Hp1 Hnq.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  apply gcd_onesided_semiprime; try assumption.
  - apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Hp1, Z.sub_diag, Z.mod_0_l by lia. reflexivity.
  - intro Hdiv.
    apply Z.mod_divide in Hdiv; [| lia].
    rewrite Zminus_mod in Hdiv.
    apply Hnq.
    assert (0 <= m mod q < q) by (apply Z.mod_pos_bound; lia).
    assert (0 <= a mod q < q) by (apply Z.mod_pos_bound; lia).
    assert (q | m mod q - a mod q) by (apply Z.mod_divide; [lia | exact Hdiv]).
    destruct H3 as [k Hk].
    assert (k = 0) by nia.
    lia.
Qed.

(** ** K5 — Williams [(2/p)] is the KeyGen shape, not a transcript bit

    A Williams pair has [N ≡ 5 (mod 8)].  That congruence is not
    sufficient: [5·17 = 85 ≡ 5 (mod 8)] is not Williams, and the
    two-characters differ from the Williams pair. *)

Lemma prime_5 : Z.prime 5.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
  intuition subst; reflexivity.
Qed.

Theorem williams_N_mod8 :
  forall p q,
    p mod 8 = 3 ->
    q mod 8 = 7 ->
    (p * q) mod 8 = 5.
Proof.
  intros p q Hp Hq.
  rewrite Z.mul_mod, Hp, Hq by lia. reflexivity.
Qed.

Theorem non_williams_N_mod8_5 :
  (5 * 17) mod 8 = 5 /\ 5 mod 8 = 5 /\ 17 mod 8 = 1.
Proof. split; [reflexivity | split; reflexivity]. Qed.

Theorem williams_two_is_shape :
  forall p q,
    Z.prime p ->
    Z.prime q ->
    p mod 8 = 3 ->
    q mod 8 = 7 ->
    legendre_two p = -1 /\ legendre_two q = 1.
Proof.
  intros p q Hp Hq H3 H7.
  split.
  - apply two_legendre_williams_p; assumption.
  - apply two_legendre_williams_q; assumption.
Qed.

Theorem non_williams_two_chars :
  legendre_two 5 = -1 /\ legendre_two 17 = 1.
Proof.
  split.
  - pose proof (two_supplement 5 prime_5 ltac:(discriminate)) as [_ [_ [H5 _]]].
    apply H5; reflexivity.
  - pose proof (two_supplement 17 prime_17 ltac:(discriminate)) as [H1 _].
    apply H1; reflexivity.
Qed.

(** ** K13 / T6 — odd [d] sends [−1] to [−1]; no extra 2-height *)

Theorem sign_neg1_odd :
  forall R,
    Z.Odd (rsa_d R) ->
    powm (rsa_N R - 1) (rsa_d R) (rsa_N R) = rsa_N R - 1.
Proof.
  intros R Hodd.
  apply odd_pow_neg1.
  - apply rsa_N_gt_1.
  - pose proof (rsa_d_pos R); lia.
  - exact Hodd.
Qed.

Theorem odd_exp_preserves_minus1 :
  forall a k N,
    1 < N ->
    0 <= k ->
    Z.Odd k ->
    powm a 2 N = 1 ->
    a mod N = N - 1 ->
    powm a k N = N - 1.
Proof.
  intros a k N HN Hk Hodd Hsq Ha.
  rewrite <- powm_mod_base by lia.
  rewrite Ha.
  apply odd_pow_neg1; [lia | lia | exact Hodd].
Qed.
