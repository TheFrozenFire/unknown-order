From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.QuadRecip.

Open Scope Z_scope.

(** * Quadratic residues and the [p ≡ 3 (mod 4)] square-root formula

    Building blocks for Rabin–Williams.  Euler's criterion is proved
    both ways: a square has value [1]; value [p−1] is QNR
    ([RocqProofs.QuadRecip]).  [(2/p) = (−1)^{(p²−1)/8}] is
    [two_supplement].  Cross-confirmed by [cas/19_rabin_williams.gp]. *)

Definition is_qr (a p : Z) : Prop :=
  exists x, (x * x) mod p = a mod p.

Definition euler_crit (a p : Z) : Z := powm a ((p - 1) / 2) p.

Lemma odd_prime_minus1_even :
  forall p, Z.prime p -> p <> 2 -> Z.Even (p - 1).
Proof.
  intros p Hp Hne.
  pose proof (Z.prime_ge_2 p Hp).
  destruct (Z.even p) eqn:Hev.
  - apply Z.even_spec in Hev. destruct Hev as [k Hk].
    assert (2 | p) by (exists k; lia).
    apply Z.divide_prime_prime in H0;
      [lia | exact Z.prime_2 | exact Hp].
  - assert (Z.odd p = true) as Hodd
      by (rewrite <- Z.negb_even, Hev; reflexivity).
    apply Z.odd_spec in Hodd. destruct Hodd as [k Hk].
    exists k. lia.
Qed.

Lemma p_mod4_3_decomp :
  forall p, p mod 4 = 3 -> p = 4 * (p / 4) + 3.
Proof.
  intros p H. pose proof (Z.div_mod p 4 ltac:(lia)). lia.
Qed.

Lemma p_mod8_decomp :
  forall p r, p mod 8 = r -> p = 8 * (p / 8) + r.
Proof.
  intros p r H. pose proof (Z.div_mod p 8 ltac:(lia)). lia.
Qed.

Lemma mod8_3_is_mod4_3 :
  forall p, p mod 8 = 3 -> p mod 4 = 3.
Proof.
  intros p H. rewrite (p_mod8_decomp p 3 H).
  replace (8 * (p / 8) + 3) with (4 * (2 * (p / 8)) + 3) by ring.
  rewrite Z.add_comm, (Z.mul_comm 4), Z.mod_add, Z.mod_small by lia.
  reflexivity.
Qed.

Lemma mod8_7_is_mod4_3 :
  forall p, p mod 8 = 7 -> p mod 4 = 3.
Proof.
  intros p H. rewrite (p_mod8_decomp p 7 H).
  replace (8 * (p / 8) + 7) with (4 * (2 * (p / 8) + 1) + 3) by ring.
  rewrite Z.add_comm, (Z.mul_comm 4), Z.mod_add, Z.mod_small by lia.
  reflexivity.
Qed.

(** [p ≡ 3 (mod 4)] ⇒ [v₂(p−1) = 1]: [p−1 = 2 · odd]. *)
Lemma blum_prime_pminus1_form :
  forall p, p mod 4 = 3 -> p - 1 = 2 * ((p - 1) / 2) /\ Z.Odd ((p - 1) / 2).
Proof.
  intros p H.
  pose proof (p_mod4_3_decomp p H) as Hd.
  rewrite Hd.
  replace (4 * (p / 4) + 3 - 1) with (2 * (2 * (p / 4) + 1)) by ring.
  rewrite Z.mul_comm, Z.div_mul by lia.
  split.
  - ring.
  - exists (p / 4). ring.
Qed.

Lemma two_times_div4 :
  forall p, p mod 4 = 3 -> 2 * ((p + 1) / 4) = (p + 1) / 2.
Proof.
  intros p H.
  pose proof (p_mod4_3_decomp p H) as Hd.
  rewrite Hd.
  replace (4 * (p / 4) + 3 + 1) with (4 * (p / 4 + 1)) by ring.
  set (k := p / 4 + 1).
  rewrite (Z.mul_comm 4 k), Z.div_mul by lia.
  replace (k * 4) with (k * 2 * 2) by ring.
  rewrite Z.div_mul by lia. ring.
Qed.

Lemma half_plus_one :
  forall p, p mod 4 = 3 -> (p - 1) / 2 + 1 = (p + 1) / 2.
Proof.
  intros p H.
  pose proof (p_mod4_3_decomp p H) as Hd.
  rewrite Hd.
  replace (4 * (p / 4) + 3 - 1) with (2 * (2 * (p / 4) + 1)) by ring.
  replace (4 * (p / 4) + 3 + 1) with (2 * (2 * (p / 4 + 1))) by ring.
  rewrite (Z.mul_comm 2 (2 * (p / 4) + 1)), Z.div_mul by lia.
  rewrite (Z.mul_comm 2 (2 * (p / 4 + 1))), Z.div_mul by lia.
  ring.
Qed.

(** Euler, QR direction: a square coprime to [p] satisfies
    [a^{(p−1)/2} ≡ 1 (mod p)]. *)
Theorem euler_qr_is_one :
  forall a p x,
    Z.prime p -> p <> 2 ->
    Z.coprime a p ->
    (x * x) mod p = a mod p ->
    euler_crit a p = 1.
Proof.
  intros a p x Hp Hne Hcop Hsq.
  unfold euler_crit.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (odd_prime_minus1_even p Hp Hne) as Hev.
  destruct Hev as [k Hk].
  assert (0 <= (p - 1) / 2) as Hhalf.
  { rewrite Hk, Z.mul_comm, Z.div_mul by lia. nia. }
  assert (Z.coprime x p) as Hxp.
  { rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hp|].
    intro Hpx.
    apply mods_eq_iff_divides in Hsq; [| lia].
    assert (p | x * x) by (eapply Z.divide_mul_l; exact Hpx).
    assert (p | a) as Hpa.
    { destruct Hsq as [t Ht]. destruct H0 as [s Hs].
      exists (s - t). lia. }
    unfold Z.coprime in Hcop.
    assert (p | Z.gcd a p).
    { apply Z.gcd_greatest; [exact Hpa | apply Z.divide_refl]. }
    rewrite Hcop in H1. apply Z.divide_1_r in H1. lia. }
  rewrite <- (powm_mod_base a ((p - 1) / 2) p) by lia.
  rewrite <- Hsq.
  rewrite powm_mod_base by lia.
  unfold powm.
  rewrite <- Z.pow_2_r.
  rewrite <- (Z.pow_mul_r x 2 ((p - 1) / 2)) by lia.
  replace (2 * ((p - 1) / 2)) with (p - 1).
  2: { rewrite Hk, Z.mul_comm, Z.div_mul by lia. lia. }
  fold (powm x (p - 1) p).
  apply fermat_coprime; assumption.
Qed.

(** The Tonelli step that needs only [p ≡ 3 (mod 4)] and Euler = 1. *)
Definition sqrt_mod4_3 (a p : Z) : Z := powm a ((p + 1) / 4) p.

Theorem sqrt_mod4_3_correct :
  forall a p,
    Z.prime p ->
    p mod 4 = 3 ->
    0 <= a ->
    euler_crit a p = 1 ->
    powm (sqrt_mod4_3 a p) 2 p = a mod p.
Proof.
  intros a p Hp Hm Ha Heu.
  pose proof (Z.prime_ge_2 p Hp).
  assert (p <> 2) as Hne by (intro Heq; subst p; discriminate).
  unfold sqrt_mod4_3, euler_crit in *.
  pose proof (p_mod4_3_decomp p Hm) as Hd.
  assert (0 <= (p + 1) / 4) as Hq.
  { rewrite Hd.
    replace (4 * (p / 4) + 3 + 1) with (4 * (p / 4 + 1)) by ring.
    rewrite Z.mul_comm, Z.div_mul by lia. nia. }
  rewrite <- powm_square by lia.
  rewrite (two_times_div4 p Hm).
  rewrite <- (half_plus_one p Hm).
  assert (0 <= (p - 1) / 2) by (pose proof (blum_prime_pminus1_form p Hm); nia).
  rewrite powm_add_r by lia.
  rewrite Heu, Z.mul_1_l, powm_1_r, Z.mod_mod by lia.
  reflexivity.
Qed.

(** [(-1)^{(p−1)/2}] is [+1] iff [p ≡ 1 (mod 4)], by parity of the
    exponent.  This is Euler's criterion for [−1], proved outright. *)
Lemma pow_neg1_even :
  forall k, 0 <= k -> Z.Even k -> (-1) ^ k = 1.
Proof.
  intros k Hk [m Hm]. subst k.
  assert (0 <= m) by lia.
  rewrite Z.pow_mul_r by lia.
  change ((-1) ^ 2) with 1.
  apply Z.pow_1_l. exact H.
Qed.

Lemma pow_neg1_odd :
  forall k, 0 <= k -> Z.Odd k -> (-1) ^ k = -1.
Proof.
  intros k Hk [m Hm]. subst k.
  assert (0 <= m) by lia.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_mul_r by lia.
  change ((-1) ^ 2) with 1.
  rewrite Z.pow_1_l, Z.pow_1_r by lia. ring.
Qed.

Theorem neg1_euler_mod4_3 :
  forall p,
    Z.prime p ->
    p mod 4 = 3 ->
    euler_crit (-1) p = p - 1.
Proof.
  intros p Hp Hm.
  pose proof (Z.prime_ge_2 p Hp).
  unfold euler_crit, powm.
  pose proof (blum_prime_pminus1_form p Hm) as [Heven Hodd].
  assert (0 <= (p - 1) / 2) by nia.
  rewrite (pow_neg1_odd ((p - 1) / 2) H0 Hodd).
  change (-1) with (- (1)).
  rewrite (Z.mod_opp_l_nz 1 p) by (rewrite ?Z.mod_1_l; lia).
  rewrite Z.mod_1_l by lia. reflexivity.
Qed.
