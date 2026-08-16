From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import Zmod.

Require Import RocqProofs.NumberTheory.
Require Import QuadResidue.
Require Import Pratt.
Require Import Hardness.
Require Import RabinWilliams.

Open Scope Z_scope.

(** * The 2-primary part of [(Z/NZ)*]

    RSA, Miller-from-[λ], Miller–Rabin, Pratt, Blum integers and
    Rabin–Williams are the same algebra here: the 2-Sylow of the
    unit group, read off [v₂(p−1)] and [v₂(q−1)].

    Cyclicity of [(Z/pZ)*] is not assumed.  What is proved is the
    valuation arithmetic, the four square roots of 1, a 2-height
    for a unit, and that mismatched heights split [N].  Blum /
    Williams is the case [(v₂, v₂) = (1, 1)].

    Cross-confirmed by [cas/20_two_primary.gp]. *)

Definition pow2n (k : nat) : Z := 2 ^ Z.of_nat k.

Lemma pow2n_pos : forall k, 0 < pow2n k.
Proof. intros. unfold pow2n. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow2n_succ : forall k, pow2n (S k) = 2 * pow2n k.
Proof.
  intros. unfold pow2n.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
Qed.

(** ** [v₂] on odds and on [2 · odd] *)

Lemma gcd2_of_odd :
  forall t, Z.Odd t -> Z.gcd 2 t = 1.
Proof.
  intros t [k Hk]. rewrite Hk.
  replace (2 * k + 1) with (1 + k * 2) by ring.
  rewrite (Z.gcd_comm 2 (1 + k * 2)).
  rewrite Z.gcd_comm.
  change (Z.gcd 2 (1 + k * 2) = 1).
  rewrite (Z.gcd_add_mult_diag_r 2 1 k).
  apply Z.gcd_1_r.
Qed.

Lemma val2_of_odd :
  forall n, 0 < n -> Z.Odd n -> val2 n = 0%nat.
Proof.
  intros n Hn Hodd.
  unfold val2, split2_of.
  destruct (Z.to_nat (Z.abs n)) as [| fuel].
  - simpl. reflexivity.
  - simpl.
    assert (Z.even n = false) as Hev.
    { apply Z.odd_spec in Hodd.
      rewrite <- Z.negb_odd, Hodd. reflexivity. }
    rewrite Hev. simpl. reflexivity.
Qed.

Lemma val2_two_times_odd :
  forall t, 0 < t -> Z.Odd t -> val2 (2 * t) = 1%nat.
Proof.
  intros t Ht Hodd.
  pose proof (split2_of_reconstructs (2 * t) ltac:(lia)) as Hr.
  pose proof (odd_part_odd_or_zero (2 * t) ltac:(lia)) as Ho.
  assert (0 < odd_part (2 * t)) as Hpos.
  { pose proof (Z.pow_nonneg 2 (Z.of_nat (val2 (2 * t))) ltac:(lia)). nia. }
  destruct Ho as [Hodd2 | Hz]; [| lia].
  destruct (val2 (2 * t)) as [| s] eqn:Hs.
  - rewrite Z.pow_0_r, Z.mul_1_l in Hr.
    apply Z.odd_spec in Hodd2. destruct Hodd2 as [k Hk].
    rewrite <- Hr in Hk. lia.
  - destruct s as [| s'].
    + reflexivity.
    + assert (4 | 2 * t) as H4.
      { rewrite Hr.
        replace (Z.of_nat (S (S s'))) with (2 + Z.of_nat s') by lia.
        rewrite Z.pow_add_r by lia. change (2 ^ 2) with 4.
        exists (2 ^ Z.of_nat s' * odd_part (2 * t)). ring. }
      destruct H4 as [u Hu].
      destruct Hodd as [w Hw]. lia.
Qed.

Lemma odd_prime_val2_ge1 :
  forall p, Z.prime p -> p <> 2 -> (1 <= val2 (p - 1))%nat.
Proof.
  intros p Hp Hne.
  pose proof (odd_prime_minus1_even p Hp Hne) as He.
  pose proof (Z.prime_ge_2 p Hp).
  destruct He as [k Hk].
  assert (0 < k) by nia.
  destruct (Z.odd k) eqn:Hok.
  - apply Z.odd_spec in Hok.
    replace (val2 (p - 1)) with (val2 (2 * k)) by (f_equal; lia).
    rewrite (val2_two_times_odd k ltac:(lia) Hok). lia.
  - pose proof (split2_of_reconstructs (p - 1) ltac:(lia)) as Hr.
    destruct (val2 (p - 1)) as [| s] eqn:Hs.
    + rewrite Z.pow_0_r, Z.mul_1_l in Hr.
      pose proof (odd_part_odd_or_zero (p - 1) ltac:(lia)) as Ho.
      destruct Ho as [Ho | Hz]; [| lia].
      apply Z.odd_spec in Ho. destruct Ho as [u Hu].
      rewrite <- Hr in Hu. rewrite Hk in Hu. lia.
    + lia.
Qed.

Theorem blum_val2_is_1 :
  forall p, Z.prime p -> p mod 4 = 3 -> val2 (p - 1) = 1%nat.
Proof.
  intros p Hp Hm.
  pose proof (Z.prime_ge_2 p Hp).
  assert (p <> 2) by (intro Heq; subst p; discriminate).
  pose proof (blum_prime_pminus1_form p Hm) as [Heven Hodd].
  assert (0 < (p - 1) / 2).
  { pose proof (p_mod4_3_decomp p Hm). nia. }
  rewrite Heven. apply val2_two_times_odd; [lia | exact Hodd].
Qed.

Lemma mod4_1_val2_ge2 :
  forall p, Z.prime p -> p <> 2 -> p mod 4 = 1 -> (2 <= val2 (p - 1))%nat.
Proof.
  intros p Hp Hne Hm.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.div_mod p 4 ltac:(lia)) as Hd.
  rewrite Hm in Hd.
  assert (Hp1 : p - 1 = 4 * (p / 4)) by lia.
  pose proof (split2_of_reconstructs (p - 1) ltac:(lia)) as Hr.
  destruct (val2 (p - 1)) as [| s] eqn:Hs.
  - rewrite Z.pow_0_r, Z.mul_1_l in Hr.
    pose proof (odd_part_odd_or_zero (p - 1) ltac:(lia)) as Ho.
    destruct Ho as [Ho | Hz].
    + apply Z.odd_spec in Ho. destruct Ho as [u Hu].
      rewrite <- Hr, Hp1 in Hu. lia.
    + rewrite <- Hr, Hp1 in Hz. nia.
  - destruct s as [| s'].
    + rewrite Z.pow_1_r in Hr.
      pose proof (odd_part_odd_or_zero (p - 1) ltac:(lia)) as Ho.
      destruct Ho as [Ho | Hz]; [| nia].
      apply Z.odd_spec in Ho. destruct Ho as [u Hu].
      assert (odd_part (p - 1) = 2 * (p / 4)) by lia.
      lia.
    + lia.
Qed.

Theorem rw_pair_val2_11 :
  forall p q, rw_pair p q ->
    val2 (p - 1) = 1%nat /\ val2 (q - 1) = 1%nat.
Proof.
  intros p q [[Hp Hpm] [[Hq Hqm] _]].
  split.
  - apply blum_val2_is_1; [exact Hp | apply mod8_3_is_mod4_3; exact Hpm].
  - apply blum_val2_is_1; [exact Hq | apply mod8_7_is_mod4_3; exact Hqm].
Qed.

(** ** Four square roots of 1 *)

Definition crt2 (p q a b : Z) : Z := Z.combinecong p q a b.

Lemma crt2_mod :
  forall p q a b,
    Z.prime p -> Z.prime q -> p <> q ->
    let x := crt2 p q a b in
    x mod p = a mod p /\ x mod q = b mod q.
Proof.
  intros p q a b Hp Hq Hneq x.
  unfold x, crt2.
  apply Z.combinecong_sound_coprime.
  apply prime_coprime_distinct; assumption.
Qed.

Definition sqrt1_pp (p q : Z) : Z := 1.
Definition sqrt1_mm (p q : Z) : Z := p * q - 1.
Definition sqrt1_pm (p q : Z) : Z := crt2 p q 1 (q - 1).
Definition sqrt1_mp (p q : Z) : Z := crt2 p q (p - 1) 1.

Lemma square_mod_one_of_pm1 :
  forall x n r,
    1 < n ->
    x mod n = r ->
    (r = 1 \/ r = n - 1) ->
    (x * x) mod n = 1 mod n.
Proof.
  intros x n r Hn Hxr [Hr | Hr].
  - rewrite Hr in Hxr.
    rewrite Z.mul_mod, Hxr, !Z.mod_1_l by lia.
    reflexivity.
  - rewrite Hr in Hxr.
    rewrite Z.mul_mod, Hxr by lia.
    replace ((n - 1) * (n - 1)) with (1 + (n - 2) * n) by ring.
    rewrite Z.mod_add, !Z.mod_1_l by lia. reflexivity.
Qed.

Lemma powm_square_one_of_pm1 :
  forall r n, 1 < n -> (r = 1 \/ r = n - 1) -> powm r 2 n = 1.
Proof.
  intros r n Hn [H | H]; subst; unfold powm; rewrite Z.pow_2_r.
  - rewrite Z.mul_1_l, Z.mod_1_l by lia. reflexivity.
  - replace ((n - 1) * (n - 1)) with (1 + (n - 2) * n) by ring.
    rewrite Z.mod_add, Z.mod_1_l by lia. reflexivity.
Qed.

Theorem four_sqrt1 :
  forall p q,
    Z.prime p -> Z.prime q -> p <> q ->
    let N := p * q in
    powm (sqrt1_pp p q) 2 N = 1 /\
    powm (sqrt1_mm p q) 2 N = 1 /\
    powm (sqrt1_pm p q) 2 N = 1 /\
    powm (sqrt1_mp p q) 2 N = 1.
Proof.
  intros p q Hp Hq Hneq N.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  assert (HN : 1 < N) by (unfold N; nia).
  unfold N.
  split; [| split; [| split]].
  - apply powm_square_one_of_pm1; [unfold N in HN; nia | left; reflexivity].
  - apply powm_square_one_of_pm1; [nia | right; reflexivity].
  - pose proof (crt2_mod p q 1 (q - 1) Hp Hq Hneq) as [Hp1 Hq1].
    unfold sqrt1_pm, powm. rewrite Z.pow_2_r.
    transitivity (1 mod (p * q)); [| apply Z.mod_small; nia].
    apply mods_eq_iff_divides; [nia|].
    apply divide_by_coprime_product.
    + apply prime_coprime_distinct; assumption.
    + apply mods_eq_iff_divides; [lia|].
      rewrite Z.mod_1_l in Hp1 by lia.
      apply (square_mod_one_of_pm1 _ p 1); [lia | exact Hp1 | left; reflexivity].
    + apply mods_eq_iff_divides; [lia|].
      assert (Hqbd : 0 <= q - 1 < q) by lia.
      rewrite (Z.mod_small (q - 1) q Hqbd) in Hq1.
      apply (square_mod_one_of_pm1 _ q (q - 1)); [lia | exact Hq1 | right; reflexivity].
  - pose proof (crt2_mod p q (p - 1) 1 Hp Hq Hneq) as [Hp1 Hq1].
    unfold sqrt1_mp, powm. rewrite Z.pow_2_r.
    transitivity (1 mod (p * q)); [| apply Z.mod_small; nia].
    apply mods_eq_iff_divides; [nia|].
    apply divide_by_coprime_product.
    + apply prime_coprime_distinct; assumption.
    + apply mods_eq_iff_divides; [lia|].
      assert (Hpbd : 0 <= p - 1 < p) by lia.
      rewrite (Z.mod_small (p - 1) p Hpbd) in Hp1.
      apply (square_mod_one_of_pm1 _ p (p - 1)); [lia | exact Hp1 | right; reflexivity].
    + apply mods_eq_iff_divides; [lia|].
      rewrite Z.mod_1_l in Hq1 by lia.
      apply (square_mod_one_of_pm1 _ q 1); [lia | exact Hq1 | left; reflexivity].
Qed.

Lemma mod_mod_of_factor :
  forall x a b, 0 < a -> 0 < b -> (x mod (a * b)) mod b = x mod b.
Proof.
  intros x a b Ha Hb.
  apply Z.mod_mod_divide. exists a. ring.
Qed.

Lemma mixed_pm_not_one :
  forall p q,
    Z.prime p -> Z.prime q -> p <> q -> q <> 2 ->
    sqrt1_pm p q mod (p * q) <> 1.
Proof.
  intros p q Hp Hq Hneq Hnq Heq.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  pose proof (crt2_mod p q 1 (q - 1) Hp Hq Hneq) as [_ Hq1].
  unfold sqrt1_pm in Heq, Hq1.
  assert ((crt2 p q 1 (q - 1) mod (p * q)) mod q = 1) as Hred.
  { rewrite Heq. apply Z.mod_1_l; lia. }
  rewrite (mod_mod_of_factor _ p q) in Hred by lia.
  rewrite Hq1, Z.mod_small in Hred by lia.
  lia.
Qed.

Lemma mixed_pm_not_minus1 :
  forall p q,
    Z.prime p -> Z.prime q -> p <> q -> p <> 2 ->
    sqrt1_pm p q mod (p * q) <> p * q - 1.
Proof.
  intros p q Hp Hq Hneq Hnp Heq.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  pose proof (crt2_mod p q 1 (q - 1) Hp Hq Hneq) as [Hp1 _].
  unfold sqrt1_pm in Heq, Hp1.
  assert ((crt2 p q 1 (q - 1) mod (p * q)) mod p = (p * q - 1) mod p) as Hred.
  { rewrite Heq. reflexivity. }
  rewrite (Z.mul_comm p q) in Hred.
  rewrite (mod_mod_of_factor _ q p) in Hred by lia.
  rewrite Hp1, Z.mod_1_l in Hred by lia.
  assert ((q * p - 1) mod p = p - 1) as Hmm.
  { replace (q * p - 1) with (- (1) + q * p) by ring.
    rewrite Z.mod_add by lia.
    rewrite Z.mod_opp_l_nz, Z.mod_1_l by (rewrite ?Z.mod_1_l; lia).
    reflexivity. }
  rewrite Hmm in Hred. lia.
Qed.

Theorem mixed_sqrt1_splits :
  forall p q,
    Z.prime p -> Z.prime q -> p <> q -> p <> 2 -> q <> 2 ->
    let N := p * q in
    let g := Z.gcd (sqrt1_pm p q - 1) N in
    1 < g /\ g < N /\ (g | N).
Proof.
  intros p q Hp Hq Hneq Hnp Hnq N g.
  pose proof (four_sqrt1 p q Hp Hq Hneq) as [_ [_ [Hsq _]]].
  unfold N, g.
  apply nontrivial_sqrt1_splits; try assumption.
  - apply mixed_pm_not_one; assumption.
  - apply mixed_pm_not_minus1; assumption.
Qed.

(** ** 2-height of a unit, and mismatch splits [N]

    Write an odd [t] (the odd part of [p−1], or of [λ]).  The
    *2-height* of [a] at [p] is the least [k] with
    [a^{t · 2^k} ≡ 1 (mod p)].  For a unit this [k] is
    [v₂(ord_p(a))], and it is at most [v₂(p−1)].

    If the heights at [p] and [q] differ, some prefix of the Miller
    square-chain is [1] on one CRT component and not the other —
    [one_sided_low_order_factors]. *)

Definition two_height (a t n : Z) (k : nat) : Prop :=
  powm a (t * pow2n k) n = 1 /\
  (forall j : nat, (j < k)%nat -> powm a (t * pow2n j) n <> 1).

Lemma two_height_unique :
  forall a t n k k',
    two_height a t n k ->
    two_height a t n k' ->
    k = k'.
Proof.
  intros a t n k k' [Hk Hmin] [Hk' Hmin'].
  destruct (Nat.lt_trichotomy k k') as [Hlt | [Heq | Hgt]].
  - exfalso. apply (Hmin' k Hlt). exact Hk.
  - exact Heq.
  - exfalso. apply (Hmin k' Hgt). exact Hk'.
Qed.

Theorem height_mismatch_splits :
  forall p q a t kp kq,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime a (p * q) ->
    0 <= t ->
    two_height a t p kp ->
    two_height a t q kq ->
    (kp < kq)%nat ->
    Z.gcd (a ^ (t * pow2n kp) - 1) (p * q) = p.
Proof.
  intros p q a t kp kq Hp Hq Hneq Hcop Ht Hpht Hqht Hlt.
  destruct Hpht as [Hpone _].
  destruct Hqht as [_ Hqmin].
  apply one_sided_low_order_factors; try assumption.
  unfold one_sided_low_order.
  split; [| split; [| split]].
  - exact Hcop.
  - apply Z.mul_nonneg_nonneg; [exact Ht | pose proof (pow2n_pos kp); lia].
  - exact Hpone.
  - apply Hqmin. exact Hlt.
Qed.

(** Generation-side 2-adic rulers.  Blum / Williams *choose*
    [(1,1)].  Matching deep 2-valuations is the opposite choice:
    more Miller liars, no extra public annihilator. *)

Definition kg_blum_2adic (p q : Z) : Prop :=
  val2 (p - 1) = 1%nat /\ val2 (q - 1) = 1%nat.

Definition kg_2adic_unbalanced (p q : Z) : Prop :=
  val2 (p - 1) <> val2 (q - 1).

Definition kg_2adic_matched_deep (d : nat) (p q : Z) : Prop :=
  val2 (p - 1) = val2 (q - 1) /\ (d <= val2 (p - 1))%nat.

Theorem rw_is_blum_2adic :
  forall p q, rw_pair p q -> kg_blum_2adic p q.
Proof. intros. apply rw_pair_val2_11. exact H. Qed.

Theorem unbalanced_not_matched :
  forall p q d,
    kg_2adic_unbalanced p q ->
    ~ kg_2adic_matched_deep d p q.
Proof.
  intros p q d Hne [Heq _]. congruence.
Qed.
