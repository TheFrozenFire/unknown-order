From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import TwoPrimary.

Open Scope Z_scope.

(** * Orders of units, as objects

    [is_order] lives in [UnknownOrder].  This file proves it exists
    from any positive annihilator (Fermat, Carmichael), that it is
    the unique least positive exponent, that [ord(a) | m] iff
    [a^m ≡ 1], that [ord(a^k) = ord(a)/gcd(ord(a),k)], and that
    the 2-height at an odd multiple of [odd_part(ord)] *is*
    [v₂(ord)].

    Completeness of sampling orders to recover [λ] is
    [orders_generate_lambda_named], discharged only by CAS on
    small [N] ([cas/25_order.gp]). *)

(** ** Uniqueness and the divide criterion *)

Lemma is_order_unique :
  forall n a k k',
    is_order n a k ->
    is_order n a k' ->
    k = k'.
Proof.
  intros n a k k' [Hk [Hank Hmin]] [Hk' [Hank' Hmin']].
  destruct (Z.lt_trichotomy k k') as [Hlt | [Heq | Hgt]].
  - exfalso. apply (Hmin' k); [lia | exact Hank].
  - exact Heq.
  - exfalso. apply (Hmin k'); [lia | exact Hank'].
Qed.

Lemma powm_one_of_divide :
  forall a k m n,
    1 < n ->
    0 < k ->
    0 <= m ->
    powm a k n = 1 ->
    (k | m) ->
    powm a m n = 1.
Proof.
  intros a k m n Hn Hk Hm Hann [q Hq].
  rewrite Hq, Z.mul_comm.
  assert (0 <= q) by nia.
  pose proof (powm_one_mul a k q n ltac:(lia) ltac:(lia) ltac:(lia) Hann).
  rewrite Z.mod_1_l in H0 by lia. exact H0.
Qed.

Theorem order_iff_divides :
  forall n a k m,
    1 < n ->
    0 <= m ->
    is_order n a k ->
    (k | m) <-> powm a m n = 1.
Proof.
  intros n a k m Hn Hm Hord.
  destruct Hord as [Hk [Hank Hmin]].
  split.
  - intros Hdiv.
    apply (powm_one_of_divide a k m n); [lia | lia | lia | exact Hank | exact Hdiv].
  - intros Hann.
    apply (order_divides_annihilator n a k m); [lia | lia | | exact Hann].
    unfold is_order. repeat split; assumption.
Qed.

(** ** Existence from a positive annihilator *)

Definition annihil_pred (a n : Z) (j : nat) : bool :=
  Z.eqb (powm a (Z.of_nat (S j)) n) 1.

Lemma order_exists_from_annihilator :
  forall a n M,
    1 < n ->
    0 < M ->
    powm a M n = 1 ->
    exists k, is_order n a k /\ (k | M).
Proof.
  intros a n M Hn HM Hann.
  set (s := Nat.pred (Z.to_nat M)).
  set (P := annihil_pred a n).
  set (j := find_least P s).
  set (k := Z.of_nat (S j)).
  assert (Z.to_nat M = S s) as HMs.
  { unfold s. pose proof (Z2Nat.inj_lt 0 M ltac:(lia) ltac:(lia)).
    destruct (Z.to_nat M) as [| m] eqn:Hmnat; [lia|].
    simpl. reflexivity. }
  assert (P s = true) as Hs.
  { unfold P, annihil_pred.
    replace (Z.of_nat (S s)) with M.
    - apply Z.eqb_eq. exact Hann.
    - rewrite <- HMs, Z2Nat.id by lia. reflexivity. }
  pose proof (find_least_hits P s Hs) as Hhit.
  pose proof (find_least_le P s) as Hle.
  pose proof (find_least_min P s) as Hminb.
  assert (is_order n a k) as Hord.
  { unfold is_order, k. split; [lia|]. split.
    - unfold j. unfold P, annihil_pred in Hhit. apply Z.eqb_eq in Hhit.
      exact Hhit.
    - intros k' [Hk'pos Hk'lt] Hpow.
      assert (0 <= k') by lia.
      set (j' := Nat.pred (Z.to_nat k')).
      assert (Z.to_nat k' = S j') as Hk's.
      { unfold j'. destruct (Z.to_nat k') as [| t] eqn:Ht.
        - pose proof (Z2Nat.inj_lt 0 k' ltac:(lia) ltac:(lia)). lia.
        - simpl. reflexivity. }
      assert (j' < j)%nat as Hjl.
      { apply Nat.succ_lt_mono. rewrite <- Hk's.
        apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
        unfold k in Hk'lt. lia. }
      unfold j in Hjl.
      pose proof (Hminb j' Hjl) as Hfalse.
      unfold P, annihil_pred in Hfalse.
      apply Z.eqb_neq in Hfalse.
      replace (Z.of_nat (S j')) with k' in Hfalse.
      + exact (Hfalse Hpow).
      + rewrite <- Hk's, Z2Nat.id by lia. reflexivity. }
  exists k. split; [exact Hord|].
  apply (order_divides_annihilator n a k M); [lia | lia | exact Hord | exact Hann].
Qed.

Theorem order_exists_prime :
  forall p a,
    Z.prime p ->
    Z.coprime a p ->
    exists k, is_order p a k.
Proof.
  intros p a Hp Hcop.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (fermat_coprime p a Hp Hcop) as Hf.
  destruct (order_exists_from_annihilator a p (p - 1)
              ltac:(lia) ltac:(lia) Hf) as [k [Hord _]].
  exists k. exact Hord.
Qed.

Theorem order_exists_semiprime :
  forall p q a,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime a (p * q) ->
    exists k, is_order (p * q) a k.
Proof.
  intros p q a Hp Hq Hneq Hcop.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  pose proof (carmichael_semiprime p q a Hp Hq Hneq Hcop) as Hc.
  pose proof (lambda_semiprime_pos p q Hp Hq).
  destruct (order_exists_from_annihilator a (p * q) (lambda_semiprime p q)
              ltac:(nia) ltac:(lia) Hc) as [k [Hord _]].
  exists k. exact Hord.
Qed.

(** ** [ord(a^k) = ord(a) / gcd(ord(a), k)] *)

Theorem order_of_power :
  forall n a d k,
    1 < n ->
    0 < k ->
    is_order n a d ->
    is_order n (powm a k n) (d / Z.gcd d k).
Proof.
  intros n a d k Hn Hk Hord.
  pose proof Hord as [Hd [Hand Hmin]].
  set (g := Z.gcd d k).
  assert (0 < g) as Hgpos.
  { pose proof (Z.gcd_nonneg d k).
    destruct (Z.eq_dec g 0) as [Hz | Hnz]; [| lia].
    unfold g in Hz. apply Z.gcd_eq_0_l in Hz. lia. }
  assert (g | d) as Hgd by apply Z.gcd_divide_l.
  assert (g | k) as Hgk by apply Z.gcd_divide_r.
  set (d' := d / g).
  set (k' := k / g).
  assert (0 < d') as Hd'pos.
  { unfold d'. apply Z.div_str_pos. split; [lia|].
    apply Z.divide_pos_le; [lia | exact Hgd]. }
  assert (d = g * d') as Hdfact.
  { unfold d'. destruct Hgd as [q Hq]. rewrite Hq.
    replace ((q * g) / g) with q by (rewrite Z.div_mul; lia). ring. }
  assert (k = g * k') as Hkfact.
  { unfold k'. destruct Hgk as [q Hq]. rewrite Hq.
    replace ((q * g) / g) with q by (rewrite Z.div_mul; lia). ring. }
  assert (Z.gcd d' k' = 1) as Hg1.
  { unfold d', k', g.
    rewrite Z.gcd_div_gcd by lia. reflexivity. }
  unfold is_order. split; [exact Hd'pos|]. split.
  - replace (powm (powm a k n) d' n) with (powm a (k * d') n).
    + rewrite Hkfact.
      replace (g * k' * d') with (d * k') by (rewrite Hdfact; ring).
      apply (powm_one_of_divide a d (d * k') n); [lia | lia | nia | exact Hand |].
      exists k'. ring.
    + unfold powm.
      rewrite (Z.mod_pow_l (a ^ k) d' n) by lia.
      rewrite Z.pow_mul_r by nia.
      reflexivity.
  - intros t [Htpos Htlt] Hpowt.
    assert (powm a (k * t) n = 1) as Hakt.
    { unfold powm in Hpowt |- *.
      rewrite (Z.mod_pow_l (a ^ k) t n) in Hpowt by lia.
      rewrite <- (Z.pow_mul_r a k t) in Hpowt by nia.
      exact Hpowt. }
    assert (d | k * t) as Hdiv.
    { apply (order_divides_annihilator n a d (k * t));
        [lia | nia | exact Hord | exact Hakt]. }
    rewrite Hdfact, Hkfact in Hdiv.
    destruct Hdiv as [q Hq].
    assert (d' | k' * t) as Hd't.
    { exists q. nia. }
    apply (Z.gauss d' k' t) in Hd't; [| exact Hg1].
    destruct Hd't as [r Hr].
    assert (0 < r).
    { destruct (Z.le_gt_cases r 0) as [Hle | Hgt]; [| exact Hgt]. nia. }
    unfold d' in Htlt. nia.
Qed.

(** ** [lcm] of orders divides [λ] *)

Theorem lcm_orders_divides_lambda :
  forall p q a b ka kb,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime a (p * q) ->
    Z.coprime b (p * q) ->
    is_order (p * q) a ka ->
    is_order (p * q) b kb ->
    (Z.lcm ka kb | lambda_semiprime p q).
Proof.
  intros p q a b ka kb Hp Hq Hneq Hca Hcb Hoa Hob.
  apply Z.lcm_least.
  - apply (order_divides_lambda p q a ka); assumption.
  - apply (order_divides_lambda p q b kb); assumption.
Qed.

(** Completeness — the lcm of *enough* orders is [λ] — is a density
    statement.  Unused refuse of a general proof; CAS
    [cas/25_order.gp] checks it exhaustively on [11×17], [11×19],
    [41×73]. *)
Definition orders_generate_lambda_named (p q : Z) (ks : Z -> Prop) : Prop :=
  (forall k, ks k -> (k | lambda_semiprime p q)) /\
  (exists K, ks K /\ K = lambda_semiprime p q).

(** Two orders' lcm need not be [λ].  Both [−1] and a mixed [√1]
    have order 2; [lcm(2,2)=2 ≠ 80] on [rsa_test].  The refuse is
    the general sampling-completeness claim, not this negative. *)

Lemma is_order_2_of :
  forall n a,
    1 < n ->
    powm a 2 n = 1 ->
    a mod n <> 1 ->
    is_order n a 2.
Proof.
  intros n a Hn Hsq Hneq.
  split; [| split]; [lia | exact Hsq |].
  intros k' Hk.
  assert (k' = 1) by lia. subst k'.
  unfold powm. rewrite Z.pow_1_r. exact Hneq.
Qed.

Theorem minus1_order_2_rsa_test :
  is_order 187 186 2.
Proof.
  apply is_order_2_of; [lia | vm_compute; reflexivity | vm_compute; discriminate].
Qed.

Theorem mixed67_order_2_rsa_test :
  is_order 187 67 2.
Proof.
  apply is_order_2_of; [lia | vm_compute; reflexivity | vm_compute; discriminate].
Qed.

Theorem lcm_two_order2_not_lambda :
  is_order 187 186 2 /\
  is_order 187 67 2 /\
  Z.lcm 2 2 <> lambda_semiprime 11 17.
Proof.
  split; [apply minus1_order_2_rsa_test|].
  split; [apply mixed67_order_2_rsa_test|].
  rewrite rsa_test_lambda. vm_compute. discriminate.
Qed.

(** ** 2-height is [v₂(ord)] at a common odd multiple of [odd_part(ord)] *)

Lemma powm_eq_1_iff_order_divides :
  forall n a d m,
    1 < n ->
    0 <= m ->
    is_order n a d ->
    powm a m n = 1 <-> (d | m).
Proof.
  intros n a d m Hn Hm Hord.
  rewrite <- (order_iff_divides n a d m Hn Hm Hord). reflexivity.
Qed.

Lemma pow2_divides_pow2 :
  forall i j : nat,
    (2 ^ Z.of_nat i | 2 ^ Z.of_nat j) <-> (i <= j)%nat.
Proof.
  intros i j. split.
  - intros [q Hq].
    pose proof (val2_scale_odd i 1 ltac:(lia) ltac:(exists 0%Z; ring)) as Hi.
    pose proof (val2_scale_odd j 1 ltac:(lia) ltac:(exists 0%Z; ring)) as Hj.
    replace (2 ^ Z.of_nat i) with (2 ^ Z.of_nat i * 1) in Hq by ring.
    replace (2 ^ Z.of_nat j) with (2 ^ Z.of_nat j * 1) in Hq by ring.
    assert (0 < 2 ^ Z.of_nat i) by (apply Z.pow_pos_nonneg; lia).
    assert (0 < q).
    { destruct (Z.le_gt_cases q 0) as [Hle | Hgt]; [| exact Hgt].
      pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j) ltac:(lia) ltac:(lia)). nia. }
    assert (val2 (2 ^ Z.of_nat j * 1) = (val2 q + val2 (2 ^ Z.of_nat i * 1))%nat).
    { rewrite Hq, val2_mul; [reflexivity | lia | lia]. }
    rewrite Hj, Hi in H1. lia.
  - intros Hle.
    exists (2 ^ Z.of_nat (j - i)).
    replace (Z.of_nat j) with (Z.of_nat i + Z.of_nat (j - i)) by lia.
    rewrite Z.pow_add_r by lia. ring.
Qed.

Theorem two_height_is_val2_ord :
  forall p a d t k,
    Z.prime p ->
    is_order p a d ->
    0 < t ->
    Z.Odd t ->
    Z.divide (odd_part d) t ->
    two_height a t p k <-> k = val2 d.
Proof.
  intros p a d t k Hp Hord Ht Hot Hdiv.
  pose proof (Z.prime_ge_2 p Hp).
  assert (Hord' : is_order p a d) by exact Hord.
  destruct Hord as [Hd [Hand Hmin]].
  assert (0 < odd_part d) as Htodd by (apply odd_part_pos; lia).
  pose proof (odd_part_odd d Hd) as Htodd_odd.
  pose proof (split2_of_reconstructs d ltac:(lia)) as Hdsplit.
  set (h := val2 d) in *.
  set (todd := odd_part d) in *.
  assert (forall j : nat,
            powm a (t * pow2n j) p = 1 <-> (h <= j)%nat) as Hchar.
  { intros j.
    assert (0 <= t * pow2n j).
    { apply Z.mul_nonneg_nonneg; [lia | pose proof (pow2n_pos j); lia]. }
    rewrite (powm_eq_1_iff_order_divides p a d (t * pow2n j));
      [ | lia | lia | exact Hord' ].
    unfold pow2n. split.
    - intros Htm.
      destruct Hdiv as [u Hu].
      assert (Z.Odd u) as Hou.
      { destruct (Z.odd u) eqn:Houb.
        - apply Z.odd_spec. exact Houb.
        - assert (Z.Even u) as Hev.
          { apply Z.even_spec. rewrite <- Z.negb_odd, Houb. reflexivity. }
          destruct Hev as [v Hv]. destruct Hot as [x Hx].
          rewrite Hu, Hv in Hx. lia. }
      apply pow2_divides_pow2.
      apply (Z.gauss (2 ^ Z.of_nat h) u (2 ^ Z.of_nat j)).
      + destruct Htm as [q Hq].
        rewrite Hdsplit, Hu in Hq.
        exists q. nia.
      + rewrite Z.gcd_comm.
        apply odd_coprime_pow2; [exact Hou | lia].
    - intros Hle.
      destruct Hdiv as [u Hu].
      exists (u * 2 ^ Z.of_nat (j - h)).
      rewrite Hdsplit, Hu.
      replace (Z.of_nat j) with (Z.of_nat h + Z.of_nat (j - h)) by lia.
      rewrite Z.pow_add_r by lia. ring. }
  split.
  - intros [Hpow Hleast].
    apply Hchar in Hpow.
    destruct (Nat.eq_dec k h) as [Heq | Hne]; [exact Heq|].
    exfalso. apply (Hleast h); [lia|]. apply Hchar. lia.
  - intros Hk. subst k.
    split.
    + apply Hchar. lia.
    + intros j Hj Hpow. apply Hchar in Hpow. lia.
Qed.

Theorem order_2_mod_11 : is_order 11 2 10.
Proof.
  unfold is_order, powm. split; [lia|]. split.
  - vm_compute. reflexivity.
  - intros k' [Hk' Hk'lt] Hk'1.
    assert (k' = 1 \/ k' = 2 \/ k' = 3 \/ k' = 4 \/ k' = 5 \/
            k' = 6 \/ k' = 7 \/ k' = 8 \/ k' = 9) by lia.
    repeat (destruct H as [H | H]; [subst k'; vm_compute in Hk'1; discriminate|]).
    subst k'. vm_compute in Hk'1. discriminate.
Qed.

Theorem order_2_mod_17 : is_order 17 2 8.
Proof.
  unfold is_order, powm. split; [lia|]. split.
  - vm_compute. reflexivity.
  - intros k' [Hk' Hk'lt] Hk'1.
    assert (k' = 1 \/ k' = 2 \/ k' = 3 \/ k' = 4 \/ k' = 5 \/
            k' = 6 \/ k' = 7) by lia.
    repeat (destruct H as [H | H]; [subst k'; vm_compute in Hk'1; discriminate|]).
    subst k'. vm_compute in Hk'1. discriminate.
Qed.

(** Same-[t] without [cyclic_units]: any two odd multiples of
    [odd_part(ord(a))] give the same 2-height, namely [v₂(ord)]. *)
Theorem two_height_independent_of_odd_multiple :
  forall p a d t t' k,
    Z.prime p ->
    is_order p a d ->
    0 < t -> 0 < t' ->
    Z.Odd t -> Z.Odd t' ->
    Z.divide (odd_part d) t ->
    Z.divide (odd_part d) t' ->
    two_height a t p k <-> two_height a t' p k.
Proof.
  intros p a d t t' k Hp Hord Ht Ht' Hot Hot' Hdt Hdt'.
  rewrite (two_height_is_val2_ord p a d t k) by assumption.
  rewrite (two_height_is_val2_ord p a d t' k) by assumption.
  reflexivity.
Qed.

Theorem height_is_val2_ord_textbook :
  two_height 2 (odd_part 10) 11 (val2 10) /\
  two_height 2 (odd_part 8) 17 (val2 8).
Proof.
  split.
  - rewrite (two_height_is_val2_ord 11 2 10 (odd_part 10) (val2 10)).
    + reflexivity.
    + exact prime_11.
    + exact order_2_mod_11.
    + assert (odd_part 10 = 5) as H10 by (vm_compute; reflexivity).
      rewrite H10. lia.
    + assert (odd_part 10 = 5) as H10 by (vm_compute; reflexivity).
      rewrite H10. exists 2%Z. reflexivity.
    + apply Z.divide_refl.
  - rewrite (two_height_is_val2_ord 17 2 8 (odd_part 8) (val2 8)).
    + reflexivity.
    + exact prime_17.
    + exact order_2_mod_17.
    + assert (odd_part 8 = 1) as H8 by (vm_compute; reflexivity).
      rewrite H8. lia.
    + assert (odd_part 8 = 1) as H8 by (vm_compute; reflexivity).
      rewrite H8. exists 0%Z. reflexivity.
    + apply Z.divide_refl.
Qed.
