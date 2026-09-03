From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.ZPoly.
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
    [orders_generate_lambda_named], unused refuse of a density
    statement ([cas/25_order.gp]).  The lcm of two unit orders is
    again a unit order ([order_lcm_attained]).  [𝔽_p*] has a
    primitive root ([primitive_root_exists]); CRT of local
    generators is a unit of order [λ] ([exists_unit_order_lambda],
    [cas/153]).  A primitive root generates: every unit is [g^k]
    ([primitive_root_generates], [cas/154]). *)

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
  is_order pin_N 186 2.
Proof.
  apply is_order_2_of; [lia | vm_compute; reflexivity | vm_compute; discriminate].
Qed.

Theorem mixed67_order_2_rsa_test :
  is_order pin_N 67 2.
Proof.
  apply is_order_2_of; [lia | vm_compute; reflexivity | vm_compute; discriminate].
Qed.

Theorem lcm_two_order2_not_lambda :
  is_order pin_N 186 2 /\
  is_order pin_N 67 2 /\
  Z.lcm 2 2 <> lambda_semiprime pin_p pin_q.
Proof.
  split; [apply minus1_order_2_rsa_test|].
  split; [apply mixed67_order_2_rsa_test|].
  replace (lambda_semiprime pin_p pin_q) with pin_lam by (apply rsa_test_lambda).
  discriminate.
Qed.

Theorem is_order_pin_3_80 :
  is_order pin_N 3 80.
Proof.
  unfold is_order. split; [lia|]. split.
  - vm_compute. reflexivity.
  - intros k' [Hk' Hk'lt] Hk'1.
    assert (
      k' = 1 \/ k' = 2 \/ k' = 3 \/ k' = 4 \/ k' = 5 \/
      k' = 6 \/ k' = 7 \/ k' = 8 \/ k' = 9 \/ k' = 10 \/
      k' = 11 \/ k' = 12 \/ k' = 13 \/ k' = 14 \/ k' = 15 \/
      k' = 16 \/ k' = 17 \/ k' = 18 \/ k' = 19 \/ k' = 20 \/
      k' = 21 \/ k' = 22 \/ k' = 23 \/ k' = 24 \/ k' = 25 \/
      k' = 26 \/ k' = 27 \/ k' = 28 \/ k' = 29 \/ k' = 30 \/
      k' = 31 \/ k' = 32 \/ k' = 33 \/ k' = 34 \/ k' = 35 \/
      k' = 36 \/ k' = 37 \/ k' = 38 \/ k' = 39 \/ k' = 40 \/
      k' = 41 \/ k' = 42 \/ k' = 43 \/ k' = 44 \/ k' = 45 \/
      k' = 46 \/ k' = 47 \/ k' = 48 \/ k' = 49 \/ k' = 50 \/
      k' = 51 \/ k' = 52 \/ k' = 53 \/ k' = 54 \/ k' = 55 \/
      k' = 56 \/ k' = 57 \/ k' = 58 \/ k' = 59 \/ k' = 60 \/
      k' = 61 \/ k' = 62 \/ k' = 63 \/ k' = 64 \/ k' = 65 \/
      k' = 66 \/ k' = 67 \/ k' = 68 \/ k' = 69 \/ k' = 70 \/
      k' = 71 \/ k' = 72 \/ k' = 73 \/ k' = 74 \/ k' = 75 \/
      k' = 76 \/ k' = 77 \/ k' = 78 \/ k' = 79) by lia.
    repeat (destruct H as [H | H]; [subst k'; vm_compute in Hk'1; discriminate|]).
    subst k'. vm_compute in Hk'1. discriminate.
Qed.

Theorem pin_unit_3_coprime :
  Z.coprime 3 pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_attains_lambda :
  Z.coprime 3 pin_N /\ is_order pin_N 3 80 /\
  pin_lam = lambda_semiprime pin_p pin_q.
Proof.
  split; [apply pin_unit_3_coprime|].
  split; [apply is_order_pin_3_80|].
  vm_compute. reflexivity.
Qed.

(** Completeness on this pin: [λ] is some unit's order, so the lcm
    of unit orders is [λ].  The unused [orders_generate_lambda_named]
    remains the general density statement. *)

Theorem orders_generate_lambda_pin :
  exists a, Z.coprime a pin_N /\ is_order pin_N a 80 /\
    pin_lam = lambda_semiprime pin_p pin_q.
Proof. exists 3. apply pin_attains_lambda. Qed.

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

(** ** A unit of order [λ] for general [N = pq]

    [orders_generate_lambda_named] stays unused: it is sampling
    completeness, not existence.  [order_lcm_attained]: the lcm
    of two unit orders is the order of a unit.  A maximal-order
    unit of [𝔽_p*] is a primitive root: [X^d−1] cannot vanish on
    all of [𝔽_p*] for [d < p−1].  CRT of two local generators
    has order [λ].  Cross-confirmed by [cas/153]. *)

Fixpoint zseq (start : Z) (n : nat) : list Z :=
  match n with
  | O => nil
  | S n' => start :: zseq (start + 1) n'
  end.

Lemma zseq_length : forall start n, length (zseq start n) = n.
Proof.
  intros start n. revert start. induction n as [|n IH]; intros start; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma zseq_In_bounds :
  forall start n x,
    In x (zseq start n) ->
    start <= x < start + Z.of_nat n.
Proof.
  intros start n. revert start.
  induction n as [|n IH]; intros start x Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst x. lia.
    + pose proof (IH (start + 1) x Hin). lia.
Qed.

Lemma zseq_Forall_distinct_head :
  forall p start n,
    1 < p ->
    0 <= start ->
    start + Z.of_nat (S n) <= p ->
    Forall (fun b => ~ (p | b - start)) (zseq (start + 1) n).
Proof.
  intros p start n Hp Hs Hle.
  apply Forall_forall. intros b Hin [k Hk].
  pose proof (zseq_In_bounds (start + 1) n b Hin) as Hb.
  assert (Hlo : 1 <= b - start) by lia.
  assert (Hhi : b < p).
  { replace (Z.of_nat (S n)) with (1 + Z.of_nat n) in Hle
      by (rewrite Nat2Z.inj_succ; unfold Z.succ; lia).
    lia. }
  replace b with (start + (b - start)) in Hhi by ring.
  rewrite Hk in Hhi, Hlo.
  destruct k as [|k|k]; nia.
Qed.

Lemma zseq_pairwise_distinct :
  forall p start n,
    1 < p ->
    0 <= start ->
    start + Z.of_nat n <= p ->
    pairwise_distinct_mod p (zseq start n).
Proof.
  intros p start n Hp Hs Hle. revert start Hs Hle.
  induction n as [|n IH]; intros start Hs Hle; [simpl; exact I|].
  simpl. split.
  - apply zseq_Forall_distinct_head; lia.
  - apply IH; lia.
Qed.

Definition units_mod_prime (p : Z) : list Z := zseq 1 (Z.to_nat (p - 1)).

Lemma units_mod_prime_length :
  forall p, 1 < p -> length (units_mod_prime p) = Z.to_nat (p - 1).
Proof. intros p Hp. unfold units_mod_prime. apply zseq_length. Qed.

Lemma units_mod_prime_In :
  forall p x,
    1 < p ->
    In x (units_mod_prime p) ->
    1 <= x < p.
Proof.
  intros p x Hp Hin. unfold units_mod_prime in Hin.
  pose proof (zseq_In_bounds 1 (Z.to_nat (p - 1)) x Hin). lia.
Qed.

Lemma units_mod_prime_coprime :
  forall p,
    Z.prime p ->
    Forall (fun a => Z.coprime a p) (units_mod_prime p).
Proof.
  intros p Hp. apply Forall_forall. intros x Hin.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (units_mod_prime_In p x ltac:(lia) Hin).
  apply rel_prime_iff_coprime, rel_prime_le_prime;
    [apply prime_alt; exact Hp | lia].
Qed.

Lemma units_mod_prime_distinct :
  forall p,
    Z.prime p ->
    pairwise_distinct_mod p (units_mod_prime p).
Proof.
  intros p Hp. unfold units_mod_prime.
  pose proof (Z.prime_ge_2 p Hp).
  apply zseq_pairwise_distinct; lia.
Qed.

Lemma units_mod_prime_nonnil :
  forall p, 1 < p -> units_mod_prime p <> [].
Proof.
  intros p Hp. unfold units_mod_prime.
  destruct (Z.to_nat (p - 1)) eqn:Hnat; [|discriminate].
  apply (f_equal Z.of_nat) in Hnat. rewrite Z2Nat.id in Hnat; lia.
Qed.

Lemma order_mul_coprime :
  forall n a b ka kb,
    1 < n ->
    Z.coprime a n ->
    Z.coprime b n ->
    is_order n a ka ->
    is_order n b kb ->
    Z.gcd ka kb = 1 ->
    is_order n ((a * b) mod n) (ka * kb).
Proof.
  intros n a b ka kb Hn Hca Hcb [Hka [Ha1 Hamin]] [Hkb [Hb1 Hbmin]] Hg.
  split; [nia|]. split.
  - rewrite powm_mod_base by lia.
    rewrite powm_mul_base by nia.
    assert (Ha : powm a (ka * kb) n = 1).
    { rewrite (powm_one_mul a ka kb n) by (try lia; exact Ha1).
      apply Z.mod_1_l. lia. }
    assert (Hb : powm b (ka * kb) n = 1).
    { rewrite (Z.mul_comm ka kb).
      rewrite (powm_one_mul b kb ka n) by (try lia; exact Hb1).
      apply Z.mod_1_l. lia. }
    rewrite Ha, Hb, Z.mul_1_l. apply Z.mod_1_l. lia.
  - intros t [Htpos Htlt] Htpow.
    rewrite powm_mod_base in Htpow by lia.
    assert (Hakt : powm a (t * kb) n = 1).
    { assert (Hab : powm (a * b) (t * kb) n = 1).
      { rewrite (powm_one_mul (a * b) t kb n);
          [apply Z.mod_1_l; lia | lia | lia | lia | exact Htpow]. }
      rewrite powm_mul_base in Hab by nia.
      assert (Hbt : powm b (t * kb) n = 1).
      { rewrite (Z.mul_comm t kb).
        rewrite (powm_one_mul b kb t n);
          [apply Z.mod_1_l; lia | lia | lia | lia | exact Hb1]. }
      rewrite Hbt, Z.mul_1_r, Z.mod_small in Hab.
      2: { unfold powm. apply Z.mod_pos_bound. lia. }
      exact Hab. }
    assert (Hbkt : powm b (t * ka) n = 1).
    { assert (Hab : powm (a * b) (t * ka) n = 1).
      { rewrite (powm_one_mul (a * b) t ka n);
          [apply Z.mod_1_l; lia | lia | lia | lia | exact Htpow]. }
      rewrite powm_mul_base in Hab by nia.
      assert (Hat : powm a (t * ka) n = 1).
      { rewrite (Z.mul_comm t ka).
        rewrite (powm_one_mul a ka t n);
          [apply Z.mod_1_l; lia | lia | lia | lia | exact Ha1]. }
      rewrite Hat, Z.mul_1_l, Z.mod_small in Hab.
      2: { unfold powm. apply Z.mod_pos_bound. lia. }
      exact Hab. }
    assert (Hord_a : is_order n a ka).
    { split; [exact Hka | split; [exact Ha1 | exact Hamin]]. }
    assert (Hord_b : is_order n b kb).
    { split; [exact Hkb | split; [exact Hb1 | exact Hbmin]]. }
    assert (Hka_t : (ka | t)).
    { apply Z.gauss with kb; [| exact Hg].
      rewrite Z.mul_comm.
      apply (order_divides_annihilator n a ka (t * kb));
        [lia | nia | exact Hord_a | exact Hakt]. }
    assert (Hkb_t : (kb | t)).
    { apply Z.gauss with ka; [| rewrite Z.gcd_comm; exact Hg].
      rewrite Z.mul_comm.
      apply (order_divides_annihilator n b kb (t * ka));
        [lia | nia | exact Hord_b | exact Hbkt]. }
    destruct Hkb_t as [r Hr].
    assert (Hkar : (ka | kb * r)).
    { replace (kb * r) with t by (rewrite Hr; ring). exact Hka_t. }
    apply (Z.gauss ka kb r) in Hkar; [| exact Hg].
    destruct Hkar as [s Hs].
    assert (t = ka * kb * s) by nia.
    destruct s as [|s|s]; nia.
Qed.

Lemma order_of_divisor_power :
  forall n a d d',
    1 < n ->
    0 < d' ->
    (d' | d) ->
    is_order n a d ->
    is_order n (powm a (d / d') n) d'.
Proof.
  intros n a d d' Hn Hd' Hdiv Hord.
  destruct Hdiv as [q Hq].
  assert (0 < d) by apply Hord.
  assert (0 < q) by (destruct q as [|q|q]; nia).
  assert (d / d' = q) as Hquot.
  { rewrite Hq, Z.div_mul; lia. }
  rewrite Hquot.
  pose proof (order_of_power n a d q Hn ltac:(lia) Hord) as Hor.
  replace (d / Z.gcd d q) with d' in Hor.
  2: { rewrite Hq.
       assert (Z.gcd (q * d') q = q) as Hgq.
       { rewrite Z.gcd_comm.
         transitivity (Z.gcd (q * 1) (q * d')).
         - f_equal; lia.
         - assert (Heq : Z.gcd (q * 1) (q * d') = q * Z.gcd 1 d').
           { apply Z.gcd_mul_mono_l_nonneg. lia. }
           rewrite Heq, Z.gcd_1_l, Z.mul_1_r. reflexivity. }
       rewrite Hgq. rewrite (Z.mul_comm q d'), Z.div_mul; lia. }
  exact Hor.
Qed.

Lemma order_lcm_attained :
  forall n a b ka kb,
    1 < n ->
    Z.coprime a n ->
    Z.coprime b n ->
    is_order n a ka ->
    is_order n b kb ->
    exists c, Z.coprime c n /\ is_order n c (Z.lcm ka kb).
Proof.
  intros n a b ka kb Hn Hca Hcb Hoa Hob.
  assert (Hka : 0 < ka) by apply Hoa.
  assert (Hkb : 0 < kb) by apply Hob.
  destruct (lcm_coprime_factors ka kb Hka Hkb)
    as [ka' [kb' [Hka'pos [Hkb'pos [Hka'd [Hkb'd [Hg1 Hprod]]]]]]].
  set (a' := powm a (ka / ka') n).
  set (b' := powm b (kb / kb') n).
  assert (Horda' : is_order n a' ka').
  { unfold a'. apply order_of_divisor_power; [lia | lia | exact Hka'd | exact Hoa]. }
  assert (Hordb' : is_order n b' kb').
  { unfold b'. apply order_of_divisor_power; [lia | lia | exact Hkb'd | exact Hob]. }
  assert (Hca' : Z.coprime a' n).
  { unfold a'. apply coprime_powm; [lia | apply Z.div_pos; lia | exact Hca]. }
  assert (Hcb' : Z.coprime b' n).
  { unfold b'. apply coprime_powm; [lia | apply Z.div_pos; lia | exact Hcb]. }
  exists ((a' * b') mod n). split.
  - unfold Z.coprime. rewrite Z.gcd_mod_l by lia.
    apply Z.coprime_mul_l; [exact Hca' | exact Hcb'].
  - rewrite <- Hprod.
    apply order_mul_coprime; [lia | exact Hca' | exact Hcb' | exact Horda' | exact Hordb' | exact Hg1].
Qed.

Lemma exists_max_order_in :
  forall p xs,
    Z.prime p ->
    Forall (fun a => Z.coprime a p) xs ->
    xs <> [] ->
    exists a k,
      In a xs /\ is_order p a k /\
      forall b kb, In b xs -> is_order p b kb -> kb <= k.
Proof.
  intros p xs Hp. induction xs as [|x rest IH]; intros Hcop Hne.
  - contradiction.
  - destruct rest as [|y rest'].
    + apply Forall_inv in Hcop.
      destruct (order_exists_prime p x Hp Hcop) as [k Hk].
      exists x, k. split; [left; reflexivity|]. split; [exact Hk|].
      intros b kb Hin Hob.
      destruct Hin as [Heq | []]. subst b.
      pose proof (@is_order_unique p x k kb Hk Hob) as Huk. lia.
    + assert (Hrest : Forall (fun a => Z.coprime a p) (y :: rest')).
      { apply Forall_inv_tail in Hcop. exact Hcop. }
      destruct (IH Hrest ltac:(discriminate)) as [a0 [k0 [Hin0 [Hor0 Hmax0]]]].
      apply Forall_inv in Hcop.
      destruct (order_exists_prime p x Hp Hcop) as [kx Horx].
      destruct (Z.le_ge_cases kx k0) as [Hle | Hge].
      * exists a0, k0. split; [right; exact Hin0|]. split; [exact Hor0|].
        intros b kb Hin Hob. destruct Hin as [Heq | Hin].
        -- subst b. pose proof (@is_order_unique p x kx kb Horx Hob) as Huk. lia.
        -- apply (Hmax0 b kb); [exact Hin | exact Hob].
      * exists x, kx. split; [left; reflexivity|]. split; [exact Horx|].
        intros b kb Hin Hob. destruct Hin as [Heq | Hin].
        -- subst b. pose proof (@is_order_unique p x kx kb Horx Hob) as Huk. lia.
        -- pose proof (Hmax0 b kb Hin Hob). lia.
Qed.

Lemma zseq_In_interval :
  forall start n x,
    start <= x < start + Z.of_nat n ->
    In x (zseq start n).
Proof.
  intros start n. revert start.
  induction n as [|n IH]; intros start x Hx; simpl.
  - lia.
  - destruct (Z.eq_dec x start) as [Heq | Hne].
    + left. symmetry. exact Heq.
    + right. apply IH. lia.
Qed.

Lemma unit_mod_in_list :
  forall p a,
    Z.prime p ->
    Z.coprime a p ->
    In (a mod p) (units_mod_prime p).
Proof.
  intros p a Hp Hcop.
  pose proof (Z.prime_ge_2 p Hp).
  assert (0 < a mod p < p).
  { pose proof (Z.mod_pos_bound a p ltac:(lia)).
    split; [| lia].
    destruct (Z.eq_dec (a mod p) 0) as [Hz | Hnz]; [| lia].
    apply Z.mod_divide in Hz; [| lia].
    unfold Z.coprime in Hcop.
    assert (HpG : (p | Z.gcd a p)).
    { apply Z.gcd_greatest; [exact Hz | apply Z.divide_refl]. }
    rewrite Hcop in HpG. apply Z.divide_1_r in HpG. lia. }
  unfold units_mod_prime.
  apply zseq_In_interval. lia.
Qed.

Lemma is_order_mod_base :
  forall n a k,
    1 < n ->
    is_order n a k ->
    is_order n (a mod n) k.
Proof.
  intros n a k Hn [Hk [H1 Hmin]].
  rewrite <- (powm_mod_base a k n) in H1 by lia.
  split; [exact Hk|]. split; [exact H1|].
  intros k' Hk' Hpow.
  rewrite powm_mod_base in Hpow by lia.
  apply (Hmin k' Hk' Hpow).
Qed.

Lemma is_order_of_mod :
  forall n a k,
    1 < n ->
    is_order n (a mod n) k ->
    is_order n a k.
Proof.
  intros n a k Hn [Hk [H1 Hmin]].
  rewrite powm_mod_base in H1 by lia.
  split; [exact Hk|]. split; [exact H1|].
  intros k' Hk' Hpow.
  rewrite <- powm_mod_base in Hpow by lia.
  apply (Hmin k' Hk' Hpow).
Qed.

Lemma is_order_eq_mod :
  forall n a b k,
    1 < n ->
    a mod n = b mod n ->
    is_order n a k <-> is_order n b k.
Proof.
  intros n a b k Hn Heq. split; intros Hord.
  - apply is_order_of_mod; [lia|].
    rewrite <- Heq. apply is_order_mod_base; [lia | exact Hord].
  - apply is_order_of_mod; [lia|].
    rewrite Heq. apply is_order_mod_base; [lia | exact Hord].
Qed.

Theorem primitive_root_exists :
  forall p,
    Z.prime p ->
    exists g, Z.coprime g p /\ is_order p g (p - 1).
Proof.
  intros p Hp.
  pose proof (Z.prime_ge_2 p Hp) as Hp2.
  destruct (exists_max_order_in p (units_mod_prime p) Hp
              (units_mod_prime_coprime p Hp)
              (units_mod_prime_nonnil p ltac:(lia)))
    as [g [k [Hin [Hord Hmax]]]].
  pose proof (units_mod_prime_coprime p Hp) as HcsF.
  assert (Hcg : Z.coprime g p).
  { rewrite Forall_forall in HcsF. apply HcsF. exact Hin. }
  assert (Hkdiv : (k | p - 1)).
  { apply (order_divides_annihilator p g k (p - 1));
      [lia | lia | exact Hord | apply fermat_coprime; assumption]. }
  assert (Hkpos : 0 < k) by apply Hord.
  assert (k <= p - 1) by (apply Z.divide_pos_le; [lia | exact Hkdiv]).
  assert (Hall1 : forall b, Z.coprime b p -> powm b k p = 1).
  { intros b Hcb.
    destruct (order_exists_prime p b Hp Hcb) as [kb Horb].
    assert (0 < kb) by apply Horb.
    destruct (order_lcm_attained p g b k kb ltac:(lia) Hcg Hcb Hord Horb)
      as [c [Hcc Horc]].
    pose proof (is_order_mod_base p c (Z.lcm k kb) ltac:(lia) Horc) as Horcm.
    pose proof (unit_mod_in_list p c Hp Hcc) as Hinc.
    pose proof (Hmax (c mod p) (Z.lcm k kb) Hinc Horcm) as Hle.
    assert (Z.lcm k kb = k) as Hlcmk.
    { pose proof (Z.divide_lcm_l k kb) as Hdl.
      pose proof (lcm_pos k kb Hkpos ltac:(apply Horb)) as Hlp.
      apply Z.le_antisymm; [exact Hle | apply Z.divide_pos_le; [lia | exact Hdl]]. }
    rewrite <- Hlcmk.
    apply (proj1 (order_iff_divides p b kb (Z.lcm k kb) ltac:(lia) ltac:(lia) Horb)).
    apply Z.divide_lcm_r. }
  assert (k = p - 1) as Hkpe.
  { destruct (Z.eq_dec k (p - 1)) as [Heq | Hne]; [exact Heq|].
    exfalso.
    assert (Hklt : k < p - 1) by lia.
    assert (Hkn : (0 < Z.to_nat k)%nat).
    { destruct (Z.to_nat k) eqn:Hz; [| lia].
      apply (f_equal Z.of_nat) in Hz. rewrite Z2Nat.id in Hz; lia. }
    assert (Hdeg : (poly_degree (poly_Xn_minus_1 (Z.to_nat k)) <
                    length (units_mod_prime p))%nat).
    { rewrite poly_degree_Xn_minus_1 by exact Hkn.
      rewrite units_mod_prime_length by lia.
      apply Z2Nat.inj_lt; lia. }
    assert (Hvan : Forall
              (fun a => (p | poly_eval (poly_Xn_minus_1 (Z.to_nat k)) a))
              (units_mod_prime p)).
    { apply Forall_forall. intros a HaIn.
      assert (Hca : Z.coprime a p).
      { rewrite Forall_forall in HcsF. apply HcsF. exact HaIn. }
      rewrite poly_eval_Xn_minus_1, Z2Nat.id by lia.
      apply Z.mod_divide; [lia|].
      pose proof (Hall1 a Hca) as Hpow1. unfold powm in Hpow1.
      rewrite Zminus_mod, Hpow1, Z.mod_1_l, Z.sub_diag, Z.mod_0_l; lia. }
    pose proof (poly_prime_roots_divides p (units_mod_prime p)
                  (poly_Xn_minus_1 (Z.to_nat k)) Hp
                  (units_mod_prime_distinct p Hp) Hdeg Hvan (Z.to_nat k))
      as Hlead.
    rewrite Xn_minus_1_leading in Hlead by (apply Nat.le_succ_l; exact Hkn).
    apply Z.divide_1_r in Hlead. lia. }
  exists g. split; [exact Hcg | rewrite <- Hkpe; exact Hord].
Qed.

Lemma order_semiprime_from_locals :
  forall p q a kp kq,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime a (p * q) ->
    is_order p a kp ->
    is_order q a kq ->
    is_order (p * q) a (Z.lcm kp kq).
Proof.
  intros p q a kp kq Hp Hq Hneq Hcop Horp Horq.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  assert (0 < kp) by apply Horp.
  assert (0 < kq) by apply Horq.
  pose proof (lcm_pos kp kq ltac:(lia) ltac:(lia)) as Hlp.
  apply coprime_semiprime in Hcop; [| assumption | assumption | assumption].
  destruct Hcop as [Hap Haq].
  split; [lia|]. split.
  - assert (Hp1 : powm a (Z.lcm kp kq) p = 1).
    { apply (proj1 (order_iff_divides p a kp (Z.lcm kp kq) ltac:(lia) ltac:(lia) Horp)).
      apply Z.divide_lcm_l. }
    assert (Hq1 : powm a (Z.lcm kp kq) q = 1).
    { apply (proj1 (order_iff_divides q a kq (Z.lcm kp kq) ltac:(lia) ltac:(lia) Horq)).
      apply Z.divide_lcm_r. }
    unfold powm in Hp1, Hq1 |- *.
    apply crt_one; try assumption.
  - intros t [Htpos Htlt] Ht1.
    assert (Htp : powm a t p = 1).
    { pose proof (powm_reduce_factor a t p q ltac:(lia) ltac:(lia) ltac:(lia)) as Hr.
      rewrite Ht1, Z.mod_1_l in Hr by lia. symmetry; exact Hr. }
    assert (Htq : powm a t q = 1).
    { pose proof (powm_reduce_factor a t q p ltac:(lia) ltac:(lia) ltac:(lia)) as Hr.
      rewrite Z.mul_comm in Hr.
      rewrite Ht1, Z.mod_1_l in Hr by lia. symmetry; exact Hr. }
    assert (Hkp_t : (kp | t)).
    { apply (proj2 (order_iff_divides p a kp t ltac:(lia) ltac:(lia) Horp)).
      exact Htp. }
    assert (Hkq_t : (kq | t)).
    { apply (proj2 (order_iff_divides q a kq t ltac:(lia) ltac:(lia) Horq)).
      exact Htq. }
    pose proof (Z.lcm_least kp kq t Hkp_t Hkq_t) as Hdiv.
    apply Z.divide_pos_le in Hdiv; [| lia].
    lia.
Qed.

Theorem exists_unit_order_lambda :
  forall p q,
    Z.prime p -> Z.prime q -> p <> q ->
    exists a, Z.coprime a (p * q) /\
      is_order (p * q) a (lambda_semiprime p q).
Proof.
  intros p q Hp Hq Hneq.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  destruct (primitive_root_exists p Hp) as [gp [Hgp Horp]].
  destruct (primitive_root_exists q Hq) as [gq [Hgq Horq]].
  set (g := crt2 p q gp gq).
  pose proof (crt2_mod p q gp gq Hp Hq Hneq) as [Hgpmod Hgqmod].
  assert (Hcp : Z.coprime g p).
  { unfold Z.coprime.
    rewrite <- (Z.gcd_mod_l g p) by lia.
    unfold g. rewrite Hgpmod.
    rewrite Z.gcd_mod_l by lia. exact Hgp. }
  assert (Hcq : Z.coprime g q).
  { unfold Z.coprime.
    rewrite <- (Z.gcd_mod_l g q) by lia.
    unfold g. rewrite Hgqmod.
    rewrite Z.gcd_mod_l by lia. exact Hgq. }
  assert (HcN : Z.coprime g (p * q)).
  { apply coprime_semiprime; [exact Hp | exact Hq | exact Hneq | split; [exact Hcp | exact Hcq]]. }
  assert (Horpg : is_order p g (p - 1)).
  { apply (proj2 (is_order_eq_mod p g gp (p - 1) ltac:(lia) Hgpmod)).
    exact Horp. }
  assert (Horqg : is_order q g (q - 1)).
  { apply (proj2 (is_order_eq_mod q g gq (q - 1) ltac:(lia) Hgqmod)).
    exact Horq. }
  exists g. split; [exact HcN|].
  unfold lambda_semiprime.
  apply (order_semiprime_from_locals p q g (p - 1) (q - 1));
    [exact Hp | exact Hq | exact Hneq | exact HcN | exact Horpg | exact Horqg].
Qed.

Theorem exists_unit_order_lambda_pin :
  exists a, Z.coprime a pin_N /\ is_order pin_N a 80.
Proof.
  destruct (exists_unit_order_lambda 11 17 prime_11 prime_17 ltac:(lia))
    as [a [Hc Ho]].
  exists a. split; [exact Hc|].
  replace (lambda_semiprime pin_p pin_q) with pin_lam in Ho by (apply rsa_test_lambda).
  exact Ho.
Qed.

(** ** A primitive root generates [𝔽_p*]

    Powers [g^0,…,g^{p−2}] are pairwise distinct units, hence every
    unit is one of them.  Not a named iso [(Z/pZ)* ≅ C_{p−1}]. *)

Lemma mul_cancel_unit_mod :
  forall n u x y,
    1 < n ->
    Z.coprime u n ->
    (u * x) mod n = (u * y) mod n ->
    x mod n = y mod n.
Proof.
  intros n u x y Hn Hu Heq.
  apply mods_eq_iff_divides in Heq; [| lia].
  replace (u * x - u * y) with (u * (x - y)) in Heq by ring.
  apply Z.gauss in Heq.
  2: { unfold Z.coprime in Hu. rewrite Z.gcd_comm. exact Hu. }
  apply mods_eq_iff_divides; [lia | exact Heq].
Qed.

Lemma powm_eq_pow_cancel :
  forall n a i d,
    1 < n ->
    Z.coprime a n ->
    0 <= i ->
    0 <= d ->
    powm a (i + d) n = powm a i n ->
    powm a d n = 1.
Proof.
  intros n a i d Hn Hcop Hi Hd Hadd.
  pose proof (powm_add_r a i d n ltac:(lia) ltac:(lia) ltac:(lia)) as Hsum.
  rewrite Hadd in Hsum.
  assert (Hcu : Z.coprime (powm a i n) n).
  { apply coprime_powm; [lia | lia | exact Hcop]. }
  assert ((powm a i n * powm a d n) mod n = (powm a i n * 1) mod n)
    as Hmul.
  { rewrite <- Hsum. rewrite Z.mul_1_r.
    unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
  apply mul_cancel_unit_mod in Hmul; [| lia | exact Hcu].
  rewrite Z.mod_1_l in Hmul by lia.
  unfold powm in Hmul. rewrite Z.mod_mod in Hmul by lia.
  fold (powm a d n) in Hmul. exact Hmul.
Qed.

Lemma powm_inj_lt_order :
  forall n a k i j,
    1 < n ->
    Z.coprime a n ->
    is_order n a k ->
    0 <= i < k ->
    0 <= j < k ->
    powm a i n = powm a j n ->
    i = j.
Proof.
  intros n a k i j Hn Hcop Hor Hi Hj Heq.
  destruct Hor as [Hk [H1 Hmin]].
  destruct (Z.le_ge_cases i j) as [Hle | Hge].
  - destruct (Z.eq_dec i j) as [Heqij | Hne]; [exact Heqij|].
    exfalso.
    assert (powm a (j - i) n = 1) as Hd1.
    { apply (powm_eq_pow_cancel n a i (j - i)
        ltac:(lia) Hcop ltac:(lia) ltac:(lia)).
      replace (i + (j - i)) with j by ring. symmetry; exact Heq. }
    apply (Hmin (j - i)); [lia | exact Hd1].
  - destruct (Z.eq_dec i j) as [Heqij | Hne]; [exact Heqij|].
    exfalso.
    assert (powm a (i - j) n = 1) as Hd1.
    { apply (powm_eq_pow_cancel n a j (i - j)
        ltac:(lia) Hcop ltac:(lia) ltac:(lia)).
      replace (j + (i - j)) with i by ring. exact Heq. }
    apply (Hmin (i - j)); [lia | exact Hd1].
Qed.

Lemma nodup_incl_le :
  forall (l l' : list Z),
    NoDup l ->
    (forall x, In x l -> In x l') ->
    (length l <= length l')%nat.
Proof.
  intros l. induction l as [|x xs IH]; intros l' Hnd Hincl.
  - simpl. lia.
  - inversion Hnd as [|? ? Hni Hnd']. subst.
    assert (In x l') as Hx by (apply Hincl; left; reflexivity).
    apply in_split in Hx. destruct Hx as [l1 [l2 Heq]]. subst l'.
    assert ((length xs <= length (l1 ++ l2))%nat).
    { apply IH; [exact Hnd'|].
      intros y Hy.
      assert (In y (l1 ++ x :: l2)) by (apply Hincl; right; exact Hy).
      rewrite in_app_iff in H. destruct H as [Hin1 | Hin2].
      - rewrite in_app_iff. left. exact Hin1.
      - simpl in Hin2. destruct Hin2 as [Heqy | Hin2].
        + subst y. contradiction.
        + rewrite in_app_iff. right. exact Hin2. }
    rewrite length_app in *. simpl in *. lia.
Qed.

Fixpoint powers_upto (g p : Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => powm g (Z.of_nat n') p :: powers_upto g p n'
  end.

Lemma powers_upto_length :
  forall g p n, length (powers_upto g p n) = n.
Proof.
  intros g p n. induction n as [|n IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma powers_upto_In :
  forall g p n x,
    In x (powers_upto g p n) ->
    exists i, (i < n)%nat /\ x = powm g (Z.of_nat i) p.
Proof.
  intros g p n. induction n as [|n IH]; intros x Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + exists n. split; [lia | symmetry; exact Heq].
    + destruct (IH x Hin) as [i [Hi Hx]].
      exists i. split; [lia | exact Hx].
Qed.

Lemma powers_upto_NoDup :
  forall p g n,
    1 < p ->
    Z.coprime g p ->
    is_order p g (p - 1) ->
    (Z.of_nat n <= p - 1) ->
    NoDup (powers_upto g p n).
Proof.
  intros p g n Hp Hg Hor Hn. induction n as [|n IH]; simpl.
  - constructor.
  - constructor.
    + intros Hin.
      destruct (powers_upto_In g p n _ Hin) as [i [Hi Heq]].
      assert (Z.of_nat n = Z.of_nat i) as Hii.
      { apply (powm_inj_lt_order p g (p - 1) (Z.of_nat n) (Z.of_nat i));
          try lia; try assumption. }
      apply Nat2Z.inj in Hii. lia.
    + apply IH. lia.
Qed.

Theorem primitive_root_generates :
  forall p g a,
    Z.prime p ->
    Z.coprime g p ->
    is_order p g (p - 1) ->
    Z.coprime a p ->
    exists k, 0 <= k < p - 1 /\ powm g k p = a mod p.
Proof.
  intros p g a Hp Hg Hor Ha.
  pose proof (Z.prime_ge_2 p Hp).
  set (n := Z.to_nat (p - 1)).
  assert (Z.of_nat n = p - 1) as HnZ by (apply Z2Nat.id; lia).
  set (ps := powers_upto g p n).
  assert (length ps = n) as Hlen by apply powers_upto_length.
  assert (NoDup ps) as Hnd.
  { unfold ps, n. apply powers_upto_NoDup; try assumption; lia. }
  destruct (in_dec Z.eq_dec (a mod p) ps) as [Hin | Hnin].
  - destruct (powers_upto_In g p n _ Hin) as [i [Hi Heq]].
    exists (Z.of_nat i). split; [| symmetry; exact Heq].
    split; [lia|]. rewrite <- HnZ. apply Nat2Z.inj_lt. exact Hi.
  - exfalso.
    assert (NoDup (a mod p :: ps)) as Hnda.
    { constructor; [exact Hnin | exact Hnd]. }
    assert (forall x, In x (a mod p :: ps) -> In x (units_mod_prime p))
      as Hall.
    { intros x Hx. destruct Hx as [Heq | Hx].
      - subst x. apply unit_mod_in_list; assumption.
      - destruct (powers_upto_In g p n _ Hx) as [i [Hi Hiq]].
        rewrite Hiq. unfold powm. apply unit_mod_in_list; [exact Hp|].
        unfold Z.coprime.
        rewrite <- (Z.gcd_mod_l (g ^ Z.of_nat i) p) by lia.
        fold (powm g (Z.of_nat i) p).
        apply coprime_powm; [lia | lia | exact Hg]. }
    assert (Nat.le (length ((a mod p) :: ps)) (length (units_mod_prime p)))
      as Hle.
    { apply nodup_incl_le; [exact Hnda | exact Hall]. }
    rewrite units_mod_prime_length in Hle by lia.
    simpl in Hle. rewrite Hlen in Hle. unfold n in Hle. lia.
Qed.
