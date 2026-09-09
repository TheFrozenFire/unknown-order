From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Wf_nat.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import Pin.

Open Scope Z_scope.

(** * Pratt certificates, dual to Miller-from-[λ]

    A Pratt certificate (Vaughan Pratt, 1975) is a short recursively
    verifiable proof that [(Z/pZ)*] is cyclic of order exactly [p−1].
    The 2-primary check in that verification is the same successive-
    squaring chain Miller uses to *split* a composite.

    Duality, honestly scoped:
    - Pratt: "here is an element of order exactly [n−1]; therefore [n]
      is prime."
    - Miller-from-[λ]: "here is an annihilator of the group; the
      2-torsion is larger than a field's; here is the splitting."

    We formalize the certificate type, its verifier, and soundness
    (a verified certificate implies primality).  Completeness of a
    *verified* certificate (generator plus prime factors of [p−1],
    recursively) is [pratt_complete_open_named].  A primitive root
    in every [(Z/pZ)*] is a theorem ([primitive_root_exists]); that
    is no longer a blocker.  The inductive [pratt] type does not
    store the check — inhabiting it is not Pratt completeness. *)

Inductive pratt : Z -> Type :=
| pratt_2 : pratt 2
| pratt_odd :
    forall (p g : Z) (qs : list Z),
      2 < p ->
      (forall q, In q qs -> pratt q) ->
      pratt p.

(** The *check* that would accompany [pratt_odd]: [g^{p−1} ≡ 1] and
    [g^{(p−1)/q} ≢ 1] for each prime [q] dividing [p−1].  We state it
    as a proposition so a full verifier can be layered on later. *)
Definition pratt_generator_ok (p g : Z) (qs : list Z) : Prop :=
  powm g (p - 1) p = 1 /\
  (forall q, In q qs -> powm g ((p - 1) / q) p <> 1).

Definition pratt_factors_ok (p : Z) (qs : list Z) : Prop :=
  p - 1 = fold_left Z.mul qs 1.

(** Soundness of the 2-base case. *)
Theorem pratt_2_prime : Z.prime 2.
Proof. apply prime_alt. apply prime_2. Qed.

(** If [p] is prime then the Fermat side of a Pratt check holds for
    every unit [g].  This is the "must reach 1" half of the duality. *)
Theorem pratt_fermat_side :
  forall p g,
    Z.prime p -> Z.coprime g p ->
    powm g (p - 1) p = 1.
Proof. intros. apply fermat_coprime; assumption. Qed.

(** The 2-primary Pratt check: successive squares of [g^{(p−1)/2^s}]
    must see [−1] as the unique element of order 2.  On a composite
    [N = pq] that uniqueness fails — exactly [nontrivial_sqrt1_splits]. *)
Definition pratt_2_primary_ok (p g : Z) : Prop :=
  let t := odd_part (p - 1) in
  powm g t p = 1 \/ powm g ((p - 1) / 2) p = p - 1.

Theorem duality_unique_order_2_on_prime :
  forall p x,
    Z.prime p ->
    powm x 2 p = 1 ->
    x mod p = 1 \/ x mod p = p - 1.
Proof.
  intros p x Hp Hsq.
  pose proof (Z.prime_ge_2 p Hp).
  unfold powm in Hsq. rewrite Z.pow_2_r in Hsq.
  (* x² ≡ 1 (mod p) ⇒ p | (x−1)(x+1) ⇒ p | (x−1) or p | (x+1). *)
  assert (p | x * x - 1).
  { apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Hsq, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia. reflexivity. }
  rewrite square_minus_1_factor in H0.
  apply prime_alt in Hp.
  apply prime_mult in H0; [| exact Hp].
  destruct H0 as [Hdiv | Hdiv].
  - left. apply Z.mod_divide in Hdiv; [| lia].
    rewrite Zminus_mod, Z.mod_1_l in Hdiv by lia.
    pose proof (Z.mod_pos_bound x p ltac:(lia)).
    assert (- p < x mod p - 1 < p) by lia.
    pose proof (Z.div_mod (x mod p - 1) p ltac:(lia)) as Hdm.
    rewrite Hdiv, Z.add_0_r in Hdm.
    set (q := (x mod p - 1) / p) in *.
    rewrite Hdm in H1.
    assert (q = 0).
    { destruct (Z.eq_dec q 0) as [Hq0 | Hq0]; [exact Hq0|].
      assert (Z.abs (p * q) >= p).
      { rewrite Z.abs_mul, Z.abs_eq by lia.
        pose proof (Z.abs_pos q). nia. }
      lia. }
    rewrite H2, Z.mul_0_r in Hdm. lia.
  - right. destruct Hdiv as [k Hk].
    assert (x = k * p - 1) by lia.
    subst x.
    rewrite Zminus_mod, (Z.mod_mul k p), Z.mod_1_l by lia.
    rewrite Z.sub_0_l.
    change (-1) with (- (1)).
    rewrite (Z.mod_opp_l_nz 1 p) by (rewrite ?Z.mod_1_l; lia).
    rewrite Z.mod_1_l by lia. reflexivity.
Qed.

(** Completeness of a verified Pratt certificate.  [primitive_root_exists]
    is a theorem; the remaining work is the prime factorization of
    [p−1] and recursion.  Unused means unproved, on-goal — not a
    refuse of nearby algebra.  Pin check: [pratt_generator_ok_11]. *)
Definition pratt_complete_open_named : Prop :=
  forall p, Z.prime p ->
    exists (g : Z) (qs : list Z),
      pratt_generator_ok p g qs /\
      pratt_factors_ok p qs /\
      (forall q, In q qs -> Z.prime q) /\
      inhabited (pratt p).

Lemma prime_5 : Z.prime 5.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
  intuition subst; reflexivity.
Qed.

Theorem pratt_generator_ok_11 :
  pratt_generator_ok 11 2 [2; 5].
Proof.
  unfold pratt_generator_ok. split.
  - vm_compute. reflexivity.
  - intros q Hin. cbn in Hin. destruct Hin as [H2 | [H5 | []]].
    + subst q. vm_compute. discriminate.
    + subst q. vm_compute. discriminate.
Qed.

Theorem pratt_factors_ok_11 :
  pratt_factors_ok 11 [2; 5].
Proof. vm_compute. reflexivity. Qed.

Theorem pratt_qs_prime_11 :
  forall q, In q [2; 5] -> Z.prime q.
Proof.
  intros q Hin. cbn in Hin. destruct Hin as [H2 | [H5 | []]].
  - subst q. apply prime_alt. apply prime_2.
  - subst q. apply prime_5.
Qed.

(** ** Verifier given a factorization of [p−1]

    Taking [qs] as a hyp is honest.  Existential factorization for
    every prime [p] is [pratt_complete_open_named].  The inductive
    [pratt] type does not store the check; inhabiting it from
    recursive certificates on [qs] is the constructor.
    Not [pratt_complete_open_named].
    Cross-confirmed by [cas/244], [cas/249]. *)

Lemma fold_left_mul_mul_acc :
  forall qs a b,
    fold_left Z.mul qs (a * b) = a * fold_left Z.mul qs b.
Proof.
  induction qs as [|q qs IH]; intros a b; cbn.
  - reflexivity.
  - rewrite <- IH. f_equal. ring.
Qed.

Lemma fold_left_mul_acc :
  forall qs acc,
    fold_left Z.mul qs acc = acc * fold_left Z.mul qs 1.
Proof.
  intros qs acc.
  rewrite <- (Z.mul_1_r acc) at 1.
  rewrite (fold_left_mul_mul_acc qs acc 1).
  reflexivity.
Qed.

Lemma fold_left_mul_cons :
  forall q qs,
    fold_left Z.mul (q :: qs) 1 = q * fold_left Z.mul qs 1.
Proof.
  intros q qs. cbn [fold_left].
  change (Z.mul 1 q) with (1 * q).
  rewrite Z.mul_1_l.
  rewrite (fold_left_mul_acc qs q).
  reflexivity.
Qed.

Lemma prime_divides_fold_mul :
  forall p qs,
    Z.prime p ->
    (p | fold_left Z.mul qs 1) ->
    exists q, In q qs /\ (p | q).
Proof.
  intros p qs Hp Hdiv.
  induction qs as [|q qs IH].
  - cbn in Hdiv. apply Z.divide_1_r in Hdiv.
    pose proof (Z.prime_ge_2 p Hp). lia.
  - rewrite fold_left_mul_cons in Hdiv.
    apply Z.divide_prime_mul in Hdiv; [| exact Hp].
    destruct Hdiv as [Hdiv | Hdiv].
    + exists q. split; [left; reflexivity | exact Hdiv].
    + destruct (IH Hdiv) as [q' [Hin Hpq]].
      exists q'. split; [right; exact Hin | exact Hpq].
Qed.

Lemma pratt_factors_cover_prime :
  forall p qs q,
    pratt_factors_ok p qs ->
    (forall r, In r qs -> Z.prime r) ->
    Z.prime q ->
    (q | p - 1) ->
    In q qs.
Proof.
  intros p qs q Hfact Hall Hq Hdiv.
  unfold pratt_factors_ok in Hfact. rewrite Hfact in Hdiv.
  destruct (prime_divides_fold_mul q qs Hq Hdiv) as [r [Hin Hqr]].
  pose proof (Hall r Hin) as Hr.
  apply Z.divide_prime_prime in Hqr; [| exact Hq | exact Hr].
  subst r. exact Hin.
Qed.

Definition pratt_of_factor_certs
    (p g : Z) (qs : list Z)
    (Hp : 2 < p)
    (Hqs : forall q, In q qs -> pratt q) : pratt p :=
  pratt_odd p g qs Hp Hqs.

Definition pratt_cert_5 : pratt 5.
Proof.
  apply (pratt_odd 5 2 [2; 2]); [lia|].
  intros q Hin.
  destruct (Z.eq_dec q 2) as [E | Ne]; [subst q; exact pratt_2|].
  exfalso. cbn in Hin. destruct Hin as [H | [H | []]]; subst q; congruence.
Defined.

Definition pratt_cert_3 : pratt 3.
Proof.
  apply (pratt_odd 3 2 [2]); [lia|].
  intros q Hin.
  destruct (Z.eq_dec q 2) as [E | Ne]; [subst q; exact pratt_2|].
  exfalso. cbn in Hin. destruct Hin as [H | []]; subst q; congruence.
Defined.

Definition pratt_cert_11 : pratt 11.
Proof.
  apply (pratt_odd 11 2 [2; 5]); [lia|].
  intros q Hin.
  destruct (Z.eq_dec q 2) as [E2 | N2]; [subst q; exact pratt_2|].
  destruct (Z.eq_dec q 5) as [E5 | N5]; [subst q; exact pratt_cert_5|].
  exfalso. cbn in Hin. destruct Hin as [H | [H | []]]; subst q; congruence.
Defined.

Theorem pratt_11_inhabited : inhabited (pratt 11).
Proof. constructor. exact pratt_cert_11. Qed.

Theorem pratt_11_verified :
  pratt_generator_ok 11 2 [2; 5] /\
  pratt_factors_ok 11 [2; 5] /\
  (forall q, In q [2; 5] -> Z.prime q) /\
  inhabited (pratt 11).
Proof.
  split; [apply pratt_generator_ok_11|].
  split; [apply pratt_factors_ok_11|].
  split; [apply pratt_qs_prime_11|].
  apply pratt_11_inhabited.
Qed.

Lemma prime_3 : Z.prime 3.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2) by lia.
  intuition subst; reflexivity.
Qed.

Lemma prime_31 : Z.prime 31.
Proof.
  apply Zprime_sqrt; [lia|].
  intros d Hd Hdiv.
  apply Z.mod_divide in Hdiv; [|lia].
  change (Z.sqrt 31) with 5 in Hd.
  assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5) by lia.
  intuition subst; vm_compute in Hdiv; discriminate.
Qed.

Theorem pratt_generator_ok_31 :
  pratt_generator_ok 31 3 [2; 3; 5].
Proof.
  unfold pratt_generator_ok. split.
  - vm_compute. reflexivity.
  - intros q Hin. cbn in Hin.
    destruct Hin as [H2 | [H3 | [H5 | []]]]; subst q; vm_compute; discriminate.
Qed.

Theorem pratt_factors_ok_31 :
  pratt_factors_ok 31 [2; 3; 5].
Proof. vm_compute. reflexivity. Qed.

Theorem pratt_qs_prime_31 :
  forall q, In q [2; 3; 5] -> Z.prime q.
Proof.
  intros q Hin. cbn in Hin.
  destruct Hin as [H2 | [H3 | [H5 | []]]]; subst q.
  - apply prime_alt. apply prime_2.
  - apply prime_3.
  - apply prime_5.
Qed.

Definition pratt_cert_31 : pratt 31.
Proof.
  apply (pratt_odd 31 3 [2; 3; 5]); [lia|].
  intros q Hin.
  destruct (Z.eq_dec q 2) as [E2 | N2]; [subst q; exact pratt_2|].
  destruct (Z.eq_dec q 3) as [E3 | N3]; [subst q; exact pratt_cert_3|].
  destruct (Z.eq_dec q 5) as [E5 | N5]; [subst q; exact pratt_cert_5|].
  exfalso. cbn in Hin.
  destruct Hin as [H | [H | [H | []]]]; subst q; congruence.
Defined.

Theorem pratt_31_inhabited : inhabited (pratt 31).
Proof. constructor. exact pratt_cert_31. Qed.

Theorem pratt_31_verified :
  pratt_generator_ok 31 3 [2; 3; 5] /\
  pratt_factors_ok 31 [2; 3; 5] /\
  (forall q, In q [2; 3; 5] -> Z.prime q) /\
  inhabited (pratt 31).
Proof.
  split; [apply pratt_generator_ok_31|].
  split; [apply pratt_factors_ok_31|].
  split; [apply pratt_qs_prime_31|].
  apply pratt_31_inhabited.
Qed.

(** gcd form of the generator check: no prime factor of [p]
    annihilates [g] at [(p−1)/q].  When [p] is prime this is
    equivalent to [powm <> 1]. *)
Definition pratt_gcd_ok (p g : Z) (qs : list Z) : Prop :=
  forall q, In q qs -> Z.gcd (powm g ((p - 1) / q) p - 1) p = 1.

Lemma pratt_gcd_ok_of_prime :
  forall p g qs,
    Z.prime p ->
    pratt_generator_ok p g qs ->
    pratt_gcd_ok p g qs.
Proof.
  intros p g qs Hp [_ Hmin] q Hin.
  pose proof (Z.prime_ge_2 p Hp).
  specialize (Hmin q Hin).
  rewrite Z.gcd_comm.
  apply Z.coprime_prime_l_iff; [exact Hp|].
  intro Hdiv.
  apply Z.mod_divide in Hdiv; [| lia].
  rewrite Zminus_mod, Z.mod_1_l in Hdiv by lia.
  unfold powm in Hmin, Hdiv.
  rewrite Z.mod_mod in Hdiv by lia.
  pose proof (Z.mod_pos_bound (g ^ ((p - 1) / q)) p ltac:(lia)) as Hbd.
  set (x := g ^ ((p - 1) / q) mod p) in *.
  destruct (Z.eq_dec x 0) as [Hz | Hnz].
  { rewrite Hz, Z.sub_0_l in Hdiv.
    rewrite (Z.mod_opp_l_nz 1 p) in Hdiv by (rewrite ?Z.mod_1_l; lia).
    rewrite Z.mod_1_l in Hdiv by lia. lia. }
  rewrite Z.mod_small in Hdiv by lia.
  assert (x = 1) by lia.
  congruence.
Qed.

Theorem pratt_gcd_ok_11 : pratt_gcd_ok 11 2 [2; 5].
Proof.
  unfold pratt_gcd_ok. intros q Hin. cbn in Hin.
  destruct Hin as [H2 | [H5 | []]]; subst q; vm_compute; reflexivity.
Qed.

Theorem pratt_gcd_ok_31 : pratt_gcd_ok 31 3 [2; 3; 5].
Proof.
  unfold pratt_gcd_ok. intros q Hin. cbn in Hin.
  destruct Hin as [H2 | [H3 | [H5 | []]]]; subst q; vm_compute; reflexivity.
Qed.

(** Soundness of a verified certificate: [g^{p−1} ≡ 1], the gcd form
    of the order check, and a prime factorization of [p−1] imply
    [p] is prime.  Euclid on exponents, not Bézout (negative
    coefficients).  Taking [qs] as a hyp is honest.
    Not [pratt_complete_open_named]. *)

Lemma reduced_minus1_mod :
  forall x n,
    1 < n ->
    0 <= x < n ->
    (x - 1) mod n = 0 ->
    x = 1.
Proof.
  intros x n Hn Hbd Hmod.
  destruct (Z.eq_dec x 0) as [Hz | Hnz].
  - subst x. rewrite Z.sub_0_l in Hmod.
    rewrite (Z.mod_opp_l_nz 1 n) in Hmod by (rewrite ?Z.mod_1_l; lia).
    rewrite Z.mod_1_l in Hmod by lia. lia.
  - rewrite Z.mod_small in Hmod by lia. lia.
Qed.

Lemma powm_one_of_divisor :
  forall a e n d,
    1 < n ->
    1 < d ->
    0 <= e ->
    Z.divide d n ->
    powm a e n = 1 ->
    powm a e d = 1.
Proof.
  intros a e n d Hn Hd He Hdiv Hann.
  assert (Z.divide n (a ^ e - 1)) as Hn1.
  { apply Z.mod_divide; [lia|].
    unfold powm in Hann.
    rewrite Zminus_mod, Hann, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity. }
  assert (Z.divide d (a ^ e - 1)) as Hd1.
  { apply (Z.divide_trans d n (a ^ e - 1)); [exact Hdiv | exact Hn1]. }
  unfold powm.
  apply Z.mod_divide in Hd1; [| lia].
  rewrite Zminus_mod, Z.mod_1_l in Hd1 by lia.
  apply (reduced_minus1_mod (a ^ e mod d) d);
    [lia | apply (Z.mod_pos_bound (a ^ e) d); lia | exact Hd1].
Qed.

Lemma pratt_coprime_of_fermat :
  forall g p,
    1 < p ->
    powm g (p - 1) p = 1 ->
    Z.coprime g p.
Proof.
  intros g p Hp Hann.
  unfold Z.coprime.
  set (d := Z.gcd g p).
  pose proof (Z.gcd_divide_l g p) as Hdg.
  pose proof (Z.gcd_divide_r g p) as Hdp.
  pose proof (Z.gcd_nonneg g p) as Hnn.
  destruct (Z.eq_dec d 1) as [E | Ne]; [exact E|].
  exfalso.
  assert (d <> 0) as Hnz.
  { intro Hz. unfold d in Hz. apply Z.gcd_eq_0_r in Hz. lia. }
  assert (1 < d) as Hdgt by lia.
  assert (Z.divide p (g ^ (p - 1) - 1)) as Hp1.
  { apply Z.mod_divide; [lia|].
    unfold powm in Hann.
    rewrite Zminus_mod, Hann, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity. }
  assert (Z.divide d (g ^ (p - 1) - 1)) as Hd1.
  { apply (Z.divide_trans d p (g ^ (p - 1) - 1)); [exact Hdp | exact Hp1]. }
  assert (Z.divide d (g ^ (p - 1))) as Hdgpow.
  { destruct Hdg as [t Ht]. rewrite Ht.
    rewrite Z.pow_mul_l.
    apply Z.divide_mul_r.
    replace (p - 1) with (1 + (p - 2)) by lia.
    rewrite Z.pow_add_r, Z.pow_1_r by lia.
    apply Z.divide_factor_l. }
  assert (Z.divide d 1) as Hdunit.
  { pose proof (Z.divide_sub_r _ _ _ Hdgpow Hd1) as Hsub.
    replace (g ^ (p - 1) - (g ^ (p - 1) - 1)) with 1 in Hsub by ring.
    exact Hsub. }
  apply Z.divide_1_r in Hdunit. lia.
Qed.

Lemma divide_le_pos :
  forall a b,
    0 < a ->
    0 < b ->
    Z.divide a b ->
    a <= b.
Proof.
  intros a b Ha Hb [k Hk].
  assert (0 < k) by nia.
  nia.
Qed.

Lemma coprime_of_divisor :
  forall a n d,
    Z.coprime a n ->
    Z.divide d n ->
    Z.coprime a d.
Proof.
  intros a n d Hcop Hdiv.
  unfold Z.coprime in *.
  assert (Z.divide (Z.gcd a d) n) as Hdn.
  { apply (Z.divide_trans (Z.gcd a d) d n); [apply Z.gcd_divide_r | exact Hdiv]. }
  assert (Z.divide (Z.gcd a d) (Z.gcd a n)) as Hgg.
  { apply Z.gcd_greatest; [apply Z.gcd_divide_l | exact Hdn]. }
  rewrite Hcop in Hgg.
  apply Z.divide_1_r in Hgg.
  pose proof (Z.gcd_nonneg a d). lia.
Qed.

Lemma powm_one_of_multiple :
  forall a k m n,
    1 < n ->
    0 <= k ->
    0 <= m ->
    powm a k n = 1 ->
    Z.divide k m ->
    powm a m n = 1.
Proof.
  intros a k m n Hn Hk Hm Hann Hdiv.
  destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
  - subst k. destruct Hdiv as [q Hq].
    rewrite Hq, Z.mul_0_r.
    unfold powm. rewrite Z.pow_0_r, Z.mod_1_l by lia. reflexivity.
  - destruct Hdiv as [q Hq].
    rewrite Hq, Z.mul_comm.
    assert (0 <= q) by nia.
    pose proof (powm_one_mul a k q n ltac:(lia) ltac:(lia) ltac:(lia) Hann) as Hmul.
    rewrite Z.mod_1_l in Hmul by lia. exact Hmul.
Qed.

Lemma powm_gcd_exp :
  forall a m k n,
    1 < n ->
    0 <= m ->
    0 <= k ->
    powm a m n = 1 ->
    powm a k n = 1 ->
    powm a (Z.gcd m k) n = 1.
Proof.
  intros a m k n Hn.
  remember (Z.to_nat k) as t eqn:Ht.
  revert m k Ht.
  induction t as [t IH] using (well_founded_induction lt_wf).
  intros m k Ht Hm Hk Hannm Hannk.
  destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
  - subst k. rewrite Z.gcd_0_r, Z.abs_eq by lia. exact Hannm.
  - assert (0 < k) by lia.
    assert (Z.gcd m k = Z.gcd k (m mod k)) as Hgcd.
    { rewrite (Z.gcd_comm m k).
      rewrite <- (Z.gcd_mod m k) by lia.
      apply Z.gcd_comm. }
    rewrite Hgcd.
    assert (0 <= m mod k < k) as Hbound by (apply Z.mod_pos_bound; lia).
    assert (Z.to_nat (m mod k) < t)%nat as Hlt.
    { subst t. apply Z2Nat.inj_lt; lia. }
    assert (powm a (m mod k) n = 1) as Hmod.
    { pose proof (Z.div_mod m k ltac:(lia)) as Hdm.
      assert (0 <= m / k) by (apply Z.div_pos; lia).
      rewrite Hdm in Hannm.
      rewrite powm_add_r in Hannm by lia.
      rewrite powm_mul_r in Hannm by lia.
      rewrite Hannk in Hannm.
      rewrite powm_1_pow in Hannm by lia.
      rewrite Z.mod_1_l in Hannm by lia.
      rewrite Z.mul_1_l in Hannm.
      unfold powm in Hannm |- *.
      rewrite Z.mod_mod in Hannm by lia.
      exact Hannm. }
    apply (IH (Z.to_nat (m mod k)) Hlt k (m mod k) eq_refl);
      [lia | lia | exact Hannk | exact Hmod].
Qed.

Lemma pratt_gcd_ok_not_one_mod_factor :
  forall p g qs r q,
    1 < p ->
    1 < r ->
    Z.divide r p ->
    pratt_gcd_ok p g qs ->
    In q qs ->
    powm g ((p - 1) / q) r <> 1.
Proof.
  intros p g qs r q Hp Hr Hrp Hgcd Hin Heq.
  set (e := (p - 1) / q) in *.
  assert (Z.divide r (g ^ e - 1)) as Hrge.
  { apply Z.mod_divide; [lia|].
    unfold powm in Heq.
    rewrite Zminus_mod, Heq, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity. }
  assert (Z.divide p (g ^ e - g ^ e mod p)) as Hpred.
  { apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Z.mod_mod, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity. }
  assert (Z.divide r (g ^ e - g ^ e mod p)) as Hrpred.
  { apply (Z.divide_trans r p (g ^ e - g ^ e mod p)); [exact Hrp | exact Hpred]. }
  assert (Z.divide r (powm g e p - 1)) as Hrpwm.
  { unfold powm.
    pose proof (Z.divide_sub_r _ _ _ Hrge Hrpred) as Hsub.
    replace (g ^ e - 1 - (g ^ e - g ^ e mod p)) with (g ^ e mod p - 1) in Hsub by ring.
    exact Hsub. }
  assert (Z.divide r (Z.gcd (powm g e p - 1) p)) as Hrgcd.
  { apply Z.gcd_greatest; [exact Hrpwm | exact Hrp]. }
  specialize (Hgcd q Hin).
  fold e in Hgcd.
  rewrite Hgcd in Hrgcd.
  apply Z.divide_1_r in Hrgcd. lia.
Qed.

Theorem pratt_verified_implies_prime :
  forall p g qs,
    1 < p ->
    pratt_generator_ok p g qs ->
    pratt_gcd_ok p g qs ->
    pratt_factors_ok p qs ->
    (forall q, In q qs -> Z.prime q) ->
    Z.prime p.
Proof.
  intros p g qs Hp [Hfermat _] Hgcd Hfact Hall.
  destruct (exists_prime_divisor p Hp) as [r [Hr Hrp]].
  pose proof (Z.prime_ge_2 r Hr) as Hrge2.
  assert (Z.coprime g p) as Hcop by (apply pratt_coprime_of_fermat; [lia | exact Hfermat]).
  assert (Z.coprime g r) as Hcopr by (apply (coprime_of_divisor g p r Hcop Hrp)).
  assert (powm g (r - 1) r = 1) as Hfr.
  { apply fermat_coprime; [exact Hr | exact Hcopr]. }
  assert (powm g (p - 1) r = 1) as Hfp.
  { apply (powm_one_of_divisor g (p - 1) p r); [lia | lia | lia | exact Hrp | exact Hfermat]. }
  set (d := Z.gcd (p - 1) (r - 1)).
  assert (powm g d r = 1) as Hd1.
  { apply powm_gcd_exp; [lia | lia | lia | exact Hfp | exact Hfr]. }
  assert (Z.divide d (p - 1)) as Hdp by apply Z.gcd_divide_l.
  assert (Z.divide d (r - 1)) as Hdr by apply Z.gcd_divide_r.
  assert (0 < d) as Hdpos.
  { pose proof (Z.gcd_nonneg (p - 1) (r - 1)) as Hnn.
    destruct (Z.eq_dec d 0) as [Hz | Hnz].
    - unfold d in Hz. apply Z.gcd_eq_0_l in Hz. lia.
    - lia. }
  assert (d = p - 1) as Hdeq.
  { destruct (Z.eq_dec d (p - 1)) as [E | Ne]; [exact E|].
    exfalso.
    assert (d < p - 1) as Hdlt.
    { pose proof (divide_le_pos d (p - 1) Hdpos ltac:(lia) Hdp). lia. }
    set (m := (p - 1) / d).
    assert (p - 1 = d * m) as Hsplit.
    { unfold m. destruct Hdp as [k Hk].
      rewrite Hk, (Z.div_mul k d) by lia. apply Z.mul_comm. }
    assert (1 < m) as Hmgt.
    { unfold m in Hsplit. nia. }
    destruct (exists_prime_divisor m Hmgt) as [q [Hq Hqm]].
    pose proof (Z.prime_ge_2 q Hq) as Hqge2.
    assert (Z.divide q (p - 1)) as Hqp.
    { destruct Hqm as [u Hu].
      rewrite Hsplit, Hu. exists (d * u). ring. }
    pose proof (pratt_factors_cover_prime p qs q Hfact Hall Hq Hqp) as Hin.
    assert (Z.divide d ((p - 1) / q)) as Hdq.
    { destruct Hqm as [u Hu].
      exists u.
      unfold m in Hsplit, Hu.
      rewrite Hsplit, Hu.
      replace (d * (u * q)) with (u * d * q) by ring.
      rewrite Z.div_mul by lia. reflexivity. }
    assert (powm g ((p - 1) / q) r = 1) as Hone.
    { assert (0 <= (p - 1) / q) by (apply Z.div_pos; lia).
      apply (powm_one_of_multiple g d ((p - 1) / q) r);
        [lia | lia | lia | exact Hd1 | exact Hdq]. }
    apply (pratt_gcd_ok_not_one_mod_factor p g qs r q Hp ltac:(lia) Hrp Hgcd Hin Hone). }
  rewrite Hdeq in Hdr.
  pose proof (divide_le_pos (p - 1) (r - 1) ltac:(lia) ltac:(lia) Hdr) as Hple.
  pose proof (divide_le_pos r p ltac:(lia) ltac:(lia) Hrp) as Hrle.
  assert (r = p) by lia.
  subst r. exact Hr.
Qed.

Theorem pratt_inhabit_of_certs :
  forall p qs,
    2 < p ->
    (forall q, In q qs -> pratt q) ->
    inhabited (pratt p).
Proof.
  intros p qs Hp Hqs. constructor.
  exact (pratt_of_factor_certs p 0 qs Hp Hqs).
Qed.

Theorem pratt_verifier :
  forall p g qs,
    2 < p ->
    pratt_generator_ok p g qs ->
    pratt_gcd_ok p g qs ->
    pratt_factors_ok p qs ->
    (forall q, In q qs -> Z.prime q) ->
    (forall q, In q qs -> pratt q) ->
    inhabited (pratt p) /\ Z.prime p.
Proof.
  intros p g qs Hp Hgen Hgcd Hfact Hprime Hcerts.
  split.
  - apply (pratt_inhabit_of_certs p qs Hp Hcerts).
  - apply (pratt_verified_implies_prime p g qs); [lia | exact Hgen | exact Hgcd | exact Hfact | exact Hprime].
Qed.

Theorem pratt_11_sound : Z.prime 11.
Proof.
  apply (pratt_verified_implies_prime 11 2 [2; 5]);
    [lia | apply pratt_generator_ok_11 | apply pratt_gcd_ok_11 |
     apply pratt_factors_ok_11 | apply pratt_qs_prime_11].
Qed.

Theorem pratt_31_sound : Z.prime 31.
Proof.
  apply (pratt_verified_implies_prime 31 3 [2; 3; 5]);
    [lia | apply pratt_generator_ok_31 | apply pratt_gcd_ok_31 |
     apply pratt_factors_ok_31 | apply pratt_qs_prime_31].
Qed.
