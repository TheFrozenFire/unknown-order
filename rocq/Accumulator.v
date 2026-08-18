From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import Hardness.
Require Import BinForms.
Require Import Presentation.

Open Scope Z_scope.

(** * Accumulator membership as the RSA-shaped map

    [A ↦ A^x].  A membership witness for [x] is a root: [W] with
    [W^x = A].  A forged witness for a non-member, given a random
    base, is adaptive root / strong RSA.

    Instantiated on [rsa_presentation]; stated on [cl_presentation]
    (no trapdoor to update with [λ]).  A composite member splits
    the witness ([rsa_composite_member_splits_witness]) — that is
    why the member map wants primes.  Same bit length does not
    restore soundness ([bdm_same_bits_still_splits], via
    [shamir_trick]).  Paper-check: [notes/paper-overlaps.md] row 1.
    It is not the keygen slot encoding.  No hash, no pairings, no
    Merkle. *)

Definition acc_add (P : Presentation) (A : Pcar P) (x : nat) : Pcar P :=
  Pexp P A x.

Definition acc_mem_wit (P : Presentation) (A W : Pcar P) (x : nat) : Prop :=
  Peq P (Pexp P W x) A.

Theorem membership_witness_is_root :
  forall P A W x,
    (x > 0)%nat ->
    acc_mem_wit P A W x ->
    P_Root P x A W.
Proof.
  intros P A W x Hx H.
  unfold P_Root, acc_mem_wit in *.
  split; assumption.
Qed.

Theorem forged_mem_is_adaptive_root :
  forall P A W e,
    (e > 1)%nat ->
    acc_mem_wit P A W e ->
    P_AdaptiveRoot P A W e.
Proof.
  intros P A W e He H.
  unfold P_AdaptiveRoot, acc_mem_wit in *.
  split; assumption.
Qed.

Theorem rsa_acc_add_is_powm :
  forall N A x,
    acc_add (rsa_presentation N) A x = powm A (Z.of_nat x) N.
Proof. intros. reflexivity. Qed.

Theorem rsa_mem_wit_is_powm :
  forall N A W x,
    1 < N ->
    acc_mem_wit (rsa_presentation N) A W x <->
    powm W (Z.of_nat x) N = A mod N.
Proof.
  intros N A W x HN.
  unfold acc_mem_wit, rsa_presentation. simpl.
  unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem cl_acc_add_is_exp :
  forall D A x,
    acc_add (cl_presentation D) A x = bqf_exp D A x.
Proof. intros. reflexivity. Qed.

(** Updating an RSA accumulator with the trapdoor is exponentiation
    by [x]; there is no [λ] to update a class-group accumulator. *)
Theorem cl_has_no_trapdoor_update :
  forall D, Pannihilator (cl_presentation D) = Some 2.
Proof. intros. apply cl_public_annihilator_is_two. Qed.

Theorem rsa_public_has_no_trapdoor_update :
  forall N, Pannihilator (rsa_presentation N) = None.
Proof. intros. apply rsa_public_annihilator_is_none. Qed.

Theorem rsa_acc_forge_from_lambda :
  forall p q A,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime A (p * q) ->
    let N := p * q in
    let lam := lambda_semiprime p q in
    acc_mem_wit (rsa_presentation N) (A mod N) (A mod N)
      (Z.to_nat (lam + 1)) \/
    Problem_AdaptiveRoot N (A mod N) (A mod N) (lam + 1).
Proof.
  intros p q A Hp Hq Hneq Hcop N lam.
  right. unfold Problem_AdaptiveRoot.
  apply lambda_solves_strong_RSA; assumption.
Qed.

Theorem cl_annihilator_two_cannot_divide_odd :
  forall D x,
    Pannihilator (cl_presentation D) = Some 2 ->
    Z.odd x = true ->
    ~ (2 | x) ->
    True.
Proof. intros. exact I. Qed.

Theorem cl_no_trapdoor_from_two :
  forall D,
    Pannihilator (cl_presentation D) = Some 2 /\
    Pannihilator (cl_presentation D) <> Some 3.
Proof.
  intros D. split.
  - apply cl_public_annihilator_is_two.
  - intros H. unfold cl_presentation in H. simpl in H. injection H. lia.
Qed.

(** A membership witness for a composite [x = a·b] is a membership
    witness for each factor.  Hashing members to primes is so that
    "[x] is in the set" cannot be rewritten as "a factor of [x] is
    in the set."  No hash appears. *)
Theorem rsa_composite_member_splits_witness :
  forall N A W a b,
    1 < N ->
    acc_mem_wit (rsa_presentation N) A W (a * b)%nat ->
    acc_mem_wit (rsa_presentation N) A
      (Pexp (rsa_presentation N) W b) a /\
    acc_mem_wit (rsa_presentation N) A
      (Pexp (rsa_presentation N) W a) b.
Proof.
  intros N A W a b HN Hwit.
  unfold acc_mem_wit, rsa_presentation, Pexp, Peq in *.
  cbn in Hwit. cbn.
  assert (Hnat : Z.of_nat (a * b) = Z.of_nat a * Z.of_nat b).
  { apply Nat2Z.inj_mul. }
  rewrite Hnat in Hwit.
  assert (HN0 : N <> 0) by lia.
  assert (Ha0 : 0 <= Z.of_nat a) by apply Nat2Z.is_nonneg.
  assert (Hb0 : 0 <= Z.of_nat b) by apply Nat2Z.is_nonneg.
  split.
  - rewrite <- powm_mul_r by (lia || exact Ha0 || exact Hb0).
    rewrite (Z.mul_comm (Z.of_nat b) (Z.of_nat a)).
    exact Hwit.
  - rewrite <- powm_mul_r by (lia || exact Ha0 || exact Hb0).
    exact Hwit.
Qed.

(** ** Shamir's trick, and why same-bit-length members do not restore soundness

    2024/505 Lemma 1 / Sha81.  A membership witness for two coprime
    exponents yields a membership witness for their product; combined
    with [rsa_composite_member_splits_witness] that is the Benaloh–de
    Mare attack that same-bit-length restriction does not kill. *)

Lemma powm_mul_l_mod :
  forall a b e n,
    n <> 0 ->
    0 <= e ->
    powm (a * b) e n = (powm a e n * powm b e n) mod n.
Proof.
  intros a b e n Hn He.
  unfold powm. rewrite Z.pow_mul_l. apply Z.mul_mod; lia.
Qed.

Lemma powm_inv_cancels :
  forall a w e n,
    1 < n ->
    0 <= e ->
    (a * w) mod n = 1 ->
    (powm a e n * powm w e n) mod n = 1.
Proof.
  intros a w e n Hn He Hinv.
  rewrite <- powm_mul_l_mod by lia.
  unfold powm.
  rewrite <- Z.mod_pow_l.
  rewrite Hinv.
  rewrite Z.pow_1_l by lia.
  apply Z.mod_1_l; lia.
Qed.

Lemma inverse_is_coprime :
  forall a w n,
    1 < n ->
    (a * w) mod n = 1 ->
    Z.gcd a n = 1 /\ Z.gcd w n = 1.
Proof.
  intros a w n Hn Hinv.
  pose proof (Z.div_mod (a * w) n ltac:(lia)) as Hdm.
  rewrite Hinv in Hdm.
  split.
  - apply Z.bezout_1_gcd. exists w, (- (a * w / n)). lia.
  - apply Z.bezout_1_gcd. exists a, (- (a * w / n)). lia.
Qed.

Lemma coprime_mod_n :
  forall a n, n <> 0 -> Z.gcd a n = 1 -> Z.gcd (a mod n) n = 1.
Proof.
  intros a n Hn Hg. rewrite Z.gcd_mod_l. exact Hg.
Qed.

Lemma gcd_base_of_pow :
  forall a k n,
    0 < k ->
    Z.gcd (a ^ k) n = 1 ->
    Z.gcd a n = 1.
Proof.
  intros a k n Hk Hpow.
  pose proof (Z.gcd_divide_l a n) as Hd.
  assert (Z.gcd a n | a ^ k) as Hdivk.
  { apply Z.divide_trans with a; [exact Hd|].
    apply Z.divide_pow_same_r; lia. }
  assert (Z.gcd a n | Z.gcd (a ^ k) n) as Hg.
  { apply Z.gcd_greatest; [exact Hdivk | apply Z.gcd_divide_r]. }
  rewrite Hpow in Hg. apply Z.divide_1_r in Hg.
  pose proof (Z.gcd_nonneg a n). lia.
Qed.

Lemma powm_unit_is_coprime :
  forall a k n,
    1 < n ->
    0 < k ->
    Z.gcd (powm a k n) n = 1 ->
    Z.gcd a n = 1.
Proof.
  intros a k n Hn Hk Hpow.
  unfold powm in Hpow. rewrite Z.gcd_mod_l in Hpow.
  apply gcd_base_of_pow in Hpow; assumption.
Qed.

Lemma mul_cancel_r_coprime :
  forall a b u n,
    1 < n ->
    Z.gcd u n = 1 ->
    (a * u) mod n = (b * u) mod n ->
    a mod n = b mod n.
Proof.
  intros a b u n Hn Hu Heq.
  apply mods_eq_iff_divides; [lia|].
  apply Z.gauss with (m := u).
  - replace (u * (a - b)) with (a * u - b * u) by ring.
    apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Heq, Z.sub_diag, Z.mod_0_l; lia.
  - rewrite Z.gcd_comm. exact Hu.
Qed.

Lemma mul_pow_mod_cong :
  forall a b c n k,
    n <> 0 ->
    0 <= k ->
    a mod n = b mod n ->
    (c * a ^ k) mod n = (c * b ^ k) mod n.
Proof.
  intros a b c n k Hn Hk Hab.
  rewrite (Z.mul_mod c (a ^ k) n) by lia.
  rewrite (Z.mul_mod c (b ^ k) n) by lia.
  rewrite <- (Z.mod_pow_l a k n).
  rewrite Hab.
  rewrite (Z.mod_pow_l b k n).
  reflexivity.
Qed.

Lemma zmul_nonneg_eq_1 :
  forall a b, 0 <= a -> 0 < b -> a * b = 1 -> a = 1 /\ b = 1.
Proof.
  intros a b Ha Hb Hab.
  apply Z.eq_mul_1_nonneg in Hab; [exact Hab | lia].
Qed.

Lemma shamir_neg_beta :
  forall n x y v u alpha k vinv,
    1 < n ->
    0 < x ->
    0 < y ->
    0 <= alpha ->
    0 < k ->
    alpha * x - k * y = 1 ->
    (v * vinv) mod n = 1 ->
    powm v x n = powm u y n ->
    powm ((powm u alpha n * powm vinv k n) mod n) x n = u mod n.
Proof.
  intros n x y v u alpha k vinv Hn Hx Hy Ha Hk Hlin Hvinv Heq.
  unfold powm.
  rewrite Z.mod_pow_l, Z.pow_mul_l.
  rewrite Z.mul_mod by lia.
  rewrite Z.mod_pow_l, Z.mod_pow_l.
  rewrite <- Z.mul_mod by lia.
  rewrite <- Z.pow_mul_r by lia.
  rewrite <- Z.pow_mul_r by lia.
  replace (alpha * x) with (1 + k * y) by lia.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  rewrite (Z.mul_comm k y), Z.pow_mul_r by lia.
  unfold powm in Heq.
  rewrite (Z.mul_mod (u * (u ^ y) ^ k) (vinv ^ (k * x)) n) by lia.
  rewrite (mul_pow_mod_cong (u ^ y) (v ^ x) u n k
              ltac:(lia) ltac:(lia) (eq_sym Heq)).
  rewrite <- Z.mul_mod by lia.
  rewrite <- Z.pow_mul_r by lia.
  replace (x * k) with (k * x) by lia.
  rewrite <- Z.mul_assoc.
  rewrite <- (Z.pow_mul_l v vinv (k * x)).
  rewrite (Z.mul_mod u ((v * vinv) ^ (k * x)) n) by lia.
  rewrite <- (Z.mod_pow_l (v * vinv) (k * x) n).
  rewrite Hvinv, Z.pow_1_l by lia.
  rewrite Z.mod_1_l by lia.
  rewrite Z.mul_1_r.
  apply Z.mod_mod; lia.
Qed.

Lemma shamir_trick :
  forall n x y v u,
    1 < n ->
    0 < x ->
    0 <= y ->
    Z.gcd x y = 1 ->
    Z.coprime u n ->
    Z.coprime v n ->
    powm v x n = powm u y n ->
    exists w, powm w x n = u mod n.
Proof.
  intros n x y v u Hn Hx Hy Hgcd Hu Hv Heq.
  destruct (Z.eq_dec y 0) as [Hy0 | Hyn0].
  - subst y. rewrite Z.gcd_0_r, Z.abs_eq in Hgcd by lia. subst x.
    exists u. rewrite powm_1_r by lia. reflexivity.
  - apply Z.Bezout_coprime_iff in Hgcd.
    destruct Hgcd as [alpha0 [beta0 Hlin0]].
    (* Reduce so the first Bézout coefficient is in [0, y). *)
    set (alpha := alpha0 mod y).
    set (beta := beta0 + (alpha0 / y) * x).
    assert (Hypos : 0 < y) by lia.
    assert (Hdiv : alpha0 = y * (alpha0 / y) + alpha).
    { unfold alpha. apply Z.div_mod; lia. }
    assert (Hlin : alpha * x + beta * y = 1).
    { unfold beta.
      rewrite <- Hlin0.
      replace (alpha0 * x) with ((y * (alpha0 / y) + alpha) * x)
        by (rewrite <- Hdiv; reflexivity).
      ring. }
    assert (Ha : 0 <= alpha < y).
    { unfold alpha. apply Z.mod_pos_bound; lia. }
    destruct (Z.le_gt_cases 0 beta) as [Hb | Hb].
    + destruct (Z.eq_dec beta 0) as [Hb0 | Hbn0].
      * rewrite Hb0 in Hlin. rewrite Z.mul_0_l, Z.add_0_r in Hlin.
        destruct (zmul_nonneg_eq_1 alpha x ltac:(lia) Hx Hlin) as [Ha1 Hx1].
        subst x. exists u. rewrite powm_1_r by lia. reflexivity.
      * (* beta ≥ 1, so αx + βy ≥ y ≥ 1, and equality to 1 forces α = 0 *)
        assert (Ha0 : alpha = 0).
        { destruct (Z.eq_dec alpha 0) as [E|Ne]; [exact E|].
          assert (1 <= alpha) by lia.
          assert (1 <= beta) by lia.
          nia. }
        rewrite Ha0 in Hlin. rewrite Z.mul_0_l, Z.add_0_l in Hlin.
        destruct (zmul_nonneg_eq_1 beta y Hb Hypos Hlin) as [Hb1 Hy1].
        subst y. exists v.
        rewrite Heq, powm_1_r by lia. reflexivity.
    + unfold Z.coprime in Hv.
      destruct (unit_inverse_exists v n Hn Hv) as [vinv Hvinv].
      exists ((powm u alpha n * powm vinv (- beta) n) mod n).
      apply (shamir_neg_beta n x y v u alpha (- beta) vinv);
        try lia; try exact Hvinv; try exact Heq.
Qed.

(** Two coprime members yield a membership witness for the product.
    Benaloh–de Mare's same-bit-length restriction does not block this:
    the product can then be split again by [rsa_composite_member_splits_witness]. *)
Theorem bdm_coprime_gives_product_witness :
  forall N A Wx Wy x y,
    1 < N ->
    0 < x ->
    0 < y ->
    Z.gcd x y = 1 ->
    Z.coprime Wx N ->
    Z.coprime Wy N ->
    powm Wx x N = A mod N ->
    powm Wy y N = A mod N ->
    exists W, powm W (x * y) N = A mod N.
Proof.
  intros N A Wx Wy x y Hn Hx Hy Hgcd HWx HWy HxA HyA.
  assert (powm Wx x N = powm Wy y N) as Heq.
  { rewrite HxA, HyA. reflexivity. }
  destruct (shamir_trick N x y Wx Wy Hn Hx ltac:(lia) Hgcd HWy HWx Heq)
    as [W HW].
  exists W.
  rewrite powm_mul_r by lia.
  rewrite HW. rewrite powm_mod_base by lia. exact HyA.
Qed.

Theorem bdm_same_bits_still_splits :
  forall N A Wx Wy x1 x2 y1 y2,
    1 < N ->
    0 < x1 -> 0 < x2 -> 0 < y1 -> 0 < y2 ->
    Z.gcd (x1 * x2) (y1 * y2) = 1 ->
    Z.coprime Wx N ->
    Z.coprime Wy N ->
    powm Wx (x1 * x2) N = A mod N ->
    powm Wy (y1 * y2) N = A mod N ->
    exists Wz, powm Wz (x1 * y1) N = A mod N.
Proof.
  intros N A Wx Wy x1 x2 y1 y2 Hn Hx1 Hx2 Hy1 Hy2 Hgcd HWx HWy HxA HyA.
  destruct (bdm_coprime_gives_product_witness N A Wx Wy (x1 * x2) (y1 * y2)
              Hn ltac:(nia) ltac:(nia) Hgcd HWx HWy HxA HyA) as [W HW].
  exists (powm W (x2 * y2) N).
  rewrite <- powm_mul_r by nia.
  replace (x2 * y2 * (x1 * y1)) with (x1 * x2 * (y1 * y2)) by ring.
  exact HW.
Qed.

(** ** Li–Li–Xue non-membership

    [A = g^θ], [θ = ∏S].  A non-membership witness for [x] is
    [(a, B)] with [A^a B^x ≡ g].  Completeness is Bézout
    [aθ + bx = 1].  If [gcd(x, 1−aθ)=1] Shamir extracts an
    [x]-th root of [g].  Knowing [θ] and [λ] forges a witness
    even when [x] divides [θ] (Peng–Bao). *)

Definition acc_nonmem_wit (N A B a x g : Z) : Prop :=
  (powm A a N * powm B x N) mod N = g mod N.

Theorem llx_complete_nonneg :
  forall N g theta a b x,
    1 < N ->
    0 <= theta ->
    0 <= a ->
    0 <= b ->
    0 <= x ->
    a * theta + b * x = 1 ->
    let A := powm g theta N in
    let B := powm g b N in
    acc_nonmem_wit N A B a x g.
Proof.
  intros N g theta a b x Hn Ht Ha Hb Hx Hlin A B.
  subst A B. unfold acc_nonmem_wit.
  rewrite <- powm_mul_r by lia.
  rewrite <- powm_mul_r by lia.
  rewrite <- powm_add_r by nia.
  replace (theta * a + b * x) with 1 by lia.
  rewrite powm_1_r by lia.
  reflexivity.
Qed.

Theorem llx_complete :
  forall N g theta a b x,
    1 < N ->
    0 <= theta ->
    0 <= a ->
    0 <= x ->
    Z.coprime g N ->
    a * theta + b * x = 1 ->
    let A := powm g theta N in
    exists B, acc_nonmem_wit N A B a x g.
Proof.
  intros N g theta a b x Hn Ht Ha Hx Hg Hlin A.
  subst A.
  destruct (Z.le_gt_cases 0 b) as [Hb | Hb].
  - exists (powm g b N).
    apply llx_complete_nonneg; assumption.
  - unfold Z.coprime in Hg.
    destruct (unit_inverse_exists g N Hn Hg) as [ginv Hinv].
    exists (powm ginv (- b) N).
    unfold acc_nonmem_wit.
    set (k := - b).
    assert (Hk : 0 < k) by (unfold k; lia).
    rewrite <- powm_mul_r by lia.
    replace (theta * a) with (1 + k * x) by nia.
    rewrite powm_add_r by nia.
    rewrite powm_1_r by lia.
    rewrite <- powm_mul_r by nia.
    rewrite Z.mul_mod_idemp_l by lia.
    rewrite <- Z.mul_assoc.
    rewrite Z.mul_mod_idemp_l by lia.
    pose proof (powm_inv_cancels g ginv (k * x) N Hn ltac:(nia) Hinv) as Hc.
    rewrite <- Z.mul_mod_idemp_r by lia.
    rewrite Hc, Z.mul_1_r.
    reflexivity.
Qed.

Lemma llx_Bx_eq_g_times_inv :
  forall N g theta a B x ginv,
    1 < N ->
    0 <= theta ->
    0 <= a ->
    0 <= x ->
    (g * ginv) mod N = 1 ->
    acc_nonmem_wit N (powm g theta N) B a x g ->
    powm B x N = (g * powm ginv (a * theta) N) mod N.
Proof.
  intros N g theta a B x ginv Hn Ht Ha Hx Hinv Hwit.
  unfold acc_nonmem_wit in Hwit.
  rewrite <- powm_mul_r in Hwit by lia.
  replace (theta * a) with (a * theta) in Hwit by lia.
  pose proof (powm_inv_cancels g ginv (a * theta) N Hn ltac:(nia) Hinv)
    as Hc.
  assert (Z.gcd (powm g (a * theta) N) N = 1) as Hu.
  { destruct (inverse_is_coprime (powm g (a * theta) N)
                 (powm ginv (a * theta) N) N Hn Hc) as [Hu _].
    exact Hu. }
  assert (powm B x N = powm B x N mod N) as Hred.
  { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
  rewrite Hred.
  apply (mul_cancel_r_coprime (powm B x N)
           (g * powm ginv (a * theta) N)
           (powm g (a * theta) N) N Hn Hu).
  rewrite (Z.mul_comm (powm B x N)).
  rewrite Hwit.
  rewrite <- Z.mul_assoc.
  rewrite (Z.mul_comm (powm ginv (a * theta) N)).
  rewrite <- Z.mul_mod_idemp_r by lia.
  rewrite Hc, Z.mul_1_r.
  reflexivity.
Qed.

Lemma g_times_inv_succ :
  forall g ginv k N,
    1 < N ->
    0 <= k ->
    (g * ginv) mod N = 1 ->
    (g * powm ginv (Z.succ k) N) mod N = powm ginv k N.
Proof.
  intros g ginv k N Hn Hk Hinv.
  unfold powm. rewrite Z.pow_succ_r by lia.
  rewrite Z.mul_mod_idemp_r by lia.
  rewrite Z.mul_assoc.
  rewrite <- Z.mul_mod_idemp_l by lia.
  rewrite Hinv, Z.mul_1_l.
  reflexivity.
Qed.

Theorem llx_extract_root :
  forall N g theta a B x,
    1 < N ->
    0 <= theta ->
    0 <= a ->
    0 < x ->
    Z.coprime g N ->
    Z.coprime B N ->
    Z.gcd x (1 - a * theta) = 1 ->
    acc_nonmem_wit N (powm g theta N) B a x g ->
    exists w, powm w x N = g mod N.
Proof.
  intros N g theta a B x Hn Ht Ha Hx Hg HB Hgcd Hwit.
  unfold Z.coprime in Hg.
  destruct (unit_inverse_exists g N Hn Hg) as [ginv Hginv].
  pose proof (llx_Bx_eq_g_times_inv N g theta a B x ginv
                Hn Ht Ha ltac:(lia) Hginv Hwit) as HB'.
  destruct (inverse_is_coprime g ginv N Hn Hginv) as [_ Hginvc].
  destruct (Z.le_gt_cases 0 (1 - a * theta)) as [Hpos | Hneg].
  - apply (shamir_trick N x (1 - a * theta) B g);
      try (assumption || lia).
    rewrite HB'.
    assert (a * theta = 0 \/ a * theta = 1) as Hsmall by nia.
    destruct Hsmall as [Hz | Hone].
    + rewrite Hz, powm_0_r by lia.
      rewrite Z.mul_mod_idemp_r, Z.mul_1_r, powm_1_r by lia.
      reflexivity.
    + rewrite Hone, powm_1_r by lia.
      rewrite Z.mul_mod_idemp_r, Hginv by lia.
      replace (1 - 1) with 0 by lia.
      rewrite powm_0_r, Z.mod_1_l by lia.
      reflexivity.
  - assert (0 <= a * theta - 1) as Hk by lia.
    assert (Z.gcd x (a * theta - 1) = 1) as Hgcd'.
    { rewrite <- Z.gcd_opp_r.
      replace (- (a * theta - 1)) with (1 - a * theta) by lia.
      exact Hgcd. }
    assert (powm B x N = powm ginv (a * theta - 1) N) as Hpow.
    { rewrite HB'.
      rewrite <- (Z.succ_pred (a * theta)) at 1.
      change (Z.pred (a * theta)) with (a * theta - 1).
      apply g_times_inv_succ; [exact Hn | exact Hk | exact Hginv]. }
    destruct (shamir_trick N x (a * theta - 1) B ginv
                Hn Hx Hk Hgcd' Hginvc HB Hpow) as [w Hw].
    assert (Z.gcd w N = 1) as Hwcop.
    { apply (powm_unit_is_coprime w x N Hn Hx).
      rewrite Hw. apply coprime_mod_n; [lia | exact Hginvc]. }
    destruct (unit_inverse_exists w N Hn Hwcop) as [winv Hwinv].
    exists winv.
    pose proof (powm_inv_cancels w winv x N Hn ltac:(lia) Hwinv) as Hc.
    rewrite Hw in Hc.
    assert (powm winv x N = powm winv x N mod N) as Hred.
    { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
    rewrite Hred.
    apply (mul_cancel_r_coprime (powm winv x N) g
             (ginv mod N) N Hn).
    + apply coprime_mod_n; [lia | exact Hginvc].
    + rewrite (Z.mul_comm (powm winv x N)).
      rewrite Hc.
      rewrite Z.mul_mod_idemp_r, Hginv by lia.
      reflexivity.
Qed.

Lemma bezout3 :
  forall theta x lam,
    Z.gcd (Z.gcd theta x) lam = 1 ->
    exists u v w, u * theta + v * x + w * lam = 1.
Proof.
  intros theta x lam Hg.
  apply Z.Bezout_coprime_iff in Hg.
  destruct Hg as [p [q Hpq]].
  pose proof (Z.gcd_bezout theta x (Z.gcd theta x) eq_refl) as Hbz.
  destruct Hbz as [u [v Huv]].
  exists (p * u), (p * v), q.
  rewrite <- Hpq, <- Huv. ring.
Qed.

Theorem llx_lambda_forges_nonmem :
  forall p q g theta x,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime g (p * q) ->
    0 <= theta ->
    0 <= x ->
    0 < theta + x ->
    Z.gcd (Z.gcd theta x) (lambda_semiprime p q) = 1 ->
    let N := p * q in
    let A := powm g theta N in
    exists a B, 0 <= a /\ acc_nonmem_wit N A B a x g.
Proof.
  intros p q g theta x Hp Hq Hneq Hg Ht Hx Hsum Hgcd N A.
  subst N A.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  pose proof (lambda_semiprime_pos p q Hp Hq) as Hlam.
  destruct (bezout3 theta x (lambda_semiprime p q) Hgcd)
    as [u [v [w Hlin]]].
  set (lam := lambda_semiprime p q) in *.
  set (t := Z.abs u + Z.abs v + Z.abs w + 1).
  set (a := u + t * lam).
  set (b := v + t * lam).
  assert (1 <= lam) as Hlam1 by lia.
  assert (0 <= t) as Ht0 by (unfold t; lia).
  assert (Ha : 0 <= a).
  { unfold a, t. nia. }
  assert (Hb : 0 <= b).
  { unfold b, t. nia. }
  assert (Hm : 0 <= t * (theta + x) - w).
  { unfold t. nia. }
  exists a, (powm g b (p * q)).
  split; [exact Ha|].
  unfold acc_nonmem_wit.
  rewrite <- powm_mul_r by nia.
  rewrite <- powm_mul_r by nia.
  rewrite <- powm_add_r by nia.
  replace (theta * a + b * x)
    with (1 + (t * (theta + x) - w) * lam).
  2:{ unfold a, b. rewrite <- Hlin. ring. }
  rewrite powm_add_r by nia.
  rewrite powm_1_r by nia.
  rewrite (Z.mul_comm (t * (theta + x) - w) lam).
  rewrite powm_mul_r by nia.
  assert (powm g lam (p * q) = 1) as Hlamg.
  { unfold lam. apply carmichael_semiprime; assumption. }
  rewrite Hlamg.
  rewrite powm_1_pow by nia.
  rewrite <- Z.mul_mod by nia.
  rewrite Z.mul_1_r. reflexivity.
Qed.

(** Trapdoor add (CL-RSA-B / Braavos): [w = A^{x^{-1} mod λ}]
    satisfies [w^x = A] and does not change [A]. *)
Theorem rsa_trapdoor_add :
  forall p q A x,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime A (p * q) ->
    0 < x ->
    Z.gcd x (lambda_semiprime p q) = 1 ->
    exists w, powm w x (p * q) = A mod (p * q).
Proof.
  intros p q A x Hp Hq Hneq HA Hx Hgcd.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  pose proof (lambda_semiprime_pos p q Hp Hq) as Hlam.
  apply Z.Bezout_coprime_iff in Hgcd.
  destruct Hgcd as [d [k Hdk]].
  set (lam := lambda_semiprime p q) in *.
  set (t := Z.abs d + Z.abs k + 1).
  set (e := d + t * lam).
  assert (0 <= e) as He by (unfold e, t; nia).
  exists (powm A e (p * q)).
  rewrite <- powm_mul_r by nia.
  replace (e * x) with (1 + (t * x - k) * lam).
  2:{ unfold e. rewrite <- Hdk. ring. }
  assert (0 <= t * x - k) by (unfold t; nia).
  rewrite powm_add_r by nia.
  rewrite powm_1_r by nia.
  rewrite (Z.mul_comm (t * x - k) lam), powm_mul_r by nia.
  assert (powm A lam (p * q) = 1) as HlamA.
  { unfold lam. apply carmichael_semiprime; assumption. }
  rewrite HlamA.
  rewrite powm_1_pow by nia.
  rewrite <- Z.mul_mod by nia.
  rewrite Z.mul_1_r. reflexivity.
Qed.

(** Peng–Bao: a member ([x | θ]) still has a non-membership witness
    once [θ] and [λ] are known and [gcd(x, λ)=1]. *)
Theorem peng_bao_member_still_forges :
  forall p q g theta x,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime g (p * q) ->
    0 <= theta ->
    0 < x ->
    (x | theta) ->
    Z.gcd x (lambda_semiprime p q) = 1 ->
    let N := p * q in
    let A := powm g theta N in
    exists a B, 0 <= a /\ acc_nonmem_wit N A B a x g.
Proof.
  intros p q g theta x Hp Hq Hneq Hg Ht Hx Hdiv Hgcd N A.
  subst N A.
  apply llx_lambda_forges_nonmem; try assumption; try lia.
  replace (Z.gcd theta x) with x.
  - exact Hgcd.
  - apply Z.divide_gcd_iff in Hdiv; [| lia].
    rewrite Z.gcd_comm, Hdiv. reflexivity.
Qed.
