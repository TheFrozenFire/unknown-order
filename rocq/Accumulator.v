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
