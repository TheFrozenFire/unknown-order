From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import Hardness.
Require Import BinForms.
Require Import ClassGroupWall.
Require Import Presentation.

Open Scope Z_scope.

(** * Proof of exponentiation, algebra only

    Wesolowski: a correct [π] is an [ℓ]-th root of [x^{q·ℓ}].
    Pietrzak at [T = 2]: a midpoint [μ] with [μ² = x⁴] is a square
    root of [y]; the quotient [μ / x²] squares to 1 (low-order, not
    adaptive root).  On [Cl(Δ)] that 2-torsion may be constructible.

    Sequentiality, random oracles, and "this is a VDF" stay named.
    Cross-confirmed by [cas/24_exp_proof.gp]. *)

Definition wesolowski_verify_rsa (N x y pi ell r : Z) : Prop :=
  (powm pi ell N * powm x r N) mod N = y mod N.

Theorem wesolowski_correct_is_root :
  forall N x q ell r,
    1 < N ->
    0 <= q ->
    0 < ell ->
    0 <= r ->
    let y := powm x (q * ell + r) N in
    let pi := powm x q N in
    powm pi ell N = powm x (q * ell) N /\
    wesolowski_verify_rsa N x y pi ell r.
Proof.
  intros N x q ell r Hn Hq He Hr y pi.
  subst y pi.
  split.
  - rewrite <- powm_mul_r by lia. rewrite Z.mul_comm. reflexivity.
  - unfold wesolowski_verify_rsa.
    rewrite <- powm_mul_r by lia.
    rewrite (Z.mul_comm q ell).
    rewrite <- powm_add_r by lia.
    unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem wesolowski_pi_is_ell_th_root :
  forall N x q ell,
    1 < N ->
    0 <= q ->
    0 < ell ->
    P_Root (rsa_presentation N) (Z.to_nat ell)
      (powm x (q * ell) N) (powm x q N).
Proof.
  intros N x q ell Hn Hq He.
  unfold P_Root, rsa_presentation. simpl.
  split; [lia|].
  rewrite Z2Nat.id by lia.
  rewrite <- powm_mul_r by lia.
  rewrite Z.mul_comm.
  unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(** Pietrzak at [T = 2]: [μ² = x⁴].  Then [μ] is a square root of
    [y = x⁴], and [μ² / (x²)² = 1]. *)
Theorem pietrzak_mid_squares_to_y :
  forall N x mu,
    1 < N ->
    powm mu 2 N = powm x 4 N ->
    powm mu 2 N = powm (powm x 2 N) 2 N.
Proof.
  intros N x mu Hn H.
  rewrite H. change 4 with (2 * 2). rewrite powm_square by lia. reflexivity.
Qed.

Theorem pietrzak_y_is_fourth_power :
  forall N x,
    1 < N ->
    0 <= x ->
    powm x 4 N = powm (powm x 2 N) 2 N.
Proof. intros. change 4 with (2 * 2). rewrite powm_square by lia. reflexivity. Qed.

(** A square root of 1 is either constructible [{±1}] or a mixed
    CRT root.  The latter is the Rabin split, not a Pietrzak
    *restricted* break. *)
Theorem pietrzak_forgery_is_low_order_shape :
  forall N mu,
    1 < N ->
    powm mu 2 N = 1 ->
    1 < mu < N ->
    rsa_constructible_2torsion N mu \/
    ~ rsa_constructible_2torsion N mu.
Proof.
  intros N mu Hn Hsq Hrng.
  destruct (Z.eq_dec (mu mod N) 1) as [H1 | Hn1].
  - left. unfold rsa_constructible_2torsion. left. exact H1.
  - destruct (Z.eq_dec (mu mod N) (N - 1)) as [Hm | Hnm].
    + left. unfold rsa_constructible_2torsion. right. exact Hm.
    + right. unfold rsa_constructible_2torsion. intros [Ha | Hb]; contradiction.
Qed.

Theorem pietrzak_on_Cl_may_be_constructible :
  forall f, bqf_ambiguous f -> bqf_equiv f (bqf_inv f).
Proof. apply ambiguous_equiv_inv. Qed.

Theorem pietrzak_restricted_ignores_Cl2 :
  forall D B f,
    bqf_ambiguous f ->
    ~ P_LowOrderOutside (cl_presentation D) B f 2%nat.
Proof. apply cl_restricted_excludes_ambiguous. Qed.
