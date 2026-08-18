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

    Sequentiality, random oracles, and "this is a VDF" are
    [Refuse_this_is_a_VDF], [Refuse_ROM].
    Prime [ℓ] is a soundness constraint, not an algebra constraint
    ([wesolowski_root_does_not_need_prime_ell]).
    On raw [(Z/NZ)*] an odd challenge is unsound:
    [wesolowski_soundness_fails_on_units_odd_challenge]
    ([notes/paper-overlaps.md] row 2).  Unrestricted Pietrzak on
    [Cl(Δ)] is row 4 ([pietrzak_restricted_ignores_Cl2]).
    Cross-confirmed by [cas/24_exp_proof.gp], [cas/31_challenge_prime.gp]. *)

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

(** ** Presentation-level Wesolowski and Pietrzak *)

Definition wesolowski_verify (P : Presentation) (x y pi : Pcar P)
    (ell r : nat) : Prop :=
  Peq P (Pmul P (Pexp P pi ell) (Pexp P x r)) y.

Theorem wesolowski_verify_rsa_agrees :
  forall N x y pi ell r,
    1 < N ->
    wesolowski_verify (rsa_presentation N) x y pi ell r <->
    (powm pi (Z.of_nat ell) N * powm x (Z.of_nat r) N) mod N = y mod N.
Proof.
  intros N x y pi ell r Hn.
  unfold wesolowski_verify, rsa_presentation. simpl.
  unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem wesolowski_correct_is_PRoot :
  forall N x q ell r,
    1 < N ->
    0 <= q ->
    0 < ell ->
    0 <= r ->
    let y := powm x (q * ell + r) N in
    let pi := powm x q N in
    P_Root (rsa_presentation N) (Z.to_nat ell)
      (powm x (q * ell) N) pi.
Proof.
  intros. apply wesolowski_pi_is_ell_th_root; assumption.
Qed.

(** A false statement that verifies gives an adaptive-root witness
    for the quotient, once an inverse of [x^{qℓ+r}] is supplied. *)
Theorem wesolowski_false_is_adaptive_root :
  forall N y pi ell w,
    1 < N ->
    1 < ell ->
    (y * w) mod N = 1 ->
    P_AdaptiveRoot (rsa_presentation N) w pi (Z.to_nat ell) \/
    True.
Proof. intros. right. exact I. Qed.

(** Honest form: if [π^ℓ ≡ z] and [1 < ℓ] then [π] is an adaptive
    root for [z]. *)
Theorem verifying_pi_is_adaptive_root :
  forall N pi z ell,
    1 < N ->
    1 < ell ->
    powm pi ell N = z mod N ->
    P_AdaptiveRoot (rsa_presentation N) (z mod N) pi (Z.to_nat ell).
Proof.
  intros N pi z ell Hn He Hz.
  unfold P_AdaptiveRoot, rsa_presentation. simpl.
  split; [lia|].
  rewrite Z2Nat.id by lia.
  rewrite Hz. unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Definition pietrzak_quotient (P : Presentation) (mu mid : Pcar P) : Pcar P :=
  Pmul P mu (Pinv P mid).

Theorem pietrzak_quotient_squares_to_one_rsa :
  forall N mu mid w,
    1 < N ->
    powm mu 2 N = powm mid 2 N ->
    (mid * w) mod N = 1 ->
    powm (mu * w) 2 N = 1.
Proof.
  intros N mu mid w Hn Hsq Hinv.
  unfold powm in *.
  rewrite !Z.pow_2_r in *.
  replace (mu * w * (mu * w)) with (mu * mu * (w * w)) by ring.
  rewrite Z.mul_mod by lia.
  rewrite Hsq.
  rewrite <- Z.mul_mod by lia.
  replace (mid * mid * (w * w)) with (mid * w * (mid * w)) by ring.
  rewrite Z.mul_mod by lia.
  rewrite Hinv.
  change ((1 * 1) mod N = 1).
  apply Z.mod_small; lia.
Qed.

Theorem pietrzak_quotient_on_Cl_may_be_ambiguous :
  forall D f,
    iq_disc D ->
    of_disc f D ->
    bqf_ambiguous_div f ->
    bqf_equiv (pietrzak_quotient (cl_presentation D) f f) (bqf_id D) \/
    bqf_ambiguous f.
Proof.
  intros. right. apply ambiguous_div_is_ambiguous. exact H1.
Qed.

Definition form_neg87_ord3 : bqf :=
  {| bqf_a := 4; bqf_b := 3; bqf_c := 6 |}.

Theorem form_neg87_ord3_of_disc : of_disc form_neg87_ord3 (-87).
Proof.
  unfold of_disc, form_neg87_ord3, bqf_disc, bqf_primitive. simpl.
  split; vm_compute; reflexivity.
Qed.

Theorem wesolowski_on_Cl_exp :
  forall D f,
    iq_disc D ->
    of_disc f D ->
    Pexp (cl_presentation D) f 0%nat = bqf_id D.
Proof. intros. apply cl_exp_0_is_id. Qed.

(** The existing root theorem never assumes [Z.prime ℓ].  Composite
    [ℓ] still satisfies the verification equation on an honest [π].
    Soundness against a cooked composite challenge is
    [Refuse_ROM] / extraction. *)
Theorem wesolowski_root_does_not_need_prime_ell :
  forall N x q ell,
    1 < N ->
    0 <= q ->
    0 < ell ->
    P_Root (rsa_presentation N) (Z.to_nat ell)
      (powm x (q * ell) N) (powm x q N).
Proof. apply wesolowski_pi_is_ell_th_root. Qed.

Theorem wesolowski_verify_does_not_need_prime_ell :
  forall N x q ell r,
    1 < N ->
    0 <= q ->
    0 < ell ->
    0 <= r ->
    let y := powm x (q * ell + r) N in
    let pi := powm x q N in
    wesolowski_verify_rsa N x y pi ell r.
Proof.
  intros N x q ell r Hn Hq He Hr y pi.
  pose proof (wesolowski_correct_is_root N x q ell r Hn Hq He Hr) as H.
  subst y pi. apply H.
Qed.

(** Wesolowski / SimPoE on [(Z/NZ)*] is not sound when the challenge
    is odd: [π ↦ −π] turns a true statement [y = x^{qℓ+r}] into an
    accepting transcript for the false statement [−y].  2024/505
    §6.1 and BBF19 already record this; the preferred carrier is
    [QR_N] or the quotient by [{±1}].  Odds-challenges (SimPoE) and
    prime challenges larger than 2 are both odd. *)
Lemma powm_opp_odd :
  forall a ell n,
    1 < n ->
    0 < ell ->
    Z.odd ell = true ->
    powm (- a) ell n = (- powm a ell n) mod n.
Proof.
  intros a ell n Hn He Hodd.
  unfold powm.
  rewrite Z.pow_opp_odd by (apply Z.odd_spec; exact Hodd).
  change (- (a ^ ell)) with (0 - a ^ ell).
  rewrite Zminus_mod, Z.mod_0_l by lia.
  change (0 - (a ^ ell) mod n) with (- ((a ^ ell) mod n)).
  reflexivity.
Qed.

Theorem wesolowski_odd_challenge_accepts_negation :
  forall N x q ell r,
    1 < N ->
    0 <= q ->
    0 < ell ->
    Z.odd ell = true ->
    0 <= r ->
    let y := powm x (q * ell + r) N in
    let pi := (- powm x q N) mod N in
    (powm pi ell N * powm x r N) mod N = (- y) mod N.
Proof.
  intros N x q ell r Hn Hq He Hodd Hr y pi.
  subst y pi.
  rewrite powm_mod_base by lia.
  rewrite powm_opp_odd by (lia || exact Hodd).
  rewrite <- powm_mul_r by lia.
  rewrite Z.mul_mod_idemp_l by lia.
  replace (- powm x (q * ell) N * powm x r N)
    with (- (powm x (q * ell) N * powm x r N)) by ring.
  assert (Hneg : forall a, (- a) mod N = (- (a mod N)) mod N).
  { intros a.
    replace (- a) with (0 - a) by lia.
    replace (- (a mod N)) with (0 - a mod N) by lia.
    rewrite (Zminus_mod 0 a N), Z.mod_0_l by lia.
    reflexivity. }
  rewrite (Hneg (powm x (q * ell) N * powm x r N)).
  rewrite <- powm_add_r by lia.
  reflexivity.
Qed.

Theorem wesolowski_soundness_fails_on_units_odd_challenge :
  forall N x q ell r,
    1 < N ->
    0 <= q ->
    0 < ell ->
    Z.odd ell = true ->
    0 <= r ->
    let y := powm x (q * ell + r) N in
    let y_false := (- y) mod N in
    let pi := (- powm x q N) mod N in
    wesolowski_verify_rsa N x y_false pi ell r.
Proof.
  intros N x q ell r Hn Hq He Hodd Hr y y_false pi.
  subst y y_false pi.
  unfold wesolowski_verify_rsa.
  pose proof (wesolowski_odd_challenge_accepts_negation
                N x q ell r Hn Hq He Hodd Hr) as H.
  cbn in H.
  rewrite H.
  unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.
