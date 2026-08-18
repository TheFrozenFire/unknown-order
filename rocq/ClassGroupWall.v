From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import Hardness.
Require Import Cyclotomic.
Require Import BinForms.

Open Scope Z_scope.

(** * The wall between Type B and adaptive root

    Adaptive root and strong RSA are the *same relation*
    ([adaptive_root_is_strong_RSA]).  On [(Z/NZ)*] the relation is
    trivialized by [λ]: [(y, λ+1)] is a witness.  Type B is how a
    factor of [λ] (or of [p±1], or of [Φ_n(p)]) becomes public
    without [d].

    That leak uses the *presentation* [N = pq].  A class group of
    an imaginary quadratic order is given by a discriminant, not
    by a modulus whose factorization is [λ].  There is no lemma
    [discriminant_to_lambda], and this file does not invent one.

    So Type B and adaptive root stop being aliases: they share a
    winning condition and differ by whether the group presents a
    period.  Not an axiom that class groups are hard.

    Restricted low-order after excluding [Cl[2]] is still won on
    the Mersenne discriminant [Δ = −31] by [(2,1,4)] (order 3):
    [mersenne31_wins_restricted_LowOrder].  Paper-check:
    [notes/paper-overlaps.md] row 5.  CAS [40]. *)

Theorem adaptive_root_trivial_from_lambda :
  forall p q y,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime y (p * q) ->
    let N := p * q in
    let lam := lambda_semiprime p q in
    Problem_AdaptiveRoot N (y mod N) (y mod N) (lam + 1).
Proof.
  intros p q y Hp Hq Hneq Hcop N lam.
  unfold Problem_AdaptiveRoot, N, lam.
  apply lambda_solves_strong_RSA; assumption.
Qed.

Theorem typeB_pminus1_is_cyc1 :
  forall p M, cyc_handle (cyc1 p) M <-> 0 <= M /\ (p - 1 | M).
Proof. intros. apply cyc1_handle_is_p1. Qed.

Theorem typeB_pplus1_is_cyc2 :
  forall p M, cyc_handle (cyc2 p) M <-> 0 <= M /\ (p + 1 | M).
Proof. intros. apply cyc2_handle_is_williams. Qed.

(** A Type-B handle is a period that divides a public [M].  It is
    a fact about a *modular* presentation. *)
Definition modular_presentation (N p q : Z) : Prop :=
  N = p * q /\ Z.prime p /\ Z.prime q /\ p <> q.

Definition typeB_period (p period : Z) : Prop :=
  period = p - 1 \/ period = p + 1 \/ period = cyc3 p \/
  period = cyc4 p \/ period = cyc6 p.

Definition typeB_leak (N p q period M : Z) : Prop :=
  modular_presentation N p q /\
  typeB_period p period /\
  cyc_handle period M.

Theorem typeB_leak_needs_modulus :
  forall N p q period M,
    typeB_leak N p q period M ->
    N = p * q.
Proof. intros N p q period M [[HN _] _]. exact HN. Qed.

(** An imaginary-quadratic discriminant is a *different*
    presentation.  No map from [D] to a [typeB_leak] is defined. *)
Definition iq_discriminant (D : Z) : Prop :=
  D < 0 /\ (D mod 4 = 0 \/ D mod 4 = 1).

Theorem iq_disc_agrees :
  forall D, iq_discriminant D <-> iq_disc D.
Proof. intros D. unfold iq_discriminant, iq_disc. reflexivity. Qed.

(** ** Restricted low-order

    On [(Z/NZ)*], [H = {±1}].  On [Cl(Δ)], [H] is the constructible
    2-torsion (ambiguous forms).  Unrestricted [Problem_LowOrder]
    is won on [Cl] by those forms; the restricted problem is not. *)

Definition rsa_constructible_2torsion (N a : Z) : Prop :=
  a mod N = 1 \/ a mod N = N - 1.

Definition Problem_LowOrderOutside (N B : Z) (H : Z -> Prop) (a k : Z) : Prop :=
  Problem_LowOrder N B a k /\ ~ H a.

Definition cl_constructible_2torsion (D : Z) (f : bqf) : Prop :=
  of_disc f D /\ bqf_ambiguous f.

Definition Problem_LowOrderOutside_Cl (D B : Z) (f : bqf) : Prop :=
  Problem_LowOrder_Cl D B f /\ ~ cl_constructible_2torsion D f.

Theorem rsa_minus1_is_constructible :
  forall N, 1 < N -> rsa_constructible_2torsion N (N - 1).
Proof. intros N HN. unfold rsa_constructible_2torsion. right. rewrite Z.mod_small; lia. Qed.

Theorem unrestricted_LowOrder_won_by_Cl2 :
  Problem_LowOrder_Cl (-87) 2 form_neg87_amb.
Proof. pose proof catalog_wins_LowOrder_B2 as H. destruct H as [H _]. exact H. Qed.

Theorem restricted_LowOrder_excludes_Cl2 :
  forall D B f,
    cl_constructible_2torsion D f ->
    ~ Problem_LowOrderOutside_Cl D B f.
Proof.
  intros D B f Hcon [Hlo Hout]. exact (Hout Hcon).
Qed.

Theorem catalog_ambiguous_is_constructible :
  cl_constructible_2torsion (-87) form_neg87_amb /\
  cl_constructible_2torsion (-403) form_neg403_amb_red /\
  cl_constructible_2torsion (-455) form_neg455_5.
Proof.
  unfold cl_constructible_2torsion.
  split; [|split].
  - split; [apply form_neg87_amb_of_disc | apply form_neg87_amb_is_ambiguous].
  - split; [apply form_neg403_amb_red_of_disc | apply form_neg403_amb_red_is_ambiguous].
  - split; [apply form_neg455_5_of_disc | apply form_neg455_5_is_ambiguous].
Qed.

(** The 2-annihilator is public on [Cl(Δ)]: every ambiguous form
    is equivalent to its inverse.  There is no odd annihilator
    constructed from [D] — no [discriminant_to_lambda], and no
    analogue of [λ+1].  The constructor is absent; this is not
    [~exists]. *)

Definition public_2_annihilator : Z := 2.

Theorem public_2_annihilator_hits_ambiguous :
  forall f, bqf_ambiguous f -> bqf_equiv f (bqf_inv f).
Proof. apply ambiguous_equiv_inv. Qed.

Definition no_discriminant_to_lambda : unit := tt.

Theorem disc_mod1_is_odd :
  forall D, D mod 4 = 1 -> Z.odd D = true.
Proof.
  intros D H.
  pose proof (Z.div_mod D 4 ltac:(lia)) as Hdm.
  rewrite H in Hdm.
  apply Z.odd_spec. exists (2 * (D / 4)). lia.
Qed.

(** Adaptive root keeps the same *relation* on a different carrier.
    [lambda_solves_strong_RSA] has no analogue: there is no public
    odd [e] built from [D] that sends every class to itself. *)
Theorem adaptive_root_relation_is_presentation_blind :
  forall N y x e,
    Problem_AdaptiveRoot N y x e <-> Problem_StrongRSA N y x e.
Proof. intros. apply adaptive_root_is_strong_RSA. Qed.

(** ** Restricted low-order after excluding [Cl[2]]

    [Problem_LowOrder_Cl] is the unrestricted [B = 2] win by
    ambiguous forms.  Protocols assume the complementary cell:
    a class of small *odd* order that is not constructible
    2-torsion.  2020/1310 (Shanks): on the Mersenne discriminant
    [Δ = 1 − 2^p] the form [(2, 1, 2^{p−3})] has order 3.
    Here [p = 5], [Δ = −31], form [(2, 1, 4)].  CAS [40]. *)

Definition form_neg31_ord3 : bqf :=
  {| bqf_a := 2; bqf_b := 1; bqf_c := 4 |}.

Definition form_neg31_sq : bqf :=
  {| bqf_a := 4; bqf_b := 1; bqf_c := 2 |}.

Definition form_neg31_cube : bqf :=
  {| bqf_a := 8; bqf_b := 1; bqf_c := 1 |}.

Theorem iq_neg31 : iq_disc (-31).
Proof. unfold iq_disc. split; [lia|]. right. vm_compute. reflexivity. Qed.

Theorem form_neg31_ord3_of_disc : of_disc form_neg31_ord3 (-31).
Proof.
  unfold of_disc, form_neg31_ord3, bqf_disc, bqf_primitive.
  simpl. split; vm_compute; reflexivity.
Qed.

Theorem form_neg31_ord3_reduced : bqf_reduced form_neg31_ord3.
Proof. unfold bqf_reduced, form_neg31_ord3. simpl. split; [lia | intros; lia]. Qed.

Theorem form_neg31_ord3_not_ambiguous : ~ bqf_ambiguous form_neg31_ord3.
Proof.
  unfold bqf_ambiguous, form_neg31_ord3. simpl. intros [H|[H|[H|H]]]; lia.
Qed.

Theorem form_neg31_ord3_not_principal :
  ~ bqf_equiv form_neg31_ord3 (bqf_id (-31)).
Proof.
  apply reduced_a_gt_1_not_principal.
  - apply form_neg31_ord3_of_disc.
  - apply form_neg31_ord3_reduced.
  - unfold form_neg31_ord3. simpl. lia.
Qed.

Theorem form_neg31_sq_compute :
  bqf_compose form_neg31_ord3 form_neg31_ord3 = form_neg31_sq.
Proof. vm_compute. reflexivity. Qed.

Theorem form_neg31_cube_compute :
  bqf_compose form_neg31_sq form_neg31_ord3 = form_neg31_cube.
Proof. vm_compute. reflexivity. Qed.

Theorem form_neg31_exp2 :
  bqf_exp (-31) form_neg31_ord3 2%nat = form_neg31_sq.
Proof.
  rewrite bqf_exp_2; [| apply iq_neg31 | apply form_neg31_ord3_of_disc].
  apply form_neg31_sq_compute.
Qed.

Theorem form_neg31_exp3 :
  bqf_exp (-31) form_neg31_ord3 3%nat = form_neg31_cube.
Proof.
  cbn [bqf_exp].
  rewrite compose_id_left; [| apply iq_neg31 | apply form_neg31_ord3_of_disc].
  rewrite form_neg31_sq_compute.
  apply form_neg31_cube_compute.
Qed.

Theorem form_neg31_sq_equiv_inv :
  bqf_equiv form_neg31_sq (bqf_inv form_neg31_ord3).
Proof.
  exists sl2_S. split; [apply sl2_S_ok|].
  vm_compute. reflexivity.
Qed.

Theorem form_neg31_inv_reduced : bqf_reduced (bqf_inv form_neg31_ord3).
Proof. unfold bqf_reduced, bqf_inv, form_neg31_ord3. simpl. split; [lia | intros; lia]. Qed.

Theorem form_neg31_inv_of_disc : of_disc (bqf_inv form_neg31_ord3) (-31).
Proof.
  unfold of_disc. split.
  - rewrite bqf_inv_disc. apply form_neg31_ord3_of_disc.
  - apply bqf_inv_primitive. apply form_neg31_ord3_of_disc.
Qed.

Theorem form_neg31_inv_not_principal :
  ~ bqf_equiv (bqf_inv form_neg31_ord3) (bqf_id (-31)).
Proof.
  apply reduced_a_gt_1_not_principal.
  - apply form_neg31_inv_of_disc.
  - apply form_neg31_inv_reduced.
  - unfold bqf_inv, form_neg31_ord3. simpl. lia.
Qed.

Theorem form_neg31_actS_inv_is_sq :
  bqf_act sl2_S (bqf_inv form_neg31_ord3) = form_neg31_sq.
Proof. vm_compute. reflexivity. Qed.

Theorem form_neg31_sq_not_principal :
  ~ bqf_equiv form_neg31_sq (bqf_id (-31)).
Proof.
  intros [m [Hok Hact]].
  apply form_neg31_inv_not_principal.
  exists (sl2_mul sl2_S m).
  split; [apply sl2_mul_ok; [apply sl2_S_ok | exact Hok]|].
  rewrite <- bqf_act_mul, form_neg31_actS_inv_is_sq.
  exact Hact.
Qed.

Definition sl2_reduce_cube : sl2 :=
  {| sl2_a := 0; sl2_b := -1; sl2_c := 1; sl2_d := 1 |}.

Theorem sl2_reduce_cube_ok : sl2_ok sl2_reduce_cube.
Proof. unfold sl2_ok, sl2_reduce_cube, sl2_det. cbn. lia. Qed.

Theorem form_neg31_cube_equiv_id :
  bqf_equiv form_neg31_cube (bqf_id (-31)).
Proof.
  exists sl2_reduce_cube. split; [apply sl2_reduce_cube_ok|].
  vm_compute. reflexivity.
Qed.

Theorem form_neg31_exp3_equiv_id :
  bqf_equiv (bqf_exp (-31) form_neg31_ord3 3%nat) (bqf_id (-31)).
Proof. rewrite form_neg31_exp3. apply form_neg31_cube_equiv_id. Qed.

Theorem form_neg31_exp1 :
  bqf_exp (-31) form_neg31_ord3 1%nat = form_neg31_ord3.
Proof. apply bqf_exp_1; [apply iq_neg31 | apply form_neg31_ord3_of_disc]. Qed.

(** Restricted low-order: small odd order, not constructible 2-torsion.
    This is the cell [P_LowOrderOutside] on [cl_presentation] after
    excluding [Cl[2]].  The old [Problem_LowOrder_Cl] is only the
    unrestricted [B = 2] win by ambiguous forms. *)
Definition Problem_LowOrderRestricted_Cl
    (D B : Z) (f : bqf) (k : nat) : Prop :=
  of_disc f D /\
  ~ bqf_ambiguous f /\
  ~ bqf_equiv f (bqf_id D) /\
  bqf_equiv (bqf_exp D f k) (bqf_id D) /\
  (forall k', (0 < k' < k)%nat ->
     ~ bqf_equiv (bqf_exp D f k') (bqf_id D)) /\
  (1 < k)%nat /\
  Z.of_nat k <= B.

Theorem mersenne31_wins_restricted_LowOrder :
  Problem_LowOrderRestricted_Cl (-31) 3 form_neg31_ord3 3%nat.
Proof.
  unfold Problem_LowOrderRestricted_Cl.
  split; [apply form_neg31_ord3_of_disc|].
  split; [apply form_neg31_ord3_not_ambiguous|].
  split; [apply form_neg31_ord3_not_principal|].
  split; [apply form_neg31_exp3_equiv_id|].
  split.
  - intros k' Hk'.
    assert (k' = 1%nat \/ k' = 2%nat) as Hkcs by lia.
    destruct Hkcs as [Hk1 | Hk2].
    + subst k'. rewrite form_neg31_exp1. apply form_neg31_ord3_not_principal.
    + subst k'. rewrite form_neg31_exp2. apply form_neg31_sq_not_principal.
  - split; [lia|lia].
Qed.

Theorem mersenne31_is_odd_order :
  (3 > 1)%nat /\ Z.odd 3 = true.
Proof. split; [lia|]. reflexivity. Qed.

(** ** Families: constructible torsion is not always [Cl[2]]

    An ordinary class-group family has [H =] ambiguous forms.
    A Mersenne / Shanks family ([D = 4u³ − 1], form [(u,1,u²)])
    also constructs the order-3 class.  2020/1310 is that family,
    not a break of ordinary [Cl(Δ)]. *)

Definition shanks_form (u : Z) : bqf :=
  {| bqf_a := u; bqf_b := 1; bqf_c := u * u |}.

Definition shanks_disc (u : Z) : Z := 1 - 4 * (u * u * u).

Theorem shanks_disc_2 : shanks_disc 2 = -31.
Proof. vm_compute. reflexivity. Qed.

Theorem shanks_form_2 : shanks_form 2 = form_neg31_ord3.
Proof. reflexivity. Qed.

Definition cl_ordinary_H : bqf -> Prop := bqf_ambiguous.

Definition cl_mersenne_H (u : Z) (f : bqf) : Prop :=
  bqf_ambiguous f \/
  bqf_equiv f (shanks_form u) \/
  bqf_equiv f (bqf_inv (shanks_form u)).

Theorem mersenne31_shanks_in_family_H :
  cl_mersenne_H 2 form_neg31_ord3.
Proof.
  unfold cl_mersenne_H. rewrite shanks_form_2. right. left.
  apply bqf_equiv_refl.
Qed.

Theorem mersenne31_shanks_not_ordinary_H :
  ~ cl_ordinary_H form_neg31_ord3.
Proof. apply form_neg31_ord3_not_ambiguous. Qed.

(** ** Class number is an AR-search trapdoor

    On units, [λ] annihilates and [(y, λ+1)] wins Strong RSA.
    On [Cl(−31)], [h = 3] annihilates the three classes; [2] is
    invertible mod [3], so each non-identity class is a square.
    The general implication [y^h ≡ 1 ⇒ y^{h+1} ≡ y] on unreduced
    representatives is [compose_left_compat_named] (unused refuse).
    CAS [41]. *)

Theorem bqf_exp_id :
  forall D k,
    iq_disc D ->
    bqf_exp D (bqf_id D) k = bqf_id D.
Proof.
  intros D k Hiq. induction k as [|k IH].
  - reflexivity.
  - simpl. rewrite IH. apply compose_id_left; [exact Hiq|].
    apply bqf_id_of_disc. exact Hiq.
Qed.

Theorem neg31_id_annihilated_by_h :
  bqf_exp (-31) (bqf_id (-31)) 3%nat = bqf_id (-31).
Proof. apply bqf_exp_id. apply iq_neg31. Qed.

Definition form_neg31_inv_sq : bqf :=
  {| bqf_a := 4; bqf_b := -1; bqf_c := 2 |}.

Theorem form_neg31_inv_exp2 :
  bqf_exp (-31) (bqf_inv form_neg31_ord3) 2%nat = form_neg31_inv_sq.
Proof.
  rewrite bqf_exp_2; [| apply iq_neg31 | apply form_neg31_inv_of_disc].
  vm_compute. reflexivity.
Qed.

Theorem form_neg31_inv_sq_equiv_f :
  bqf_equiv form_neg31_inv_sq form_neg31_ord3.
Proof.
  exists sl2_S. split; [apply sl2_S_ok|].
  vm_compute. reflexivity.
Qed.

Theorem shanks_inv_square_is_shanks :
  bqf_equiv
    (bqf_exp (-31) (bqf_inv form_neg31_ord3) 2%nat)
    form_neg31_ord3.
Proof.
  rewrite form_neg31_inv_exp2. apply form_neg31_inv_sq_equiv_f.
Qed.

Theorem shanks_annihilated_by_h :
  bqf_equiv (bqf_exp (-31) form_neg31_ord3 3%nat) (bqf_id (-31)).
Proof. apply form_neg31_exp3_equiv_id. Qed.
