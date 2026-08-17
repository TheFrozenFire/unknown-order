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
    period.  Not an axiom that class groups are hard. *)

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
