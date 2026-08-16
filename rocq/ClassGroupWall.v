From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import Hardness.
Require Import Cyclotomic.

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
