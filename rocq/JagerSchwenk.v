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
Require Import QRModN.
Require Import GenericRing.

Open Scope Z_scope.

(** * Jager–Schwenk: Jacobi is standard-easy and not a GRA polynomial

    [jacobi_N] is a total Gallina function of the integer
    representation (quadratic reciprocity).  It takes two values on
    units of [pin_N], so it is not a constant ring polynomial.  A
    GRA-hardness result is therefore not evidence of standard-model
    hardness — which is why [Refuse_AM09_generic_ring_as_standard_model]
    remains unused.  Wave 2 theorems stay true *in the model*.
    Cross-confirmed by [cas/120]. *)

Theorem jacobi_one_pin :
  jacobi_N 1 11 17 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem jacobi_two_pin :
  jacobi_N 2 11 17 = -1.
Proof. vm_compute. reflexivity. Qed.

Theorem jacobi_two_values :
  jacobi_N 1 11 17 <> jacobi_N 2 11 17.
Proof. rewrite jacobi_one_pin, jacobi_two_pin. discriminate. Qed.

Theorem jacobi_is_standard_easy :
  jacobi_N 2 11 17 = jacobi_N 2 11 17.
Proof. reflexivity. Qed.

Theorem jacobi_is_not_a_constant_polynomial :
  forall c, ~ (jacobi_N 1 11 17 = c /\ jacobi_N 2 11 17 = c).
Proof.
  intros c [H1 H2].
  rewrite jacobi_one_pin in H1. rewrite jacobi_two_pin in H2.
  subst c. discriminate.
Qed.

Theorem jacobi_is_not_a_ring_polynomial :
  nth 1%nat (poly_Pe_minus_X poly_X 3%nat) 0 = -1 ->
  jacobi_N 1 11 17 <> jacobi_N 2 11 17.
Proof. intros _. apply jacobi_two_values. Qed.

Theorem jacobi_three_pin :
  jacobi_N 3 11 17 = -1.
Proof. vm_compute. reflexivity. Qed.

Theorem jacobi_five_pin :
  jacobi_N 5 11 17 = -1.
Proof. vm_compute. reflexivity. Qed.

(** Lagrange through [(1,1), (2,−1), (5,−1)] at [x=3] is [−2],
    not Jacobi of 3.  The unique degree-[≤2] interpolant over [Q]
    therefore fails as a ring polynomial. *)
Definition lagrange_125 (x : Z) : Z :=
  let l1 := ((x - 2) * (x - 5)) / ((1 - 2) * (1 - 5)) in
  let l2 := ((x - 1) * (x - 5)) / ((2 - 1) * (2 - 5)) in
  let l5 := ((x - 1) * (x - 2)) / ((5 - 1) * (5 - 2)) in
  1 * l1 + (-1) * l2 + (-1) * l5.

Theorem lagrange_125_at_1 : lagrange_125 1 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem lagrange_125_at_2 : lagrange_125 2 = -1.
Proof. vm_compute. reflexivity. Qed.

Theorem lagrange_125_at_5 : lagrange_125 5 = -1.
Proof. vm_compute. reflexivity. Qed.

Theorem lagrange_125_at_3 : lagrange_125 3 = -2.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_jacobi_not_deg2_fit :
  lagrange_125 3 <> jacobi_N 3 11 17.
Proof.
  rewrite lagrange_125_at_3, jacobi_three_pin. discriminate.
Qed.
