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
Require Import StrongRSAPeel.
Require Import GenericRing.

Open Scope Z_scope.

(** * Residual GRA dichotomy

    A generic-ring algorithm that writes a *residual-shaped*
    Strong-RSA witness (odd [e], [gcd(e,λ)=1], [λ] ndiv [e−1])
    either gcd-leaks a proper factor of [N] or is forbidden by a
    degree / leading-coefficient identity.  [e = λ+1] fails those
    residual tests, so [GConst (λ+1)] solving Strong RSA on every
    unit without splitting is not a counterexample.  A constant
    leftover root that inverts one pin [y] and misses another unit
    is not a GRA of every unit.

    Generic-ring inroad on [residual_solver_constructs_factor_open_named],
    not a proof of that unrestricted name, and not RSA ≡ or ≢
    factoring.  Cross-confirmed by [cas/146]. *)

(** ** Residual-shaped exponents *)

Definition residual_shaped_e (e lam : Z) : Prop :=
  1 < e /\
  Z.Odd e /\
  Z.gcd e lam = 1 /\
  ~ (lam | e - 1).

Theorem residual_shaped_e_3 :
  residual_shaped_e 3 80.
Proof.
  unfold residual_shaped_e.
  split; [lia|].
  split; [exists 1; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem residual_shaped_e_7 :
  residual_shaped_e 7 80.
Proof.
  unfold residual_shaped_e.
  split; [lia|].
  split; [exists 3; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

(** ** [λ+1] is outside the residual class *)

Theorem not_residual_shaped_e_81 :
  ~ residual_shaped_e 81 80.
Proof.
  unfold residual_shaped_e.
  intros [_ [_ [_ Hnd]]].
  apply Hnd. exists 1. reflexivity.
Qed.

Theorem lambda_plus_one_witness_not_residual :
  forall y,
    ~ srsa_residual_leaf 187 80 y y 81.
Proof.
  intros y [_ [_ [_ [_ Hnd]]]].
  apply Hnd. exists 1. lia.
Qed.

Theorem residual_gra_const81_independent_of_y :
  gra_eval_Z [GConst 81] 36 3%nat = 81 /\
  gra_eval_Z [GConst 81] 8 3%nat = 81.
Proof. apply gra_const_81. Qed.

Theorem residual_gra_const81_gcd_is_1 :
  Z.gcd 81 187 = 1.
Proof. apply gra_const_81_does_not_factor. Qed.

Theorem residual_gra_const81_solves_sRSA_not_residual :
  forall y,
    Z.coprime y 187 ->
    Problem_StrongRSA 187 (y mod 187) (y mod 187) 81 /\
    ~ srsa_residual_leaf 187 80 (y mod 187) (y mod 187) 81.
Proof.
  intros y Hcop. split.
  - apply gra_const_lambda_plus_one_solves_sRSA_without_factoring. exact Hcop.
  - apply lambda_plus_one_witness_not_residual.
Qed.

(** ** Constant leftover inverts one [y], not every unit *)

Theorem residual_gra_const42_inverts_pin_not_8 :
  gra_eval_Z [GConst 42] 36 3%nat = 42 /\
  powm 42 3 187 = 36 /\
  Z.coprime 8 187 /\
  powm 42 3 187 <> 8.
Proof.
  split; [apply gra_const42|].
  split; [apply gra_nodiv_const42_inverts_36|].
  split; [vm_compute; reflexivity|].
  apply gra_nodiv_const42_fails_on_8.
Qed.

Theorem residual_gra_const42_misses_unit_2 :
  Z.coprime 2 187 /\
  powm 42 3 187 <> 2.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

(** ** Degree / leading-coefficient fork for residual-shaped [e] *)

Theorem residual_shaped_forbids_rational_Pe_XQe :
  forall e lam dp dq,
    residual_shaped_e e lam ->
    e * dp <> 1 + e * dq.
Proof.
  intros e lam dp dq [He _].
  apply rational_Pe_minus_XQe_leading. exact He.
Qed.

Theorem residual_shaped_e3_leading :
  forall dp dq, 3 * dp <> 1 + 3 * dq.
Proof.
  intros dp dq.
  apply (residual_shaped_forbids_rational_Pe_XQe 3 80 dp dq).
  apply residual_shaped_e_3.
Qed.

Theorem residual_shaped_e7_leading :
  forall dp dq, 7 * dp <> 1 + 7 * dq.
Proof.
  intros dp dq.
  apply (residual_shaped_forbids_rational_Pe_XQe 7 80 dp dq).
  apply residual_shaped_e_7.
Qed.

Theorem residual_gra_Xe_minus_X_N_ndiv_linear :
  forall e,
    (2 <= e)%nat ->
    nth 1%nat (poly_sub (poly_Xn e) poly_X) 0 = -1 /\
    ~ (187 | -1).
Proof.
  intros e He. split.
  - apply Xe_minus_X_linear_coeff. exact He.
  - intros [k Hk]. nia.
Qed.

Theorem residual_gra_X3_minus_X_N_ndiv_linear :
  nth 1%nat (poly_sub (poly_Xn 3) poly_X) 0 = -1 /\
  ~ (187 | -1).
Proof. apply residual_gra_Xe_minus_X_N_ndiv_linear. lia. Qed.

Theorem residual_gra_X7_minus_X_N_ndiv_linear :
  nth 1%nat (poly_sub (poly_Xn 7) poly_X) 0 = -1 /\
  ~ (187 | -1).
Proof. apply residual_gra_Xe_minus_X_N_ndiv_linear. lia. Qed.

(** Equality-test and [GInv] of a non-unit still leak a proper
    factor.  Residual-shaped [e] does not disable those leaks. *)

Theorem residual_gra_eq_leak_factors :
  Problem_Factor 187 (gra_eq_leak pin_N gra_eq_prog 36 9%nat 0%nat).
Proof. apply gra_eq_leak_factors. Qed.

Theorem residual_gra_inv_nonunit_factors :
  Problem_Factor 187 (gra_eval_Z gra_inv11_prog 36 4%nat).
Proof. apply gra_inv_nonunit_factors. Qed.

(** ** Division-free tape denotes a polynomial; integer [P^e = X]
    is forbidden for residual-shaped [e ≥ 2].  Identity tape
    (output [y]) is not residual invert on the pin. *)

Theorem residual_gra_nodiv_empty_is_nodiv :
  Forall is_nodiv [].
Proof. constructor. Qed.

Theorem residual_gra_identity_tape_is_y :
  gra_eval 187 [] 36 2%nat = 36.
Proof. reflexivity. Qed.

Theorem residual_gra_identity_tape_not_cube :
  powm 36 3 187 <> 36.
Proof. vm_compute. discriminate. Qed.

Theorem residual_gra_nodiv_integer_identity_forbidden :
  forall ops e N out,
    Forall is_nodiv ops ->
    residual_shaped_e (Z.of_nat e) 80 ->
    (2 <= e)%nat ->
    (forall y, Z.pow (gra_eval N ops y out) (Z.of_nat e) = y) ->
    False.
Proof.
  intros ops e N out Hop [He _] H2 Hall.
  apply (gra_nodiv_integer_eth_root_forbidden ops e N out); assumption.
Qed.

Theorem residual_gra_nodiv_cube_identity_forbidden :
  forall ops N out,
    Forall is_nodiv ops ->
    (forall y, Z.pow (gra_eval N ops y out) 3 = y) ->
    False.
Proof.
  intros ops N out Hop Hall.
  apply (gra_nodiv_integer_eth_root_forbidden ops 3%nat N out);
    [exact Hop | lia | exact Hall].
Qed.

Theorem residual_gra_mul_denotes_square :
  gra_eval 187 [GMul 2%nat 2%nat] 36 3%nat = 36 * 36.
Proof. apply gra_nodiv_mul_denotes_square. Qed.
