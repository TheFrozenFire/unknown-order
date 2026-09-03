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
Require Import SmallExponent.
Require Import GenericRing.

Open Scope Z_scope.

(** * Brown SLP-solver: identity vs functional-on-units

    An SLP that *is* a low-[e] RSA solver.  Complementary to
    Boneh–Venkatesan (which inspects a reduction that *uses* a root
    oracle).  [X^d] with [ed ≡ 1 (mod λ)] solves cubing on units and
    is a short SLP; [X^{81} − X] is not the zero polynomial.
    Dual-number tangent is [81 y^{80}], [gcd(80, pin_N) = 1] — this
    extension does not split.  A low-degree polynomial identity would
    require [N | −1].  Cross-confirmed by [cas/119]. *)

Theorem slp_carmichael_is_functional :
  powm 36 27 pin_N = 42 /\ powm 42 3 pin_N = 36.
Proof. vm_compute. split; reflexivity. Qed.

Theorem slp_solver_not_poly_identity_linear :
  nth 1%nat (poly_sub (poly_Xn 81%nat) poly_X) 0 = -1.
Proof. apply Xe_minus_X_linear_coeff. lia. Qed.

Theorem slp_solver_not_poly_identity_last :
  poly_last (poly_Xn 81%nat) = 1.
Proof. apply Xe_minus_X_last. Qed.

Theorem X81_minus_X_leading_not_zero_mod_11 :
  (poly_last (poly_Xn 81%nat)) mod 11 <> 0.
Proof. rewrite slp_solver_not_poly_identity_last. vm_compute. discriminate. Qed.

Theorem brown_low_degree_identity_forbids_N_dividing_minus1 :
  ~ (pin_N | -1).
Proof. intros [k Hk]. nia. Qed.

Theorem two_pow_81_is_two_mod_N :
  powm 2 81 pin_N = 2.
Proof. vm_compute. reflexivity. Qed.

(** Dual numbers: [(y+ε)^n = y^n + n y^{n-1} ε] with [ε² = 0]. *)
Fixpoint dual_pow (y : Z) (e : nat) : Z * Z :=
  match e with
  | O => (1, 0)
  | S e' =>
      let (a, b) := dual_pow y e' in
      (y * a, y * b + a)
  end.

Theorem brown_dual_pow27_fst :
  fst (dual_pow 2 27%nat) = Z.pow 2 27.
Proof. vm_compute. reflexivity. Qed.

Theorem brown_dual_not_identity :
  81 <> 1.
Proof. discriminate. Qed.

Theorem brown_dual_tangent_mod_N :
  (81 * powm 2 80 pin_N) mod pin_N = 81.
Proof. vm_compute. reflexivity. Qed.

Theorem brown_dual_gcd_pin :
  Z.gcd (81 - 1) pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem brown_ed_minus_1_is_80 :
  3 * 27 - 1 = 80.
Proof. reflexivity. Qed.
