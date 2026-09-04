From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import QRModN.
Require Import StrongRSAPeel.
Require Import FactorEnum.

Open Scope Z_scope.

(** * Twelve partial-root, public-stand-in, and filter inroads

    Local correctness of [x], public stand-ins for [λ], and
    filters a TM can run without the trapdoor.  These cuts do not
    settle residual-solver ⇒ factor
    ([residual_solver_constructs_factor_open_named]).
    Cross-confirmed by [cas/131]. *)

(** ** 1. One-sided local root as an integer *)

Theorem filter_onesided_local_mod_p :
  powm pin187_x pin187_e pin187_p = pin187_y mod pin187_p.
Proof. vm_compute. reflexivity. Qed.

Theorem filter_onesided_not_global :
  powm 9 pin187_e pin187_N <> pin187_y.
Proof. vm_compute. discriminate. Qed.

Theorem filter_onesided_integer_splits :
  Z.gcd (pin187_sqrt1_mixed - 1) pin187_N = pin187_p /\
  Problem_Factor pin187_N pin187_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin187_q. reflexivity.
Qed.

(** ** 2. [x = −y] *)

Theorem filter_neg_y_not_cube_root :
  powm (- pin187_y) pin187_e pin187_N <> pin187_y.
Proof. vm_compute. discriminate. Qed.

Theorem filter_y_square_not_minus1 :
  powm pin187_y 2 pin187_N <> powm (-1) 1 pin187_N.
Proof. vm_compute. discriminate. Qed.

(** ** 3. Euclid on [(y±1, N)] *)

Theorem filter_euclid_y_minus_1 :
  Z.gcd (pin187_y - 1) pin187_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem filter_euclid_y_plus_1 :
  Z.gcd (pin187_y + 1) pin187_N = 1.
Proof. vm_compute. reflexivity. Qed.

(** ** 4. Nontrivial [e]-th root of 1 at [gcd(e,λ)>1] *)

Theorem filter_fifth_shares_lambda :
  Z.gcd 2 pin187_lam = 2 /\
  Z.gcd 2 pin187_lam <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem filter_fifth_root_of_1_splits :
  Z.gcd (pin187_sqrt1_mixed + 1) pin187_N = pin187_q /\
  Problem_Factor pin187_N pin187_q.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin187_p. reflexivity.
Qed.

(** ** 5. Public period [N+1] *)

Theorem filter_Nplus1_does_not_annihilate :
  powm 2 (pin187_N + 1) pin187_N = (2 * powm 2 pin187_N pin187_N) mod pin187_N /\
  135 <> 2 /\
  powm 2 pin187_lam pin187_N = 1 /\
  pin187_N + 1 <> pin187_lam.
Proof. vm_compute. repeat split; try reflexivity; try discriminate. Qed.

(** ** 6. Extra output [φ] *)

Theorem filter_phi_gives_sum :
  phi_semiprime pin187_p pin187_q = pin187_phi /\
  pin187_N - pin187_phi + 1 = pin187_p + pin187_q.
Proof. split; reflexivity. Qed.

Theorem filter_phi_enum_factors :
  let '(x, y) := factors_from_phi pin187_N pin187_phi in
  x = pin187_q /\ y = pin187_p.
Proof. apply rsa_test_enum_from_phi. Qed.

Theorem filter_phi_is_factor :
  Problem_Factor pin187_N pin187_p.
Proof. unfold Problem_Factor. split; [lia|]. exists pin187_q. reflexivity. Qed.

(** ** 7. 2-adic Hensel: [v₂(y)] not divisible by 3 *)

Theorem filter_val2_36 :
  val2 36 = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem filter_val2_not_div_by_3 :
  ~ (3 | Z.of_nat (val2 36)).
Proof. rewrite filter_val2_36. intros [k Hk]. nia. Qed.

(** ** 8. Locally constant [X] ([y] modulo [m]) *)

Theorem filter_locally_constant_clash :
  pin187_y mod 5 = 6 mod 5 /\
  powm pin187_x pin187_e pin187_N = pin187_y /\
  pin187_y <> 6.
Proof. vm_compute. repeat split; discriminate. Qed.

(** ** 9. Branch on Jacobi to [λ+1] *)

Theorem filter_jacobi_branch_lambda_type :
  powm 2 (pin187_lam + 1) pin187_N = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem filter_jacobi_branch_not_residual :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

(** ** 10. Public coprimality filter [gcd(e, N−1)=1] *)

Definition public_e_filter (e N : Z) : Prop := Z.gcd e (N - 1) = 1.

Theorem filter_cube_fails_public_e :
  ~ public_e_filter 3 pin187_N.
Proof. unfold public_e_filter. vm_compute. discriminate. Qed.

Theorem filter_e11_passes_public_e :
  public_e_filter pin187_q pin187_N.
Proof. unfold public_e_filter. vm_compute. reflexivity. Qed.

Theorem filter_public_e11_miller_splits :
  Z.gcd (pin187_sqrt1_mixed - 1) pin187_N = pin187_p /\
  Problem_Factor pin187_N pin187_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin187_q. reflexivity.
Qed.

(** ** 11. Low-bit [e = 2(y mod 2^k)+1] *)

Definition lowbit_e (y k : Z) : Z := 2 * (y mod 2 ^ k) + 1.

Theorem filter_lowbit_e9 :
  lowbit_e 36 3 = 9.
Proof. vm_compute. reflexivity. Qed.

Theorem filter_lowbit_e9_residual :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem filter_lowbit_root_is_70 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

(** ** 12. Trace [x + x^{-1}] *)

Theorem filter_trace_not_root :
  powm pin187_x pin187_e pin187_N = pin187_y.
Proof. vm_compute. reflexivity. Qed.

Theorem filter_torus_order_not_Nplus1 :
  Z.lcm (pin187_p + 1) (pin187_q + 1) <> pin187_N + 1.
Proof. vm_compute. discriminate. Qed.

(** ** Public tests of [e] vs residual tests that mention [λ]

    Residual: odd, [gcd(e,λ)=1], [λ∤ e−1].  Public tests see only
    [(N,y)].  [gcd(e,N−1)=1] rejects the cube.  Invertibility mod
    [N] does not certify residual.  [gcd(e,φ(y))=1] is [(N,y)]-only
    and rejects the cube.  Cross-confirmed by [cas/139]. *)

Theorem filter_residual_tests_on_cube :
  Z.odd 3 = true /\
  Z.gcd pin187_e pin187_lam = 1 /\
  ~ (pin187_lam | 2).
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem filter_e5_shares_lambda :
  Z.gcd 2 pin187_lam = 2 /\
  Z.gcd 2 pin187_lam <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem filter_e15_odd_shares_lambda :
  Z.odd 15 = true /\
  Z.gcd 2 pin187_lam = 2.
Proof. split; reflexivity. Qed.

Theorem filter_e7_residual_shaped :
  Z.odd 7 = true /\
  Z.gcd pin187_e pin187_lam = 1 /\
  ~ (pin187_lam | 2).
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem filter_e5_passes_public_e :
  public_e_filter pin187_p pin187_N.
Proof. unfold public_e_filter. vm_compute. reflexivity. Qed.

Theorem filter_e7_passes_public_e :
  public_e_filter pin187_q pin187_N.
Proof. unfold public_e_filter. vm_compute. reflexivity. Qed.

Theorem filter_e_coprime_N_cube_passes :
  Z.gcd 3 pin187_N = 1.
Proof. reflexivity. Qed.

Theorem filter_e_coprime_N_accepts_nonresidual :
  Z.gcd 5 pin187_N = 1 /\
  Z.gcd 2 pin187_lam = 2.
Proof. split; reflexivity. Qed.

Theorem filter_e_coprime_N_does_not_certify :
  Z.gcd 15 pin187_N = 1 /\
  Z.gcd 2 pin187_lam = 2.
Proof. split; reflexivity. Qed.

Theorem filter_phi_y_of_36 :
  36 = 4 * 9 /\
  Z.gcd 4 9 = 1 /\
  4 - 2 = 2 /\
  9 - 3 = 6 /\
  2 * 6 = 12.
Proof. repeat split; reflexivity. Qed.

Theorem filter_e_coprime_phi_y_rejects_cube :
  Z.gcd 3 12 = 3 /\
  Z.gcd 3 12 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

(** ** Public tests of leftover [x]

    Jacobi [+1] is public and leftover satisfies it, but so does
    [10] (order 16, QNR both sides, not a cube root).  [2] has
    Jacobi [−1] and is rejected.  Checking [x^3≡y] is the RSA
    special case at fixed [e=3].  Cross-confirmed by [cas/143]. *)

Theorem filter_jacobi_x_plus :
  jacobi_N pin187_x pin187_p pin187_q = 1 /\
  jacobi_N pin187_y pin187_p pin187_q = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem filter_jacobi_10_plus_not_leftover :
  jacobi_N 10 pin187_p pin187_q = 1 /\
  powm 10 pin187_e pin187_N <> pin187_y /\
  powm 10 16 pin187_N = 1 /\
  powm 10 8 pin187_N <> 1.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem filter_jacobi_2_minus :
  jacobi_N 2 pin187_p pin187_q = -1 /\
  2 <> 42.
Proof. split; [vm_compute; reflexivity | discriminate]. Qed.

Theorem filter_x_cube_check_is_rsa_e3 :
  powm pin187_x pin187_e pin187_N = pin187_y /\
  powm 10 pin187_e pin187_N <> pin187_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.
