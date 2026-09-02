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
    filters a TM can run without the trapdoor.  None inhabits
    [srsa_residual_leaf] as [Problem_Factor].  Cross-confirmed
    by [cas/131]. *)

(** ** 1. One-sided local root as an integer *)

Theorem filter_onesided_local_mod_p :
  powm 9 3 11 = 36 mod 11.
Proof. vm_compute. reflexivity. Qed.

Theorem filter_onesided_not_global :
  powm 9 3 187 <> 36.
Proof. vm_compute. discriminate. Qed.

Theorem filter_onesided_integer_splits :
  9 * 9 * 9 = 729 /\
  Z.gcd (729 - 36) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

(** ** 2. [x = −y] *)

Theorem filter_neg_y_not_cube_root :
  powm (-36) 3 187 = 94 /\
  94 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem filter_y_square_not_minus1 :
  powm 36 2 187 <> powm (-1) 1 187.
Proof. vm_compute. discriminate. Qed.

(** ** 3. Euclid on [(y±1, N)] *)

Theorem filter_euclid_y_minus_1 :
  Z.gcd (36 - 1) 187 = 1.
Proof. reflexivity. Qed.

Theorem filter_euclid_y_plus_1 :
  Z.gcd (36 + 1) 187 = 1.
Proof. reflexivity. Qed.

(** ** 4. Nontrivial [e]-th root of 1 at [gcd(e,λ)>1] *)

Theorem filter_fifth_shares_lambda :
  Z.gcd 5 80 = 5 /\
  Z.gcd 5 80 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem filter_fifth_root_of_1_splits :
  powm 69 5 187 = 1 /\
  Z.gcd (69 - 1) 187 = 17 /\
  Z.coprime 69 187 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

(** ** 5. Public period [N+1] *)

Theorem filter_Nplus1_does_not_annihilate :
  powm 2 (187 + 1) 187 = 135 /\
  135 <> 2 /\
  powm 2 80 187 = 1 /\
  187 + 1 <> 80.
Proof. vm_compute. repeat split; discriminate. Qed.

(** ** 6. Extra output [φ] *)

Theorem filter_phi_gives_sum :
  phi_semiprime 11 17 = 160 /\
  187 - 160 + 1 = 11 + 17.
Proof. split; reflexivity. Qed.

Theorem filter_phi_enum_factors :
  let '(x, y) := factors_from_phi 187 160 in
  x = 17 /\ y = 11.
Proof. apply rsa_test_enum_from_phi. Qed.

Theorem filter_phi_is_factor :
  Problem_Factor 187 11.
Proof. unfold Problem_Factor. split; [lia|]. exists 17. reflexivity. Qed.

(** ** 7. 2-adic Hensel: [v₂(y)] not divisible by 3 *)

Theorem filter_val2_36 :
  val2 36 = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem filter_val2_not_div_by_3 :
  ~ (3 | Z.of_nat (val2 36)).
Proof. rewrite filter_val2_36. intros [k Hk]. nia. Qed.

(** ** 8. Locally constant [X] ([y] modulo [m]) *)

Theorem filter_locally_constant_clash :
  36 mod 5 = 6 mod 5 /\
  powm 42 3 187 = 36 /\
  36 <> 6.
Proof. vm_compute. repeat split; discriminate. Qed.

(** ** 9. Branch on Jacobi to [λ+1] *)

Theorem filter_jacobi_branch_lambda_type :
  jacobi_N 2 11 17 = -1 /\
  powm 2 81 187 = 2 /\
  (80 | 81 - 1).
Proof. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. exists 1. reflexivity. Qed.

Theorem filter_jacobi_branch_not_residual :
  ~ srsa_residual_leaf 187 80 2 2 81.
Proof.
  unfold srsa_residual_leaf. intros [_ [_ [_ [_ Hnd]]]].
  apply Hnd. exists 1. reflexivity.
Qed.

(** ** 10. Public coprimality filter [gcd(e, N−1)=1] *)

Definition public_e_filter (e N : Z) : Prop := Z.gcd e (N - 1) = 1.

Theorem filter_cube_fails_public_e :
  ~ public_e_filter 3 187.
Proof. unfold public_e_filter. vm_compute. discriminate. Qed.

Theorem filter_e11_passes_public_e :
  public_e_filter 11 187.
Proof. unfold public_e_filter. vm_compute. reflexivity. Qed.

Theorem filter_public_e11_miller_splits :
  Z.gcd (powm 36 10 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

(** ** 11. Low-bit [e = 2(y mod 2^k)+1] *)

Definition lowbit_e (y k : Z) : Z := 2 * (y mod 2 ^ k) + 1.

Theorem filter_lowbit_e9 :
  lowbit_e 36 3 = 9.
Proof. vm_compute. reflexivity. Qed.

Theorem filter_lowbit_e9_residual :
  srsa_residual_leaf 187 80 36 (powm 36 9 187) 9.
Proof.
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 4; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem filter_lowbit_root_is_70 :
  powm 36 9 187 = 70 /\
  powm 70 9 187 = 36.
Proof. vm_compute. split; reflexivity. Qed.

(** ** 12. Trace [x + x^{-1}] *)

Theorem filter_trace_not_root :
  (36 * 26) mod 187 = 1 /\
  36 + 26 = 62 /\
  powm 62 3 187 = 90 /\
  90 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem filter_torus_order_not_Nplus1 :
  Z.lcm (11 + 1) (17 + 1) = 36 /\
  36 <> 187 + 1.
Proof. split; [vm_compute; reflexivity | discriminate]. Qed.
