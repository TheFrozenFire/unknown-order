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
Require Import GenericRing.
Require Import SAGM.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Algorithm restrictions: SAGM-only, safeprime residual, polynomial [e(y)]

    These close solvers of a restricted *shape*.  They do not inhabit
    [srsa_residual_leaf] as [Problem_Factor].  Cross-confirmed by
    [cas/128]. *)

(** ** SAGM-only: known exponents of public bases *)

Definition sagm_scale (r : SAGMRep) (e : Z) : SAGMRep :=
  {| sagm_a := sagm_a r * e; sagm_b := sagm_b r * e |}.

Theorem sagm_powm_mul_exp :
  forall N g a e,
    N <> 0 ->
    0 <= a ->
    0 <= e ->
    powm (powm g a N) e N = powm g (a * e) N.
Proof.
  intros N g a e Hn Ha He.
  symmetry. apply powm_mul_r; lia.
Qed.

Theorem sagm_root_of_generator_pin :
  powm (powm 3 27 187) 3 187 = 3.
Proof. vm_compute. reflexivity. Qed.

Theorem sagm_ae_minus_one_is_lambda :
  27 * 3 - 1 = 80.
Proof. reflexivity. Qed.

Theorem sagm_generator_annihilated :
  powm 3 (27 * 3 - 1) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem sagm_only_miller_splits :
  Z.gcd (67 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem sagm_scale_eval_pin :
  let r := {| sagm_a := 2; sagm_b := 1 |} in
  sagm_eval 187 sagm_pin_g sagm_pin_h (sagm_scale r 81) =
    powm (sagm_eval 187 sagm_pin_g sagm_pin_h r) 81 187.
Proof. vm_compute. reflexivity. Qed.

Theorem sagm_scale_lambda_type :
  let r := {| sagm_a := 2; sagm_b := 1 |} in
  sagm_eval 187 sagm_pin_g sagm_pin_h (sagm_scale r 81) =
    sagm_eval 187 sagm_pin_g sagm_pin_h r.
Proof. vm_compute. reflexivity. Qed.

(** ** Safeprime residual on [N = 77], [λ = 30 = 2 p' q'] *)

Theorem safeprime_e3_names_p :
  Z.gcd 3 30 = 3 /\
  2 * 3 + 1 = 7 /\
  (7 | 77).
Proof. split; [reflexivity|]. split; [reflexivity|]. exists 11. reflexivity. Qed.

Theorem safeprime_e5_names_q :
  Z.gcd 5 30 = 5 /\
  2 * 5 + 1 = 11 /\
  (11 | 77).
Proof. split; [reflexivity|]. split; [reflexivity|]. exists 7. reflexivity. Qed.

Theorem safeprime_e3_not_residual :
  Z.gcd 3 30 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem safeprime_residual_e7 :
  srsa_residual_leaf 77 30 51 2 7.
Proof.
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 3; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

(** ** Polynomial [e] of the challenge *)

Theorem poly_e_constant :
  forall y, poly_eval [3] y = 3.
Proof. intros y. unfold poly_eval. lia. Qed.

Theorem poly_e_constant_is_fixed_e :
  poly_eval [3] 36 = 3 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof. split; [apply poly_e_constant | apply srsa_residual_pin]. Qed.

Theorem poly_e_X_two_points :
  poly_eval poly_X 36 <> poly_eval poly_X 2.
Proof. rewrite poly_eval_X. rewrite poly_eval_X. discriminate. Qed.

Theorem poly_e_X_not_rerand :
  poly_eval poly_X (36 * Z.pow 2 3) <> poly_eval poly_X 36.
Proof. apply srsa_poly_e_not_rerand_invariant. Qed.

Theorem poly_e_nonconstant_not_fixed_parameter :
  forall dq, 3 * 1 <> 1 + 3 * dq.
Proof. intros dq. apply am09_fixed_e_is_a_parameter. lia. Qed.
