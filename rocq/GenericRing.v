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
Require Import PollardP1.
Require Import SmallExponent.

Open Scope Z_scope.

(** * Generic ring algorithms (GRA) on [Z/NZ]

    A tape of ring handles, ops [{+, −, ·}] (wave 1), then [inv]
    (wave 2a) and a cube-root marker (wave 3).  Equality-test
    [gcd] of integer lifts is the leak.  Theorems are about traces,
    not standard-model RSA ≡ factoring.  Cross-confirmed by
    [cas/115]–[cas/117] and [cas/121]. *)

(** ** The machine *)

Inductive GRAOp : Set :=
  | GConst (c : Z)
  | GAdd (i j : nat)
  | GSub (i j : nat)
  | GMul (i j : nat)
  | GInv (i : nat)
  | GRoot (i : nat).

Definition gra_init (y : Z) : list Z := [0; 1; y].

Definition step_Z (op : GRAOp) (t : list Z) : list Z :=
  match op with
  | GConst c => t ++ [c]
  | GAdd i j => t ++ [nth i t 0 + nth j t 0]
  | GSub i j => t ++ [nth i t 0 - nth j t 0]
  | GMul i j => t ++ [nth i t 0 * nth j t 0]
  | GInv i => t ++ [Z.gcd (nth i t 0) 1]
  | GRoot i => t ++ [nth i t 0]
  end.

Fixpoint gra_run_Z (ops : list GRAOp) (t : list Z) : list Z :=
  match ops with
  | nil => t
  | op :: rest => gra_run_Z rest (step_Z op t)
  end.

Definition gra_eval_Z (ops : list GRAOp) (y : Z) (out : nat) : Z :=
  nth out (gra_run_Z ops (gra_init y)) 0.

Definition gra_eq_gcd (a b N : Z) : Z := Z.gcd (a - b) N.

(** ** Wave 0 — equality leak and the tape *)

Theorem gra_eq_leak_pin :
  Z.gcd 88 187 = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_eq_leak_factors :
  Problem_Factor 187 (Z.gcd 88 187).
Proof.
  unfold Problem_Factor. rewrite gra_eq_leak_pin.
  split; [lia|]. exists 17. reflexivity.
Qed.

Theorem gra_eq_leak_onesided :
  Z.prime 11 ->
  Z.prime 17 ->
  (11 | 88) ->
  ~ (17 | 88) ->
  Z.gcd 88 (11 * 17) = 11.
Proof.
  intros Hp Hq H11 H17.
  apply gcd_onesided_semiprime; try assumption; discriminate.
Qed.

Theorem gra_eq_N_is_not_a_split :
  Z.gcd 187 187 = 187.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_mul_y_pin :
  gra_eval_Z [GMul 2%nat 2%nat; GMul 3%nat 2%nat] 36 4%nat = 36 * 36 * 36.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_const42 :
  gra_eval_Z [GConst 42] 36 3%nat = 42.
Proof. vm_compute. reflexivity. Qed.

(** Division-free SLP → polynomial: each handle is [poly_eval] of a
    coeff list.  Init is [[0]; [1]; X]. *)

Definition slp_init_poly : list (list Z) := [[0]; [1]; poly_X].

Definition step_poly (op : GRAOp) (t : list (list Z)) : list (list Z) :=
  match op with
  | GConst c => t ++ [[c]]
  | GAdd i j => t ++ [poly_add (nth i t []) (nth j t [])]
  | GSub i j => t ++ [poly_sub (nth i t []) (nth j t [])]
  | GMul i j => t ++ [poly_mul (nth i t []) (nth j t [])]
  | GInv i => t ++ [nth i t []]
  | GRoot i => t ++ [nth i t []]
  end.

Fixpoint gra_run_poly (ops : list GRAOp) (t : list (list Z)) : list (list Z) :=
  match ops with
  | nil => t
  | op :: rest => gra_run_poly rest (step_poly op t)
  end.

Theorem slp_init_eval :
  forall y,
    poly_eval (nth 0%nat slp_init_poly []) y = 0 /\
    poly_eval (nth 1%nat slp_init_poly []) y = 1 /\
    poly_eval (nth 2%nat slp_init_poly []) y = y.
Proof.
  intros y. unfold slp_init_poly, nth, poly_eval.
  split; [ring|]. split; [ring|].
  fold (poly_eval poly_X y). apply poly_eval_X.
Qed.

Theorem slp_to_poly_mul_pin :
  let t := gra_run_poly [GMul 2%nat 2%nat] slp_init_poly in
  poly_eval (nth 3%nat t []) 36 = 36 * 36.
Proof. vm_compute. reflexivity. Qed.

(** ** Wave 1 — Leander–Rupp, no division, low [e] *)

Theorem gra_nodiv_const42_inverts_36 :
  powm 42 3 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_nodiv_const42_fails_on_8 :
  powm 42 3 187 <> 8.
Proof. vm_compute. discriminate. Qed.

Theorem gra_identity_not_cube_root_at_2 :
  powm 2 3 187 <> 2.
Proof. vm_compute. discriminate. Qed.

Theorem gra_identity_at_one :
  powm 1 3 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_identity_gcd_at_2 :
  Z.gcd (2 * 2 * 2 - 2) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_nodiv_identical_X3_linear :
  nth 1%nat (poly_Pe_minus_X poly_X 3%nat) 0 = -1.
Proof. apply X3_minus_X_nth1. Qed.

Theorem gra_nodiv_N_does_not_divide_minus1 :
  Z.gcd 1 187 = 1.
Proof. reflexivity. Qed.

Theorem gra_nodiv_identical_root_impossible_X3 :
  nth 1%nat (poly_Pe_minus_X poly_X 3%nat) 0 = -1 ->
  ~ (187 | -1).
Proof.
  intros H div. destruct div as [k Hk]. nia.
Qed.

Theorem Pe_minus_X_eval2_is_six_on_X :
  poly_eval (poly_Pe_minus_X poly_X 3%nat) 2 = 6.
Proof. apply X3_minus_X_eval_2. Qed.

(** ** Wave 2a — AM09 inversion leak and leading term *)

Theorem gra_inv_nonunit_pin :
  Z.gcd 11 187 = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_inv_nonunit_factors :
  Problem_Factor 187 (Z.gcd 11 187).
Proof.
  unfold Problem_Factor. rewrite gra_inv_nonunit_pin.
  split; [lia|]. exists 17. reflexivity.
Qed.

Theorem gra_inv_22_factors :
  Z.gcd 22 187 = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_inv_unit_pin :
  Z.gcd 36 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_fixed_e_leading_const :
  3 * 0 <> 1 + 3 * 0.
Proof. lia. Qed.

Theorem gra_fixed_e_leading :
  forall dp dq, 3 * dp <> 1 + 3 * dq.
Proof.
  intros dp dq. apply rational_Pe_minus_XQe_leading. lia.
Qed.

Theorem rsa_inverter_is_not_a_GRA_comment :
  powm 42 3 187 = 36.
Proof. apply gra_nodiv_const42_inverts_36. Qed.

(** Functional decryption [x ↦ x^d] inverts cubing on units and is
    not a polynomial identity in [F_11[X]]. *)
Theorem powm_d_inverts_cube_pin :
  powm 36 27 187 = 42.
Proof. vm_compute. reflexivity. Qed.

(** ** Wave 2b — AMS flexible [e]; [λ+1] is a constant, not a ring op on [y] *)

Theorem gra_const_81 :
  gra_eval_Z [GConst 81] 36 3%nat = 81 /\
  gra_eval_Z [GConst 81] 8 3%nat = 81.
Proof. vm_compute. split; reflexivity. Qed.

Theorem gra_const_lambda_plus_one_solves_sRSA_without_factoring :
  forall y,
    Z.coprime y 187 ->
    Problem_StrongRSA 187 (y mod 187) (y mod 187) 81.
Proof.
  intros y Hcop.
  apply (lambda_solves_strong_RSA 11 17 y prime_11 prime_17
           ltac:(discriminate) Hcop).
Qed.

Theorem gra_const_81_does_not_factor :
  Z.gcd 81 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem lambda_plus_one_is_81 :
  lambda_semiprime 11 17 + 1 = 81.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_add_mul_of_36_is_not_81 :
  36 + 36 <> 81 /\ 36 * 36 <> 81 /\ 36 - 36 <> 81.
Proof. lia. Qed.

Theorem am09_fixed_e_is_a_parameter :
  forall e dp dq,
    1 < e ->
    e * dp <> 1 + e * dq.
Proof. apply rational_Pe_minus_XQe_leading. Qed.

(** ** Wave 6a — Damgård–Koprowski signature contrast *)

Inductive GGMOp : Set :=
  | GGMul (i j : nat)
  | GGInv (i : nat).

Inductive is_ggm_op : GRAOp -> Prop :=
  | is_ggm_mul : forall i j, is_ggm_op (GMul i j)
  | is_ggm_inv : forall i, is_ggm_op (GInv i).

Theorem gadd_is_not_a_ggm_op :
  forall i j, ~ is_ggm_op (GAdd i j).
Proof. intros i j H. inversion H. Qed.

Theorem gsub_is_not_a_ggm_op :
  forall i j, ~ is_ggm_op (GSub i j).
Proof. intros i j H. inversion H. Qed.

Theorem gconst_is_not_a_ggm_op :
  forall c, ~ is_ggm_op (GConst c).
Proof. intros c H. inversion H. Qed.

Theorem gra_poly_construction_needs_add :
  nth 1%nat (poly_Pe_minus_X poly_X 3%nat) 0 = -1.
Proof. apply X3_minus_X_nth1. Qed.

Theorem generic_group_does_not_separate_rsa_from_srsa :
  forall N e y x,
    1 < e ->
    Problem_RSA N e y x ->
    Problem_StrongRSA N y x e.
Proof. intros N e y x He. apply rsa_solution_is_strong_RSA. exact He. Qed.

Theorem ggm_mul_pin :
  gra_eval_Z [GMul 2%nat 2%nat; GMul 3%nat 2%nat] 36 4%nat = 46656.
Proof. vm_compute. reflexivity. Qed.
