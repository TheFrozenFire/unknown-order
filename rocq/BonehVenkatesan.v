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

(** * Boneh–Venkatesan unwind of a low-[e] algebraic reduction

    A GRA that calls [GRoot] (integer cube-root) on a public cube,
    then uses that handle to produce a factor: [gcd(r^{10}−1, N)].
    Replacing [GRoot(8)] by [GConst 2] yields the same factor — the
    oracle was unnecessary.  Not a theorem that RSA is easier than
    factoring, and not Miller-from-[(e,d)].  Cross-confirmed by
    [cas/118]. *)

Theorem bv_two_is_integer_cube :
  2 * 2 * 2 = 8.
Proof. reflexivity. Qed.

Theorem bv_36_is_not_integer_cube :
  3 * 3 * 3 <> 36 /\ 4 * 4 * 4 <> 36.
Proof. split; discriminate. Qed.

Theorem cube_is_powm3_pin :
  forall N, N <> 0 -> powm 2 3 N = (2 * 2 * 2) mod N.
Proof. intros N HN. apply cube_is_powm3. exact HN. Qed.

Theorem integer_cube_root_8 :
  integer_cube_root 8 = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem bv_groot_8_is_2 :
  gra_eval_Z [GConst 8; GRoot 3%nat] 36 4%nat = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem bv_root_gate_is_not_rsa_inverter :
  integer_cube_root 8 = 2 /\ 2 * 2 * 2 = 8.
Proof. split; [apply integer_cube_root_8 | reflexivity]. Qed.

(** Query [GRoot(8)] getting [r=2], then [r^{10}−1], then [GInv]
    which returns [gcd(1023, 187)=11]. *)
Definition bv_with_root : list GRAOp :=
  [GConst 8;
   GRoot 3%nat;
   GMul 4%nat 4%nat;
   GMul 5%nat 5%nat;
   GMul 6%nat 6%nat;
   GMul 7%nat 5%nat;
   GConst 1;
   GSub 8%nat 9%nat;
   GInv 10%nat].

(** Same program with [GRoot] deleted and [GConst 2] in its place. *)
Definition bv_unwound : list GRAOp :=
  [GConst 8;
   GConst 2;
   GMul 4%nat 4%nat;
   GMul 5%nat 5%nat;
   GMul 6%nat 6%nat;
   GMul 7%nat 5%nat;
   GConst 1;
   GSub 8%nat 9%nat;
   GInv 10%nat].

Theorem bv_groot_handle_is_2 :
  gra_eval_Z bv_with_root 36 4%nat = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem bv_unwound_handle_is_2 :
  gra_eval_Z bv_unwound 36 4%nat = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem bv_with_root_outputs_11 :
  gra_eval_Z bv_with_root 36 11%nat = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem bv_unwound_outputs_11 :
  gra_eval_Z bv_unwound 36 11%nat = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem bv_unwind_one_cube :
  gra_eval_Z bv_with_root 36 11%nat =
    gra_eval_Z bv_unwound 36 11%nat.
Proof.
  rewrite bv_with_root_outputs_11, bv_unwound_outputs_11. reflexivity.
Qed.

Theorem bv_few_query_low_e_drops_oracle :
  Problem_Factor 187 (gra_eval_Z bv_unwound 36 11%nat).
Proof.
  rewrite bv_unwound_outputs_11. unfold Problem_Factor.
  split; [lia|]. exists 17. reflexivity.
Qed.

Theorem bv_factor_from_root_handle :
  Problem_Factor 187 (gra_eval_Z bv_with_root 36 11%nat).
Proof.
  rewrite bv_with_root_outputs_11. unfold Problem_Factor.
  split; [lia|]. exists 17. reflexivity.
Qed.

Theorem bv_42_cube_in_Z_is_not_36 :
  42 * 42 * 42 = 74088 /\ 74088 <> 36.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem bv_query_leak_already_factors :
  Problem_Factor 187 (gra_eq_leak pin_N gra_eq_prog 36 9%nat 0%nat).
Proof. apply gra_eq_leak_factors. Qed.
