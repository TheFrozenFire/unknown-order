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

    A GRA that may call [GRoot] (cube-root gate) and outputs a factor
    of [N].  If the query is an integer cube, [GRoot] is [GConst] of
    that root — the oracle was unnecessary.  This is not a theorem
    that RSA is easier than factoring, and not Miller-from-[(e,d)].
    Cross-confirmed by [cas/118]. *)

(** [GRoot] is a trace marker, not [rsa_inverter]. *)
Theorem bv_root_gate_is_not_rsa_inverter :
  forall t : list Z,
    step_Z (GRoot 0%nat) t = t ++ [nth 0%nat t 0].
Proof. intros t. reflexivity. Qed.

Theorem bv_two_is_integer_cube :
  2 * 2 * 2 = 8.
Proof. reflexivity. Qed.

Theorem bv_36_is_not_integer_cube :
  3 * 3 * 3 <> 36 /\ 4 * 4 * 4 <> 36.
Proof. split; discriminate. Qed.

Theorem cube_is_powm3_pin :
  forall N, N <> 0 -> powm 2 3 N = (2 * 2 * 2) mod N.
Proof. intros N HN. apply cube_is_powm3. exact HN. Qed.

(** Program: [GConst 8; GRoot; GConst 11].  Output handle 5 is 11. *)
Definition bv_with_root : list GRAOp :=
  [GConst 8; GRoot 3%nat; GConst 11].

Definition bv_unwound : list GRAOp :=
  [GConst 8; GConst 2; GConst 11].

Theorem bv_with_root_outputs_11 :
  gra_eval_Z bv_with_root 36 5%nat = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem bv_unwound_outputs_11 :
  gra_eval_Z bv_unwound 36 5%nat = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem bv_unwind_one_cube :
  gra_eval_Z bv_with_root 36 5%nat =
    gra_eval_Z bv_unwound 36 5%nat.
Proof.
  rewrite bv_with_root_outputs_11, bv_unwound_outputs_11. reflexivity.
Qed.

Theorem bv_few_query_low_e_drops_oracle :
  Problem_Factor 187 (gra_eval_Z bv_unwound 36 5%nat).
Proof.
  rewrite bv_unwound_outputs_11. unfold Problem_Factor.
  split; [lia|]. exists 17. reflexivity.
Qed.

Theorem bv_42_cube_in_Z_is_not_36 :
  42 * 42 * 42 = 74088 /\ 74088 <> 36.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem bv_query_leak_already_factors :
  Problem_Factor 187 (Z.gcd 88 187).
Proof. apply gra_eq_leak_factors. Qed.
