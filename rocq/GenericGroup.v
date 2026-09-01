From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import GenericRing.

Open Scope Z_scope.

(** * Unknown-order generic group interpreter

    Ops [{*, inv, eq}].  Tape starts at [[1]; y] — no additive
    identity, no [GAdd].  Equality of products can still leak a
    factor ([gcd(2^{10}−1, N)]).  Query-complexity lower bounds
    stay [Refuse_UO_GGM].  Cross-confirmed by [cas/122]. *)

Inductive GGMStep : Set :=
  | GSMul (i j : nat)
  | GSInv (i : nat)
  | GSEq (i j : nat).

Definition ggm_init (y : Z) : list Z := [1; y].

Definition ggm_step (N : Z) (op : GGMStep) (t : list Z) : list Z :=
  match op with
  | GSMul i j => t ++ [nth i t 0 * nth j t 0]
  | GSInv i => t ++ [gra_inv (nth i t 0) N]
  | GSEq i j => t ++ [Z.gcd (nth i t 0 - nth j t 0) N]
  end.

Fixpoint ggm_run (N : Z) (ops : list GGMStep) (t : list Z) : list Z :=
  match ops with
  | nil => t
  | op :: rest => ggm_run N rest (ggm_step N op t)
  end.

Definition ggm_eval (N : Z) (ops : list GGMStep) (y : Z) (out : nat) : Z :=
  nth out (ggm_run N ops (ggm_init y)) 0.

(** Adding two handles is uninhabited: [GGMStep] has no add constructor. *)
Inductive ggm_has_add : GGMStep -> Prop := .

Theorem ggm_add_uninhabited :
  forall s, ~ ggm_has_add s.
Proof. intros s H. destruct H. Qed.

Theorem ggm_step_is_mul_inv_or_eq :
  forall s,
    (exists i j, s = GSMul i j) \/
    (exists i, s = GSInv i) \/
    (exists i j, s = GSEq i j).
Proof.
  intros s. destruct s as [i j | i | i j].
  - left. exists i, j. reflexivity.
  - right. left. exists i. reflexivity.
  - right. right. exists i, j. reflexivity.
Qed.

(** [2^{10}] by successive squares from [[1]; 2], then eq against 1. *)
Definition ggm_pow10 : list GGMStep :=
  [GSMul 1%nat 1%nat;
   GSMul 2%nat 2%nat;
   GSMul 3%nat 3%nat;
   GSMul 4%nat 2%nat;
   GSEq 5%nat 0%nat].

Theorem ggm_init_is_one_and_y :
  ggm_init 2 = [1; 2].
Proof. reflexivity. Qed.

Theorem ggm_pow10_handle :
  ggm_eval pin_N ggm_pow10 2 5%nat = 1024.
Proof. vm_compute. reflexivity. Qed.

Theorem ggm_eq_leak_from_tape :
  ggm_eval pin_N ggm_pow10 2 6%nat = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem ggm_eq_leak_factors :
  Problem_Factor 187 (ggm_eval pin_N ggm_pow10 2 6%nat).
Proof.
  unfold Problem_Factor. rewrite ggm_eq_leak_from_tape.
  split; [lia|]. exists 17. reflexivity.
Qed.

Theorem ggm_yyy_pin :
  ggm_eval pin_N [GSMul 1%nat 1%nat; GSMul 2%nat 1%nat] 36 3%nat = 36 * 36 * 36.
Proof. vm_compute. reflexivity. Qed.
