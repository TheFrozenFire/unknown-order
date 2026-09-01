From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import Hardness.
Require Import GenericRing.

Open Scope Z_scope.

(** * Preprocessing GRA (Dachman-Soled–Loss–O'Neill shape)

    Arbitrary computation on [N] produces advice; then generic ring
    ops run on the instance [y].  If the advice already splits [N],
    factoring happened in preprocessing, not in the GRA.  Not NFS
    cost and not “RSA is easier than factoring.”  Cross-confirmed
    by [cas/124]. *)

Definition prep_advice_factor (N : Z) : Z := N / 17.

Definition prep_advice_id (N : Z) : Z := N.

Theorem prep_advice_depends_on_N :
  prep_advice_factor 187 = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem prep_advice_ignores_y :
  forall y : Z, prep_advice_factor 187 = 11.
Proof. intros y. apply prep_advice_depends_on_N. Qed.

Theorem prep_factor_advice :
  Problem_Factor 187 (prep_advice_factor 187).
Proof.
  unfold Problem_Factor, prep_advice_factor.
  change (187 / 17) with 11.
  split; [lia|]. exists 17. reflexivity.
Qed.

Theorem prep_id_advice_not_a_split :
  Z.gcd (prep_advice_id 187) 187 = 187.
Proof. vm_compute. reflexivity. Qed.

(** Tape [[0]; 1; y; advice].  [GInv] of the advice handle. *)
Definition prep_inv_prog : list GRAOp := [GInv 3%nat].

Definition prep_init (y advice : Z) : list Z := [0; 1; y; advice].

Definition prep_eval (y advice : Z) (ops : list GRAOp) (out : nat) : Z :=
  nth out (gra_run pin_N ops (prep_init y advice)) 0.

Theorem prep_ginv_of_factor_advice :
  prep_eval 36 (prep_advice_factor 187) prep_inv_prog 4%nat = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem prep_then_gra_factors :
  Problem_Factor 187
    (prep_eval 36 (prep_advice_factor 187) prep_inv_prog 4%nat).
Proof.
  unfold Problem_Factor. rewrite prep_ginv_of_factor_advice.
  split; [lia|]. exists 17. reflexivity.
Qed.
