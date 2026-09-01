From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * Strong algebraic group model (representation)

    Each group handle carries known exponents of public generators.
    A product of handles is the sum of those exponents.  Not a
    standard-model hardness claim.  Cross-confirmed by [cas/124]. *)

Record SAGMRep : Set := {
  sagm_a : Z;
  sagm_b : Z
}.

Definition sagm_eval (N g h : Z) (r : SAGMRep) : Z :=
  (powm g (sagm_a r) N * powm h (sagm_b r) N) mod N.

Definition sagm_mul (r s : SAGMRep) : SAGMRep :=
  {| sagm_a := sagm_a r + sagm_a s;
     sagm_b := sagm_b r + sagm_b s |}.

Definition sagm_pin_g : Z := 3.
Definition sagm_pin_h : Z := 5.

Theorem sagm_eval_21 :
  sagm_eval 187 sagm_pin_g sagm_pin_h {| sagm_a := 2; sagm_b := 1 |} =
    (9 * 5) mod 187.
Proof. vm_compute. reflexivity. Qed.

Theorem sagm_product_adds_exponents :
  let r := {| sagm_a := 2; sagm_b := 1 |} in
  let s := {| sagm_a := 1; sagm_b := 3 |} in
  sagm_eval 187 sagm_pin_g sagm_pin_h (sagm_mul r s) =
    (sagm_eval 187 sagm_pin_g sagm_pin_h r *
     sagm_eval 187 sagm_pin_g sagm_pin_h s) mod 187.
Proof. vm_compute. reflexivity. Qed.

Theorem sagm_mul_exps :
  sagm_a (sagm_mul {| sagm_a := 2; sagm_b := 1 |}
                   {| sagm_a := 1; sagm_b := 3 |}) = 3 /\
  sagm_b (sagm_mul {| sagm_a := 2; sagm_b := 1 |}
                   {| sagm_a := 1; sagm_b := 3 |}) = 4.
Proof. split; reflexivity. Qed.
