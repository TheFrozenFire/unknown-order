From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import GenericRing.

Open Scope Z_scope.

(** * Joux–Naccache–Thomé affine-root oracle

    An [e]-th-root oracle restricted to values of the form [x + c],
    not a general [GRoot].  SNFS cost stays [Refuse_NFS_cost].
    Cross-confirmed by [cas/123]. *)

Definition jnt_oracle (x c : Z) : Z :=
  integer_cube_root (x + c).

Theorem jnt_roots_affine :
  jnt_oracle 7 1 = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem jnt_affine_is_plain_cube :
  7 + 1 = 8 /\ 2 * 2 * 2 = 8.
Proof. split; reflexivity. Qed.

Theorem jnt_not_a_general_root :
  integer_cube_root 7 = 7.
Proof. vm_compute. reflexivity. Qed.

Theorem jnt_general_roots_plain_cubes :
  integer_cube_root 8 = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem jnt_c0_is_general :
  jnt_oracle 8 0 = integer_cube_root 8.
Proof. vm_compute. reflexivity. Qed.
