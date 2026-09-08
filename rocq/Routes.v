From Stdlib Require Import ZArith.

Require Import StrongRSAPeel.
Require Import SrsaRootPoly.

Open Scope Z_scope.

(** * Residual-solver route pin

    Compile-time names for the live target and the reverse-closed
    fold classification.  [named-skips] harvests
    [Not [residual_solver_constructs_factor_open_named]] from
    subsection comments into [generated/NAMED_SKIPS.md].  This file
    fails to compile if either identifier is renamed or deleted.

    Not a proof that the fold theorem inhabits the open named —
    the types already forbid that.  The open named stays unused. *)

Check residual_solver_constructs_factor_open_named.
Check invert_all_units_both_folds_are_local_monomials.
