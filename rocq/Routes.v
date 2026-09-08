From Stdlib Require Import ZArith.

Require Import Hardness.
Require Import TranscriptOracle.
Require Import StrongRSAPeel.
Require Import SrsaRootPoly.

Open Scope Z_scope.

(** * Live-target route pins

    Compile-time names for the three unused live targets and the
    reverse-closed sentences that must not inhabit them.
    [named-skips] harvests the [Not] join from subsection comments
    into [generated/NAMED_SKIPS.md].  This file fails to compile if
    a pinned identifier is renamed or deleted.

    [Check] is not a hypothesis.  The open nameds stay unused. *)

Check residual_solver_constructs_factor_open_named.
Check invert_all_units_both_folds_are_local_monomials.
Check leftover_kernel_span.

Check rsa_inverter_constructs_factor_open_named.
Check rsa_inverter_recovers_message.

Check strong_rsa_solver_constructs_factor_open_named.
Check rsa_solution_is_strong_RSA.
Check leftover_mismatch_factors.
