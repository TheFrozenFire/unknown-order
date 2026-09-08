From Stdlib Require Import ZArith.

Require Import Hardness.
Require Import TranscriptOracle.
Require Import StrongRSAPeel.
Require Import GenericRing.
Require Import SrsaRootPoly.
Require Import SrsaModCbrt.
Require Import SrsaInverter.
Require Import SrsaVaryingE.

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
Check invert_all_units_poly_constructs_factor.
Check pin_binomial_plus_N_kernel_cong_mod_N.
Check nodiv_gra_invert_all_units_constructs_factor.
Check invert_all_units_rational_constructs_factor.
Check invert_all_units_rational_Xd1_over_X.
Check unit_ginv_gra_invert_all_units_constructs_factor.
Check gra_first_inv_gcd_factors.
Check gra_first_root_factor_factors.
Check gra_unit_inv_denotes.
Check mod_cbrt_nonunit_factors.
Check pin_cbrt_p_factors.
Check integer_cbrt_p_neq_mod_cbrt_p.
Check mod_cbrt_unit_is_residual_leaf.
Check residual_leaf_y_is_residue.
Check pin_N_plus_1_not_a_leaf.
Check trapdoor_inhabits_residual_leaf.
Check pin_trapdoor_residual_solver.
Check residual_solver_reduced_pin_e_is_trapdoor.
Check residual_solver_reduced_pin_e_constructs_factor.
Check eth_root_nonunit_factors.
Check rsa_inverter_reduced_units_constructs_factor.
Check pin_dec_inverter.
Check inverter_as_residual.
Check pin_lambda_strong_solver.
Check pin_lambda_plus_one_does_not_split.
Check pin_lambda_strong_solver_not_residual.
Check strong_rsa_solver_pin_e_constructs_factor.
Check pin_N_plus_1_not_rsa_problem.
Check pin_N_plus_1_not_strong_RSA.
Check pin_lambda_strong_solver_outputs_never_proper_gcd.
Check residual_leaf_plus_k_lam.
Check pin_e_plus_lam_residual.
Check same_unit_x_two_exponents_annihilates.
Check pin_x_lam_gcd_is_N.
Check pin_miller_from_lambda_multiple.
Check pin_miller_from_lam_factors.
Check pin_e7_residual.
Check pin_e7_x_neq_pin_x.
Check residual_solver_reduced_e_cong_x_is_trapdoor.
Check residual_solver_reduced_e_cong_nonminimal_constructs_factor.
Check residual_solver_reduced_e_cong_constructs_factor.
Check pin_e_plus_lam_residual_solver.
Check pin_e_plus_lam_solver_millers.
Check unique_unit_eth_root_inv.
Check trapdoor_inhabits_residual_leaf_at.
Check residual_solver_reduced_fixed_e_is_trapdoor.
Check residual_solver_reduced_fixed_e_constructs_factor.
Check pin_e7_residual_solver.
Check pin_e7_solver_constructs_factor.
Check pin_miller_from_e7_inv.
Check pin_miller_from_e11_inv.
Check residual_solver_reduced_pin_e_via_fixed_e.
