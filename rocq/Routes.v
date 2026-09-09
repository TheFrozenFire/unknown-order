From Stdlib Require Import ZArith.

Require Import Hardness.
Require Import TranscriptOracle.
Require Import StrongRSAPeel.
Require Import Pratt.
Require Import Order.
Require Import BinForms.
Require Import GenericRing.
Require Import SrsaRootPoly.
Require Import SrsaModCbrt.
Require Import SrsaInverter.
Require Import SrsaVaryingE.
Require Import Miller.
Require Import MillerHeight.
Require Import SrsaExtractD.
Require Import SrsaHom.

Open Scope Z_scope.

(** * Live-target route pins

    Compile-time names for the unused live targets and the
    reverse-closed sentences that must not inhabit them.
    [named-skips] harvests the [Not] join from subsection comments
    into [generated/NAMED_SKIPS.md].  This file fails to compile if
    a pinned identifier is renamed or deleted.

    The [RSAInstance] forms ([residual_solver_constructs_factor_open_named]
    and siblings) are instance-vacuous: [exists f] ignores the solver
    and [rsa_p] inhabits them.  Do not inhabit.  The extraction forms
    ([residual_solver_extracts_factor_open_named] and siblings) quantify
    over [N] and the solver graph, with no [RSAInstance].  Unused means
    unproved, on-goal.  [Check] is not a hypothesis. *)

Check residual_solver_constructs_factor_open_named.
Check residual_solver_extracts_factor_open_named.
Check invert_all_units_both_folds_are_local_monomials.
Check leftover_kernel_span.

Check rsa_inverter_constructs_factor_open_named.
Check rsa_inverter_extracts_factor_open_named.
Check rsa_inverter_recovers_message.

Check strong_rsa_solver_constructs_factor_open_named.
Check strong_rsa_solver_extracts_factor_open_named.
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
Check miller_walk.
Check pin_miller_walk_base2.
Check pin_miller_walk_not_at_g0.
Check miller_walk_factors.
Check miller_search.
Check pin_miller_search.
Check pin_miller_search_in_range.
Check pin_miller_walk_liar_1.
Check pin_miller_walk_liar_minus1.
Check pin_miller_walk_liar_50.
Check pin_209_is_blum.
Check pin_209_miller_walk_base2_liar.
Check pin_209_miller_walk_base3.
Check pin_209_miller_search.
Check pin_77_miller_walk_base2_hits.
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
Check unique_unit_eth_root_from_coprime_e.
Check pin_e5_fifth_roots_not_unique.
Check residual_inv_mod_lam.
Check residual_solver_reduced_fixed_e_constructs_factor_from_e.
Check invert_all_units_poly_at_e.
Check pin_X23_poly_at_7_constructs_factor.
Check residual_solver_reduced_fixed_e_extracts_and_factors.
Check pin_e7_solver_extracts_and_factors.
Check residual_leaf_at_g_extracts_and_factors.
Check residual_solver_reduced_constructs_factor_pin.
Check residual_x_homomorphic.
Check pin_trapdoor_solver_x_homomorphic.
Check residual_x_homomorphic_constructs_factor.
Check rsa_inverter_reduced_units_constructs_factor_pin.
Check strong_rsa_solver_annihilator_e_constructs_factor.
Check pin_lambda_strong_solver_annihilator_e.
Check residual_solver_not_annihilator_e.
Check pratt_complete_open_named.
Check pratt_generator_ok_11.
Check pratt_factors_ok_11.
Check orders_attained_generate_lambda.
Check compose_preserves_disc_open_named.
Check compose_assoc_open_named.
Check compose_left_compat_open_named.
