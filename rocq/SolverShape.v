From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Zmod.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.ZPoly.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import QRModN.
Require Import StrongRSAPeel.
Require Import SmallExponent.
Require Import BlindRSA.
Require Import TwoPrimary.
Require Import GenericRing.
Require Import Miller.

Open Scope Z_scope.

(** * Twelve solver-shape inroads on Strong RSA

    Restrict how a TM writes [x] and [e], not which values they
    happen to be.  These cuts do not settle residual-solver ⇒ factor
    ([residual_solver_constructs_factor_open_named]).
    Cross-confirmed by [cas/130]. *)

(** ** 1. Monomial [x = y^k], [k] even *)

Theorem shape_even_ndiv_odd :
  forall a b, Z.Even a -> Z.Odd b -> ~ (a | b).
Proof.
  intros a b [ka Ha] [kb Hb] [t Ht].
  subst. nia.
Qed.

Theorem shape_monomial_k2_period_obstruction :
  forall e, ~ (40 | 2 * e - 1).
Proof.
  intros e. apply shape_even_ndiv_odd.
  - exists 20. reflexivity.
  - exists (e - 1). lia.
Qed.

Theorem shape_monomial_k2_pin :
  powm 36 2 187 = 174 /\
  powm 174 3 187 <> 36 /\
  powm 36 40 187 = 1.
Proof. vm_compute. repeat split; discriminate. Qed.

(** ** 2. Inverse [x = y^{-1}] *)

Theorem shape_inverse_of_36_residual_shaped :
  srsa_residual_leaf 187 80 36 26 39.
Proof.
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 19; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem shape_inverse_of_generator :
  powm 125 79 187 = 3 /\
  79 + 1 = 80.
Proof. vm_compute. split; reflexivity. Qed.

Theorem shape_inverse_generator_miller :
  Z.gcd (67 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

(** ** 3. Affine identity [x = a y + b] for all [y] *)

Theorem shape_affine_identity_forbidden :
  nth 1%nat (poly_Pe_minus_X poly_X 3%nat) 0 = -1 /\
  ~ (187 | -1).
Proof.
  split.
  - apply X3_minus_X_nth1.
  - intros [k Hk]. nia.
Qed.

Theorem shape_affine_eval_not_zero :
  poly_eval (poly_Pe_minus_X poly_X 3%nat) 2 = 6.
Proof. apply X3_minus_X_eval_2. Qed.

Theorem shape_affine_pointwise_const_residual :
  srsa_residual_leaf 187 80 36 42 3.
Proof. apply srsa_residual_pin. Qed.

(** ** 4. Two outputs at the same coprime [e] *)

Theorem shape_eth_root_of_1 :
  forall R x,
    Z.coprime x (rsa_N R) ->
    powm x (rsa_e R) (rsa_N R) = 1 ->
    x mod rsa_N R = 1.
Proof.
  intros R x Hcop Hx.
  pose proof (rsa_dec_enc_units R x Hcop) as Hrt.
  unfold rsa_dec, rsa_enc in Hrt.
  rewrite Hx in Hrt.
  assert (powm 1 (rsa_d R) (rsa_N R) = 1) as Hone.
  { unfold powm. pose proof (rsa_d_pos R). pose proof (rsa_N_gt_1 R).
    rewrite Z.pow_1_l by lia. apply Z.mod_1_l; lia. }
  rewrite Hone in Hrt. symmetry. exact Hrt.
Qed.

Theorem shape_unique_eth_root :
  forall R x y,
    Z.coprime x (rsa_N R) ->
    Z.coprime y (rsa_N R) ->
    powm x (rsa_e R) (rsa_N R) = powm y (rsa_e R) (rsa_N R) ->
    x mod rsa_N R = y mod rsa_N R.
Proof.
  intros R x y Hx Hy Heq.
  pose proof (rsa_dec_enc_units R x Hx) as H1.
  pose proof (rsa_dec_enc_units R y Hy) as H2.
  rewrite <- H1, <- H2. f_equal. unfold rsa_enc. exact Heq.
Qed.

Theorem shape_two_unit_cube_roots_agree :
  forall x z,
    Z.coprime x 187 ->
    Z.coprime z 187 ->
    powm x 3 187 = 36 ->
    powm z 3 187 = 36 ->
    x mod 187 = z mod 187.
Proof.
  intros x z Hx Hz Hxz Hzz.
  change 3 with (rsa_e rsa_test) in Hxz, Hzz.
  change 187 with (rsa_N rsa_test) in Hx, Hz, Hxz, Hzz |- *.
  apply (shape_unique_eth_root rsa_test); try assumption.
  rewrite Hxz, Hzz. reflexivity.
Qed.

Theorem shape_unique_unit_cube_root_of_36 :
  forall x,
    Z.coprime x 187 ->
    powm x 3 187 = 36 ->
    x mod 187 = 42.
Proof.
  intros x Hx Hx3.
  apply (shape_two_unit_cube_roots_agree x 42 Hx).
  - vm_compute. reflexivity.
  - exact Hx3.
  - vm_compute. reflexivity.
Qed.

(** ** 5. Franklin–Reiter: additive related at fixed [e] *)

Theorem shape_fr_small_integer :
  4 * 4 * 4 = 64 /\
  5 * 5 * 5 = 125 /\
  64 < 187 /\
  125 < 187 /\
  5 * 5 * 5 - 4 * 4 * 4 = 3 * 1 * 4 * 5 + 1.
Proof. repeat split; lia. Qed.

Theorem shape_fr_cube_gap_small :
  (4 + 1) * (4 + 1) * (4 + 1) - 4 * 4 * 4 =
    3 * 1 * 4 * (4 + 1) + 1 * 1 * 1.
Proof. apply fr_cube_gap. Qed.

Theorem shape_fr_residual_not_integer_cube :
  42 * 42 * 42 = 74088 /\
  74088 > 187 /\
  powm 42 3 187 = 36 /\
  74088 <> 36.
Proof. vm_compute. repeat split; lia || discriminate. Qed.

Theorem shape_fr_reduced_offset_not_integer :
  powm 41 3 187 = 105 /\
  41 * 41 * 41 <> 105.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

(** ** 6. Chaum-blind: sees [y r^e], returns [x r] *)

Theorem shape_chaum_unblind :
  rsa_unblind rsa_test (rsa_dec rsa_test (rsa_blind rsa_test 36 2)) 94 =
    rsa_dec rsa_test 36.
Proof.
  apply chaum_unblind_is_raw_sign.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Theorem shape_chaum_recovers_cube_root :
  rsa_unblind rsa_test (rsa_dec rsa_test (rsa_blind rsa_test 36 2)) 94 = 42.
Proof.
  rewrite shape_chaum_unblind.
  vm_compute. reflexivity.
Qed.

Theorem shape_chaum_e_is_protocol :
  rsa_e rsa_test = 3 /\
  rsa_blind rsa_test 36 2 = 101.
Proof. vm_compute. split; reflexivity. Qed.

(** ** 7. Jacobi-discrete [e(y) ∈ {3,5}] *)

Definition jacobi_discrete_e (y p q : Z) : Z :=
  if jacobi_N y p q =? 1 then 3 else 5.

Theorem shape_jacobi_e_on_square :
  jacobi_discrete_e 36 11 17 = 3 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof. split; [vm_compute; reflexivity | apply srsa_residual_pin]. Qed.

Theorem shape_jacobi_e_on_nonsquare :
  jacobi_discrete_e 2 11 17 = 5 /\
  Z.gcd 5 80 = 5 /\
  Z.gcd 5 80 <> 1.
Proof. vm_compute. repeat split; discriminate. Qed.

(** ** 8. Extra annihilator output [M] with [y^M ≡ 1] *)

Theorem shape_short_period_of_y_no_split :
  powm 36 40 187 = 1 /\
  Z.gcd (powm 36 40 187 - 1) 187 = 187 /\
  ~ Problem_Factor 187 187.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. intros [H _]. lia.
Qed.

Theorem shape_lambda_quality_miller :
  Z.gcd (67 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

(** ** 9. Extra [d] with [e d ≡ 1 (mod λ)] *)

Theorem shape_ed_minus_one_is_lambda :
  3 * 27 - 1 = 80 /\
  (3 * 27) mod 80 = 1.
Proof. split; reflexivity. Qed.

Theorem shape_ed_miller :
  Z.gcd (67 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof. apply shape_lambda_quality_miller. Qed.

(** ** 10. Euler inverse modulo [N−1], not [λ] *)

Theorem shape_e3_not_invertible_mod_Nminus1 :
  Z.gcd 3 186 = 3 /\
  Z.gcd 3 186 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem shape_wrong_euler_inv :
  Z.gcd 11 186 = 1 /\
  (11 * 17) mod 186 = 1 /\
  powm 36 17 187 = 53 /\
  powm 36 27 187 = 42 /\
  53 <> 42.
Proof. vm_compute. repeat split; discriminate. Qed.

(** ** 11. CRT-tape: [x = CRT(x_p, x_q)] *)

Theorem shape_crt_residues :
  42 mod 11 = 9 /\
  42 mod 17 = 8.
Proof. split; reflexivity. Qed.

Theorem shape_crt_recovers_root :
  crt2 11 17 9 8 = 42.
Proof. vm_compute. reflexivity. Qed.

Theorem shape_crt_moduli_are_factors :
  Problem_Factor 187 11 /\
  Problem_Factor 187 17.
Proof.
  split.
  - unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
  - unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

(** ** 12. Miller on [e−1] against the challenge [y] *)

Theorem shape_miller_e11_on_y_splits :
  Z.gcd (powm 36 10 187 - 1) 187 = 11 /\
  Problem_Factor 187 11 /\
  Z.gcd 11 80 = 1 /\
  ~ (80 | 10).
Proof.
  split; [vm_compute; reflexivity|].
  split.
  - unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
  - split; [reflexivity|]. intros [k Hk]. nia.
Qed.

Theorem shape_miller_e3_on_y_survives :
  Z.gcd (powm 36 2 187 - 1) 187 = 1 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof. split; [vm_compute; reflexivity | apply srsa_residual_pin]. Qed.

(** ** Public addition chain, polynomial [X], short bases, gcd-free multiply

    Joint machines that write [x] after a public [e], or from [y]
    by multiply-only of bounded length, or as [P(y)] of degree [≥2],
    or in the cyclic of a short public base list without SAGM-known
    exponents.  None hits leftover [x] except the trapdoor chain
    for [d=27].  Cross-confirmed by [cas/142]. *)

Theorem shape_public_chain_e3 :
  3 = 2 + 1 /\
  powm 36 2 187 = 174 /\
  (174 * 36) mod 187 = 93 /\
  93 <> 42 /\
  powm 93 3 187 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem shape_trapdoor_chain_d27 :
  27 = 16 + 8 + 2 + 1 /\
  powm 36 27 187 = 42.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem shape_poly_x_quadratic :
  poly_eval [1; 0; 1] 36 = 1297 /\
  1297 mod 187 = 175 /\
  powm 175 3 187 = 142 /\
  142 <> 36 /\
  Z.gcd (142 - 36) 187 = 1.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem shape_public_bases_2_3 :
  (2 * 3) mod 187 = 6 /\
  powm 6 3 187 = 29 /\
  29 <> 36 /\
  powm 2 3 187 = 8 /\
  8 <> 42 /\
  powm 2 27 187 = 161 /\
  161 <> 42.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem shape_gcdfree_bounded_from_y :
  36 <> 42 /\
  (36 * 36) mod 187 = 174 /\
  174 <> 42 /\
  (174 * 36) mod 187 = 93 /\
  93 <> 42.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem shape_public_exp_not_membership :
  powm 42 40 187 = 1 /\
  powm 42 186 187 = 64 /\
  64 <> 1.
Proof. vm_compute. repeat split; discriminate. Qed.
