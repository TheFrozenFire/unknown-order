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
  powm pin_y 2 pin_N = 174 /\
  powm 174 pin_e pin_N <> pin_y /\
  powm pin_y pin_y_ord pin_N = 1.
Proof. vm_compute. repeat split; discriminate. Qed.

(** ** 2. Inverse [x = y^{-1}] *)

Theorem shape_inverse_of_36_residual_shaped :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem shape_inverse_of_generator :
  (powm pin_g (pin_lam - 1) pin_N * pin_g) mod pin_N = 1 /\
  pin_lam - 1 + 1 = pin_lam.
Proof. vm_compute. split; [reflexivity | lia]. Qed.

Theorem shape_inverse_generator_miller :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

(** ** 3. Affine identity [x = a y + b] for all [y] *)

Theorem shape_affine_identity_forbidden :
  nth 1%nat (poly_Pe_minus_X poly_X 3%nat) 0 = -1 /\
  ~ (pin_N | -1).
Proof.
  split.
  - apply X3_minus_X_nth1.
  - intros [k Hk]. nia.
Qed.

Theorem shape_affine_eval_not_zero :
  poly_eval (poly_Pe_minus_X poly_X 3%nat) 2 = 6.
Proof. apply X3_minus_X_eval_2. Qed.

Theorem shape_affine_pointwise_const_residual :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
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
    Z.coprime x pin_N ->
    Z.coprime z pin_N ->
    powm x pin_e pin_N = pin_y ->
    powm z pin_e pin_N = pin_y ->
    x mod pin_N = z mod pin_N.
Proof.
  intros x z Hx Hz Hxz Hzz.
  change pin_e with (rsa_e rsa_test) in Hxz, Hzz.
  change pin_N with (rsa_N rsa_test) in Hx, Hz, Hxz, Hzz |- *.
  apply (shape_unique_eth_root rsa_test); try assumption.
  rewrite Hxz, Hzz. reflexivity.
Qed.

Theorem shape_unique_unit_cube_root_of_36 :
  forall x,
    Z.coprime x pin_N ->
    powm x pin_e pin_N = pin_y ->
    x mod pin_N = pin_x.
Proof.
  intros x Hx Hx3.
  apply (shape_two_unit_cube_roots_agree x pin_x Hx).
  - vm_compute. reflexivity.
  - exact Hx3.
  - vm_compute. reflexivity.
Qed.

(** ** 5. Franklin–Reiter: additive related at fixed [e] *)

Theorem shape_fr_small_integer :
  4 * 4 * 4 = 64 /\
  5 * 5 * 5 = 125 /\
  64 < pin_N /\
  125 < pin_N /\
  5 * 5 * 5 - 4 * 4 * 4 = 3 * 1 * 4 * 5 + 1.
Proof. repeat split; lia. Qed.

Theorem shape_fr_cube_gap_small :
  (4 + 1) * (4 + 1) * (4 + 1) - 4 * 4 * 4 =
    3 * 1 * 4 * (4 + 1) + 1 * 1 * 1.
Proof. apply fr_cube_gap. Qed.

Theorem shape_fr_residual_not_integer_cube :
  pin_x * pin_x * pin_x = 74088 /\
  74088 > pin_N /\
  powm pin_x pin_e pin_N = pin_y /\
  74088 <> pin_y.
Proof. vm_compute. repeat split; lia || discriminate. Qed.

Theorem shape_fr_reduced_offset_not_integer :
  powm pin_x pin_e pin_N = pin_y /\
  pin_x * pin_x * pin_x <> pin_y.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

(** ** 6. Chaum-blind: sees [y r^e], returns [x r] *)

Theorem shape_chaum_unblind :
  rsa_unblind rsa_test (rsa_dec rsa_test (rsa_blind rsa_test pin_y 2))
    ((pin_N + 1) / 2) =
    rsa_dec rsa_test pin_y.
Proof.
  apply chaum_unblind_is_raw_sign.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Theorem shape_chaum_recovers_cube_root :
  rsa_dec rsa_test pin_y = pin_x.
Proof. vm_compute. reflexivity. Qed.

Theorem shape_chaum_e_is_protocol :
  rsa_e rsa_test = pin_e.
Proof. reflexivity. Qed.

(** ** 7. Jacobi-discrete [e(y) ∈ {3,5}] *)

Definition jacobi_discrete_e (y p q : Z) : Z :=
  if jacobi_N y p q =? 1 then 3 else 5.

Theorem shape_jacobi_e_on_square :
  jacobi_discrete_e pin_y pin_p pin_q = 3 /\
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. split; [vm_compute; reflexivity | apply srsa_residual_pin]. Qed.

Theorem shape_jacobi_e_on_nonsquare :
  jacobi_discrete_e 2 pin_p pin_q = 5 /\
  Z.gcd 2 pin_lam = 2 /\
  Z.gcd 2 pin_lam <> 1.
Proof. vm_compute. repeat split; discriminate. Qed.

(** ** 8. Extra annihilator output [M] with [y^M ≡ 1] *)

Theorem shape_short_period_of_y_no_split :
  powm pin_y pin_y_ord pin_N = 1 /\
  Z.gcd (powm pin_y pin_y_ord pin_N - 1) pin_N = pin_N /\
  ~ Problem_Factor pin_N pin_N.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. intros [H _]. lia.
Qed.

Theorem shape_lambda_quality_miller :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

(** ** 9. Extra [d] with [e d ≡ 1 (mod λ)] *)

Theorem shape_ed_minus_one_is_lambda :
  (pin_e * pin_d) mod pin_lam = 1 /\
  (pin_e * pin_d) mod pin_lam = 1.
Proof. split; reflexivity. Qed.

Theorem shape_ed_miller :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

(** ** 10. Euler inverse modulo [N−1], not [λ] *)

Theorem shape_e3_not_invertible_mod_Nminus1 :
  Z.gcd pin_e (pin_N - 1) = 3 /\
  Z.gcd pin_e (pin_N - 1) <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem shape_wrong_euler_inv :
  Z.gcd pin_p (pin_N - 1) = 1 /\
  pin_N mod (pin_N - 1) = 1 /\
  powm pin_y pin_q pin_N = 53 /\
  powm pin_y pin_d pin_N = pin_x /\
  53 <> pin_x.
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
  Problem_Factor pin_N pin_p /\
  Problem_Factor pin_N pin_q.
Proof.
  split.
  - unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
  - unfold Problem_Factor. split; [lia|]. exists pin_p. reflexivity.
Qed.

(** ** 12. Miller on [e−1] against the challenge [y] *)

Theorem shape_miller_e11_on_y_splits :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem shape_miller_e3_on_y_survives :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

(** ** Public addition chain, polynomial [X], short bases, gcd-free multiply

    Joint machines that write [x] after a public [e], or from [y]
    by multiply-only of bounded length, or as [P(y)] of degree [≥2],
    or in the cyclic of a short public base list without SAGM-known
    exponents.  None hits leftover [x] except the trapdoor chain
    for [d=27].  Cross-confirmed by [cas/142]. *)

Theorem shape_public_chain_e3 :
  pin_e = 2 + 1 /\
  powm pin_y 2 pin_N = 174 /\
  (174 * pin_y) mod pin_N = 93 /\
  93 <> pin_x /\
  powm 93 pin_e pin_N <> pin_y.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem shape_trapdoor_chain_d27 :
  pin_d = 16 + 8 + 2 + 1 /\
  powm pin_y pin_d pin_N = pin_x.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem shape_poly_x_quadratic :
  poly_eval [1; 0; 1] pin_y = 1297 /\
  1297 mod pin_N = 175 /\
  powm 175 pin_e pin_N = 142 /\
  142 <> pin_y /\
  Z.gcd (142 - pin_y) pin_N = 1.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem shape_public_bases_2_3 :
  (2 * 3) mod pin_N = 6 /\
  powm 6 pin_e pin_N = 29 /\
  29 <> pin_y /\
  powm 2 pin_e pin_N = 8 /\
  8 <> pin_x /\
  powm 2 pin_d pin_N = 161 /\
  161 <> pin_x.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem shape_gcdfree_bounded_from_y :
  pin_y <> pin_x /\
  (pin_y * pin_y) mod pin_N = 174 /\
  174 <> pin_x /\
  (174 * pin_y) mod pin_N = 93 /\
  93 <> pin_x.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem shape_public_exp_not_membership :
  powm pin_x pin_y_ord pin_N = 1 /\
  powm pin_x (pin_N - 1) pin_N = 64 /\
  64 <> 1.
Proof. vm_compute. repeat split; discriminate. Qed.
