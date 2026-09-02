From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import QRModN.
Require Import RabinWilliams.
Require Import CRTRSA.

Open Scope Z_scope.

(** * Hundred classes D–E (51–74)

    Extra outputs and multi-challenge combinations.
    Cross-confirmed by [cas/133]. *)

Theorem hun_51_extra_dp :
  (3 * 27 - 1) mod 10 = 0 /\
  (10 | 80).
Proof. split; [reflexivity|]. exists 8. reflexivity. Qed.

Theorem hun_52_fermat_difference :
  (11 - 17) * (11 - 17) = 28 * 28 - 4 * 187.
Proof. reflexivity. Qed.

Theorem hun_53_extra_sqrt_splits :
  6 * 6 = 36 /\
  Z.gcd (28 - 6) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_54_extra_order_is_lambda :
  powm 3 80 187 = 1 /\
  80 = lambda_semiprime 11 17.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_55_factor_e_minus_1 :
  10 = 2 * 5 /\
  Z.gcd (powm 36 10 187 - 1) 187 = 11.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem hun_56_factor_N_minus_1 :
  186 = 2 * 3 * 31.
Proof. reflexivity. Qed.

Theorem hun_57_wiener_d_not_small :
  27 > 4 /\
  4 * 4 * 4 * 4 = 256 /\
  256 > 187.
Proof. split; [lia|]. split; reflexivity. Qed.

Theorem hun_58_sequential_square_period :
  powm 2 80 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_59_height_mismatch :
  powm 2 10 11 = 1 /\
  powm 2 8 17 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_60_primitive_root_mod_p :
  powm 2 10 11 = 1 /\
  powm 2 5 11 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_61_half_bits :
  42 / 8 = 5 /\
  42 mod 8 = 2.
Proof. split; reflexivity. Qed.

Theorem hun_62_cubic_symbol_vacuous :
  jacobi_N 36 11 17 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_63_inverse_challenge :
  powm 49 3 187 = 26 /\
  (42 * 49) mod 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_64_neg_y :
  (-36) mod 187 = 151.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_65_two_y :
  2 * 36 = 72.
Proof. reflexivity. Qed.

Theorem hun_66_three_powers_gcd :
  Z.gcd 3 5 = 1.
Proof. reflexivity. Qed.

Theorem hun_67_y_plus_1_root :
  powm 126 3 187 = 37.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_68_batch_gcd_of_roots :
  Z.gcd (42 - 60) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_69_adaptive_lambda_plus_one :
  80 + 1 = 81 /\
  powm 2 81 187 = 2.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem hun_70_same_y_two_moduli :
  Z.gcd 187 247 = 1 /\
  36 mod 247 = 36.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem hun_71_twin_exponents :
  Z.gcd 3 (3 + 2) = 1.
Proof. reflexivity. Qed.

Theorem hun_72_product_of_leftovers :
  (42 * 60) mod 187 = 89 /\
  powm 89 3 187 = 166 /\
  166 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_73_rerand_forces_fixed_e :
  rsa_e rsa_test = 3.
Proof. reflexivity. Qed.

Theorem hun_74_coins_independent_fixed_e :
  rsa_e rsa_test = 3 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof. split; [reflexivity | apply srsa_residual_pin]. Qed.
