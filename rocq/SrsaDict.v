From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import ArithShape.

Open Scope Z_scope.

(** * Residual dictionary, cubing cycles, SAGM on [y]

    Each generator of [⟨y⟩] is leftover [x] for two residual [e]
    ([e] and [e+40]).  Cubing is an automorphism of order [4] in
    [(ℤ/40ℤ)*], hence four 4-cycles on the 16 generators.  Residual
    cube is SAGM [(a,e)=(27,3)] on the challenge: [ae−1=λ]. *)

Theorem dict_e_eq_d :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_e43_same_x_leaf :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_N_mod_40_is_d :
  pin187_N mod pin187_y_ord = pin187_d.
Proof. reflexivity. Qed.

Theorem dict_public_N_mod_40 :
  pin187_N mod pin187_y_ord = pin187_d /\
  powm pin187_y pin187_d pin187_N = pin187_x.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem dict_y_to_d :
  powm pin187_y pin187_d pin187_N = pin187_x.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_x93_e67 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_x25_e11 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_x25_e51 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_x15_e29 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_x15_e69 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_x168_e61 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_x104_e57 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_x185_e53 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_xy_e41 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_y_lambda_type :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_e_plus_80 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_phi80 :
  80 / 2 * 4 / 5 = 32.
Proof. reflexivity. Qed.

Theorem dict_phi40 :
  40 / 2 * 4 / 5 = 16.
Proof. reflexivity. Qed.

Theorem dict_two_e_per_x :
  32 / 16 = 2.
Proof. reflexivity. Qed.

Theorem dict_e_mod_40 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_kernel_1_41 :
  1 mod 40 = 1 /\
  41 mod 40 = 1 /\
  Z.gcd 41 80 = 1.
Proof. repeat split; reflexivity. Qed.

Theorem dict_cube_bij_on_cyc :
  Z.gcd 3 40 = 1.
Proof. reflexivity. Qed.

Theorem dict_27th_is_inverse_auto :
  Z.gcd pin187_d pin187_y_ord = 1 /\
  (pin187_e * pin187_d) mod pin187_y_ord = 1.
Proof. split; reflexivity. Qed.

Theorem dict_compose_autos :
  powm pin187_y pin187_d pin187_N = pin187_x /\
  powm pin187_x pin187_e pin187_N = pin187_y.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_ae_is_lambda_plus_1 :
  27 * 3 = 80 + 1.
Proof. reflexivity. Qed.

Theorem dict_bits_of_27 :
  16 + 8 + 2 + 1 = 27.
Proof. reflexivity. Qed.

Theorem dict_binary_product :
  powm pin187_y 16 pin187_N = 69 /\
  powm pin187_y 8 pin187_N = 137 /\
  powm pin187_y 2 pin187_N = 174 /\
  (69 * 137 * 174 * pin187_y) mod pin187_N = pin187_x.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem dict_add_chain_y6 :
  powm pin187_y 6 pin187_N = 47.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_add_chain_y12 :
  powm pin187_y 12 pin187_N = 152.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_add_chain_y24 :
  powm pin187_y 24 pin187_N = 103.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_k_odd :
  Z.odd 27 = true.
Proof. reflexivity. Qed.

Theorem dict_hamming_27 :
  27 = 2 ^ 0 + 2 ^ 1 + 2 ^ 3 + 2 ^ 4.
Proof. reflexivity. Qed.

Theorem dict_naf_shape :
  32 - 4 - 1 = pin187_d /\
  powm pin187_y 32 pin187_N = 86 /\
  powm pin187_y 4 pin187_N = 169.
Proof. split; [reflexivity|]. vm_compute. split; reflexivity. Qed.

Theorem dict_y25 :
  powm pin187_y 25 pin187_N = 155.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_y16_is_g5sq :
  powm pin187_y 16 pin187_N = 69 /\
  powm 137 2 pin187_N = 69.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_sagm_on_y :
  27 * 3 - 1 = 80.
Proof. reflexivity. Qed.

Theorem dict_y81 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_ae_lambda_plus_1 :
  27 * 3 = 80 + 1.
Proof. reflexivity. Qed.

Theorem dict_e43_same_x :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_e83_same_x :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_e43_minus_3 :
  (43 - 3) mod 40 = 0.
Proof. reflexivity. Qed.

Theorem dict_e83_minus_3 :
  (83 - 3) mod 80 = 0.
Proof. reflexivity. Qed.

Theorem dict_e67_coprime :
  Z.gcd 67 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_e51_coprime :
  Z.gcd 51 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_e61_coprime :
  Z.gcd 61 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_e57_coprime :
  Z.gcd 57 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_e29_coprime :
  Z.gcd 29 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_e39_coprime :
  Z.gcd 39 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_x26_e39 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem dict_self_inverse_11 :
  (11 * 11) mod 40 = 1.
Proof. reflexivity. Qed.

Theorem dict_sagm_ae_minus_1 :
  27 * 3 - 1 = 80.
Proof. reflexivity. Qed.

Theorem dict_inv_mod_40 :
  (pin187_e * pin187_d) mod pin187_lam = 1.
Proof. reflexivity. Qed.

Theorem dict_inv_mod_lam :
  (pin187_e * pin187_d) mod pin187_lam = 1.
Proof. reflexivity. Qed.

Theorem dict_cycle_70_cube :
  powm 70 pin187_e pin187_N = pin187_x.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle_42_cube :
  powm pin187_x pin187_e pin187_N = pin187_y.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle_36_cube :
  powm pin187_y pin187_e pin187_N = 93.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle_93_cube :
  powm 93 pin187_e pin187_N = 70.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_three_order_4_mod_40 :
  (3 * 3 * 3 * 3) mod 40 = 1.
Proof. reflexivity. Qed.

Theorem dict_27_order_4_mod_40 :
  (27 * 27 * 27 * 27) mod 40 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle2_9 :
  powm 9 pin187_e pin187_N = 168.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle2_168 :
  powm 168 pin187_e pin187_N = 60.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle2_15 :
  powm 15 pin187_e pin187_N = 9.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_k27_coords :
  27 mod 8 = 3 /\
  27 mod 5 = 2.
Proof. split; reflexivity. Qed.

Theorem dict_e3_coords :
  3 mod 8 = 3 /\
  3 mod 5 = 3.
Proof. split; reflexivity. Qed.

Theorem dict_3_order_4_mod_40 :
  (3 ^ 4) mod 40 = 1 /\
  (3 ^ 2) mod 40 <> 1.
Proof. split; [reflexivity | vm_compute; discriminate]. Qed.

Theorem dict_cube_root_of_2 :
  powm 2 pin187_d pin187_N = 161 /\
  powm 161 pin187_e pin187_N = 2.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_sagm_of_3 :
  powm pin187_g pin187_d pin187_N = 75 /\
  powm 75 pin187_e pin187_N = 3.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_75_not_42 :
  75 <> 42.
Proof. discriminate. Qed.

Theorem dict_cycle2_60 :
  powm 60 pin187_e pin187_N = 15.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle3_25 :
  powm 25 pin187_e pin187_N = 104.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle3_104 :
  powm 104 pin187_e pin187_N = 59.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle3_59 :
  powm 59 pin187_e pin187_N = 53.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle3_53 :
  powm 53 pin187_e pin187_N = 25.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle4_49 :
  powm 49 pin187_e pin187_N = 26.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle4_26 :
  powm 26 pin187_e pin187_N = 185.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle4_185 :
  powm 185 pin187_e pin187_N = 179.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle4_179 :
  powm 179 pin187_e pin187_N = 49.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cbrt_2_in_ltwo :
  powm 2 pin187_d pin187_N = 161 /\
  powm 161 pin187_e pin187_N = 2.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_cbrt_3_in_lthree :
  powm pin187_g pin187_d pin187_N = 75 /\
  powm 75 pin187_e pin187_N = 3.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_cbrt_36_in_ly :
  powm pin187_y pin187_d pin187_N = pin187_x /\
  powm pin187_x pin187_e pin187_N = pin187_y.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_three_x_for_k27 :
  161 <> 42 /\
  75 <> 42.
Proof. split; discriminate. Qed.
