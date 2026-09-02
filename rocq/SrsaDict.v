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
  Z.gcd 27 80 = 1 /\
  powm 93 27 187 = 36 /\
  srsa_residual_leaf 187 80 36 93 27.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 13; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem dict_e43_same_x_leaf :
  Z.gcd 43 80 = 1 /\
  powm 42 43 187 = 36 /\
  srsa_residual_leaf 187 80 36 42 43.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 21; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem dict_N_mod_40_is_d :
  187 mod 40 = 27.
Proof. reflexivity. Qed.

Theorem dict_public_N_mod_40 :
  187 mod 40 = 27 /\
  powm 36 27 187 = 42.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem dict_y_to_d :
  powm 36 27 187 = 42.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_x93_e67 :
  powm 93 67 187 = 36 /\
  srsa_residual_leaf 187 80 36 93 67.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 33; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem dict_x25_e11 :
  powm 25 11 187 = 36 /\
  srsa_residual_leaf 187 80 36 25 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 5; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem dict_x25_e51 :
  powm 25 51 187 = 36 /\
  srsa_residual_leaf 187 80 36 25 51.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 25; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem dict_x15_e29 :
  powm 15 29 187 = 36 /\
  srsa_residual_leaf 187 80 36 15 29.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 14; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem dict_x15_e69 :
  powm 15 69 187 = 36 /\
  srsa_residual_leaf 187 80 36 15 69.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 34; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem dict_x168_e61 :
  powm 168 61 187 = 36 /\
  srsa_residual_leaf 187 80 36 168 61.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 30; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem dict_x104_e57 :
  powm 104 57 187 = 36 /\
  srsa_residual_leaf 187 80 36 104 57.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 28; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem dict_x185_e53 :
  powm 185 53 187 = 36 /\
  srsa_residual_leaf 187 80 36 185 53.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 26; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem dict_xy_e41 :
  powm 36 41 187 = 36 /\
  srsa_residual_leaf 187 80 36 36 41.
Proof.
  split; [vm_compute; reflexivity|].
  apply arith_xy_period_residual.
Qed.

Theorem dict_y_lambda_type :
  powm 36 81 187 = 36 /\
  (80 | 81 - 1).
Proof. split; [vm_compute; reflexivity|]. exists 1. reflexivity. Qed.

Theorem dict_e_plus_80 :
  powm 42 83 187 = 36.
Proof. vm_compute. reflexivity. Qed.

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
  powm 42 3 187 = 36 /\
  powm 42 43 187 = 36.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_kernel_1_41 :
  1 mod 40 = 1 /\
  41 mod 40 = 1 /\
  Z.gcd 41 80 = 1.
Proof. repeat split; reflexivity. Qed.

Theorem dict_cube_bij_on_cyc :
  Z.gcd 3 40 = 1.
Proof. reflexivity. Qed.

Theorem dict_27th_is_inverse_auto :
  Z.gcd 27 40 = 1 /\
  (3 * 27) mod 40 = 1.
Proof. split; reflexivity. Qed.

Theorem dict_compose_autos :
  powm 36 27 187 = 42 /\
  powm 42 3 187 = 36.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_ae_is_lambda_plus_1 :
  27 * 3 = 80 + 1.
Proof. reflexivity. Qed.

Theorem dict_bits_of_27 :
  16 + 8 + 2 + 1 = 27.
Proof. reflexivity. Qed.

Theorem dict_binary_product :
  powm 36 16 187 = 69 /\
  powm 36 8 187 = 137 /\
  powm 36 2 187 = 174 /\
  (69 * 137 * 174 * 36) mod 187 = 42.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem dict_add_chain_y6 :
  powm 36 6 187 = 47.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_add_chain_y12 :
  powm 36 12 187 = 152.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_add_chain_y24 :
  powm 36 24 187 = 103.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_k_odd :
  Z.odd 27 = true.
Proof. reflexivity. Qed.

Theorem dict_hamming_27 :
  27 = 2 ^ 0 + 2 ^ 1 + 2 ^ 3 + 2 ^ 4.
Proof. reflexivity. Qed.

Theorem dict_naf_shape :
  32 - 4 - 1 = 27 /\
  powm 36 32 187 = 86 /\
  powm 36 4 187 = 169.
Proof. split; [reflexivity|]. vm_compute. split; reflexivity. Qed.

Theorem dict_y25 :
  powm 36 25 187 = 155.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_y16_is_g5sq :
  powm 36 16 187 = 69 /\
  powm 137 2 187 = 69.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_sagm_on_y :
  27 * 3 - 1 = 80.
Proof. reflexivity. Qed.

Theorem dict_y81 :
  powm 36 81 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_ae_lambda_plus_1 :
  27 * 3 = 80 + 1.
Proof. reflexivity. Qed.

Theorem dict_e43_same_x :
  powm 42 43 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_e83_same_x :
  powm 42 83 187 = 36.
Proof. vm_compute. reflexivity. Qed.

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
  powm 26 39 187 = 36 /\
  srsa_residual_leaf 187 80 36 26 39.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 19; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem dict_self_inverse_11 :
  (11 * 11) mod 40 = 1.
Proof. reflexivity. Qed.

Theorem dict_sagm_ae_minus_1 :
  27 * 3 - 1 = 80.
Proof. reflexivity. Qed.

Theorem dict_inv_mod_40 :
  (3 * 27) mod 40 = 1.
Proof. reflexivity. Qed.

Theorem dict_inv_mod_lam :
  (3 * 27) mod 80 = 1.
Proof. reflexivity. Qed.

Theorem dict_cycle_70_cube :
  powm 70 3 187 = 42.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle_42_cube :
  powm 42 3 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle_36_cube :
  powm 36 3 187 = 93.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle_93_cube :
  powm 93 3 187 = 70.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_three_order_4_mod_40 :
  (3 * 3 * 3 * 3) mod 40 = 1.
Proof. reflexivity. Qed.

Theorem dict_27_order_4_mod_40 :
  (27 * 27 * 27 * 27) mod 40 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle2_9 :
  powm 9 3 187 = 168.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle2_168 :
  powm 168 3 187 = 60.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle2_15 :
  powm 15 3 187 = 9.
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
  powm 2 27 187 = 161 /\
  powm 161 3 187 = 2.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_sagm_of_3 :
  powm 3 27 187 = 75 /\
  powm 75 3 187 = 3.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_75_not_42 :
  75 <> 42.
Proof. discriminate. Qed.

Theorem dict_cycle2_60 :
  powm 60 3 187 = 15.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle3_25 :
  powm 25 3 187 = 104.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle3_104 :
  powm 104 3 187 = 59.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle3_59 :
  powm 59 3 187 = 53.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle3_53 :
  powm 53 3 187 = 25.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle4_49 :
  powm 49 3 187 = 26.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle4_26 :
  powm 26 3 187 = 185.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle4_185 :
  powm 185 3 187 = 179.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cycle4_179 :
  powm 179 3 187 = 49.
Proof. vm_compute. reflexivity. Qed.

Theorem dict_cbrt_2_in_ltwo :
  powm 2 27 187 = 161 /\
  powm 161 3 187 = 2.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_cbrt_3_in_lthree :
  powm 3 27 187 = 75 /\
  powm 75 3 187 = 3.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_cbrt_36_in_ly :
  powm 36 27 187 = 42 /\
  powm 42 3 187 = 36.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dict_three_x_for_k27 :
  161 <> 42 /\
  75 <> 42.
Proof. split; discriminate. Qed.
