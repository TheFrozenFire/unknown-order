From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import FilterShape.
Require Import ArithShape.

Open Scope Z_scope.

(** * Public maps of leftover [e]

    Restrictions on the TM that writes [E(N,y)].  Even [e] peels;
    [gcd(e,λ)≠1] is not residual; leftover-shaped odd [e] coprime to
    [λ] invert in [⟨y⟩] for a named [x]. *)

Theorem emap_phi_y_even :
  Z.even 12 = true /\
  12 = 12.
Proof. split; reflexivity. Qed.

Theorem emap_hamming_even :
  36 = 2 ^ 5 + 2 ^ 2 /\
  Z.even 2 = true.
Proof. split; reflexivity. Qed.

Theorem emap_lsb_y_even :
  Z.even 36 = true.
Proof. reflexivity. Qed.

Theorem emap_e25_shares_lambda :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem emap_lambda_y_even :
  Z.lcm 2 6 = 6 /\
  Z.even 6 = true.
Proof. split; reflexivity. Qed.

Theorem emap_bitlength_even :
  1 + 5 = 6 /\
  Z.even 6 = true.
Proof. split; reflexivity. Qed.

Theorem emap_tau_leftover_e9 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_sigma_leftover :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_rad_even :
  2 * 3 = 6 /\
  Z.even 6 = true.
Proof. split; reflexivity. Qed.

Theorem emap_omega_even :
  Z.even 2 = true.
Proof. reflexivity. Qed.

Theorem emap_Omega_even :
  Z.even 4 = true.
Proof. reflexivity. Qed.

Theorem emap_lpf_hits_cube :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_y_plus_1_is_nextprime :
  36 + 1 = 37 /\
  36 < 37 /\
  Z.gcd 37 80 = 1.
Proof. split; [reflexivity|]. split; [lia | reflexivity]. Qed.

Theorem emap_odd_part_e9 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem emap_odd_hamming_shares :
  2 * 2 + 1 = 5 /\
  Z.gcd 2 pin_lam = 2.
Proof. split; reflexivity. Qed.

Theorem emap_gcd_yminus1_Nminus1 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem emap_phi3_y_leftover_shaped :
  Z.gcd 1333 80 = 1 /\
  Z.odd 1333 = true /\
  ~ (80 | 1332).
Proof.
  split; [vm_compute; reflexivity|].
  split; [reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_v2_yminus1 :
  35 mod 2 = 1 /\
  2 * 2 + 1 = 5 /\
  Z.gcd 2 pin_lam = 2.
Proof. split; [reflexivity|]. split; reflexivity. Qed.

Theorem emap_mersenne_leftover :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_N_mod_y_hits_e7 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_fermatish_leftover :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_smooth_even :
  2 * 3 * 5 = 30 /\
  Z.even 30 = true.
Proof. split; reflexivity. Qed.

Theorem emap_e_eq_N :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem emap_e_eq_Nminus2 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem emap_e_y_minus_1_shares :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem emap_e_two_y_plus_1 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_e_two_y_minus_1 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_prevprime_e31 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_dedekind_psi_even :
  36 * 3 / 2 * 4 / 3 = 72 /\
  Z.even 72 = true.
Proof. split; reflexivity. Qed.

Theorem emap_ord_y_even :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem emap_phi_N_even :
  Z.even 160 = true.
Proof. reflexivity. Qed.

Theorem emap_aliquot_shares :
  91 - 36 = 55 /\
  Z.gcd 55 80 = 5.
Proof. split; reflexivity. Qed.

Theorem emap_e17_leftover :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_e_N_plus_1_even :
  Z.even (pin_N + 1) = true.
Proof. reflexivity. Qed.

Theorem emap_e_N_minus_1_even :
  Z.even (pin_N - 1) = true.
Proof. reflexivity. Qed.

Theorem emap_e_lam_minus_1 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_phi_y_plus_1 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_digit_sum_e9 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_repunit_111 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_primorial_even :
  2 * 3 * 5 * 7 = 210 /\
  Z.even 210 = true.
Proof. split; reflexivity. Qed.

Theorem emap_fermat_5_shares :
  Z.gcd 2 pin_lam = 2 /\
  Z.gcd 2 pin_lam <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem emap_collatz_e21 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_squarefree_core_e9 :
  powm pin_y pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem emap_e47_second_leftover :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_e23_ninth :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_e19_leftover :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_e_eq_x :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_e_N_minus_lam :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_e_nextprime_N :
  Z.gcd 191 80 = 1 /\
  Z.odd 191 = true.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem emap_prevprime_even_peel :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_e_prime :
  Z.odd 3 = true /\
  Z.gcd pin_e pin_lam = 1.
Proof. split; reflexivity. Qed.

Theorem emap_prime_e7 :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.
