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
  Z.gcd 25 80 = 5 /\
  Z.gcd 25 80 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem emap_lambda_y_even :
  Z.lcm 2 6 = 6 /\
  Z.even 6 = true.
Proof. split; reflexivity. Qed.

Theorem emap_bitlength_even :
  1 + 5 = 6 /\
  Z.even 6 = true.
Proof. split; reflexivity. Qed.

Theorem emap_tau_leftover_e9 :
  Z.gcd 9 80 = 1 /\
  srsa_residual_leaf pin_N 80 36 (powm 36 9 pin_N) 9.
Proof. split; [reflexivity|]. apply filter_lowbit_e9_residual. Qed.

Theorem emap_sigma_leftover :
  Z.gcd 91 80 = 1 /\
  powm 25 91 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 25 91.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 45; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

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
  srsa_residual_leaf pin_N 80 36 42 3.
Proof. apply srsa_residual_pin. Qed.

Theorem emap_y_plus_1_is_nextprime :
  36 + 1 = 37 /\
  36 < 37 /\
  Z.gcd 37 80 = 1.
Proof. split; [reflexivity|]. split; [lia | reflexivity]. Qed.

Theorem emap_odd_part_e9 :
  36 / 4 = 9 /\
  Z.gcd 9 80 = 1.
Proof. split; reflexivity. Qed.

Theorem emap_odd_hamming_shares :
  2 * 2 + 1 = 5 /\
  Z.gcd 5 80 = 5.
Proof. split; reflexivity. Qed.

Theorem emap_gcd_yminus1_Nminus1 :
  Z.gcd (36 - 1) (pin_N - 1) = 1.
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
  Z.gcd 5 80 = 5.
Proof. split; [reflexivity|]. split; reflexivity. Qed.

Theorem emap_mersenne_leftover :
  Z.gcd 63 80 = 1 /\
  powm 9 63 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 9 63.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 31; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_N_mod_y_hits_e7 :
  pin_N mod 36 = 7 /\
  srsa_residual_leaf pin_N 80 36 60 7.
Proof. split; [reflexivity|]. apply arith_e7_residual. Qed.

Theorem emap_fermatish_leftover :
  2 ^ 5 + 1 = 33 /\
  Z.gcd 33 80 = 1 /\
  powm 53 33 pin_N = 36.
Proof. split; [reflexivity|]. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem emap_smooth_even :
  2 * 3 * 5 = 30 /\
  Z.even 30 = true.
Proof. split; reflexivity. Qed.

Theorem emap_e_eq_N :
  Z.gcd pin_N 80 = 1 /\
  ~ (80 | 186).
Proof. split; [reflexivity|]. intros [k Hk]. nia. Qed.

Theorem emap_e_eq_Nminus2 :
  Z.gcd (pin_N - 2) 80 = 5 /\
  Z.gcd 185 80 <> 1.
Proof. split; [vm_compute; reflexivity | discriminate]. Qed.

Theorem emap_e_y_minus_1_shares :
  Z.gcd 35 80 = 5 /\
  Z.gcd 35 80 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem emap_e_two_y_plus_1 :
  Z.gcd 73 80 = 1 /\
  powm 53 73 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 53 73.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 36; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_e_two_y_minus_1 :
  Z.gcd 71 80 = 1 /\
  powm 179 71 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 179 71.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 35; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_prevprime_e31 :
  Z.gcd 31 80 = 1 /\
  powm 179 31 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 179 31.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 15; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_dedekind_psi_even :
  36 * 3 / 2 * 4 / 3 = 72 /\
  Z.even 72 = true.
Proof. split; reflexivity. Qed.

Theorem emap_ord_y_even :
  powm 36 40 pin_N = 1 /\
  Z.even 40 = true.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem emap_phi_N_even :
  Z.even 160 = true.
Proof. reflexivity. Qed.

Theorem emap_aliquot_shares :
  91 - 36 = 55 /\
  Z.gcd 55 80 = 5.
Proof. split; reflexivity. Qed.

Theorem emap_e17_leftover :
  Z.gcd 17 80 = 1 /\
  powm 104 17 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 104 17.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 8; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_e_N_plus_1_even :
  Z.even (pin_N + 1) = true.
Proof. reflexivity. Qed.

Theorem emap_e_N_minus_1_even :
  Z.even (pin_N - 1) = true.
Proof. reflexivity. Qed.

Theorem emap_e_lam_minus_1 :
  Z.gcd 79 80 = 1 /\
  powm 26 79 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 26 79.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 39; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_phi_y_plus_1 :
  Z.gcd 13 80 = 1 /\
  powm 185 13 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 185 13.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 6; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_digit_sum_e9 :
  3 + 6 = 9 /\
  Z.gcd 9 80 = 1 /\
  srsa_residual_leaf pin_N 80 36 (powm 36 9 pin_N) 9.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  apply filter_lowbit_e9_residual.
Qed.

Theorem emap_repunit_111 :
  Z.gcd 111 80 = 1 /\
  powm 179 111 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 179 111.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 55; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_primorial_even :
  2 * 3 * 5 * 7 = 210 /\
  Z.even 210 = true.
Proof. split; reflexivity. Qed.

Theorem emap_fermat_5_shares :
  Z.gcd 5 80 = 5 /\
  Z.gcd 5 80 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem emap_collatz_e21 :
  Z.gcd 21 80 = 1 /\
  powm 168 21 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 168 21.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 10; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_squarefree_core_e9 :
  36 / 4 = 9 /\
  Z.gcd 9 80 = 1.
Proof. split; reflexivity. Qed.

Theorem emap_e47_second_leftover :
  Z.gcd 47 80 = 1 /\
  powm 60 47 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 60 47.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 23; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_e23_ninth :
  Z.gcd 23 80 = 1 /\
  powm 9 23 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 9 23.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 11; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_e19_leftover :
  Z.gcd 19 80 = 1 /\
  powm 59 19 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 59 19.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 9; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_e_eq_x :
  Z.gcd 59 80 = 1 /\
  powm 59 59 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 59 59.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 29; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_e_N_minus_lam :
  Z.gcd 107 80 = 1 /\
  powm 93 107 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 93 107.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 53; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem emap_e_nextprime_N :
  Z.gcd 191 80 = 1 /\
  Z.odd 191 = true.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem emap_prevprime_even_peel :
  pin_N - 6 = 181 /\
  powm 181 2 pin_N = 36 /\
  Z.even 2 = true.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem emap_e_prime :
  Z.odd 3 = true /\
  Z.gcd 3 80 = 1.
Proof. split; reflexivity. Qed.

Theorem emap_prime_e7 :
  powm 60 7 pin_N = 36 /\
  srsa_residual_leaf pin_N 80 36 60 7.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 3; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.
