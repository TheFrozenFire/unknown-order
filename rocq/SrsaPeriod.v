From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Period: gcd vs multiply

    The same exponents, two TMs.  [gcd(y^k−1,N)] for [k∈{5,8,10}]
    splits; equality [y^k≡1] finds [ord=40] and does not split, then
    [x=y^{27}] leftover-inverts.  Leftover [x] is the same Pohlig
    oracle.  On this pin [gcd(p−1,q−1)=2], so matching local orders
    exist only at [{1,2}].  Extra pin [N=247] has matching leftover
    orders and the same gcd is not a proper factor. *)

Theorem period_base3_period :
  Z.gcd (powm 3 8 187 - 1) 187 = 1 /\
  Z.gcd (powm 3 10 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_y32_splits :
  powm 36 32 187 = 86 /\
  powm 86 3 187 = 69 /\
  Z.gcd (69 - 36) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_y5_minus_1_splits :
  Z.gcd (powm 36 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_y8_minus_1_splits :
  Z.gcd (powm 36 8 187 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem period_y10_minus_1_splits :
  Z.gcd (powm 36 10 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_phi8_y_splits :
  Z.gcd ((powm 36 4 187 + 1) mod 187) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem period_y2_plus_1_gcd :
  Z.gcd ((powm 36 2 187 + 1) mod 187) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem period_phi5_y_splits :
  (36 * 36 * 36 * 36 + 36 * 36 * 36 + 36 * 36 + 36 + 1) mod 187 = 99 /\
  Z.gcd 99 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_x2_minus_1_int :
  Z.gcd (42 * 42 - 1) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem period_full_period_no_split :
  powm 36 40 187 = 1 /\
  Z.gcd (powm 36 40 187 - 1) 187 = 187.
Proof. vm_compute. split; reflexivity. Qed.

Theorem period_miller_on_period2 :
  powm 67 2 187 = 1 /\
  Z.gcd (67 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_local_orders :
  36 mod 11 = 3 /\
  powm 3 5 11 = 1 /\
  36 mod 17 = 2 /\
  powm 2 8 17 = 1.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity|]. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem period_gcd_pminus1_qminus1 :
  Z.gcd 10 16 = 2.
Proof. reflexivity. Qed.

Theorem period_public_d5_pohlig :
  (5 | 40) /\
  Z.gcd (powm 36 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [exists 8; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_mismatched_local_orders :
  powm 3 5 11 = 1 /\
  powm 2 8 17 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem period_lcm_local_orders :
  Z.lcm 5 8 = 40.
Proof. vm_compute. reflexivity. Qed.

Theorem period_v2_local_orders :
  Z.even 5 = false /\
  8 = 2 ^ 3.
Proof. split; reflexivity. Qed.

Theorem period_gcd_path_splits :
  Z.gcd (powm 36 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_exp_path_leftover :
  powm 36 27 187 = 42 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem period_eq_order_40 :
  powm 36 40 187 = 1 /\
  powm 36 20 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem period_eq_not_8 :
  powm 36 8 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem period_eq_not_5 :
  powm 36 5 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem period_eq_y40 :
  powm 36 40 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem period_eq_y20 :
  powm 36 20 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem period_eq_y8 :
  powm 36 8 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem period_eq_y5 :
  powm 36 5 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem period_gcd_y5_splits :
  Z.gcd (powm 36 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_gcd_y8_splits :
  Z.gcd (powm 36 8 187 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem period_gcd_full_period :
  Z.gcd (powm 36 40 187 - 1) 187 = 187.
Proof. vm_compute. reflexivity. Qed.

Theorem period_after_ord_invert :
  powm 36 27 187 = 42 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [vm_compute; reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem period_v2_ord_p :
  Z.even 5 = false.
Proof. reflexivity. Qed.

Theorem period_v2_ord_q :
  8 = 2 ^ 3.
Proof. reflexivity. Qed.

Theorem period_v2_ord_N :
  40 = 8 * 5 /\
  8 = 2 ^ 3.
Proof. split; reflexivity. Qed.

Theorem period_v2_lam_bigger :
  80 = 16 * 5 /\
  16 = 2 ^ 4.
Proof. split; reflexivity. Qed.

Theorem period_x5_minus_1_splits :
  Z.gcd (powm 42 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_x8_minus_1_splits :
  Z.gcd (powm 42 8 187 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem period_x10_minus_1_splits :
  Z.gcd (powm 42 10 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_x16_minus_1_splits :
  Z.gcd (powm 42 16 187 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem period_x4_minus_1 :
  Z.gcd (powm 42 4 187 - 1) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem period_x2_minus_1 :
  Z.gcd (powm 42 2 187 - 1) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem period_same_oracle :
  Z.gcd (powm 36 5 187 - 1) 187 = 11 /\
  Z.gcd (powm 42 5 187 - 1) 187 = 11.
Proof. vm_compute. split; reflexivity. Qed.

Theorem period_ten_order_16 :
  powm 10 16 187 = 1 /\
  powm 10 8 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem period_ten_pow8_miller :
  powm 10 8 187 = 67.
Proof. vm_compute. reflexivity. Qed.

Theorem period_ten_pow8_splits :
  Z.gcd (powm 10 8 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_ten_pow16 :
  powm 10 16 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem period_21_order_4 :
  powm 21 4 187 = 1 /\
  powm 21 2 187 = 67.
Proof. vm_compute. split; reflexivity. Qed.

Theorem period_21_sq_splits :
  Z.gcd (powm 21 2 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_89_order_4 :
  powm 36 10 187 = 89 /\
  powm 89 4 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem period_77_pminus1 :
  Z.gcd (2 ^ 6 - 1) 77 = 7 /\
  Problem_Factor 77 7.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem period_77_qminus1 :
  Z.gcd (2 ^ 10 - 1) 77 = 11 /\
  Problem_Factor 77 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 7. reflexivity.
Qed.

Theorem period_77_leftover_pohlig :
  Z.gcd (powm 51 3 77 - 1) 77 = 7 /\
  Problem_Factor 77 7.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem period_77_ord2_is_lam :
  powm 2 30 77 = 1 /\
  Z.lcm 6 10 = 30.
Proof. split; [vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

Theorem period_two_subgroups_split :
  Z.gcd (161 - 42) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem period_three_pohlig_5 :
  Z.gcd (powm 3 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_three_pohlig_16 :
  Z.gcd (powm 3 16 187 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem period_three_pow8_no_split :
  Z.gcd (powm 3 8 187 - 1) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem period_cbrt2_cbrt36_split :
  Z.gcd (161 - 42) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem period_cbrt3_cbrt36_split :
  Z.gcd (75 - 42) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_cbrt3_cbrt2 :
  Z.gcd (75 - 161) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem period_five_max_order :
  powm 5 80 187 = 1 /\
  powm 5 40 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem period_five_pohlig_5 :
  Z.gcd (powm 5 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem period_five_pohlig_16 :
  Z.gcd (powm 5 16 187 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem period_ord16_to_miller :
  powm 10 8 187 = 67.
Proof. vm_compute. reflexivity. Qed.

Theorem period_77_51_is_2_pow7 :
  powm 2 7 77 = 51.
Proof. vm_compute. reflexivity. Qed.

Theorem period_77_lambda :
  Z.lcm 6 10 = 30.
Proof. vm_compute. reflexivity. Qed.

Theorem period_77_two_pow3 :
  Z.gcd (2 ^ 3 - 1) 77 = 7 /\
  Problem_Factor 77 7.
Proof.
  split; [reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem period_77_two_pow5 :
  Z.gcd (2 ^ 5 - 1) 77 = 1.
Proof. vm_compute. reflexivity. Qed.

(** ** KeyGen shape: leftover [x] splits iff local orders mismatch

    [N=187] and [N=77]: [gcd(p−1,q−1)=2], leftover [x] is a
    [gcd(x^k−1,N)] proper-factor oracle.  [N=13·19=247]: leftover
    [x=179] of [y=69] at [e=5] has matching local orders [6], and
    the same [k∈{5,8}] do not split.  Residual leaf named, not
    [Problem_Factor].  Cross-confirmed by [cas/140]. *)

Theorem period_187_mismatch_gcd :
  Z.gcd 10 16 = 2.
Proof. reflexivity. Qed.

Theorem period_77_mismatch_gcd :
  Z.gcd 6 10 = 2.
Proof. reflexivity. Qed.

Theorem period_247_match_gcd :
  13 * 19 = 247 /\
  Z.gcd 12 18 = 6 /\
  Z.lcm 12 18 = 36.
Proof. split; [reflexivity|]. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem period_247_leftover_pair :
  powm 179 5 247 = 69 /\
  Z.gcd 69 247 = 1 /\
  Z.gcd 179 247 = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem period_247_residual_leaf :
  srsa_residual_leaf 247 36 69 179 5.
Proof.
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 2; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem period_247_local_residues :
  179 mod 13 = 10 /\
  179 mod 19 = 8.
Proof. split; reflexivity. Qed.

Theorem period_247_matching_local_orders :
  powm 10 6 13 = 1 /\
  powm 10 3 13 <> 1 /\
  powm 8 6 19 = 1 /\
  powm 8 3 19 <> 1.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem period_247_x5_minus_1_no_split :
  Z.gcd (powm 179 5 247 - 1) 247 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem period_247_x8_minus_1_no_split :
  Z.gcd (powm 179 8 247 - 1) 247 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem period_247_x6_minus_1_is_N :
  powm 179 6 247 = 1 /\
  Z.gcd (powm 179 6 247 - 1) 247 = 247.
Proof. vm_compute. split; reflexivity. Qed.

(** ** Public exponent lattice [N−1], [N+1] vs trapdoor period

    A TM that only uses exponents dividing [N−1=186=2·3·31] or
    [N+1=188] neither finds [ord(y)=40] nor hits the Pohlig [k]
    that split leftover [x].  Cross-confirmed by [cas/141]. *)

Theorem period_Nminus1_factors :
  186 = 2 * 3 * 31.
Proof. reflexivity. Qed.

Theorem period_pohlig_ndiv_Nminus1 :
  186 mod 5 = 1 /\
  186 mod 8 = 2 /\
  186 mod 10 = 6 /\
  186 mod 16 = 10.
Proof. repeat split; reflexivity. Qed.

Theorem period_ord_ndiv_Nminus1 :
  186 mod 40 = 26 /\
  186 mod 80 = 26 /\
  188 mod 40 = 28.
Proof. repeat split; reflexivity. Qed.

Theorem period_Nminus1_divisors_no_split :
  Z.gcd (powm 36 2 187 - 1) 187 = 1 /\
  Z.gcd (powm 36 3 187 - 1) 187 = 1 /\
  Z.gcd (powm 36 6 187 - 1) 187 = 1 /\
  Z.gcd (powm 36 31 187 - 1) 187 = 1 /\
  Z.gcd (powm 36 62 187 - 1) 187 = 1 /\
  Z.gcd (powm 36 93 187 - 1) 187 = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem period_y_Nminus1_no_annihilator :
  powm 36 186 187 = 157 /\
  157 <> 1 /\
  Z.gcd (157 - 1) 187 = 1.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem period_x_Nminus1_no_membership :
  powm 42 186 187 = 64 /\
  64 <> 1 /\
  Z.gcd (64 - 1) 187 = 1.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem period_Nplus1_factors :
  188 = 4 * 47.
Proof. reflexivity. Qed.

Theorem period_Nplus1_divisors_no_split :
  Z.gcd (powm 36 4 187 - 1) 187 = 1 /\
  Z.gcd (powm 36 47 187 - 1) 187 = 1 /\
  Z.gcd (powm 36 94 187 - 1) 187 = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem period_y_Nplus1_no_annihilator :
  powm 36 188 187 = 16 /\
  16 <> 1 /\
  Z.gcd (16 - 1) 187 = 1.
Proof. vm_compute. repeat split; discriminate. Qed.
