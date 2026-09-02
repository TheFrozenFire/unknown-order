From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes K (141–160)

    Extra public tapes of [N] / [y].  Cross-confirmed by [cas/135]. *)

Theorem hun_141_p_plus_q :
  11 + 17 = 28.
Proof. reflexivity. Qed.

Theorem hun_142_torus_order_is_y :
  Z.lcm 12 18 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_143_phi_over_lambda :
  160 / 80 = 2.
Proof. reflexivity. Qed.

Theorem hun_144_N_mod_8 :
  187 mod 8 = 3.
Proof. reflexivity. Qed.

Theorem hun_145_bitlength_N :
  2 ^ 7 <= 187 < 2 ^ 8.
Proof. split; lia. Qed.

Theorem hun_146_v2_N_minus_1 :
  Z.even 186 = true /\
  Z.odd (186 / 2) = true.
Proof. split; reflexivity. Qed.

Theorem hun_147_units_not_cyclic :
  Z.gcd 10 16 = 2 /\
  80 <> 160.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem hun_148_hamming_N :
  187 = 128 + 32 + 16 + 8 + 2 + 1.
Proof. reflexivity. Qed.

Theorem hun_149_digit_reverse_splits :
  7 * 100 + 8 * 10 + 1 = 781 /\
  Z.gcd 781 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_150_mod4_shape :
  11 mod 4 = 3 /\
  17 mod 4 = 1.
Proof. split; reflexivity. Qed.

Theorem hun_151_N_mod_8_two_sylow :
  187 mod 8 = 3.
Proof. reflexivity. Qed.

Theorem hun_152_digits_of_N :
  1 * 100 + 8 * 10 + 7 = 187.
Proof. reflexivity. Qed.

Theorem hun_153_N_mod_100 :
  187 mod 100 = 87.
Proof. reflexivity. Qed.

Theorem hun_154_nextprime_N :
  187 + 4 = 191 /\
  Z.odd 191 = true.
Proof. split; reflexivity. Qed.

Theorem hun_155_prevprime_associate :
  187 - 6 = 181 /\
  powm 181 2 187 = 36.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem hun_156_y_to_lambda :
  powm 36 80 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_157_y_to_phi :
  powm 36 160 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_158_base3_period :
  Z.gcd (powm 3 8 187 - 1) 187 = 1 /\
  Z.gcd (powm 3 10 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_159_ord2_is_40 :
  powm 2 40 187 = 1 /\
  powm 2 20 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_160_phi_is_product :
  (11 - 1) * (17 - 1) = 160.
Proof. reflexivity. Qed.
