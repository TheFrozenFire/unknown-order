From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes Q (261–280)

    Advice less than [λ], and programs that write [x = y^k] for a
    public [k].  [k = e^{-1} (mod 40)] hits the residual cube.
    Cross-confirmed by [cas/136]. *)

Theorem hun_261_lam_ne_Nminus1 :
  80 <> 186.
Proof. discriminate. Qed.

Theorem hun_262_ord_div_lam :
  (40 | 80).
Proof. exists 2. reflexivity. Qed.

Theorem hun_263_e_coprime_10_16 :
  Z.gcd 3 10 = 1 /\
  Z.gcd 3 16 = 1.
Proof. split; reflexivity. Qed.

Theorem hun_264_five_ndiv_e :
  3 mod 5 = 3 /\
  3 <> 0.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem hun_265_y_local_qr :
  36 mod 11 = 3 /\
  5 * 5 mod 11 = 3 /\
  36 mod 17 = 2 /\
  6 * 6 mod 17 = 2.
Proof. repeat split; reflexivity. Qed.

Theorem hun_266_advice_local_9 :
  42 mod 11 = 9.
Proof. reflexivity. Qed.

Theorem hun_267_N_mod_40_is_d :
  187 mod 40 = 27.
Proof. reflexivity. Qed.

Theorem hun_268_bitlength_lam :
  2 ^ 6 <= 80 < 2 ^ 7.
Proof. split; lia. Qed.

Theorem hun_269_gcd_pminus1_qminus1 :
  Z.gcd 10 16 = 2.
Proof. reflexivity. Qed.

Theorem hun_270_lambda_lcm :
  Z.lcm 10 16 = 80.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_271_y_to_e_inv :
  powm 36 27 187 = 42 /\
  Z.gcd 27 40 = 1 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [vm_compute; reflexivity|].
  split; [reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem hun_272_public_N_mod_40 :
  187 mod 40 = 27 /\
  powm 36 27 187 = 42.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem hun_273_y_to_d :
  powm 36 27 187 = 42.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_274_k1_is_y :
  powm 36 1 187 = 36 /\
  36 <> 42.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem hun_275_k3_is_y_cube :
  powm 36 3 187 = 93 /\
  93 <> 42.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_276_public_d5_pohlig :
  (5 | 40) /\
  Z.gcd (powm 36 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [exists 8; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_277_euclid_x_minus_y :
  Z.gcd (42 - 36) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_278_low_bits_y :
  36 mod 4 = 0.
Proof. reflexivity. Qed.

Theorem hun_279_even_k_shares_ord :
  Z.gcd 2 40 = 2 /\
  Z.gcd 2 40 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem hun_280_inv_lam_minus_1 :
  powm 26 79 187 = 36 /\
  srsa_residual_leaf 187 80 36 26 79.
Proof.
  split; [vm_compute; reflexivity|].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 39; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.
