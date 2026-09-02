From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes P (241–260)

    Pohlig–Miller on the challenge: local orders of [y] are [5] and
    [8], so [gcd(y^5−1,N)] and [gcd(y^8−1,N)] split.  Partial [λ].
    Cross-confirmed by [cas/136]. *)

Theorem hun_241_y5_minus_1_splits :
  Z.gcd (powm 36 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_242_y8_minus_1_splits :
  Z.gcd (powm 36 8 187 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_243_y10_minus_1_splits :
  Z.gcd (powm 36 10 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_244_phi8_y_splits :
  Z.gcd ((powm 36 4 187 + 1) mod 187) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_245_y2_plus_1 :
  Z.gcd ((powm 36 2 187 + 1) mod 187) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_246_phi5_y_splits :
  (36 * 36 * 36 * 36 + 36 * 36 * 36 + 36 * 36 + 36 + 1) mod 187 = 99 /\
  Z.gcd 99 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_247_x2_minus_1 :
  Z.gcd (42 * 42 - 1) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_248_full_period_no_split :
  powm 36 40 187 = 1 /\
  Z.gcd (powm 36 40 187 - 1) 187 = 187.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_249_miller_on_period2 :
  powm 67 2 187 = 1 /\
  Z.gcd (67 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_250_local_orders :
  36 mod 11 = 3 /\
  powm 3 5 11 = 1 /\
  36 mod 17 = 2 /\
  powm 2 8 17 = 1.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity|]. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem hun_251_five_divides_ord :
  (5 | 40).
Proof. exists 8. reflexivity. Qed.

Theorem hun_252_eight_divides_ord :
  (8 | 40).
Proof. exists 5. reflexivity. Qed.

Theorem hun_253_index_two :
  powm 3 80 187 = 1 /\
  powm 3 40 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_254_dl_even :
  Z.even 46 = true.
Proof. reflexivity. Qed.

Theorem hun_255_y_in_square_subgroup :
  powm 3 46 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_256_advice_five_div_lam :
  (5 | 80).
Proof. exists 16. reflexivity. Qed.

Theorem hun_257_v2_lambda :
  80 = 16 * 5 /\
  Z.even 16 = true.
Proof. split; reflexivity. Qed.

Theorem hun_258_ord_divides_lam :
  (40 | 80).
Proof. exists 2. reflexivity. Qed.

Theorem hun_259_y_to_ord :
  powm 36 40 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_260_phi_over_lam :
  160 / 80 = 2.
Proof. reflexivity. Qed.
