From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes AB (481–500)

    One exponent [k=27] gives three leftover cube roots in three
    order-40 subgroups; [gcd] of two of them splits.  Max-order
    elements Pohlig-split.  Pin [77] local orders [3] vs [5].
    Cross-confirmed by [cas/138]. *)

Theorem hun_481_cbrt_2_in_ltwo :
  powm 2 27 187 = 161 /\
  powm 161 3 187 = 2.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_482_cbrt_3_in_lthree :
  powm 3 27 187 = 75 /\
  powm 75 3 187 = 3.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_483_cbrt_36_in_ly :
  powm 36 27 187 = 42 /\
  powm 42 3 187 = 36.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_484_three_x_for_k27 :
  161 <> 42 /\
  75 <> 42.
Proof. split; discriminate. Qed.

Theorem hun_485_cbrt2_cbrt36_split :
  Z.gcd (161 - 42) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_486_cbrt3_cbrt36_split :
  Z.gcd (75 - 42) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_487_cbrt3_cbrt2 :
  Z.gcd (75 - 161) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_488_five_max_order :
  powm 5 80 187 = 1 /\
  powm 5 40 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_489_five_pohlig_5 :
  Z.gcd (powm 5 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_490_five_pohlig_16 :
  Z.gcd (powm 5 16 187 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_491_lam_bitlength :
  2 ^ 6 <= 80 < 2 ^ 7.
Proof. split; lia. Qed.

Theorem hun_492_x_local_qr :
  42 mod 11 = 9 /\
  42 mod 17 = 8.
Proof. split; reflexivity. Qed.

Theorem hun_493_161_mod_8 :
  161 mod 8 = 1 /\
  2 mod 8 = 2.
Proof. split; reflexivity. Qed.

Theorem hun_494_ord16_to_miller :
  powm 10 8 187 = 67.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_495_x_not_ord16 :
  powm 42 16 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem hun_496_x_not_ord10 :
  powm 42 10 187 <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem hun_497_77_51_is_2_pow7 :
  powm 2 7 77 = 51.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_498_77_lambda :
  Z.lcm 6 10 = 30.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_499_77_two_pow3 :
  Z.gcd (2 ^ 3 - 1) 77 = 7 /\
  Problem_Factor 77 7.
Proof.
  split; [reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_500_77_two_pow5 :
  Z.gcd (2 ^ 5 - 1) 77 = 1.
Proof. vm_compute. reflexivity. Qed.
