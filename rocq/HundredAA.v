From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes AA (461–480)

    The other three cubing 4-cycles on generators.  Four square
    roots of 1.  [gcd(p−1,q−1)=2] forces mismatched local orders
    above 2.  Cross-confirmed by [cas/138]. *)

Theorem hun_461_cycle2_168 :
  powm 168 3 187 = 60.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_462_cycle3_25 :
  powm 25 3 187 = 104.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_463_cycle3_104 :
  powm 104 3 187 = 59.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_464_cycle3_59 :
  powm 59 3 187 = 53.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_465_cycle3_53 :
  powm 53 3 187 = 25.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_466_cycle4_49 :
  powm 49 3 187 = 26.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_467_cycle4_26 :
  powm 26 3 187 = 185.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_468_cycle4_185 :
  powm 185 3 187 = 179.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_469_cycle4_179 :
  powm 179 3 187 = 49.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_470_gcd_pminus1_qminus1 :
  Z.gcd 10 16 = 2.
Proof. reflexivity. Qed.

Theorem hun_471_five_div_ord :
  (5 | 40).
Proof. exists 8. reflexivity. Qed.

Theorem hun_472_eight_div_ord :
  (8 | 40).
Proof. exists 5. reflexivity. Qed.

Theorem hun_473_three_pohlig_5 :
  Z.gcd (powm 3 5 187 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_474_three_pohlig_16 :
  Z.gcd (powm 3 16 187 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_475_three_pow8_no_split :
  Z.gcd (powm 3 8 187 - 1) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_476_120_plus_1 :
  120 + 1 = 121 /\
  11 * 11 = 121 /\
  Z.gcd 121 187 = 11.
Proof. split; [reflexivity|]. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem hun_477_miller_66 :
  67 - 1 = 66 /\
  Z.gcd 66 187 = 11.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem hun_478_four_sqrt1 :
  powm 1 2 187 = 1 /\
  powm 186 2 187 = 1 /\
  powm 67 2 187 = 1 /\
  powm 120 2 187 = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem hun_479_x16_not_1 :
  powm 42 16 187 = 86 /\
  86 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_480_x8_not_1 :
  powm 42 8 187 <> 1.
Proof. vm_compute. discriminate. Qed.
