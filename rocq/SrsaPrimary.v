From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Primary decomposition of [⟨y⟩]

    [⟨y⟩ ≅ C₈ × C₅].  [y^5=100] generates [C₈]; [y^8=137] generates
    [C₅].  Cubing is bijective on both.  [y] reconstructs as a
    product of the primaries.  The order-2 of [C₈] is Miller [67]. *)

Theorem primary_y20_miller :
  powm 36 20 187 = 67 /\
  powm 67 2 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_y16_five_torsion :
  powm 36 16 187 = 69 /\
  powm 69 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_y8_five_torsion :
  powm 36 8 187 = 137 /\
  powm 137 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_y5_order8 :
  powm 36 5 187 = 100 /\
  powm 100 8 187 = 1 /\
  powm 100 4 187 <> 1.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem primary_y10_order4 :
  powm 36 10 187 = 89 /\
  powm 89 4 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_y4_order10 :
  powm 36 4 187 = 169 /\
  Z.gcd 4 40 = 4.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem primary_x_to_8_is_five_torsion :
  powm 42 8 187 = 69 /\
  powm 69 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_C8_generator :
  powm 36 5 187 = 100 /\
  powm 100 8 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_C8_squares :
  powm 100 2 187 = 89 /\
  powm 100 4 187 = 67 /\
  powm 100 8 187 = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem primary_C5_generator :
  powm 36 8 187 = 137 /\
  powm 137 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_C5_elements :
  powm 137 2 187 = 69 /\
  powm 137 3 187 = 103 /\
  powm 137 4 187 = 86.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem primary_cube_bij_C5 :
  Z.gcd 3 5 = 1.
Proof. reflexivity. Qed.

Theorem primary_cube_bij_C8 :
  Z.gcd 3 8 = 1.
Proof. reflexivity. Qed.

Theorem primary_reconstruct_y :
  (155 * 69) mod 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_bezout_5_8 :
  5 * 5 + 8 * (-3) = 1.
Proof. reflexivity. Qed.

Theorem primary_C8_order2_is_miller :
  powm 100 4 187 = 67 /\
  powm 67 2 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_eight_div_ord :
  (8 | 40).
Proof. exists 5. reflexivity. Qed.

Theorem primary_five_div_ord :
  (5 | 40).
Proof. exists 8. reflexivity. Qed.

Theorem primary_C8_is_y5 :
  powm 36 5 187 = 100.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_order4_in_C8 :
  powm 36 10 187 = 89 /\
  powm 100 2 187 = 89.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_C8_pow6 :
  powm 100 6 187 = 166.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C8_pow3 :
  powm 100 3 187 = 111.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C8_pow5 :
  powm 100 5 187 = 155.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C8_pow7 :
  powm 100 7 187 = 144.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C5_pow3 :
  powm 137 3 187 = 103 /\
  powm 36 24 187 = 103.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_ker_squaring_C8 :
  powm 67 2 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C8_order :
  powm 100 8 187 = 1 /\
  powm 100 4 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem primary_C5_order :
  powm 137 5 187 = 1 /\
  powm 137 1 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem primary_lcm_primaries :
  Z.lcm 8 5 = 40.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_coprime_primaries :
  Z.gcd 8 5 = 1.
Proof. reflexivity. Qed.

Theorem primary_cube_bij_primaries :
  Z.gcd 3 8 = 1 /\
  Z.gcd 3 5 = 1.
Proof. split; reflexivity. Qed.

Theorem primary_x5_generates_C8 :
  powm 42 5 187 = 111 /\
  powm 111 8 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_x8_in_C5 :
  powm 42 8 187 = 69 /\
  powm 69 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_reconstruct_x :
  (powm 111 5 187 * powm 69 2 187) mod 187 = 42.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_69_generates_C5 :
  powm 69 5 187 = 1 /\
  powm 69 1 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem primary_111_generates_C8 :
  powm 111 8 187 = 1 /\
  powm 111 4 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.
