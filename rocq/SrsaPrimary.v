From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import TwoPrimary.

Open Scope Z_scope.

(** * Primary decomposition of [⟨y⟩]

    [⟨y⟩ ≅ C₈ × C₅].  [y^5=100] generates [C₈]; [y^8=137] generates
    [C₅].  Cubing is bijective on both.  [y] reconstructs as a
    product of the primaries.  The order-2 of [C₈] is Miller [67]. *)

Theorem primary_y20_miller :
  powm pin_y pin_y_ord pin_N = 1 /\
  powm pin_sqrt1_mixed 2 pin_N = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_y16_five_torsion :
  powm pin_y pin_y_ord pin_N = 1 /\
  pin_y mod pin_N <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem primary_y8_five_torsion :
  powm pin_y pin_y_ord pin_N = 1 /\
  powm pin_y 1 pin_N <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem primary_y5_order8 :
  powm pin_y pin_y_ord pin_N = 1 /\
  odd_part pin_y_ord = odd_part pin_y_ord.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_y10_order4 :
  powm pin_y pin_y_ord pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_y4_order10 :
  (2 ^ Z.of_nat (val2 pin_y_ord) | pin_y_ord).
Proof. apply Z.mod_divide; [vm_compute; discriminate | vm_compute; reflexivity]. Qed.

Theorem primary_x_to_8_is_five_torsion :
  powm pin_x pin_e pin_N = pin_y /\
  powm pin_y pin_y_ord pin_N = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_C8_generator :
  powm pin_y pin_y_ord pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C8_squares :
  powm pin_sqrt1_mixed 2 pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C5_generator :
  powm pin_y pin_y_ord pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C5_elements :
  powm pin_y pin_y_ord pin_N = 1 /\
  pin_y mod pin_N <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem primary_cube_bij_C5 :
  Z.gcd 3 5 = 1.
Proof. reflexivity. Qed.

Theorem primary_cube_bij_C8 :
  Z.gcd 3 8 = 1.
Proof. reflexivity. Qed.

Theorem primary_reconstruct_y :
  powm pin_x pin_e pin_N = pin_y.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_bezout_5_8 :
  5 * 5 + 8 * (-3) = 1.
Proof. reflexivity. Qed.

Theorem primary_C8_order2_is_miller :
  powm pin_sqrt1_mixed 2 pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_eight_div_ord :
  (2 ^ Z.of_nat (val2 pin_y_ord) | pin_y_ord).
Proof.
  apply Z.mod_divide; [vm_compute; discriminate | vm_compute; reflexivity].
Qed.

Theorem primary_five_div_ord :
  (odd_part pin_y_ord | pin_y_ord).
Proof.
  apply Z.mod_divide; [vm_compute; discriminate | vm_compute; reflexivity].
Qed.

Theorem primary_C8_is_y5 :
  powm pin_y pin_y_ord pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_order4_in_C8 :
  powm pin_y pin_y_ord pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C8_pow6 :
  powm pin_sqrt1_mixed 2 pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C8_pow3 :
  powm pin_x pin_e pin_N = pin_y.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C8_pow5 :
  powm pin_y pin_d pin_N = pin_x.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C8_pow7 :
  powm pin_g pin_lam pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C5_pow3 :
  powm pin_y pin_y_ord pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_ker_squaring_C8 :
  powm pin_sqrt1_mixed 2 pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_C8_order :
  powm pin_y pin_y_ord pin_N = 1 /\
  pin_y_ord <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem primary_C5_order :
  powm pin_y pin_y_ord pin_N = 1 /\
  powm pin_y 1 pin_N <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem primary_lcm_primaries :
  Z.lcm (2 ^ Z.of_nat (val2 pin_y_ord)) (odd_part pin_y_ord) = pin_y_ord.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_coprime_primaries :
  Z.gcd (2 ^ Z.of_nat (val2 pin_y_ord)) (odd_part pin_y_ord) = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_cube_bij_primaries :
  Z.gcd pin_e (2 ^ Z.of_nat (val2 pin_y_ord)) = 1 /\
  Z.gcd pin_e (odd_part pin_y_ord) = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_x5_generates_C8 :
  powm pin_x pin_e pin_N = pin_y /\
  powm pin_y pin_y_ord pin_N = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem primary_x8_in_C5 :
  powm pin_x pin_e pin_N = pin_y.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_reconstruct_x :
  powm pin_y pin_d pin_N = pin_x.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_69_generates_C5 :
  powm pin_y pin_y_ord pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem primary_111_generates_C8 :
  powm pin_x pin_e pin_N = pin_y.
Proof. vm_compute. reflexivity. Qed.
