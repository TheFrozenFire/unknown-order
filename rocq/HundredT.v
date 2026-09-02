From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes T (321–340)

    [⟨y⟩ ≅ C₈ × C₅].  Cubing is bijective on both primary components.
    [y] reconstructs as a product of a [C₈] part and a [C₅] part.
    Cross-confirmed by [cas/137]. *)

Theorem hun_321_C8_generator :
  powm 36 5 187 = 100 /\
  powm 100 8 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_322_C8_squares :
  powm 100 2 187 = 89 /\
  powm 100 4 187 = 67 /\
  powm 100 8 187 = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem hun_323_C5_generator :
  powm 36 8 187 = 137 /\
  powm 137 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_324_C5_elements :
  powm 137 2 187 = 69 /\
  powm 137 3 187 = 103 /\
  powm 137 4 187 = 86.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem hun_325_cube_bij_C5 :
  Z.gcd 3 5 = 1.
Proof. reflexivity. Qed.

Theorem hun_326_cube_bij_C8 :
  Z.gcd 3 8 = 1.
Proof. reflexivity. Qed.

Theorem hun_327_reconstruct_y :
  (155 * 69) mod 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_328_bezout_5_8 :
  5 * 5 + 8 * (-3) = 1.
Proof. reflexivity. Qed.

Theorem hun_329_C8_order2_is_miller :
  powm 100 4 187 = 67 /\
  powm 67 2 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_330_v2_local_orders :
  Z.even 5 = false /\
  8 = 2 ^ 3.
Proof. split; reflexivity. Qed.

Theorem hun_331_eight_div_ord :
  (8 | 40).
Proof. exists 5. reflexivity. Qed.

Theorem hun_332_five_div_ord :
  (5 | 40).
Proof. exists 8. reflexivity. Qed.

Theorem hun_333_C8_is_y5 :
  powm 36 5 187 = 100.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_334_order4_in_C8 :
  powm 36 10 187 = 89 /\
  powm 100 2 187 = 89.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_335_C8_pow6 :
  powm 100 6 187 = 166.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_336_C8_pow3 :
  powm 100 3 187 = 111.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_337_C8_pow5 :
  powm 100 5 187 = 155.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_338_C8_pow7 :
  powm 100 7 187 = 144.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_339_C5_pow3 :
  powm 137 3 187 = 103 /\
  powm 36 24 187 = 103.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_340_ker_squaring_C8 :
  powm 67 2 187 = 1.
Proof. vm_compute. reflexivity. Qed.
