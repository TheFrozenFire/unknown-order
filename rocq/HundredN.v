From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import SolverShape.

Open Scope Z_scope.

(** * Hundred classes N (201–220)

    Residual output language: [x] lives in [⟨y⟩], generates it,
    local CRT of the cube root, [e] invertible mod [16] and [5].
    Cross-confirmed by [cas/136]. *)

Theorem hun_201_x_in_cyc_y :
  powm 42 40 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_202_x_generates :
  powm 42 40 187 = 1 /\
  powm 42 20 187 = 67 /\
  67 <> 1.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_203_x_is_y_to_27 :
  powm 36 27 187 = 42 /\
  Z.gcd 27 40 = 1.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem hun_204_cube_root_of_1 :
  powm 1 3 187 = 1 /\
  powm 67 3 187 = 67 /\
  67 <> 1.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_205_unique_unit_cube :
  powm 42 3 187 = 36 /\
  (forall z, Z.coprime z 187 -> powm z 3 187 = 36 -> z mod 187 = 42).
Proof.
  split; [vm_compute; reflexivity|].
  exact shape_unique_unit_cube_root_of_36.
Qed.

Theorem hun_206_e_inv_mod_16 :
  Z.gcd 3 16 = 1.
Proof. reflexivity. Qed.

Theorem hun_207_e_inv_mod_5 :
  Z.gcd 3 5 = 1.
Proof. reflexivity. Qed.

Theorem hun_208_crt_e_inverse :
  27 mod 16 = 11 /\
  27 mod 5 = 2 /\
  11 + 16 * 1 = 27.
Proof. repeat split; reflexivity. Qed.

Theorem hun_209_five_divides_lambda :
  Z.gcd 5 80 = 5 /\
  Z.gcd 5 80 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem hun_210_local_squares :
  42 mod 11 = 9 /\
  3 * 3 = 9 /\
  42 mod 17 = 8 /\
  5 * 5 mod 17 = 8.
Proof. repeat split; reflexivity. Qed.

Theorem hun_211_qr_both_sides :
  42 mod 11 = 9 /\
  42 mod 17 = 8.
Proof. split; reflexivity. Qed.

Theorem hun_212_not_in_ltwo :
  powm 2 40 187 = 1 /\
  powm 2 1 187 <> 42 /\
  powm 2 20 187 <> 42.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_213_in_lthree_and_lfive :
  powm 3 42 187 = 42 /\
  powm 5 34 187 = 42.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_214_local_cube_mod_p :
  42 mod 11 = 9 /\
  powm 9 3 11 = 3 /\
  36 mod 11 = 3.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem hun_215_local_x_mod_q :
  42 mod 17 = 8.
Proof. reflexivity. Qed.

Theorem hun_216_crt_locals :
  9 + 11 * 3 = 42 /\
  42 mod 17 = 8.
Proof. split; reflexivity. Qed.

Theorem hun_217_bits_of_x :
  32 + 8 + 2 = 42.
Proof. reflexivity. Qed.

Theorem hun_218_x_mod_8 :
  42 mod 8 = 2.
Proof. reflexivity. Qed.

Theorem hun_219_x_minus_1_prime :
  Z.gcd 41 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_220_x_plus_1_prime :
  Z.gcd 43 187 = 1.
Proof. vm_compute. reflexivity. Qed.
