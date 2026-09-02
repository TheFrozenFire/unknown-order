From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import Zmod.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import TwoPrimary.

Open Scope Z_scope.

(** * Hundred classes B (13–32)

    Further [x = f(y)] maps.  Cross-confirmed by [cas/133]. *)

Fixpoint hun_fib_iter (n : nat) (a b : Z) : Z :=
  match n with
  | O => a
  | S n' => hun_fib_iter n' b (a + b)
  end.

Theorem hun_13_odd_monomial_y5 :
  powm 36 5 187 = 100 /\
  powm 100 3 187 = 111 /\
  111 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_14_y_to_the_y :
  powm 36 36 187 = 135 /\
  135 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_15_y_to_the_N :
  powm 36 187 187 = 42 /\
  187 mod 40 = 27 /\
  srsa_residual_leaf 187 80 36 42 3.
Proof.
  split; [vm_compute; reflexivity|].
  split; [reflexivity|].
  apply srsa_residual_pin.
Qed.

Theorem hun_16_y_to_Nminus1 :
  powm 36 (187 - 1) 187 = 157 /\
  157 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_17_y_to_Nplus1 :
  powm 36 (187 + 1) 187 = 16 /\
  16 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_18_floor_sqrt_y :
  Z.sqrt 36 = 6 /\
  6 * 6 = 36.
Proof. split; reflexivity. Qed.

Theorem hun_19_half_y :
  36 / 2 = 18 /\
  powm 18 3 187 = 35 /\
  35 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_20_bitrev_36_is_9 :
  powm 9 3 187 = 168 /\
  168 <> 36 /\
  powm 53 3 187 = 25 /\
  25 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_21_triangular :
  (36 * 35 / 2) mod 187 = 69 /\
  powm 69 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_22_nextprime_as_x :
  powm 37 3 187 = 163 /\
  163 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_23_fibonacci_y :
  hun_fib_iter 36%nat 0 1 = 14930352 /\
  14930352 mod 187 = 85 /\
  powm 85 3 187 = 17 /\
  17 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_24_exp_base2 :
  powm 2 36 187 = 152 /\
  152 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_25_exp_base3 :
  powm 3 36 187 = 47 /\
  47 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_26_phi3_of_y :
  (36 * 36 + 36 + 1) mod 187 = 24 /\
  24 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_27_inv_then_cube :
  powm 26 3 187 = 185 /\
  185 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_28_cube_then_inv :
  (93 * 185) mod 187 = 1 /\
  185 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_29_hybrid_crt :
  crt2 11 17 1 36 = 155 /\
  Z.gcd 155 187 = 1 /\
  powm 155 3 187 = 144 /\
  144 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_30_mismatched_crt_splits :
  crt2 11 17 9 1 = 86 /\
  Z.gcd (powm 86 3 187 - 36) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_31_integer_jnt :
  36 + 28 = 64 /\
  4 * 4 * 4 = 64.
Proof. split; reflexivity. Qed.

Theorem hun_32_y2_plus_1 :
  (36 * 36 + 1) mod 187 = 175 /\
  175 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.
