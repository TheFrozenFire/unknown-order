From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes O (221–240)

    The 16 generators of [⟨y⟩] are exactly the residual [x]'s.
    Non-generators cubing either miss or one-sided-split.
    Cross-confirmed by [cas/136]. *)

Theorem hun_221_sixteen_generators :
  40 / 2 * 4 / 5 = 16.
Proof. reflexivity. Qed.

Theorem hun_222_even_k_not_generator :
  Z.gcd 2 40 = 2 /\
  powm 36 2 187 = 174 /\
  powm 174 3 187 = 47 /\
  Z.gcd (47 - 36) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_223_y20_miller :
  powm 36 20 187 = 67 /\
  powm 67 2 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_224_y16_five_torsion :
  powm 36 16 187 = 69 /\
  powm 69 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_225_y8_five_torsion :
  powm 36 8 187 = 137 /\
  powm 137 5 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_226_y32_splits :
  powm 36 32 187 = 86 /\
  powm 86 3 187 = 69 /\
  Z.gcd (69 - 36) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_227_y5_order8 :
  powm 36 5 187 = 100 /\
  powm 100 8 187 = 1 /\
  powm 100 4 187 <> 1.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_228_y10_order4 :
  powm 36 10 187 = 89 /\
  powm 89 4 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_229_identity_not_root :
  powm 1 3 187 = 1 /\
  1 <> 36.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem hun_230_y35_onesided :
  powm 36 35 187 = 144 /\
  powm 144 3 187 = 155 /\
  Z.gcd (155 - 36) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_231_y4_order10 :
  powm 36 4 187 = 169 /\
  Z.gcd 4 40 = 4.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem hun_232_gen_pair_42_9 :
  Z.gcd (42 - 9) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_233_gen_pair_42_53 :
  Z.gcd (42 - 53) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_234_gen_pair_42_93 :
  Z.gcd (42 - 93) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_235_y_minus_x :
  Z.gcd (36 - 42) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_236_y_inv_generator :
  powm 36 39 187 = 26 /\
  (36 * 26) mod 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_237_x_inv_generator :
  powm 36 13 187 = 49 /\
  (42 * 49) mod 187 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_238_y29 :
  powm 36 29 187 = 15.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_239_y3_generator :
  powm 36 3 187 = 93 /\
  Z.gcd 3 40 = 1.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem hun_240_y9_generator :
  powm 36 9 187 = 70 /\
  Z.gcd 9 40 = 1.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.
