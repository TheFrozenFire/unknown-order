From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes Z (441–460)

    Safeprime pin [77] Pohlig, [(Z/40Z)*] coordinates of [k=27],
    cube roots in [⟨2⟩] and [⟨3⟩] vs [⟨y⟩], two-subgroup split.
    Cross-confirmed by [cas/138]. *)

Theorem hun_441_77_pminus1 :
  Z.gcd (2 ^ 6 - 1) 77 = 7 /\
  Problem_Factor 77 7.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_442_77_qminus1 :
  Z.gcd (2 ^ 10 - 1) 77 = 11 /\
  Problem_Factor 77 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 7. reflexivity.
Qed.

Theorem hun_443_77_leftover_pohlig :
  Z.gcd (powm 51 3 77 - 1) 77 = 7 /\
  Problem_Factor 77 7.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_444_77_ord2_is_lam :
  powm 2 30 77 = 1 /\
  Z.lcm 6 10 = 30.
Proof. split; [vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

Theorem hun_445_k27_coords :
  27 mod 8 = 3 /\
  27 mod 5 = 2.
Proof. split; reflexivity. Qed.

Theorem hun_446_e3_coords :
  3 mod 8 = 3 /\
  3 mod 5 = 3.
Proof. split; reflexivity. Qed.

Theorem hun_447_3_order_4_mod_40 :
  (3 ^ 4) mod 40 = 1 /\
  (3 ^ 2) mod 40 <> 1.
Proof. split; [reflexivity | vm_compute; discriminate]. Qed.

Theorem hun_448_N_mod_8_for_2 :
  187 mod 8 = 3.
Proof. reflexivity. Qed.

Theorem hun_449_cube_root_of_2 :
  powm 2 27 187 = 161 /\
  powm 161 3 187 = 2.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_450_sagm_of_3 :
  powm 3 27 187 = 75 /\
  powm 75 3 187 = 3.
Proof. vm_compute. split; reflexivity. Qed.

Theorem hun_451_75_not_42 :
  75 <> 42.
Proof. discriminate. Qed.

Theorem hun_452_y_to_27 :
  powm 36 27 187 = 42.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_453_ten_jacobi_plus :
  10 mod 8 = 2.
Proof. reflexivity. Qed.

Theorem hun_454_ten_not_ord40 :
  powm 10 16 187 = 1 /\
  powm 10 8 187 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_455_21_mod_8 :
  21 mod 8 = 5.
Proof. reflexivity. Qed.

Theorem hun_456_ltwo_ord40 :
  powm 2 40 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_457_two_ne_y :
  2 <> 36.
Proof. discriminate. Qed.

Theorem hun_458_two_subgroups_split :
  Z.gcd (161 - 42) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_459_four_cosets :
  160 / 40 = 4.
Proof. reflexivity. Qed.

Theorem hun_460_cycle2_60 :
  powm 60 3 187 = 15.
Proof. vm_compute. reflexivity. Qed.
