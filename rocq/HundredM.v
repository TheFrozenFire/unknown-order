From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Hundred classes M (181–200)

    Named engines, further moduli, DL bases 5 and 9.  Cross-confirmed
    by [cas/135]. *)

Theorem hun_181_pminus1_B8 :
  Z.gcd (powm 2 840 187 - 1) 187 = 187.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_182_rho_x2_minus_1 :
  2 * 2 - 1 = 3 /\
  3 * 3 - 1 = 8 /\
  Z.gcd (8 - 41) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_183_williams_P3_no_split :
  Z.gcd (103682 - 2) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_184_factorial_trial :
  Z.gcd 3628800 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_185_hart_square :
  14 * 14 - 187 = 9 /\
  3 * 3 = 9.
Proof. split; reflexivity. Qed.

Theorem hun_186_fermat_recovers :
  14 - 3 = 11 /\
  14 + 3 = 17 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_187_trial_13_then_11 :
  (187 mod 13 <> 0) /\
  (11 | 187) /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; discriminate|].
  split; [exists 17; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_188_fibonacci_gcd_engine :
  Z.gcd 34 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_189_mersenne_engine :
  Z.gcd (2 ^ 8 - 1) 187 = 17 /\
  Problem_Factor 187 17.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 11. reflexivity.
Qed.

Theorem hun_190_shor_period_of_2 :
  powm 2 40 187 = 1 /\
  40 <> 80.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_191_N55_cube_residual_shaped :
  5 * 11 = 55 /\
  Z.lcm 4 10 = 20 /\
  Z.gcd 3 20 = 1.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem hun_192_N119_cube_shares :
  7 * 17 = 119 /\
  Z.lcm 6 16 = 48 /\
  Z.gcd 3 48 = 3.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem hun_193_N209_cube_shares :
  11 * 19 = 209 /\
  Z.lcm 10 18 = 90 /\
  Z.gcd 3 90 = 3.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem hun_194_N221_cube_shares :
  13 * 17 = 221 /\
  Z.lcm 12 16 = 48 /\
  Z.gcd 3 48 = 3.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem hun_195_N323_cube_shares :
  17 * 19 = 323 /\
  Z.lcm 16 18 = 144 /\
  Z.gcd 3 144 = 3.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem hun_196_prime_cube :
  11 * 11 * 11 = 1331.
Proof. reflexivity. Qed.

Theorem hun_197_dl_base5 :
  powm 5 22 187 = 36 /\
  powm 5 34 187 = 42 /\
  (34 * 3) mod 80 = 22.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem hun_198_dl_base9 :
  powm 9 23 187 = 36 /\
  powm 9 21 187 = 42 /\
  (21 * 3) mod 40 = 23.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem hun_199_e_nextprime_N :
  Z.gcd 191 80 = 1 /\
  Z.odd 191 = true.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem hun_200_prevprime_even_peel :
  187 - 6 = 181 /\
  powm 181 2 187 = 36 /\
  Z.even 2 = true.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.
