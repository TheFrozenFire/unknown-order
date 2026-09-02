From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import PollardP1.
Require Import FermatFactor.
Require Import Lucas.
Require Import Takagi.
Require Import OkamotoUchiyama.
Require Import QRModN.
Require Import ExtraRelations.

Open Scope Z_scope.

(** * Hundred classes F–H (75–100)

    Named factoring engines as solvers, modulus/group variants,
    public-[N] maps, DL base 3.  Cross-confirmed by [cas/133]. *)

Theorem hun_75_pollard_p1 :
  Z.gcd (powm 2 60 187 - 1) 187 = 11 /\
  (10 | 60) /\
  ~ (16 | 60) /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [exists 6; reflexivity|].
  split; [intros [k Hk]; nia|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_76_rho_walk :
  2 * 2 + 1 = 5 /\
  5 * 5 + 1 = 26 /\
  (26 * 26 + 1) mod 187 = 116 /\
  (116 * 116 + 1) mod 187 = 180 /\
  Z.gcd (26 - 180) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_77_bsgs_wrong_order :
  lambda_semiprime 11 17 = 80 /\
  187 - 1 = 186 /\
  80 <> 186.
Proof. split; [vm_compute; reflexivity|]. split; [reflexivity | discriminate]. Qed.

Theorem hun_78_fermat_splits :
  14 * 14 - 187 = 9 /\
  3 * 3 = 9 /\
  14 - 3 = 11 /\
  14 + 3 = 17 /\
  Problem_Factor 187 11.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_79_trial_division :
  (11 | 187) /\
  Problem_Factor 187 11.
Proof.
  split; [exists 17; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_80_williams_pplus1 :
  Z.gcd (lucasV 5 1 12%nat - 2) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem hun_81_index_calculus_Nminus1 :
  Z.gcd (powm 2 186 187 - 1) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_82_squaring_only :
  powm 2 8 187 = 69 /\
  2 ^ 8 = 256 /\
  256 mod 187 = 69.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem hun_83_advice_on_y_lsb :
  Z.even 36 = true.
Proof. reflexivity. Qed.

Theorem hun_84_streaming_first_bit :
  36 mod 2 = 0.
Proof. reflexivity. Qed.

Theorem hun_85_ou_carrier :
  takagi_N 3 5 = 45 /\
  powm (1 + 3) 2 (3 * 3) = (1 + 2 * 3) mod (3 * 3).
Proof.
  split; [reflexivity|].
  apply one_plus_p_pow; lia.
Qed.

Theorem hun_86_dj_carrier :
  187 * 187 * 187 = 6539203.
Proof. reflexivity. Qed.

Theorem hun_87_cocks_jacobi :
  jacobi_N 36 11 17 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_88_prime_power_field :
  17 * 17 = 289 /\
  powm 8 3 17 = 2 /\
  powm 2 11 17 = 8.
Proof. split; [reflexivity | vm_compute; split; reflexivity]. Qed.

Theorem hun_89_two_safeprimes :
  7 * 23 = 161 /\
  Z.lcm 6 22 = 66 /\
  Z.gcd 3 66 = 3 /\
  Z.gcd 3 66 <> 1.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [reflexivity | discriminate].
Qed.

Theorem hun_90_rw_shape_odd_e :
  11 mod 8 = 3 /\
  23 mod 8 = 7.
Proof. split; reflexivity. Qed.

Theorem hun_91_twins :
  101 + 103 = 204 /\
  204 / 2 = 102.
Proof. split; reflexivity. Qed.

Theorem hun_92_unbalanced :
  11 * 101 = 1111 /\
  (11 | 1111) /\
  Problem_Factor 1111 11.
Proof.
  split; [reflexivity|].
  split; [exists 101; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 101. reflexivity.
Qed.

Theorem hun_93_triprime_cube_not_residual :
  3 * 5 * 7 = 105 /\
  Z.lcm (Z.lcm 2 4) 6 = 12 /\
  Z.gcd 3 12 = 3 /\
  Z.gcd 3 12 <> 1.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [reflexivity | discriminate].
Qed.

Theorem hun_94_prime_field :
  Z.gcd 3 16 = 1 /\
  powm 2 11 17 = 8 /\
  powm 8 3 17 = 2.
Proof. split; [reflexivity | vm_compute; split; reflexivity]. Qed.

Theorem hun_95_e_eq_N :
  Z.gcd 187 80 = 1 /\
  ~ (80 | 186).
Proof. split; [reflexivity|]. intros [k Hk]. nia. Qed.

Theorem hun_96_e_eq_Nminus2 :
  Z.gcd (187 - 2) 80 = 5 /\
  Z.gcd 185 80 <> 1.
Proof. split; [vm_compute; reflexivity | discriminate]. Qed.

Theorem hun_97_x_eq_Nminus1 :
  powm (-1) 3 187 = 186 /\
  186 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_98_floor_sqrt_N :
  Z.sqrt 187 = 13 /\
  powm 13 3 187 = 140 /\
  140 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_99_phi3_of_N :
  Z.gcd (187 * 187 + 187 + 1) 80 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hun_100_dl_base3 :
  powm 3 46 187 = 36 /\
  powm 3 42 187 = 42 /\
  (42 * 3) mod 80 = 46.
Proof. vm_compute. repeat split; reflexivity. Qed.
