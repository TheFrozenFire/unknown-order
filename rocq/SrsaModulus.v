From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import Paillier.
Require Import Lucas.
Require Import Takagi.
Require Import OkamotoUchiyama.
Require Import QRModN.

Open Scope Z_scope.

(** * Different group or modulus

    Paillier [N²], Damgård–Jurik [N³], Okamoto–Uchiyama / Takagi
    [p²q], prime [N], prime-power, triprime, two safeprimes, Williams
    torus [V_e], Cocks Jacobi.  Not the semiprime cube. *)

Theorem modulus_paillier_carrier :
  pin_Nsq = 34969 /\
  powm (1 + pin_N) 1 pin_Nsq = (1 + 1 * pin_N) mod pin_Nsq.
Proof.
  split; [reflexivity|].
  apply one_plus_N_pow; lia.
Qed.

Theorem modulus_williams_Ve :
  lucasV 62 1 3%nat = 238142 /\
  238142 mod pin_N = 91 /\
  91 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem modulus_ou_carrier :
  takagi_N pin_45_p pin_45_q = pin_45 /\
  powm (1 + pin_45_p) 2 (pin_45_p * pin_45_p) =
    (1 + 2 * pin_45_p) mod (pin_45_p * pin_45_p).
Proof.
  split; [reflexivity|].
  apply one_plus_p_pow; lia.
Qed.

Theorem modulus_dj_carrier :
  pin_N * pin_N * pin_N = 6539203.
Proof. reflexivity. Qed.

Theorem modulus_cocks_jacobi :
  jacobi_N pin_y pin_p pin_q = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem modulus_prime_power_field :
  17 * 17 = 289 /\
  powm 8 3 17 = 2 /\
  powm 2 11 17 = 8.
Proof. split; [reflexivity | vm_compute; split; reflexivity]. Qed.

Theorem modulus_two_safeprimes :
  7 * 23 = 161 /\
  Z.lcm 6 22 = 66 /\
  Z.gcd 3 66 = 3 /\
  Z.gcd 3 66 <> 1.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [reflexivity | discriminate].
Qed.

Theorem modulus_rw_shape_odd_e :
  pin_253_p mod 8 = 3 /\
  pin_253_q mod 8 = 7.
Proof. split; reflexivity. Qed.

Theorem modulus_twins :
  101 + 103 = 204 /\
  204 / 2 = 102.
Proof. split; reflexivity. Qed.

Theorem modulus_unbalanced :
  11 * 101 = 1111 /\
  (11 | 1111) /\
  Problem_Factor 1111 11.
Proof.
  split; [reflexivity|].
  split; [exists 101; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 101. reflexivity.
Qed.

Theorem modulus_triprime_cube_not_residual :
  pin_105_p * pin_105_q * pin_105_r = pin_105 /\
  Z.lcm (Z.lcm 2 4) 6 = pin_105_lam /\
  Z.gcd 3 pin_105_lam = 3 /\
  Z.gcd 3 pin_105_lam <> 1.
Proof.
  split; [reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [reflexivity | discriminate].
Qed.

Theorem modulus_prime_field :
  Z.gcd 3 16 = 1 /\
  powm 2 11 17 = 8 /\
  powm 8 3 17 = 2.
Proof. split; [reflexivity | vm_compute; split; reflexivity]. Qed.

Theorem modulus_N55_cube_residual_shaped :
  5 * 11 = 55 /\
  Z.lcm 4 10 = 20 /\
  Z.gcd 3 20 = 1.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem modulus_N119_cube_shares :
  7 * 17 = 119 /\
  Z.lcm 6 16 = 48 /\
  Z.gcd 3 48 = 3.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem modulus_N209_cube_shares :
  11 * 19 = 209 /\
  Z.lcm 10 18 = 90 /\
  Z.gcd 3 90 = 3.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem modulus_N221_cube_shares :
  13 * 17 = 221 /\
  Z.lcm 12 16 = 48 /\
  Z.gcd 3 48 = 3.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem modulus_N323_cube_shares :
  17 * 19 = 323 /\
  Z.lcm 16 18 = 144 /\
  Z.gcd 3 144 = 3.
Proof. split; [reflexivity|]. split; [vm_compute; reflexivity | reflexivity]. Qed.

Theorem modulus_prime_cube :
  11 * 11 * 11 = 1331.
Proof. reflexivity. Qed.
