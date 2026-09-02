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
  187 * 187 = 34969 /\
  powm (1 + 187) 1 (187 * 187) = (1 + 1 * 187) mod (187 * 187).
Proof.
  split; [reflexivity|].
  apply one_plus_N_pow; lia.
Qed.

Theorem modulus_williams_Ve :
  lucasV 62 1 3%nat = 238142 /\
  238142 mod 187 = 91 /\
  91 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem modulus_ou_carrier :
  takagi_N 3 5 = 45 /\
  powm (1 + 3) 2 (3 * 3) = (1 + 2 * 3) mod (3 * 3).
Proof.
  split; [reflexivity|].
  apply one_plus_p_pow; lia.
Qed.

Theorem modulus_dj_carrier :
  187 * 187 * 187 = 6539203.
Proof. reflexivity. Qed.

Theorem modulus_cocks_jacobi :
  jacobi_N 36 11 17 = 1.
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
  11 mod 8 = 3 /\
  23 mod 8 = 7.
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
  3 * 5 * 7 = 105 /\
  Z.lcm (Z.lcm 2 4) 6 = 12 /\
  Z.gcd 3 12 = 3 /\
  Z.gcd 3 12 <> 1.
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
