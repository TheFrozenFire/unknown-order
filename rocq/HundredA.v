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

Open Scope Z_scope.

(** * Hundred classes A (1–12)

    Odd monomial, associate, midpoint, [φ(y)] / Hamming [e],
    Shamir two leftovers, Paillier, [V_e], LSB [e], [x=y^e],
    [e=25], Coppersmith bound.  Cross-confirmed by [cas/133]. *)

Theorem hun_01_odd_monomial :
  powm 36 3 187 = 93 /\
  powm 93 3 187 = 70 /\
  70 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_02_associate :
  powm (187 - 42) 3 187 = 151 /\
  151 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_03_midpoint :
  187 / 2 = 93 /\
  Z.abs (36 - 93) = 57 /\
  powm 57 3 187 = 63 /\
  63 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_04_phi_y_even :
  Z.even 12 = true /\
  12 = 12.
Proof. split; reflexivity. Qed.

Theorem hun_05_hamming_even :
  36 = 2 ^ 5 + 2 ^ 2 /\
  Z.even 2 = true.
Proof. split; reflexivity. Qed.

Theorem hun_06_shamir_two_leftovers :
  Z.gcd 3 7 = 1 /\
  powm 42 3 187 = 36 /\
  powm 60 7 187 = 36.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem hun_07_paillier_carrier :
  187 * 187 = 34969 /\
  powm (1 + 187) 1 (187 * 187) = (1 + 1 * 187) mod (187 * 187).
Proof.
  split; [reflexivity|].
  apply one_plus_N_pow; lia.
Qed.

Theorem hun_08_williams_Ve :
  lucasV 62 1 3%nat = 238142 /\
  238142 mod 187 = 91 /\
  91 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

Theorem hun_09_lsb_y_even :
  Z.even 36 = true.
Proof. reflexivity. Qed.

Theorem hun_10_encrypt_as_decrypt :
  powm 36 3 187 = 93 /\
  93 <> 42.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem hun_11_e25_shares_lambda :
  Z.gcd 25 80 = 5 /\
  Z.gcd 25 80 <> 1.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem hun_12_not_coppersmith_small :
  2 ^ 9 > 187 /\
  42 >= 2 /\
  ~ (42 ^ 9 < 187).
Proof.
  change (2 ^ 9) with 512.
  split; [lia|].
  split; [lia|].
  intros Hle. vm_compute in Hle. discriminate.
Qed.
