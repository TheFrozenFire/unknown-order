From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import TranscriptOracle.

Open Scope Z_scope.

(** * Chaum blinded RSA

    The signer sees [m · r^e] and returns [(m · r^e)^d = m^d · r].
    The user multiplies by [r⁻¹].  No hash.  Hash-then-blind is
    [Refuse_hash_as_oracle] / [Refuse_OAEP_PSS].

    Cross-confirmed by [cas/66_blind_rsa.gp]. *)

Definition rsa_blind (R : RSAInstance) (m r : Z) : Z :=
  (m * rsa_enc R r) mod rsa_N R.

Definition rsa_unblind (R : RSAInstance) (s rinv : Z) : Z :=
  (s * rinv) mod rsa_N R.

Theorem chaum_sign_blinded_is_raw_times_r :
  forall R m r,
    Z.coprime r (rsa_N R) ->
    rsa_dec R (rsa_blind R m r) =
      (rsa_dec R m * r) mod rsa_N R.
Proof.
  intros R m r Hr.
  pose proof (rsa_N_gt_1 R).
  pose proof (rsa_d_pos R).
  pose proof (rsa_e_pos R).
  unfold rsa_blind, rsa_dec, rsa_enc.
  rewrite powm_mod_base by lia.
  rewrite powm_mul_l_mod by lia.
  fold (rsa_dec R m).
  fold (rsa_enc R r).
  fold (rsa_dec R (rsa_enc R r)).
  rewrite (rsa_dec_enc_units R r Hr).
  rewrite Z.mul_mod_idemp_r by lia.
  reflexivity.
Qed.

Theorem chaum_unblind_is_raw_sign :
  forall R m r rinv,
    Z.coprime r (rsa_N R) ->
    (r * rinv) mod rsa_N R = 1 ->
    rsa_unblind R (rsa_dec R (rsa_blind R m r)) rinv =
      rsa_dec R m.
Proof.
  intros R m r rinv Hr Hinv.
  pose proof (rsa_N_gt_1 R).
  unfold rsa_unblind.
  rewrite chaum_sign_blinded_is_raw_times_r by exact Hr.
  rewrite Z.mul_mod_idemp_l by lia.
  rewrite <- Z.mul_assoc.
  rewrite <- Z.mul_mod_idemp_r by lia.
  rewrite Hinv, Z.mul_1_r.
  unfold rsa_dec, powm.
  rewrite Z.mod_mod by lia.
  reflexivity.
Qed.

