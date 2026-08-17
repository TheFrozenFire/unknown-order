From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import BitLeak.
Require Import KeyGenCtor.
Require Import HashSlot.

Open Scope Z_scope.

(** * Challenge / member encoding: odd integers, not the constructor AP

    Map B is not map A.  [ch_encode seed = 2·seed+1] lands on odd
    positives.  Accept is primality.  There is no [p±1] / [Φn] /
    Blum obligation.  The image is not the constructor slot.

    Prime [ℓ] in Wesolowski is a soundness constraint; the algebra
    in [ExpProof] only needs [0 < ℓ] (see
    [wesolowski_root_does_not_need_prime_ell]).  Accumulator
    members want primes because a composite member splits the
    witness ([rsa_composite_member_splits_witness]).

    No hash, no ROM.  CAS [cas/31_challenge_prime.gp]. *)

Definition ch_encode (seed : Z) : Z := 2 * seed + 1.

Definition ch_accept (seed : Z) : Prop := Z.prime (ch_encode seed).

Theorem ch_encode_odd :
  forall seed, Z.odd (ch_encode seed) = true.
Proof.
  intros seed. unfold ch_encode.
  apply Z.odd_spec. exists seed. reflexivity.
Qed.

Theorem ch_accept_is_prime :
  forall seed, ch_accept seed -> Z.prime (ch_encode seed).
Proof. intros seed H. exact H. Qed.

Theorem ch_encode_not_slot_residue :
  ch_encode 0 mod 103740 <> 13099.
Proof. vm_compute. discriminate. Qed.

Theorem ch_image_is_not_slot_image :
  forall S,
    ss_a S = 13099 ->
    sa_mod (ss_aux S) = 103740 ->
    ~ public_ap_discriminates S (ch_encode 0).
Proof.
  intros S Ha HM.
  unfold public_ap_discriminates. rewrite Ha, HM.
  exact ch_encode_not_slot_residue.
Qed.

Theorem ch_encode_not_roca_on_cas28 :
  ~ roca_form (ch_encode 0) 0 103740 13099.
Proof.
  unfold roca_form, ch_encode. intros [_ [Heq _]]. lia.
Qed.
