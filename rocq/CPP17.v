From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import Accumulator.
Require Import GQ.

Open Scope Z_scope.

(** * Couteau–Peters–Pointcheval (EUROCRYPT 2017) shape

    An integer Σ (Guillou–Quisquater) extracts a root at the
    *public* [e], hence [Problem_RSA], not a freely chosen Strong-RSA
    exponent.  The protocol is not a NIZK; HVZK/ROM stay refused.
    Cross-confirmed by [cas/126]. *)

Theorem cpp17_witness_is_rsa :
  Problem_RSA pin_N 3 36 42.
Proof. unfold Problem_RSA, rsa_problem. vm_compute. reflexivity. Qed.

Theorem cpp17_complete_pin :
  gq_verify 36 3 (gq_commit 1 3 pin_N) 1 (gq_response 1 42 1 pin_N) pin_N.
Proof.
  apply gq_complete; try lia.
  unfold powm. vm_compute. reflexivity.
Qed.

Theorem cpp17_second_transcript :
  gq_verify 36 3 (gq_commit 2 3 pin_N) 0 (gq_response 2 42 0 pin_N) pin_N.
Proof.
  apply gq_complete; try lia.
  unfold powm. vm_compute. reflexivity.
Qed.

Theorem cpp17_shamir_gcd_pin :
  Z.gcd (1 - 0) 3 = 1.
Proof. reflexivity. Qed.

Theorem cpp17_extract_is_fixed_e :
  forall w,
    powm w 3 pin_N = 36 ->
    Problem_RSA pin_N 3 36 w.
Proof.
  intros w H. unfold Problem_RSA, rsa_problem. exact H.
Qed.

Theorem cpp17_protocol_e_is_three :
  3 <> 81.
Proof. discriminate. Qed.

Theorem cpp17_srsa_other_pair :
  Problem_StrongRSA pin_N 36 36 81.
Proof.
  unfold Problem_StrongRSA. split; [lia|].
  vm_compute. reflexivity.
Qed.

Theorem cpp17_sigma_does_not_output_that_pair :
  gq_verify 36 3 (gq_commit 1 3 pin_N) 1 (gq_response 1 42 1 pin_N) pin_N ->
  3 <> 81.
Proof. intros _. apply cpp17_protocol_e_is_three. Qed.
