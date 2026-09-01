From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.

Open Scope Z_scope.

(** * Extra search relations: one-more RSA, GHR prime-[e], φ-hiding

    Named winning conditions, not PPT games.  φ-hiding is [e | λ(N)],
    not [Refuse_PPT_advantage].  Cross-confirmed by [cas/125]. *)

(** ** One-more RSA *)

Definition answers_queries (N e : Z) (ys xs : list Z) : Prop :=
  length ys = length xs /\
  Forall2 (fun y x => powm x e N = y) ys xs.

Definition Problem_OneMore (N e : Z) (ys xs : list Z) (y' x' : Z) : Prop :=
  answers_queries N e ys xs /\
  powm x' e N = y' /\
  ~ In y' ys.

Theorem one_more_pin :
  Problem_OneMore 187 3 [36] [42] 8 2.
Proof.
  unfold Problem_OneMore, answers_queries.
  split.
  - split; [reflexivity|].
    apply Forall2_cons; [vm_compute; reflexivity | apply Forall2_nil].
  - split; [vm_compute; reflexivity|].
    intros Hin. inversion Hin as [Heq | Hrest]; [discriminate | inversion Hrest].
Qed.

Theorem one_more_queried_is_not_extra :
  ~ Problem_OneMore 187 3 [36] [42] 36 42.
Proof.
  unfold Problem_OneMore. intros [_ [_ Hin]].
  apply Hin. left. reflexivity.
Qed.

(** ** GHR: prime public [e] *)

Definition Problem_GHR (N e y x : Z) : Prop :=
  Z.prime e /\ Problem_RSA N e y x.

Lemma prime_3 : Z.prime 3.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2) by lia.
  intuition subst; reflexivity.
Qed.

Theorem ghr_pin :
  Problem_GHR 187 3 36 42.
Proof.
  unfold Problem_GHR, Problem_RSA, rsa_problem.
  split; [apply prime_3 | vm_compute; reflexivity].
Qed.

Theorem ghr_is_rsa :
  forall N e y x, Problem_GHR N e y x -> Problem_RSA N e y x.
Proof. intros N e y x [_ H]. exact H. Qed.

Theorem ghr_prime_e_shamir_gcd :
  forall e delta,
    Z.prime e ->
    ~ (e | delta) ->
    Z.gcd delta e = 1.
Proof.
  intros e delta Hp Hnd.
  rewrite Z.gcd_comm.
  apply Z.coprime_prime_l_iff; [exact Hp | exact Hnd].
Qed.

Theorem ghr_shamir_gcd_pin :
  Z.gcd 1 3 = 1.
Proof. reflexivity. Qed.

(** ** φ-hiding: [e | λ(N)], a relation, not a PPT game *)

Definition Problem_PhiHiding (p q e : Z) : Prop :=
  1 < e /\ (e | lambda_semiprime p q).

Theorem phi_hiding_lambda_80 :
  lambda_semiprime 11 17 = 80.
Proof. vm_compute. reflexivity. Qed.

Theorem phi_hiding_pin_e5 :
  Problem_PhiHiding 11 17 5.
Proof.
  unfold Problem_PhiHiding. split; [lia|].
  exists 16. rewrite phi_hiding_lambda_80. reflexivity.
Qed.

Theorem phi_hiding_public_e3_misses :
  ~ Problem_PhiHiding 11 17 3.
Proof.
  unfold Problem_PhiHiding. intros [_ [k Hk]].
  rewrite phi_hiding_lambda_80 in Hk.
  nia.
Qed.
