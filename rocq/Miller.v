From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import RSA.

Open Scope Z_scope.

(** * Miller successive-squaring: factor [N] from a multiple of [λ(N)]

    Write [M = ed−1 = 2^s · t] with [t] odd.  For a base [a] coprime to
    [N], set [g₀ ≡ a^t (mod N)] and [g_{i+1} ≡ g_i² (mod N)].  The first
    [g_j ≡ 1] with [g_{j−1} ≢ ±1] yields [gcd(g_{j−1}−1, N)] as a
    non-trivial factor.

    A base succeeds iff the 2-adic valuations of the orders of [a] modulo
    [p] and modulo [q] differ.  Cross-confirmed by [cas/04_miller_factor.gp]. *)

Definition miller_M (R : RSAInstance) : Z := rsa_e R * rsa_d R - 1.
Definition miller_s (R : RSAInstance) : nat := val2 (miller_M R).
Definition miller_t (R : RSAInstance) : Z := odd_part (miller_M R).

Lemma miller_M_pos : forall R, 0 < miller_M R.
Proof. intros R. pose proof (rsa_ed_gt_1 R). unfold miller_M. lia. Qed.

Lemma miller_M_split :
  forall R, miller_M R = 2 ^ Z.of_nat (miller_s R) * miller_t R.
Proof.
  intros R. unfold miller_s, miller_t, miller_M.
  apply split2_of_reconstructs. pose proof (rsa_ed_gt_1 R). lia.
Qed.

Lemma miller_t_nonneg : forall R, 0 <= miller_t R.
Proof.
  intros R. unfold miller_t, miller_M.
  apply odd_part_nonneg. pose proof (rsa_ed_gt_1 R). lia.
Qed.

Lemma miller_M_annihilates :
  forall R a,
    Z.coprime a (rsa_N R) ->
    powm a (miller_M R) (rsa_N R) = 1.
Proof.
  intros R a Hcop. unfold miller_M, rsa_N.
  apply annihilates_units.
  - apply rsa_p_prime.
  - apply rsa_q_prime.
  - apply rsa_distinct.
  - exact Hcop.
  - pose proof (rsa_ed_gt_1 R). lia.
  - apply rsa_ed_minus_1_divides.
Qed.

(** The successive-squaring sequence, as a list of length [s+1]. *)
Fixpoint miller_seq (a t N : Z) (s : nat) : list Z :=
  match s with
  | O => [powm a t N]
  | S s' =>
      let gs := miller_seq a t N s' in
      gs ++ [powm (last gs 0) 2 N]
  end.

Definition miller_g0 (a t N : Z) : Z := powm a t N.

(** A base is a *splitting witness* when some iterate is a non-trivial
    square root of 1. *)
Definition miller_splits (a N g : Z) : Prop :=
  powm g 2 N = 1 /\ g mod N <> 1 /\ g mod N <> N - 1.

Theorem miller_witness_factors :
  forall R a g,
    Z.coprime a (rsa_N R) ->
    miller_splits a (rsa_N R) g ->
    let f := Z.gcd (g - 1) (rsa_N R) in
    1 < f /\ f < rsa_N R /\ (f | rsa_N R).
Proof.
  intros R a g Hcop [Hsq [Hn1 Hnm1]].
  unfold rsa_N.
  apply nontrivial_sqrt1_splits.
  - apply rsa_p_prime.
  - apply rsa_q_prime.
  - apply rsa_distinct.
  - exact Hsq.
  - exact Hn1.
  - exact Hnm1.
Qed.

(** Sequential-base Miller: try the first [n] positive integers as bases.
    Deterministic; polynomial runtime is ERH-conditional (Miller 1976).
    We do not claim the ERH bound. *)
Fixpoint first_n_bases (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => first_n_bases n' ++ [Z.of_nat (S n')]
  end.

Definition miller_try_base (R : RSAInstance) (a : Z) : Z :=
  Z.gcd (powm a (miller_t R) (rsa_N R) - 1) (rsa_N R).

(** On the textbook instance [M = 80 = 16·5], so [s = 4], [t = 5]. *)
Theorem rsa_test_miller_split : miller_M rsa_test = 80.
Proof. vm_compute. reflexivity. Qed.

Theorem rsa_test_miller_t : miller_t rsa_test = 5.
Proof. vm_compute. reflexivity. Qed.

Theorem rsa_test_miller_s : miller_s rsa_test = 4%nat.
Proof. vm_compute. reflexivity. Qed.

(** Base [a = 2]: [2^5 = 32], and some square in the chain splits 187. *)
Theorem rsa_test_base2_g0 : powm 2 5 187 = 32.
Proof. vm_compute. reflexivity. Qed.

(** [2^5 = 32], [32² ≡ 89], [89² ≡ 67], [67² ≡ 1].  Then [67 ≢ ±1]
    and [gcd(66, 187) = 11]. *)
Theorem rsa_test_base2_chain :
  powm 32 2 187 = 89 /\
  powm 89 2 187 = 67 /\
  powm 67 2 187 = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem rsa_test_base2_splits :
  miller_splits 2 187 67 /\
  Z.gcd (67 - 1) 187 = 11.
Proof.
  split.
  - unfold miller_splits. vm_compute. repeat split; discriminate.
  - vm_compute. reflexivity.
Qed.
