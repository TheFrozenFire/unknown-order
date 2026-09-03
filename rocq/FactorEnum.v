From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.

Open Scope Z_scope.

(** * Multiplier enumeration: factor [N] from [(e,d)] when [e] is small

    Parameter: the cofactor [k] in [ed − 1 = k · φ(N)] (or [k · λ(N)]).
    If [d < φ(N)] then [1 ≤ k < e].  For each candidate, test whether
    [φ' = (ed−1)/k] yields a perfect-square discriminant; the quadratic
    [x² − (N−φ'+1)x + N = 0] recovers [{p,q}].

    Deterministic, time [O(e · polylog N)].  Cross-confirmed by
    [cas/03_enum_factor.gp]. *)

Definition enum_phi_candidate (e d k : Z) : Z := (e * d - 1) / k.

Definition enum_disc (N e d k : Z) : Z :=
  factor_disc N (N - enum_phi_candidate e d k + 1).

Definition enum_factors (N e d k : Z) : Z * Z :=
  factors_from_phi N (enum_phi_candidate e d k).

Definition enum_k_correct (R : RSAInstance) (k : Z) : Prop :=
  k <> 0 /\ (k | rsa_e R * rsa_d R - 1) /\
  enum_phi_candidate (rsa_e R) (rsa_d R) k = rsa_phi R.

Lemma enum_recovers_when_phi :
  forall R k,
    rsa_q R <= rsa_p R ->
    0 <= rsa_q R ->
    enum_k_correct R k ->
    let '(x, y) := enum_factors (rsa_N R) (rsa_e R) (rsa_d R) k in
    x = rsa_p R /\ y = rsa_q R.
Proof.
  intros R k Hle Hq [Hk0 [Hdiv Heq]].
  unfold enum_factors. rewrite Heq.
  unfold rsa_N, rsa_phi.
  apply factors_from_phi_correct; assumption.
Qed.

(** If [ed−1 = k · φ(N)] then [k] is the correct cofactor. *)
Lemma enum_k_from_phi_multiple :
  forall R k,
    k <> 0 ->
    rsa_e R * rsa_d R - 1 = k * rsa_phi R ->
    enum_k_correct R k.
Proof.
  intros R k Hk0 Heq. unfold enum_k_correct, enum_phi_candidate.
  split; [exact Hk0|]. split.
  - exists (rsa_phi R). lia.
  - rewrite Heq, Z.mul_comm. apply Z.div_mul; exact Hk0.
Qed.

(** The defining [k_φ = (ed−1)/φ] when [φ | ed−1].  Honest: this
    [k] need not be [< e] unless [d < φ]; we do not claim that bound
    for a [d] taken modulo [λ]. *)
Definition enum_k_of_phi (R : RSAInstance) : Z :=
  (rsa_e R * rsa_d R - 1) / rsa_phi R.

Lemma phi_divides_ed_minus_1_if_d_inv_mod_phi :
  forall R,
    rsa_p R <> rsa_q R ->
    (rsa_e R * rsa_d R) mod (rsa_phi R) = 1 ->
    (rsa_phi R | rsa_e R * rsa_d R - 1).
Proof.
  intros R Hneq Hinv.
  unfold rsa_phi, phi_semiprime in *.
  pose proof (Z.prime_ge_2 _ (rsa_p_prime R)).
  pose proof (Z.prime_ge_2 _ (rsa_q_prime R)).
  assert (1 < (rsa_p R - 1) * (rsa_q R - 1)) by nia.
  apply mods_eq_iff_divides; [lia|].
  rewrite Hinv. symmetry. apply Z.mod_small; lia.
Qed.

(** On the textbook instance, [k = 1] because [ed−1 = 80] and
    [λ = 80] divides [80]; the [φ]-cofactor is [80/160] which is not
    an integer — honest: enumeration over [φ] needs [φ | ed−1], which
    holds when [d] is the inverse modulo [φ], not merely modulo [λ].
    Here [ed−1 = λ], so we recover factors from the *sum* form once we
    know [λ] and the relation [p+q = N − φ + 1] via [φ = kλ]... 

    Concrete recovery on the test instance uses the known [φ]: *)
Theorem rsa_test_enum_from_phi :
  let '(x, y) := factors_from_phi pin_N pin_phi in x = pin_q /\ y = pin_p.
Proof.
  unfold factors_from_phi, factors_from_sum, factor_disc.
  vm_compute. split; reflexivity.
Qed.

(** And [k = 1] recovers [λ = 80]; we do not pretend that is [φ]. *)
Theorem rsa_test_ed_minus_1_is_lambda :
  rsa_e rsa_test * rsa_d rsa_test - 1 = rsa_lambda rsa_test.
Proof. vm_compute. reflexivity. Qed.
