From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import NamedSkips.

Open Scope Z_scope.

(** * Lattice / Coron–May interface

    From [ed − 1 = k · φ(N)] one builds a modular polynomial with a
    small root related to [k] or to [p+q].  The quadratic of
    [factors_from_phi] then splits [N].

    LLL / Howgrave–Graham / Coppersmith recovery is
    [coppersmith_named] (unused refuse) and
    [Refuse_lattice_lll_development].  What is proved: once [φ]
    or [p+q] is in hand, the factors drop out ([is_phi_of],
    [lattice_phi_factors], [lattice_sum_factors]). *)

(** The useful hypothesis: a value that *is* [φ(pq)].  Not an
    oracle, not a tautology. *)
Definition is_phi_of (p q phi : Z) : Prop :=
  phi = phi_semiprime p q.

Theorem lattice_phi_factors :
  forall p q phi,
    0 <= q -> q <= p ->
    is_phi_of p q phi ->
    let '(x, y) := factors_from_phi (p * q) phi in
    x = p /\ y = q.
Proof.
  intros p q phi Hq Hle Heq. unfold is_phi_of in Heq. subst phi.
  apply factors_from_phi_correct; assumption.
Qed.

Theorem lattice_sum_factors :
  forall p q s,
    0 <= q -> q <= p ->
    s = p + q ->
    let '(x, y) := factors_from_sum (p * q) s in
    x = p /\ y = q.
Proof.
  intros p q s Hq Hle Heq. subst s.
  apply factors_from_sum_correct; assumption.
Qed.

(** If a recovery step returns [k] with [ed−1 = k·φ], we obtain [φ]
    by division and fall back to [lattice_phi_factors]. *)
Definition phi_from_k (e d k : Z) : Z := (e * d - 1) / k.

Lemma phi_from_k_correct :
  forall e d k phi,
    k <> 0 ->
    e * d - 1 = k * phi ->
    phi_from_k e d k = phi.
Proof.
  intros e d k phi Hk Heq. unfold phi_from_k.
  rewrite Heq, Z.mul_comm. apply Z.div_mul; exact Hk.
Qed.

(** Numeric Coppersmith window ([|x|^δ < N]).  Recovery of the
    root is [Refuse_lattice_lll_development].  Unused as a
    hypothesis of any recovery theorem. *)
Definition coppersmith_named (N delta X : Z) : Prop :=
  0 < delta /\ 0 < N /\ 0 < X /\ X ^ delta < N.
