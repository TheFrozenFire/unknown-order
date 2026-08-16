From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.

Open Scope Z_scope.

(** * Lattice / Coron–May interface

    From [ed − 1 = k · φ(N)] one builds a modular polynomial with a
    small root related to [k] or to [p+q].  Coppersmith / LLL recovers
    that root; the quadratic of [NumberTheory.factors_from_phi] then
    splits [N].

    We do **not** formalize LLL or Howgrave–Graham.  What is proved:
    once [φ] or [p+q] is in hand, the factors drop out.  The lattice
    step is an opaque recovery hypothesis — honest closure (rule 5).

    Conversation-claimed regime ([ed ≤ N²] polynomial, [ed ≤ N^{3/2}]
    in [O(log² N)]) is recorded as documentation, not a theorem. *)

(** A *φ-oracle* is whatever the lattice step is supposed to return. *)
Definition recovers_phi (N e d phi : Z) : Prop :=
  phi = N - ((N - phi + 1)) + 1.  (* tautological shape; see below *)

(** The useful hypothesis: a value that *is* [φ(pq)]. *)
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

(** If the lattice step returns [k] with [ed−1 = k·φ], we obtain [φ]
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

(** Honest skip: Coppersmith's theorem (a small root of a modular
    polynomial of degree [δ] below [N^{1/δ}] is recoverable in poly
    time) is not proved here.  The algebraic *use* of that root is. *)
Definition coppersmith_bound (N delta : Z) : Z :=
  (* informal; not used in proofs *)
  N.
