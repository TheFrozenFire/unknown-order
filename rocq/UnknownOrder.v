From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.

Open Scope Z_scope.

(** * Computational problems in a group of unknown order

    The public object is [G = (Z/NZ)*] with [N = pq].  The group
    operation is efficient; [|G| = φ(N)] and the exponent [λ(N)] are
    not part of the public input.  RSA is the defining example of this
    class: the RSA problem *is* [e]-th-root extraction in [G].

    Later problems (strong RSA, order, adaptive root) are stated here
    as propositions so they share one vocabulary.  None is assumed
    hard — we only write down what the problem *asks*.  Relation-level
    arrows (trapdoor, RSA vs strong RSA, order divides [λ], one-sided
    split) live in [Hardness.v].  A hardness *claim* is a sentence
    about a KeyGen distribution; see [THEORY.md] §9. *)

(** The hidden-order group attached to an RSA instance. *)
Definition hidden_order_N (R : RSAInstance) : Z := rsa_N R.

(** Knowing the order (or any multiple of [λ]) is a trapdoor: it
    produces [d] by inversion, hence roots. *)
Definition trapdoor_from_lambda (R : RSAInstance) (lam : Z) : Prop :=
  lam = rsa_lambda R.

Lemma trapdoor_gives_inverse :
  forall R,
    Z.coprime (rsa_e R) (rsa_lambda R) ->
    (rsa_e R * rsa_d R) mod (rsa_lambda R) = 1.
Proof. intros R _. apply rsa_d_inv. Qed.

(** ** The named problems *)

(** RSA: given [(N,e,y)], find [x] with [x^e ≡ y (mod N)]. *)
Definition Problem_RSA (N e y : Z) (x : Z) : Prop :=
  rsa_problem N e y x.

(** Strong RSA: given [(N,y)], find [e > 1] and [x] with [x^e ≡ y (mod N)]. *)
Definition Problem_StrongRSA (N y : Z) (x e : Z) : Prop :=
  1 < e /\ powm x e N = y.

(** Order problem: given [(N,a)], find the order of [a] in [(Z/NZ)*]. *)
Definition is_order (N a k : Z) : Prop :=
  0 < k /\
  powm a k N = 1 /\
  forall k', 0 < k' < k -> powm a k' N <> 1.

Definition Problem_Order (N a : Z) (k : Z) : Prop :=
  Z.coprime a N -> is_order N a k.

(** Low-order: find a non-identity element of small order. *)
Definition Problem_LowOrder (N B : Z) (a k : Z) : Prop :=
  Z.coprime a N /\ 1 < a < N /\ is_order N a k /\ k <= B.

(** Adaptive root (informal shape): given a random [y], produce [e > 1]
    and [x] with [x^e ≡ y (mod N)] — the same shape as strong RSA, used
    as the named assumption in class groups / unknown-order accumulators.
    Stated, not assumed. *)
Definition Problem_AdaptiveRoot (N y : Z) (x e : Z) : Prop :=
  Problem_StrongRSA N y x e.

(** ** What the trapdoor actually buys *)

Theorem lambda_solves_RSA_on_units :
  forall R y x,
    Z.coprime x (rsa_N R) ->
    rsa_enc R x = y ->
    rsa_dec R y = x mod rsa_N R.
Proof.
  intros R y x Hcop Henc.
  rewrite <- Henc. apply rsa_dec_enc_units; exact Hcop.
Qed.

(** Possession of [d] is possession of a multiple of [λ], hence of a
    factoring procedure (see [Miller] / [FactorEnum]).  The two pieces
    of information are computationally interchangeable in the sense
    formalized there; we do not claim a complexity-theoretic reduction
    with running-time bounds. *)
Theorem d_yields_annihilator :
  forall R, (rsa_lambda R | rsa_e R * rsa_d R - 1).
Proof. apply rsa_ed_minus_1_divides. Qed.
