From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * Partial bits / thin arithmetic progressions

    Knowing the high or low bits of [p], or sampling [p] from a public
    thin AP (ROCA: [p = k M + (65537^a mod M)]), puts a *small*
    unknown in a polynomial that vanishes modulo a factor of [N].
    The unknown is small ([high_bits_unknown_is_x],
    [roca_unknown_is_k]).  Recovery is [coppersmith_named] /
    [Refuse_lattice_lll_development] in [Lattice.v] and
    [NamedSkips].  This file records the generation-side shape.

    Cross-confirmed algebra (the hidden unknown really is small, and
    [p] really lies on the AP) is in [cas/08_fermat.gp] for the
    close-prime special case and recorded as a skip for the lattice
    step. *)

(** [p] with known high bits: [p = p0 + x], [0 ≤ x < X]. *)
Definition high_bits_form (p p0 x X : Z) : Prop :=
  p = p0 + x /\ 0 <= x < X.

(** Low bits known: [p = 2^k * y + p0] with [0 ≤ p0 < 2^k] public. *)
Definition low_bits_form (p p0 y k : Z) : Prop :=
  0 <= k /\ p = 2 ^ k * y + p0 /\ 0 <= p0 < 2 ^ k.

(** ROCA / Infineon form: [p] lies in a public residue class modulo
    a smooth [M] (a primorial).  The unknown is the cofactor [k]. *)
Definition roca_form (p k M residue : Z) : Prop :=
  0 < M /\ p = k * M + residue /\ 0 <= residue < M.

Lemma high_bits_unknown_is_x :
  forall p p0 x X,
    high_bits_form p p0 x X ->
    p - p0 = x /\ 0 <= x < X.
Proof. intros p p0 x X [Heq Hbd]. subst p. split; lia. Qed.

Lemma roca_unknown_is_k :
  forall p k M residue,
    roca_form p k M residue ->
    (p - residue) / M = k /\ (M | p - residue).
Proof.
  intros p k M residue [HM [Heq Hbd]].
  subst p. split.
  - replace (k * M + residue - residue) with (k * M) by ring.
    apply Z.div_mul; lia.
  - exists k. ring.
Qed.

(** The polynomial the lattice step is asked to solve: [f(x) = p0 + x]
    shares a factor with [N] at the unknown [x].  Stated, not solved. *)
Definition bitleak_poly (p0 x : Z) : Z := p0 + x.

Lemma bitleak_poly_divides_N :
  forall p q p0 x X,
    high_bits_form p p0 x X ->
    bitleak_poly p0 x * q = p * q.
Proof.
  intros p q p0 x X Hform.
  unfold high_bits_form, bitleak_poly in *.
  destruct Hform as [Heq Hbd]. subst p. ring.
Qed.


