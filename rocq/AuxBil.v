From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import PowersOfTau.

Open Scope Z_scope.

(** * Self-bilinear with auxiliary public data

    [self_bilinear] is the bare spec.  The next object is a map
    that is bilinear only given extra public data [aux], without
    iO (iO stays deferred, not refused).  Freezing the auxiliary
    argument recovers [self_bilinear].  If additionally
    [e(aux,g,g) = g], the map *computes* [P_{i+1}] from [P_i]
    and [P_1].  Publishing a computable map of that strength
    extends the string; it is too strong to publish.

    Existence remains a hypothesis.  Cross-confirmed by
    [cas/90_aux_bil.gp] on the discrete-log evaluation of the
    spec (the dlogs are not a construction). *)

Definition aux_self_bilinear (e : Z -> Z -> Z -> Z) (N g aux : Z) : Prop :=
  forall a b,
    0 <= a ->
    0 <= b ->
    e aux (powm g a N) (powm g b N) = powm (e aux g g) (a * b) N.

Lemma aux_is_self_bil :
  forall e N g aux,
    aux_self_bilinear e N g aux ->
    self_bilinear (fun x y => e aux x y) N g.
Proof.
  intros e N g aux H.
  unfold self_bilinear.
  exact H.
Qed.

Theorem aux_self_bil_checks_pot :
  forall e N g aux tau i,
    1 < N ->
    0 <= tau ->
    0 <= i ->
    aux_self_bilinear e N g aux ->
    e aux (pot N g tau i) (pot N g tau 1) =
      e aux (pot N g tau (i + 1)) (pot N g tau 0).
Proof.
  intros e N g aux tau i Hn Ht Hi He.
  apply (self_bil_checks_pot (fun x y => e aux x y) N g tau i Hn Ht Hi).
  apply aux_is_self_bil. exact He.
Qed.

Theorem aux_self_bil_evaluates_pot :
  forall e N g aux tau i,
    1 < N ->
    0 <= tau ->
    0 <= i ->
    aux_self_bilinear e N g aux ->
    e aux g g = g mod N ->
    e aux (pot N g tau i) (pot N g tau 1) = pot N g tau (i + 1).
Proof.
  intros e N g aux tau i Hn Ht Hi He Hgg.
  apply (self_bil_evaluates_pot (fun x y => e aux x y) N g tau i Hn Ht Hi).
  - apply aux_is_self_bil. exact He.
  - exact Hgg.
Qed.

(** If [e] and [aux] are public and [e(aux,g,g) = g], anyone
    extends the string.  That is the same strength as a public
    self-bilinear map with [e(g,g) = g]. *)
Theorem aux_eval_publishes_next :
  forall e N g aux tau i,
    1 < N ->
    0 <= tau ->
    0 <= i ->
    aux_self_bilinear e N g aux ->
    e aux g g = g mod N ->
    e aux (pot N g tau i) (pot N g tau 1) = pot N g tau (i + 1).
Proof. apply aux_self_bil_evaluates_pot. Qed.

Theorem forget_aux_is_self_bil :
  forall e0 N g aux,
    aux_self_bilinear (fun _ x y => e0 x y) N g aux ->
    self_bilinear e0 N g.
Proof.
  intros e0 N g aux H.
  apply (aux_is_self_bil (fun _ x y => e0 x y) N g aux H).
Qed.
