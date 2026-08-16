From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import FermatFactor.
Require Import KeyGen.

Open Scope Z_scope.

(** * Type A geometries that modern keygens actually commit

    Fermat is the geometry [f = ⌈√N⌉].  Three common *generation*
    geometries produce a short [|p−q|] without looking like "pick
    close primes on purpose":

    - increment-from-a-shared-start (or a short window),
    - adjacent / nextprime-twin sampling,
    - shared high bits (same top half of [p] and [q]).

    Each bounds [|p−q|] by a public or generation-side quantity, so
    [kg_far] fails.  Cross-confirmed by [cas/17_keygen_geom.gp] and
    the sampler [cas/13_keygen_sampler.gp]. *)

(** [p] and [q] have the same bits above position [s]: they lie in
    one interval of length [2^s]. *)
Definition shared_high_bits (p q s : Z) : Prop :=
  0 <= s /\ 0 <= p /\ 0 <= q /\ p / 2 ^ s = q / 2 ^ s.

Theorem shared_high_bits_bound :
  forall p q s,
    shared_high_bits p q s ->
    Z.abs (p - q) < 2 ^ s.
Proof.
  intros p q s [Hs [Hp [Hq Heq]]].
  assert (0 < 2 ^ s) as H2 by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod p (2 ^ s) ltac:(lia)) as Hpmod.
  pose proof (Z.div_mod q (2 ^ s) ltac:(lia)) as Hqmod.
  pose proof (Z.mod_pos_bound p (2 ^ s) H2) as Hpb.
  pose proof (Z.mod_pos_bound q (2 ^ s) H2) as Hqb.
  rewrite Heq in Hpmod.
  lia.
Qed.

Theorem shared_high_bits_fails_far :
  forall p q s gap,
    shared_high_bits p q s ->
    0 <= gap ->
    2 ^ s <= 2 ^ gap ->
    ~ kg_far p q gap.
Proof.
  intros p q s gap Hsh Hgap Hle [Hgn Habs].
  pose proof (shared_high_bits_bound p q s Hsh) as Hbd.
  (* |p-q| < 2^s ≤ 2^gap ≤ |p-q| *)
  lia.
Qed.

(** Both primes came from incrementing inside [[x, x+W)]. *)
Definition increment_window (p q x W : Z) : Prop :=
  0 < W /\ x <= p < x + W /\ x <= q < x + W.

Theorem increment_window_bound :
  forall p q x W,
    increment_window p q x W ->
    Z.abs (p - q) < W.
Proof.
  intros p q x W [_ [Hp Hq]]. lia.
Qed.

Theorem increment_window_fails_far :
  forall p q x W gap,
    increment_window p q x W ->
    0 <= gap ->
    W <= 2 ^ gap ->
    ~ kg_far p q gap.
Proof.
  intros p q x W gap Hwin Hgap Hle [Hgn Habs].
  pose proof (increment_window_bound p q x W Hwin) as Hbd.
  lia.
Qed.

(** Consecutive odd numbers (twin-prime / nextprime-adjacent shape). *)
Definition adjacent_odd (p q : Z) : Prop :=
  Z.odd p = true /\ Z.odd q = true /\ Z.abs (p - q) = 2.

Theorem adjacent_fermat_diff :
  forall p q,
    adjacent_odd p q ->
    Z.abs (fermat_diff p q) = 1.
Proof.
  intros p q [Hp [Hq Hadj]].
  pose proof (fermat_diff_abs p q Hp Hq) as H2.
  rewrite Hadj in H2.
  (* 2 = 2 * |fermat_diff| *)
  nia.
Qed.

Theorem adjacent_fails_far_ge2 :
  forall p q gap,
    adjacent_odd p q ->
    2 <= gap ->
    ~ kg_far p q gap.
Proof.
  intros p q gap [Hp [Hq Hadj]] Hgap [_ Habs].
  rewrite Hadj in Habs.
  assert (4 <= 2 ^ gap).
  { change 4 with (2 ^ 2). apply Z.pow_le_mono_r; lia. }
  lia.
Qed.

(** Half-bit shared prefix: [s] is half the bit length of [p].
    Then [|p−q|] is at most [√p]-class, which is Fermat-food for
    balanced primes (steps ≈ [(|p−q|)^2 / (p+q)] become small). *)
Definition half_bits_shared (p q : Z) : Prop :=
  0 < p /\ shared_high_bits p q (Z.log2 p / 2).
