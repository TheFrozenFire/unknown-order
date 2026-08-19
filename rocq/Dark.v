From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * DARK-style openings in unknown order — exponent identities

    A degree-[d] commitment [C = g^{f(s)}] and a witness
    [π = g^{q(s)}] satisfy [f(X) − f(z) = q(X)(X − z)], hence
    [C = π^{s−z} · g^{f(z)}].  That is an identity in the
    exponent.  Checking the right-hand side from public
    [(C, π, z, f(z), g^s)] without the integer [s] is a pairing
    ([Refuse_elliptic_curve_branch]) or a proof of
    exponentiation ([Refuse_this_is_a_VDF]).  Sequentiality is
    not a theorem here.

    Cross-confirmed by [cas/91_dark.gp]. *)

Definition poly1 (a0 a1 x : Z) : Z :=
  a0 + a1 * x.

Definition poly2 (a0 a1 a2 x : Z) : Z :=
  a0 + a1 * x + a2 * x * x.

Definition quot1 (a1 : Z) : Z :=
  a1.

Definition quot2 (a1 a2 s z : Z) : Z :=
  a1 + a2 * (s + z).

Definition dark_commit1 (N g s a0 a1 : Z) : Z :=
  powm g (poly1 a0 a1 s) N.

Definition dark_pi1 (N g a1 : Z) : Z :=
  powm g a1 N.

Definition dark_commit2 (N g s a0 a1 a2 : Z) : Z :=
  powm g (poly2 a0 a1 a2 s) N.

Definition dark_pi2 (N g s z a1 a2 : Z) : Z :=
  powm g (quot2 a1 a2 s z) N.

Lemma poly1_factor :
  forall a0 a1 s z,
    poly1 a0 a1 s - poly1 a0 a1 z = quot1 a1 * (s - z).
Proof. intros. unfold poly1, quot1. ring. Qed.

Lemma poly2_factor :
  forall a0 a1 a2 s z,
    poly2 a0 a1 a2 s - poly2 a0 a1 a2 z =
      quot2 a1 a2 s z * (s - z).
Proof. intros. unfold poly2, quot2. ring. Qed.

Theorem dark_deg1_open :
  forall N g a0 a1 s z,
    1 < N ->
    0 <= a0 ->
    0 <= a1 ->
    0 <= z ->
    z <= s ->
    dark_commit1 N g s a0 a1 =
      (powm (dark_pi1 N g a1) (s - z) N *
         powm g (poly1 a0 a1 z) N) mod N.
Proof.
  intros N g a0 a1 s z Hn Ha0 Ha1 Hz Hsz.
  unfold dark_commit1, dark_pi1, poly1, quot1.
  assert (0 <= s - z) by lia.
  assert (0 <= a0 + a1 * z) by nia.
  assert (0 <= a1 * (s - z)) by nia.
  replace (a0 + a1 * s) with (a1 * (s - z) + (a0 + a1 * z)) by ring.
  rewrite powm_add_r by lia.
  rewrite <- powm_mul_r by lia.
  reflexivity.
Qed.

Theorem dark_deg2_open :
  forall N g a0 a1 a2 s z,
    1 < N ->
    0 <= a0 ->
    0 <= a1 ->
    0 <= a2 ->
    0 <= z ->
    z <= s ->
    dark_commit2 N g s a0 a1 a2 =
      (powm (dark_pi2 N g s z a1 a2) (s - z) N *
         powm g (poly2 a0 a1 a2 z) N) mod N.
Proof.
  intros N g a0 a1 a2 s z Hn Ha0 Ha1 Ha2 Hz Hsz.
  unfold dark_commit2, dark_pi2, poly2, quot2.
  assert (0 <= s - z) by lia.
  assert (0 <= a0 + a1 * z + a2 * z * z) by nia.
  assert (0 <= s) by lia.
  assert (0 <= a1 + a2 * (s + z)) by nia.
  assert (0 <= (a1 + a2 * (s + z)) * (s - z)) by nia.
  replace (a0 + a1 * s + a2 * s * s)
    with ((a1 + a2 * (s + z)) * (s - z) + (a0 + a1 * z + a2 * z * z))
    by ring.
  rewrite powm_add_r by lia.
  rewrite <- powm_mul_r by lia.
  reflexivity.
Qed.

Theorem dark_deg1_commit_is_powm :
  forall N g s a0 a1,
    dark_commit1 N g s a0 a1 = powm g (a0 + a1 * s) N.
Proof. intros. reflexivity. Qed.

Theorem dark_deg2_commit_is_powm :
  forall N g s a0 a1 a2,
    dark_commit2 N g s a0 a1 a2 = powm g (a0 + a1 * s + a2 * s * s) N.
Proof. intros. reflexivity. Qed.
