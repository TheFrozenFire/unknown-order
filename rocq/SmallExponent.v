From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.

Open Scope Z_scope.

(** * Small public [e]: the RSA map is a low-degree polynomial

    [e = 3] is a valid inverse-mod-[λ] choice and does not factor [N].
    It makes encryption [m ↦ m³ (mod N)], so Coppersmith / Hastad apply
    to small or stereotyped [m].  This file records that shape and the
    broadcast collision.  Lattice recovery is [coppersmith_named].

    Cross-confirmed by [cas/12_small_e.gp]. *)

Definition rsa_poly (e N m : Z) : Z := powm m e N.

Lemma rsa_poly_degree_is_e :
  forall R m, rsa_enc R m = powm m (rsa_e R) (rsa_N R).
Proof. intros. reflexivity. Qed.

(** The useful, checkable core: [powm m 3 N = (m^3) mod N]. *)
Lemma cube_is_powm3 :
  forall m N, N <> 0 -> powm m 3 N = (m * m * m) mod N.
Proof.
  intros m N HN. unfold powm.
  change 3 with (Z.succ 2). rewrite Z.pow_succ_r, Z.pow_2_r by lia.
  f_equal. ring.
Qed.

Lemma unique_nonneg_rep :
  forall x y M,
    0 < M ->
    0 <= x < M ->
    0 <= y < M ->
    (M | x - y) ->
    x = y.
Proof.
  intros x y M HM Hx Hy [k Hk].
  assert (x - y = 0).
  { assert (- M < x - y < M) by lia.
    assert (k = 0) by nia. lia. }
  lia.
Qed.

Lemma three_moduli_divide :
  forall a b N1 N2 N3,
    0 < N1 -> 0 < N2 -> 0 < N3 ->
    Z.coprime N1 N2 -> Z.coprime N1 N3 -> Z.coprime N2 N3 ->
    a mod N1 = b mod N1 ->
    a mod N2 = b mod N2 ->
    a mod N3 = b mod N3 ->
    (N1 * N2 * N3 | a - b).
Proof.
  intros a b N1 N2 N3 HN1 HN2 HN3 H12 H13 H23 H1 H2 H3.
  assert (N1 | a - b) as D1 by (apply mods_eq_iff_divides; [lia | exact H1]).
  assert (N2 | a - b) as D2 by (apply mods_eq_iff_divides; [lia | exact H2]).
  assert (N3 | a - b) as D3 by (apply mods_eq_iff_divides; [lia | exact H3]).
  assert (Z.coprime N1 (N2 * N3)) as H1p.
  { apply coprime_mul_iff. split; assumption. }
  assert (N2 * N3 | a - b) as D23.
  { apply divide_by_coprime_product; assumption. }
  replace (N1 * N2 * N3) with (N1 * (N2 * N3)) by ring.
  apply divide_by_coprime_product; assumption.
Qed.

(** Hastad's broadcast, algebraically: the same [m] sent under [e = 3]
    to three pairwise-coprime moduli.  If [0 ≤ m³ < N₁ N₂ N₃] and the
    CRT representative [c] of the three ciphertexts lies in the same
    interval, then [c] *is* [m³] in [ℤ] — no lattice step. *)
Theorem hastad_cube_if_small :
  forall m c N1 N2 N3,
    0 <= m ->
    0 < N1 -> 0 < N2 -> 0 < N3 ->
    0 <= c < N1 * N2 * N3 ->
    c mod N1 = powm m 3 N1 ->
    c mod N2 = powm m 3 N2 ->
    c mod N3 = powm m 3 N3 ->
    0 <= m * m * m < N1 * N2 * N3 ->
    Z.coprime N1 N2 -> Z.coprime N1 N3 -> Z.coprime N2 N3 ->
    c = m * m * m.
Proof.
  intros m c N1 N2 N3 Hm HN1 HN2 HN3 Hc H1 H2 H3 Hm3 C12 C13 C23.
  rewrite cube_is_powm3 in H1, H2, H3 by lia.
  assert (N1 * N2 * N3 | c - m * m * m) as Hdiv.
  { apply three_moduli_divide; try assumption. }
  apply unique_nonneg_rep with (M := N1 * N2 * N3); lia || exact Hdiv.
Qed.

(** Franklin–Reiter shape: a known offset [δ] between two messages
    under the same key is a polynomial relation.  [m] is a common
    root of [X^e − c1] and [(X+δ)^e − c2].  Degree-1 recovery of that
    gcd is [Refuse_polynomial_gcd_over_ZN]. *)
Lemma related_message_common_root :
  forall e N m delta c1 c2,
    N <> 0 -> 0 <= e ->
    c1 = powm m e N ->
    c2 = powm (m + delta) e N ->
    powm m e N = c1 /\ powm (m + delta) e N = c2.
Proof. intros. split; congruence. Qed.
