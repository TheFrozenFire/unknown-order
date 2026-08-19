From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import Paillier.

Open Scope Z_scope.

(** * Damgård–Jurik: the [s = 2] binomial on [N³]

    Paillier is [s = 1]: [(1+N)^m ≡ 1 + m N (mod N²)].
    One more term: [(1+N)^m ≡ 1 + m N + C(m,2) N² (mod N³)].
    Higher [s] is the same binomial, not a new group.
    DCR / DJ-residuosity stay [Refuse_PPT_advantage].

    Cross-confirmed by [cas/77_damgard_jurik.gp]. *)

Theorem one_plus_N_pow_N3 :
  forall N m t,
    1 < N ->
    0 <= m ->
    m * (m - 1) = 2 * t ->
    powm (1 + N) m (N * N * N) = (1 + m * N + t * (N * N)) mod (N * N * N).
Proof.
  intros N m t HN Hm Ht.
  apply powm_one_plus_cube_nilpotent; [nia | exact Hm | | exact Ht].
  rewrite Z.mod_same by nia. reflexivity.
Qed.

Theorem one_plus_N_pow_N3_div :
  forall N m,
    1 < N ->
    0 <= m ->
    powm (1 + N) m (N * N * N) =
      (1 + m * N + (m * (m - 1) / 2) * (N * N)) mod (N * N * N).
Proof.
  intros N m HN Hm.
  destruct (two_divides_consecutive_product m) as [t Ht].
  assert (m * (m - 1) = 2 * t) as Ht' by lia.
  rewrite (one_plus_N_pow_N3 N m t HN Hm Ht').
  replace t with (m * (m - 1) / 2)
    by (symmetry; rewrite Ht', Z.mul_comm, Z.div_mul by lia; reflexivity).
  reflexivity.
Qed.

Theorem dj_add :
  forall N m1 m2 r1 r2,
    1 < N ->
    0 <= m1 ->
    0 <= m2 ->
    let N3 := N * N * N in
    ((powm (1 + N) (m1 + m2) N3 * powm (r1 * r2) N N3) mod N3) =
      ((powm (1 + N) m1 N3 * powm r1 N N3)
       * (powm (1 + N) m2 N3 * powm r2 N N3)) mod N3.
Proof.
  intros N m1 m2 r1 r2 HN H1 H2 N3.
  subst N3.
  assert (N * N * N <> 0) by nia.
  rewrite powm_add_r by lia.
  rewrite (powm_mul_base r1 r2 N (N * N * N)) by nia.
  rewrite <- Z.mul_mod by lia.
  f_equal. ring.
Qed.
