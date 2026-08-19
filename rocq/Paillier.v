From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * Paillier, as a neighbour of RSA

    Carrier [(Z/N²Z)*], not [(Z/NZ)*].  With [g = 1+N] the binomial
    [(1+N)^m ≡ 1 + m N (mod N²)] is [powm_one_plus_nilpotent].
    Encryption is additively homomorphic.  Decisional composite
    residuosity is [Refuse_PPT_advantage].

    Cross-confirmed by [cas/73_paillier.gp]. *)

Definition paillier_L (x N : Z) : Z := (x - 1) / N.

Definition paillier_enc (N m r : Z) : Z :=
  (powm (1 + N) m (N * N) * powm r N (N * N)) mod (N * N).

Lemma powm_mul_base :
  forall a b e n,
    n <> 0 ->
    0 <= e ->
    powm (a * b) e n = (powm a e n * powm b e n) mod n.
Proof.
  intros a b e n Hn He.
  unfold powm. rewrite Z.pow_mul_l. apply Z.mul_mod; lia.
Qed.

Theorem one_plus_N_pow :
  forall N m,
    1 < N ->
    0 <= m ->
    powm (1 + N) m (N * N) = (1 + m * N) mod (N * N).
Proof.
  intros N m HN Hm.
  apply powm_one_plus_nilpotent; [nia | exact Hm |].
  rewrite Z.mod_same by nia. reflexivity.
Qed.

Theorem paillier_L_of_plain :
  forall N m,
    1 < N ->
    0 <= m < N ->
    paillier_L (1 + m * N) N = m.
Proof.
  intros N m HN Hm.
  unfold paillier_L.
  rewrite Z.add_comm, Z.add_simpl_r, Z.div_mul by lia.
  reflexivity.
Qed.

Theorem paillier_L_recovers_exp :
  forall N m,
    1 < N ->
    0 <= m < N ->
    paillier_L (powm (1 + N) m (N * N)) N = m.
Proof.
  intros N m HN Hm.
  rewrite one_plus_N_pow by lia.
  rewrite Z.mod_small by nia.
  apply paillier_L_of_plain; lia.
Qed.

Theorem paillier_add :
  forall N m1 m2 r1 r2,
    1 < N ->
    0 <= m1 ->
    0 <= m2 ->
    paillier_enc N (m1 + m2) (r1 * r2) =
      (paillier_enc N m1 r1 * paillier_enc N m2 r2) mod (N * N).
Proof.
  intros N m1 m2 r1 r2 HN H1 H2.
  unfold paillier_enc.
  assert (N * N <> 0) by nia.
  rewrite powm_add_r by lia.
  rewrite (powm_mul_base r1 r2 N (N * N)) by nia.
  rewrite <- Z.mul_mod by lia.
  rewrite <- Z.mul_mod by lia.
  f_equal. ring.
Qed.

Theorem one_plus_N_order_N :
  forall N,
    1 < N ->
    powm (1 + N) N (N * N) = 1.
Proof.
  intros N HN.
  rewrite one_plus_N_pow by lia.
  replace (1 + N * N) with (1 + 1 * (N * N)) by ring.
  rewrite Z.mod_add, Z.mod_1_l by nia.
  reflexivity.
Qed.
