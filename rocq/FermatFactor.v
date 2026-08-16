From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * Fermat factoring: close primes make [N] a near-square

    For odd [p,q],
    [N = ((p+q)/2)² − ((p−q)/2)²].
    Fermat starts at [⌈√N⌉] and increments [a] until [a²−N] is square.
    The number of steps is [(p+q)/2 − ⌈√N⌉], which is small exactly
    when [|p−q|] is small.  Cross-confirmed by [cas/08_fermat.gp]. *)

Definition fermat_sum (p q : Z) : Z := (p + q) / 2.
Definition fermat_diff (p q : Z) : Z := (p - q) / 2.

Lemma odd_prime_ge_3 : forall p, Z.prime p -> p <> 2 -> 3 <= p.
Proof.
  intros p Hp Hne. pose proof (Z.prime_ge_2 p Hp). lia.
Qed.

Lemma odd_add_even :
  forall a b, Z.odd a = true -> Z.odd b = true -> Z.even (a + b) = true.
Proof.
  intros a b Ha Hb.
  apply Z.odd_spec in Ha. apply Z.odd_spec in Hb.
  destruct Ha as [ka Ha]. destruct Hb as [kb Hb]. subst.
  apply Z.even_spec. exists (ka + kb + 1). ring.
Qed.

Lemma odd_sub_even :
  forall a b, Z.odd a = true -> Z.odd b = true -> Z.even (a - b) = true.
Proof.
  intros a b Ha Hb.
  apply Z.odd_spec in Ha. apply Z.odd_spec in Hb.
  destruct Ha as [ka Ha]. destruct Hb as [kb Hb]. subst.
  apply Z.even_spec. exists (ka - kb). ring.
Qed.

Lemma prime_odd_if_ne_2 :
  forall p, Z.prime p -> p <> 2 -> Z.odd p = true.
Proof.
  intros p Hp Hne.
  pose proof (Z.prime_ge_2 p Hp).
  destruct (Z.even p) eqn:Hev.
  - apply Z.even_spec in Hev. destruct Hev as [k Hk].
    (* p = 2k, prime, p<>2 ⇒ contradiction *)
    assert (2 | p) by (exists k; lia).
    apply Z.divide_prime_prime in H0; [lia | apply prime_alt, prime_2 | exact Hp].
  - rewrite <- Z.negb_even, Hev. reflexivity.
Qed.

Theorem fermat_identity :
  forall p q,
    Z.odd p = true -> Z.odd q = true ->
    p * q =
      fermat_sum p q * fermat_sum p q -
      fermat_diff p q * fermat_diff p q.
Proof.
  intros p q Hp Hq.
  unfold fermat_sum, fermat_diff.
  pose proof (odd_add_even p q Hp Hq) as He.
  pose proof (odd_sub_even p q Hp Hq) as Hd.
  apply Z.even_spec in He. apply Z.even_spec in Hd.
  destruct He as [s Hs]. destruct Hd as [t Ht].
  rewrite Hs, Ht.
  rewrite (Z.mul_comm 2 s), (Z.mul_comm 2 t), !Z.div_mul by lia.
  assert (p = s + t) by lia. assert (q = s - t) by lia.
  subst p q. ring.
Qed.

Theorem fermat_square_gap :
  forall p q,
    Z.odd p = true -> Z.odd q = true ->
    fermat_sum p q * fermat_sum p q - p * q =
      fermat_diff p q * fermat_diff p q.
Proof.
  intros p q Hp Hq.
  pose proof (fermat_identity p q Hp Hq). lia.
Qed.

(** Starting point: [⌈√N⌉].  [Z.sqrt] is [⌊√N⌋]; if [N] is not square we
    step to [Z.sqrt N + 1]. *)
Definition ceil_sqrt (n : Z) : Z :=
  let s := Z.sqrt n in
  if s * s =? n then s else s + 1.

Lemma ceil_sqrt_ge :
  forall n, 0 <= n -> n <= ceil_sqrt n * ceil_sqrt n.
Proof.
  intros n Hn. unfold ceil_sqrt.
  pose proof (Z.sqrt_spec n Hn) as Hsp. cbn in Hsp.
  destruct (Z.eqb_spec (Z.sqrt n * Z.sqrt n) n) as [Heq | Hne].
  - lia.
  - lia.
Qed.

Lemma ceil_sqrt_le_of_square :
  forall n a, 0 <= n -> 0 <= a -> n <= a * a -> ceil_sqrt n <= a.
Proof.
  intros n a Hn Ha Haa. unfold ceil_sqrt.
  pose proof (Z.sqrt_spec n Hn) as Hsp. cbn in Hsp.
  assert (Z.sqrt n <= a).
  { apply Z.square_le_simpl_nonneg; [exact Ha|].
    pose proof (Z.sqrt_nonneg n). lia. }
  destruct (Z.eqb_spec (Z.sqrt n * Z.sqrt n) n) as [Heq | Hne]; [lia|].
  assert (Z.sqrt n <> a).
  { intro Heq. subst a. lia. }
  lia.
Qed.

Lemma fermat_sum_ge_ceil_sqrt :
  forall p q,
    0 <= q -> q <= p ->
    Z.odd p = true -> Z.odd q = true ->
    ceil_sqrt (p * q) <= fermat_sum p q.
Proof.
  intros p q Hq Hle Hp Hqodd.
  assert (0 <= p) by lia.
  apply ceil_sqrt_le_of_square; [apply Z.mul_nonneg_nonneg; lia | |].
  - unfold fermat_sum.
    pose proof (odd_add_even p q Hp Hqodd) as He.
    apply Z.even_spec in He. destruct He as [s Hs].
    rewrite Hs, (Z.mul_comm 2 s), Z.div_mul by lia. lia.
  - pose proof (fermat_square_gap p q Hp Hqodd) as Hgap.
    unfold fermat_sum in *.
    apply Z.le_0_sub. rewrite Hgap.
    set (z := fermat_diff p q). nia.
Qed.

(** One Fermat step: given [a ≥ ⌈√N⌉], test whether [a² − N] is square. *)
Definition fermat_is_square (N a : Z) : bool :=
  let d := a * a - N in
  (0 <=? d) && (Z.sqrt d * Z.sqrt d =? d).

Definition fermat_factors (N a : Z) : Z * Z :=
  let b := Z.sqrt (a * a - N) in
  (a + b, a - b).

Theorem fermat_recovers :
  forall p q,
    0 <= q -> q <= p ->
    Z.odd p = true -> Z.odd q = true ->
    let a := fermat_sum p q in
    let '(x, y) := fermat_factors (p * q) a in
    x = p /\ y = q.
Proof.
  intros p q Hq Hle Hp Hqodd.
  unfold fermat_factors.
  pose proof (fermat_square_gap p q Hp Hqodd) as Hgap.
  unfold fermat_sum, fermat_diff in *.
  pose proof (odd_add_even p q Hp Hqodd) as He.
  pose proof (odd_sub_even p q Hp Hqodd) as Hd.
  apply Z.even_spec in He. apply Z.even_spec in Hd.
  destruct He as [s Hs]. destruct Hd as [t Ht].
  rewrite Hs, Ht in *.
  rewrite (Z.mul_comm 2 s), (Z.mul_comm 2 t), !Z.div_mul in * by lia.
  assert (0 <= t) by lia.
  rewrite Hgap, Z.sqrt_square by lia.
  assert (p = s + t) by lia. assert (q = s - t) by lia.
  subst p q. split; ring.
Qed.

(** Generation-side: a lower bound on [|p−q|/2] from a bit-gap on
    [|p−q|].  Fermat's step count is this quantity *squared*, divided
    by [p+q] — large gap ⇒ exponentially many steps. *)
Lemma fermat_diff_abs :
  forall p q,
    Z.odd p = true -> Z.odd q = true ->
    Z.abs (p - q) = 2 * Z.abs (fermat_diff p q).
Proof.
  intros p q Hp Hq.
  unfold fermat_diff.
  pose proof (odd_sub_even p q Hp Hq) as Hd.
  apply Z.even_spec in Hd. destruct Hd as [t Ht].
  rewrite Ht, (Z.mul_comm 2 t), Z.div_mul by lia.
  lia.
Qed.

Theorem far_apart_large_diff :
  forall p q gap,
    0 <= gap ->
    2 ^ gap <= Z.abs (p - q) ->
    Z.odd p = true -> Z.odd q = true ->
    2 ^ gap <= 2 * Z.abs (fermat_diff p q).
Proof.
  intros p q gap Hgap Hfar Hp Hq.
  rewrite <- fermat_diff_abs by assumption. exact Hfar.
Qed.

Theorem fermat_square_gap_from_diff :
  forall p q,
    Z.odd p = true -> Z.odd q = true ->
    fermat_sum p q * fermat_sum p q - p * q =
      fermat_diff p q * fermat_diff p q.
Proof. apply fermat_square_gap. Qed.
