From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.ZPoly.
Require Import RSA.
Require Import Hardness.
Require Import RabinWilliams.

Open Scope Z_scope.

(** * Sieve relations: the algebraic engine of QS and NFS

    Every successful RSA-challenge factorization from RSA-100
    (MPQS) through RSA-250 (GNFS / CADO-NFS) manufactures
    [x² ≡ y² (mod N)] with [x ≢ ±y], then [gcd(x−y, N)] splits.
    The last step is [rabin_roots_split] / [nontrivial_sqrt1_splits].
    This file is how the sieve *builds* that congruence:

    - Dixon / QS: B-smooth squares, even exponent vectors, a
      product that is a square ([cas/161]).
    - NFS setup: two integer polynomials sharing a root [m]
      modulo [N]; homogenised remainder [F − f(m) b² = G H]
      so [F ≡ G H (mod N)] ([cas/162]).
    - Two-sided combination: [G]-product and [H]-product both
      squares ⇒ [F]-product is a square modulo [N] ([cas/163]).

    Pin [N = 11·17 = 187].  Cost, smoothness probability, and
    LLL polynomial search are out of this file. *)

(** ** Even exponents make a square *)

Lemma even_nonneg_pow_square :
  forall a e,
    0 <= e ->
    Z.even e = true ->
    exists s, a ^ e = s * s.
Proof.
  intros a e He0 Hev.
  apply Z.even_spec in Hev. destruct Hev as [k Hk]. subst e.
  assert (0 <= k) by lia.
  exists (a ^ k).
  rewrite <- Z.pow_2_r, <- Z.pow_mul_r by lia.
  f_equal. lia.
Qed.

Lemma square_times_square :
  forall r s t u,
    r = t * t ->
    s = u * u ->
    r * s = (t * u) * (t * u).
Proof. intros r s t u Ht Hu. subst. ring. Qed.

Theorem even_exp_2_3_5_square :
  exists s, 2 ^ 2 * 3 ^ 2 * 5 ^ 2 = s * s.
Proof.
  destruct (even_nonneg_pow_square 2 2 ltac:(lia) eq_refl) as [a Ha].
  destruct (even_nonneg_pow_square 3 2 ltac:(lia) eq_refl) as [b Hb].
  destruct (even_nonneg_pow_square 5 2 ltac:(lia) eq_refl) as [c Hc].
  exists (a * b * c).
  rewrite Ha, Hb, Hc. ring.
Qed.

Lemma mul_mod_cong :
  forall N x y x' y',
    N <> 0 ->
    x mod N = x' mod N ->
    y mod N = y' mod N ->
    (x * y) mod N = (x' * y') mod N.
Proof.
  intros N x y x' y' HN Hx Hy.
  rewrite Z.mul_mod by exact HN.
  rewrite Hx, Hy.
  rewrite <- Z.mul_mod by exact HN.
  reflexivity.
Qed.

(** Two modular squares whose residues multiply to a square
    combine to a congruence of squares. *)
Theorem dixon_two_relations :
  forall N a b r s t,
    0 < N ->
    (a * a) mod N = r mod N ->
    (b * b) mod N = s mod N ->
    r * s = t * t ->
    ((a * b) * (a * b)) mod N = (t * t) mod N.
Proof.
  intros N a b r s t HN Ha Hb Hrs.
  replace ((a * b) * (a * b)) with ((a * a) * (b * b)) by ring.
  pose proof (mul_mod_cong N (a * a) (b * b) r s ltac:(lia) Ha Hb) as Hmul.
  rewrite Hmul, Hrs. reflexivity.
Qed.

Theorem dixon_combination_splits :
  forall p q a b r s t,
    Z.prime p -> Z.prime q -> p <> q ->
    (a * a) mod (p * q) = r mod (p * q) ->
    (b * b) mod (p * q) = s mod (p * q) ->
    r * s = t * t ->
    ~ (p * q | a * b - t) ->
    ~ (p * q | a * b + t) ->
    let g := Z.gcd (a * b - t) (p * q) in
    1 < g /\ g < p * q /\ (g | p * q).
Proof.
  intros p q a b r s t Hp Hq Hneq Ha Hb Hrs Hny Hnm g.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  apply (rabin_roots_split p q (a * b) t Hp Hq Hneq); try assumption.
  apply (dixon_two_relations (p * q) a b r s t);
    [nia | exact Ha | exact Hb | exact Hrs].
Qed.

(** Pin: [24² ≡ 15], [37² ≡ 60], same odd primes, product [30²]. *)
Theorem dixon_residues_even_exponents :
  15 = 3 ^ 1 * 5 ^ 1 /\
  60 = 2 ^ 2 * 3 ^ 1 * 5 ^ 1 /\
  15 * 60 = 2 ^ 2 * 3 ^ 2 * 5 ^ 2 /\
  2 ^ 2 * 3 ^ 2 * 5 ^ 2 = 30 * 30.
Proof. repeat split; reflexivity. Qed.

Theorem dixon_24_37_cong :
  (24 * 24) mod 187 = 15 mod 187 /\
  (37 * 37) mod 187 = 60 mod 187 /\
  15 * 60 = 30 * 30 /\
  ((24 * 37) * (24 * 37)) mod 187 = (30 * 30) mod 187.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [reflexivity|].
  apply (dixon_two_relations 187 24 37 15 60 30);
    [lia | vm_compute; reflexivity
     | vm_compute; reflexivity | reflexivity].
Qed.

Lemma dixon_24_37_not_assoc :
  ~ (187 | 24 * 37 - 30) /\ ~ (187 | 24 * 37 + 30).
Proof.
  split; intros Hdiv;
    rewrite <- Z.mod_divide in Hdiv by lia;
    vm_compute in Hdiv; discriminate.
Qed.

Theorem dixon_24_37_splits :
  let g := Z.gcd (24 * 37 - 30) 187 in
  1 < g /\ g < 187 /\ (g | 187) /\ Problem_Factor 187 g.
Proof.
  pose proof dixon_24_37_not_assoc as [Hny Hnm].
  pose proof (dixon_combination_splits 11 17 24 37 15 60 30
                prime_11 prime_17 ltac:(discriminate)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) Hny Hnm) as Hg.
  destruct Hg as [Hg1 [Hg2 HgN]].
  unfold Problem_Factor.
  repeat split; try assumption; lia.
Qed.

Theorem dixon_24_37_gcd :
  Z.gcd (24 * 37 - 30) 187 = 11.
Proof. vm_compute. reflexivity. Qed.

(** Length-1 even vector: the residue is already a square. *)
Theorem dixon_14_already_square :
  (14 * 14) mod 187 = (3 * 3) mod 187 /\
  Z.gcd (14 - 3) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia | exists 17; reflexivity].
Qed.

(** ** NFS setup: common root and homogenised remainder *)

Definition nfs_F (c0 c1 c2 a b : Z) : Z :=
  c2 * a * a + c1 * a * b + c0 * b * b.
Definition nfs_G (m a b : Z) : Z := a - m * b.
Definition nfs_H (c1 c2 m a b : Z) : Z :=
  c2 * a + (c2 * m + c1) * b.

(** For a quadratic [c₂ x² + c₁ x + c₀], the remainder identity
    [F(a,b) − f(m) b² = (a − m b) H(a,b)] is a ring calculation. *)
Theorem hom_quad_remainder :
  forall c0 c1 c2 m a b,
    nfs_F c0 c1 c2 a b
      - (c2 * m * m + c1 * m + c0) * b * b
    = nfs_G m a b * nfs_H c1 c2 m a b.
Proof. intros. unfold nfs_F, nfs_G, nfs_H. ring. Qed.

Theorem hom_quad_cong :
  forall N c0 c1 c2 m a b,
    0 < N ->
    (N | c2 * m * m + c1 * m + c0) ->
    nfs_F c0 c1 c2 a b mod N
    = (nfs_G m a b * nfs_H c1 c2 m a b) mod N.
Proof.
  intros N c0 c1 c2 m a b HN Hdiv.
  apply mods_eq_iff_divides; [lia|].
  pose proof (hom_quad_remainder c0 c1 c2 m a b) as Hrem.
  assert (nfs_F c0 c1 c2 a b - nfs_G m a b * nfs_H c1 c2 m a b
          = (c2 * m * m + c1 * m + c0) * (b * b)) as Hdiff.
  { rewrite <- Hrem. ring. }
  rewrite Hdiff.
  destruct Hdiv as [k Hk]. rewrite Hk.
  exists (k * (b * b)). ring.
Qed.

Definition nfs_f_irr : list Z := [5; 1; 1].
Definition nfs_f_red : list Z := [7; 8; 1].

Theorem nfs_eval_irr :
  poly_eval nfs_f_irr 13 = 187.
Proof. vm_compute. reflexivity. Qed.

Theorem nfs_eval_red :
  poly_eval nfs_f_red 10 = 187.
Proof. vm_compute. reflexivity. Qed.

(** Resultant of [f] and [x−m] is [±f(m)].  Here [f(m)=N]. *)
Theorem nfs_common_root_irr :
  (187 | poly_eval nfs_f_irr 13).
Proof. rewrite nfs_eval_irr. exists 1. reflexivity. Qed.

Theorem nfs_common_root_red :
  (187 | poly_eval nfs_f_red 10).
Proof. rewrite nfs_eval_red. exists 1. reflexivity. Qed.

Theorem nfs_f_irr_disc_neg :
  1 - 4 * 5 = -19.
Proof. reflexivity. Qed.

Theorem nfs_neg19_not_square :
  forall s, s * s <> -19.
Proof.
  intros s Hs.
  destruct (Z.le_ge_cases 0 s) as [Hs0 | Hs0]; nia.
Qed.

Theorem nfs_f_red_splits_Z :
  poly_eval nfs_f_red (-1) = 0 /\ poly_eval nfs_f_red (-7) = 0.
Proof. vm_compute. split; reflexivity. Qed.

Theorem nfs_hom_irr_pin :
  nfs_F 5 1 1 2 1 - 187 * 1 * 1
  = nfs_G 13 2 1 * nfs_H 1 1 13 2 1.
Proof. vm_compute. reflexivity. Qed.

Theorem nfs_hom_red_pin :
  nfs_F 7 8 1 (-15) 1 - 187 * 1 * 1
  = nfs_G 10 (-15) 1 * nfs_H 8 1 10 (-15) 1.
Proof. vm_compute. reflexivity. Qed.

Theorem nfs_F_cong_GH_irr :
  nfs_F 5 1 1 3 2 mod 187
  = (nfs_G 13 3 2 * nfs_H 1 1 13 3 2) mod 187.
Proof.
  apply hom_quad_cong; [lia|].
  exists 1. vm_compute. reflexivity.
Qed.

Theorem nfs_F_cong_GH_red :
  nfs_F 7 8 1 1 1 mod 187
  = (nfs_G 10 1 1 * nfs_H 8 1 10 1 1) mod 187.
Proof.
  apply hom_quad_cong; [lia|].
  exists 1. vm_compute. reflexivity.
Qed.

(** ** Two-sided combination *)

Theorem nfs_two_sided_product :
  forall N F1 F2 G1 G2 H1 H2 T U,
    0 < N ->
    F1 mod N = (G1 * H1) mod N ->
    F2 mod N = (G2 * H2) mod N ->
    G1 * G2 = T * T ->
    H1 * H2 = U * U ->
    (F1 * F2) mod N = ((T * U) * (T * U)) mod N.
Proof.
  intros N F1 F2 G1 G2 H1 H2 T U HN HF1 HF2 HG HH.
  pose proof (mul_mod_cong N F1 F2 (G1 * H1) (G2 * H2)
                ltac:(lia) HF1 HF2) as Hmul.
  rewrite Hmul.
  replace ((G1 * H1) * (G2 * H2)) with ((G1 * G2) * (H1 * H2)) by ring.
  rewrite HG, HH.
  replace ((T * T) * (U * U)) with ((T * U) * (T * U)) by ring.
  reflexivity.
Qed.

Lemma nfs_rel_minus15 :
  nfs_G 10 (-15) 1 = -25 /\
  nfs_H 8 1 10 (-15) 1 = 3 /\
  nfs_F 7 8 1 (-15) 1 = 112.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma nfs_rel_minus6 :
  nfs_G 10 (-6) 1 = -16 /\
  nfs_H 8 1 10 (-6) 1 = 12 /\
  nfs_F 7 8 1 (-6) 1 = -5.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem nfs_two_sided_pin_squares :
  nfs_G 10 (-15) 1 * nfs_G 10 (-6) 1 = 20 * 20 /\
  nfs_H 8 1 10 (-15) 1 * nfs_H 8 1 10 (-6) 1 = 6 * 6 /\
  (nfs_F 7 8 1 (-15) 1 * nfs_F 7 8 1 (-6) 1) mod 187
    = ((20 * 6) * (20 * 6)) mod 187.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  apply (nfs_two_sided_product 187
           (nfs_F 7 8 1 (-15) 1) (nfs_F 7 8 1 (-6) 1)
           (nfs_G 10 (-15) 1) (nfs_G 10 (-6) 1)
           (nfs_H 8 1 10 (-15) 1) (nfs_H 8 1 10 (-6) 1)
           20 6);
    [lia
    | apply hom_quad_cong; [lia | exists 1; vm_compute; reflexivity]
    | apply hom_quad_cong; [lia | exists 1; vm_compute; reflexivity]
    | vm_compute; reflexivity
    | vm_compute; reflexivity].
Qed.

Theorem nfs_two_sided_120_is_sqrt1 :
  powm 120 2 187 = 1 /\
  120 mod 187 <> 1 /\
  120 mod 187 <> 186.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; discriminate|].
  vm_compute. discriminate.
Qed.

Theorem nfs_two_sided_splits :
  let g := Z.gcd (120 - 1) 187 in
  1 < g /\ g < 187 /\ (g | 187) /\ Problem_Factor 187 g.
Proof.
  pose proof nfs_two_sided_120_is_sqrt1 as [Hsq [Hn1 Hnm1]].
  pose proof (nontrivial_sqrt1_splits 11 17 120
                prime_11 prime_17 ltac:(discriminate)
                Hsq Hn1 Hnm1) as Hg.
  destruct Hg as [Hg1 [Hg2 HgN]].
  unfold Problem_Factor.
  repeat split; try assumption; lia.
Qed.

Theorem nfs_two_sided_gcd :
  Z.gcd (120 - 1) 187 = 17 /\ Z.gcd (120 + 1) 187 = 11.
Proof. vm_compute. split; reflexivity. Qed.

(** One pair with [G] and [F] already squares, [H] not: leftover
    does not split. *)
Theorem nfs_onesided_no_split :
  nfs_G 10 1 1 = -9 /\
  nfs_F 7 8 1 1 1 = 16 /\
  nfs_H 8 1 10 1 1 = 19 /\
  Z.gcd (4 - 3) 187 = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.
