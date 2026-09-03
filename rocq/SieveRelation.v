From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.ZPoly.
Require Import Pin.
Require Import RSA.
Require Import Hardness.
Require Import RabinWilliams.

Open Scope Z_scope.

(** * Sieve relations: the algebraic engine of QS and NFS

    Every successful RSA-challenge factorization from RSA-100
    (MPQS) through RSA-250 (GNFS / CADO-NFS) manufactures
    [x² ≡ y² (mod N)] with [x ≢ ±y], then [gcd(x−y, N)] splits.
    The last step is [rabin_roots_split] / [nontrivial_sqrt1_splits].
    This file is how the sieve *builds* that congruence.

    Numbers come from [Pin.v]: [pin_N], Dixon bases, NFS
    coefficients.  Cost, smoothness probability, and LLL search
    are out of this file.  CAS [161]–[163] load [cas/lib/pin.gp]. *)

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

Lemma not_div_mod :
  forall n a, 0 < n -> a mod n <> 0 -> ~ (n | a).
Proof.
  intros n a Hn Ha Hdiv.
  rewrite <- Z.mod_divide in Hdiv by lia.
  contradiction.
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

(** Pin instance: names from [Pin.v]. *)
Theorem dixon_pin_residue_factors :
  pin_dixon_r * pin_dixon_s = pin_dixon_t * pin_dixon_t.
Proof. vm_compute. reflexivity. Qed.

Theorem dixon_pin_cong :
  (pin_dixon_a * pin_dixon_a) mod pin_N = pin_dixon_r mod pin_N /\
  (pin_dixon_b * pin_dixon_b) mod pin_N = pin_dixon_s mod pin_N /\
  pin_dixon_r * pin_dixon_s = pin_dixon_t * pin_dixon_t /\
  ((pin_dixon_a * pin_dixon_b) * (pin_dixon_a * pin_dixon_b)) mod pin_N
    = (pin_dixon_t * pin_dixon_t) mod pin_N.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  apply (dixon_two_relations pin_N pin_dixon_a pin_dixon_b
           pin_dixon_r pin_dixon_s pin_dixon_t);
    [apply pin_N_pos | vm_compute; reflexivity
     | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma dixon_pin_not_assoc :
  ~ (pin_N | pin_dixon_a * pin_dixon_b - pin_dixon_t) /\
  ~ (pin_N | pin_dixon_a * pin_dixon_b + pin_dixon_t).
Proof.
  split; apply not_div_mod;
    [apply pin_N_pos | vm_compute; discriminate
    | apply pin_N_pos | vm_compute; discriminate].
Qed.

Theorem dixon_pin_splits :
  let g := Z.gcd (pin_dixon_a * pin_dixon_b - pin_dixon_t) pin_N in
  1 < g /\ g < pin_N /\ (g | pin_N) /\ Problem_Factor pin_N g.
Proof.
  pose proof dixon_pin_not_assoc as [Hny Hnm].
  pose proof (dixon_combination_splits pin_p pin_q
                pin_dixon_a pin_dixon_b pin_dixon_r pin_dixon_s pin_dixon_t
                pin_p_prime pin_q_prime pin_p_neq_q
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) Hny Hnm) as Hg.
  destruct Hg as [Hg1 [Hg2 HgN]].
  unfold Problem_Factor.
  repeat split; try assumption; try (lia).
Qed.

Theorem dixon_pin_gcd :
  let g := Z.gcd (pin_dixon_a * pin_dixon_b - pin_dixon_t) pin_N in
  g = pin_p \/ g = pin_q.
Proof. vm_compute. first [left; reflexivity | right; reflexivity]. Qed.

Theorem dixon_pin_b_splits :
  let g := Z.gcd (pin_dixon_a * pin_dixon_b2 - pin_dixon_t2) pin_N in
  1 < g /\ g < pin_N /\ (g | pin_N) /\ Problem_Factor pin_N g.
Proof.
  assert (~ (pin_N | pin_dixon_a * pin_dixon_b2 - pin_dixon_t2)) as Hny
    by (apply not_div_mod; [apply pin_N_pos | vm_compute; discriminate]).
  assert (~ (pin_N | pin_dixon_a * pin_dixon_b2 + pin_dixon_t2)) as Hnm
    by (apply not_div_mod; [apply pin_N_pos | vm_compute; discriminate]).
  pose proof (dixon_combination_splits pin_p pin_q
                pin_dixon_a pin_dixon_b2 pin_dixon_r pin_dixon_s2 pin_dixon_t2
                pin_p_prime pin_q_prime pin_p_neq_q
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) Hny Hnm) as Hg.
  destruct Hg as [Hg1 [Hg2 HgN]].
  unfold Problem_Factor.
  repeat split; try assumption; try (lia).
Qed.

Theorem asquare_pin_splits :
  (pin_asquare_a * pin_asquare_a) mod pin_N
    = (pin_asquare_t * pin_asquare_t) mod pin_N /\
  Z.gcd (pin_asquare_a - pin_asquare_t) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia | exists pin_q; reflexivity].
Qed.

(** ** NFS setup: common root and homogenised remainder *)

Definition nfs_F (c0 c1 c2 a b : Z) : Z :=
  c2 * a * a + c1 * a * b + c0 * b * b.
Definition nfs_G (m a b : Z) : Z := a - m * b.
Definition nfs_H (c1 c2 m a b : Z) : Z :=
  c2 * a + (c2 * m + c1) * b.

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

Definition nfs_poly_irr : list Z :=
  [pin_nfs_irr_c0; pin_nfs_irr_c1; pin_nfs_irr_c2].
Definition nfs_poly_red : list Z :=
  [pin_nfs_red_c0; pin_nfs_red_c1; pin_nfs_red_c2].

Lemma poly_eval_quad :
  forall c0 c1 c2 m,
    poly_eval [c0; c1; c2] m = c2 * m * m + c1 * m + c0.
Proof. intros. unfold poly_eval. ring. Qed.

Theorem nfs_eval_irr :
  poly_eval nfs_poly_irr pin_nfs_irr_m = pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem nfs_eval_red :
  poly_eval nfs_poly_red pin_nfs_red_m = pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem nfs_common_root_irr :
  (pin_N | poly_eval nfs_poly_irr pin_nfs_irr_m).
Proof. rewrite nfs_eval_irr. exists 1. ring. Qed.

Theorem nfs_common_root_red :
  (pin_N | poly_eval nfs_poly_red pin_nfs_red_m).
Proof. rewrite nfs_eval_red. exists 1. ring. Qed.

Theorem nfs_irr_disc_neg :
  pin_nfs_irr_c1 * pin_nfs_irr_c1
    - 4 * pin_nfs_irr_c2 * pin_nfs_irr_c0 < 0.
Proof.
  unfold pin_nfs_irr_c0, pin_nfs_irr_c1, pin_nfs_irr_c2.
  vm_compute. reflexivity.
Qed.

Theorem nfs_neg_not_square :
  forall d s, d < 0 -> s * s <> d.
Proof.
  intros d s Hd Hs.
  destruct (Z.le_ge_cases 0 s) as [Hs0 | Hs0]; nia.
Qed.

Theorem nfs_red_splits_Z :
  poly_eval nfs_poly_red 1 = 0 /\
  poly_eval nfs_poly_red pin_nfs_red_c0 = 0.
Proof. vm_compute. split; reflexivity. Qed.

Theorem nfs_F_cong_GH_irr :
  nfs_F pin_nfs_irr_c0 pin_nfs_irr_c1 pin_nfs_irr_c2 3 2 mod pin_N
  = (nfs_G pin_nfs_irr_m 3 2
     * nfs_H pin_nfs_irr_c1 pin_nfs_irr_c2 pin_nfs_irr_m 3 2) mod pin_N.
Proof.
  apply hom_quad_cong; [apply pin_N_pos|].
  rewrite <- nfs_eval_irr. unfold nfs_poly_irr. rewrite poly_eval_quad.
  exists 1. ring.
Qed.

Theorem nfs_F_cong_GH_red :
  nfs_F pin_nfs_red_c0 pin_nfs_red_c1 pin_nfs_red_c2 1 1 mod pin_N
  = (nfs_G pin_nfs_red_m 1 1
     * nfs_H pin_nfs_red_c1 pin_nfs_red_c2 pin_nfs_red_m 1 1) mod pin_N.
Proof.
  apply hom_quad_cong; [apply pin_N_pos|].
  rewrite <- nfs_eval_red. unfold nfs_poly_red. rewrite poly_eval_quad.
  exists 1. ring.
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

Theorem nfs_two_sided_pin_squares :
  nfs_G pin_nfs_red_m pin_ts_a1 pin_ts_b1
    * nfs_G pin_nfs_red_m pin_ts_a2 pin_ts_b2
    = pin_ts_T * pin_ts_T /\
  nfs_H pin_nfs_red_c1 pin_nfs_red_c2 pin_nfs_red_m pin_ts_a1 pin_ts_b1
    * nfs_H pin_nfs_red_c1 pin_nfs_red_c2 pin_nfs_red_m pin_ts_a2 pin_ts_b2
    = pin_ts_U * pin_ts_U /\
  (nfs_F pin_nfs_red_c0 pin_nfs_red_c1 pin_nfs_red_c2 pin_ts_a1 pin_ts_b1
     * nfs_F pin_nfs_red_c0 pin_nfs_red_c1 pin_nfs_red_c2 pin_ts_a2 pin_ts_b2)
    mod pin_N
    = ((pin_ts_T * pin_ts_U) * (pin_ts_T * pin_ts_U)) mod pin_N.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  apply (nfs_two_sided_product pin_N
           (nfs_F pin_nfs_red_c0 pin_nfs_red_c1 pin_nfs_red_c2 pin_ts_a1 pin_ts_b1)
           (nfs_F pin_nfs_red_c0 pin_nfs_red_c1 pin_nfs_red_c2 pin_ts_a2 pin_ts_b2)
           (nfs_G pin_nfs_red_m pin_ts_a1 pin_ts_b1)
           (nfs_G pin_nfs_red_m pin_ts_a2 pin_ts_b2)
           (nfs_H pin_nfs_red_c1 pin_nfs_red_c2 pin_nfs_red_m pin_ts_a1 pin_ts_b1)
           (nfs_H pin_nfs_red_c1 pin_nfs_red_c2 pin_nfs_red_m pin_ts_a2 pin_ts_b2)
           pin_ts_T pin_ts_U);
    [apply pin_N_pos
    | apply hom_quad_cong; [apply pin_N_pos |
        rewrite <- nfs_eval_red; unfold nfs_poly_red; rewrite poly_eval_quad;
        exists 1; ring]
    | apply hom_quad_cong; [apply pin_N_pos |
        rewrite <- nfs_eval_red; unfold nfs_poly_red; rewrite poly_eval_quad;
        exists 1; ring]
    | vm_compute; reflexivity
    | vm_compute; reflexivity].
Qed.

Theorem nfs_two_sided_pin_sqrt1 :
  powm pin_sqrt1_mixed 2 pin_N = 1 /\
  pin_sqrt1_mixed mod pin_N <> 1 /\
  pin_sqrt1_mixed mod pin_N <> pin_N - 1.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; discriminate|].
  vm_compute. discriminate.
Qed.

Theorem nfs_two_sided_splits :
  let g := Z.gcd (pin_sqrt1_mixed - 1) pin_N in
  1 < g /\ g < pin_N /\ (g | pin_N) /\ Problem_Factor pin_N g.
Proof.
  pose proof nfs_two_sided_pin_sqrt1 as [Hsq [Hn1 Hnm1]].
  pose proof (nontrivial_sqrt1_splits pin_p pin_q pin_sqrt1_mixed
                pin_p_prime pin_q_prime pin_p_neq_q
                Hsq Hn1 Hnm1) as Hg.
  destruct Hg as [Hg1 [Hg2 HgN]].
  unfold Problem_Factor.
  repeat split; try assumption; try (lia).
Qed.

Theorem nfs_two_sided_gcd :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Z.gcd (pin_sqrt1_mixed + 1) pin_N = pin_q.
Proof. vm_compute. split; reflexivity. Qed.

Theorem nfs_onesided_no_split :
  nfs_G pin_nfs_red_m 1 0 = 1 /\
  Z.gcd 1 pin_N = 1.
Proof. vm_compute. split; reflexivity. Qed.
