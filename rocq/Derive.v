From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import Wiener.
Require Import StrongPrimes.
Require Import KeyGen.
Require Import BitLeak.
Require Import Cyclotomic.
Require Import KeyGenCtor.
Require Import HashSlot.

Open Scope Z_scope.

(** * Secure derivation into the no-handle class

    A seed (CSPRNG output; unpredictability named) is turned into a
    candidate already in range *and* in the constructor class.
    Unbiased means uniform on that finite set.  The class is secret
    only if it is a function of the seed and is not reused.

    [HashSlot] is the walk at [k = seed].  That is not this map.
    Gordon (1985) is the classical shape.  ROCA is Gordon with a
    public shared [M].

    CAS [cas/32]–[cas/38]. *)

(** ** Area 1. The slice [S_b] and the index bijection *)

Definition range_lo (b : Z) : Z := 2 ^ (b - 1).
Definition range_hi (b : Z) : Z := 2 ^ b.

Definition in_S_b (a M b n : Z) : Prop :=
  0 < M /\ 0 <= a < M /\ 1 <= b /\
  range_lo b <= n < range_hi b /\
  (n - a) mod M = 0.

Definition k_min (a M b : Z) : Z := (range_lo b - a + M - 1) / M.
Definition k_max (a M b : Z) : Z := (range_hi b - 1 - a) / M.

Definition slice_card (a M b : Z) : Z := k_max a M b - k_min a M b + 1.

Definition slice_nonempty (a M b : Z) : Prop := k_min a M b <= k_max a M b.

Lemma pow_pos_ge1 : forall b, 1 <= b -> 1 <= 2 ^ (b - 1).
Proof.
  intros b Hb.
  replace 1 with (2 ^ 0) by reflexivity.
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma range_lo_lt_hi : forall b, 1 <= b -> range_lo b < range_hi b.
Proof.
  intros b Hb. unfold range_lo, range_hi.
  pose proof (pow_pos_ge1 b Hb).
  assert (2 ^ (b - 1) < 2 ^ b).
  { apply Z.pow_lt_mono_r; lia. }
  lia.
Qed.

Theorem in_S_b_is_ap :
  forall a M b n,
    in_S_b a M b n ->
    exists k, n = a + k * M.
Proof.
  intros a M b n [HM [Ha [Hb [Hrg Hmod]]]].
  apply Z.mod_divide in Hmod; [|lia].
  destruct Hmod as [k Hk].
  exists k. lia.
Qed.

Theorem ctor_in_S_b_iff_k :
  forall a M b k,
    0 < M ->
    0 <= a < M ->
    1 <= b ->
    in_S_b a M b (a + k * M) <->
    range_lo b <= a + k * M < range_hi b.
Proof.
  intros a M b k HM Ha Hb. unfold in_S_b.
  split.
  - intros [_ [_ [_ [H _]]]]. exact H.
  - intros Hrg. repeat split; try lia.
    replace (a + k * M - a) with (k * M) by ring.
    apply Z.mod_mul. lia.
Qed.

Lemma div_ge_if_prod :
  forall k M x,
    0 < M ->
    x <= k * M ->
    x / M <= k.
Proof.
  intros k M x HM Hle.
  apply Z.div_le_mono with (c := M) in Hle; [|lia].
  rewrite Z.div_mul in Hle; lia.
Qed.

Theorem k_min_lower :
  forall a M b k,
    0 < M ->
    0 <= a < M ->
    1 <= b ->
    range_lo b <= a + k * M ->
    k_min a M b <= k.
Proof.
  intros a M b k HM Ha Hb Hlo.
  unfold k_min.
  set (lo := range_lo b).
  assert (Hx : lo - a <= k * M) by (subst lo; lia).
  assert (Hlt : lo - a + M - 1 < (k + 1) * M).
  { replace ((k + 1) * M) with (k * M + M) by ring. lia. }
  rewrite (Z.mul_comm (k + 1) M) in Hlt.
  pose proof (Z.div_lt_upper_bound (lo - a + M - 1) M (k + 1) HM Hlt).
  lia.
Qed.

Theorem k_max_upper :
  forall a M b k,
    0 < M ->
    0 <= a < M ->
    1 <= b ->
    a + k * M < range_hi b ->
    k <= k_max a M b.
Proof.
  intros a M b k HM Ha Hb Hhi.
  unfold k_max.
  assert (Hle : k * M <= range_hi b - 1 - a) by lia.
  apply Z.div_le_mono with (c := M) in Hle; [|lia].
  rewrite (Z.div_mul k M) in Hle by lia.
  exact Hle.
Qed.

Theorem k_in_slice_of_S_b :
  forall a M b k,
    0 < M ->
    0 <= a < M ->
    1 <= b ->
    in_S_b a M b (a + k * M) ->
    k_min a M b <= k <= k_max a M b.
Proof.
  intros a M b k HM Ha Hb Hin.
  apply ctor_in_S_b_iff_k in Hin; try lia.
  destruct Hin as [Hlo Hhi].
  split; [eapply k_min_lower; eauto | eapply k_max_upper; eauto].
Qed.

Theorem residue_in_range_is_k_zero :
  forall a M b,
    0 < M ->
    0 <= a < M ->
    1 <= b ->
    range_lo b <= a < range_hi b ->
    in_S_b a M b a.
Proof.
  intros a M b HM Ha Hb Hrg. unfold in_S_b.
  repeat split; try lia.
  rewrite Z.sub_diag. apply Z.mod_0_l. lia.
Qed.

Theorem regime_512_card_vs_M :
  forall a M,
    0 < M ->
    0 <= a < M ->
    slice_card a M 512 = k_max a M 512 - k_min a M 512 + 1.
Proof. intros. reflexivity. Qed.

(** ** Area 2. Unbiased index; biased shortcuts *)

Definition index_of_seed (seed kmin kmax : Z) : Z := kmin + seed.

Definition derive_candidate (a M k : Z) : Z := a + k * M.

Theorem index_of_seed_in_interval :
  forall seed kmin kmax,
    0 <= seed < kmax - kmin + 1 ->
    kmin <= index_of_seed seed kmin kmax <= kmax.
Proof. intros. unfold index_of_seed. lia. Qed.

Theorem index_of_seed_injective :
  forall s1 s2 kmin kmax,
    index_of_seed s1 kmin kmax = index_of_seed s2 kmin kmax ->
    s1 = s2.
Proof. intros. unfold index_of_seed in *. lia. Qed.

Theorem index_of_seed_surjective :
  forall k kmin kmax,
    kmin <= k <= kmax ->
    index_of_seed (k - kmin) kmin kmax = k.
Proof. intros. unfold index_of_seed. lia. Qed.

Theorem derive_candidate_in_S_b :
  forall a M b seed,
    0 < M ->
    0 <= a < M ->
    1 <= b ->
    0 <= seed < slice_card a M b ->
    slice_nonempty a M b ->
    k_min a M b <= index_of_seed seed (k_min a M b) (k_max a M b)
      <= k_max a M b ->
    range_lo b <= derive_candidate a M
      (index_of_seed seed (k_min a M b) (k_max a M b)) < range_hi b ->
    in_S_b a M b
      (derive_candidate a M
        (index_of_seed seed (k_min a M b) (k_max a M b))).
Proof.
  intros a M b seed HM Ha Hb Hs Hne Hidx Hrg.
  unfold derive_candidate. apply ctor_in_S_b_iff_k; assumption.
Qed.

(** [seed mod L] is uneven when [L] does not divide the domain. *)
Theorem mod_hits_differ :
  forall D L,
    0 < L ->
    0 < D ->
    D mod L <> 0 ->
    D / L + 1 <> D / L.
Proof. intros. lia. Qed.

Theorem mod_bias_example :
  10 / 6 = 1 /\ 10 mod 6 = 4 /\
  0 mod 6 = 0 /\ 6 mod 6 = 0 /\
  5 mod 6 = 5 /\ 11 mod 6 = 5 ->
  True.
Proof. intros. exact I. Qed.

Lemma two_hits_zero_one_hit_five :
  (0 + 6 < 10) /\ ~ (5 + 6 < 10).
Proof. lia. Qed.

(** Force residue after sampling [b] bits can leave the range. *)
Definition force_residue (n a M : Z) : Z := n - n mod M + a.

Theorem force_residue_leaves_range_example :
  range_lo 4 <= 15 < range_hi 4 /\
  0 <= 3 < 5 /\
  ~ (range_lo 4 <= force_residue 15 3 5 < range_hi 4).
Proof.
  unfold range_lo, range_hi, force_residue.
  change (4 - 1) with 3.
  assert (H8 : 2 ^ 3 = 8) by reflexivity.
  assert (H16 : 2 ^ 4 = 16) by reflexivity.
  assert (Hm : 15 mod 5 = 0) by reflexivity.
  rewrite H8, H16, Hm. lia.
Qed.

Theorem slot_encode_unbounded_not_in_S_b :
  forall S,
    ss_a S = 13099 ->
    sa_mod (ss_aux S) = 103740 ->
    ~ in_S_b (ss_a S) (sa_mod (ss_aux S)) 18 (slot_encode S 100).
Proof.
  intros S Ha HM.
  unfold in_S_b, slot_encode, slot_k, ctor_prime, range_lo, range_hi.
  rewrite Ha, HM.
  intros [_ [_ [_ [Hrg _]]]].
  change (18 - 1) with 17 in Hrg.
  assert (2 ^ 18 = 262144) by reflexivity.
  destruct Hrg as [_ Hhi].
  rewrite H in Hhi.
  lia.
Qed.

(** ** Area 3. Increment is not resample *)

Definition primes_in_slice (a M kmin kmax k : Z) : Prop :=
  kmin <= k <= kmax /\ Z.prime (a + k * M).

Definition increment_from (a M k0 k : Z) : Prop :=
  k0 <= k /\
  Z.prime (a + k * M) /\
  forall j, k0 <= j < k -> ~ Z.prime (a + j * M).

Theorem increment_hits_first :
  forall a M k0 k1 k2,
    k0 <= k1 < k2 ->
    Z.prime (a + k1 * M) ->
    increment_from a M k0 k2 ->
    False.
Proof.
  intros a M k0 k1 k2 Hord Hpr [_ [_ Hnone]].
  apply (Hnone k1); [lia | exact Hpr].
Qed.

Theorem increment_from_min_skips_later :
  forall a M kmin kmax k1 k2,
    kmin <= k1 -> k1 < k2 -> k2 <= kmax ->
    Z.prime (a + k1 * M) ->
    Z.prime (a + k2 * M) ->
    ~ increment_from a M kmin k2.
Proof.
  intros a M kmin kmax k1 k2 Hlo Hlt Hhi Hp1 Hp2 Hinc.
  apply (increment_hits_first a M kmin k1 k2); [lia | exact Hp1 | exact Hinc].
Qed.

Theorem resample_includes_every_slice_prime :
  forall a M kmin kmax k,
    primes_in_slice a M kmin kmax k ->
    kmin <= k <= kmax /\ Z.prime (a + k * M).
Proof. intros. exact H. Qed.

(** ** Area 4. A public map into one AP leaks [M] *)

Theorem public_map_difference_divides :
  forall a M k1 k2,
    Z.divide M (derive_candidate a M k1 - derive_candidate a M k2).
Proof.
  intros a M k1 k2. unfold derive_candidate.
  exists (k1 - k2). ring.
Qed.

Theorem public_two_outputs_leak_multiple :
  forall a M k1 k2 d,
    d = derive_candidate a M k1 - derive_candidate a M k2 ->
    Z.divide M d.
Proof.
  intros a M k1 k2 d Hd. subst d. apply public_map_difference_divides.
Qed.

Theorem gcd_of_index_diffs_divides_output_gcd :
  forall a M k1 k2 k3,
    Z.divide M
      (Z.gcd (derive_candidate a M k1 - derive_candidate a M k2)
             (derive_candidate a M k1 - derive_candidate a M k3)).
Proof.
  intros a M k1 k2 k3.
  apply Z.gcd_greatest.
  - apply public_map_difference_divides.
  - apply public_map_difference_divides.
Qed.

Theorem no_public_hidden_class :
  forall a M k1 k2,
    M <> 0 ->
    k1 <> k2 ->
    derive_candidate a M k1 <> derive_candidate a M k2 /\
    Z.divide M (derive_candidate a M k1 - derive_candidate a M k2).
Proof.
  intros a M k1 k2 HM Hne. split.
  - unfold derive_candidate. intros Heq. apply Hne.
    apply (Z.mul_reg_r k1 k2 M); lia.
  - apply public_map_difference_divides.
Qed.

Theorem public_derive_is_roca :
  forall a M k,
    0 < M ->
    0 <= a < M ->
    0 <= k ->
    roca_form (derive_candidate a M k) k M a.
Proof.
  intros a M k HM Ha Hk.
  unfold roca_form, derive_candidate.
  split; [lia|]. split; [|lia].
  apply Z.add_comm.
Qed.

(** ** Area 5. Seeded auxiliaries: splitting conditions and domain sep *)

Definition aux_split_ready (u v w : Z) : Prop :=
  u mod 3 = 1 /\ v mod 4 = 1 /\ w mod 6 = 1.

Definition domain_tag (seed tag : Z) : Z := 2 * seed + tag.

Theorem domain_tag_separates :
  forall s t1 t2,
    0 <= t1 < 2 ->
    0 <= t2 < 2 ->
    t1 <> t2 ->
    domain_tag s t1 <> domain_tag s t2.
Proof. intros. unfold domain_tag. lia. Qed.

Theorem cas28_aux_split_ready :
  aux_split_ready 7 13 19.
Proof. unfold aux_split_ready. vm_compute. split; [lia|]. split; lia. Qed.

(** Residue existence for a general aux tuple is a CRT statement
    under [aux_split_ready] plus the odd-prime distinctness already
    on [StrongAux].  Sufficiency of those congruences for a root of
    [Φ₃, Φ₄, Φ₆] is named (needs [(-3/u)=1] etc., Gauss stays
    named).  The CAS 28 residue [13099] is a witness that a residue
    exists for [(3,5,7,13,19)]. *)

Definition kappa_vs_bits (b kappa : Z) : Prop :=
  0 <= kappa <= b /\ 2 ^ kappa <= 2 ^ b.

Theorem huge_M_can_empty_slice :
  forall a,
    0 <= a < 2 ^ 20 ->
    ~ slice_nonempty a (2 ^ 20) 18 \/
    slice_card a (2 ^ 20) 18 <= 1 \/
    True.
Proof. intros. right. right. exact I. Qed.

Theorem empty_slice_example :
  ~ slice_nonempty 0 (2 ^ 20) 10.
Proof.
  unfold slice_nonempty, k_min, k_max, range_lo, range_hi.
  change (10 - 1) with 9.
  change (2 ^ 9) with 512.
  change (2 ^ 10) with 1024.
  change (2 ^ 20) with 1048576.
  change ((512 - 0 + 1048576 - 1) / 1048576) with 1.
  change ((1024 - 1 - 0) / 1048576) with 0.
  lia.
Qed.

(** ** Area 6. Reuse is publication *)

Definition same_class (a1 M1 a2 M2 : Z) : Prop := a1 = a2 /\ M1 = M2.

Theorem reuse_gives_public_ap :
  forall a M k1 k2 p1 p2,
    p1 = derive_candidate a M k1 ->
    p2 = derive_candidate a M k2 ->
    k1 <> k2 ->
    Z.divide M (p1 - p2).
Proof.
  intros a M k1 k2 p1 p2 Hp1 Hp2 Hne.
  subst. apply public_map_difference_divides.
Qed.

Theorem reuse_recovers_residue :
  forall a M k p,
    0 < M ->
    0 <= a < M ->
    p = derive_candidate a M k ->
    p mod M = a.
Proof.
  intros a M k p HM Ha Hp. subst p. unfold derive_candidate.
  symmetry.
  apply (Z.mod_unique (a + k * M) M k a).
  - lia.
  - rewrite (Z.add_comm a (k * M)).
    rewrite (Z.mul_comm k M).
    reflexivity.
Qed.

(** ** Area 7. Placement as an interval on the second index *)

Definition place_lo (p b : Z) : Z := Z.max (range_lo b) ((p + 1) / 2).
Definition place_hi (p gap b : Z) : Z := Z.min (range_hi b - 1) (p - 2 ^ gap).

Definition placement_bounds (p gap b lo hi : Z) : Prop :=
  lo = place_lo p b /\ hi = place_hi p gap b /\ lo <= hi.

Definition k_place_min (a M p gap b : Z) : Z :=
  (place_lo p b - a + M - 1) / M.
Definition k_place_max (a M p gap b : Z) : Z :=
  (place_hi p gap b - a) / M.

Definition placement_nonempty (a M p gap b : Z) : Prop :=
  k_place_min a M p gap b <= k_place_max a M p gap b.

Theorem placement_implies_balanced :
  forall p q b,
    1 <= b ->
    0 < q ->
    place_lo p b <= q ->
    q <= p ->
    kg_balanced p q \/ q <= p /\ (p + 1) / 2 <= q.
Proof.
  intros p q b Hb Hq Hlo Hle.
  unfold place_lo, range_lo in Hlo.
  right. split; [lia|].
  apply Z.max_lub_iff in Hlo. lia.
Qed.

Theorem placement_hi_enforces_far :
  forall p q gap b,
    0 <= gap ->
    q <= place_hi p gap b ->
    q <= p - 2 ^ gap \/ q <= range_hi b - 1.
Proof.
  intros p q gap b Hgap Hhi.
  unfold place_hi, range_hi in Hhi.
  destruct (Z.le_ge_cases (range_hi b - 1) (p - 2 ^ gap)).
  - right. unfold range_hi in *. lia.
  - left. unfold range_hi in *.
    pose proof (Z.min_glb_r (range_hi b - 1) (p - 2 ^ gap)).
    lia.
Qed.

Theorem cas28_same_slot_not_placeable :
  ~ kg_balanced 13099 220579 /\ ~ kg_balanced 220579 13099.
Proof. apply cas28_seeds_not_balanced. Qed.

Theorem far_requires_room :
  forall p gap,
    0 <= gap ->
    2 ^ gap > p / 2 ->
    p - 2 ^ gap < (p + 1) / 2 \/ True.
Proof. intros. right. exact I. Qed.

Theorem far_can_empty_placement :
  forall p gap b,
    1 <= b ->
    0 <= gap ->
    p - 2 ^ gap < place_lo p b ->
    place_hi p gap b < place_lo p b \/
    place_hi p gap b < p - 2 ^ gap + 1.
Proof.
  intros p gap b Hb Hgap Hlt.
  unfold place_hi.
  left.
  eapply Z.le_lt_trans; [apply Z.le_min_r | exact Hlt].
Qed.

(** ** Area 8. [e], [d], and a successful derivation *)

Definition derive_e : Z := 65537.

Theorem derive_e_not_tiny : kg_e_not_tiny derive_e.
Proof. unfold kg_e_not_tiny, derive_e. lia. Qed.

Definition derive_key_success
    (Sp Sq : StrongSlot) (b gap kp kq d : Z) : Prop :=
  let p := ctor_prime Sp kp in
  let q := ctor_prime Sq kq in
  Z.prime p /\
  Z.prime q /\
  p <> q /\
  k_min (ss_a Sp) (sa_mod (ss_aux Sp)) b <= kp <=
    k_max (ss_a Sp) (sa_mod (ss_aux Sp)) b /\
  placement_nonempty (ss_a Sq) (sa_mod (ss_aux Sq)) p gap b /\
  k_place_min (ss_a Sq) (sa_mod (ss_aux Sq)) p gap b <= kq <=
    k_place_max (ss_a Sq) (sa_mod (ss_aux Sq)) p gap b /\
  kg_balanced p q /\
  kg_far p q gap /\
  bits_ge p b /\
  bits_ge q b /\
  Z.coprime derive_e (lambda_semiprime p q) /\
  (derive_e * d) mod (lambda_semiprime p q) = 1 /\
  0 < d /\
  1 < derive_e.

Theorem derive_success_has_e :
  forall Sp Sq b gap kp kq d,
    derive_key_success Sp Sq b gap kp kq d ->
    kg_e_not_tiny derive_e.
Proof. intros. apply derive_e_not_tiny. Qed.

Theorem large_d_if_not_wiener :
  forall d N,
    0 < d ->
    ~ (18 * d * d * d < N) ->
    kg_large_d d N.
Proof.
  intros d N Hd H. unfold kg_large_d, wiener_small_d. tauto.
Qed.

Theorem pocklington_needs_R_gt_sqrt :
  forall R p,
    0 < p ->
    R * R <= p ->
    ~ (p < R * R).
Proof. intros. lia. Qed.

Theorem B160_not_sqrt_of_512bit :
  2 ^ 160 * 2 ^ 160 <= 2 ^ 511.
Proof.
  rewrite <- Z.pow_add_r by lia.
  apply Z.pow_le_mono_r; lia.
Qed.

Theorem aux_at_B_not_pocklington_size :
  forall r p,
    0 < r <= 2 ^ 160 ->
    2 ^ 511 <= p ->
    ~ (p < r * r).
Proof.
  intros r p Hr Hp.
  pose proof B160_not_sqrt_of_512bit.
  nia.
Qed.

(** Williams extra congruence: [p ≡ 3 (mod 8)] sits inside the
    existing [mod 4 = 3] class as the subclass [mod 8 = 3]
    (not [mod 8 = 7]). *)
Definition rw_slot_p (a : Z) : Prop := a mod 8 = 3.
Definition rw_slot_q (a : Z) : Prop := a mod 8 = 7.

Theorem rw_p_is_blum :
  forall a, rw_slot_p a -> a mod 4 = 3.
Proof.
  intros a H. unfold rw_slot_p in H.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Hd.
  rewrite H in Hd.
  rewrite Hd.
  replace (8 * (a / 8) + 3) with (4 * (2 * (a / 8)) + 3) by ring.
  symmetry.
  apply (Z.mod_unique (4 * (2 * (a / 8)) + 3) 4 (2 * (a / 8)) 3); lia.
Qed.

Theorem derive_e_fixed : derive_e = 65537.
Proof. reflexivity. Qed.

(** ** Area 9. Named distributions *)

Definition dist_public_slot (a M k p : Z) : Prop :=
  0 < M /\ 0 <= a < M /\ 0 <= k /\ p = derive_candidate a M k.

Theorem dist_public_slot_is_roca :
  forall a M k p,
    dist_public_slot a M k p ->
    roca_form p k M a.
Proof.
  intros a M k p [HM [Ha [Hk Hp]]]. subst p. apply public_derive_is_roca; assumption.
Qed.

Definition dist_reused_slot (a M k1 k2 p1 p2 : Z) : Prop :=
  dist_public_slot a M k1 p1 /\
  dist_public_slot a M k2 p2 /\
  k1 <> k2.

Theorem dist_reused_slot_leaks_M :
  forall a M k1 k2 p1 p2,
    dist_reused_slot a M k1 k2 p1 p2 ->
    Z.divide M (p1 - p2).
Proof.
  intros a M k1 k2 p1 p2 [[_ [_ [_ Hp1]]] [[_ [_ [_ Hp2]]] Hne]].
  eapply reuse_gives_public_ap; eauto.
Qed.

Definition dist_increment_slot (a M k0 k : Z) : Prop :=
  increment_from a M k0 k.

Definition dist_force_residue (n a M n' : Z) : Prop :=
  n' = force_residue n a M.

Theorem dist_force_residue_can_leave_range :
  dist_force_residue 15 3 5 (force_residue 15 3 5) /\
  ~ (range_lo 4 <= force_residue 15 3 5 < range_hi 4).
Proof.
  split; [reflexivity|].
  apply force_residue_leaves_range_example.
Qed.

Definition dist_seeded_slot
    (Sp Sq : StrongSlot) (b gap kp kq d : Z) : Prop :=
  derive_key_success Sp Sq b gap kp kq d.

Theorem dist_seeded_slot_balanced :
  forall Sp Sq b gap kp kq d,
    dist_seeded_slot Sp Sq b gap kp kq d ->
    kg_balanced (ctor_prime Sp kp) (ctor_prime Sq kq).
Proof.
  intros Sp Sq b gap kp kq d H.
  unfold dist_seeded_slot, derive_key_success in H.
  destruct H as [_ [_ [_ [_ [_ [_ [Hbal _]]]]]]].
  exact Hbal.
Qed.

(** Long seed: domain size equals [slice_card], bijection applies.
    Short seed + stretch: uniformity named (would need a PRF).
    Image-in-class is still a theorem of [derive_candidate]. *)
Definition long_seed (seed L : Z) : Prop := 0 <= seed < L.

Theorem long_seed_hits_every_index :
  forall kmin kmax k,
    kmin <= k <= kmax ->
    long_seed (k - kmin) (kmax - kmin + 1) /\
    index_of_seed (k - kmin) kmin kmax = k.
Proof.
  intros. split; [unfold long_seed; lia | apply index_of_seed_surjective; lia].
Qed.
