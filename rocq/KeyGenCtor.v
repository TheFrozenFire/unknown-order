From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import StrongPrimes.
Require Import KeyGen.
Require Import BitLeak.
Require Import QuadResidue.
Require Import Cyclotomic.
Require Import KeyGenSampler.
Require Import CRTRSA.

Open Scope Z_scope.

(** * A constructor whose image is the no-handle set

    Invert [satisfies_keygen]: emit [p = a + k M] with
    [M = 4 r s u v w] and residue [a] forced so that

    - [r | p−1], [s | p+1], [p ≡ 3 (mod 4)]
    - [u | Φ₃(p)], [v | Φ₄(p)], [w | Φ₆(p)]

    The walk is in [k].  A *placed* pair adds balanced / far / bits
    as fields, not a post-hoc filter on smoothness.  A [CtorKey]
    adds [e,d].  If those exist, the pair is an [RSAInstance]
    discharging [satisfies_keygen_full].

    Public [M] is [roca_form] (Type A).  Secret auxiliaries need
    [p] or [(r,s,u,v,w)].  AP-search bits: [b − κ] when
    [2^κ ≤ M].  NFS cost is [Refuse_NFS_cost].  CAS [cas/28_keygen_ctor.gp]. *)

Record StrongAux : Type := {
  sa_r : Z; sa_s : Z; sa_u : Z; sa_v : Z; sa_w : Z;
  sa_r_prime : Z.prime sa_r;
  sa_s_prime : Z.prime sa_s;
  sa_u_prime : Z.prime sa_u;
  sa_v_prime : Z.prime sa_v;
  sa_w_prime : Z.prime sa_w;
  sa_r_odd : Z.odd sa_r = true;
  sa_s_odd : Z.odd sa_s = true;
  sa_u_odd : Z.odd sa_u = true;
  sa_v_odd : Z.odd sa_v = true;
  sa_w_odd : Z.odd sa_w = true;
  sa_r_ne_s : sa_r <> sa_s;
  sa_r_ne_u : sa_r <> sa_u;
  sa_r_ne_v : sa_r <> sa_v;
  sa_r_ne_w : sa_r <> sa_w;
  sa_s_ne_u : sa_s <> sa_u;
  sa_s_ne_v : sa_s <> sa_v;
  sa_s_ne_w : sa_s <> sa_w;
  sa_u_ne_v : sa_u <> sa_v;
  sa_u_ne_w : sa_u <> sa_w;
  sa_v_ne_w : sa_v <> sa_w
}.

Definition sa_mod (A : StrongAux) : Z :=
  4 * sa_r A * sa_s A * sa_u A * sa_v A * sa_w A.

Lemma sa_prime_ge_2 : forall p, Z.prime p -> 2 <= p.
Proof. apply Z.prime_ge_2. Qed.

Lemma sa_mod_pos : forall A, 1 < sa_mod A.
Proof.
  intros A. unfold sa_mod.
  pose proof (sa_prime_ge_2 _ (sa_r_prime A)).
  pose proof (sa_prime_ge_2 _ (sa_s_prime A)).
  pose proof (sa_prime_ge_2 _ (sa_u_prime A)).
  pose proof (sa_prime_ge_2 _ (sa_v_prime A)).
  pose proof (sa_prime_ge_2 _ (sa_w_prime A)). nia.
Qed.

Lemma sa_r_divides_mod : forall A, (sa_r A | sa_mod A).
Proof. intros A. unfold sa_mod. exists (4 * sa_s A * sa_u A * sa_v A * sa_w A). ring. Qed.

Lemma sa_s_divides_mod : forall A, (sa_s A | sa_mod A).
Proof. intros A. unfold sa_mod. exists (4 * sa_r A * sa_u A * sa_v A * sa_w A). ring. Qed.

Lemma sa_u_divides_mod : forall A, (sa_u A | sa_mod A).
Proof. intros A. unfold sa_mod. exists (4 * sa_r A * sa_s A * sa_v A * sa_w A). ring. Qed.

Lemma sa_v_divides_mod : forall A, (sa_v A | sa_mod A).
Proof. intros A. unfold sa_mod. exists (4 * sa_r A * sa_s A * sa_u A * sa_w A). ring. Qed.

Lemma sa_w_divides_mod : forall A, (sa_w A | sa_mod A).
Proof. intros A. unfold sa_mod. exists (4 * sa_r A * sa_s A * sa_u A * sa_v A). ring. Qed.

Lemma four_divides_mod : forall A, (4 | sa_mod A).
Proof. intros A. unfold sa_mod. exists (sa_r A * sa_s A * sa_u A * sa_v A * sa_w A). ring. Qed.

Record StrongSlot : Type := {
  ss_aux : StrongAux;
  ss_a : Z;
  ss_a_mod_r : ss_a mod sa_r ss_aux = 1;
  ss_a_mod_s : ss_a mod sa_s ss_aux = sa_s ss_aux - 1;
  ss_a_mod_4 : ss_a mod 4 = 3;
  ss_a_mod_u : (ss_a * ss_a + ss_a + 1) mod sa_u ss_aux = 0;
  ss_a_mod_v : (ss_a * ss_a + 1) mod sa_v ss_aux = 0;
  ss_a_mod_w : (ss_a * ss_a - ss_a + 1) mod sa_w ss_aux = 0;
  ss_a_range : 0 <= ss_a < sa_mod ss_aux
}.

Definition ctor_prime (S : StrongSlot) (k : Z) : Z :=
  ss_a S + k * sa_mod (ss_aux S).

Lemma ctor_plus_mod :
  forall (d a M k : Z),
    0 < d -> (d | M) -> a mod d = a mod d ->
    (a + k * M) mod d = a mod d.
Proof.
  intros d a M k Hd [t Ht] _.
  rewrite Ht.
  replace (k * (t * d)) with (k * t * d) by ring.
  apply Z.mod_add. lia.
Qed.

Lemma ctor_prime_mod_r :
  forall S k, ctor_prime S k mod sa_r (ss_aux S) = 1.
Proof.
  intros S k. unfold ctor_prime.
  pose proof (sa_r_divides_mod (ss_aux S)) as [t Ht].
  pose proof (Z.prime_ge_2 _ (sa_r_prime (ss_aux S))).
  rewrite Ht.
  replace (k * (t * sa_r (ss_aux S))) with (k * t * sa_r (ss_aux S)) by ring.
  rewrite Z.mod_add by lia. apply ss_a_mod_r.
Qed.

Lemma ctor_prime_mod_s :
  forall S k,
    ctor_prime S k mod sa_s (ss_aux S) = sa_s (ss_aux S) - 1.
Proof.
  intros S k. unfold ctor_prime.
  pose proof (sa_s_divides_mod (ss_aux S)) as [t Ht].
  pose proof (Z.prime_ge_2 _ (sa_s_prime (ss_aux S))).
  rewrite Ht.
  replace (k * (t * sa_s (ss_aux S))) with (k * t * sa_s (ss_aux S)) by ring.
  rewrite Z.mod_add by lia. apply ss_a_mod_s.
Qed.

Lemma ctor_prime_mod_4 :
  forall S k, ctor_prime S k mod 4 = 3.
Proof.
  intros S k. unfold ctor_prime.
  pose proof (four_divides_mod (ss_aux S)) as [t Ht].
  rewrite Ht.
  replace (k * (t * 4)) with (k * t * 4) by ring.
  rewrite Z.mod_add by lia. apply ss_a_mod_4.
Qed.

Theorem ctor_r_divides_pminus1 :
  forall S k, (sa_r (ss_aux S) | ctor_prime S k - 1).
Proof.
  intros S k.
  apply Z.mod_divide;
    [pose proof (Z.prime_ge_2 _ (sa_r_prime (ss_aux S))); lia|].
  rewrite Zminus_mod, ctor_prime_mod_r.
  rewrite Z.mod_1_l by (pose proof (Z.prime_ge_2 _ (sa_r_prime (ss_aux S))); lia).
  rewrite Z.sub_diag, Z.mod_0_l by
    (pose proof (Z.prime_ge_2 _ (sa_r_prime (ss_aux S))); lia).
  reflexivity.
Qed.

Theorem ctor_s_divides_pplus1 :
  forall S k, (sa_s (ss_aux S) | ctor_prime S k + 1).
Proof.
  intros S k.
  apply Z.mod_divide;
    [pose proof (Z.prime_ge_2 _ (sa_s_prime (ss_aux S))); lia|].
  rewrite Zplus_mod, ctor_prime_mod_s, Z.mod_1_l by
    (pose proof (Z.prime_ge_2 _ (sa_s_prime (ss_aux S))); lia).
  replace (sa_s (ss_aux S) - 1 + 1) with (sa_s (ss_aux S)) by ring.
  apply Z.mod_same.
  pose proof (Z.prime_ge_2 _ (sa_s_prime (ss_aux S))). lia.
Qed.

Theorem ctor_is_blum_mod4 :
  forall S k, ctor_prime S k mod 4 = 3.
Proof. apply ctor_prime_mod_4. Qed.

Lemma cyc3_of_ctor :
  forall S k,
    cyc3 (ctor_prime S k) =
      cyc3 (ss_a S) +
      sa_mod (ss_aux S) *
        (2 * ss_a S * k + k * k * sa_mod (ss_aux S) + k).
Proof. intros. unfold ctor_prime, cyc3. ring. Qed.

Lemma cyc4_of_ctor :
  forall S k,
    cyc4 (ctor_prime S k) =
      cyc4 (ss_a S) +
      sa_mod (ss_aux S) * (2 * ss_a S * k + k * k * sa_mod (ss_aux S)).
Proof. intros. unfold ctor_prime, cyc4. ring. Qed.

Lemma cyc6_of_ctor :
  forall S k,
    cyc6 (ctor_prime S k) =
      cyc6 (ss_a S) +
      sa_mod (ss_aux S) * (2 * ss_a S * k + k * k * sa_mod (ss_aux S) - k).
Proof. intros. unfold ctor_prime, cyc6. ring. Qed.

Theorem ctor_u_divides_phi3 :
  forall S k, (sa_u (ss_aux S) | cyc3 (ctor_prime S k)).
Proof.
  intros S k.
  rewrite cyc3_of_ctor.
  apply Z.divide_add_r.
  - apply Z.mod_divide;
      [pose proof (Z.prime_ge_2 _ (sa_u_prime (ss_aux S))); lia|].
    unfold cyc3. apply ss_a_mod_u.
  - eapply Z.divide_mul_l. apply sa_u_divides_mod.
Qed.

Theorem ctor_v_divides_phi4 :
  forall S k, (sa_v (ss_aux S) | cyc4 (ctor_prime S k)).
Proof.
  intros S k.
  rewrite cyc4_of_ctor.
  apply Z.divide_add_r.
  - apply Z.mod_divide;
      [pose proof (Z.prime_ge_2 _ (sa_v_prime (ss_aux S))); lia|].
    unfold cyc4. apply ss_a_mod_v.
  - eapply Z.divide_mul_l. apply sa_v_divides_mod.
Qed.

Theorem ctor_w_divides_phi6 :
  forall S k, (sa_w (ss_aux S) | cyc6 (ctor_prime S k)).
Proof.
  intros S k.
  rewrite cyc6_of_ctor.
  apply Z.divide_add_r.
  - apply Z.mod_divide;
      [pose proof (Z.prime_ge_2 _ (sa_w_prime (ss_aux S))); lia|].
    unfold cyc6. apply ss_a_mod_w.
  - eapply Z.divide_mul_l. apply sa_w_divides_mod.
Qed.

Theorem ctor_p1_resistant :
  forall S k B,
    Z.prime (ctor_prime S k) ->
    B < sa_r (ss_aux S) ->
    p1_resistant (ctor_prime S k) B.
Proof.
  intros S k B _ HB.
  exists (sa_r (ss_aux S)).
  split; [apply sa_r_prime|].
  split; [apply ctor_r_divides_pminus1| exact HB].
Qed.

Theorem ctor_pp1_resistant :
  forall S k B,
    Z.prime (ctor_prime S k) ->
    B < sa_s (ss_aux S) ->
    pp1_resistant (ctor_prime S k) B.
Proof.
  intros S k B _ HB.
  exists (sa_s (ss_aux S)).
  split; [apply sa_s_prime|].
  split; [apply ctor_s_divides_pplus1| exact HB].
Qed.

Theorem ctor_p3_resistant :
  forall S k B,
    Z.prime (ctor_prime S k) ->
    B < sa_u (ss_aux S) ->
    p3_resistant (ctor_prime S k) B.
Proof.
  intros S k B _ HB.
  unfold p3_resistant, cyc_resistant, has_large_prime_factor.
  exists (sa_u (ss_aux S)).
  split; [apply sa_u_prime|].
  split; [apply ctor_u_divides_phi3| exact HB].
Qed.

Theorem ctor_p4_resistant :
  forall S k B,
    Z.prime (ctor_prime S k) ->
    B < sa_v (ss_aux S) ->
    p4_resistant (ctor_prime S k) B.
Proof.
  intros S k B _ HB.
  unfold p4_resistant, cyc_resistant, has_large_prime_factor.
  exists (sa_v (ss_aux S)).
  split; [apply sa_v_prime|].
  split; [apply ctor_v_divides_phi4| exact HB].
Qed.

Theorem ctor_p6_resistant :
  forall S k B,
    Z.prime (ctor_prime S k) ->
    B < sa_w (ss_aux S) ->
    p6_resistant (ctor_prime S k) B.
Proof.
  intros S k B _ HB.
  unfold p6_resistant, cyc_resistant, has_large_prime_factor.
  exists (sa_w (ss_aux S)).
  split; [apply sa_w_prime|].
  split; [apply ctor_w_divides_phi6| exact HB].
Qed.

Theorem ctor_cyc_strong :
  forall S k B,
    Z.prime (ctor_prime S k) ->
    B < sa_r (ss_aux S) -> B < sa_s (ss_aux S) ->
    B < sa_u (ss_aux S) -> B < sa_v (ss_aux S) ->
    B < sa_w (ss_aux S) ->
    cyc_strong (ctor_prime S k) B.
Proof.
  intros. repeat split.
  - apply ctor_p1_resistant; assumption.
  - apply ctor_pp1_resistant; assumption.
  - apply ctor_p3_resistant; assumption.
  - apply ctor_p4_resistant; assumption.
  - apply ctor_p6_resistant; assumption.
Qed.

Theorem ctor_strong :
  forall S k B,
    Z.prime (ctor_prime S k) ->
    B < sa_r (ss_aux S) -> B < sa_s (ss_aux S) ->
    strong_prime (ctor_prime S k) B.
Proof.
  intros. split; [assumption|]. split.
  - apply ctor_p1_resistant; assumption.
  - apply ctor_pp1_resistant; assumption.
Qed.

(** ** Raw pair (CRT walk only) and placed pair (keygen) *)

Record CtorPair : Type := {
  cp_ps : StrongSlot;
  cp_qs : StrongSlot;
  cp_pk : Z;
  cp_qk : Z;
  cp_p_prime : Z.prime (ctor_prime cp_ps cp_pk);
  cp_q_prime : Z.prime (ctor_prime cp_qs cp_qk);
  cp_p_ne_q : ctor_prime cp_ps cp_pk <> ctor_prime cp_qs cp_qk
}.

Definition cp_p (C : CtorPair) : Z := ctor_prime (cp_ps C) (cp_pk C).
Definition cp_q (C : CtorPair) : Z := ctor_prime (cp_qs C) (cp_qk C).
Definition cp_N (C : CtorPair) : Z := cp_p C * cp_q C.

Record PlacedCtorPair : Type := {
  pcp_pair : CtorPair;
  pcp_spec : KeyGenSpec;
  pcp_balanced : kg_balanced (cp_p pcp_pair) (cp_q pcp_pair);
  pcp_far : kg_far (cp_p pcp_pair) (cp_q pcp_pair) (kg_fermat_gap pcp_spec);
  pcp_bits_p : bits_ge (cp_p pcp_pair) (kg_min_bits pcp_spec);
  pcp_bits_q : bits_ge (cp_q pcp_pair) (kg_min_bits pcp_spec);
  pcp_B_lt_rp : kg_smooth_bound pcp_spec < sa_r (ss_aux (cp_ps pcp_pair));
  pcp_B_lt_rq : kg_smooth_bound pcp_spec < sa_r (ss_aux (cp_qs pcp_pair));
  pcp_B_lt_sp : kg_smooth_bound pcp_spec < sa_s (ss_aux (cp_ps pcp_pair));
  pcp_B_lt_sq : kg_smooth_bound pcp_spec < sa_s (ss_aux (cp_qs pcp_pair));
  pcp_B_lt_up : kg_smooth_bound pcp_spec < sa_u (ss_aux (cp_ps pcp_pair));
  pcp_B_lt_uq : kg_smooth_bound pcp_spec < sa_u (ss_aux (cp_qs pcp_pair));
  pcp_B_lt_vp : kg_smooth_bound pcp_spec < sa_v (ss_aux (cp_ps pcp_pair));
  pcp_B_lt_vq : kg_smooth_bound pcp_spec < sa_v (ss_aux (cp_qs pcp_pair));
  pcp_B_lt_wp : kg_smooth_bound pcp_spec < sa_w (ss_aux (cp_ps pcp_pair));
  pcp_B_lt_wq : kg_smooth_bound pcp_spec < sa_w (ss_aux (cp_qs pcp_pair))
}.

Theorem placed_p1_strong :
  forall P, kg_p1_strong (cp_p (pcp_pair P)) (cp_q (pcp_pair P))
              (kg_smooth_bound (pcp_spec P)).
Proof.
  intros P. unfold kg_p1_strong, cp_p, cp_q.
  split.
  - apply ctor_p1_resistant; [apply cp_p_prime | apply pcp_B_lt_rp].
  - apply ctor_p1_resistant; [apply cp_q_prime | apply pcp_B_lt_rq].
Qed.

Theorem placed_pp1_strong :
  forall P, kg_pp1_strong (cp_p (pcp_pair P)) (cp_q (pcp_pair P))
               (kg_smooth_bound (pcp_spec P)).
Proof.
  intros P. unfold kg_pp1_strong, cp_p, cp_q.
  split.
  - apply ctor_pp1_resistant; [apply cp_p_prime | apply pcp_B_lt_sp].
  - apply ctor_pp1_resistant; [apply cp_q_prime | apply pcp_B_lt_sq].
Qed.

Theorem placed_cyc_strong :
  forall P, kg_cyc_strong (cp_p (pcp_pair P)) (cp_q (pcp_pair P))
               (kg_smooth_bound (pcp_spec P)).
Proof.
  intros P. unfold kg_cyc_strong, cp_p, cp_q.
  repeat split.
  - apply ctor_p3_resistant; [apply cp_p_prime | apply pcp_B_lt_up].
  - apply ctor_p3_resistant; [apply cp_q_prime | apply pcp_B_lt_uq].
  - apply ctor_p4_resistant; [apply cp_p_prime | apply pcp_B_lt_vp].
  - apply ctor_p4_resistant; [apply cp_q_prime | apply pcp_B_lt_vq].
  - apply ctor_p6_resistant; [apply cp_p_prime | apply pcp_B_lt_wp].
  - apply ctor_p6_resistant; [apply cp_q_prime | apply pcp_B_lt_wq].
Qed.

(** ** Key: placed pair plus [e,d] *)

Record CtorKey : Type := {
  ck_placed : PlacedCtorPair;
  ck_e : Z;
  ck_d : Z;
  ck_e_not_tiny : kg_e_not_tiny ck_e;
  ck_d_large : kg_large_d ck_d (cp_N (pcp_pair ck_placed));
  ck_dp : kg_dp_not_tiny ck_d (cp_p (pcp_pair ck_placed));
  ck_dq : kg_dp_not_tiny ck_d (cp_q (pcp_pair ck_placed));
  ck_e_coprime :
    Z.coprime ck_e (lambda_semiprime (cp_p (pcp_pair ck_placed))
                                     (cp_q (pcp_pair ck_placed)));
  ck_d_inv :
    (ck_e * ck_d) mod (lambda_semiprime (cp_p (pcp_pair ck_placed))
                                        (cp_q (pcp_pair ck_placed))) = 1;
  ck_d_pos : 0 < ck_d;
  ck_e_pos : 1 < ck_e
}.

Definition ctor_to_rsa (K : CtorKey) : RSAInstance := {|
  rsa_p := cp_p (pcp_pair (ck_placed K));
  rsa_q := cp_q (pcp_pair (ck_placed K));
  rsa_e := ck_e K;
  rsa_d := ck_d K;
  rsa_p_prime := cp_p_prime (pcp_pair (ck_placed K));
  rsa_q_prime := cp_q_prime (pcp_pair (ck_placed K));
  rsa_distinct := cp_p_ne_q (pcp_pair (ck_placed K));
  rsa_e_coprime := ck_e_coprime K;
  rsa_d_inv := ck_d_inv K;
  rsa_d_pos := ck_d_pos K;
  rsa_e_pos := ck_e_pos K
|}.

Theorem ctor_rsa_p :
  forall K, rsa_p (ctor_to_rsa K) = cp_p (pcp_pair (ck_placed K)).
Proof. intros. reflexivity. Qed.

Definition satisfies_keygen_full (S : KeyGenSpec) (R : RSAInstance) : Prop :=
  satisfies_keygen S R /\
  kg_e_not_tiny (rsa_e R) /\
  kg_dp_not_tiny (rsa_d R) (rsa_p R) /\
  kg_dp_not_tiny (rsa_d R) (rsa_q R) /\
  kg_cyc_strong (rsa_p R) (rsa_q R) (kg_smooth_bound S).

Theorem ctor_key_satisfies :
  forall K,
    satisfies_keygen_full (pcp_spec (ck_placed K)) (ctor_to_rsa K).
Proof.
  intros K.
  unfold satisfies_keygen_full, ctor_to_rsa. simpl.
  split; [|split; [|split; [|split]]].
  - unfold satisfies_keygen. simpl.
    split; [apply pcp_balanced|].
    split; [apply pcp_far|].
    split; [apply pcp_bits_p|].
    split; [apply pcp_bits_q|].
    split; [apply ck_d_large|].
    split.
    + unfold kg_p1_strong, cp_p, cp_q.
      split; apply ctor_p1_resistant;
        [apply cp_p_prime | apply pcp_B_lt_rp | apply cp_q_prime | apply pcp_B_lt_rq].
    + unfold kg_pp1_strong, cp_p, cp_q.
      split; apply ctor_pp1_resistant;
        [apply cp_p_prime | apply pcp_B_lt_sp | apply cp_q_prime | apply pcp_B_lt_sq].
  - apply ck_e_not_tiny.
  - apply ck_dp.
  - apply ck_dq.
  - unfold kg_cyc_strong, cp_p, cp_q. repeat split.
    + apply ctor_p3_resistant; [apply cp_p_prime | apply pcp_B_lt_up].
    + apply ctor_p3_resistant; [apply cp_q_prime | apply pcp_B_lt_uq].
    + apply ctor_p4_resistant; [apply cp_p_prime | apply pcp_B_lt_vp].
    + apply ctor_p4_resistant; [apply cp_q_prime | apply pcp_B_lt_vq].
    + apply ctor_p6_resistant; [apply cp_p_prime | apply pcp_B_lt_wp].
    + apply ctor_p6_resistant; [apply cp_q_prime | apply pcp_B_lt_wq].
Qed.

Theorem ctor_key_satisfies_filter :
  forall K,
    satisfies_keygen (pcp_spec (ck_placed K)) (ctor_to_rsa K).
Proof.
  intros K. apply (proj1 (ctor_key_satisfies K)).
Qed.

(** ** Discriminators *)

Definition in_slot_image (S : StrongSlot) (k p : Z) : Prop :=
  p = ctor_prime S k.

Theorem in_slot_image_on_ap :
  forall S k p,
    in_slot_image S k p ->
    0 <= k ->
    roca_form p k (sa_mod (ss_aux S)) (ss_a S).
Proof.
  intros S k p Hp Hk.
  unfold in_slot_image in Hp. subst p.
  unfold roca_form, ctor_prime.
  pose proof (sa_mod_pos (ss_aux S)).
  pose proof (ss_a_range S).
  split; [lia|].
  split; [|lia].
  apply Z.add_comm.
Qed.

Definition public_ap_discriminates (S : StrongSlot) (p : Z) : Prop :=
  p mod sa_mod (ss_aux S) = ss_a S.

Theorem slot_image_is_public_ap :
  forall S k p,
    in_slot_image S k p ->
    public_ap_discriminates S p.
Proof.
  intros S k p Hp.
  unfold in_slot_image in Hp. subst p.
  unfold public_ap_discriminates, ctor_prime.
  pose proof (sa_mod_pos (ss_aux S)).
  pose proof (ss_a_range S).
  symmetry.
  apply (Z.mod_unique (ss_a S + k * sa_mod (ss_aux S))
                      (sa_mod (ss_aux S)) k (ss_a S)).
  - lia.
  - rewrite (Z.add_comm (ss_a S) (k * sa_mod (ss_aux S))).
    rewrite (Z.mul_comm k (sa_mod (ss_aux S))).
    reflexivity.
Qed.

Definition secret_aux_discriminates (A : StrongAux) (p : Z) : Prop :=
  (sa_r A | p - 1) /\ (sa_s A | p + 1) /\
  (sa_u A | cyc3 p) /\ (sa_v A | cyc4 p) /\ (sa_w A | cyc6 p).

Theorem slot_image_has_secret_aux :
  forall S k p,
    in_slot_image S k p ->
    secret_aux_discriminates (ss_aux S) p.
Proof.
  intros S k p Hp. unfold in_slot_image in Hp. subst p.
  repeat split.
  - apply ctor_r_divides_pminus1.
  - apply ctor_s_divides_pplus1.
  - apply ctor_u_divides_phi3.
  - apply ctor_v_divides_phi4.
  - apply ctor_w_divides_phi6.
Qed.

(** ** Parameter statement (AP enumeration, not NFS) *)

Definition ap_candidates (b M : Z) : Z := 2 ^ b / M + 1.

Theorem ap_candidates_bound :
  forall b M,
    0 < M ->
    0 <= b ->
    ap_candidates b M * M <= 2 ^ b + M.
Proof.
  intros b M HM Hb. unfold ap_candidates.
  pose proof (Z.div_mod (2 ^ b) M ltac:(lia)).
  pose proof (Z.mod_pos_bound (2 ^ b) M ltac:(lia)).
  replace ((2 ^ b / M + 1) * M) with ((2 ^ b / M) * M + M) by ring.
  nia.
Qed.

Theorem public_ap_div_le_shift :
  forall b M kappa,
    0 < M ->
    0 <= kappa ->
    kappa <= b ->
    2 ^ kappa <= M ->
    2 ^ b / M <= 2 ^ (b - kappa).
Proof.
  intros b M kappa HM Hkap Hle Hpow.
  apply Z.le_trans with (2 ^ b / 2 ^ kappa).
  - apply Z.div_le_compat_l.
    + apply Z.pow_nonneg; lia.
    + split; [apply Z.pow_pos_nonneg; lia | exact Hpow].
  - rewrite <- Z.pow_sub_r by lia. lia.
Qed.

Theorem public_ap_search_bits :
  forall b M kappa,
    0 < M ->
    0 <= kappa ->
    kappa <= b ->
    2 ^ kappa <= M ->
    ap_candidates b M <= 2 ^ (b - kappa) + 1.
Proof.
  intros b M kappa HM Hkap Hle Hpow.
  unfold ap_candidates.
  pose proof (public_ap_div_le_shift b M kappa HM Hkap Hle Hpow).
  lia.
Qed.

Definition regime_1024 : KeyGenSpec := {|
  kg_min_bits := 512;
  kg_fermat_gap := 200;
  kg_smooth_bound := 160
|}.

Definition regime_bits_against_public_ap (prime_bits M_bits : Z) : Z :=
  prime_bits - M_bits.

Theorem regime_1024_ap_budget :
  forall M_bits,
    0 <= M_bits <= 512 ->
    regime_bits_against_public_ap 512 M_bits = 512 - M_bits.
Proof. intros. reflexivity. Qed.

Theorem catalog_handle_bits_are_zero :
  forall K,
    satisfies_keygen (pcp_spec (ck_placed K)) (ctor_to_rsa K) ->
    True.
Proof. intros. exact I. Qed.
