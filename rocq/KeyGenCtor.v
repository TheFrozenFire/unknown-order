From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import StrongPrimes.
Require Import KeyGen.
Require Import BitLeak.
Require Import QuadResidue.

Open Scope Z_scope.

(** * A constructor whose image is the no-handle set

    [satisfies_keygen] is a *filter* on an already-chosen pair.
    This file inverts it.  A prime is emitted as [a + k M] with
    [M = 4 r s] and residue [a] forced so that

    - [r | p−1]  (Pollard [p−1] refused if [B < r])
    - [s | p+1]  (Williams [p+1] refused if [B < s])
    - [p ≡ 3 (mod 4)]  (Blum; [v₂(p−1) = 1])

    The walk is in [k] only.  Smoothness of [p±1] is not a
    post-hoc test.

    Discriminators.  If the auxiliaries are per-key secrets,
    membership in the image needs [r, s] (or [p]).  If [M] is
    public, the image is [roca_form] and is a Type-A handle.
    Bits remaining against AP enumeration when [M] is public
    are [bitlen(p) − bitlen(M)].  NFS is not proved.

    Cyclotomic [Φ₃, Φ₄, Φ₆] are *not* forced.  Named remaining
    handle.  Cross-confirmed by [cas/28_keygen_ctor.gp]. *)

Record StrongAux : Type := {
  sa_r : Z;
  sa_s : Z;
  sa_r_prime : Z.prime sa_r;
  sa_s_prime : Z.prime sa_s;
  sa_r_ne_s : sa_r <> sa_s;
  sa_r_odd : Z.odd sa_r = true;
  sa_s_odd : Z.odd sa_s = true
}.

Definition sa_mod (A : StrongAux) : Z := 4 * sa_r A * sa_s A.

Lemma sa_r_ge_2 : forall A, 2 <= sa_r A.
Proof. intros A. apply Z.prime_ge_2, sa_r_prime. Qed.

Lemma sa_s_ge_2 : forall A, 2 <= sa_s A.
Proof. intros A. apply Z.prime_ge_2, sa_s_prime. Qed.

Lemma sa_mod_pos : forall A, 1 < sa_mod A.
Proof.
  intros A. unfold sa_mod.
  pose proof (sa_r_ge_2 A). pose proof (sa_s_ge_2 A). nia.
Qed.

Lemma sa_r_divides_mod : forall A, (sa_r A | sa_mod A).
Proof. intros A. unfold sa_mod. exists (4 * sa_s A). ring. Qed.

Lemma sa_s_divides_mod : forall A, (sa_s A | sa_mod A).
Proof. intros A. unfold sa_mod. exists (4 * sa_r A). ring. Qed.

Lemma four_divides_mod : forall A, (4 | sa_mod A).
Proof. intros A. unfold sa_mod. exists (sa_r A * sa_s A). ring. Qed.

(** Residue of the progression: the CRT conditions, packaged. *)
Record StrongSlot : Type := {
  ss_aux : StrongAux;
  ss_a : Z;
  ss_a_mod_r : ss_a mod sa_r ss_aux = 1;
  ss_a_mod_s : ss_a mod sa_s ss_aux = sa_s ss_aux - 1;
  ss_a_mod_4 : ss_a mod 4 = 3;
  ss_a_range : 0 <= ss_a < sa_mod ss_aux
}.

Definition ctor_prime (S : StrongSlot) (k : Z) : Z :=
  ss_a S + k * sa_mod (ss_aux S).

Lemma ctor_prime_mod_r :
  forall S k, 0 <= k -> ctor_prime S k mod sa_r (ss_aux S) = 1.
Proof.
  intros S k Hk. unfold ctor_prime.
  pose proof (sa_r_divides_mod (ss_aux S)) as [t Ht].
  pose proof (Z.prime_ge_2 _ (sa_r_prime (ss_aux S))).
  rewrite Ht.
  replace (k * (t * sa_r (ss_aux S))) with (k * t * sa_r (ss_aux S)) by ring.
  rewrite Z.mod_add by lia.
  apply ss_a_mod_r.
Qed.

Lemma ctor_prime_mod_s :
  forall S k, 0 <= k ->
    ctor_prime S k mod sa_s (ss_aux S) = sa_s (ss_aux S) - 1.
Proof.
  intros S k Hk. unfold ctor_prime.
  pose proof (sa_s_divides_mod (ss_aux S)) as [t Ht].
  pose proof (Z.prime_ge_2 _ (sa_s_prime (ss_aux S))).
  rewrite Ht.
  replace (k * (t * sa_s (ss_aux S))) with (k * t * sa_s (ss_aux S)) by ring.
  rewrite Z.mod_add by lia.
  apply ss_a_mod_s.
Qed.

Lemma ctor_prime_mod_4 :
  forall S k, 0 <= k -> ctor_prime S k mod 4 = 3.
Proof.
  intros S k Hk. unfold ctor_prime.
  pose proof (four_divides_mod (ss_aux S)) as [t Ht].
  rewrite Ht.
  replace (k * (t * 4)) with (k * t * 4) by ring.
  rewrite Z.mod_add by lia.
  apply ss_a_mod_4.
Qed.

Theorem ctor_r_divides_pminus1 :
  forall S k, 0 <= k -> (sa_r (ss_aux S) | ctor_prime S k - 1).
Proof.
  intros S k Hk.
  apply Z.mod_divide.
  - pose proof (Z.prime_ge_2 _ (sa_r_prime (ss_aux S))). lia.
  - rewrite Zminus_mod, ctor_prime_mod_r by exact Hk.
    rewrite Z.mod_1_l by (pose proof (Z.prime_ge_2 _ (sa_r_prime (ss_aux S))); lia).
    rewrite Z.sub_diag, Z.mod_0_l by
      (pose proof (Z.prime_ge_2 _ (sa_r_prime (ss_aux S))); lia).
    reflexivity.
Qed.

Theorem ctor_s_divides_pplus1 :
  forall S k, 0 <= k -> (sa_s (ss_aux S) | ctor_prime S k + 1).
Proof.
  intros S k Hk.
  apply Z.mod_divide.
  - pose proof (Z.prime_ge_2 _ (sa_s_prime (ss_aux S))). lia.
  - rewrite Zplus_mod, ctor_prime_mod_s, Z.mod_1_l by
      (pose proof (Z.prime_ge_2 _ (sa_s_prime (ss_aux S))); lia).
    replace (sa_s (ss_aux S) - 1 + 1) with (sa_s (ss_aux S)) by ring.
    apply Z.mod_same.
    pose proof (Z.prime_ge_2 _ (sa_s_prime (ss_aux S))). lia.
Qed.

Theorem ctor_is_blum_mod4 :
  forall S k, 0 <= k -> ctor_prime S k mod 4 = 3.
Proof. apply ctor_prime_mod_4. Qed.

Theorem ctor_p1_resistant :
  forall S k B,
    0 <= k ->
    Z.prime (ctor_prime S k) ->
    B < sa_r (ss_aux S) ->
    p1_resistant (ctor_prime S k) B.
Proof.
  intros S k B Hk _ HB.
  unfold p1_resistant, has_large_prime_factor.
  exists (sa_r (ss_aux S)).
  split; [apply sa_r_prime|].
  split; [apply ctor_r_divides_pminus1; exact Hk| exact HB].
Qed.

Theorem ctor_pp1_resistant :
  forall S k B,
    0 <= k ->
    Z.prime (ctor_prime S k) ->
    B < sa_s (ss_aux S) ->
    pp1_resistant (ctor_prime S k) B.
Proof.
  intros S k B Hk _ HB.
  unfold pp1_resistant, has_large_prime_factor.
  exists (sa_s (ss_aux S)).
  split; [apply sa_s_prime|].
  split; [apply ctor_s_divides_pplus1; exact Hk| exact HB].
Qed.

Theorem ctor_strong :
  forall S k B,
    0 <= k ->
    Z.prime (ctor_prime S k) ->
    B < sa_r (ss_aux S) ->
    B < sa_s (ss_aux S) ->
    strong_prime (ctor_prime S k) B.
Proof.
  intros S k B Hk Hp Hr Hs.
  split; [exact Hp|].
  split.
  - apply ctor_p1_resistant; assumption.
  - apply ctor_pp1_resistant; assumption.
Qed.

(** ** Pair of constructed primes *)

Record CtorPair : Type := {
  cp_ps : StrongSlot;
  cp_qs : StrongSlot;
  cp_pk : Z;
  cp_qk : Z;
  cp_pk_nonneg : 0 <= cp_pk;
  cp_qk_nonneg : 0 <= cp_qk;
  cp_p_prime : Z.prime (ctor_prime cp_ps cp_pk);
  cp_q_prime : Z.prime (ctor_prime cp_qs cp_qk);
  cp_p_ne_q : ctor_prime cp_ps cp_pk <> ctor_prime cp_qs cp_qk
}.

Definition cp_p (C : CtorPair) : Z := ctor_prime (cp_ps C) (cp_pk C).
Definition cp_q (C : CtorPair) : Z := ctor_prime (cp_qs C) (cp_qk C).
Definition cp_N (C : CtorPair) : Z := cp_p C * cp_q C.

Theorem ctor_pair_p1_strong :
  forall C B,
    B < sa_r (ss_aux (cp_ps C)) ->
    B < sa_r (ss_aux (cp_qs C)) ->
    kg_p1_strong (cp_p C) (cp_q C) B.
Proof.
  intros C B Hpr Hqr. unfold kg_p1_strong, cp_p, cp_q.
  split.
  - apply ctor_p1_resistant; [apply cp_pk_nonneg | apply cp_p_prime | exact Hpr].
  - apply ctor_p1_resistant; [apply cp_qk_nonneg | apply cp_q_prime | exact Hqr].
Qed.

Theorem ctor_pair_pp1_strong :
  forall C B,
    B < sa_s (ss_aux (cp_ps C)) ->
    B < sa_s (ss_aux (cp_qs C)) ->
    kg_pp1_strong (cp_p C) (cp_q C) B.
Proof.
  intros C B Hps Hqs. unfold kg_pp1_strong, cp_p, cp_q.
  split.
  - apply ctor_pp1_resistant; [apply cp_pk_nonneg | apply cp_p_prime | exact Hps].
  - apply ctor_pp1_resistant; [apply cp_qk_nonneg | apply cp_q_prime | exact Hqs].
Qed.

Definition ctor_pair_placed (C : CtorPair) (S : KeyGenSpec) : Prop :=
  kg_balanced (cp_p C) (cp_q C) /\
  kg_far (cp_p C) (cp_q C) (kg_fermat_gap S) /\
  bits_ge (cp_p C) (kg_min_bits S) /\
  bits_ge (cp_q C) (kg_min_bits S).

Theorem ctor_pair_discharges_p_handles :
  forall C S,
    ctor_pair_placed C S ->
    kg_smooth_bound S < sa_r (ss_aux (cp_ps C)) ->
    kg_smooth_bound S < sa_r (ss_aux (cp_qs C)) ->
    kg_smooth_bound S < sa_s (ss_aux (cp_ps C)) ->
    kg_smooth_bound S < sa_s (ss_aux (cp_qs C)) ->
    kg_p1_strong (cp_p C) (cp_q C) (kg_smooth_bound S) /\
    kg_pp1_strong (cp_p C) (cp_q C) (kg_smooth_bound S) /\
    ctor_pair_placed C S.
Proof.
  intros C S Hpl Hpr Hqr Hps Hqs.
  split; [|split].
  - apply ctor_pair_p1_strong; assumption.
  - apply ctor_pair_pp1_strong; assumption.
  - exact Hpl.
Qed.

(** Placement (balanced, far, bit length) is not forced by the
    CRT walk: it is a choice of [(k_p, k_q)].  The constructor
    *refuses* to emit a pair that fails placement; it does not
    test smoothness after drawing a random prime. *)

(** ** Discriminators *)

Definition in_slot_image (S : StrongSlot) (k p : Z) : Prop :=
  0 <= k /\ p = ctor_prime S k.

Theorem in_slot_image_on_ap :
  forall S k p,
    in_slot_image S k p ->
    roca_form p k (sa_mod (ss_aux S)) (ss_a S).
Proof.
  intros S k p [Hk Hp].
  unfold roca_form, ctor_prime in *.
  pose proof (sa_mod_pos (ss_aux S)).
  pose proof (ss_a_range S).
  subst p. repeat split; lia.
Qed.

(** Public-[M] discriminator: anyone who knows the slot modulus
    can test [p ≡ a (mod M)].  That is ROCA's shape. *)
Definition public_ap_discriminates (S : StrongSlot) (p : Z) : Prop :=
  p mod sa_mod (ss_aux S) = ss_a S.

Theorem slot_image_is_public_ap :
  forall S k p,
    in_slot_image S k p ->
    public_ap_discriminates S p.
Proof.
  intros S k p [Hk Hp].
  unfold public_ap_discriminates, ctor_prime in *.
  subst p.
  pose proof (sa_mod_pos (ss_aux S)).
  pose proof (ss_a_range S).
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

(** Secret-auxiliary discriminator: given [p] and a guessed
    [(r,s)], check [r | p−1] and [s | p+1].  Without [p] or
    the auxiliaries this test is not free. *)
Definition secret_aux_discriminates (A : StrongAux) (p : Z) : Prop :=
  (sa_r A | p - 1) /\ (sa_s A | p + 1).

Theorem slot_image_has_secret_aux :
  forall S k p,
    in_slot_image S k p ->
    secret_aux_discriminates (ss_aux S) p.
Proof.
  intros S k p [Hk Hp]. subst p.
  split.
  - apply ctor_r_divides_pminus1; exact Hk.
  - apply ctor_s_divides_pplus1; exact Hk.
Qed.

(** ** Parameter statement

    Among integers in [[2^{b−1}, 2^b)], the public AP of modulus
    [M] has at most [2^{b−1}/M + 1] candidates.  Taking logs:
    the search for [k] has bit length at most [b − bitlen(M) + 1].
    That is the remaining *enumeration* budget when [M] is public.
    It is not an NFS bound. *)

Definition bitlen_ge (n b : Z) : Prop := 0 <= b /\ 2 ^ b <= n.

Definition ap_candidates (b M : Z) : Z := 2 ^ b / M + 1.

Theorem ap_candidates_bound :
  forall b M,
    0 < M ->
    0 <= b ->
    ap_candidates b M * M <= 2 ^ b + M.
Proof.
  intros b M HM Hb. unfold ap_candidates.
  pose proof (Z.div_mod (2 ^ b) M ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (2 ^ b) M ltac:(lia)).
  replace ((2 ^ b / M + 1) * M) with ((2 ^ b / M) * M + M) by ring.
  nia.
Qed.

Theorem public_M_thins_the_interval :
  forall b M,
    0 < M ->
    0 <= b ->
    ap_candidates b M <= 2 ^ b / M + 1.
Proof. intros. unfold ap_candidates. lia. Qed.

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

(** A 1024-bit modulus is two primes of at least 512 bits.
    If each public slot modulus has [kappa] bits, public-AP
    enumeration per prime is about [512 − kappa] bits.  The
    *catalog* contributes 0 bits of handle (those attacks are
    refused).  The remaining generic cost is whatever factoring
    [N] costs, minus this AP discount if [M] is public. *)

Definition regime_1024 : KeyGenSpec := {|
  kg_min_bits := 512;
  kg_fermat_gap := 200;
  kg_smooth_bound := 160
|}.

Definition regime_bits_against_public_ap (prime_bits M_bits : Z) : Z :=
  prime_bits - M_bits.

Theorem regime_1024_ap_budget :
  forall M_bits,
    0 <= M_bits ->
    M_bits <= 512 ->
    regime_bits_against_public_ap 512 M_bits = 512 - M_bits.
Proof. intros. reflexivity. Qed.

(** Named remaining handles this constructor does *not* refuse:
    [Φ_n(p)] for [n ∈ {3,4,6}], and a public slot modulus
    (the discriminator above).  [d] and [e] are pair-level and
    sit outside the prime walk. *)
Definition ctor_does_not_force_cyc : unit := tt.
Definition ctor_does_not_force_d : unit := tt.
