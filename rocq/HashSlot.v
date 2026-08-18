From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import StrongPrimes.
Require Import KeyGen.
Require Import BitLeak.
Require Import Cyclotomic.
Require Import KeyGenCtor.

Open Scope Z_scope.

(** * Slot encoding: the generator lands only on the constructor AP

    A seed is an integer.  [slot_encode S seed] is the constructor
    walk at [k = seed].  There is no hash and no oracle
    ([Refuse_hash_as_oracle], [Refuse_SHA_in_Rocq]).  Every
    output is in the slot.  If it is prime and the auxiliaries
    exceed [B], it is [cyc_strong] and Blum.  Generation accept is
    [Z.prime].  If the encoding is public, the image is
    [roca_form].  Placement is not the encoding.

    CAS [cas/29_hash_slot.gp], [cas/30_hash_slot_cost.gp]. *)

Definition slot_k (seed : Z) : Z := seed.

Definition slot_encode (S : StrongSlot) (seed : Z) : Z :=
  ctor_prime S (slot_k seed).

Definition slot_accept (S : StrongSlot) (seed : Z) : Prop :=
  Z.prime (slot_encode S seed).

Theorem slot_encode_in_image :
  forall S seed,
    in_slot_image S (slot_k seed) (slot_encode S seed).
Proof. intros. unfold in_slot_image, slot_encode, slot_k. reflexivity. Qed.

Theorem slot_encode_rulers :
  forall S seed B,
    slot_accept S seed ->
    B < sa_r (ss_aux S) -> B < sa_s (ss_aux S) ->
    B < sa_u (ss_aux S) -> B < sa_v (ss_aux S) ->
    B < sa_w (ss_aux S) ->
    cyc_strong (slot_encode S seed) B /\
    ctor_prime S (slot_k seed) mod 4 = 3.
Proof.
  intros S seed B Hacc Hr Hs Hu Hv Hw.
  unfold slot_accept, slot_encode, slot_k in *.
  split.
  - apply ctor_cyc_strong; assumption.
  - apply ctor_is_blum_mod4.
Qed.

Theorem slot_accept_implies_rulers :
  forall S seed B,
    slot_accept S seed ->
    B < sa_r (ss_aux S) -> B < sa_s (ss_aux S) ->
    B < sa_u (ss_aux S) -> B < sa_v (ss_aux S) ->
    B < sa_w (ss_aux S) ->
    cyc_strong (slot_encode S seed) B.
Proof.
  intros. apply slot_encode_rulers; assumption.
Qed.

(** If an encoding output fails the rulers, it is composite.
    Off-image primes can fail a ruler without being composite —
    that is a fact about membership, not about accept. *)
Theorem slot_reject_is_composite :
  forall S seed B,
    B < sa_r (ss_aux S) -> B < sa_s (ss_aux S) ->
    B < sa_u (ss_aux S) -> B < sa_v (ss_aux S) ->
    B < sa_w (ss_aux S) ->
    ~ cyc_strong (slot_encode S seed) B ->
    ~ Z.prime (slot_encode S seed).
Proof.
  intros S seed B Hr Hs Hu Hv Hw Hfail Hpr.
  apply Hfail. unfold slot_encode, slot_k in *.
  apply ctor_cyc_strong; assumption.
Qed.

Theorem slot_encode_public_ap :
  forall S seed,
    public_ap_discriminates S (slot_encode S seed).
Proof.
  intros S seed.
  apply (slot_image_is_public_ap S (slot_k seed)).
  apply slot_encode_in_image.
Qed.

Theorem public_slot_encode_is_roca :
  forall S seed,
    0 <= seed ->
    roca_form (slot_encode S seed) (slot_k seed)
              (sa_mod (ss_aux S)) (ss_a S).
Proof.
  intros S seed Hk.
  apply in_slot_image_on_ap; [apply slot_encode_in_image | exact Hk].
Qed.

(** A public encoding publishes [M].  There is no public
    [slot_encode] free of Type A. *)
Theorem public_encode_admits_ap_test :
  forall S seed,
    public_ap_discriminates S (slot_encode S seed).
Proof. apply slot_encode_public_ap. Qed.

Theorem public_slot_encode_ap_budget :
  forall S b kappa,
    0 <= kappa ->
    kappa <= b ->
    2 ^ kappa <= sa_mod (ss_aux S) ->
    ap_candidates b (sa_mod (ss_aux S)) <= 2 ^ (b - kappa) + 1.
Proof.
  intros S b kappa Hkap Hle Hpow.
  pose proof (sa_mod_pos (ss_aux S)).
  apply public_ap_search_bits; lia.
Qed.

(** ** Placement is not the encoding *)

Definition pair_encode (S : StrongSlot) (seed : Z) : Z * Z :=
  (slot_encode S seed, slot_encode S (seed + 2)).

Theorem cas28_seeds_not_balanced :
  ~ kg_balanced 13099 220579 /\ ~ kg_balanced 220579 13099.
Proof. split; intros [H1 [H2 H3]]; lia. Qed.

Theorem slot_encode_does_not_place :
  forall S,
    ss_a S = 13099 ->
    sa_mod (ss_aux S) = 103740 ->
    ~ kg_balanced (slot_encode S 0) (slot_encode S 2) /\
    ~ kg_balanced (slot_encode S 2) (slot_encode S 0).
Proof.
  intros S Ha HM.
  unfold slot_encode, slot_k, ctor_prime.
  rewrite Ha, HM.
  replace (13099 + 0 * 103740) with 13099 by lia.
  replace (13099 + 2 * 103740) with 220579 by lia.
  apply cas28_seeds_not_balanced.
Qed.

Theorem pair_encode_does_not_force_balance :
  forall S,
    ss_a S = 13099 ->
    sa_mod (ss_aux S) = 103740 ->
    let pq := pair_encode S 0 in
    ~ kg_balanced (fst pq) (snd pq) /\
    ~ kg_balanced (snd pq) (fst pq).
Proof.
  intros S Ha HM pq. subst pq. unfold pair_encode. simpl.
  apply slot_encode_does_not_place; assumption.
Qed.

(** ** Try-and-increment is a filter spec, not a program *)

Definition slot_try (S : StrongSlot) (seed0 bound : Z) (p : Z) : Prop :=
  exists i, 0 <= i < bound /\
            p = slot_encode S (seed0 + i) /\
            Z.prime p.

Theorem slot_try_sound :
  forall S seed0 bound p B,
    slot_try S seed0 bound p ->
    B < sa_r (ss_aux S) -> B < sa_s (ss_aux S) ->
    B < sa_u (ss_aux S) -> B < sa_v (ss_aux S) ->
    B < sa_w (ss_aux S) ->
    Z.prime p /\
    (exists i, 0 <= i < bound /\ in_slot_image S (seed0 + i) p) /\
    cyc_strong p B.
Proof.
  intros S seed0 bound p B [i [Hi [Hp Hpr]]] Hr Hs Hu Hv Hw.
  subst p.
  split; [exact Hpr|].
  split.
  - exists i. split; [exact Hi|].
    unfold in_slot_image, slot_encode, slot_k. reflexivity.
  - unfold slot_encode, slot_k in *.
    apply ctor_cyc_strong; assumption.
Qed.

Theorem slot_try_complete :
  forall S seed0 bound i,
    0 <= i < bound ->
    Z.prime (slot_encode S (seed0 + i)) ->
    slot_try S seed0 bound (slot_encode S (seed0 + i)).
Proof.
  intros S seed0 bound i Hi Hpr.
  exists i.
  split; [exact Hi|].
  split; [reflexivity| exact Hpr].
Qed.
