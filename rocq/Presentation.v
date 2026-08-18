From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import BinForms.
Require Import ClassGroupWall.

Open Scope Z_scope.

(** * A presentation of a group of unknown order

    Carrier, multiplication, identity, exponentiation, a named
    constructible-torsion predicate, and an optional *public*
    annihilator.  RSA's public view has [None]; the trapdoor view
    would carry [Some λ].  [Cl(Δ)] carries [Some 2] — the
    2-annihilator is public; no odd period is.

    Constructible torsion [Pconstructible] is a family parameter,
    not a global [Cl[2]].  Ordinary class groups use ambiguous
    forms; a Mersenne / Shanks family also constructs the order-3
    class.  Adaptive root as a game is [P_AdaptiveRoot_C]; the
    search relation stays [P_AdaptiveRoot] / Strong RSA.

    Problems are the same winning conditions as [UnknownOrder],
    stated once.  Sentences 1–3 of the roadmap instantiate on
    both carriers. *)

Record Presentation : Type := {
  Pcar : Type;
  Peq : Pcar -> Pcar -> Prop;
  Pmul : Pcar -> Pcar -> Pcar;
  Pid : Pcar;
  Pinv : Pcar -> Pcar;
  Pexp : Pcar -> nat -> Pcar;
  Pconstructible : Pcar -> Prop;
  Pannihilator : option Z
}.

Definition P_is_order (P : Presentation) (a : Pcar P) (k : nat) : Prop :=
  (k > 0)%nat /\
  Peq P (Pexp P a k) (Pid P) /\
  forall k', (0 < k' < k)%nat -> ~ Peq P (Pexp P a k') (Pid P).

Definition P_Order (P : Presentation) (a : Pcar P) (k : nat) : Prop :=
  P_is_order P a k.

Definition P_LowOrder (P : Presentation) (B : Z) (a : Pcar P) (k : nat) : Prop :=
  ~ Peq P a (Pid P) /\ P_is_order P a k /\ Z.of_nat k <= B.

Definition P_LowOrderOutside (P : Presentation) (B : Z) (a : Pcar P) (k : nat) : Prop :=
  P_LowOrder P B a k /\ ~ Pconstructible P a.

Definition P_Root (P : Presentation) (e : nat) (y x : Pcar P) : Prop :=
  (e > 0)%nat /\ Peq P (Pexp P x e) y.

Definition P_AdaptiveRoot (P : Presentation) (y x : Pcar P) (e : nat) : Prop :=
  (e > 1)%nat /\ Peq P (Pexp P x e) y.

(** Game: [y] is published first, then [c] is drawn from [C].
    The attacker does not choose [c].  Exclude [y = 1] as in
    Wesolowski / 2024/505. *)
Definition P_AdaptiveRoot_C (P : Presentation) (C : nat -> Prop)
    (y x : Pcar P) (c : nat) : Prop :=
  C c /\
  (c > 1)%nat /\
  ~ Peq P y (Pid P) /\
  Peq P (Pexp P x c) y.

(** ** RSA, public view: no annihilator, constructible torsion is [±1] *)

Definition rsa_presentation (N : Z) : Presentation := {|
  Pcar := Z;
  Peq := fun x y => x mod N = y mod N;
  Pmul := fun x y => (x * y) mod N;
  Pid := 1;
  Pinv := fun a => a;
  Pexp := fun a k => powm a (Z.of_nat k) N;
  Pconstructible := fun a => rsa_constructible_2torsion N a;
  Pannihilator := None
|}.

Definition rsa_trapdoor_presentation (N lam : Z) : Presentation := {|
  Pcar := Z;
  Peq := fun x y => x mod N = y mod N;
  Pmul := fun x y => (x * y) mod N;
  Pid := 1;
  Pinv := fun a => powm a (Z.abs (lam - 1)) N;
  Pexp := fun a k => powm a (Z.of_nat k) N;
  Pconstructible := fun a => rsa_constructible_2torsion N a;
  Pannihilator := Some lam
|}.

(** ** [Cl(Δ)]: public 2-annihilator, constructible torsion is ambiguous forms *)

Definition cl_presentation_H (D : Z) (H : bqf -> Prop) : Presentation := {|
  Pcar := bqf;
  Peq := bqf_equiv;
  Pmul := bqf_compose;
  Pid := bqf_id D;
  Pinv := bqf_inv;
  Pexp := bqf_exp D;
  Pconstructible := H;
  Pannihilator := Some 2
|}.

Definition cl_presentation (D : Z) : Presentation :=
  cl_presentation_H D cl_ordinary_H.

Definition cl_mersenne_presentation (u : Z) : Presentation :=
  cl_presentation_H (shanks_disc u) (cl_mersenne_H u).

Definition UOFamily := Z -> Presentation.

Definition ordinary_cl_family : UOFamily := cl_presentation.
Definition mersenne_cl_family : UOFamily := cl_mersenne_presentation.

(** ** Sentence 1 — units have an order, which divides every annihilator *)

Theorem rsa_order_divides_lambda :
  forall p q a k,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime a (p * q) ->
    is_order (p * q) a k ->
    (k | lambda_semiprime p q).
Proof. apply order_divides_lambda. Qed.

Theorem cl_constructible_order_divides_2 :
  forall f, bqf_ambiguous f -> bqf_equiv f (bqf_inv f).
Proof. apply public_2_annihilator_hits_ambiguous. Qed.

(** ** Sentence 2 — low-order for [B = 2] is a public construction
    on [Cl], and only [±1] on RSA *)

Theorem rsa_public_annihilator_is_none :
  forall N, Pannihilator (rsa_presentation N) = None.
Proof. reflexivity. Qed.

Theorem cl_public_annihilator_is_two :
  forall D, Pannihilator (cl_presentation D) = Some 2.
Proof. reflexivity. Qed.

Theorem rsa_minus1_constructible :
  forall N, 1 < N -> Pconstructible (rsa_presentation N) (N - 1).
Proof. intros. apply rsa_minus1_is_constructible. exact H. Qed.

Theorem cl_unrestricted_LowOrder_B2 :
  Problem_LowOrder_Cl (-87) 2 form_neg87_amb.
Proof. apply unrestricted_LowOrder_won_by_Cl2. Qed.

Theorem cl_restricted_excludes_ambiguous :
  forall D B f,
    bqf_ambiguous f ->
    ~ P_LowOrderOutside (cl_presentation D) B f 2%nat.
Proof.
  intros D B f Hamb [_ Hcon].
  unfold cl_presentation in Hcon. simpl in Hcon. exact (Hcon Hamb).
Qed.

Theorem mersenne31_wins_P_LowOrderOutside :
  P_LowOrderOutside (cl_presentation (-31)) 3 form_neg31_ord3 3%nat.
Proof.
  pose proof mersenne31_wins_restricted_LowOrder as H.
  unfold Problem_LowOrderRestricted_Cl in H.
  destruct H as [Hof [Hna [Hnp [H3 [Hmin [Hk HB]]]]]].
  unfold P_LowOrderOutside, P_LowOrder, P_is_order, cl_presentation.
  simpl.
  split.
  - split.
    + exact Hnp.
    + split.
      * split; [lia|]. split; [exact H3|].
        intros k' Hk'. apply Hmin. exact Hk'.
      * exact HB.
  - exact Hna.
Qed.

Theorem mersenne31_family_excludes_shanks :
  ~ P_LowOrderOutside (cl_mersenne_presentation 2) 3
      form_neg31_ord3 3%nat.
Proof.
  intros [_ Hcon].
  unfold cl_mersenne_presentation, cl_presentation_H in Hcon.
  simpl in Hcon.
  apply Hcon. apply mersenne31_shanks_in_family_H.
Qed.

Theorem ordinary_vs_mersenne_H :
  P_LowOrderOutside (cl_presentation (-31)) 3 form_neg31_ord3 3%nat /\
  ~ P_LowOrderOutside (cl_mersenne_presentation 2) 3
      form_neg31_ord3 3%nat.
Proof.
  split; [apply mersenne31_wins_P_LowOrderOutside
        | apply mersenne31_family_excludes_shanks].
Qed.

Theorem mersenne_family_at_2 :
  mersenne_cl_family 2 = cl_mersenne_presentation 2.
Proof. reflexivity. Qed.

(** Same form, two families: restricted low-order fires on the
    ordinary sampler and is excluded on the Mersenne sampler. *)

Theorem cl_AR_C_broken_when_two_in_C :
  forall C,
    C 2%nat ->
    P_AdaptiveRoot_C (cl_presentation (-31)) C
      form_neg31_sq form_neg31_ord3 2%nat.
Proof.
  intros C HC.
  unfold P_AdaptiveRoot_C, cl_presentation, cl_presentation_H.
  cbn [Peq Pexp Pid].
  split; [exact HC|].
  split; [lia|].
  split; [apply form_neg31_sq_not_principal|].
  rewrite form_neg31_exp2.
  apply bqf_equiv_refl.
Qed.

(** ** Sentence 3 — adaptive root is trivial from public data on RSA
    with the trapdoor, and is not on [Cl(Δ)] *)

Theorem rsa_trapdoor_annihilator_is_lambda :
  forall N lam, Pannihilator (rsa_trapdoor_presentation N lam) = Some lam.
Proof. reflexivity. Qed.

Theorem rsa_lambda_solves_adaptive_root :
  forall p q y,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime y (p * q) ->
    let N := p * q in
    let lam := lambda_semiprime p q in
    Problem_AdaptiveRoot N (y mod N) (y mod N) (lam + 1).
Proof. apply adaptive_root_trivial_from_lambda. Qed.

Theorem cl_has_no_lambda_plus_one :
  forall D, iq_disc D -> Pannihilator (cl_presentation D) <> Some (D + 1).
Proof.
  intros D [Hneg _] Hc.
  unfold cl_presentation in Hc. simpl in Hc. injection Hc. lia.
Qed.

(** ** Week 8 — same mechanics, no modulus

    [Problem_Order] and [Problem_AdaptiveRoot] on forms are
    [P_Order] / [P_AdaptiveRoot] at [cl_presentation].  One-sided
    low-order / CRT splitting has no analogue: there is no pair of
    rings whose idempotents are factors of a public [N]. *)

Definition Problem_Order_Cl (D : Z) (f : bqf) (k : nat) : Prop :=
  of_disc f D /\ P_Order (cl_presentation D) f k.

Definition Problem_AdaptiveRoot_Cl (D : Z) (y x : bqf) (e : nat) : Prop :=
  of_disc y D /\ of_disc x D /\ P_AdaptiveRoot (cl_presentation D) y x e.

Theorem no_crt_split_from_disc :
  forall D, iq_disc D -> ~ exists (N : Z), N = D /\ 1 < N.
Proof.
  intros D [Hneg _] [N [HN Hgt]]. subst N. lia.
Qed.

Theorem cl_exp_0_is_id :
  forall D f, Pexp (cl_presentation D) f 0%nat = bqf_id D.
Proof. intros. reflexivity. Qed.

Theorem cl_exp_1_is_f :
  forall D f,
    iq_disc D ->
    of_disc f D ->
    Pexp (cl_presentation D) f 1%nat = f.
Proof. intros. apply bqf_exp_1; assumption. Qed.

Theorem cl_inv_is_bqf_inv :
  forall D f, Pinv (cl_presentation D) f = bqf_inv f.
Proof. intros. reflexivity. Qed.

Theorem cl_mul_inv_equiv_id :
  forall D f,
    iq_disc D ->
    of_disc f D ->
    Peq (cl_presentation D)
      (Pmul (cl_presentation D) f (Pinv (cl_presentation D) f))
      (Pid (cl_presentation D)).
Proof.
  intros D f Hiq Hof.
  unfold cl_presentation. simpl.
  apply compose_inv_equiv_id; assumption.
Qed.

(** A unit has an inverse in [(Z/NZ)*] (Bezout).  The public
    [rsa_presentation] does not package a constructive [Pinv]
    (extended gcd is not in this file); the trapdoor presentation
    inverts by [a^{λ−1}]. *)
Theorem unit_inverse_exists :
  forall a n,
    1 < n ->
    Z.gcd a n = 1 ->
    exists w, (a * w) mod n = 1.
Proof.
  intros a n Hn Hg.
  apply Z.Bezout_coprime_iff in Hg.
  destruct Hg as [u [v Huv]].
  exists u.
  rewrite (Z.mul_comm a u).
  replace (u * a) with (1 + (- v) * n) by lia.
  rewrite Z.mod_add by lia.
  apply Z.mod_1_l. lia.
Qed.

Theorem rsa_trapdoor_inv_is_root :
  forall p q a,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime a (p * q) ->
    let N := p * q in
    let lam := lambda_semiprime p q in
    (a * powm a (lam - 1) N) mod N = 1.
Proof.
  intros p q a Hp Hq Hneq Hcop N lam.
  subst N lam.
  pose proof (lambda_semiprime_pos p q Hp Hq) as Hpos.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  unfold powm.
  rewrite Z.mul_mod_idemp_r by nia.
  rewrite <- Z.pow_succ_r by lia.
  replace (Z.succ (lambda_semiprime p q - 1))
    with (lambda_semiprime p q) by lia.
  fold (powm a (lambda_semiprime p q) (p * q)).
  rewrite carmichael_semiprime by assumption.
  reflexivity.
Qed.

Theorem Pexp_0 :
  forall N a, 1 < N -> Pexp (rsa_presentation N) a 0%nat = 1 mod N.
Proof.
  intros N a Hn. unfold rsa_presentation. simpl.
  apply powm_0_r. lia.
Qed.

Theorem Pexp_S_rsa :
  forall N a k,
    1 < N ->
    0 <= a ->
    Pexp (rsa_presentation N) a (S k) =
      (a * Pexp (rsa_presentation N) a k) mod N.
Proof.
  intros N a k Hn Ha.
  unfold rsa_presentation, Pexp. cbn [Pexp].
  unfold powm.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  rewrite Z.mul_mod_idemp_r by lia. reflexivity.
Qed.
