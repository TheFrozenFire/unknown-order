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

    Problems are the same winning conditions as [UnknownOrder],
    stated once.  Sentences 1–3 of the roadmap instantiate on
    both carriers. *)

Record Presentation : Type := {
  Pcar : Type;
  Peq : Pcar -> Pcar -> Prop;
  Pmul : Pcar -> Pcar -> Pcar;
  Pid : Pcar;
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

(** ** RSA, public view: no annihilator, constructible torsion is [±1] *)

Definition rsa_presentation (N : Z) : Presentation := {|
  Pcar := Z;
  Peq := fun x y => x mod N = y mod N;
  Pmul := fun x y => (x * y) mod N;
  Pid := 1;
  Pexp := fun a k => powm a (Z.of_nat k) N;
  Pconstructible := fun a => rsa_constructible_2torsion N a;
  Pannihilator := None
|}.

Definition rsa_trapdoor_presentation (N lam : Z) : Presentation := {|
  Pcar := Z;
  Peq := fun x y => x mod N = y mod N;
  Pmul := fun x y => (x * y) mod N;
  Pid := 1;
  Pexp := fun a k => powm a (Z.of_nat k) N;
  Pconstructible := fun a => rsa_constructible_2torsion N a;
  Pannihilator := Some lam
|}.

(** ** [Cl(Δ)]: public 2-annihilator, constructible torsion is ambiguous forms *)

Definition cl_presentation (D : Z) : Presentation := {|
  Pcar := bqf;
  Peq := bqf_equiv;
  Pmul := bqf_compose;
  Pid := bqf_id D;
  Pexp := bqf_exp D;
  Pconstructible := bqf_ambiguous;
  Pannihilator := Some 2
|}.

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
