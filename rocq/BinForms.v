From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * Primitive binary quadratic forms of discriminant [Δ]

    The carrier of [Cl(Δ)] for [Δ < 0].  Identity, inverse, SL2
    equivalence, and Dirichlet composition (exact on the identity;
    [a = 1] after composing with the inverse).  Ambiguous forms are
    public order-2 classes, constructed from a divisor of [Δ].
    Cross-confirmed by [cas/23_class_group.gp]. *)

Record bqf : Type := {
  bqf_a : Z;
  bqf_b : Z;
  bqf_c : Z
}.

Definition bqf_disc (f : bqf) : Z :=
  bqf_b f * bqf_b f - 4 * bqf_a f * bqf_c f.

Definition bqf_primitive (f : bqf) : Prop :=
  Z.gcd (Z.gcd (bqf_a f) (bqf_b f)) (bqf_c f) = 1.

Definition iq_disc (D : Z) : Prop :=
  D < 0 /\ (D mod 4 = 0 \/ D mod 4 = 1).

Definition of_disc (f : bqf) (D : Z) : Prop :=
  bqf_disc f = D /\ bqf_primitive f.

(** Principal form of discriminant [D]. *)
Definition bqf_id (D : Z) : bqf :=
  if D mod 4 =? 0
  then {| bqf_a := 1; bqf_b := 0; bqf_c := -(D / 4) |}
  else {| bqf_a := 1; bqf_b := 1; bqf_c := (1 - D) / 4 |}.

Definition bqf_inv (f : bqf) : bqf :=
  {| bqf_a := bqf_a f; bqf_b := - bqf_b f; bqf_c := bqf_c f |}.

Lemma bqf_inv_disc :
  forall f, bqf_disc (bqf_inv f) = bqf_disc f.
Proof. intros f. unfold bqf_disc, bqf_inv. simpl. ring. Qed.

Lemma bqf_inv_primitive :
  forall f, bqf_primitive f -> bqf_primitive (bqf_inv f).
Proof.
  intros f. unfold bqf_primitive, bqf_inv. simpl.
  rewrite (Z.gcd_opp_r (bqf_a f) (bqf_b f)).
  intros H. exact H.
Qed.

Lemma bqf_inv_inv :
  forall f, bqf_inv (bqf_inv f) = f.
Proof.
  intros [a b c]. unfold bqf_inv. simpl.
  rewrite Z.opp_involutive. reflexivity.
Qed.

Lemma bqf_id_a :
  forall D, bqf_a (bqf_id D) = 1.
Proof.
  intros D. unfold bqf_id. destruct (D mod 4 =? 0); reflexivity.
Qed.

Lemma four_times_div4 :
  forall n, n mod 4 = 0 -> n / 4 * 4 = n.
Proof.
  intros n H.
  pose proof (Z.div_mod n 4 ltac:(lia)) as Hdm.
  rewrite H, Z.add_0_r in Hdm.
  rewrite Z.mul_comm. lia.
Qed.

Lemma one_minus_D_mod4 :
  forall D, D mod 4 = 1 -> (1 - D) mod 4 = 0.
Proof.
  intros D H1.
  replace (1 - D) with (1 + - D) by ring.
  rewrite Z.add_mod by lia.
  rewrite Z.mod_1_l by lia.
  rewrite Z.mod_opp_l_nz; [| lia | rewrite H1; lia].
  rewrite H1. reflexivity.
Qed.

Theorem bqf_id_disc :
  forall D, iq_disc D -> bqf_disc (bqf_id D) = D.
Proof.
  intros D [Hneg Hcong].
  unfold bqf_id, bqf_disc.
  destruct (Z.eqb_spec (D mod 4) 0) as [H0 | Hne].
  - cbn [bqf_a bqf_b bqf_c].
    rewrite Z.mul_0_l, Z.sub_0_l, Z.mul_1_r, Z.mul_opp_r, Z.opp_involutive.
    rewrite Z.mul_comm. apply four_times_div4. exact H0.
  - destruct Hcong as [Hc | H1]; [congruence|].
    cbn [bqf_a bqf_b bqf_c].
    rewrite Z.mul_1_l, Z.mul_1_r.
    pose proof (one_minus_D_mod4 D H1) as Hm.
    rewrite (Z.mul_comm 4 ((1 - D) / 4)).
    rewrite (four_times_div4 (1 - D) Hm).
    ring.
Qed.

Lemma bqf_id_primitive :
  forall D, bqf_primitive (bqf_id D).
Proof.
  intros D. unfold bqf_primitive, bqf_id, bqf_a, bqf_b, bqf_c.
  destruct (D mod 4 =? 0); rewrite !Z.gcd_1_l; reflexivity.
Qed.

Theorem bqf_id_of_disc :
  forall D, iq_disc D -> of_disc (bqf_id D) D.
Proof. intros D H. split; [apply bqf_id_disc; exact H | apply bqf_id_primitive]. Qed.

Theorem bqf_id_disc_neg4 : bqf_disc (bqf_id (-4)) = -4.
Proof. apply bqf_id_disc. unfold iq_disc. split; [lia|]. left. vm_compute. reflexivity. Qed.

Theorem bqf_id_disc_neg47 : bqf_disc (bqf_id (-47)) = -47.
Proof. apply bqf_id_disc. unfold iq_disc. split; [lia|]. right. vm_compute. reflexivity. Qed.

Theorem bqf_id_disc_neg23 : bqf_disc (bqf_id (-23)) = -23.
Proof. apply bqf_id_disc. unfold iq_disc. split; [lia|]. right. vm_compute. reflexivity. Qed.

Theorem bqf_id_of_disc_neg47 :
  of_disc (bqf_id (-47)) (-47).
Proof. apply bqf_id_of_disc. unfold iq_disc. split; [lia|]. right. vm_compute. reflexivity. Qed.

Lemma of_disc_a_nz :
  forall f D, of_disc f D -> D < 0 -> bqf_a f <> 0.
Proof.
  intros f D [Hdisc _] HD Ha.
  unfold bqf_disc in Hdisc. rewrite Ha in Hdisc.
  assert (0 <= bqf_b f * bqf_b f) by nia.
  nia.
Qed.

(** Reduced (Gauss): [|b| ≤ a ≤ c], and [b ≥ 0] if either equality holds. *)
Definition bqf_reduced (f : bqf) : Prop :=
  Z.abs (bqf_b f) <= bqf_a f <= bqf_c f /\
  (bqf_b f < 0 -> bqf_a f <> Z.abs (bqf_b f) /\ bqf_a f <> bqf_c f).

(** Ambiguous forms (order dividing 2 on the class): [b = 0],
    [a = ±b], or [a = c].  The last is the reduced shape of some
    classes that start life as [a = ±b]. *)
Definition bqf_ambiguous (f : bqf) : Prop :=
  bqf_b f = 0 \/ bqf_a f = bqf_b f \/ bqf_a f = - bqf_b f \/
  bqf_a f = bqf_c f.

Lemma bqf_id_ambiguous_mod0 :
  forall D, D mod 4 = 0 -> bqf_ambiguous (bqf_id D).
Proof.
  intros D Hm. unfold bqf_ambiguous, bqf_id. rewrite Hm. simpl. now left.
Qed.

Theorem disc_neg47 :
  iq_disc (-47) /\ bqf_disc (bqf_id (-47)) = -47.
Proof.
  split.
  - unfold iq_disc. split; [lia|]. right. vm_compute. reflexivity.
  - apply bqf_id_disc_neg47.
Qed.

(** ** SL2 action and proper equivalence *)

Record sl2 : Type := {
  sl2_a : Z;
  sl2_b : Z;
  sl2_c : Z;
  sl2_d : Z
}.

Definition sl2_det (m : sl2) : Z :=
  sl2_a m * sl2_d m - sl2_b m * sl2_c m.

Definition sl2_ok (m : sl2) : Prop := sl2_det m = 1.

Definition bqf_act (m : sl2) (f : bqf) : bqf :=
  let α := sl2_a m in
  let β := sl2_b m in
  let γ := sl2_c m in
  let δ := sl2_d m in
  let a := bqf_a f in
  let b := bqf_b f in
  let c := bqf_c f in
  {| bqf_a := a * α * α + b * α * γ + c * γ * γ;
     bqf_b := 2 * a * α * β + b * (α * δ + β * γ) + 2 * c * γ * δ;
     bqf_c := a * β * β + b * β * δ + c * δ * δ |}.

Definition bqf_equiv (f g : bqf) : Prop :=
  exists m, sl2_ok m /\ bqf_act m f = g.

Definition sl2_I : sl2 :=
  {| sl2_a := 1; sl2_b := 0; sl2_c := 0; sl2_d := 1 |}.

Definition sl2_T (k : Z) : sl2 :=
  {| sl2_a := 1; sl2_b := k; sl2_c := 0; sl2_d := 1 |}.

Definition sl2_S : sl2 :=
  {| sl2_a := 0; sl2_b := -1; sl2_c := 1; sl2_d := 0 |}.

Lemma sl2_I_ok : sl2_ok sl2_I.
Proof. unfold sl2_ok, sl2_I, sl2_det. cbn [sl2_a sl2_b sl2_c sl2_d]. ring. Qed.

Lemma sl2_T_ok : forall k, sl2_ok (sl2_T k).
Proof. intros k. unfold sl2_ok, sl2_T, sl2_det. cbn [sl2_a sl2_b sl2_c sl2_d]. ring. Qed.

Lemma sl2_S_ok : sl2_ok sl2_S.
Proof. unfold sl2_ok, sl2_S, sl2_det. cbn [sl2_a sl2_b sl2_c sl2_d]. ring. Qed.

Lemma bqf_act_I :
  forall f, bqf_act sl2_I f = f.
Proof.
  intros [a b c]. unfold bqf_act, sl2_I. cbn [sl2_a sl2_b sl2_c sl2_d bqf_a bqf_b bqf_c].
  f_equal; ring.
Qed.

Lemma bqf_equiv_refl : forall f, bqf_equiv f f.
Proof. intros f. exists sl2_I. split; [apply sl2_I_ok | apply bqf_act_I]. Qed.

Definition sl2_mul (m n : sl2) : sl2 :=
  {| sl2_a := sl2_a m * sl2_a n + sl2_b m * sl2_c n;
     sl2_b := sl2_a m * sl2_b n + sl2_b m * sl2_d n;
     sl2_c := sl2_c m * sl2_a n + sl2_d m * sl2_c n;
     sl2_d := sl2_c m * sl2_b n + sl2_d m * sl2_d n |}.

Definition sl2_inverse (m : sl2) : sl2 :=
  {| sl2_a := sl2_d m;
     sl2_b := - sl2_b m;
     sl2_c := - sl2_c m;
     sl2_d := sl2_a m |}.

Lemma sl2_mul_det :
  forall m n, sl2_det (sl2_mul m n) = sl2_det m * sl2_det n.
Proof.
  intros [a b c d] [a' b' c' d'].
  unfold sl2_mul, sl2_det.
  cbn [sl2_a sl2_b sl2_c sl2_d]. ring.
Qed.

Lemma sl2_mul_ok :
  forall m n, sl2_ok m -> sl2_ok n -> sl2_ok (sl2_mul m n).
Proof.
  intros m n Hm Hn. unfold sl2_ok. rewrite sl2_mul_det, Hm, Hn. ring.
Qed.

Lemma sl2_inverse_ok :
  forall m, sl2_ok m -> sl2_ok (sl2_inverse m).
Proof.
  intros m H. unfold sl2_ok in *.
  replace (sl2_det (sl2_inverse m)) with (sl2_det m).
  { exact H. }
  destruct m as [a b c d].
  unfold sl2_inverse, sl2_det.
  cbn [sl2_a sl2_b sl2_c sl2_d].
  ring.
Qed.

Lemma bqf_act_mul :
  forall m n f,
    bqf_act m (bqf_act n f) = bqf_act (sl2_mul n m) f.
Proof.
  intros [a b c d] [a' b' c' d'] [A B C].
  unfold bqf_act, sl2_mul.
  cbn [sl2_a sl2_b sl2_c sl2_d bqf_a bqf_b bqf_c].
  f_equal; ring.
Qed.

Theorem bqf_equiv_trans :
  forall f g h,
    bqf_equiv f g -> bqf_equiv g h -> bqf_equiv f h.
Proof.
  intros f g h [m [Hm Hfm]] [n [Hn Hgn]].
  exists (sl2_mul m n). split; [apply sl2_mul_ok; assumption|].
  rewrite <- Hgn, <- Hfm, bqf_act_mul. reflexivity.
Qed.

Lemma bqf_act_disc :
  forall m f,
    bqf_disc (bqf_act m f) = bqf_disc f * sl2_det m * sl2_det m.
Proof.
  intros [α β γ δ] [a b c].
  unfold bqf_act, bqf_disc, sl2_det.
  cbn [sl2_a sl2_b sl2_c sl2_d bqf_a bqf_b bqf_c]. ring.
Qed.

Lemma bqf_act_disc_sl2 :
  forall m f, sl2_ok m -> bqf_disc (bqf_act m f) = bqf_disc f.
Proof.
  intros m f Hok. rewrite bqf_act_disc, Hok. ring.
Qed.

Lemma bqf_act_T :
  forall k f,
    bqf_act (sl2_T k) f =
    {| bqf_a := bqf_a f;
       bqf_b := bqf_b f + 2 * k * bqf_a f;
       bqf_c := bqf_c f + k * bqf_b f + k * k * bqf_a f |}.
Proof.
  intros k [a b c]. unfold bqf_act, sl2_T.
  cbn [sl2_a sl2_b sl2_c sl2_d bqf_a bqf_b bqf_c]. f_equal; ring.
Qed.

Lemma bqf_act_S :
  forall f,
    bqf_act sl2_S f =
    {| bqf_a := bqf_c f; bqf_b := - bqf_b f; bqf_c := bqf_a f |}.
Proof.
  intros [a b c]. unfold bqf_act, sl2_S.
  cbn [sl2_a sl2_b sl2_c sl2_d bqf_a bqf_b bqf_c]. f_equal; ring.
Qed.

(** An ambiguous form is properly equivalent to its inverse, so its
    class has order dividing 2. *)
Theorem ambiguous_equiv_inv :
  forall f, bqf_ambiguous f -> bqf_equiv f (bqf_inv f).
Proof.
  intros [a b c] [Hb0 | [Hab | [Hanb | Hac]]]; cbn in *.
  - exists sl2_I. split; [apply sl2_I_ok|].
    rewrite bqf_act_I. unfold bqf_inv. cbn [bqf_a bqf_b bqf_c].
    rewrite Hb0, Z.opp_0. reflexivity.
  - exists (sl2_T (-1)). split; [apply sl2_T_ok|].
    rewrite bqf_act_T. unfold bqf_inv. cbn [bqf_a bqf_b bqf_c].
    subst b. f_equal; ring.
  - exists (sl2_T 1). split; [apply sl2_T_ok|].
    rewrite bqf_act_T. unfold bqf_inv. cbn [bqf_a bqf_b bqf_c].
    subst a. f_equal; ring.
  - exists sl2_S. split; [apply sl2_S_ok|].
    rewrite bqf_act_S. unfold bqf_inv. cbn [bqf_a bqf_b bqf_c].
    subst c. reflexivity.
Qed.

(** ** Represented values: a reduced form with [a > 1] is not principal *)

Definition bqf_eval (f : bqf) (x y : Z) : Z :=
  bqf_a f * x * x + bqf_b f * x * y + bqf_c f * y * y.

Lemma bqf_act_eval :
  forall m f x y,
    bqf_eval (bqf_act m f) x y =
    bqf_eval f (sl2_a m * x + sl2_b m * y) (sl2_c m * x + sl2_d m * y).
Proof.
  intros [α β γ δ] [a b c] x y.
  unfold bqf_eval, bqf_act.
  cbn [sl2_a sl2_b sl2_c sl2_d bqf_a bqf_b bqf_c]. ring.
Qed.

Lemma bqf_id_eval_1 :
  forall D, bqf_eval (bqf_id D) 1 0 = 1.
Proof.
  intros D. unfold bqf_eval, bqf_id.
  destruct (D mod 4 =? 0); cbn [bqf_a bqf_b bqf_c]; ring.
Qed.

Lemma z_le_abs : forall n, n <= Z.abs n.
Proof. intros n. destruct (Z.abs_spec n) as [[_ ?]|[_ ?]]; lia. Qed.

Lemma reduced_eval_ge_a :
  forall f x y,
    bqf_reduced f ->
    0 < bqf_a f ->
    ~ (x = 0 /\ y = 0) ->
    bqf_a f <= bqf_eval f x y.
Proof.
  intros f x y [[Hba Hac] _] Ha Hnz.
  destruct (Z.eq_dec y 0) as [Hy | Hy].
  - subst y.
    assert (x <> 0) by (intro Hx; apply Hnz; split; [exact Hx | reflexivity]).
    assert (bqf_eval f x 0 = bqf_a f * (x * x)) as He by (unfold bqf_eval; ring).
    rewrite He. assert (1 <= x * x) by nia. nia.
  - destruct (Z.eq_dec x 0) as [Hx | Hx].
    + subst x.
      assert (bqf_eval f 0 y = bqf_c f * (y * y)) as He by (unfold bqf_eval; ring).
      rewrite He. assert (1 <= y * y) by nia. nia.
    + assert (bqf_eval f x y =
                bqf_a f * (x * x) + bqf_b f * (x * y) + bqf_c f * (y * y)) as Hev
        by (unfold bqf_eval; ring).
      rewrite Hev.
      rewrite <- (Z.abs_square x), <- (Z.abs_square y).
      assert (bqf_b f * (x * y) >= - Z.abs (bqf_b f * (x * y)))
        by (pose proof (z_le_abs (bqf_b f * (x * y))); lia).
      rewrite Z.abs_mul, Z.abs_mul in H.
      assert (1 <= Z.abs x) by nia.
      assert (1 <= Z.abs y) by nia.
      set (A := bqf_a f) in *.
      set (C := bqf_c f) in *.
      set (X := Z.abs x) in *.
      set (Y := Z.abs y) in *.
      set (Babs := Z.abs (bqf_b f)) in *.
      assert (Babs <= A) by exact Hba.
      assert (A <= C) by exact Hac.
      assert (X * X - X * Y + Y * Y = (X - Y) * (X - Y) + X * Y) by ring.
      assert (1 <= X * X - X * Y + Y * Y) by nia.
      nia.
Qed.

Theorem reduced_a_gt_1_not_principal :
  forall f D,
    of_disc f D ->
    bqf_reduced f ->
    1 < bqf_a f ->
    ~ bqf_equiv f (bqf_id D).
Proof.
  intros f D Hof Hred Ha [m [Hok Hact]].
  assert (0 < bqf_a f) by lia.
  assert (~ (sl2_a m = 0 /\ sl2_c m = 0)) as Hnz.
  { intros [H1 H2]. unfold sl2_ok, sl2_det in Hok. rewrite H1, H2 in Hok. lia. }
  assert (bqf_eval f (sl2_a m) (sl2_c m) = 1) as Hev.
  { pose proof (bqf_act_eval m f 1 0) as Hv.
    rewrite Hact, bqf_id_eval_1 in Hv.
    rewrite !Z.mul_1_r, !Z.mul_0_r, !Z.add_0_r in Hv.
    symmetry. exact Hv. }
  pose proof (reduced_eval_ge_a f (sl2_a m) (sl2_c m) Hred H Hnz) as Hge.
  rewrite Hev in Hge. lia.
Qed.

(** ** Dirichlet composition

    Special-cased on a unit leading coefficient so [id ∘ f = f]
    holds on representatives, not just classes.  The general branch
    is the Bézout formula; [f ∘ f⁻¹] has leading coefficient 1 and
    is therefore equivalent to the identity. *)

Definition bqf_comp_gcd (f g : bqf) : Z :=
  Z.gcd (Z.gcd (bqf_a f) (bqf_a g)) ((bqf_b f + bqf_b g) / 2).

Definition solve_cong (a m target : Z) : Z :=
  let '(d, (u, _)) := Z.ggcd a m in
  u * (target / d).

Definition dirichlet_B (f g : bqf) : Z :=
  if Z.abs (bqf_a f) =? 1 then bqf_b g
  else
    let n := bqf_comp_gcd f g in
    let a1' := bqf_a f / n in
    let a2' := bqf_a g / n in
    bqf_b f + 2 * a1' * solve_cong a1' a2' ((bqf_b g - bqf_b f) / 2).

Definition bqf_compose (f g : bqf) : bqf :=
  let n := bqf_comp_gcd f g in
  let aa := (bqf_a f * bqf_a g) / (n * n) in
  let B := dirichlet_B f g in
  {| bqf_a := aa;
     bqf_b := B;
     bqf_c := (B * B - bqf_disc f) / (4 * aa) |}.

Lemma compose_gcd_id_l :
  forall D f, bqf_comp_gcd (bqf_id D) f = 1.
Proof.
  intros D f. unfold bqf_comp_gcd. rewrite bqf_id_a, Z.gcd_1_l, Z.gcd_1_l.
  reflexivity.
Qed.

Lemma dirichlet_B_id_l :
  forall D f, dirichlet_B (bqf_id D) f = bqf_b f.
Proof.
  intros D f. unfold dirichlet_B. rewrite bqf_id_a.
  change (Z.abs 1) with 1. reflexivity.
Qed.

Theorem compose_id_left :
  forall D f,
    iq_disc D ->
    of_disc f D ->
    bqf_compose (bqf_id D) f = f.
Proof.
  intros D f Hiq Hof.
  pose proof (of_disc_a_nz f D Hof (proj1 Hiq)) as Ha_nz.
  pose proof (bqf_id_disc D Hiq) as HidD.
  destruct Hof as [Hdisc _].
  unfold bqf_compose.
  rewrite compose_gcd_id_l, dirichlet_B_id_l, bqf_id_a.
  rewrite Z.mul_1_l, Z.mul_1_l, Z.div_1_r.
  rewrite HidD.
  destruct f as [a b c].
  cbn [bqf_a bqf_b bqf_c] in *.
  unfold bqf_disc in Hdisc.
  cbn [bqf_a bqf_b bqf_c] in Hdisc.
  rewrite <- Hdisc.
  replace (b * b - (b * b - 4 * a * c)) with (4 * a * c) by ring.
  assert (4 * a <> 0) as H4a by nia.
  rewrite (Z.mul_comm (4 * a) c).
  rewrite (Z.div_mul c (4 * a) H4a).
  reflexivity.
Qed.

Lemma compose_inv_gcd :
  forall f, bqf_comp_gcd f (bqf_inv f) = Z.abs (bqf_a f).
Proof.
  intros [a b c]. unfold bqf_comp_gcd, bqf_inv. simpl.
  rewrite Z.add_opp_r, Z.sub_diag, Z.div_0_l by lia.
  rewrite Z.gcd_diag, Z.gcd_0_r, Z.abs_idemp. reflexivity.
Qed.

Theorem compose_inv_leading_one :
  forall f, bqf_a f <> 0 -> bqf_a (bqf_compose f (bqf_inv f)) = 1.
Proof.
  intros f Ha.
  unfold bqf_compose. rewrite compose_inv_gcd. simpl.
  destruct f as [a b c]. simpl in *.
  rewrite Z.abs_square.
  apply Z.div_same. nia.
Qed.

Lemma dirichlet_B_inv_plus_2 :
  forall f, exists k, dirichlet_B f (bqf_inv f) = bqf_b f + 2 * k.
Proof.
  intros f. unfold dirichlet_B.
  destruct (Z.eqb_spec (Z.abs (bqf_a f)) 1) as [_ | _].
  - exists (- bqf_b f). unfold bqf_inv. cbn [bqf_a bqf_b bqf_c]. ring.
  - set (n := bqf_comp_gcd f (bqf_inv f)).
    exists ((bqf_a f / n) *
            solve_cong (bqf_a f / n) (bqf_a (bqf_inv f) / n)
              ((bqf_b (bqf_inv f) - bqf_b f) / 2)).
    ring.
Qed.

Lemma four_divides_B2_minus_disc_inv :
  forall f,
    (4 | dirichlet_B f (bqf_inv f) * dirichlet_B f (bqf_inv f) - bqf_disc f).
Proof.
  intros f.
  destruct (dirichlet_B_inv_plus_2 f) as [k Hk].
  rewrite Hk. unfold bqf_disc.
  exists (k * bqf_b f + k * k + bqf_a f * bqf_c f). ring.
Qed.

Lemma reconstruct_disc_div4 :
  forall B D, (4 | B * B - D) -> B * B - 4 * ((B * B - D) / 4) = D.
Proof.
  intros B D [k Hk]. rewrite Hk.
  rewrite Z.div_mul by lia. lia.
Qed.

Lemma compose_inv_c :
  forall f,
    bqf_a f <> 0 ->
    bqf_c (bqf_compose f (bqf_inv f)) =
      (dirichlet_B f (bqf_inv f) * dirichlet_B f (bqf_inv f) - bqf_disc f) / 4.
Proof.
  intros f Ha.
  unfold bqf_compose. rewrite compose_inv_gcd.
  destruct f as [a b c]. cbn [bqf_a bqf_b bqf_c] in *.
  rewrite Z.abs_square, Z.div_same by nia.
  rewrite Z.mul_1_r. reflexivity.
Qed.

Lemma compose_inv_primitive :
  forall f,
    bqf_a f <> 0 ->
    bqf_primitive (bqf_compose f (bqf_inv f)).
Proof.
  intros f Ha.
  unfold bqf_primitive.
  rewrite compose_inv_leading_one by exact Ha.
  rewrite Z.gcd_1_l. apply Z.gcd_1_l.
Qed.

Theorem compose_inv_of_disc :
  forall f D,
    iq_disc D ->
    of_disc f D ->
    of_disc (bqf_compose f (bqf_inv f)) D.
Proof.
  intros f D Hiq Hof.
  pose proof (of_disc_a_nz f D Hof (proj1 Hiq)) as Ha.
  destruct Hof as [Hdisc _].
  split.
  - unfold bqf_disc.
    rewrite compose_inv_leading_one by exact Ha.
    rewrite compose_inv_c by exact Ha.
    rewrite Hdisc.
    apply reconstruct_disc_div4.
    rewrite <- Hdisc. apply four_divides_B2_minus_disc_inv.
  - apply compose_inv_primitive. exact Ha.
Qed.

(** A form of leading coefficient 1 is a translate of the identity. *)
Theorem form_a_one_equiv_id :
  forall f D,
    iq_disc D ->
    of_disc f D ->
    bqf_a f = 1 ->
    bqf_equiv f (bqf_id D).
Proof.
  intros f D Hiq [Hdisc _] Ha.
  unfold bqf_disc in Hdisc.
  destruct f as [af bf cf].
  cbn [bqf_a bqf_b bqf_c] in *.
  subst af.
  assert (4 * cf = bf * bf - D) as H4c by lia.
  destruct Hiq as [Hneg Hcong].
  destruct (Z.eqb_spec (D mod 4) 0) as [H0 | Hne].
  - assert (Z.Even bf) as Heven.
    { destruct (Z.Even_or_Odd bf) as [He | Ho]; [exact He|].
      destruct Ho as [t Ht].
      assert ((bf * bf) mod 4 = 1) as Hodd2.
      { rewrite Ht.
        replace ((2 * t + 1) * (2 * t + 1)) with (4 * (t * t + t) + 1) by ring.
        rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full, Z.mod_1_l by lia.
        reflexivity. }
      assert ((bf * bf) mod 4 = 0) as Heven2.
      { replace (bf * bf) with (D + 4 * cf) by lia.
        rewrite Z.add_mod, H0, (Z.mul_comm 4 cf), Z.mod_mul, Z.add_0_r, Z.mod_0_l by lia.
        reflexivity. }
      lia. }
    destruct Heven as [k Hk].
    exists (sl2_T (-k)). split; [apply sl2_T_ok|].
    rewrite bqf_act_T. cbn [bqf_a bqf_b bqf_c].
    unfold bqf_id. rewrite H0.
    change (0 =? 0) with true. cbn [bqf_a bqf_b bqf_c].
    subst bf.
    assert (2 * k + 2 * - k * 1 = 0) as Hb0 by ring.
    assert (cf + - k * (2 * k) + - k * - k * 1 = cf - k * k) as Hc0 by ring.
    rewrite Hb0, Hc0.
    assert (4 * (cf - k * k) = - D) as H4.
    { replace (4 * (cf - k * k)) with (4 * cf - 4 * (k * k)) by ring.
      rewrite H4c. ring. }
    assert (4 * (D / 4) = D) as Hd4.
    { rewrite Z.mul_comm. apply four_times_div4. exact H0. }
    f_equal.
    apply (Z.mul_reg_l _ _ 4); [lia|].
    rewrite H4, Z.mul_opp_r, Hd4. reflexivity.
  - destruct Hcong as [Hc | H1]; [congruence|].
    assert (Z.Odd bf) as Hodd.
    { destruct (Z.Even_or_Odd bf) as [He | Ho]; [|exact Ho].
      destruct He as [t Ht].
      assert ((bf * bf) mod 4 = 0) as He2.
      { rewrite Ht.
        replace ((2 * t) * (2 * t)) with (4 * (t * t)) by ring.
        rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
      assert ((bf * bf) mod 4 = 1) as Ho2.
      { replace (bf * bf) with (D + 4 * cf) by lia.
        rewrite Z.add_mod, H1, (Z.mul_comm 4 cf), Z.mod_mul, Z.add_0_r, Z.mod_1_l by lia.
        reflexivity. }
      lia. }
    destruct Hodd as [k Hk].
    exists (sl2_T (-k)). split; [apply sl2_T_ok|].
    rewrite bqf_act_T. cbn [bqf_a bqf_b bqf_c].
    unfold bqf_id.
    destruct (Z.eqb_spec (D mod 4) 0) as [H00 | _]; [congruence|].
    cbn [bqf_a bqf_b bqf_c]. subst bf.
    assert (2 * k + 1 + 2 * - k * 1 = 1) as Hb1 by ring.
    assert (cf + - k * (2 * k + 1) + - k * - k * 1 = cf - k * k - k) as Hc1 by ring.
    rewrite Hb1, Hc1.
    assert (4 * (cf - k * k - k) = 1 - D) as H4.
    { replace (4 * (cf - k * k - k)) with (4 * cf - 4 * (k * k) - 4 * k) by ring.
      rewrite H4c. ring. }
    assert (4 * ((1 - D) / 4) = 1 - D) as Hd4.
    { rewrite Z.mul_comm. apply four_times_div4. apply one_minus_D_mod4. exact H1. }
    f_equal.
    apply (Z.mul_reg_l _ _ 4); [lia|].
    rewrite H4. symmetry. exact Hd4.
Qed.

Theorem compose_inv_equiv_id :
  forall f D,
    iq_disc D ->
    of_disc f D ->
    bqf_equiv (bqf_compose f (bqf_inv f)) (bqf_id D).
Proof.
  intros f D Hiq Hof.
  apply form_a_one_equiv_id; [exact Hiq | apply compose_inv_of_disc; assumption |].
  apply compose_inv_leading_one.
  apply (of_disc_a_nz f D Hof (proj1 Hiq)).
Qed.

(** Inverse composition preserves the discriminant as a theorem.
    Two-form Dirichlet when a leading coefficient is a unit is
    [compose_id_left].  Self-composition of a construction-side
    ambiguous form ([b = 0] or [a = ±b]) has leading coefficient 1
    and is therefore principal.  The remaining two-form branch
    (neither leading coefficient a unit, not an inverse pair) is
    [compose_preserves_disc_named]. *)
Definition compose_preserves_disc_named (f g : bqf) : Prop :=
  bqf_disc (bqf_compose f g) = bqf_disc f /\
  bqf_primitive (bqf_compose f g).

Definition bqf_ambiguous_div (f : bqf) : Prop :=
  bqf_b f = 0 \/ bqf_a f = bqf_b f \/ bqf_a f = - bqf_b f.

Lemma ambiguous_div_is_ambiguous :
  forall f, bqf_ambiguous_div f -> bqf_ambiguous f.
Proof. intros f [H|[H|H]]; unfold bqf_ambiguous; auto. Qed.

Lemma solve_cong_target_0 :
  forall a m, solve_cong a m 0 = 0.
Proof.
  intros a m. unfold solve_cong.
  destruct (Z.ggcd a m) as [d [u _]].
  assert (0 / d = 0) as Hz.
  { destruct (Z.eq_dec d 0) as [Hd|Hd]; [subst; reflexivity|].
    apply Z.div_0_l. exact Hd. }
  rewrite Hz. ring.
Qed.

Lemma compose_self_gcd_div :
  forall f,
    bqf_ambiguous_div f ->
    bqf_comp_gcd f f = Z.abs (bqf_a f).
Proof.
  intros [a b c] [Hb0 | [Hab | Hanb]];
    unfold bqf_comp_gcd; cbn [bqf_a bqf_b] in *.
  - rewrite Hb0, Z.add_0_l, Z.div_0_l by lia.
    rewrite Z.gcd_diag, Z.gcd_0_r, Z.abs_idemp. reflexivity.
  - subst b. replace ((a + a) / 2) with a by (apply Z.div_unique with 0; lia).
    rewrite Z.gcd_diag, Z.gcd_comm, Z.gcd_abs_r, Z.gcd_diag. reflexivity.
  - subst a.
    rewrite Z.gcd_diag.
    replace ((b + b) / 2) with b by (apply Z.div_unique with 0; lia).
    rewrite Z.gcd_abs_l, Z.gcd_opp_l, Z.gcd_diag, Z.abs_opp. reflexivity.
Qed.

Lemma dirichlet_B_self_div :
  forall f, dirichlet_B f f = bqf_b f.
Proof.
  intros f. unfold dirichlet_B.
  destruct (Z.abs (bqf_a f) =? 1); [reflexivity|].
  rewrite Z.sub_diag. rewrite Z.div_0_l by lia.
  rewrite solve_cong_target_0. ring.
Qed.

Theorem compose_self_leading_one :
  forall f,
    bqf_a f <> 0 ->
    bqf_ambiguous_div f ->
    bqf_a (bqf_compose f f) = 1.
Proof.
  intros f Ha Hdiv.
  unfold bqf_compose. rewrite compose_self_gcd_div by exact Hdiv.
  destruct f as [a b c]. cbn [bqf_a] in *.
  rewrite Z.abs_square. apply Z.div_same. nia.
Qed.

Lemma compose_self_b :
  forall f, bqf_b (bqf_compose f f) = bqf_b f.
Proof.
  intros f. unfold bqf_compose. apply dirichlet_B_self_div.
Qed.

Lemma compose_self_c :
  forall f,
    bqf_a f <> 0 ->
    bqf_ambiguous_div f ->
    bqf_c (bqf_compose f f) =
      (bqf_b f * bqf_b f - bqf_disc f) / 4.
Proof.
  intros f Ha Hdiv.
  unfold bqf_compose.
  rewrite compose_self_gcd_div by exact Hdiv.
  rewrite dirichlet_B_self_div.
  destruct f as [a b c]. cbn [bqf_a bqf_b bqf_c] in *.
  rewrite Z.abs_square, Z.div_same by nia.
  rewrite Z.mul_1_r. reflexivity.
Qed.

Lemma four_divides_b2_minus_disc :
  forall f, (4 | bqf_b f * bqf_b f - bqf_disc f).
Proof.
  intros f. unfold bqf_disc.
  exists (bqf_a f * bqf_c f). ring.
Qed.

Theorem compose_self_of_disc :
  forall f D,
    iq_disc D ->
    of_disc f D ->
    bqf_ambiguous_div f ->
    of_disc (bqf_compose f f) D.
Proof.
  intros f D Hiq Hof Hdiv.
  pose proof (of_disc_a_nz f D Hof (proj1 Hiq)) as Ha.
  destruct Hof as [Hdisc _].
  split.
  - unfold bqf_disc.
    rewrite compose_self_leading_one by assumption.
    rewrite compose_self_b, compose_self_c by assumption.
    rewrite Hdisc.
    apply reconstruct_disc_div4.
    rewrite <- Hdisc. apply four_divides_b2_minus_disc.
  - unfold bqf_primitive.
    rewrite compose_self_leading_one by assumption.
    rewrite Z.gcd_1_l. apply Z.gcd_1_l.
Qed.

Theorem compose_self_ambiguous_equiv_id :
  forall f D,
    iq_disc D ->
    of_disc f D ->
    bqf_ambiguous_div f ->
    bqf_equiv (bqf_compose f f) (bqf_id D).
Proof.
  intros f D Hiq Hof Hdiv.
  apply form_a_one_equiv_id; [exact Hiq | apply compose_self_of_disc; assumption |].
  apply compose_self_leading_one;
    [apply (of_disc_a_nz f D Hof (proj1 Hiq)) | exact Hdiv].
Qed.

(** Associativity of Dirichlet composition is named, except on
    the triple [{id, f, f⁻¹}] where the identity laws suffice. *)
Definition compose_assoc_named (D : Z) : Prop :=
  forall f g h,
    of_disc f D -> of_disc g D -> of_disc h D ->
    bqf_equiv (bqf_compose (bqf_compose f g) h)
              (bqf_compose f (bqf_compose g h)).

(** Left-compatibility of composition with equivalence.  Unused
    refuse: blocks [y^h = 1 ⇒ y^{h+1} = y] on unreduced
    representatives ([ClassGroupWall]). *)
Definition compose_left_compat_named (D : Z) : Prop :=
  forall f g h,
    of_disc f D -> of_disc g D -> of_disc h D ->
    bqf_equiv f g ->
    bqf_equiv (bqf_compose h f) (bqf_compose h g).

Theorem compose_assoc_id_inv :
  forall D f,
    iq_disc D ->
    of_disc f D ->
    bqf_compose (bqf_compose (bqf_id D) f) (bqf_inv f) =
      bqf_compose (bqf_id D) (bqf_compose f (bqf_inv f)).
Proof.
  intros D f Hiq Hof.
  rewrite (compose_id_left D f Hiq Hof).
  rewrite (compose_id_left D (bqf_compose f (bqf_inv f)) Hiq).
  - reflexivity.
  - apply compose_inv_of_disc; assumption.
Qed.

(** ** Ambiguous forms from a divisor of [Δ] *)

Definition amb_from_div (D a : Z) : bqf :=
  if a =? 0 then bqf_id D
  else if D mod 4 =? 0
  then {| bqf_a := a; bqf_b := 0; bqf_c := - (D / (4 * a)) |}
  else {| bqf_a := a; bqf_b := a; bqf_c := (a * a - D) / (4 * a) |}.

Lemma amb_from_div_ambiguous :
  forall D a, a <> 0 -> bqf_ambiguous (amb_from_div D a).
Proof.
  intros D a Ha. unfold amb_from_div, bqf_ambiguous.
  destruct (Z.eqb_spec a 0); [congruence|].
  destruct (D mod 4 =? 0); simpl; [now left | right; now left].
Qed.

Lemma amb_from_div_disc_mod0 :
  forall D a,
    a <> 0 ->
    D mod 4 = 0 ->
    (4 * a | D) ->
    bqf_disc (amb_from_div D a) = D.
Proof.
  intros D a Ha Hm [k Hk].
  unfold amb_from_div, bqf_disc.
  destruct (Z.eqb_spec a 0); [congruence|].
  rewrite Hm. change (0 =? 0) with true.
  cbn [bqf_a bqf_b bqf_c].
  rewrite Z.mul_0_l, Z.sub_0_l, Z.mul_opp_r, Z.opp_involutive.
  rewrite Hk.
  rewrite (Z.div_mul k (4 * a)) by nia.
  ring.
Qed.

Lemma amb_from_div_disc_mod1 :
  forall D a,
    a <> 0 ->
    D mod 4 = 1 ->
    (4 * a | a * a - D) ->
    bqf_disc (amb_from_div D a) = D.
Proof.
  intros D a Ha Hm [k Hk].
  unfold amb_from_div, bqf_disc.
  destruct (Z.eqb_spec a 0); [congruence|].
  destruct (Z.eqb_spec (D mod 4) 0) as [H0 | _]; [congruence|].
  cbn [bqf_a bqf_b bqf_c].
  rewrite Hk.
  rewrite (Z.div_mul k (4 * a)) by nia.
  lia.
Qed.

(** ** Catalog: [Δ ∈ {−23, −47, −87, −403, −455}] *)

Definition form_neg87_amb : bqf :=
  {| bqf_a := 3; bqf_b := 3; bqf_c := 8 |}.

Definition form_neg403_amb : bqf :=
  {| bqf_a := 13; bqf_b := 13; bqf_c := 11 |}.

Definition form_neg403_amb_red : bqf :=
  {| bqf_a := 11; bqf_b := 9; bqf_c := 11 |}.

Definition form_neg455_5 : bqf :=
  {| bqf_a := 5; bqf_b := 5; bqf_c := 24 |}.

Definition form_neg455_7 : bqf :=
  {| bqf_a := 7; bqf_b := 7; bqf_c := 18 |}.

Definition form_neg455_13 : bqf :=
  {| bqf_a := 13; bqf_b := 13; bqf_c := 12 |}.

Definition form_neg455_13_red : bqf :=
  {| bqf_a := 12; bqf_b := 11; bqf_c := 12 |}.

Lemma iq_neg23 : iq_disc (-23).
Proof. unfold iq_disc. split; [lia|]. right. vm_compute. reflexivity. Qed.

Lemma iq_neg47 : iq_disc (-47).
Proof. unfold iq_disc. split; [lia|]. right. vm_compute. reflexivity. Qed.

Lemma iq_neg87 : iq_disc (-87).
Proof. unfold iq_disc. split; [lia|]. right. vm_compute. reflexivity. Qed.

Lemma iq_neg403 : iq_disc (-403).
Proof. unfold iq_disc. split; [lia|]. right. vm_compute. reflexivity. Qed.

Lemma iq_neg455 : iq_disc (-455).
Proof. unfold iq_disc. split; [lia|]. right. vm_compute. reflexivity. Qed.

Theorem form_neg87_amb_of_disc : of_disc form_neg87_amb (-87).
Proof. unfold of_disc, form_neg87_amb, bqf_disc, bqf_primitive. simpl. split; vm_compute; reflexivity. Qed.

Theorem form_neg403_amb_of_disc : of_disc form_neg403_amb (-403).
Proof. unfold of_disc, form_neg403_amb, bqf_disc, bqf_primitive. simpl. split; vm_compute; reflexivity. Qed.

Theorem form_neg403_amb_red_of_disc : of_disc form_neg403_amb_red (-403).
Proof. unfold of_disc, form_neg403_amb_red, bqf_disc, bqf_primitive. simpl. split; vm_compute; reflexivity. Qed.

Theorem form_neg455_5_of_disc : of_disc form_neg455_5 (-455).
Proof. unfold of_disc, form_neg455_5, bqf_disc, bqf_primitive. simpl. split; vm_compute; reflexivity. Qed.

Theorem form_neg455_7_of_disc : of_disc form_neg455_7 (-455).
Proof. unfold of_disc, form_neg455_7, bqf_disc, bqf_primitive. simpl. split; vm_compute; reflexivity. Qed.

Theorem form_neg455_13_red_of_disc : of_disc form_neg455_13_red (-455).
Proof. unfold of_disc, form_neg455_13_red, bqf_disc, bqf_primitive. simpl. split; vm_compute; reflexivity. Qed.

Theorem form_neg87_amb_reduced : bqf_reduced form_neg87_amb.
Proof. unfold bqf_reduced, form_neg87_amb. simpl. split; [lia | intros; lia]. Qed.

Theorem form_neg403_amb_red_reduced : bqf_reduced form_neg403_amb_red.
Proof. unfold bqf_reduced, form_neg403_amb_red. simpl. split; [lia | intros; lia]. Qed.

Theorem form_neg455_5_reduced : bqf_reduced form_neg455_5.
Proof. unfold bqf_reduced, form_neg455_5. simpl. split; [lia | intros; lia]. Qed.

Theorem form_neg455_7_reduced : bqf_reduced form_neg455_7.
Proof. unfold bqf_reduced, form_neg455_7. simpl. split; [lia | intros; lia]. Qed.

Theorem form_neg455_13_red_reduced : bqf_reduced form_neg455_13_red.
Proof. unfold bqf_reduced, form_neg455_13_red. simpl. split; [lia | intros; lia]. Qed.

Theorem form_neg87_amb_is_ambiguous : bqf_ambiguous form_neg87_amb.
Proof. unfold bqf_ambiguous, form_neg87_amb. simpl. right; left; reflexivity. Qed.

Theorem form_neg403_amb_is_ambiguous : bqf_ambiguous form_neg403_amb.
Proof. unfold bqf_ambiguous, form_neg403_amb. simpl. right; left; reflexivity. Qed.

Theorem form_neg403_amb_red_is_ambiguous : bqf_ambiguous form_neg403_amb_red.
Proof. unfold bqf_ambiguous, form_neg403_amb_red. simpl. do 3 right. reflexivity. Qed.

Theorem form_neg455_5_is_ambiguous : bqf_ambiguous form_neg455_5.
Proof. unfold bqf_ambiguous, form_neg455_5. simpl. right; left; reflexivity. Qed.

Theorem form_neg455_7_is_ambiguous : bqf_ambiguous form_neg455_7.
Proof. unfold bqf_ambiguous, form_neg455_7. simpl. right; left; reflexivity. Qed.

Theorem form_neg455_13_red_is_ambiguous : bqf_ambiguous form_neg455_13_red.
Proof. unfold bqf_ambiguous, form_neg455_13_red. simpl. do 3 right. reflexivity. Qed.

Theorem form_neg87_not_principal :
  ~ bqf_equiv form_neg87_amb (bqf_id (-87)).
Proof.
  apply reduced_a_gt_1_not_principal with (D := -87).
  - apply form_neg87_amb_of_disc.
  - apply form_neg87_amb_reduced.
  - unfold form_neg87_amb. simpl. lia.
Qed.

Theorem form_neg403_not_principal :
  ~ bqf_equiv form_neg403_amb_red (bqf_id (-403)).
Proof.
  apply reduced_a_gt_1_not_principal with (D := -403).
  - apply form_neg403_amb_red_of_disc.
  - apply form_neg403_amb_red_reduced.
  - unfold form_neg403_amb_red. simpl. lia.
Qed.

Theorem form_neg455_5_not_principal :
  ~ bqf_equiv form_neg455_5 (bqf_id (-455)).
Proof.
  apply reduced_a_gt_1_not_principal with (D := -455).
  - apply form_neg455_5_of_disc.
  - apply form_neg455_5_reduced.
  - unfold form_neg455_5. simpl. lia.
Qed.

Theorem form_neg455_7_not_principal :
  ~ bqf_equiv form_neg455_7 (bqf_id (-455)).
Proof.
  apply reduced_a_gt_1_not_principal with (D := -455).
  - apply form_neg455_7_of_disc.
  - apply form_neg455_7_reduced.
  - unfold form_neg455_7. simpl. lia.
Qed.

Theorem form_neg455_13_not_principal :
  ~ bqf_equiv form_neg455_13_red (bqf_id (-455)).
Proof.
  apply reduced_a_gt_1_not_principal with (D := -455).
  - apply form_neg455_13_red_of_disc.
  - apply form_neg455_13_red_reduced.
  - unfold form_neg455_13_red. simpl. lia.
Qed.

(** Unrestricted low-order on [Cl(Δ)] for [B = 2]: a non-principal
    ambiguous form.  There is no CRT-split analogue — the winning
    condition is the class, not a factor of a modulus. *)
Definition Problem_LowOrder_Cl (D B : Z) (f : bqf) : Prop :=
  of_disc f D /\
  bqf_ambiguous f /\
  ~ bqf_equiv f (bqf_id D) /\
  2 <= B.

Theorem catalog_compose_inv_is_principal :
  bqf_equiv (bqf_compose form_neg87_amb (bqf_inv form_neg87_amb)) (bqf_id (-87)) /\
  bqf_equiv (bqf_compose form_neg403_amb_red (bqf_inv form_neg403_amb_red)) (bqf_id (-403)) /\
  bqf_equiv (bqf_compose form_neg455_5 (bqf_inv form_neg455_5)) (bqf_id (-455)).
Proof.
  split; [|split].
  - apply compose_inv_equiv_id; [apply iq_neg87 | apply form_neg87_amb_of_disc].
  - apply compose_inv_equiv_id; [apply iq_neg403 | apply form_neg403_amb_red_of_disc].
  - apply compose_inv_equiv_id; [apply iq_neg455 | apply form_neg455_5_of_disc].
Qed.

Theorem catalog_wins_LowOrder_B2 :
  Problem_LowOrder_Cl (-87) 2 form_neg87_amb /\
  Problem_LowOrder_Cl (-403) 2 form_neg403_amb_red /\
  Problem_LowOrder_Cl (-455) 2 form_neg455_5 /\
  Problem_LowOrder_Cl (-455) 2 form_neg455_7 /\
  Problem_LowOrder_Cl (-455) 2 form_neg455_13_red.
Proof.
  unfold Problem_LowOrder_Cl.
  split; [|split; [|split; [|split]]].
  - split; [apply form_neg87_amb_of_disc|].
    split; [apply form_neg87_amb_is_ambiguous|].
    split; [apply form_neg87_not_principal|lia].
  - split; [apply form_neg403_amb_red_of_disc|].
    split; [apply form_neg403_amb_red_is_ambiguous|].
    split; [apply form_neg403_not_principal|lia].
  - split; [apply form_neg455_5_of_disc|].
    split; [apply form_neg455_5_is_ambiguous|].
    split; [apply form_neg455_5_not_principal|lia].
  - split; [apply form_neg455_7_of_disc|].
    split; [apply form_neg455_7_is_ambiguous|].
    split; [apply form_neg455_7_not_principal|lia].
  - split; [apply form_neg455_13_red_of_disc|].
    split; [apply form_neg455_13_red_is_ambiguous|].
    split; [apply form_neg455_13_not_principal|lia].
Qed.

(** Exponentiation is repeated composition.  Used in week 8. *)
Fixpoint bqf_exp (D : Z) (f : bqf) (k : nat) : bqf :=
  match k with
  | O => bqf_id D
  | S k' => bqf_compose (bqf_exp D f k') f
  end.

Lemma bqf_exp_0 : forall D f, bqf_exp D f 0 = bqf_id D.
Proof. reflexivity. Qed.

Lemma bqf_exp_1 :
  forall D f,
    iq_disc D ->
    of_disc f D ->
    bqf_exp D f 1 = f.
Proof.
  intros D f Hiq Hof. simpl.
  apply compose_id_left; assumption.
Qed.

Lemma bqf_exp_2 :
  forall D f,
    iq_disc D ->
    of_disc f D ->
    bqf_exp D f 2 = bqf_compose f f.
Proof.
  intros D f Hiq Hof. simpl.
  rewrite compose_id_left by assumption. reflexivity.
Qed.

Theorem bqf_exp_2_ambiguous_div :
  forall f D,
    iq_disc D ->
    of_disc f D ->
    bqf_ambiguous_div f ->
    bqf_equiv (bqf_exp D f 2) (bqf_id D).
Proof.
  intros f D Hiq Hof Hdiv.
  rewrite bqf_exp_2 by assumption.
  apply compose_self_ambiguous_equiv_id; assumption.
Qed.


