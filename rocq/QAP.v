From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import Hardness.
Require Import PowersOfTau.
Require Import EvalProduct.

Open Scope Z_scope.

(** * QAP completeness on committed evaluations

    A witness [w] against public families [As, Bs, Cs] produces
    [A_w = Σ w_j A_j] (same for [B,C]).  The QAP identity is
    [A_w B_w − C_w = H Z] as polynomial functions.  At the CRS
    point [τ] that is [C_{A·B} = C_C · C_{H·Z}]
    ([qap_complete_at_tau]).  The specialized-CRS multi-exponent
    [∏ U_j^{w_j}] equals that encoding ([pot_wires_is_lincomb]).
    Public inputs are the prefix of the same multi-exponent
    ([pot_wires_app]).

    If the remainder encoding is [1] then either [τ] is a root
    or the order of [g] divides the remainder ([qap_point_sound]).

    Cross-confirmed by [cas/96_qap.gp]. *)

Definition poly_sub (a b : list Z) : list Z :=
  poly_add a (map_mul (-1) b).

Lemma poly_eval_sub :
  forall a b x,
    poly_eval (poly_sub a b) x = poly_eval a x - poly_eval b x.
Proof.
  intros a b x.
  unfold poly_sub.
  rewrite poly_eval_add, poly_eval_map_mul.
  lia.
Qed.

Definition qap_rem (A B C H van : list Z) : list Z :=
  poly_sub (poly_conv A B) (poly_add C (poly_conv H van)).

Definition qap_at (A B C H van : list Z) (x : Z) : Prop :=
  poly_eval A x * poly_eval B x - poly_eval C x -
    poly_eval H x * poly_eval van x = 0.

Theorem qap_rem_eval :
  forall A B C H van x,
    poly_eval (qap_rem A B C H van) x =
      poly_eval A x * poly_eval B x - poly_eval C x -
        poly_eval H x * poly_eval van x.
Proof.
  intros A B C H van x.
  unfold qap_rem.
  rewrite poly_eval_sub, poly_eval_add, !poly_eval_conv.
  lia.
Qed.

Theorem qap_at_iff_rem_zero :
  forall A B C H van x,
    qap_at A B C H van x <-> poly_eval (qap_rem A B C H van) x = 0.
Proof.
  intros. unfold qap_at. rewrite qap_rem_eval. lia.
Qed.

Theorem qap_complete_at_tau :
  forall N g tau A B C H van,
    1 < N ->
    qap_at A B C H van tau ->
    0 <= poly_eval C tau ->
    0 <= poly_eval (poly_conv H van) tau ->
    pot_poly N g tau (poly_conv A B) =
      (pot_poly N g tau C *
         pot_poly N g tau (poly_conv H van)) mod N.
Proof.
  intros N g tau A B C H van Hn Hq HaC HaHZ.
  unfold qap_at in Hq.
  unfold pot_poly.
  rewrite poly_eval_conv.
  assert (poly_eval A tau * poly_eval B tau =
            poly_eval C tau + poly_eval (poly_conv H van) tau) as Heq.
  { rewrite poly_eval_conv. lia. }
  rewrite Heq.
  apply powm_add_r; lia.
Qed.

Theorem qap_point_sound :
  forall N g tau r ord,
    1 < N ->
    0 <= poly_eval r tau ->
    Z.coprime g N ->
    is_order N g ord ->
    pot_poly N g tau r = 1 ->
    poly_eval r tau = 0 \/ (ord | poly_eval r tau).
Proof.
  intros N g tau r ord Hn Hr Hcop Hord Henc.
  unfold pot_poly in Henc.
  destruct (Z.eq_dec (poly_eval r tau) 0) as [Hz | Hnz].
  - left. exact Hz.
  - right.
    apply (order_divides_annihilator N g ord (poly_eval r tau));
      assumption.
Qed.

Theorem qap_sound_at_tau :
  forall N g tau A B C H van ord,
    1 < N ->
    0 <= poly_eval (qap_rem A B C H van) tau ->
    Z.coprime g N ->
    is_order N g ord ->
    pot_poly N g tau (qap_rem A B C H van) = 1 ->
    qap_at A B C H van tau \/
      (ord | poly_eval (qap_rem A B C H van) tau).
Proof.
  intros N g tau A B C H van ord Hn Hr Hcop Hord Henc.
  destruct (qap_point_sound N g tau (qap_rem A B C H van) ord
              Hn Hr Hcop Hord Henc) as [Hz | Hdiv].
  - left. apply qap_at_iff_rem_zero. exact Hz.
  - right. exact Hdiv.
Qed.

(** ** Specialized CRS: [∏ U_j^{w_j} = g^{(Σ w_j A_j)(τ)}] *)

Fixpoint poly_lincomb (ws : list Z) (As : list (list Z)) : list Z :=
  match ws, As with
  | w :: ws', A :: As' =>
      poly_add (map_mul w A) (poly_lincomb ws' As')
  | _, _ => nil
  end.

Fixpoint pot_wires (N g tau : Z) (ws : list Z) (As : list (list Z)) : Z :=
  match ws, As with
  | w :: ws', A :: As' =>
      (powm (pot_poly N g tau A) w N * pot_wires N g tau ws' As') mod N
  | _, _ => 1 mod N
  end.

Inductive wires_nn (x : Z) : list Z -> list (list Z) -> Prop :=
  | wnn_nil_w : forall As, wires_nn x nil As
  | wnn_nil_A : forall ws, wires_nn x ws nil
  | wnn_cons : forall w ws A As,
      0 <= w ->
      0 <= poly_eval A x ->
      wires_nn x ws As ->
      wires_nn x (w :: ws) (A :: As).

Lemma poly_eval_lincomb :
  forall ws As x,
    poly_eval (poly_lincomb ws As) x =
      match ws, As with
      | w :: ws', A :: As' =>
          w * poly_eval A x + poly_eval (poly_lincomb ws' As') x
      | _, _ => 0
      end.
Proof.
  intros ws As x.
  destruct ws as [|w ws']; destruct As as [|A As']; simpl; try lia.
  rewrite poly_eval_add, poly_eval_map_mul.
  lia.
Qed.

Lemma wires_nn_lincomb_nonneg :
  forall x ws As,
    wires_nn x ws As ->
    0 <= poly_eval (poly_lincomb ws As) x.
Proof.
  intros x ws As Hnn.
  induction Hnn.
  - simpl. lia.
  - destruct ws; simpl; lia.
  - rewrite poly_eval_lincomb. simpl. nia.
Qed.

Theorem pot_wires_is_lincomb :
  forall N g tau ws As,
    1 < N ->
    wires_nn tau ws As ->
    pot_wires N g tau ws As =
      pot_poly N g tau (poly_lincomb ws As).
Proof.
  intros N g tau ws As Hn Hnn.
  induction Hnn.
  - simpl. unfold pot_poly, poly_eval. symmetry. apply powm_0_r. lia.
  - unfold pot_poly. destruct ws; simpl; (symmetry; apply powm_0_r; lia).
  - simpl.
    rewrite IHHnn.
    rewrite <- (pot_poly_scale N g tau w A) by assumption.
    apply pot_poly_mul_is_add.
    + exact Hn.
    + rewrite poly_eval_map_mul. nia.
    + apply wires_nn_lincomb_nonneg. exact Hnn.
Qed.

Theorem same_witness_two_families :
  forall N g tau w As Bs,
    1 < N ->
    wires_nn tau w As ->
    wires_nn tau w Bs ->
    pot_wires N g tau w As = pot_poly N g tau (poly_lincomb w As) /\
    pot_wires N g tau w Bs = pot_poly N g tau (poly_lincomb w Bs).
Proof.
  intros N g tau w As Bs Hn Ha Hb.
  split; apply pot_wires_is_lincomb; assumption.
Qed.

Theorem qap_witness_complete :
  forall N g tau w As Bs Cs H van,
    1 < N ->
    wires_nn tau w As ->
    wires_nn tau w Bs ->
    wires_nn tau w Cs ->
    qap_at (poly_lincomb w As) (poly_lincomb w Bs)
           (poly_lincomb w Cs) H van tau ->
    0 <= poly_eval (poly_lincomb w Cs) tau ->
    0 <= poly_eval (poly_conv H van) tau ->
    pot_poly N g tau
      (poly_conv (poly_lincomb w As) (poly_lincomb w Bs)) =
      (pot_wires N g tau w Cs *
         pot_poly N g tau (poly_conv H van)) mod N.
Proof.
  intros N g tau w As Bs Cs H van Hn HAs HBs HCs Hq HC HHZ.
  rewrite (pot_wires_is_lincomb N g tau w Cs Hn HCs).
  apply (qap_complete_at_tau N g tau
           (poly_lincomb w As) (poly_lincomb w Bs)
           (poly_lincomb w Cs) H van); assumption.
Qed.

Lemma pot_wires_bounded :
  forall N g tau ws As,
    1 < N ->
    0 <= pot_wires N g tau ws As < N.
Proof.
  intros N g tau ws As Hn.
  revert As.
  induction ws as [|w ws IH]; intros As.
  - simpl. rewrite Z.mod_1_l by lia. lia.
  - destruct As as [|A As].
    + simpl. rewrite Z.mod_1_l by lia. lia.
    + simpl. apply Z.mod_pos_bound. lia.
Qed.

Theorem pot_wires_app :
  forall N g tau io priv As_io As_priv,
    1 < N ->
    wires_nn tau io As_io ->
    length io = length As_io ->
    pot_wires N g tau (io ++ priv) (As_io ++ As_priv) =
      (pot_wires N g tau io As_io *
         pot_wires N g tau priv As_priv) mod N.
Proof.
  intros N g tau io priv As_io As_priv Hn Hnn.
  revert As_io Hnn.
  induction io as [|w io IH]; intros As_io Hnn Hl.
  - simpl in Hl. destruct As_io; [|discriminate].
    simpl.
    rewrite Z.mod_1_l by lia.
    rewrite Z.mul_1_l.
    symmetry.
    apply Z.mod_small.
    apply pot_wires_bounded.
    exact Hn.
  - destruct As_io as [|A As]; [discriminate|].
    inversion Hnn; subst.
    simpl.
    rewrite (IH As H5 ltac:(simpl in Hl; lia)).
    rewrite Z.mul_mod_idemp_r by lia.
    rewrite Z.mul_assoc.
    rewrite Z.mul_mod_idemp_l by lia.
    reflexivity.
Qed.