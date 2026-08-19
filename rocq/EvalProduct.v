From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import PowersOfTau.

Open Scope Z_scope.

(** * Product of two committed evaluations at [τ]

    [C_f = g^{f(τ)}] is [pot_poly].  The group law adds exponents:
    [C_f · C_h = g^{f(τ)+h(τ)}].  The QAP identity wants the
    *field* product [f(τ)·h(τ)], i.e. [g^{(f·h)(τ)}].  That is
    evaluation of the coefficient convolution, or equivalently
    [C_f^{h(τ)}].  The second form needs the integer [h(τ)].

    Monomials are already in the CRS: [τ^i · τ^j = τ^{i+j}], so
    [g^{τ^i · τ^j} = P_{i+j}].  A self-bilinear map with
    [e(g,g)=g] is a public product of arbitrary committed
    evaluations (existence a hypothesis).

    Cross-confirmed by [cas/95_eval_product.gp]. *)

(** ** Coefficient polynomials, low term first *)

Fixpoint poly_eval (cs : list Z) (x : Z) : Z :=
  match cs with
  | nil => 0
  | c :: rest => c + x * poly_eval rest x
  end.

Inductive nn : list Z -> Prop :=
  | nn_nil : nn nil
  | nn_cons : forall c rest, 0 <= c -> nn rest -> nn (c :: rest).

Lemma poly_eval_nonneg :
  forall cs x, nn cs -> 0 <= x -> 0 <= poly_eval cs x.
Proof.
  intros cs x Hcs Hx.
  induction Hcs; simpl; nia.
Qed.

Fixpoint map_mul (k : Z) (cs : list Z) : list Z :=
  match cs with
  | nil => nil
  | c :: rest => (k * c) :: map_mul k rest
  end.

Lemma poly_eval_map_mul :
  forall k cs x,
    poly_eval (map_mul k cs) x = k * poly_eval cs x.
Proof.
  intros k cs x.
  induction cs as [|c rest IH]; simpl; lia.
Qed.

Fixpoint poly_add (a b : list Z) : list Z :=
  match a, b with
  | nil, _ => b
  | _, nil => a
  | ha :: ta, hb :: tb => (ha + hb) :: poly_add ta tb
  end.

Lemma poly_eval_add :
  forall a b x,
    poly_eval (poly_add a b) x = poly_eval a x + poly_eval b x.
Proof.
  intros a.
  induction a as [|ha ta IH]; intros b x.
  - simpl. lia.
  - destruct b as [|hb tb]; simpl; try lia.
    rewrite IH. lia.
Qed.

Definition poly_shift (a : list Z) : list Z :=
  0 :: a.

Lemma poly_eval_shift :
  forall a x,
    poly_eval (poly_shift a) x = x * poly_eval a x.
Proof. intros. unfold poly_shift. simpl. lia. Qed.

Fixpoint poly_conv (a b : list Z) : list Z :=
  match a with
  | nil => nil
  | ha :: ta => poly_add (map_mul ha b) (poly_shift (poly_conv ta b))
  end.

Theorem poly_eval_conv :
  forall a b x,
    poly_eval (poly_conv a b) x = poly_eval a x * poly_eval b x.
Proof.
  intros a.
  induction a as [|ha ta IH]; intros b x.
  - simpl. lia.
  - simpl.
    rewrite poly_eval_add, poly_eval_map_mul, poly_eval_shift, IH.
    ring.
Qed.

(** ** The encoding [g^{f(τ)}] *)

Definition pot_poly (N g tau : Z) (cs : list Z) : Z :=
  powm g (poly_eval cs tau) N.

Theorem pot_poly_is_eval :
  forall N g tau cs,
    pot_poly N g tau cs = powm g (poly_eval cs tau) N.
Proof. intros. reflexivity. Qed.

Theorem pot_poly_add :
  forall N g tau a b,
    1 < N ->
    0 <= poly_eval a tau ->
    0 <= poly_eval b tau ->
    pot_poly N g tau (poly_add a b) =
      (pot_poly N g tau a * pot_poly N g tau b) mod N.
Proof.
  intros N g tau a b Hn Ha Hb.
  unfold pot_poly.
  rewrite poly_eval_add.
  apply powm_add_r; lia.
Qed.

Theorem pot_poly_scale :
  forall N g tau k a,
    1 < N ->
    0 <= k ->
    0 <= poly_eval a tau ->
    pot_poly N g tau (map_mul k a) =
      powm (pot_poly N g tau a) k N.
Proof.
  intros N g tau k a Hn Hk Ha.
  unfold pot_poly.
  rewrite poly_eval_map_mul.
  rewrite (Z.mul_comm k).
  apply powm_mul_r; lia.
Qed.

Theorem pot_poly_shift :
  forall N g tau a,
    1 < N ->
    0 <= tau ->
    0 <= poly_eval a tau ->
    pot_poly N g tau (poly_shift a) =
      powm (pot_poly N g tau a) tau N.
Proof.
  intros N g tau a Hn Ht Ha.
  unfold pot_poly.
  rewrite poly_eval_shift.
  rewrite (Z.mul_comm tau).
  apply powm_mul_r; lia.
Qed.

(** The field product of evaluations is a raise of one encoding
    to the *integer* evaluation of the other. *)
Theorem pot_poly_conv_raise :
  forall N g tau a b,
    1 < N ->
    0 <= poly_eval a tau ->
    0 <= poly_eval b tau ->
    pot_poly N g tau (poly_conv a b) =
      powm (pot_poly N g tau a) (poly_eval b tau) N.
Proof.
  intros N g tau a b Hn Ha Hb.
  unfold pot_poly.
  rewrite poly_eval_conv.
  apply powm_mul_r; lia.
Qed.

Theorem pot_poly_conv_raise_comm :
  forall N g tau a b,
    1 < N ->
    0 <= poly_eval a tau ->
    0 <= poly_eval b tau ->
    pot_poly N g tau (poly_conv a b) =
      powm (pot_poly N g tau b) (poly_eval a tau) N.
Proof.
  intros N g tau a b Hn Ha Hb.
  unfold pot_poly.
  rewrite poly_eval_conv, Z.mul_comm.
  apply powm_mul_r; lia.
Qed.

(** Group multiplication of encodings is the *sum* of evaluations,
    not the product. *)
Theorem pot_poly_mul_is_add :
  forall N g tau a b,
    1 < N ->
    0 <= poly_eval a tau ->
    0 <= poly_eval b tau ->
    (pot_poly N g tau a * pot_poly N g tau b) mod N =
      pot_poly N g tau (poly_add a b).
Proof.
  intros. rewrite pot_poly_add by assumption. reflexivity.
Qed.

(** ** Monomials: the CRS already publishes [τ^i · τ^j] *)

Fixpoint poly_Xn (n : nat) : list Z :=
  match n with
  | O => 1 :: nil
  | S n' => 0 :: poly_Xn n'
  end.

Lemma nn_Xn : forall n, nn (poly_Xn n).
Proof.
  intros n. induction n as [|n IH].
  - simpl. constructor. lia. constructor.
  - simpl. constructor. lia. exact IH.
Qed.

Lemma poly_eval_Xn :
  forall n x,
    0 <= x ->
    poly_eval (poly_Xn n) x = x ^ Z.of_nat n.
Proof.
  intros n x Hx.
  induction n as [|n IH].
  - simpl. replace (x * 0) with 0 by lia. simpl. reflexivity.
  - simpl. rewrite IH.
    change (Z.pow_pos x (Pos.of_succ_nat n))
      with (x ^ Z.pos (Pos.of_succ_nat n)).
    change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    ring.
Qed.

Theorem pot_poly_Xn :
  forall N g tau n,
    1 < N ->
    0 <= tau ->
    pot_poly N g tau (poly_Xn n) = pot N g tau (Z.of_nat n).
Proof.
  intros N g tau n Hn Ht.
  unfold pot_poly, pot.
  rewrite poly_eval_Xn by exact Ht.
  reflexivity.
Qed.

Theorem monomial_eval_product :
  forall N g tau i j,
    1 < N ->
    0 <= tau ->
    pot N g tau (Z.of_nat (i + j)%nat) =
      powm g ((tau ^ Z.of_nat i) * (tau ^ Z.of_nat j)) N.
Proof.
  intros N g tau i j Hn Ht.
  unfold pot.
  rewrite Nat2Z.inj_add.
  rewrite Z.pow_add_r by (apply Nat2Z.is_nonneg || lia).
  reflexivity.
Qed.

Theorem monomial_conv_is_later_slot :
  forall N g tau i j,
    1 < N ->
    0 <= tau ->
    pot_poly N g tau (poly_conv (poly_Xn i) (poly_Xn j)) =
      pot N g tau (Z.of_nat (i + j)%nat).
Proof.
  intros N g tau i j Hn Ht.
  unfold pot_poly.
  rewrite poly_eval_conv.
  rewrite !poly_eval_Xn by exact Ht.
  rewrite monomial_eval_product by assumption.
  reflexivity.
Qed.

Theorem monomial_group_mul_is_sum :
  forall N g tau i j,
    1 < N ->
    0 <= tau ->
    (pot N g tau (Z.of_nat i) * pot N g tau (Z.of_nat j)) mod N =
      powm g (tau ^ Z.of_nat i + tau ^ Z.of_nat j) N.
Proof.
  intros N g tau i j Hn Ht.
  unfold pot.
  symmetry.
  apply powm_add_r; try (apply Z.pow_nonneg; exact Ht); lia.
Qed.

(** ** Self-bilinear map is a public product of encodings *)

Theorem self_bil_committed_product :
  forall e N g tau a b,
    1 < N ->
    0 <= tau ->
    nn a ->
    nn b ->
    self_bilinear e N g ->
    e g g = g mod N ->
    e (pot_poly N g tau a) (pot_poly N g tau b) =
      pot_poly N g tau (poly_conv a b).
Proof.
  intros e N g tau a b Hn Ht Hna Hnb He Hgg.
  unfold pot_poly.
  pose proof (poly_eval_nonneg a tau Hna Ht) as Ha.
  pose proof (poly_eval_nonneg b tau Hnb Ht) as Hb.
  rewrite (He (poly_eval a tau) (poly_eval b tau) Ha Hb).
  rewrite Hgg.
  rewrite powm_mod_base by lia.
  rewrite poly_eval_conv.
  reflexivity.
Qed.

Theorem self_bil_monomial_product :
  forall e N g tau i j,
    1 < N ->
    0 <= tau ->
    self_bilinear e N g ->
    e g g = g mod N ->
    e (pot N g tau (Z.of_nat i)) (pot N g tau (Z.of_nat j)) =
      pot N g tau (Z.of_nat (i + j)%nat).
Proof.
  intros e N g tau i j Hn Ht He Hgg.
  rewrite <- (pot_poly_Xn N g tau i), <- (pot_poly_Xn N g tau j)
    by assumption.
  rewrite (self_bil_committed_product e N g tau (poly_Xn i) (poly_Xn j)
             Hn Ht (nn_Xn i) (nn_Xn j) He Hgg).
  apply monomial_conv_is_later_slot; assumption.
Qed.

(** ** Two-wire witness encoding: [∏ U_j^{w_j} = g^{(w0 A0 + w1 A1)(τ)}] *)

Theorem two_wire_commit :
  forall N g tau w0 w1 A0 A1,
    1 < N ->
    0 <= w0 ->
    0 <= w1 ->
    0 <= poly_eval A0 tau ->
    0 <= poly_eval A1 tau ->
    (powm (pot_poly N g tau A0) w0 N *
       powm (pot_poly N g tau A1) w1 N) mod N =
      pot_poly N g tau (poly_add (map_mul w0 A0) (map_mul w1 A1)).
Proof.
  intros N g tau w0 w1 A0 A1 Hn Hw0 Hw1 Ha0 Ha1.
  rewrite <- (pot_poly_scale N g tau w0 A0) by assumption.
  rewrite <- (pot_poly_scale N g tau w1 A1) by assumption.
  symmetry.
  apply pot_poly_add; try rewrite poly_eval_map_mul; nia.
Qed.

Theorem two_wire_product_raise :
  forall N g tau w0 w1 A0 A1 B,
    1 < N ->
    0 <= w0 ->
    0 <= w1 ->
    0 <= poly_eval A0 tau ->
    0 <= poly_eval A1 tau ->
    0 <= poly_eval B tau ->
    pot_poly N g tau
      (poly_conv (poly_add (map_mul w0 A0) (map_mul w1 A1)) B) =
      powm (pot_poly N g tau (poly_add (map_mul w0 A0) (map_mul w1 A1)))
        (poly_eval B tau) N.
Proof.
  intros N g tau w0 w1 A0 A1 B Hn Hw0 Hw1 Ha0 Ha1 Hb.
  apply pot_poly_conv_raise; try assumption.
  rewrite poly_eval_add, !poly_eval_map_mul. nia.
Qed.
