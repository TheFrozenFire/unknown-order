From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import PowersOfTau.
Require Import EvalProduct.
Require Import PublicQuad.

Open Scope Z_scope.

(** * Logarithmic fold of the bilinear CRS combine

    [public_quad_check] plus per-slot Fiat–Shamir posts one
    encoding (and a Sigma) per private coefficient: linear in
    the private length.  Packed [C_A = g^{A(τ)}] is already one
    group element.  The gap is the product opening.

    This file folds the coefficient vectors with public [x=2].
    Each round posts 13 residues; the leaf posts two scalars.
    The verifier does not take a slot list and does not
    bound-search every slot.  Completeness is the honest product
    / QAP identity.  Group-mul is rejected on the pin.
    Collision-resistance / ROM / PPT SNARK remain
    [Refuse_hash_as_oracle], [Refuse_ROM], [Refuse_PPT_advantage].

    Cross-confirmed by [cas/114_succinct.gp]. *)

Definition succ_x : Z := 2.

(** ** List halves and the fold [a_L + 2 a_R] *)

Definition succ_half (a : list Z) : list Z * list Z :=
  let m := Nat.div2 (length a) in
  (firstn m a, skipn m a).

Definition succ_fold_vec (aL aR : list Z) : list Z :=
  poly_add aL (map_mul succ_x aR).

Lemma poly_eval_app :
  forall a b x,
    0 <= x ->
    poly_eval (a ++ b) x =
      poly_eval a x + x ^ Z.of_nat (length a) * poly_eval b x.
Proof.
  intros a b x Hx.
  induction a as [|ha ta IH].
  - cbn [app poly_eval length].
    replace (x ^ Z.of_nat 0%nat) with 1 by (rewrite Z.pow_0_r; reflexivity).
    lia.
  - cbn [app poly_eval length].
    rewrite IH.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    ring.
Qed.

Lemma nn_app :
  forall a b, nn a -> nn b -> nn (a ++ b).
Proof.
  intros a b Ha.
  induction Ha; intros Hb; simpl.
  - exact Hb.
  - constructor; [assumption|]. apply IHHa. exact Hb.
Qed.

Lemma nn_firstn :
  forall n a, nn a -> nn (firstn n a).
Proof.
  intros n a Ha.
  revert n.
  induction Ha; intros n.
  - destruct n; constructor.
  - destruct n; simpl.
    + constructor.
    + constructor; [assumption|]. apply IHHa.
Qed.

Lemma nn_skipn :
  forall n a, nn a -> nn (skipn n a).
Proof.
  intros n a Ha.
  revert n.
  induction Ha; intros n.
  - destruct n; constructor.
  - destruct n; simpl.
    + constructor; [assumption|exact Ha].
    + apply IHHa.
Qed.

Lemma nn_map_mul_nonneg :
  forall k a, 0 <= k -> nn a -> nn (map_mul k a).
Proof.
  intros k a Hk Ha.
  induction Ha.
  - constructor.
  - simpl. constructor; [nia|exact IHHa].
Qed.

Lemma nn_poly_add :
  forall a b, nn a -> nn b -> nn (poly_add a b).
Proof.
  intros a b Ha Hb.
  revert b Hb.
  induction Ha; intros b Hb.
  - exact Hb.
  - destruct Hb.
    + simpl. constructor; [assumption|exact Ha].
    + simpl. constructor; [nia|]. apply IHHa. exact Hb.
Qed.

Lemma nn_succ_fold :
  forall aL aR, nn aL -> nn aR -> nn (succ_fold_vec aL aR).
Proof.
  intros aL aR Ha Hb.
  unfold succ_fold_vec, succ_x.
  apply nn_poly_add; [exact Ha|].
  apply nn_map_mul_nonneg; [lia|exact Hb].
Qed.

Lemma poly_eval_succ_fold :
  forall aL aR x,
    poly_eval (succ_fold_vec aL aR) x =
      poly_eval aL x + 2 * poly_eval aR x.
Proof.
  intros aL aR x.
  unfold succ_fold_vec, succ_x.
  rewrite poly_eval_add, poly_eval_map_mul.
  lia.
Qed.

(** ** One round of the posted proof (13 residues) *)

Definition succ_round_pack
    (CAL CAR YA CBL CBR YB U L R W Ls Rs Ws : Z)
    (rest : list Z) : list Z :=
  CAL :: CAR :: YA :: CBL :: CBR :: YB ::
  U :: L :: R :: W :: Ls :: Rs :: Ws :: rest.

Definition succ_proof_len (rounds : list Z) : nat :=
  (length rounds + 2)%nat.

(** ** Prover *)

Definition succ_prove_cons (N g tau : Z) (a b rest : list Z) : list Z :=
  let m := Nat.div2 (length a) in
  let aL := firstn m a in
  let aR := skipn m a in
  let bL := firstn m b in
  let bR := skipn m b in
  let Ps := pot_crs N g tau (2 * length a)%nat in
  succ_round_pack
    (pot_poly N g tau aL) (pot_poly N g tau aR)
    (quad_combine N Ps aR (1 :: nil) m)
    (pot_poly N g tau bL) (pot_poly N g tau bR)
    (quad_combine N Ps bR (1 :: nil) m)
    (quad_combine N Ps aL bL 0%nat)
    (quad_combine N Ps aL bR 0%nat)
    (quad_combine N Ps aR bL 0%nat)
    (quad_combine N Ps aR bR 0%nat)
    (quad_combine N Ps aL bR m)
    (quad_combine N Ps aR bL m)
    (quad_combine N Ps aR bR (2 * m)%nat)
    rest.

Fixpoint succ_prove (N g tau : Z) (fuel : nat) (a b : list Z)
  : list Z * Z * Z :=
  match fuel with
  | O =>
      match a, b with
      | a0 :: _, b0 :: _ => (nil, a0, b0)
      | _, _ => (nil, 0, 0)
      end
  | S fuel' =>
      (succ_prove_cons N g tau a b
         (fst (fst (succ_prove N g tau fuel'
            (succ_fold_vec (firstn (Nat.div2 (length a)) a)
                           (skipn (Nat.div2 (length a)) a))
            (succ_fold_vec (firstn (Nat.div2 (length b)) b)
                           (skipn (Nat.div2 (length b)) b))))),
       snd (fst (succ_prove N g tau fuel'
          (succ_fold_vec (firstn (Nat.div2 (length a)) a)
                         (skipn (Nat.div2 (length a)) a))
          (succ_fold_vec (firstn (Nat.div2 (length b)) b)
                         (skipn (Nat.div2 (length b)) b)))),
       snd (succ_prove N g tau fuel'
          (succ_fold_vec (firstn (Nat.div2 (length a)) a)
                         (skipn (Nat.div2 (length a)) a))
          (succ_fold_vec (firstn (Nat.div2 (length b)) b)
                         (skipn (Nat.div2 (length b)) b))))
  end.

Definition succ_prove_of (N g tau : Z) (a b : list Z) : list Z * Z * Z :=
  succ_prove N g tau (Nat.log2 (length a)) a b.

Lemma succ_round_pack_length :
  forall CAL CAR YA CBL CBR YB U L R W Ls Rs Ws rest,
    length (succ_round_pack CAL CAR YA CBL CBR YB U L R W Ls Rs Ws rest) =
      (13 + length rest)%nat.
Proof. intros. reflexivity. Qed.

Lemma succ_prove_cons_length :
  forall N g tau a b rest,
    length (succ_prove_cons N g tau a b rest) = (13 + length rest)%nat.
Proof.
  intros. unfold succ_prove_cons. rewrite succ_round_pack_length. reflexivity.
Qed.

Lemma succ_prove_rounds_log :
  forall N g tau fuel a b,
    length (fst (fst (succ_prove N g tau fuel a b))) = (13 * fuel)%nat.
Proof.
  intros N g tau fuel.
  Opaque succ_prove_cons.
  induction fuel as [|fuel IH]; intros a b.
  - destruct a; destruct b; reflexivity.
  - simpl.
    rewrite succ_prove_cons_length.
    rewrite IH.
    lia.
Qed.
Transparent succ_prove_cons.

(** ** Verifier: no slot list, no per-slot bound search *)

Fixpoint succ_verify (N : Z) (Ps : list Z)
    (CA CB CAB : Z) (rounds : list Z) (ast bst : Z) (n : nat) : bool :=
  match n with
  | S O =>
      let P0 := nth 0%nat Ps 0 in
      (powm P0 ast N =? CA) &&
      (powm P0 bst N =? CB) &&
      (powm P0 (ast * bst) N =? CAB) &&
      (0 <=? ast) && (0 <=? bst)
  | _ =>
      match rounds with
      | CAL :: CAR :: YA :: CBL :: CBR :: YB ::
        U :: L :: R :: W :: Ls :: Rs :: Ws :: rest =>
          let prod := (((U * Ls) mod N * Rs) mod N * Ws) mod N in
          let CAok := (CAL * YA) mod N =? CA in
          let CBok := (CBL * YB) mod N =? CB in
          let CABok := prod =? CAB in
          let CAp := (CAL * powm CAR succ_x N) mod N in
          let CBp := (CBL * powm CBR succ_x N) mod N in
          let CABp :=
            (((U * powm L succ_x N) mod N * powm R succ_x N) mod N *
               powm W (succ_x * succ_x) N) mod N in
          CAok && CBok && CABok &&
          succ_verify N Ps CAp CBp CABp rest ast bst (Nat.div2 n)
      | _ => false
      end
  end.

Definition succ_verify_of (N : Z) (Ps : list Z)
    (CA CB CAB : Z) (pr : list Z * Z * Z) (n : nat) : bool :=
  succ_verify N Ps CA CB CAB (fst (fst pr)) (snd (fst pr)) (snd pr) n.

(** ** Size: [13 log2 n + 2] *)

Theorem succ_proof_len_is_log :
  forall N g tau a b,
    succ_proof_len (fst (fst (succ_prove_of N g tau a b))) =
      (13 * Nat.log2 (length a) + 2)%nat.
Proof.
  intros N g tau a b.
  unfold succ_prove_of, succ_proof_len.
  rewrite succ_prove_rounds_log.
  lia.
Qed.

Theorem succ_proof_len_n4 :
  let a := [2; 3; 1; 0] in
  let b := [1; 4; 0; 1] in
  succ_proof_len (fst (fst (succ_prove_of 187 3 5 a b))) = 28%nat.
Proof.
  unfold succ_proof_len, succ_prove_of.
  rewrite succ_prove_rounds_log.
  reflexivity.
Qed.

Theorem succ_proof_len_n16 :
  let a := [2; 3; 1; 0; 1; 0; 2; 1; 0; 3; 1; 0; 2; 0; 1; 0] in
  let b := [1; 4; 0; 1; 0; 1; 0; 2; 1; 0; 1; 0; 0; 1; 2; 1] in
  succ_proof_len (fst (fst (succ_prove_of 187 3 5 a b))) = 54%nat.
Proof.
  unfold succ_proof_len, succ_prove_of.
  rewrite succ_prove_rounds_log.
  reflexivity.
Qed.

Theorem succ_proof_len_bound_pin :
  let C := 16%nat in
  (28 <= C * 2)%nat /\ (54 <= C * 4)%nat.
Proof. lia. Qed.

(** ** Completeness on the pin family and QAP *)

Definition pinN : Z := 11 * 17.
Definition ping : Z := 3.
Definition pintau : Z := 5.

Theorem succ_pin_n2_accepts :
  let a := [2; 3] in
  let b := [1; 4] in
  let Ps := pot_crs pinN ping pintau 4%nat in
  let pr := succ_prove_of pinN ping pintau a b in
  succ_verify_of pinN Ps
    (pot_poly pinN ping pintau a)
    (pot_poly pinN ping pintau b)
    (pot_poly pinN ping pintau (poly_conv a b))
    pr 2%nat = true.
Proof. vm_compute. reflexivity. Qed.

Theorem succ_pin_n2_rejects_group_mul :
  let a := [2; 3] in
  let b := [1; 4] in
  let Ps := pot_crs pinN ping pintau 4%nat in
  let pr := succ_prove_of pinN ping pintau a b in
  let CA := pot_poly pinN ping pintau a in
  let CB := pot_poly pinN ping pintau b in
  succ_verify_of pinN Ps CA CB ((CA * CB) mod pinN) pr 2%nat = false.
Proof. vm_compute. reflexivity. Qed.

Theorem succ_pin_n2_sum_neq_prod :
  let a := [2; 3] in
  let b := [1; 4] in
  (pot_poly pinN ping pintau a * pot_poly pinN ping pintau b) mod pinN <>
    pot_poly pinN ping pintau (poly_conv a b).
Proof. vm_compute. discriminate. Qed.

Theorem succ_pin_qap :
  let A := [1; 1] in
  let B := [2; 0] in
  let C := [2; 2] in
  let Hh := [0] in
  let van := [0; 1] in
  let Ps := pot_crs pinN ping pintau 4%nat in
  let pr := succ_prove_of pinN ping pintau A B in
  succ_verify_of pinN Ps
    (pot_poly pinN ping pintau A)
    (pot_poly pinN ping pintau B)
    ((pot_poly pinN ping pintau C *
        pot_poly pinN ping pintau (poly_conv Hh van)) mod pinN)
    pr 2%nat = true.
Proof. vm_compute. reflexivity. Qed.
