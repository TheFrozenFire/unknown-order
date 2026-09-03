From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Require Import Pin.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import PowersOfTau.
Require Import EvalProduct.
Require Import CoeffPoK.
Require Import WirePoK.

Open Scope Z_scope.

(** * Fiat–Shamir compilation of the public-coin Sigma

    Interactive [eqdl_verify] takes a free challenge [c].
    [Refuse_NIZK_Fiat_Shamir] refuses ROM / PPT NIZK
    soundness, not this substitution.  The transform is
    [c = fs_challenge(statement, commitment)].  The posted proof
    is [(t1, t2, z)]; the NI verifier recomputes [c] and runs
    the same Sigma equation.  Collision-resistance and ROM
    quality remain [Refuse_hash_as_oracle], [Refuse_ROM],
    [Refuse_SHA_in_Rocq].  There is no SHA.

    Cross-confirmed by [cas/113_fiat_shamir.gp]. *)

(** ** Deterministic challenge map (not a hash oracle) *)

Definition fs_step (acc x m : Z) : Z := (2 * acc + x) mod m.

Fixpoint fs_fold (xs : list Z) (m acc : Z) : Z :=
  match xs with
  | nil => acc
  | x :: rest => fs_fold rest m (fs_step acc x m)
  end.

Definition fs_challenge (m : Z) (xs : list Z) : Z :=
  fs_fold xs m 0.

Lemma fs_step_nonneg :
  forall acc x m, 0 < m -> 0 <= fs_step acc x m.
Proof.
  intros acc x m Hm.
  unfold fs_step.
  pose proof (Z.mod_pos_bound (2 * acc + x) m Hm) as H.
  lia.
Qed.

Lemma fs_fold_nonneg :
  forall xs m acc,
    0 < m ->
    0 <= acc ->
    0 <= fs_fold xs m acc.
Proof.
  intros xs m acc Hm.
  revert acc.
  induction xs as [|x rest IH]; intros acc Hacc.
  - simpl. exact Hacc.
  - simpl. apply IH. apply fs_step_nonneg. exact Hm.
Qed.

Lemma fs_challenge_nonneg :
  forall m xs, 0 < m -> 0 <= fs_challenge m xs.
Proof.
  intros m xs Hm.
  unfold fs_challenge.
  apply fs_fold_nonneg; [exact Hm | lia].
Qed.

(** Statement of equal-DL: [(N, g, h, u, v)].  First message:
    [(t1, t2)]. *)

Definition fs_eqdl_challenge (N g h u v t1 t2 : Z) : Z :=
  fs_challenge N [N; g; h; u; v; t1; t2].

Lemma fs_eqdl_challenge_nonneg :
  forall N g h u v t1 t2,
    1 < N ->
    0 <= fs_eqdl_challenge N g h u v t1 t2.
Proof.
  intros. unfold fs_eqdl_challenge. apply fs_challenge_nonneg. lia.
Qed.

(** Posted NI proof: commitment and response.  No challenge. *)

Record ni_eqdl : Set := {
  ni_t1 : Z;
  ni_t2 : Z;
  ni_z : Z
}.

Definition fs_eqdl_prove (N g u tau w : Z) : ni_eqdl :=
  let h := powm g tau N in
  let v := powm u tau N in
  let t := eqdl_commit N g u w in
  let c := fs_eqdl_challenge N g h u v (fst t) (snd t) in
  {| ni_t1 := fst t; ni_t2 := snd t; ni_z := eqdl_response w c tau |}.

Definition fs_eqdl_verify (N g h u v : Z) (pr : ni_eqdl) : Prop :=
  let c := fs_eqdl_challenge N g h u v (ni_t1 pr) (ni_t2 pr) in
  eqdl_verify N g h u v (ni_t1 pr) (ni_t2 pr) c (ni_z pr).

Definition eqdl_verifyb (N g h u v t1 t2 c z : Z) : bool :=
  (powm g z N =? (t1 * powm h c N) mod N) &&
  (powm u z N =? (t2 * powm v c N) mod N).

Definition fs_eqdl_verifyb (N g h u v : Z) (pr : ni_eqdl) : bool :=
  let c := fs_eqdl_challenge N g h u v (ni_t1 pr) (ni_t2 pr) in
  eqdl_verifyb N g h u v (ni_t1 pr) (ni_t2 pr) c (ni_z pr).

Lemma eqdl_verifyb_iff :
  forall N g h u v t1 t2 c z,
    eqdl_verifyb N g h u v t1 t2 c z = true <->
    eqdl_verify N g h u v t1 t2 c z.
Proof.
  intros. unfold eqdl_verifyb, eqdl_verify.
  rewrite andb_true_iff, !Z.eqb_eq.
  reflexivity.
Qed.

Lemma fs_eqdl_verifyb_iff :
  forall N g h u v pr,
    fs_eqdl_verifyb N g h u v pr = true <->
    fs_eqdl_verify N g h u v pr.
Proof.
  intros. unfold fs_eqdl_verifyb, fs_eqdl_verify.
  apply eqdl_verifyb_iff.
Qed.

Theorem fs_eqdl_complete :
  forall N g u tau w,
    1 < N ->
    0 <= tau ->
    0 <= w ->
    fs_eqdl_verify N g (powm g tau N) u (powm u tau N)
      (fs_eqdl_prove N g u tau w).
Proof.
  intros N g u tau w Hn Ht Hw.
  unfold fs_eqdl_verify, fs_eqdl_prove.
  simpl.
  apply eqdl_complete; try assumption.
  apply fs_eqdl_challenge_nonneg; exact Hn.
Qed.

Theorem fs_eqdl_complete_b :
  forall N g u tau w,
    1 < N ->
    0 <= tau ->
    0 <= w ->
    fs_eqdl_verifyb N g (powm g tau N) u (powm u tau N)
      (fs_eqdl_prove N g u tau w) = true.
Proof.
  intros N g u tau w Hn Ht Hw.
  apply fs_eqdl_verifyb_iff.
  apply fs_eqdl_complete; assumption.
Qed.

(** ** Slot Sigma of the proving system *)

Theorem fs_slot_complete :
  forall N g tau i a s,
    1 < N ->
    0 <= tau ->
    0 <= i ->
    0 <= a ->
    0 <= s ->
    let Pi := pot N g tau i in
    let Qi := coeff_slot N g tau i a in
    fs_eqdl_verify N Pi Qi Pi Qi (fs_eqdl_prove N Pi Pi a s).
Proof.
  intros N g tau i a s Hn Ht Hi Ha Hs Pi Qi.
  subst Pi Qi.
  unfold coeff_slot.
  apply fs_eqdl_complete; assumption.
Qed.

Theorem fs_wire_complete :
  forall N g tau A w s,
    1 < N ->
    0 <= w ->
    0 <= s ->
    let U := pot_poly N g tau A in
    let Q := wire_slot N g tau A w in
    fs_eqdl_verify N U Q U Q (fs_eqdl_prove N U U w s).
Proof.
  intros N g tau A w s Hn Hw Hs U Q.
  subst U Q.
  unfold wire_slot.
  apply fs_eqdl_complete; assumption.
Qed.

(** ** Representative pin: challenge depends on the first message *)

Definition pin_g : Z := 3.
Definition pin_tau : Z := 5.
Definition pin_a : Z := 3.
Definition pin_s : Z := 4.
Definition pin_s2 : Z := 7.
Definition pin_P : Z := pot pin_N pin_g pin_tau 1.
Definition pin_Q : Z := powm pin_P pin_a pin_N.
Definition pin_pr : ni_eqdl :=
  fs_eqdl_prove pin_N pin_P pin_P pin_a pin_s.
Definition pin_pr2 : ni_eqdl :=
  fs_eqdl_prove pin_N pin_P pin_P pin_a pin_s2.

Theorem fs_pin_accepts :
  fs_eqdl_verifyb pin_N pin_P pin_Q pin_P pin_Q pin_pr = true.
Proof. vm_compute. reflexivity. Qed.

Theorem fs_pin_rejects_wrong_challenge :
  let c := fs_eqdl_challenge pin_N pin_P pin_Q pin_P pin_Q
             (ni_t1 pin_pr) (ni_t2 pin_pr) in
  let pr_bad := {| ni_t1 := ni_t1 pin_pr;
                   ni_t2 := ni_t2 pin_pr;
                   ni_z := eqdl_response pin_s (c + 1) pin_a |} in
  fs_eqdl_verifyb pin_N pin_P pin_Q pin_P pin_Q pr_bad = false.
Proof. vm_compute. reflexivity. Qed.

Theorem fs_pin_challenge_depends_on_commit :
  fs_eqdl_challenge pin_N pin_P pin_Q pin_P pin_Q
    (ni_t1 pin_pr) (ni_t2 pin_pr) <>
  fs_eqdl_challenge pin_N pin_P pin_Q pin_P pin_Q
    (ni_t1 pin_pr2) (ni_t2 pin_pr2).
Proof. vm_compute. discriminate. Qed.

Theorem fs_pin_second_accepts :
  fs_eqdl_verifyb pin_N pin_P pin_Q pin_P pin_Q pin_pr2 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem fs_pin_commits_distinct :
  ni_t1 pin_pr <> ni_t1 pin_pr2.
Proof. vm_compute. discriminate. Qed.
