From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import PowersOfTau.
Require Import EvalProduct.
Require Import CoeffPoK.
Require Import QAP.

Open Scope Z_scope.

(** * Public quadratic check of two committed evaluations

    [qap_complete_at_tau] needs the coefficient lists.
    [pot_poly_conv_raise] needs the integer [h(τ)].
    [self_bil_committed_product] needs an unspecified [e].
    None of those is a check a verifier can run on encodings.

    This file ships one.  Extra slot encodings [Q_i = P_i^{a_i}]
    sit next to the CRS [P_i = g^{τ^i}].  A bounded search on
    those *public* bases recovers the coefficients (not from [τ],
    not from [C_A] as a discrete log).  The bilinear combine
    [∏_{i,j} P_{i+j}^{a_i b_j}] is then a group product of CRS
    slots and equals [g^{(a·b)(τ)}].  Inputs of the check are
    [N], the CRS, [C_A], [C_B], [C_{AB}], the slot encodings, and
    a public bound — no coefficient vector, no [τ], no [h(τ)].

    Completeness is for honest slot encodings whose coefficients
    lie in [[0, bound)] and are the least such exponents.  The
    search reveals those coefficients: this is not a hiding
    pairing and not a NIZK.  Group multiplication of [C_A] and
    [C_B] encodes the *sum* and is rejected on the representative
    pin where sum and product encodings differ.

    Cross-confirmed by [cas/112_public_quad.gp]. *)

(** ** Bounded exponent search against a public base *)

Fixpoint find_exp_from (N P Q k : Z) (fuel : nat) : option Z :=
  match fuel with
  | O => None
  | S fuel' =>
      if powm P k N =? Q then Some k
      else find_exp_from N P Q (k + 1) fuel'
  end.

Definition find_exp (N P Q bound : Z) : option Z :=
  find_exp_from N P Q 0 (Z.to_nat bound).

Lemma find_exp_from_sound :
  forall N P Q k fuel a,
    find_exp_from N P Q k fuel = Some a ->
    k <= a /\
    a < k + Z.of_nat fuel /\
    powm P a N = Q /\
    (forall j, k <= j < a -> powm P j N <> Q).
Proof.
  intros N P Q k fuel.
  revert k.
  induction fuel as [|fuel' IH]; intros k a Hfind.
  - simpl in Hfind. discriminate.
  - simpl in Hfind.
    destruct (Z.eqb_spec (powm P k N) Q) as [Heq | Hne].
    + inversion Hfind. subst a.
      split; [lia|].
      split; [lia|].
      split; [exact Heq|].
      intros j Hj. lia.
    + specialize (IH (k + 1) a Hfind).
      destruct IH as [Hka [Hak [Hpow Huniq]]].
      split; [lia|].
      split; [lia|].
      split; [exact Hpow|].
      intros j Hj.
      destruct (Z.eq_dec j k) as [Hjk | Hjneq].
      * subst j. exact Hne.
      * apply Huniq. lia.
Qed.

Lemma find_exp_from_complete :
  forall N P Q k fuel a,
    k <= a ->
    a < k + Z.of_nat fuel ->
    powm P a N = Q ->
    (forall j, k <= j < a -> powm P j N <> Q) ->
    find_exp_from N P Q k fuel = Some a.
Proof.
  intros N P Q k fuel.
  revert k.
  induction fuel as [|fuel' IH]; intros k a Hka Hak Hpow Huniq.
  - simpl. lia.
  - simpl.
    destruct (Z.eqb_spec (powm P k N) Q) as [Heq | Hne].
    + f_equal.
      destruct (Z.eq_dec k a) as [Hkaeq | Hkane].
      * exact Hkaeq.
      * exfalso. apply (Huniq k); [lia|exact Heq].
    + assert (k <> a) by (intro Heqka; subst a; contradiction).
      apply IH; try lia; try exact Hpow.
      intros j Hj. apply Huniq. lia.
Qed.

Lemma find_exp_complete :
  forall N P Q bound a,
    0 <= a < bound ->
    powm P a N = Q ->
    (forall j, 0 <= j < a -> powm P j N <> Q) ->
    find_exp N P Q bound = Some a.
Proof.
  intros N P Q bound a Hab Hpow Huniq.
  unfold find_exp.
  apply find_exp_from_complete.
  - lia.
  - rewrite Z2Nat.id by lia. lia.
  - exact Hpow.
  - intros j Hj. apply Huniq. lia.
Qed.

Lemma find_exp_sound :
  forall N P Q bound a,
    find_exp N P Q bound = Some a ->
    0 <= a < Z.of_nat (Z.to_nat bound) /\
    powm P a N = Q /\
    (forall j, 0 <= j < a -> powm P j N <> Q).
Proof.
  intros N P Q bound a Hfind.
  unfold find_exp in Hfind.
  pose proof (find_exp_from_sound N P Q 0 (Z.to_nat bound) a Hfind) as H.
  destruct H as [H0 [H1 [H2 H3]]].
  split; [lia|].
  split; [exact H2|].
  intros j Hj. apply H3. lia.
Qed.

(** ** Recover a coefficient list from slot encodings vs CRS *)

Fixpoint recover_exps (N : Z) (Ps Qs : list Z) (bound : Z) {struct Qs}
  : option (list Z) :=
  match Qs with
  | nil => Some nil
  | Q :: Qrest =>
      match Ps with
      | nil => None
      | P :: Prest =>
          match find_exp N P Q bound with
          | None => None
          | Some k =>
              match recover_exps N Prest Qrest bound with
              | None => None
              | Some rest => Some (k :: rest)
              end
          end
      end
  end.

(** ** Public CRS list [P_0,…,P_{n-1}] *)

Fixpoint pot_crs_from (N g tau : Z) (i n : nat) : list Z :=
  match n with
  | O => nil
  | S n' => pot N g tau (Z.of_nat i) :: pot_crs_from N g tau (S i) n'
  end.

Definition pot_crs (N g tau : Z) (n : nat) : list Z :=
  pot_crs_from N g tau 0 n.

Lemma pot_crs_from_length :
  forall N g tau i n,
    length (pot_crs_from N g tau i n) = n.
Proof.
  intros N g tau i n.
  revert i.
  induction n as [|n IH]; intros i; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma pot_crs_length :
  forall N g tau n,
    length (pot_crs N g tau n) = n.
Proof.
  intros. unfold pot_crs. apply pot_crs_from_length.
Qed.

Lemma pot_crs_from_nth :
  forall N g tau i n k d,
    (k < n)%nat ->
    nth k (pot_crs_from N g tau i n) d =
      pot N g tau (Z.of_nat (i + k)%nat).
Proof.
  intros N g tau i n.
  revert i.
  induction n as [|n IH]; intros i k d Hk.
  - lia.
  - simpl.
    destruct k as [|k']; simpl.
    + f_equal. rewrite Nat.add_0_r. reflexivity.
    + rewrite IH by lia.
      f_equal. f_equal. lia.
Qed.

Lemma pot_crs_nth :
  forall N g tau n k d,
    (k < n)%nat ->
    nth k (pot_crs N g tau n) d = pot N g tau (Z.of_nat k).
Proof.
  intros N g tau n k d Hk.
  unfold pot_crs.
  rewrite pot_crs_from_nth by exact Hk.
  reflexivity.
Qed.

(** Least-exponent uniqueness of each honest coefficient vs its
    public CRS slot. *)

Fixpoint first_exps (N g tau bound : Z) (cs : list Z) (i : nat) : Prop :=
  match cs with
  | nil => True
  | a :: rest =>
      0 <= a < bound /\
      (forall k, 0 <= k < a ->
         powm (pot N g tau (Z.of_nat i)) k N <>
         powm (pot N g tau (Z.of_nat i)) a N) /\
      first_exps N g tau bound rest (S i)
  end.

Lemma recover_honest :
  forall N g tau bound cs i n,
    1 < N ->
    0 <= tau ->
    first_exps N g tau bound cs i ->
    (length cs <= n)%nat ->
    recover_exps N (pot_crs_from N g tau i n)
      (coeff_slots N g tau cs i) bound = Some cs.
Proof.
  intros N g tau bound cs.
  induction cs as [|a rest IH]; intros i n Hn Ht Hfirst Hlen.
  - simpl. reflexivity.
  - destruct n as [|n']; [simpl in Hlen; lia|].
    simpl in Hfirst.
    destruct Hfirst as [Hab [Huniq Hrest]].
    simpl.
    assert (find_exp N (pot N g tau (Z.of_nat i))
              (coeff_slot N g tau (Z.of_nat i) a) bound = Some a)
      as Hfound.
    { apply find_exp_complete.
      - exact Hab.
      - unfold coeff_slot. reflexivity.
      - intros k Hk. unfold coeff_slot. apply Huniq. exact Hk. }
    rewrite Hfound.
    rewrite (IH (S i) n' Hn Ht Hrest) by (simpl in Hlen; lia).
    reflexivity.
Qed.

(** ** Bilinear combine [∏_{i,j} P_{i+j}^{a_i b_j}] *)

Fixpoint quad_row (N : Z) (Ps : list Z) (ai : Z) (bb : list Z)
    (i j : nat) {struct bb} : Z :=
  match bb with
  | nil => 1 mod N
  | bj :: rest =>
      (powm (nth (i + j)%nat Ps 0) (ai * bj) N *
         quad_row N Ps ai rest i (S j)) mod N
  end.

Fixpoint quad_combine (N : Z) (Ps as_ bs : list Z) (i : nat) {struct as_} : Z :=
  match as_ with
  | nil => 1 mod N
  | ai :: rest =>
      (quad_row N Ps ai bs i 0%nat *
         quad_combine N Ps rest bs (S i)) mod N
  end.

Lemma quad_row_spec :
  forall N g tau n ai bb i j,
    1 < N ->
    0 <= tau ->
    0 <= ai ->
    nn bb ->
    (i + j + length bb <= n)%nat ->
    quad_row N (pot_crs N g tau n) ai bb i j =
      powm g (ai * poly_eval bb tau * tau ^ Z.of_nat (i + j)%nat) N.
Proof.
  intros N g tau n ai bb i j Hn Ht Hai Hnn.
  revert j.
  induction Hnn as [|bj rest Hbj Hrest IH]; intros j Hlen.
  - simpl.
    replace (ai * 0 * tau ^ Z.of_nat (i + j)%nat) with 0 by lia.
    symmetry. apply powm_0_r. lia.
  - simpl.
    assert ((i + j < n)%nat) as Hlt by (simpl in Hlen; lia).
    rewrite pot_crs_nth by exact Hlt.
    unfold pot.
    assert (0 <= tau ^ Z.of_nat (i + j)%nat) by (apply Z.pow_nonneg; lia).
    assert (0 <= ai * bj) by nia.
    rewrite <- powm_mul_r by lia.
    rewrite (IH (S j)) by (simpl in Hlen; lia).
    assert (0 <= poly_eval rest tau) by (apply poly_eval_nonneg; assumption).
    assert (0 <= tau ^ Z.of_nat (i + S j)%nat) by (apply Z.pow_nonneg; lia).
    assert (0 <= ai * bj * tau ^ Z.of_nat (i + j)%nat) by nia.
    assert (0 <= ai * poly_eval rest tau * tau ^ Z.of_nat (i + S j)%nat)
      by nia.
    rewrite <- powm_add_r by lia.
    f_equal.
    rewrite Nat.add_succ_r, Nat2Z.inj_succ, Z.pow_succ_r
      by (apply Nat2Z.is_nonneg || lia).
    ring.
Qed.

Lemma quad_combine_spec :
  forall N g tau n aa bb i,
    1 < N ->
    0 <= tau ->
    nn aa ->
    nn bb ->
    (i + length aa + length bb <= n)%nat ->
    quad_combine N (pot_crs N g tau n) aa bb i =
      powm g (poly_eval aa tau * poly_eval bb tau *
                tau ^ Z.of_nat i) N.
Proof.
  intros N g tau n aa bb i Hn Ht Haa Hbb.
  revert i.
  induction Haa as [|ai rest Hai Hrest IH]; intros i Hlen.
  - simpl.
    replace (0 * poly_eval bb tau * tau ^ Z.of_nat i) with 0 by lia.
    symmetry. apply powm_0_r. lia.
  - simpl.
    rewrite (quad_row_spec N g tau n ai bb i 0%nat)
      by (try assumption; simpl in Hlen; lia).
    rewrite Nat.add_0_r.
    rewrite (IH (S i)) by (simpl in Hlen; lia).
    assert (0 <= poly_eval rest tau) by (apply poly_eval_nonneg; assumption).
    assert (0 <= poly_eval bb tau) by (apply poly_eval_nonneg; assumption).
    assert (0 <= tau ^ Z.of_nat i) by (apply Z.pow_nonneg; lia).
    assert (0 <= tau ^ Z.of_nat (S i)) by (apply Z.pow_nonneg; lia).
    assert (0 <= ai * poly_eval bb tau * tau ^ Z.of_nat i) by nia.
    assert (0 <= poly_eval rest tau * poly_eval bb tau * tau ^ Z.of_nat (S i))
      by nia.
    rewrite <- powm_add_r by lia.
    f_equal.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by (apply Nat2Z.is_nonneg || lia).
    ring.
Qed.

Theorem quad_combine_is_product :
  forall N g tau a b,
    1 < N ->
    0 <= tau ->
    nn a ->
    nn b ->
    quad_combine N (pot_crs N g tau (length a + length b)%nat) a b 0%nat =
      pot_poly N g tau (poly_conv a b).
Proof.
  intros N g tau a b Hn Ht Ha Hb.
  unfold pot_poly.
  rewrite (quad_combine_spec N g tau (length a + length b)%nat a b 0%nat);
    try assumption; try lia.
  rewrite poly_eval_conv, Z.pow_0_r, Z.mul_1_r.
  reflexivity.
Qed.

(** ** The public check: encodings and CRS only *)

Definition public_quad_check
    (N : Z) (Ps : list Z) (CA CB CAB : Z)
    (QA QB : list Z) (bound : Z) : bool :=
  match recover_exps N Ps QA bound, recover_exps N Ps QB bound with
  | Some as_, Some bs =>
      (gprod N QA =? CA) &&
      (gprod N QB =? CB) &&
      (quad_combine N Ps as_ bs 0%nat =? CAB)
  | _, _ => false
  end.

Lemma first_exps_nn :
  forall N g tau bound cs i,
    first_exps N g tau bound cs i ->
    nn cs.
Proof.
  intros N g tau bound cs.
  induction cs as [|a rest IH]; intros i H.
  - constructor.
  - simpl in H. destruct H as [Hab [_ Hrest]].
    constructor; [lia|]. apply (IH (S i)). exact Hrest.
Qed.

Theorem public_quad_complete :
  forall N g tau a b bound,
    1 < N ->
    0 <= tau ->
    nn a ->
    nn b ->
    first_exps N g tau bound a 0%nat ->
    first_exps N g tau bound b 0%nat ->
    public_quad_check N
      (pot_crs N g tau (length a + length b)%nat)
      (pot_poly N g tau a)
      (pot_poly N g tau b)
      (pot_poly N g tau (poly_conv a b))
      (coeff_slots N g tau a 0)
      (coeff_slots N g tau b 0)
      bound = true.
Proof.
  intros N g tau a b bound Hn Ht Ha Hb Hfa Hfb.
  unfold public_quad_check, pot_crs.
  rewrite (recover_honest N g tau bound a 0 (length a + length b)%nat)
    by (try assumption; lia).
  rewrite (recover_honest N g tau bound b 0 (length a + length b)%nat)
    by (try assumption; lia).
  apply andb_true_iff. split.
  - apply andb_true_iff. split.
    + apply Z.eqb_eq. apply slots_assemble; assumption.
    + apply Z.eqb_eq. apply slots_assemble; assumption.
  - apply Z.eqb_eq. apply quad_combine_is_product; assumption.
Qed.

Theorem public_quad_qap :
  forall N g tau A B C H van bound,
    1 < N ->
    0 <= tau ->
    nn A ->
    nn B ->
    first_exps N g tau bound A 0%nat ->
    first_exps N g tau bound B 0%nat ->
    qap_at A B C H van tau ->
    0 <= poly_eval C tau ->
    0 <= poly_eval (poly_conv H van) tau ->
    public_quad_check N
      (pot_crs N g tau (length A + length B)%nat)
      (pot_poly N g tau A)
      (pot_poly N g tau B)
      ((pot_poly N g tau C *
          pot_poly N g tau (poly_conv H van)) mod N)
      (coeff_slots N g tau A 0)
      (coeff_slots N g tau B 0)
      bound = true.
Proof.
  intros N g tau A B C H van bound Hn Ht HA HB HfA HfB Hq HC HHZ.
  rewrite <- (qap_complete_at_tau N g tau A B C H van Hn Hq HC HHZ).
  apply public_quad_complete; assumption.
Qed.

(** ** Representative pin: the check is not the group law *)

Definition pin_N : Z := 11 * 17.
Definition pin_g : Z := 3.
Definition pin_tau : Z := 5.
Definition pin_bound : Z := 5.
Definition pin_a : list Z := [2; 3].
Definition pin_b : list Z := [1; 4].

Theorem public_quad_pin_accepts :
  public_quad_check pin_N
    (pot_crs pin_N pin_g pin_tau (length pin_a + length pin_b)%nat)
    (pot_poly pin_N pin_g pin_tau pin_a)
    (pot_poly pin_N pin_g pin_tau pin_b)
    (pot_poly pin_N pin_g pin_tau (poly_conv pin_a pin_b))
    (coeff_slots pin_N pin_g pin_tau pin_a 0)
    (coeff_slots pin_N pin_g pin_tau pin_b 0)
    pin_bound = true.
Proof. vm_compute. reflexivity. Qed.

Theorem public_quad_pin_rejects_group_mul :
  public_quad_check pin_N
    (pot_crs pin_N pin_g pin_tau (length pin_a + length pin_b)%nat)
    (pot_poly pin_N pin_g pin_tau pin_a)
    (pot_poly pin_N pin_g pin_tau pin_b)
    ((pot_poly pin_N pin_g pin_tau pin_a *
        pot_poly pin_N pin_g pin_tau pin_b) mod pin_N)
    (coeff_slots pin_N pin_g pin_tau pin_a 0)
    (coeff_slots pin_N pin_g pin_tau pin_b 0)
    pin_bound = false.
Proof. vm_compute. reflexivity. Qed.

Theorem public_quad_pin_sum_neq_prod :
  (pot_poly pin_N pin_g pin_tau pin_a *
     pot_poly pin_N pin_g pin_tau pin_b) mod pin_N <>
    pot_poly pin_N pin_g pin_tau (poly_conv pin_a pin_b).
Proof. vm_compute. discriminate. Qed.

Theorem public_quad_pin_qap :
  let A := [1; 1] in
  let B := [2] in
  let C := [2; 2] in
  let Hh := [0] in
  let van := [0; 1] in
  public_quad_check pin_N
    (pot_crs pin_N pin_g pin_tau (length A + length B)%nat)
    (pot_poly pin_N pin_g pin_tau A)
    (pot_poly pin_N pin_g pin_tau B)
    ((pot_poly pin_N pin_g pin_tau C *
        pot_poly pin_N pin_g pin_tau (poly_conv Hh van)) mod pin_N)
    (coeff_slots pin_N pin_g pin_tau A 0)
    (coeff_slots pin_N pin_g pin_tau B 0)
    pin_bound = true.
Proof. vm_compute. reflexivity. Qed.
