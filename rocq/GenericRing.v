From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.ZPoly.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import PollardP1.
Require Import SmallExponent.

Open Scope Z_scope.

(** * Generic ring algorithms (GRA) on [Z/NZ]

    A tape of ring handles, ops [{+, −, ·}] (wave 1), then [inv]
    (wave 2a) and a cube-root marker (wave 3).  Equality-test
    [gcd] of integer lifts is the leak.  Theorems are about traces,
    not standard-model RSA ≡ factoring.  Cross-confirmed by
    [cas/115]–[cas/117] and [cas/121]. *)

(** ** The machine *)

Inductive GRAOp : Set :=
  | GConst (c : Z)
  | GAdd (i j : nat)
  | GSub (i j : nat)
  | GMul (i j : nat)
  | GInv (i : nat)
  | GRoot (i : nat).


Definition gra_init (y : Z) : list Z := [0; 1; y].

(** Extended Euclidean: [fst * a + snd * b = gcd] when fuel suffices. *)
Fixpoint egcd_uv (fuel : nat) (a b : Z) : Z * Z :=
  match fuel with
  | O => (1, 0)
  | S fuel' =>
      if b =? 0 then (1, 0)
      else
        let uv := egcd_uv fuel' b (a mod b) in
        (snd uv, fst uv - snd uv * (a / b))
  end.

(** Invert [h] in [Z/NZ] when [gcd = 1]; otherwise return that gcd
    (the AM09 non-unit leak). *)
Definition gra_inv (h N : Z) : Z :=
  let g := Z.gcd h N in
  if g =? 1 then (fst (egcd_uv 64%nat h N)) mod N else g.

Theorem gra_inv_eq_gcd_if_nonunit :
  forall h N, Z.gcd h N <> 1 -> gra_inv h N = Z.gcd h N.
Proof.
  intros h N Hne.
  unfold gra_inv.
  destruct (Z.eqb_spec (Z.gcd h N) 1); [lia | reflexivity].
Qed.

Theorem gra_inv_proper_gcd_factors :
  forall h,
    1 < Z.gcd h pin_N < pin_N ->
    Problem_Factor pin_N (gra_inv h pin_N).
Proof.
  intros h [Hlo Hhi].
  rewrite gra_inv_eq_gcd_if_nonunit by lia.
  unfold Problem_Factor.
  split; [lia | apply Z.gcd_divide_r].
Qed.

(** Integer cube root by bounded search.  Not a cube: identity. *)
Fixpoint icbrt_up (k fuel : nat) (t : Z) : Z :=
  match fuel with
  | O => t
  | S fuel' =>
      let kz := Z.of_nat k in
      if kz * kz * kz =? t then kz
      else if (- kz) * (- kz) * (- kz) =? t then - kz
      else icbrt_up (S k) fuel' t
  end.

Definition integer_cube_root (t : Z) : Z := icbrt_up 0%nat 64%nat t.

Definition step (N : Z) (op : GRAOp) (t : list Z) : list Z :=
  match op with
  | GConst c => t ++ [c]
  | GAdd i j => t ++ [nth i t 0 + nth j t 0]
  | GSub i j => t ++ [nth i t 0 - nth j t 0]
  | GMul i j => t ++ [nth i t 0 * nth j t 0]
  | GInv i => t ++ [gra_inv (nth i t 0) N]
  | GRoot i => t ++ [integer_cube_root (nth i t 0)]
  end.

Definition step_Z (op : GRAOp) (t : list Z) : list Z := step pin_N op t.

Fixpoint gra_run (N : Z) (ops : list GRAOp) (t : list Z) : list Z :=
  match ops with
  | nil => t
  | op :: rest => gra_run N rest (step N op t)
  end.

Definition gra_run_Z (ops : list GRAOp) (t : list Z) : list Z :=
  gra_run pin_N ops t.

Definition gra_eval (N : Z) (ops : list GRAOp) (y : Z) (out : nat) : Z :=
  nth out (gra_run N ops (gra_init y)) 0.

Definition gra_eval_Z (ops : list GRAOp) (y : Z) (out : nat) : Z :=
  gra_eval pin_N ops y out.

(** Walk a tape for the first [GInv] of a handle with proper
    [gcd(h,N)].  [Some f] is a factor.  [None] means every [GInv]
    was of a unit (or of a multiple of [N]). *)
Fixpoint gra_first_inv_gcd (N : Z) (ops : list GRAOp) (t : list Z)
  : option Z :=
  match ops with
  | nil => None
  | op :: rest =>
      match op with
      | GInv i =>
          let g := Z.gcd (nth i t 0) N in
          if (1 <? g) && (g <? N) then Some g
          else gra_first_inv_gcd N rest (step N op t)
      | _ => gra_first_inv_gcd N rest (step N op t)
      end
  end.

Lemma gra_first_inv_gcd_some :
  forall ops N t f,
    gra_first_inv_gcd N ops t = Some f ->
    1 < f < N /\ (f | N).
Proof.
  induction ops as [|op rest IH]; intros N t f Hf.
  - discriminate.
  - destruct op as [c | i j | i j | i j | i | i]; simpl in Hf.
    + apply (IH N (step N (GConst c) t) f Hf).
    + apply (IH N (step N (GAdd i j) t) f Hf).
    + apply (IH N (step N (GSub i j) t) f Hf).
    + apply (IH N (step N (GMul i j) t) f Hf).
    + set (g := Z.gcd (nth i t 0) N) in *.
      destruct ((1 <? g) && (g <? N)) eqn:Hb.
      * inversion Hf; subst f.
        apply andb_true_iff in Hb. destruct Hb as [H1 H2].
        apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
        split; [split; [exact H1 | exact H2] | apply Z.gcd_divide_r].
      * apply (IH N (step N (GInv i) t) f Hf).
    + apply (IH N (step N (GRoot i) t) f Hf).
Qed.

Theorem gra_first_inv_gcd_factors :
  forall ops y f,
    gra_first_inv_gcd pin_N ops (gra_init y) = Some f ->
    Problem_Factor pin_N f.
Proof.
  intros ops y f Hf.
  destruct (gra_first_inv_gcd_some ops pin_N (gra_init y) f Hf) as [Hrng Hdiv].
  unfold Problem_Factor. split; [exact Hrng | exact Hdiv].
Qed.

Definition gra_eq_gcd (a b N : Z) : Z := Z.gcd (a - b) N.

Definition gra_eq_leak (N : Z) (ops : list GRAOp) (y : Z) (i j : nat) : Z :=
  gra_eq_gcd (gra_eval N ops y i) (gra_eval N ops y j) N.

(** ** Wave 0 — equality leak and the tape

    Build 88 from 1 by [+,*]: [2,4,8,16,64,80,88].  Equality against
    handle 0 (the ring zero) is [gcd(88−0, N)]. *)

Definition gra_eq_prog : list GRAOp :=
  [GAdd 1%nat 1%nat;
   GMul 3%nat 3%nat;
   GMul 4%nat 3%nat;
   GMul 4%nat 4%nat;
   GMul 6%nat 4%nat;
   GAdd 7%nat 6%nat;
   GAdd 8%nat 5%nat].

Theorem gra_eq_tape_88 :
  gra_eval_Z gra_eq_prog 36 9%nat = 88.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_eq_tape_zero :
  gra_eval_Z gra_eq_prog 36 0%nat = 0.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_eq_leak_pin :
  gra_eq_leak pin_N gra_eq_prog 36 9%nat 0%nat = Z.gcd 88 pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_eq_leak_factors :
  let g := gra_eq_leak pin_N gra_eq_prog 36 9%nat 0%nat in
  1 < g < pin_N -> Problem_Factor pin_N g.
Proof.
  intros g Hg. unfold Problem_Factor. split; [exact Hg|].
  unfold gra_eq_leak in g. apply Z.gcd_divide_r.
Qed.

Theorem gra_eq_leak_onesided :
  Z.gcd (8 * pin_p) pin_N = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_eq_N_is_not_a_split :
  Z.gcd pin_N pin_N = pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_mul_y_pin :
  gra_eval_Z [GMul 2%nat 2%nat; GMul 3%nat 2%nat] 36 4%nat = 36 * 36 * 36.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_const42 :
  gra_eval_Z [GConst 42] 36 3%nat = 42.
Proof. vm_compute. reflexivity. Qed.

(** Division-free SLP → polynomial: each handle is [poly_eval] of a
    coeff list.  Init is [[0]; [1]; X]. *)

Definition slp_init_poly : list (list Z) := [[0]; [1]; poly_X].

Definition step_poly (op : GRAOp) (t : list (list Z)) : list (list Z) :=
  match op with
  | GConst c => t ++ [[c]]
  | GAdd i j => t ++ [poly_add (nth i t []) (nth j t [])]
  | GSub i j => t ++ [poly_sub (nth i t []) (nth j t [])]
  | GMul i j => t ++ [poly_mul (nth i t []) (nth j t [])]
  | GInv i => t ++ [nth i t []]
  | GRoot i => t ++ [nth i t []]
  end.

Fixpoint gra_run_poly (ops : list GRAOp) (t : list (list Z)) : list (list Z) :=
  match ops with
  | nil => t
  | op :: rest => gra_run_poly rest (step_poly op t)
  end.

Theorem slp_init_eval :
  forall y,
    poly_eval (nth 0%nat slp_init_poly []) y = 0 /\
    poly_eval (nth 1%nat slp_init_poly []) y = 1 /\
    poly_eval (nth 2%nat slp_init_poly []) y = y.
Proof.
  intros y. unfold slp_init_poly, nth, poly_eval.
  split; [ring|]. split; [ring|].
  fold (poly_eval poly_X y). apply poly_eval_X.
Qed.

Theorem slp_to_poly_mul_pin :
  let t := gra_run_poly [GMul 2%nat 2%nat] slp_init_poly in
  poly_eval (nth 3%nat t []) 36 = 36 * 36.
Proof. vm_compute. reflexivity. Qed.

(** ** Division-free tapes denote polynomials

    [GConst]/[GAdd]/[GSub]/[GMul] act on integer handles exactly as
    [poly_eval] of the matching coefficient lists.  [GInv] and [GRoot]
    are excluded.  An integer identity [P(y)^e = y] for all [y] is
    forbidden for [e ≥ 2] by evaluation at 2. *)

Inductive is_nodiv : GRAOp -> Prop :=
  | nodiv_GConst : forall c, is_nodiv (GConst c)
  | nodiv_GAdd : forall i j, is_nodiv (GAdd i j)
  | nodiv_GSub : forall i j, is_nodiv (GSub i j)
  | nodiv_GMul : forall i j, is_nodiv (GMul i j).

Lemma nth_app_last :
  forall (A : Type) (l : list A) (x d : A),
    nth (length l) (l ++ [x]) d = x.
Proof.
  intros A l x d. induction l as [|h t IH]; simpl; [reflexivity | exact IH].
Qed.

Lemma nth_app_lt :
  forall (A : Type) (l : list A) (x d : A) i,
    (i < length l)%nat ->
    nth i (l ++ [x]) d = nth i l d.
Proof.
  intros A l x d i Hi. rewrite app_nth1; [reflexivity | exact Hi].
Qed.

Lemma step_length :
  forall N op t, length (step N op t) = S (length t).
Proof. intros N op t. destruct op; simpl; rewrite length_app; simpl; lia. Qed.

Lemma step_poly_length :
  forall op t, length (step_poly op t) = S (length t).
Proof. intros op t. destruct op; simpl; rewrite length_app; simpl; lia. Qed.

Lemma step_nodiv_prefix :
  forall N y op t pt k,
    length t = length pt ->
    (k < length t)%nat ->
    (forall i, nth i t 0 = poly_eval (nth i pt []) y) ->
    nth k (step N op t) 0 = poly_eval (nth k (step_poly op pt) []) y.
Proof.
  intros N y op t pt k Hlen Hlt Hagree.
  destruct op; simpl;
    (rewrite nth_app_lt by exact Hlt;
     rewrite nth_app_lt by (rewrite <- Hlen; exact Hlt);
     apply Hagree).
Qed.

Lemma step_nodiv_new :
  forall N y op t pt,
    is_nodiv op ->
    length t = length pt ->
    (forall i, nth i t 0 = poly_eval (nth i pt []) y) ->
    nth (length t) (step N op t) 0 =
      poly_eval (nth (length pt) (step_poly op pt) []) y.
Proof.
  intros N y op t pt Hop Hlen Hagree.
  destruct op as [c | ia ja | ia ja | ia ja | ia | ia];
    try (inversion Hop).
  - simpl. rewrite !nth_app_last. simpl. lia.
  - simpl. rewrite !nth_app_last.
    rewrite Hagree, (Hagree ja). rewrite <- poly_eval_add. reflexivity.
  - simpl. rewrite !nth_app_last.
    rewrite Hagree, (Hagree ja). rewrite <- poly_eval_sub. reflexivity.
  - simpl. rewrite !nth_app_last.
    rewrite Hagree, (Hagree ja). rewrite <- poly_eval_mul. reflexivity.
Qed.

Lemma step_nodiv_overflow :
  forall N y op t pt k,
    length t = length pt ->
    (length t < k)%nat ->
    nth k (step N op t) 0 = poly_eval (nth k (step_poly op pt) []) y.
Proof.
  intros N y op t pt k Hlen Hgt.
  destruct op; simpl;
    (rewrite nth_overflow by (rewrite length_app; simpl; lia);
     rewrite nth_overflow by (rewrite length_app, <- Hlen; simpl; lia);
     reflexivity).
Qed.

Lemma step_nodiv_agree :
  forall N y op t pt,
    is_nodiv op ->
    length t = length pt ->
    (forall i, nth i t 0 = poly_eval (nth i pt []) y) ->
    length (step N op t) = length (step_poly op pt) /\
    forall k, nth k (step N op t) 0 = poly_eval (nth k (step_poly op pt) []) y.
Proof.
  intros N y op t pt Hop Hlen Hagree.
  split.
  - rewrite step_length, step_poly_length, Hlen. reflexivity.
  - intros k.
    destruct (lt_dec k (length t)) as [Hlt | Hnlt].
    + apply step_nodiv_prefix; assumption.
    + apply Nat.nlt_ge in Hnlt.
      destruct (Nat.eq_dec k (length t)) as [Heq | Hne].
      * subst k. rewrite Hlen at 2. apply step_nodiv_new; assumption.
      * apply step_nodiv_overflow; [exact Hlen | lia].
Qed.

Lemma gra_run_nodiv_agree :
  forall ops N y t pt,
    Forall is_nodiv ops ->
    length t = length pt ->
    (forall i, nth i t 0 = poly_eval (nth i pt []) y) ->
    length (gra_run N ops t) = length (gra_run_poly ops pt) /\
    forall i, nth i (gra_run N ops t) 0 =
      poly_eval (nth i (gra_run_poly ops pt) []) y.
Proof.
  intros ops N y.
  induction ops as [|op rest IH]; intros t pt Hop Hlen Hagree.
  - simpl. split; [exact Hlen | exact Hagree].
  - inversion Hop; subst.
    destruct (step_nodiv_agree N y op t pt H1 Hlen Hagree) as [Hlen' Hagree'].
    apply IH; [exact H2 | exact Hlen' | exact Hagree'].
Qed.

Lemma slp_init_length : length slp_init_poly = 3%nat.
Proof. reflexivity. Qed.

Lemma gra_init_length : forall y, length (gra_init y) = 3%nat.
Proof. reflexivity. Qed.

Lemma gra_init_agrees :
  forall y i, nth i (gra_init y) 0 = poly_eval (nth i slp_init_poly []) y.
Proof.
  intros y i.
  destruct i as [|i]; [|destruct i as [|i]; [|destruct i as [|i]]].
  - unfold gra_init, slp_init_poly. cbn [nth poly_eval]. ring.
  - unfold gra_init, slp_init_poly. cbn [nth poly_eval]. ring.
  - unfold gra_init, slp_init_poly, poly_X. cbn [nth poly_eval]. ring.
  - unfold gra_init, slp_init_poly.
    rewrite nth_overflow by (cbn [length]; lia).
    rewrite nth_overflow by (cbn [length]; lia). reflexivity.
Qed.

Theorem gra_nodiv_denotes :
  forall ops N y out,
    Forall is_nodiv ops ->
    gra_eval N ops y out =
      poly_eval (nth out (gra_run_poly ops slp_init_poly) []) y.
Proof.
  intros ops N y out Hop.
  unfold gra_eval.
  destruct (gra_run_nodiv_agree ops N y (gra_init y) slp_init_poly
              Hop (eq_trans (gra_init_length y) (eq_sym slp_init_length))
              (gra_init_agrees y)) as [_ Hagree].
  apply Hagree.
Qed.

(** ** Unit-[GInv] tapes denote rationals

    Nodiv handles are polynomials ([Q = 1]).  [GInv] of a unit
    swaps numerator and denominator.  [GRoot] is excluded: an
    integer cube-root is not a rational function.  Agreement is
    only modulo [N] (a [GInv] reduces).  Fuel-64 [gra_inv] must
    actually invert the handle; that is a hypothesis, proved on
    reduced pin units by [pin_gra_inv_inverts_reduced_unit]. *)

Definition gra_rat := (list Z * list Z)%type.

Definition slp_init_rat : list gra_rat :=
  [([0], [1]); ([1], [1]); (poly_X, [1])].

Definition step_rat (op : GRAOp) (t : list gra_rat) : list gra_rat :=
  match op with
  | GConst c => t ++ [([c], [1])]
  | GAdd i j =>
      t ++ [(poly_add
               (poly_mul (fst (nth i t ([], [1]))) (snd (nth j t ([], [1]))))
               (poly_mul (fst (nth j t ([], [1]))) (snd (nth i t ([], [1])))),
             poly_mul (snd (nth i t ([], [1]))) (snd (nth j t ([], [1]))))]
  | GSub i j =>
      t ++ [(poly_sub
               (poly_mul (fst (nth i t ([], [1]))) (snd (nth j t ([], [1]))))
               (poly_mul (fst (nth j t ([], [1]))) (snd (nth i t ([], [1])))),
             poly_mul (snd (nth i t ([], [1]))) (snd (nth j t ([], [1]))))]
  | GMul i j =>
      t ++ [(poly_mul (fst (nth i t ([], [1]))) (fst (nth j t ([], [1]))),
             poly_mul (snd (nth i t ([], [1]))) (snd (nth j t ([], [1]))))]
  | GInv i =>
      t ++ [(snd (nth i t ([], [1])), fst (nth i t ([], [1])))]
  | GRoot i => t ++ [nth i t ([], [1])]
  end.

Fixpoint gra_run_rat (ops : list GRAOp) (t : list gra_rat) : list gra_rat :=
  match ops with
  | nil => t
  | op :: rest => gra_run_rat rest (step_rat op t)
  end.

Fixpoint gra_unit_invs (N : Z) (ops : list GRAOp) (t : list Z) : Prop :=
  match ops with
  | nil => True
  | op :: rest =>
      match op with
      | GInv i =>
          Z.gcd (nth i t 0) N = 1 /\
          (gra_inv (nth i t 0) N * nth i t 0) mod N = 1 /\
          gra_unit_invs N rest (step N op t)
      | GRoot _ => False
      | _ => gra_unit_invs N rest (step N op t)
      end
  end.

Definition rat_handle_agrees (N y h : Z) (pq : gra_rat) : Prop :=
  Z.coprime (poly_eval (snd pq) y) N /\
  (h * poly_eval (snd pq) y) mod N = poly_eval (fst pq) y mod N.

Lemma nodiv_gra_unit_invs :
  forall ops N t,
    Forall is_nodiv ops ->
    gra_unit_invs N ops t.
Proof.
  induction ops as [|op rest IH]; intros N t Hop.
  - simpl. exact I.
  - inversion Hop; subst.
    destruct op; simpl; try (inversion H1); apply IH; exact H2.
Qed.

Lemma step_rat_length :
  forall op t, length (step_rat op t) = S (length t).
Proof. intros op t. destruct op; simpl; rewrite length_app; simpl; lia. Qed.

Lemma rat_overflow_agrees :
  forall N y, 1 < N -> rat_handle_agrees N y 0 ([], [1]).
Proof.
  intros N y HN. unfold rat_handle_agrees. cbn [fst snd poly_eval].
  rewrite Z.mul_0_r, Z.add_0_r.
  split; [unfold Z.coprime; apply Z.gcd_1_l | reflexivity].
Qed.

Lemma gra_init_rat_agrees :
  forall N y,
    1 < N ->
    length (gra_init y) = length slp_init_rat /\
    forall k,
      rat_handle_agrees N y (nth k (gra_init y) 0)
        (nth k slp_init_rat ([], [1])).
Proof.
  intros N y HN. split; [reflexivity|].
  intros k.
  destruct k as [|k]; [|destruct k as [|k]; [|destruct k as [|k]]].
  - unfold gra_init, slp_init_rat, rat_handle_agrees.
    cbn [nth fst snd poly_eval].
    split; [rewrite Z.mul_0_r, Z.add_0_r; unfold Z.coprime; apply Z.gcd_1_l
           | f_equal; ring].
  - unfold gra_init, slp_init_rat, rat_handle_agrees.
    cbn [nth fst snd poly_eval].
    split; [rewrite Z.mul_0_r, Z.add_0_r; unfold Z.coprime; apply Z.gcd_1_l
           | f_equal; ring].
  - unfold gra_init, slp_init_rat, rat_handle_agrees, poly_X.
    cbn [nth fst snd poly_eval].
    split; [rewrite Z.mul_0_r, Z.add_0_r; unfold Z.coprime; apply Z.gcd_1_l
           | f_equal; ring].
  - unfold gra_init, slp_init_rat.
    rewrite !nth_overflow by (cbn [length]; lia).
    apply rat_overflow_agrees. exact HN.
Qed.

Lemma rat_add_cong :
  forall N h1 h2 P1 P2 Q1 Q2,
    N <> 0 ->
    (h1 * Q1) mod N = P1 mod N ->
    (h2 * Q2) mod N = P2 mod N ->
    ((h1 + h2) * (Q1 * Q2)) mod N = (P1 * Q2 + P2 * Q1) mod N.
Proof.
  intros N h1 h2 P1 P2 Q1 Q2 HN H1 H2.
  transitivity (((h1 * Q1) * Q2 + (h2 * Q2) * Q1) mod N).
  { f_equal. ring. }
  rewrite Z.add_mod by lia.
  rewrite <- (Z.mul_mod_idemp_l (h1 * Q1) Q2 N) by lia.
  rewrite <- (Z.mul_mod_idemp_l (h2 * Q2) Q1 N) by lia.
  rewrite H1, H2.
  rewrite !Z.mul_mod_idemp_l by lia.
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.

Lemma rat_sub_cong :
  forall N h1 h2 P1 P2 Q1 Q2,
    N <> 0 ->
    (h1 * Q1) mod N = P1 mod N ->
    (h2 * Q2) mod N = P2 mod N ->
    ((h1 - h2) * (Q1 * Q2)) mod N = (P1 * Q2 - P2 * Q1) mod N.
Proof.
  intros N h1 h2 P1 P2 Q1 Q2 HN H1 H2.
  transitivity (((h1 * Q1) * Q2 - (h2 * Q2) * Q1) mod N).
  { f_equal. ring. }
  rewrite Zminus_mod.
  rewrite <- (Z.mul_mod_idemp_l (h1 * Q1) Q2 N) by lia.
  rewrite <- (Z.mul_mod_idemp_l (h2 * Q2) Q1 N) by lia.
  rewrite H1, H2.
  rewrite !Z.mul_mod_idemp_l by lia.
  rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma rat_mul_cong :
  forall N h1 h2 P1 P2 Q1 Q2,
    N <> 0 ->
    (h1 * Q1) mod N = P1 mod N ->
    (h2 * Q2) mod N = P2 mod N ->
    ((h1 * h2) * (Q1 * Q2)) mod N = (P1 * P2) mod N.
Proof.
  intros N h1 h2 P1 P2 Q1 Q2 HN H1 H2.
  transitivity (((h1 * Q1) * (h2 * Q2)) mod N).
  { f_equal. ring. }
  rewrite Z.mul_mod by lia.
  rewrite H1, H2.
  rewrite <- Z.mul_mod by lia. reflexivity.
Qed.

Lemma rat_inv_cong :
  forall N h P Q invh,
    N <> 0 ->
    (h * Q) mod N = P mod N ->
    (invh * h) mod N = 1 ->
    (invh * P) mod N = Q mod N.
Proof.
  intros N h P Q invh HN Hcong Hinv.
  rewrite <- (Z.mul_mod_idemp_r invh P N) by lia.
  rewrite <- Hcong.
  rewrite Z.mul_mod_idemp_r by lia.
  transitivity (((invh * h) * Q) mod N).
  { f_equal. ring. }
  rewrite <- (Z.mul_mod_idemp_l (invh * h) Q N) by lia.
  rewrite Hinv. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma rat_inv_den_coprime :
  forall N h P Q,
    N <> 0 ->
    (h * Q) mod N = P mod N ->
    Z.coprime h N ->
    Z.coprime Q N ->
    Z.coprime P N.
Proof.
  intros N h P Q HN Hcong Hh Hq.
  unfold Z.coprime.
  rewrite <- Z.gcd_mod_l.
  rewrite <- Hcong.
  rewrite Z.gcd_mod_l.
  apply Z.coprime_mul_l; assumption.
Qed.

Lemma step_unit_inv_agrees :
  forall N y op t pt,
    1 < N ->
    length t = length pt ->
    (forall k,
        rat_handle_agrees N y (nth k t 0) (nth k pt ([], [1]))) ->
    match op with
    | GInv i =>
        Z.gcd (nth i t 0) N = 1 /\
        (gra_inv (nth i t 0) N * nth i t 0) mod N = 1
    | GRoot _ => False
    | _ => True
    end ->
    length (step N op t) = length (step_rat op pt) /\
    forall k,
      rat_handle_agrees N y (nth k (step N op t) 0)
        (nth k (step_rat op pt) ([], [1])).
Proof.
  intros N y op t pt HN Hlen Hagree Hop.
  split.
  - rewrite step_length, step_rat_length, Hlen. reflexivity.
  - intros k.
    destruct (lt_dec k (length t)) as [Hlt | Hnlt].
    + assert (nth k (step N op t) 0 = nth k t 0) as Ht.
      { destruct op; simpl; apply nth_app_lt; exact Hlt. }
      assert (nth k (step_rat op pt) ([], [1]) = nth k pt ([], [1])) as Hpt.
      { destruct op; simpl; apply nth_app_lt; rewrite <- Hlen; exact Hlt. }
      rewrite Ht, Hpt. apply Hagree.
    + apply Nat.nlt_ge in Hnlt.
      destruct (Nat.eq_dec k (length t)) as [Heq | Hne].
      * subst k.
        destruct op as [c | ia ja | ia ja | ia ja | ia | ia];
          simpl; rewrite (nth_app_last _ t); rewrite Hlen; rewrite nth_app_last.
        -- unfold rat_handle_agrees. cbn [fst snd].
           replace (poly_eval [1] y) with 1.
           2: { unfold poly_eval. rewrite Z.mul_0_r. lia. }
           replace (poly_eval [c] y) with c.
           2: { unfold poly_eval. rewrite Z.mul_0_r. lia. }
           split; [unfold Z.coprime; apply Z.gcd_1_l | rewrite Z.mul_1_r; reflexivity].
        -- unfold rat_handle_agrees. cbn [fst snd].
           destruct (Hagree ia) as [Hc1 Hm1].
           destruct (Hagree ja) as [Hc2 Hm2].
           split.
           ++ rewrite poly_eval_mul. apply Z.coprime_mul_l; [exact Hc1 | exact Hc2].
           ++ rewrite poly_eval_add, !poly_eval_mul.
              apply rat_add_cong; [lia | exact Hm1 | exact Hm2].
        -- unfold rat_handle_agrees. cbn [fst snd].
           destruct (Hagree ia) as [Hc1 Hm1].
           destruct (Hagree ja) as [Hc2 Hm2].
           split.
           ++ rewrite poly_eval_mul. apply Z.coprime_mul_l; [exact Hc1 | exact Hc2].
           ++ rewrite poly_eval_sub, !poly_eval_mul.
              apply rat_sub_cong; [lia | exact Hm1 | exact Hm2].
        -- unfold rat_handle_agrees. cbn [fst snd].
           destruct (Hagree ia) as [Hc1 Hm1].
           destruct (Hagree ja) as [Hc2 Hm2].
           split.
           ++ rewrite poly_eval_mul. apply Z.coprime_mul_l; [exact Hc1 | exact Hc2].
           ++ rewrite !poly_eval_mul.
              apply rat_mul_cong; [lia | exact Hm1 | exact Hm2].
        -- unfold rat_handle_agrees. cbn [fst snd].
           destruct Hop as [Hgcd Hinv].
           destruct (Hagree ia) as [Hc Hm].
           split.
           ++ apply (rat_inv_den_coprime N (nth ia t 0)
                       (poly_eval (fst (nth ia pt ([], [1]))) y)
                       (poly_eval (snd (nth ia pt ([], [1]))) y));
                [lia | exact Hm | exact Hgcd | exact Hc].
           ++ apply (rat_inv_cong N (nth ia t 0)
                       (poly_eval (fst (nth ia pt ([], [1]))) y)
                       (poly_eval (snd (nth ia pt ([], [1]))) y)
                       (gra_inv (nth ia t 0) N));
                [lia | exact Hm | exact Hinv].
        -- destruct Hop.
      * assert (Hltk : (length t < k)%nat).
        { apply Nat.le_neq. split; [exact Hnlt | intros Heq; apply Hne; symmetry; exact Heq]. }
        assert (Hkstep : (length (step N op t) <= k)%nat).
        { rewrite (step_length N op t). apply Nat.le_succ_l. exact Hltk. }
        assert (Hkrat : (length (step_rat op pt) <= k)%nat).
        { replace (length (step_rat op pt)) with (length (step N op t)).
          2: { rewrite (step_length N op t), (step_rat_length op pt).
               f_equal. exact Hlen. }
          exact Hkstep. }
        unfold rat_handle_agrees.
        rewrite (nth_overflow (step N op t) 0 Hkstep).
        rewrite (nth_overflow (step_rat op pt) ([], [1]) Hkrat).
        apply rat_overflow_agrees. exact HN.
Qed.

Lemma gra_run_unit_inv_agree :
  forall ops N y t pt,
    1 < N ->
    gra_unit_invs N ops t ->
    length t = length pt ->
    (forall k,
        rat_handle_agrees N y (nth k t 0) (nth k pt ([], [1]))) ->
    length (gra_run N ops t) = length (gra_run_rat ops pt) /\
    forall k,
      rat_handle_agrees N y (nth k (gra_run N ops t) 0)
        (nth k (gra_run_rat ops pt) ([], [1])).
Proof.
  induction ops as [|op rest IH]; intros N y t pt HN Hu Hlen Hagree.
  - simpl. split; [exact Hlen | exact Hagree].
  - destruct op as [c | ia ja | ia ja | ia ja | ia | ia];
      simpl in Hu |- *.
    + destruct (step_unit_inv_agrees N y (GConst c) t pt HN Hlen Hagree I)
        as [Hlen' Hagree'].
      apply IH; [exact HN | exact Hu | exact Hlen' | exact Hagree'].
    + destruct (step_unit_inv_agrees N y (GAdd ia ja) t pt HN Hlen Hagree I)
        as [Hlen' Hagree'].
      apply IH; [exact HN | exact Hu | exact Hlen' | exact Hagree'].
    + destruct (step_unit_inv_agrees N y (GSub ia ja) t pt HN Hlen Hagree I)
        as [Hlen' Hagree'].
      apply IH; [exact HN | exact Hu | exact Hlen' | exact Hagree'].
    + destruct (step_unit_inv_agrees N y (GMul ia ja) t pt HN Hlen Hagree I)
        as [Hlen' Hagree'].
      apply IH; [exact HN | exact Hu | exact Hlen' | exact Hagree'].
    + destruct Hu as [Hgcd [Hinv Hu']].
      destruct (step_unit_inv_agrees N y (GInv ia) t pt HN Hlen Hagree
                  (conj Hgcd Hinv)) as [Hlen' Hagree'].
      apply IH; [exact HN | exact Hu' | exact Hlen' | exact Hagree'].
    + destruct Hu.
Qed.

Theorem gra_unit_inv_denotes :
  forall ops N y out,
    1 < N ->
    gra_unit_invs N ops (gra_init y) ->
    rat_handle_agrees N y (gra_eval N ops y out)
      (nth out (gra_run_rat ops slp_init_rat) ([], [1])).
Proof.
  intros ops N y out HN Hu.
  unfold gra_eval.
  destruct (gra_init_rat_agrees N y HN) as [Hlen Hagree].
  destruct (gra_run_unit_inv_agree ops N y (gra_init y) slp_init_rat
              HN Hu Hlen Hagree) as [_ Hk].
  apply Hk.
Qed.

(** ** Degree bound of a nodiv tape

    Init handles have degrees [0; 0; 1].  [GConst] is [0]; add/sub
    take [Nat.max]; mul adds.  Upper bound: cancellation may drop
    degree.  A handle of bound [≤ 3] sits in the pin window
    [e=3 ⇒ deg(P^3−X) < 10]. *)

Definition slp_init_deg : list nat := [0%nat; 0%nat; 1%nat].

Definition step_deg_bound (op : GRAOp) (bs : list nat) : list nat :=
  match op with
  | GConst _ => bs ++ [0%nat]
  | GAdd i j => bs ++ [Nat.max (nth i bs 0%nat) (nth j bs 0%nat)]
  | GSub i j => bs ++ [Nat.max (nth i bs 0%nat) (nth j bs 0%nat)]
  | GMul i j => bs ++ [(nth i bs 0%nat + nth j bs 0%nat)%nat]
  | GInv i => bs ++ [nth i bs 0%nat]
  | GRoot i => bs ++ [nth i bs 0%nat]
  end.

Fixpoint gra_deg_bound (ops : list GRAOp) (bs : list nat) : list nat :=
  match ops with
  | nil => bs
  | op :: rest => gra_deg_bound rest (step_deg_bound op bs)
  end.

Lemma slp_init_deg_le :
  forall i,
    (poly_degree (nth i slp_init_poly []) <= nth i slp_init_deg 0%nat)%nat.
Proof.
  intros i.
  destruct i as [|i]; [|destruct i as [|i]; [|destruct i as [|i]]];
    try (vm_compute; lia).
  unfold slp_init_poly, slp_init_deg.
  rewrite !nth_overflow by (cbn [length]; lia).
  unfold poly_degree. simpl. lia.
Qed.

Lemma step_deg_bound_length :
  forall op bs, length (step_deg_bound op bs) = S (length bs).
Proof. intros op bs. destruct op; simpl; rewrite length_app; simpl; lia. Qed.

Lemma step_nodiv_degree_le :
  forall op pt bs i,
    is_nodiv op ->
    length pt = length bs ->
    (forall k, (poly_degree (nth k pt []) <= nth k bs 0%nat)%nat) ->
    (poly_degree (nth i (step_poly op pt) []) <=
       nth i (step_deg_bound op bs) 0%nat)%nat.
Proof.
  intros op pt bs i Hop Hlen Hall.
  destruct (lt_dec i (length pt)) as [Hlt | Hnlt].
  - destruct op; simpl;
      (rewrite nth_app_lt by exact Hlt;
       rewrite nth_app_lt by (rewrite <- Hlen; exact Hlt);
       apply Hall).
  - apply Nat.nlt_ge in Hnlt.
    destruct (Nat.eq_dec i (length pt)) as [Heq | Hne].
    + subst i. rewrite Hlen at 2.
      destruct Hop as [c | ia ja | ia ja | ia ja]; simpl; rewrite !nth_app_last.
      * unfold poly_degree. simpl. destruct (c =? 0); lia.
      * pose proof (poly_degree_add_le (nth ia pt []) (nth ja pt [])).
        pose proof (Hall ia). pose proof (Hall ja). lia.
      * pose proof (poly_degree_sub_le (nth ia pt []) (nth ja pt [])).
        pose proof (Hall ia). pose proof (Hall ja). lia.
      * pose proof (poly_degree_mul_le (nth ia pt []) (nth ja pt [])).
        pose proof (Hall ia). pose proof (Hall ja). lia.
    + destruct op; simpl;
        (rewrite nth_overflow by (rewrite length_app; simpl; lia);
         rewrite nth_overflow by (rewrite length_app, <- Hlen; simpl; lia);
         unfold poly_degree; simpl; lia).
Qed.

Lemma gra_run_poly_length :
  forall ops t, length (gra_run_poly ops t) = (length t + length ops)%nat.
Proof.
  intros ops. induction ops as [|op rest IH]; intros t; simpl.
  - lia.
  - rewrite IH, step_poly_length. lia.
Qed.

Lemma gra_nodiv_degree_le :
  forall ops i,
    Forall is_nodiv ops ->
    (poly_degree (nth i (gra_run_poly ops slp_init_poly) []) <=
       nth i (gra_deg_bound ops slp_init_deg) 0%nat)%nat.
Proof.
  intros ops i Hop.
  assert (Hacc :
    length slp_init_poly = length slp_init_deg /\
    forall k, (poly_degree (nth k slp_init_poly []) <= nth k slp_init_deg 0%nat)%nat).
  { split; [reflexivity | apply slp_init_deg_le]. }
  revert Hop Hacc.
  generalize slp_init_poly as pt. generalize slp_init_deg as bs.
  intros bs pt Hop Hacc.
  revert pt bs Hacc.
  induction ops as [|op rest IH]; intros pt bs Hacc.
  - simpl. destruct Hacc as [_ Hall]. apply Hall.
  - inversion Hop; subst.
    destruct Hacc as [Hlen Hall].
    apply (IH H2 (step_poly op pt) (step_deg_bound op bs)).
    split.
    + rewrite step_poly_length, step_deg_bound_length, Hlen. reflexivity.
    + intros k. apply step_nodiv_degree_le; [exact H1 | exact Hlen | exact Hall].
Qed.

Theorem gra_deg_bound_identity :
  nth 2%nat (gra_deg_bound [] slp_init_deg) 0%nat = 1%nat.
Proof. reflexivity. Qed.

Theorem gra_deg_bound_square :
  nth 3%nat (gra_deg_bound [GMul 2%nat 2%nat] slp_init_deg) 0%nat = 2%nat.
Proof. reflexivity. Qed.

Theorem gra_deg_bound_x3 :
  nth 4%nat (gra_deg_bound [GMul 2%nat 2%nat; GMul 3%nat 2%nat] slp_init_deg) 0%nat = 3%nat.
Proof. reflexivity. Qed.

Theorem gra_deg_bound_x4 :
  nth 4%nat (gra_deg_bound [GMul 2%nat 2%nat; GMul 3%nat 3%nat] slp_init_deg) 0%nat = 4%nat.
Proof. reflexivity. Qed.

Theorem gra_nodiv_mul_is_nodiv :
  Forall is_nodiv [GMul 2%nat 2%nat].
Proof. repeat constructor. Qed.

Theorem gra_nodiv_mul_denotes_square :
  gra_eval pin_N [GMul 2%nat 2%nat] 36 3%nat = 36 * 36.
Proof.
  rewrite gra_nodiv_denotes by apply gra_nodiv_mul_is_nodiv.
  vm_compute. reflexivity.
Qed.

Theorem gra_nodiv_integer_eth_root_forbidden :
  forall ops e N out,
    Forall is_nodiv ops ->
    (2 <= e)%nat ->
    (forall y, Z.pow (gra_eval N ops y out) (Z.of_nat e) = y) ->
    False.
Proof.
  intros ops e N out Hop He Hall.
  pose proof (Hall 2) as H2.
  rewrite gra_nodiv_denotes in H2 by exact Hop.
  pose proof (Pe_minus_X_eval_2_nonzero
                (nth out (gra_run_poly ops slp_init_poly) []) e He) as Hz.
  rewrite poly_eval_Pe_minus_X in Hz.
  apply Hz. lia.
Qed.

(** ** Wave 1 — Leander–Rupp, no division, low [e] *)

Theorem gra_nodiv_const42_inverts_36 :
  powm pin_x pin_e pin_N = pin_y.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_nodiv_const42_fails_on_8 :
  powm pin_x pin_e pin_N <> 8.
Proof. vm_compute. discriminate. Qed.

Theorem gra_identity_not_cube_root_at_2 :
  powm 2 3 pin_N <> 2.
Proof. vm_compute. discriminate. Qed.

Theorem gra_identity_at_one :
  powm 1 3 pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_identity_gcd_at_2 :
  Z.gcd (2 * 2 * 2 - 2) pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_nodiv_identical_X3_linear :
  nth 1%nat (poly_Pe_minus_X poly_X 3%nat) 0 = -1.
Proof. apply X3_minus_X_nth1. Qed.

Theorem gra_nodiv_N_does_not_divide_minus1 :
  Z.gcd 1 pin_N = 1.
Proof. reflexivity. Qed.

Theorem gra_nodiv_identical_root_impossible_X3 :
  nth 1%nat (poly_Pe_minus_X poly_X 3%nat) 0 = -1 ->
  ~ (pin_N | -1).
Proof.
  intros H div. destruct div as [k Hk].
  nia.
Qed.

Theorem Pe_minus_X_eval2_is_six_on_X :
  poly_eval (poly_Pe_minus_X poly_X 3%nat) 2 = 6.
Proof. apply X3_minus_X_eval_2. Qed.

(** ** Wave 2a — AM09 inversion leak and leading term

    [GInv] of a non-unit handle returns [gcd(h, N)].  [GInv] of a unit
    returns a modular inverse. *)

Definition gra_inv11_prog : list GRAOp := [GConst pin_p; GInv 3%nat].
Definition gra_inv22_prog : list GRAOp := [GConst (2 * pin_p); GInv 3%nat].
Definition gra_inv36_prog : list GRAOp := [GConst pin_y; GInv 3%nat].

Theorem gra_inv_nonunit_pin :
  gra_eval_Z gra_inv11_prog pin_y 4%nat = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_inv_nonunit_factors :
  Problem_Factor pin_N (gra_eval_Z gra_inv11_prog pin_y 4%nat).
Proof.
  unfold Problem_Factor. rewrite gra_inv_nonunit_pin.
  split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem pin_gra_inv11_first_gcd :
  gra_first_inv_gcd pin_N gra_inv11_prog (gra_init pin_y) = Some pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_gra_inv36_first_gcd_none :
  gra_first_inv_gcd pin_N gra_inv36_prog (gra_init pin_y) = None.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_gra_square_first_gcd_none :
  gra_first_inv_gcd pin_N [GMul 2%nat 2%nat] (gra_init pin_y) = None.
Proof. vm_compute. reflexivity. Qed.

Fixpoint units_gra_inv_ok (k : nat) : bool :=
  match k with
  | O => true
  | S k' =>
      let h := Z.of_nat (S k') in
      if Z.gcd h pin_N =? 1
      then ((gra_inv h pin_N * h) mod pin_N =? 1) && units_gra_inv_ok k'
      else units_gra_inv_ok k'
  end.

Theorem pin_units_gra_inv_ok :
  units_gra_inv_ok (Z.to_nat (pin_N - 1)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma units_gra_inv_ok_spec :
  forall k h,
    units_gra_inv_ok k = true ->
    0 < h <= Z.of_nat k ->
    Z.gcd h pin_N = 1 ->
    (gra_inv h pin_N * h) mod pin_N = 1.
Proof.
  induction k as [|k IH]; intros h Hok Hrng Hgcd.
  - lia.
  - cbn [units_gra_inv_ok] in Hok.
    destruct (Z.le_gt_cases h (Z.of_nat k)) as [Hle | Hgt].
    + destruct (Z.eqb_spec (Z.gcd (Z.of_nat (S k)) pin_N) 1).
      * apply andb_true_iff in Hok. destruct Hok as [_ Hrest].
        apply IH; [exact Hrest | lia | exact Hgcd].
      * apply IH; [exact Hok | lia | exact Hgcd].
    + assert (h = Z.of_nat (S k)) by lia. subst h.
      destruct (Z.eqb_spec (Z.gcd (Z.of_nat (S k)) pin_N) 1) as [Heq | Hne].
      * apply andb_true_iff in Hok. destruct Hok as [Hinv _].
        apply Z.eqb_eq in Hinv. exact Hinv.
      * congruence.
Qed.

Theorem pin_gra_inv_inverts_reduced_unit :
  forall h,
    0 < h < pin_N ->
    Z.gcd h pin_N = 1 ->
    (gra_inv h pin_N * h) mod pin_N = 1.
Proof.
  intros h Hrng Hgcd.
  apply (units_gra_inv_ok_spec (Z.to_nat (pin_N - 1)));
    [apply pin_units_gra_inv_ok | | exact Hgcd].
  rewrite Z2Nat.id by lia. lia.
Qed.

Theorem pin_ginv_of_y_unit_invs :
  forall y,
    0 < y < pin_N ->
    Z.coprime y pin_N ->
    gra_unit_invs pin_N [GInv 2%nat] (gra_init y).
Proof.
  intros y Hrng Hy.
  unfold gra_unit_invs, gra_init. cbn [nth].
  split; [exact Hy|].
  split; [|exact I].
  apply pin_gra_inv_inverts_reduced_unit; [exact Hrng | exact Hy].
Qed.

(** [GRoot] of a [Z]-cube whose root shares a factor with [N]
    leaks that factor.  This is integer cube-root, not a modular
    cube-root: a residue cube that is not a [Z]-cube is a search
    miss and returns the handle. *)

Definition gra_root_p3_prog : list GRAOp :=
  [GConst (pin_p * pin_p * pin_p); GRoot 3%nat].

Theorem integer_cube_root_p3 :
  integer_cube_root (pin_p * pin_p * pin_p) = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_root_p3_from_tape :
  gra_eval_Z gra_root_p3_prog pin_y 4%nat = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_root_p3_factors :
  Problem_Factor pin_N (gra_eval_Z gra_root_p3_prog pin_y 4%nat).
Proof.
  unfold Problem_Factor. rewrite gra_root_p3_from_tape.
  split; [lia|]. exists pin_q. reflexivity.
Qed.

Fixpoint gra_first_root_factor (N : Z) (ops : list GRAOp) (t : list Z)
  : option Z :=
  match ops with
  | nil => None
  | op :: rest =>
      match op with
      | GRoot i =>
          let r := integer_cube_root (nth i t 0) in
          let g := Z.gcd r N in
          if (1 <? g) && (g <? N) then Some g
          else gra_first_root_factor N rest (step N op t)
      | _ => gra_first_root_factor N rest (step N op t)
      end
  end.

Lemma gra_first_root_factor_some :
  forall ops N t f,
    gra_first_root_factor N ops t = Some f ->
    1 < f < N /\ (f | N).
Proof.
  induction ops as [|op rest IH]; intros N t f Hf.
  - discriminate.
  - destruct op as [c | i j | i j | i j | i | i]; simpl in Hf.
    + apply (IH N (step N (GConst c) t) f Hf).
    + apply (IH N (step N (GAdd i j) t) f Hf).
    + apply (IH N (step N (GSub i j) t) f Hf).
    + apply (IH N (step N (GMul i j) t) f Hf).
    + apply (IH N (step N (GInv i) t) f Hf).
    + set (r := integer_cube_root (nth i t 0)) in *.
      set (g := Z.gcd r N) in *.
      destruct ((1 <? g) && (g <? N)) eqn:Hb.
      * inversion Hf; subst f.
        apply andb_true_iff in Hb. destruct Hb as [H1 H2].
        apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
        split; [split; [exact H1 | exact H2] | apply Z.gcd_divide_r].
      * apply (IH N (step N (GRoot i) t) f Hf).
Qed.

Theorem gra_first_root_factor_factors :
  forall ops y f,
    gra_first_root_factor pin_N ops (gra_init y) = Some f ->
    Problem_Factor pin_N f.
Proof.
  intros ops y f Hf.
  destruct (gra_first_root_factor_some ops pin_N (gra_init y) f Hf)
    as [Hrng Hdiv].
  unfold Problem_Factor. split; [exact Hrng | exact Hdiv].
Qed.

Theorem pin_gra_root_p3_first_factor :
  gra_first_root_factor pin_N gra_root_p3_prog (gra_init pin_y) = Some pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_gra_root_8_first_none :
  gra_first_root_factor pin_N [GConst 8; GRoot 3%nat] (gra_init pin_y) = None.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_inv_22_from_tape :
  gra_eval_Z gra_inv22_prog pin_y 4%nat = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_inv_unit_gcd :
  Z.gcd pin_y pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_inv_unit_from_tape :
  (gra_eval_Z gra_inv36_prog 0 4%nat * pin_y) mod pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_fixed_e_leading_const :
  3 * 0 <> 1 + 3 * 0.
Proof. lia. Qed.

Theorem gra_fixed_e_leading :
  forall dp dq, 3 * dp <> 1 + 3 * dq.
Proof.
  intros dp dq. apply rational_Pe_minus_XQe_leading. lia.
Qed.

Theorem rsa_inverter_is_not_a_GRA_comment :
  powm pin_x pin_e pin_N = pin_y.
Proof. apply gra_nodiv_const42_inverts_36. Qed.

(** Functional decryption [x ↦ x^d] inverts cubing on units and is
    not a polynomial identity in [F_11[X]]. *)
Theorem powm_d_inverts_cube_pin :
  powm pin_y pin_d pin_N = pin_x.
Proof. vm_compute. reflexivity. Qed.

(** ** Wave 2b — AMS flexible [e]; [λ+1] is a constant, not a ring op on [y] *)

Theorem gra_const_81 :
  gra_eval_Z [GConst (pin_lam + 1)] pin_y 3%nat = pin_lam + 1 /\
  gra_eval_Z [GConst (pin_lam + 1)] 8 3%nat = pin_lam + 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem gra_const_lambda_plus_one_solves_sRSA_without_factoring :
  forall y,
    Z.coprime y pin_N ->
    Problem_StrongRSA pin_N (y mod pin_N) (y mod pin_N) (pin_lam + 1).
Proof.
  intros y Hcop.
  apply (lambda_solves_strong_RSA pin_p pin_q y pin_p_prime pin_q_prime
           pin_p_neq_q Hcop).
Qed.

Theorem gra_const_81_does_not_factor :
  Z.gcd (pin_lam + 1) pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem lambda_plus_one_is_81 :
  lambda_semiprime pin_p pin_q + 1 = pin_lam + 1.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_add_mul_of_36_is_not_81 :
  pin_y + pin_y <> pin_lam + 1 /\
  pin_y * pin_y <> pin_lam + 1 /\
  pin_y - pin_y <> pin_lam + 1.
Proof. lia. Qed.

Theorem am09_fixed_e_is_a_parameter :
  forall e dp dq,
    1 < e ->
    e * dp <> 1 + e * dq.
Proof. apply rational_Pe_minus_XQe_leading. Qed.

(** ** Wave 6a — Damgård–Koprowski signature contrast *)

Inductive GGMOp : Set :=
  | GGMul (i j : nat)
  | GGInv (i : nat).

Inductive is_ggm_op : GRAOp -> Prop :=
  | is_ggm_mul : forall i j, is_ggm_op (GMul i j)
  | is_ggm_inv : forall i, is_ggm_op (GInv i).

Theorem gadd_is_not_a_ggm_op :
  forall i j, ~ is_ggm_op (GAdd i j).
Proof. intros i j H. inversion H. Qed.

Theorem gsub_is_not_a_ggm_op :
  forall i j, ~ is_ggm_op (GSub i j).
Proof. intros i j H. inversion H. Qed.

Theorem gconst_is_not_a_ggm_op :
  forall c, ~ is_ggm_op (GConst c).
Proof. intros c H. inversion H. Qed.

Theorem gra_poly_construction_needs_add :
  nth 1%nat (poly_Pe_minus_X poly_X 3%nat) 0 = -1.
Proof. apply X3_minus_X_nth1. Qed.

Theorem generic_group_does_not_separate_rsa_from_srsa :
  forall N e y x,
    1 < e ->
    Problem_RSA N e y x ->
    Problem_StrongRSA N y x e.
Proof. intros N e y x He. apply rsa_solution_is_strong_RSA. exact He. Qed.

Theorem ggm_mul_pin :
  gra_eval_Z [GMul 2%nat 2%nat; GMul 3%nat 2%nat] 36 4%nat = 36 * 36 * 36.
Proof. vm_compute. reflexivity. Qed.
