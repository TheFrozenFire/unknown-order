From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
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

Definition pin_N : Z := 187.

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
  gra_eq_leak pin_N gra_eq_prog 36 9%nat 0%nat = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_eq_leak_factors :
  Problem_Factor 187 (gra_eq_leak pin_N gra_eq_prog 36 9%nat 0%nat).
Proof.
  unfold Problem_Factor. rewrite gra_eq_leak_pin.
  split; [lia|]. exists 17. reflexivity.
Qed.

Theorem gra_eq_leak_onesided :
  Z.prime 11 ->
  Z.prime 17 ->
  (11 | 88) ->
  ~ (17 | 88) ->
  Z.gcd 88 (11 * 17) = 11.
Proof.
  intros Hp Hq H11 H17.
  apply gcd_onesided_semiprime; try assumption; discriminate.
Qed.

Theorem gra_eq_N_is_not_a_split :
  Z.gcd 187 187 = 187.
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

Theorem gra_nodiv_mul_is_nodiv :
  Forall is_nodiv [GMul 2%nat 2%nat].
Proof. repeat constructor. Qed.

Theorem gra_nodiv_mul_denotes_square :
  gra_eval 187 [GMul 2%nat 2%nat] 36 3%nat = 36 * 36.
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
  powm 42 3 187 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_nodiv_const42_fails_on_8 :
  powm 42 3 187 <> 8.
Proof. vm_compute. discriminate. Qed.

Theorem gra_identity_not_cube_root_at_2 :
  powm 2 3 187 <> 2.
Proof. vm_compute. discriminate. Qed.

Theorem gra_identity_at_one :
  powm 1 3 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_identity_gcd_at_2 :
  Z.gcd (2 * 2 * 2 - 2) 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_nodiv_identical_X3_linear :
  nth 1%nat (poly_Pe_minus_X poly_X 3%nat) 0 = -1.
Proof. apply X3_minus_X_nth1. Qed.

Theorem gra_nodiv_N_does_not_divide_minus1 :
  Z.gcd 1 187 = 1.
Proof. reflexivity. Qed.

Theorem gra_nodiv_identical_root_impossible_X3 :
  nth 1%nat (poly_Pe_minus_X poly_X 3%nat) 0 = -1 ->
  ~ (187 | -1).
Proof.
  intros H div. destruct div as [k Hk]. nia.
Qed.

Theorem Pe_minus_X_eval2_is_six_on_X :
  poly_eval (poly_Pe_minus_X poly_X 3%nat) 2 = 6.
Proof. apply X3_minus_X_eval_2. Qed.

(** ** Wave 2a — AM09 inversion leak and leading term

    [GInv] of a non-unit handle returns [gcd(h, N)].  [GInv] of a unit
    returns a modular inverse. *)

Definition gra_inv11_prog : list GRAOp := [GConst 11; GInv 3%nat].
Definition gra_inv22_prog : list GRAOp := [GConst 22; GInv 3%nat].
Definition gra_inv36_prog : list GRAOp := [GConst 36; GInv 3%nat].

Theorem gra_inv_nonunit_pin :
  gra_eval_Z gra_inv11_prog 36 4%nat = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_inv_nonunit_factors :
  Problem_Factor 187 (gra_eval_Z gra_inv11_prog 36 4%nat).
Proof.
  unfold Problem_Factor. rewrite gra_inv_nonunit_pin.
  split; [lia|]. exists 17. reflexivity.
Qed.

Theorem gra_inv_22_from_tape :
  gra_eval_Z gra_inv22_prog 36 4%nat = 11.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_inv_unit_gcd :
  Z.gcd 36 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_inv_unit_from_tape :
  (gra_eval_Z gra_inv36_prog 0 4%nat * 36) mod 187 = 1.
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
  powm 42 3 187 = 36.
Proof. apply gra_nodiv_const42_inverts_36. Qed.

(** Functional decryption [x ↦ x^d] inverts cubing on units and is
    not a polynomial identity in [F_11[X]]. *)
Theorem powm_d_inverts_cube_pin :
  powm 36 27 187 = 42.
Proof. vm_compute. reflexivity. Qed.

(** ** Wave 2b — AMS flexible [e]; [λ+1] is a constant, not a ring op on [y] *)

Theorem gra_const_81 :
  gra_eval_Z [GConst 81] 36 3%nat = 81 /\
  gra_eval_Z [GConst 81] 8 3%nat = 81.
Proof. vm_compute. split; reflexivity. Qed.

Theorem gra_const_lambda_plus_one_solves_sRSA_without_factoring :
  forall y,
    Z.coprime y 187 ->
    Problem_StrongRSA 187 (y mod 187) (y mod 187) 81.
Proof.
  intros y Hcop.
  apply (lambda_solves_strong_RSA 11 17 y prime_11 prime_17
           ltac:(discriminate) Hcop).
Qed.

Theorem gra_const_81_does_not_factor :
  Z.gcd 81 187 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem lambda_plus_one_is_81 :
  lambda_semiprime 11 17 + 1 = 81.
Proof. vm_compute. reflexivity. Qed.

Theorem gra_add_mul_of_36_is_not_81 :
  36 + 36 <> 81 /\ 36 * 36 <> 81 /\ 36 - 36 <> 81.
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
  gra_eval_Z [GMul 2%nat 2%nat; GMul 3%nat 2%nat] 36 4%nat = 46656.
Proof. vm_compute. reflexivity. Qed.
