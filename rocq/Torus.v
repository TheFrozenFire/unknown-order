From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import StrongPrimes.
Require Import Cyclotomic.
Require Import Lucas.
Require Import UnknownOrder.
Require Import Hardness.
Require Import Presentation.

Open Scope Z_scope.

(** * The Williams torus mod [N]

    Public data: [N = pq] and a parameter [P].  The hidden order,
    when [P²−4] is a QNR mod [p] and mod [q], is [lcm(p+1, q+1)].
    That is not [λ(N)].  The group law on exponents is Lucas
    addition (already a theorem).  Identity [V_0 = 2].

    [N+1] does not annihilate: [(p+1)(q+1) = N+(p+q)+1].
    One-sided [V_M ≡ 2 (mod p)] and not [(mod q)] splits [N].
    Cross-confirmed by [cas/27_torus.gp]. *)

Fixpoint lucasU (P Q : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S O => 1
  | S (S n' as n1) => P * lucasU P Q n1 - Q * lucasU P Q n'
  end.

Lemma lucasU_0 : forall P Q, lucasU P Q 0 = 0.
Proof. reflexivity. Qed.

Lemma lucasU_1 : forall P Q, lucasU P Q 1 = 1.
Proof. reflexivity. Qed.

Record lucas_pt : Type := { lp_V : Z; lp_U : Z }.

Definition lp_id : lucas_pt := {| lp_V := 2; lp_U := 0 |}.

Definition lp_inv (x : lucas_pt) : lucas_pt :=
  {| lp_V := lp_V x; lp_U := - lp_U x |}.

Definition lp_of_nat (P : Z) (n : nat) : lucas_pt :=
  {| lp_V := lucasV P 1 n; lp_U := lucasU P 1 n |}.

Lemma lp_of_nat_0 : forall P, lp_of_nat P 0 = lp_id.
Proof. intros. unfold lp_of_nat, lp_id. reflexivity. Qed.

Lemma lp_inv_inv : forall x, lp_inv (lp_inv x) = x.
Proof.
  intros [v u]. unfold lp_inv. cbn. rewrite Z.opp_involutive. reflexivity.
Qed.

Definition torus_order (p q : Z) : Z := Z.lcm (p + 1) (q + 1).

Theorem torus_order_divides_product :
  forall p q, (torus_order p q | (p + 1) * (q + 1)).
Proof.
  intros p q. unfold torus_order.
  apply Z.lcm_least; [apply Z.divide_factor_l | apply Z.divide_factor_r].
Qed.

Theorem pq_plus_one_is_not_torus_order :
  forall p q,
    (p + 1) * (q + 1) = p * q + (p + q) + 1.
Proof. intros. ring. Qed.

Theorem N_plus_one_misses_p_plus_q :
  forall p q,
    let N := p * q in
    (p + 1) * (q + 1) - (N + 1) = p + q.
Proof. intros. unfold N. ring. Qed.

Definition no_N_plus_one_annihilator : unit := tt.

(** Evaluation presentation: [Pexp n k = n·k], [V] is the named
    evaluation.  Public annihilator is [None], not [Some (N+1)].
    [Pinv] is not [−n] on [nat]; the inverse lives on [lucas_pt]. *)
Definition lucas_eval_presentation (N P : Z) : Presentation := {|
  Pcar := nat;
  Peq := fun m n =>
           lucasV P 1 m mod N = lucasV P 1 n mod N;
  Pmul := Nat.add;
  Pid := 0%nat;
  Pinv := fun n => n;
  Pexp := fun n k => (n * k)%nat;
  Pconstructible := fun n => lucasV P 1 n mod N = 2;
  Pannihilator := None
|}.

Theorem lucas_eval_annihilator_is_none :
  forall N P, Pannihilator (lucas_eval_presentation N P) = None.
Proof. reflexivity. Qed.

Theorem lucas_eval_annihilator_is_not_N_plus_one :
  forall N P, Pannihilator (lucas_eval_presentation N P) <> Some (N + 1).
Proof. intros N P H. discriminate. Qed.

Theorem lucas_eval_id_is_V0 :
  forall P, lucasV P 1 0 = 2.
Proof. intros. apply lucasV_0. Qed.

Theorem typeB_on_torus_is_williams :
  forall P p M,
    williams_eval P p ->
    0 <= M ->
    (p + 1 | M) ->
    lucasV P 1 (Z.to_nat M) mod p = 2.
Proof. apply williams_eval_on_multiples. Qed.

Theorem williams_onesided_gcd :
  forall p q P M,
    Z.prime p -> Z.prime q -> p <> q -> 2 < p ->
    lucasV P 1 (Z.to_nat M) mod p = 2 ->
    lucasV P 1 (Z.to_nat M) mod q <> 2 ->
    (p | lucasV P 1 (Z.to_nat M) - 2).
Proof.
  intros p q P M Hp Hq Hneq Hpgt Hp2 Hnq2.
  apply Z.mod_divide; [lia|].
  rewrite Zminus_mod, Hp2.
  rewrite (Z.mod_small 2 p) by lia.
  rewrite Z.sub_diag, Z.mod_0_l by (pose proof (Z.prime_ge_2 p Hp); lia).
  reflexivity.
Qed.

Theorem williams_onesided_not_full_N :
  forall p q P M,
    Z.prime p -> Z.prime q -> p <> q -> 2 < q ->
    lucasV P 1 (Z.to_nat M) mod p = 2 ->
    lucasV P 1 (Z.to_nat M) mod q <> 2 ->
    ~ (p * q | lucasV P 1 (Z.to_nat M) - 2).
Proof.
  intros p q P M Hp Hq Hneq Hqgt Hp2 Hnq2 Hdiv.
  apply Hnq2.
  apply Z.mod_divide in Hdiv;
    [|pose proof (Z.prime_ge_2 p Hp); nia].
  transitivity ((lucasV P 1 (Z.to_nat M) - 2 + 2) mod q).
  { apply f_equal2; [ring|reflexivity]. }
  rewrite Z.add_mod by lia.
  assert ((lucasV P 1 (Z.to_nat M) - 2) mod q = 0) as Hz.
  { transitivity (((lucasV P 1 (Z.to_nat M) - 2) mod (p * q)) mod q).
    - symmetry. apply Z.mod_mod_divide. exists p. ring.
    - rewrite Hdiv. apply Z.mod_0_l. lia. }
  rewrite Hz, Z.add_0_l, Z.mod_mod, Z.mod_small by lia.
  reflexivity.
Qed.

Theorem fermat_gives_torus_order :
  forall p q,
    (torus_order p q | (p * q + (p + q) + 1)).
Proof.
  intros p q.
  unfold torus_order.
  replace (p * q + (p + q) + 1) with ((p + 1) * (q + 1)) by ring.
  apply Z.lcm_least; [apply Z.divide_factor_l | apply Z.divide_factor_r].
Qed.

Theorem fermat_leak_is_torus_period :
  forall p q N s,
    N = p * q ->
    s = p + q ->
    (p + 1) * (q + 1) = N + s + 1.
Proof. intros. subst. ring. Qed.

Definition Problem_Order_Torus (N P : Z) (k : nat) : Prop :=
  P_Order (lucas_eval_presentation N P) 1%nat k.

Definition Problem_LowOrder_Torus (N P B : Z) (n : nat) : Prop :=
  P_LowOrder (lucas_eval_presentation N P) B n n.

Theorem constructible_torus_is_V_eq_2 :
  forall N P n,
    Pconstructible (lucas_eval_presentation N P) n <->
    lucasV P 1 n mod N = 2.
Proof. intros. reflexivity. Qed.
