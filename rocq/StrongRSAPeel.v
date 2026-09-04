From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.ZPoly.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import Miller.
Require Import RabinWilliams.
Require Import QRModN.
Require Import SAGM.

Open Scope Z_scope.

(** * Standard-model Strong-RSA witness peel

    Classify a witness [(x,e)] of [y]: non-unit [x] is a factor;
    Jacobi [−1] forces odd [e]; even [e] is a square root (associate
    does not split; mixed root does).  The [λ]-type [x = y] is an
    annihilator; [a^{e−1} ≡ 1] on units makes [e−1] a multiple of
    [λ] and Miller splits.  The leftover — odd [e(y)] coprime to
    [λ], [λ] not dividing [e−1] — is the residual leaf: standard-model
    RSA with a [y]-dependent exponent.  Whether a residual *solver*
    constructs a factor is [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/127]. *)

(** ** Non-unit [x] *)

Theorem srsa_unit_y_forces_unit_x :
  forall N y x e,
    1 < N ->
    0 < e ->
    Z.coprime y N ->
    powm x e N = y ->
    Z.coprime x N.
Proof.
  intros N y x e Hn He Hcop Hy.
  apply (powm_unit_is_coprime x e N); try lia.
  rewrite Hy. exact Hcop.
Qed.

Theorem srsa_gcd_proper_is_factor :
  forall p q x,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    let g := Z.gcd x (p * q) in
    1 < g < p * q ->
    Problem_Factor (p * q) g.
Proof.
  intros p q x Hp Hq Hneq g Hg.
  unfold Problem_Factor, g.
  split; [exact Hg | apply Z.gcd_divide_r].
Qed.

Theorem srsa_nonunit_x_pin :
  powm pin_p pin_e pin_N = (pin_p ^ pin_e) mod pin_N /\
  Z.gcd pin_p pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

(** ** Jacobi [−1] forces odd [e] *)

Theorem srsa_jacobi_minus1_forces_odd_e :
  forall p q x e,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    p <> q ->
    Z.coprime x p ->
    Z.coprime x q ->
    0 <= e ->
    jacobi_N (powm x e (p * q)) p q = -1 ->
    Z.Odd e.
Proof.
  intros p q x e Hp Hq Hp2 Hq2 Hneq Hxp Hxq He Hj.
  destruct (Z.Even_or_Odd e) as [Hev | Hod]; [| exact Hod].
  pose proof (jacobi_even_power x e p q Hp Hq Hp2 Hq2 Hneq Hxp Hxq He Hev) as Heven.
  rewrite Heven in Hj. discriminate.
Qed.

Theorem srsa_jacobi_two_is_minus1 :
  jacobi_N 2 pin_p pin_q = -1.
Proof. vm_compute. reflexivity. Qed.

Theorem srsa_lambda_type_on_jacobi_minus1 :
  Problem_StrongRSA pin_N 2 2 (pin_lam + 1) /\ Z.Odd (pin_lam + 1).
Proof.
  split.
  - unfold Problem_StrongRSA. split; [lia|]. vm_compute. reflexivity.
  - exists (pin_lam / 2). vm_compute. lia.
Qed.

(** ** Even [e] is a square root *)

Theorem srsa_even_e_is_square_root :
  forall N x k y,
    1 < N ->
    0 <= k ->
    powm x (2 * k) N = y ->
    powm (powm x k N) 2 N = y.
Proof.
  intros N x k y Hn Hk Hy.
  rewrite <- powm_mul_r by lia.
  rewrite (Z.mul_comm k 2). exact Hy.
Qed.

Theorem srsa_even_e_pin :
  powm 6 2 pin_N = (6 * 6) mod pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem srsa_associate_neg6_does_not_split :
  powm (pin_N - 6) 2 pin_N = (6 * 6) mod pin_N /\
  Z.gcd (pin_N - 6 + 6) pin_N = pin_N.
Proof. vm_compute. split; reflexivity. Qed.

Theorem srsa_mixed_root_of_36_factors :
  powm pin_sqrt1_mixed 2 pin_N = 1 /\
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem srsa_even_e_nonassociate_factors :
  forall p q r x,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    powm x 2 (p * q) = powm r 2 (p * q) ->
    ~ (p * q | x - r) ->
    ~ (p * q | x + r) ->
    let g := Z.gcd (x - r) (p * q) in
    1 < g < p * q /\ (g | p * q).
Proof.
  intros p q r x Hp Hq Hneq Hsq Hny Hnm.
  apply (rabin_oracle_nonassociate_factors p q r x Hp Hq Hneq Hsq Hny Hnm).
Qed.

(** ** [λ]-type: [x = y] is an annihilator *)

Theorem srsa_x_eq_y_annihilates :
  forall N y e,
    1 < N ->
    1 < e ->
    Z.coprime y N ->
    powm y e N = y ->
    powm y (e - 1) N = 1.
Proof.
  intros N y e Hn He Hcop Hy.
  assert (He1 : 0 <= e - 1) by lia.
  pose proof (powm_add_r y (e - 1) 1 N ltac:(lia) He1 ltac:(lia)) as Hsum.
  replace (e - 1 + 1) with e in Hsum by lia.
  rewrite Hy, (powm_1_r y N ltac:(lia)) in Hsum.
  assert (Hyred : y = y mod N).
  { assert (0 <= y < N).
    { rewrite <- Hy. unfold powm. apply Z.mod_pos_bound; lia. }
    rewrite Z.mod_small; lia. }
  rewrite Hyred in Hsum at 1.
  assert (Hgcd : Z.gcd (y mod N) N = 1).
  { rewrite Z.gcd_mod_l. exact Hcop. }
  assert (Heq : (powm y (e - 1) N * (y mod N)) mod N =
                  (1 * (y mod N)) mod N).
  { rewrite Z.mul_1_l, Z.mod_mod by lia. symmetry. exact Hsum. }
  pose proof (mul_cancel_r_coprime (powm y (e - 1) N) 1 (y mod N) N
                Hn Hgcd Heq) as Hcan.
  rewrite Z.mod_1_l in Hcan by lia.
  unfold powm in Hcan |- *.
  rewrite Z.mod_mod in Hcan by lia. exact Hcan.
Qed.

Theorem srsa_lambda_type_annihilator_pin :
  powm 2 (pin_lam + 1) pin_N = 2 /\
  powm 2 pin_lam pin_N = 1 /\
  (pin_lam | pin_lam).
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  exists 1. lia.
Qed.

Theorem srsa_lambda_type_miller_splits :
  miller_splits 2 pin_N pin_sqrt1_mixed /\
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p.
Proof.
  split.
  - unfold miller_splits. vm_compute. split; [reflexivity|].
    split; discriminate.
  - vm_compute. reflexivity.
Qed.

Theorem srsa_lambda_type_miller_factors :
  let f := Z.gcd (pin_sqrt1_mixed - 1) pin_N in
  1 < f /\ f < pin_N /\ (f | pin_N).
Proof.
  apply (nontrivial_sqrt1_splits pin_p pin_q pin_sqrt1_mixed pin_p_prime pin_q_prime
           ltac:(discriminate)).
  - vm_compute. reflexivity.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.

Lemma prime_7 : Z.prime 7.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6) by lia.
  intuition subst; reflexivity.
Qed.

Theorem srsa_safeprime_lambda_30 :
  lambda_semiprime pin_77_p pin_77_q = pin_77_lam.
Proof. vm_compute. reflexivity. Qed.

Theorem srsa_safeprime_lambda_type :
  powm pin_77_x (pin_77_lam + 1) pin_77 = pin_77_x /\
  powm pin_77_x pin_77_lam pin_77 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem srsa_safeprime_g0_square :
  powm (powm pin_77_x 15 pin_77) 2 pin_77 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem srsa_safeprime_miller_gcd :
  Z.gcd (powm pin_77_x 15 pin_77 - 1) pin_77 = pin_77_p.
Proof. vm_compute. reflexivity. Qed.

Theorem srsa_safeprime_miller_factors :
  Problem_Factor pin_77 (Z.gcd (powm pin_77_x 15 pin_77 - 1) pin_77).
Proof.
  rewrite srsa_safeprime_miller_gcd. unfold Problem_Factor.
  split; [lia|]. exists pin_77_q. reflexivity.
Qed.

(** ** Residual leaf (open: solver ⇒ factor is the live target) *)

Definition srsa_residual_leaf (N lam y x e : Z) : Prop :=
  Z.coprime y N /\
  Problem_StrongRSA N y x e /\
  Z.Odd e /\
  Z.gcd e lam = 1 /\
  ~ (lam | e - 1).

Theorem srsa_residual_pin :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof.
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 1; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem srsa_residual_pin187 :
  srsa_residual_leaf pin187_N pin187_lam pin187_y pin187_x pin187_e.
Proof.
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 1; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

(** A residual solver returns a leftover pair for every unit [y].
    A single leftover pair does not always split ([matching_247_*]).
    Whether the *solver* constructs a factor is unproved and on-goal.
    Do not inhabit by projecting [rsa_p].  Well-posed GRA fragment:
    [gra_nodiv_integer_eth_root_forbidden], the residual dichotomy,
    and low-degree vanishing on units in [SrsaResidualGRA]. *)
Definition residual_solver (N lam : Z) : Type :=
  forall y, Z.coprime y N ->
    { xe : Z * Z | let '(x, e) := xe in srsa_residual_leaf N lam y x e }.

Definition residual_solver_constructs_factor_open_named : Prop :=
  forall (R : RSAInstance) (Solve : residual_solver (rsa_N R) (rsa_lambda R)),
    exists f, Problem_Factor (rsa_N R) f.

(** ** Self-randomization and related queries *)

Theorem srsa_fixed_e_rerand :
  forall N x e y r,
    N <> 0 ->
    0 <= e ->
    powm x e N = y ->
    powm (x * r) e N = (y * powm r e N) mod N.
Proof.
  intros N x e y r Hn He Hy.
  unfold powm in Hy |- *.
  rewrite Z.pow_mul_l, Z.mul_mod by lia.
  rewrite Hy. rewrite Z.mul_mod by lia. reflexivity.
Qed.

Theorem srsa_fixed_e_rerand_pin :
  powm (pin_x * 2) pin_e pin_N = (pin_y * powm 2 pin_e pin_N) mod pin_N.
Proof.
  apply srsa_fixed_e_rerand; [discriminate | lia |].
  vm_compute. reflexivity.
Qed.

Theorem srsa_poly_e_not_rerand_invariant :
  poly_eval poly_X (pin_y * Z.pow 2 pin_e) <> poly_eval poly_X pin_y.
Proof.
  rewrite poly_eval_X. rewrite poly_eval_X. vm_compute. discriminate.
Qed.

Theorem srsa_related_y_square :
  forall N x1 e1 y x2 e2,
    N <> 0 ->
    0 <= e1 ->
    0 <= e2 ->
    powm x1 e1 N = y ->
    powm x2 e2 N = powm y 2 N ->
    powm x2 e2 N = powm x1 (2 * e1) N.
Proof.
  intros N x1 e1 y x2 e2 Hn He1 He2 Hy Hy2.
  rewrite Hy2.
  replace (2 * e1) with (e1 * 2) by lia.
  rewrite powm_mul_r by lia.
  rewrite Hy. reflexivity.
Qed.

Theorem srsa_related_pin :
  powm pin_x (2 * pin_e) pin_N = powm pin_y 2 pin_N.
Proof. vm_compute. reflexivity. Qed.

(** ** SAGM handle still peels *)

Theorem srsa_sagm_handle_unit :
  Z.gcd (sagm_eval pin_N sagm_pin_g sagm_pin_h {| sagm_a := 2; sagm_b := 1 |})
        pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem srsa_sagm_lambda_type_peel :
  let y := sagm_eval pin_N sagm_pin_g sagm_pin_h {| sagm_a := 2; sagm_b := 1 |} in
  powm y (pin_lam + 1) pin_N = y.
Proof. vm_compute. reflexivity. Qed.

Theorem srsa_sagm_product_reused :
  sagm_eval pin_N sagm_pin_g sagm_pin_h
    (sagm_mul {| sagm_a := 2; sagm_b := 1 |} {| sagm_a := 1; sagm_b := 3 |}) =
    (sagm_eval pin_N sagm_pin_g sagm_pin_h {| sagm_a := 2; sagm_b := 1 |} *
     sagm_eval pin_N sagm_pin_g sagm_pin_h {| sagm_a := 1; sagm_b := 3 |})
      mod pin_N.
Proof. apply sagm_product_adds_exponents. Qed.

(** ** Four square roots of 1; mixed splits, [−1] does not *)

Theorem srsa_sqrt1_120_splits :
  powm pin_sqrt1_mixed2 2 pin_N = 1 /\
  Z.gcd (pin_sqrt1_mixed2 - 1) pin_N = pin_q /\
  Z.gcd (pin_sqrt1_mixed2 + 1) pin_N = pin_p.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem srsa_minus1_no_split :
  powm (pin_N - 1) 2 pin_N = 1 /\
  Z.gcd (pin_N - 2) pin_N = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem srsa_120_plus_1 :
  Z.gcd (pin_p * pin_p) pin_N = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem srsa_miller_66 :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem srsa_four_sqrt1 :
  powm 1 2 pin_N = 1 /\
  powm (pin_N - 1) 2 pin_N = 1 /\
  powm pin_sqrt1_mixed 2 pin_N = 1 /\
  powm pin_sqrt1_mixed2 2 pin_N = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.
