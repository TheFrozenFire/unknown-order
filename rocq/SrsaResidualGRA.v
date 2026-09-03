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
Require Import StrongRSAPeel.
Require Import GenericRing.
Require Import TwoPrimary.

Open Scope Z_scope.

(** * Residual GRA dichotomy

    A generic-ring algorithm that writes a *residual-shaped*
    Strong-RSA witness (odd [e], [gcd(e,λ)=1], [λ] ndiv [e−1])
    either gcd-leaks a proper factor of [N] or is forbidden by a
    degree / leading-coefficient identity.  [e = λ+1] fails those
    residual tests, so [GConst (λ+1)] solving Strong RSA on every
    unit without splitting is not a counterexample.  A constant
    leftover root that inverts one pin [y] and misses another unit
    is not a GRA of every unit.

    Generic-ring inroad on [residual_solver_constructs_factor_open_named],
    not a proof of that unrestricted name, and not RSA ≡ or ≢
    factoring.  Cross-confirmed by [cas/146], [cas/148], [cas/149],
    [cas/150], [cas/151], and [cas/152]. *)

(** ** Residual-shaped exponents *)

Definition residual_shaped_e (e lam : Z) : Prop :=
  1 < e /\
  Z.Odd e /\
  Z.gcd e lam = 1 /\
  ~ (lam | e - 1).

Theorem residual_shaped_e_3 :
  residual_shaped_e 3 80.
Proof.
  unfold residual_shaped_e.
  split; [lia|].
  split; [exists 1; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem residual_shaped_e_7 :
  residual_shaped_e 7 80.
Proof.
  unfold residual_shaped_e.
  split; [lia|].
  split; [exists 3; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

(** ** [λ+1] is outside the residual class *)

Theorem not_residual_shaped_e_81 :
  ~ residual_shaped_e 81 80.
Proof.
  unfold residual_shaped_e.
  intros [_ [_ [_ Hnd]]].
  apply Hnd. exists 1. reflexivity.
Qed.

Theorem lambda_plus_one_witness_not_residual :
  forall y,
    ~ srsa_residual_leaf pin_N 80 y y 81.
Proof.
  intros y [_ [_ [_ [_ Hnd]]]].
  apply Hnd. exists 1. lia.
Qed.

Theorem residual_gra_const81_independent_of_y :
  gra_eval_Z [GConst 81] 36 3%nat = 81 /\
  gra_eval_Z [GConst 81] 8 3%nat = 81.
Proof. apply gra_const_81. Qed.

Theorem residual_gra_const81_gcd_is_1 :
  Z.gcd 81 pin_N = 1.
Proof. apply gra_const_81_does_not_factor. Qed.

Theorem residual_gra_const81_solves_sRSA_not_residual :
  forall y,
    Z.coprime y pin_N ->
    Problem_StrongRSA pin_N (y mod pin_N) (y mod pin_N) 81 /\
    ~ srsa_residual_leaf pin_N 80 (y mod pin_N) (y mod pin_N) 81.
Proof.
  intros y Hcop. split.
  - apply gra_const_lambda_plus_one_solves_sRSA_without_factoring. exact Hcop.
  - apply lambda_plus_one_witness_not_residual.
Qed.

(** ** Constant leftover inverts one [y], not every unit *)

Theorem residual_gra_const42_inverts_pin_not_8 :
  gra_eval_Z [GConst 42] 36 3%nat = 42 /\
  powm 42 3 pin_N = 36 /\
  Z.coprime 8 pin_N /\
  powm 42 3 pin_N <> 8.
Proof.
  split; [apply gra_const42|].
  split; [apply gra_nodiv_const42_inverts_36|].
  split; [vm_compute; reflexivity|].
  apply gra_nodiv_const42_fails_on_8.
Qed.

Theorem residual_gra_const42_misses_unit_2 :
  Z.coprime 2 pin_N /\
  powm 42 3 pin_N <> 2.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

(** ** Degree / leading-coefficient fork for residual-shaped [e] *)

Theorem residual_shaped_forbids_rational_Pe_XQe :
  forall e lam dp dq,
    residual_shaped_e e lam ->
    e * dp <> 1 + e * dq.
Proof.
  intros e lam dp dq [He _].
  apply rational_Pe_minus_XQe_leading. exact He.
Qed.

Theorem residual_shaped_e3_leading :
  forall dp dq, 3 * dp <> 1 + 3 * dq.
Proof.
  intros dp dq.
  apply (residual_shaped_forbids_rational_Pe_XQe 3 80 dp dq).
  apply residual_shaped_e_3.
Qed.

Theorem residual_shaped_e7_leading :
  forall dp dq, 7 * dp <> 1 + 7 * dq.
Proof.
  intros dp dq.
  apply (residual_shaped_forbids_rational_Pe_XQe 7 80 dp dq).
  apply residual_shaped_e_7.
Qed.

Theorem residual_gra_Xe_minus_X_N_ndiv_linear :
  forall e,
    (2 <= e)%nat ->
    nth 1%nat (poly_sub (poly_Xn e) poly_X) 0 = -1 /\
    ~ (pin_N | -1).
Proof.
  intros e He. split.
  - apply Xe_minus_X_linear_coeff. exact He.
  - intros [k Hk]. nia.
Qed.

Theorem residual_gra_X3_minus_X_N_ndiv_linear :
  nth 1%nat (poly_sub (poly_Xn 3) poly_X) 0 = -1 /\
  ~ (pin_N | -1).
Proof. apply residual_gra_Xe_minus_X_N_ndiv_linear. lia. Qed.

Theorem residual_gra_X7_minus_X_N_ndiv_linear :
  nth 1%nat (poly_sub (poly_Xn 7) poly_X) 0 = -1 /\
  ~ (pin_N | -1).
Proof. apply residual_gra_Xe_minus_X_N_ndiv_linear. lia. Qed.

(** Equality-test and [GInv] of a non-unit still leak a proper
    factor.  Residual-shaped [e] does not disable those leaks. *)

Theorem residual_gra_eq_leak_factors :
  Problem_Factor pin_N (gra_eq_leak pin_N gra_eq_prog 36 9%nat 0%nat).
Proof. apply gra_eq_leak_factors. Qed.

Theorem residual_gra_inv_nonunit_factors :
  Problem_Factor pin_N (gra_eval_Z gra_inv11_prog 36 4%nat).
Proof. apply gra_inv_nonunit_factors. Qed.

(** ** Division-free tape denotes a polynomial; integer [P^e = X]
    is forbidden for residual-shaped [e ≥ 2].  Identity tape
    (output [y]) is not residual invert on the pin. *)

Theorem residual_gra_nodiv_empty_is_nodiv :
  Forall is_nodiv [].
Proof. constructor. Qed.

Theorem residual_gra_identity_tape_is_y :
  gra_eval pin_N [] 36 2%nat = 36.
Proof. reflexivity. Qed.

Theorem residual_gra_identity_tape_not_cube :
  powm 36 3 pin_N <> 36.
Proof. vm_compute. discriminate. Qed.

Theorem residual_gra_nodiv_integer_identity_forbidden :
  forall ops e N out,
    Forall is_nodiv ops ->
    residual_shaped_e (Z.of_nat e) 80 ->
    (2 <= e)%nat ->
    (forall y, Z.pow (gra_eval N ops y out) (Z.of_nat e) = y) ->
    False.
Proof.
  intros ops e N out Hop [He _] H2 Hall.
  apply (gra_nodiv_integer_eth_root_forbidden ops e N out); assumption.
Qed.

Theorem residual_gra_nodiv_cube_identity_forbidden :
  forall ops N out,
    Forall is_nodiv ops ->
    (forall y, Z.pow (gra_eval N ops y out) 3 = y) ->
    False.
Proof.
  intros ops N out Hop Hall.
  apply (gra_nodiv_integer_eth_root_forbidden ops 3%nat N out);
    [exact Hop | lia | exact Hall].
Qed.

Theorem residual_gra_mul_denotes_square :
  gra_eval pin_N [GMul 2%nat 2%nat] 36 3%nat = 36 * 36.
Proof. apply gra_nodiv_mul_denotes_square. Qed.

(** ** Low-degree vanishing on units

    Denotation is load-bearing: the identity tape denotes [X], so
    [y^3 − y] is [eval(X^3 − X, y)]; [GConst c] denotes [[c]].
    [X^3 − X] has degree 3, strictly below [p−1=10] and [q−1=16].
    Its roots mod 11 are [0,1,10], so it does not vanish on [𝔽_11*]
    (unit 2 is a counterexample).  A constant [P] has [P^e − X]
    linear coeff [−1], so [N] cannot divide every coefficient.
    High-degree functional-on-units maps ([X^d], [d=27]) are not
    forbidden by this degree bound.  The general roots bound:
    [deg Q < 10] and vanishing on [1..10] (all of [𝔽_11*] and
    units of [Z/187Z]) forces [11] to divide every coefficient.
    Vanishing on [(Z/NZ)*] does not sample [11] mod [17], so this
    is not a [17]-divides claim. *)

Theorem residual_identity_is_low_degree :
  poly_degree (poly_Pe_minus_X poly_X 3%nat) = 3%nat /\
  (3 < 10)%nat /\
  (3 < 16)%nat.
Proof. split; [apply poly_degree_X3_minus_X | lia]. Qed.

Lemma residual_X3_eval :
  forall a, poly_eval (poly_Pe_minus_X poly_X 3%nat) a = a * a * a - a.
Proof. apply poly_eval_X3_minus_X. Qed.

Lemma residual_X3_not_div_11_mid :
  forall a, a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 ->
    ~ (11 | a * a * a - a).
Proof.
  intros a Ha [k Hk].
  repeat (destruct Ha as [Heq|Ha]; [subst a; lia|]).
  subst a. lia.
Qed.

Theorem residual_X3_roots_mod_11 :
  forall a,
    0 <= a < 11 ->
    (11 | poly_eval (poly_Pe_minus_X poly_X 3%nat) a) ->
    a = 0 \/ a = 1 \/ a = 10.
Proof.
  intros a Ha Hdiv. rewrite residual_X3_eval in Hdiv.
  destruct (Z.eq_dec a 0) as [Hz|Hnz]; [left; exact Hz|].
  destruct (Z.eq_dec a 1) as [Hone|Hnone]; [right; left; exact Hone|].
  destruct (Z.eq_dec a 10) as [Hten|Hnten]; [right; right; exact Hten|].
  exfalso. apply (residual_X3_not_div_11_mid a); [lia|exact Hdiv].
Qed.

Theorem residual_X3_unit_2_not_root_mod_11 :
  0 < 2 < 11 /\ ~ (11 | poly_eval (poly_Pe_minus_X poly_X 3%nat) 2).
Proof.
  split; [lia|]. rewrite residual_X3_eval. apply residual_X3_not_div_11_mid. lia.
Qed.

Lemma residual_X3_not_div_17_mid :
  forall a,
    a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/
    a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 ->
    ~ (17 | a * a * a - a).
Proof.
  intros a Ha [k Hk].
  repeat (destruct Ha as [Heq|Ha]; [subst a; lia|]).
  subst a. lia.
Qed.

Theorem residual_X3_unit_2_not_root_mod_17 :
  0 < 2 < 17 /\ ~ (17 | poly_eval (poly_Pe_minus_X poly_X 3%nat) 2).
Proof.
  split; [lia|]. rewrite residual_X3_eval. apply residual_X3_not_div_17_mid. lia.
Qed.

Theorem residual_X3_roots_mod_17 :
  forall a,
    0 <= a < 17 ->
    (17 | poly_eval (poly_Pe_minus_X poly_X 3%nat) a) ->
    a = 0 \/ a = 1 \/ a = 16.
Proof.
  intros a Ha Hdiv. rewrite residual_X3_eval in Hdiv.
  destruct (Z.eq_dec a 0) as [Hz|Hnz]; [left; exact Hz|].
  destruct (Z.eq_dec a 1) as [Hone|Hnone]; [right; left; exact Hone|].
  destruct (Z.eq_dec a 16) as [Hlast|Hnlast]; [right; right; exact Hlast|].
  exfalso. apply (residual_X3_not_div_17_mid a); [lia|exact Hdiv].
Qed.

Theorem residual_const_Pe_minus_X_nth1 :
  forall c, nth 1%nat (poly_Pe_minus_X [c] 3%nat) 0 = -1.
Proof. intros c. apply const_Pe_minus_X_nth1. Qed.

Theorem residual_const_N_ndiv_linear :
  forall c, ~ (pin_N | nth 1%nat (poly_Pe_minus_X [c] 3%nat) 0).
Proof.
  intros c. rewrite residual_const_Pe_minus_X_nth1. intros [k Hk]. nia.
Qed.

Theorem residual_nodiv_identity_denotes_X :
  forall y, gra_eval pin_N [] y 2%nat = poly_eval poly_X y.
Proof. intros y. rewrite gra_nodiv_denotes by constructor. reflexivity. Qed.

Theorem residual_identity_cube_minus_y :
  forall y,
    Z.pow (gra_eval pin_N [] y 2%nat) (Z.of_nat 3%nat) - y =
      poly_eval (poly_Pe_minus_X poly_X 3%nat) y.
Proof.
  intros y.
  rewrite residual_nodiv_identity_denotes_X, poly_eval_Pe_minus_X, poly_eval_X.
  reflexivity.
Qed.

Theorem residual_nodiv_const_is_nodiv :
  forall c, Forall is_nodiv [GConst c].
Proof. intros c. repeat constructor. Qed.

Theorem residual_nodiv_const_denotes :
  forall c y, gra_eval pin_N [GConst c] y 3%nat = poly_eval [c] y.
Proof.
  intros c y.
  rewrite gra_nodiv_denotes by apply residual_nodiv_const_is_nodiv.
  cbn [gra_run_poly step_poly].
  rewrite <- slp_init_length.
  rewrite nth_app_last.
  unfold poly_eval. lia.
Qed.

Theorem residual_low_degree_identity_not_all_Fp_units :
  (3 < 10)%nat /\
  ~ (11 | Z.pow (gra_eval pin_N [] 2 2%nat) (Z.of_nat 3%nat) - 2).
Proof.
  split; [lia|].
  rewrite residual_identity_cube_minus_y.
  destruct residual_X3_unit_2_not_root_mod_11 as [_ Hnd].
  exact Hnd.
Qed.

(** ** Roots bound: low-degree + vanish on [1..10] ⇒ [11] | coeffs

    Denotation is load-bearing: a nodiv tape that cube-inverts
    (or [e]-inverts) every pin unit denotes a [Q = P^e − X] that
    vanishes on [1..10].  If that [Q] is low-degree, every
    coefficient is [0] mod [11].  Identity and [GConst] have
    linear coeff [−1], so they cannot vanish.  Cross-confirmed
    by [cas/149]. *)

Definition pin_Fp_star : list Z := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].

Lemma pin_Fp_star_length : length pin_Fp_star = 10%nat.
Proof. reflexivity. Qed.

Lemma forall_pin_Fp_star :
  forall (R : Z -> Prop),
    (forall y, 1 <= y <= 10 -> R y) ->
    Forall R pin_Fp_star.
Proof.
  intros R HR. unfold pin_Fp_star.
  repeat (apply Forall_cons; [apply HR; lia|]).
  apply Forall_nil.
Qed.

Lemma pin_Fp_star_coprime :
  Forall (fun y => Z.coprime y pin_N) pin_Fp_star.
Proof.
  unfold pin_Fp_star.
  repeat (apply Forall_cons; [vm_compute; reflexivity|]).
  apply Forall_nil.
Qed.

Lemma pin_Fp_star_distinct_mod_11 :
  pairwise_distinct_mod 11 pin_Fp_star.
Proof.
  unfold pin_Fp_star, pairwise_distinct_mod.
  repeat split;
    repeat (apply Forall_cons; [intros [k Hk]; lia|]);
    apply Forall_nil.
Qed.

Theorem residual_low_degree_units_divides_11 :
  forall Q,
    (poly_degree Q < 10)%nat ->
    (forall y, 1 <= y <= 10 -> (11 | poly_eval Q y)) ->
    forall i, (11 | nth i Q 0).
Proof.
  intros Q Hdeg Hall i.
  apply (poly_prime_roots_divides 11 pin_Fp_star Q).
  - apply prime_11.
  - apply pin_Fp_star_distinct_mod_11.
  - rewrite pin_Fp_star_length. exact Hdeg.
  - apply forall_pin_Fp_star. exact Hall.
Qed.

Theorem residual_nodiv_low_degree_units_divides_11 :
  forall ops out e,
    Forall is_nodiv ops ->
    (poly_degree (poly_Pe_minus_X (nth out (gra_run_poly ops slp_init_poly) []) e)
       < 10)%nat ->
    (forall y, 1 <= y <= 10 ->
      (11 | Z.pow (gra_eval pin_N ops y out) (Z.of_nat e) - y)) ->
    forall i,
      (11 | nth i (poly_Pe_minus_X (nth out (gra_run_poly ops slp_init_poly) []) e) 0).
Proof.
  intros ops out e Hop Hdeg Hall i.
  apply residual_low_degree_units_divides_11; [exact Hdeg|].
  intros y Hy.
  rewrite poly_eval_Pe_minus_X.
  rewrite <- (gra_nodiv_denotes ops pin_N y out Hop).
  apply Hall. exact Hy.
Qed.

Theorem residual_identity_nth1_ndiv_11 :
  ~ (11 | nth 1%nat (poly_Pe_minus_X poly_X 3%nat) 0).
Proof. rewrite X3_minus_X_nth1. intros [k Hk]. nia. Qed.

Theorem residual_identity_cannot_vanish_on_Fp_star :
  (poly_degree (poly_Pe_minus_X poly_X 3%nat) < 10)%nat /\
  ~ (forall y, 1 <= y <= 10 ->
       (11 | poly_eval (poly_Pe_minus_X poly_X 3%nat) y)).
Proof.
  split; [rewrite poly_degree_X3_minus_X; lia|].
  intros Hall.
  apply residual_identity_nth1_ndiv_11.
  apply residual_low_degree_units_divides_11.
  - rewrite poly_degree_X3_minus_X. lia.
  - exact Hall.
Qed.

Lemma residual_const_Pe_degree :
  forall c, poly_degree (poly_Pe_minus_X [c] 3%nat) = 1%nat.
Proof. intros c. vm_compute. reflexivity. Qed.

Theorem residual_const_cannot_vanish_on_Fp_star :
  forall c,
    (poly_degree (poly_Pe_minus_X [c] 3%nat) < 10)%nat /\
    ~ (forall y, 1 <= y <= 10 ->
         (11 | poly_eval (poly_Pe_minus_X [c] 3%nat) y)).
Proof.
  intros c. split; [rewrite residual_const_Pe_degree; lia|].
  intros Hall.
  pose proof (residual_low_degree_units_divides_11
                (poly_Pe_minus_X [c] 3%nat)
                ltac:(rewrite residual_const_Pe_degree; lia)
                Hall 1%nat) as Hdiv.
  rewrite residual_const_Pe_minus_X_nth1 in Hdiv.
  destruct Hdiv as [k Hk]. nia.
Qed.

(** ** CRT lift: vanish on [(Z/NZ)*] + low degree ⇒ [N] | coeffs

    Residue [11] is missing from the [𝔽_17*] sample of [(Z/NZ)*].
    [crt2 11 17 1 11] lifts it to a unit ([45]).  Then [deg < 10 < 16]
    forces [17] to divide every coefficient, hence [N].  High-degree
    [X^d] is not forbidden.  Cross-confirmed by [cas/150]. *)

Definition pin_Fq_star : list Z :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16].

Lemma pin_Fq_star_length : length pin_Fq_star = 16%nat.
Proof. reflexivity. Qed.

Lemma forall_pin_Fq_star :
  forall (R : Z -> Prop),
    (forall y, 1 <= y <= 16 -> R y) ->
    Forall R pin_Fq_star.
Proof.
  intros R HR. unfold pin_Fq_star.
  repeat (apply Forall_cons; [apply HR; lia|]).
  apply Forall_nil.
Qed.

Lemma pin_Fq_star_distinct_mod_17 :
  pairwise_distinct_mod 17 pin_Fq_star.
Proof.
  unfold pin_Fq_star, pairwise_distinct_mod.
  repeat split;
    repeat (apply Forall_cons; [intros [k Hk]; lia|]);
    apply Forall_nil.
Qed.

Lemma pin_1_16_coprime_N :
  forall a, 1 <= a <= 16 -> a <> 11 -> Z.coprime a pin_N.
Proof.
  intros a Ha Hne.

  apply (proj2 (coprime_semiprime 11 17 a prime_11 prime_17 ltac:(lia))).
  split.
  - rewrite coprime_comm. apply Z.coprime_prime_l_iff; [apply prime_11|].
    intros [k Hk]. nia.
  - rewrite coprime_comm. apply Z.coprime_prime_l_iff; [apply prime_17|].
    intros [k Hk]. nia.
Qed.

Definition pin_crt_lift_11 : Z := crt2 11 17 1 11.

Lemma pin_crt_lift_11_spec :
  pin_crt_lift_11 = 45 /\
  pin_crt_lift_11 mod 11 = 1 /\
  pin_crt_lift_11 mod 17 = 11 /\
  Z.coprime pin_crt_lift_11 pin_N.
Proof. unfold pin_crt_lift_11, crt2. vm_compute. repeat split; reflexivity. Qed.

Lemma pin_N_divides_11 : forall n, (pin_N | n) -> (11 | n).
Proof.
  intros n Hn. apply (Z.divide_trans 11 pin_N n); [exists pin_q; reflexivity | exact Hn].
Qed.

Lemma pin_N_divides_17 : forall n, (pin_N | n) -> (17 | n).
Proof.
  intros n Hn. apply (Z.divide_trans 17 pin_N n); [exists 11; reflexivity | exact Hn].
Qed.

Lemma pin_11_17_divides_N :
  forall c, (11 | c) -> (17 | c) -> (pin_N | c).
Proof.
  intros c H11 H17.

  apply divide_by_coprime_product; [|exact H11 | exact H17].
  apply prime_coprime_distinct; [apply prime_11 | apply prime_17 | lia].
Qed.

Lemma residual_ZN_units_vanish_at_Fq :
  forall Q,
    (forall y, Z.coprime y pin_N -> (pin_N | poly_eval Q y)) ->
    forall a, 1 <= a <= 16 -> (17 | poly_eval Q a).
Proof.
  intros Q Hall a Ha.
  destruct (Z.eq_dec a 11) as [H11 | Hne].
  - subst a.
    destruct pin_crt_lift_11_spec as [Heq [_ [Hmod Hcop]]].
    pose proof (Hall _ Hcop) as HyN.
    pose proof (pin_N_divides_17 _ HyN) as Hy17.
    assert (Hcong : (17 | pin_crt_lift_11 - 11)).
    { apply Z.mod_divide; [lia|].
      rewrite Zminus_mod, Hmod, Z.sub_diag, Z.mod_0_l by lia. reflexivity. }
    pose proof (poly_eval_cong Q 11 pin_crt_lift_11 17 Hcong) as Hdiff.
    replace (poly_eval Q 11) with
      (poly_eval Q pin_crt_lift_11 - (poly_eval Q pin_crt_lift_11 - poly_eval Q 11))
      by ring.
    apply Z.divide_sub_r; [exact Hy17 | exact Hdiff].
  - apply pin_N_divides_17. apply Hall. apply pin_1_16_coprime_N; [exact Ha | exact Hne].
Qed.

Theorem residual_low_degree_ZN_units_divides_17 :
  forall Q,
    (poly_degree Q < 10)%nat ->
    (forall y, Z.coprime y pin_N -> (pin_N | poly_eval Q y)) ->
    forall i, (17 | nth i Q 0).
Proof.
  intros Q Hdeg Hall i.
  apply (poly_prime_roots_divides 17 pin_Fq_star Q).
  - apply prime_17.
  - apply pin_Fq_star_distinct_mod_17.
  - rewrite pin_Fq_star_length. lia.
  - apply forall_pin_Fq_star.
    intros a Ha. apply residual_ZN_units_vanish_at_Fq; [exact Hall | exact Ha].
Qed.

Theorem residual_low_degree_ZN_units_divides_N :
  forall Q,
    (poly_degree Q < 10)%nat ->
    (forall y, Z.coprime y pin_N -> (pin_N | poly_eval Q y)) ->
    forall i, (pin_N | nth i Q 0).
Proof.
  intros Q Hdeg Hall i.
  apply pin_11_17_divides_N.
  - apply residual_low_degree_units_divides_11; [exact Hdeg|].
    intros y Hy. apply pin_N_divides_11. apply Hall.
    apply pin_1_16_coprime_N; lia.
  - apply residual_low_degree_ZN_units_divides_17; [exact Hdeg | exact Hall].
Qed.

Theorem residual_nodiv_low_degree_ZN_units_divides_N :
  forall ops out e,
    Forall is_nodiv ops ->
    (poly_degree (poly_Pe_minus_X (nth out (gra_run_poly ops slp_init_poly) []) e)
       < 10)%nat ->
    (forall y, Z.coprime y pin_N ->
      (pin_N | Z.pow (gra_eval pin_N ops y out) (Z.of_nat e) - y)) ->
    forall i,
      (pin_N | nth i (poly_Pe_minus_X (nth out (gra_run_poly ops slp_init_poly) []) e) 0).
Proof.
  intros ops out e Hop Hdeg Hall i.
  apply residual_low_degree_ZN_units_divides_N; [exact Hdeg|].
  intros y Hy.
  rewrite poly_eval_Pe_minus_X.
  rewrite <- (gra_nodiv_denotes ops pin_N y out Hop).
  apply Hall. exact Hy.
Qed.

Theorem residual_identity_cannot_vanish_on_ZN_units :
  (poly_degree (poly_Pe_minus_X poly_X 3%nat) < 10)%nat /\
  ~ (forall y, Z.coprime y pin_N ->
       (pin_N | poly_eval (poly_Pe_minus_X poly_X 3%nat) y)).
Proof.
  split; [rewrite poly_degree_X3_minus_X; lia|].
  intros Hall.
  pose proof (residual_low_degree_ZN_units_divides_N
                (poly_Pe_minus_X poly_X 3%nat)
                ltac:(rewrite poly_degree_X3_minus_X; lia)
                Hall 1%nat) as Hdiv.
  rewrite X3_minus_X_nth1 in Hdiv.
  destruct Hdiv as [k Hk]. nia.
Qed.

Theorem residual_const_cannot_vanish_on_ZN_units :
  forall c,
    (poly_degree (poly_Pe_minus_X [c] 3%nat) < 10)%nat /\
    ~ (forall y, Z.coprime y pin_N ->
         (pin_N | poly_eval (poly_Pe_minus_X [c] 3%nat) y)).
Proof.
  intros c. split; [rewrite residual_const_Pe_degree; lia|].
  intros Hall.
  pose proof (residual_low_degree_ZN_units_divides_N
                (poly_Pe_minus_X [c] 3%nat)
                ltac:(rewrite residual_const_Pe_degree; lia)
                Hall 1%nat) as Hdiv.
  rewrite residual_const_Pe_minus_X_nth1 in Hdiv.
  destruct Hdiv as [k Hk]. nia.
Qed.

(** ** Nodiv tape degree bound

    Denotation is load-bearing: a handle of [gra_deg_bound ≤ 3]
    has [deg P ≤ 3], so [deg(P^3−X) < 10].  One squaring is bound
    [2]; [X^2·X] is [3]; two squarings are [4], outside the window.
    [X^{27}] is not low-degree.  Exact [deg(PQ)=deg P+deg Q] is
    [poly_degree_mul]; the [≤] bound is the tape-window payload.
    Cross-confirmed by [cas/151]. *)

Theorem residual_nodiv_bound_le3_Q_lt10 :
  forall ops out,
    Forall is_nodiv ops ->
    (nth out (gra_deg_bound ops slp_init_deg) 0%nat <= 3)%nat ->
    (poly_degree (poly_Pe_minus_X (nth out (gra_run_poly ops slp_init_poly) []) 3%nat)
       < 10)%nat.
Proof.
  intros ops out Hop Hbound.
  apply poly_degree_Pe_minus_X_e3_degP_le3_lt10.
  pose proof (gra_nodiv_degree_le ops out Hop) as Hle.
  lia.
Qed.

Theorem residual_nodiv_short_ZN_units_divides_N :
  forall ops out,
    Forall is_nodiv ops ->
    (nth out (gra_deg_bound ops slp_init_deg) 0%nat <= 3)%nat ->
    (forall y, Z.coprime y pin_N ->
      (pin_N | Z.pow (gra_eval pin_N ops y out) 3 - y)) ->
    forall i,
      (pin_N | nth i (poly_Pe_minus_X (nth out (gra_run_poly ops slp_init_poly) []) 3%nat) 0).
Proof.
  intros ops out Hop Hbound Hall i.
  apply residual_nodiv_low_degree_ZN_units_divides_N.
  - exact Hop.
  - apply residual_nodiv_bound_le3_Q_lt10; [exact Hop | exact Hbound].
  - intros y Hy. apply Hall. exact Hy.
Qed.

Theorem residual_identity_bound_is_1 :
  nth 2%nat (gra_deg_bound [] slp_init_deg) 0%nat = 1%nat.
Proof. apply gra_deg_bound_identity. Qed.

Theorem residual_square_bound_is_2 :
  nth 3%nat (gra_deg_bound [GMul 2%nat 2%nat] slp_init_deg) 0%nat = 2%nat.
Proof. apply gra_deg_bound_square. Qed.

Theorem residual_x3_bound_is_3 :
  nth 4%nat (gra_deg_bound [GMul 2%nat 2%nat; GMul 3%nat 2%nat] slp_init_deg) 0%nat = 3%nat.
Proof. apply gra_deg_bound_x3. Qed.

Theorem residual_two_squarings_bound_is_4 :
  nth 4%nat (gra_deg_bound [GMul 2%nat 2%nat; GMul 3%nat 3%nat] slp_init_deg) 0%nat = 4%nat.
Proof. apply gra_deg_bound_x4. Qed.

Theorem residual_two_squarings_outside_window :
  (3 * 4 >= 10)%nat.
Proof. lia. Qed.

Theorem residual_trapdoor_deg27_outside_window :
  (3 * 27 >= 10)%nat.
Proof. lia. Qed.

(** ** Exact degree; square and cube tapes miss units

    Over [Z], [deg(X·X)=2] and [deg((X^2)^3−X)=6]; [deg(X^3)=3]
    and [deg((X^3)^3−X)=9].  Both [Q] have linear coeff [−1], so
    [N] cannot divide every coefficient, and unit [2] is not a
    root.  Trapdoor [X^{27}] inverts the pin and cubes back, but
    sits outside the low-degree window: it is not forbidden as a
    map on units.  The low-degree nodiv GRA class on this pin is
    settled.  Not a proof of
    [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/152]. *)

Theorem residual_square_denotes_X2 :
  nth 3%nat (gra_run_poly [GMul 2%nat 2%nat] slp_init_poly) [] =
    poly_mul poly_X poly_X.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_square_degree_eq_bound :
  poly_degree (nth 3%nat (gra_run_poly [GMul 2%nat 2%nat] slp_init_poly) [])
    = 2%nat /\
  nth 3%nat (gra_deg_bound [GMul 2%nat 2%nat] slp_init_deg) 0%nat = 2%nat.
Proof.
  split.
  - rewrite residual_square_denotes_X2. apply poly_degree_XX_is_2.
  - apply gra_deg_bound_square.
Qed.

Theorem residual_square_eval :
  forall y, gra_eval pin_N [GMul 2%nat 2%nat] y 3%nat = y * y.
Proof.
  intros y.
  rewrite gra_nodiv_denotes by apply gra_nodiv_mul_is_nodiv.
  rewrite residual_square_denotes_X2, poly_eval_mul, !poly_eval_X.
  reflexivity.
Qed.

Theorem residual_square_Q_degree_is_6 :
  poly_degree (poly_Pe_minus_X
    (nth 3%nat (gra_run_poly [GMul 2%nat 2%nat] slp_init_poly) []) 3%nat)
    = 6%nat.
Proof.
  rewrite residual_square_denotes_X2. apply poly_degree_X6_minus_X.
Qed.

Theorem residual_square_Q_nth1 :
  nth 1%nat (poly_Pe_minus_X
    (nth 3%nat (gra_run_poly [GMul 2%nat 2%nat] slp_init_poly) []) 3%nat) 0
    = -1.
Proof.
  rewrite residual_square_denotes_X2. apply X6_minus_X_nth1.
Qed.

Theorem residual_square_cannot_vanish_on_ZN_units :
  (poly_degree (poly_Pe_minus_X
     (nth 3%nat (gra_run_poly [GMul 2%nat 2%nat] slp_init_poly) []) 3%nat)
     < 10)%nat /\
  ~ (forall y, Z.coprime y pin_N ->
       (pin_N | poly_eval (poly_Pe_minus_X
         (nth 3%nat (gra_run_poly [GMul 2%nat 2%nat] slp_init_poly) []) 3%nat) y)).
Proof.
  split; [rewrite residual_square_Q_degree_is_6; lia|].
  intros Hall.
  pose proof (residual_low_degree_ZN_units_divides_N
                (poly_Pe_minus_X
                   (nth 3%nat (gra_run_poly [GMul 2%nat 2%nat] slp_init_poly) [])
                   3%nat)
                ltac:(rewrite residual_square_Q_degree_is_6; lia)
                Hall 1%nat) as Hdiv.
  rewrite residual_square_Q_nth1 in Hdiv.
  destruct Hdiv as [k Hk]. nia.
Qed.

Theorem residual_square_unit_2_not_root :
  Z.coprime 2 pin_N /\
  ~ (pin_N | poly_eval (poly_Pe_minus_X
       (nth 3%nat (gra_run_poly [GMul 2%nat 2%nat] slp_init_poly) []) 3%nat) 2).
Proof.
  split; [vm_compute; reflexivity|].
  rewrite residual_square_denotes_X2, X6_minus_X_eval_2.
  intros [k Hk]. nia.
Qed.

Theorem residual_cube_is_nodiv :
  Forall is_nodiv [GMul 2%nat 2%nat; GMul 3%nat 2%nat].
Proof. repeat constructor. Qed.

Theorem residual_cube_denotes_X3 :
  nth 4%nat (gra_run_poly [GMul 2%nat 2%nat; GMul 3%nat 2%nat] slp_init_poly) [] =
    poly_pow poly_X 3%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_cube_degree_eq_bound :
  poly_degree (nth 4%nat
    (gra_run_poly [GMul 2%nat 2%nat; GMul 3%nat 2%nat] slp_init_poly) [])
    = 3%nat /\
  nth 4%nat (gra_deg_bound [GMul 2%nat 2%nat; GMul 3%nat 2%nat] slp_init_deg)
    0%nat = 3%nat.
Proof.
  split.
  - rewrite residual_cube_denotes_X3. apply poly_degree_X3_is_3.
  - apply gra_deg_bound_x3.
Qed.

Theorem residual_cube_eval :
  forall y,
    gra_eval pin_N [GMul 2%nat 2%nat; GMul 3%nat 2%nat] y 4%nat = y * y * y.
Proof.
  intros y.
  rewrite gra_nodiv_denotes by apply residual_cube_is_nodiv.
  rewrite residual_cube_denotes_X3, poly_eval_pow, poly_eval_X.
  change (Z.of_nat 3%nat) with (Z.succ (Z.succ 1)).
  rewrite !Z.pow_succ_r, Z.pow_1_r by lia. ring.
Qed.

Theorem residual_cube_Q_degree_is_9 :
  poly_degree (poly_Pe_minus_X
    (nth 4%nat (gra_run_poly [GMul 2%nat 2%nat; GMul 3%nat 2%nat] slp_init_poly) [])
    3%nat) = 9%nat.
Proof.
  rewrite residual_cube_denotes_X3. apply poly_degree_X9_minus_X.
Qed.

Theorem residual_cube_Q_nth1 :
  nth 1%nat (poly_Pe_minus_X
    (nth 4%nat (gra_run_poly [GMul 2%nat 2%nat; GMul 3%nat 2%nat] slp_init_poly) [])
    3%nat) 0 = -1.
Proof.
  rewrite residual_cube_denotes_X3. apply X9_minus_X_nth1.
Qed.

Theorem residual_cube_cannot_vanish_on_ZN_units :
  (poly_degree (poly_Pe_minus_X
     (nth 4%nat (gra_run_poly [GMul 2%nat 2%nat; GMul 3%nat 2%nat] slp_init_poly) [])
     3%nat) < 10)%nat /\
  ~ (forall y, Z.coprime y pin_N ->
       (pin_N | poly_eval (poly_Pe_minus_X
         (nth 4%nat
            (gra_run_poly [GMul 2%nat 2%nat; GMul 3%nat 2%nat] slp_init_poly) [])
         3%nat) y)).
Proof.
  split; [rewrite residual_cube_Q_degree_is_9; lia|].
  intros Hall.
  pose proof (residual_low_degree_ZN_units_divides_N
                (poly_Pe_minus_X
                   (nth 4%nat
                      (gra_run_poly [GMul 2%nat 2%nat; GMul 3%nat 2%nat]
                         slp_init_poly) [])
                   3%nat)
                ltac:(rewrite residual_cube_Q_degree_is_9; lia)
                Hall 1%nat) as Hdiv.
  rewrite residual_cube_Q_nth1 in Hdiv.
  destruct Hdiv as [k Hk]. nia.
Qed.

Theorem residual_cube_unit_2_not_root :
  Z.coprime 2 pin_N /\
  ~ (pin_N | poly_eval (poly_Pe_minus_X
       (nth 4%nat
          (gra_run_poly [GMul 2%nat 2%nat; GMul 3%nat 2%nat] slp_init_poly) [])
       3%nat) 2).
Proof.
  split; [vm_compute; reflexivity|].
  rewrite residual_cube_denotes_X3, X9_minus_X_eval_2.
  intros [k Hk]. nia.
Qed.

Theorem residual_trapdoor_inverts_pin :
  powm 36 27 pin_N = 42 /\ powm 42 3 pin_N = 36.
Proof. vm_compute. split; reflexivity. Qed.

Theorem residual_trapdoor_not_a_low_degree_identity :
  powm 36 27 pin_N = 42 /\
  (3 * 27 >= 10)%nat.
Proof.
  split.
  - exact (proj1 residual_trapdoor_inverts_pin).
  - apply residual_trapdoor_deg27_outside_window.
Qed.
