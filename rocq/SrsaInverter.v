From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import SrsaRootPoly.
Require Import SrsaModCbrt.

Open Scope Z_scope.

(** * Restricted RSA inverter and Strong-RSA solver shapes

    A public-[e] inverter on reduced units is the trapdoor map
    ([unique] unit [e]-th root).  Miller-from-[d] still splits.
    A Strong-RSA solver on units is inhabited by [λ+1] and does
    *not* split [N].  An [e]-th root of a non-unit carries the
    same proper gcd.  Not
    [rsa_inverter_constructs_factor_open_named]: Miller uses [d],
    not the inverter.  Not
    [strong_rsa_solver_constructs_factor_open_named]: the [λ+1]
    solver is a counter-shape (solves Strong RSA, no factor).
    Cross-confirmed by [cas/222]–[cas/227]. *)

(** ** [e]-th root of a non-unit *)

Definition eth_root_rel (r h e N : Z) : Prop :=
  powm r e N = h mod N.

Lemma prime_divides_pow :
  forall p r e,
    Z.prime p ->
    0 < e ->
    (p | r ^ e) ->
    (p | r).
Proof.
  intros p r e Hp He Hdiv.
  rewrite <- (Z2Nat.id e) in Hdiv by lia.
  set (k := Z.to_nat e) in *.
  assert (Hk : (0 < k)%nat).
  { change 0%nat with (Z.to_nat 0). apply Z2Nat.inj_lt; lia. }
  clearbody k. revert Hdiv. revert Hk.
  induction k as [|k IH]; intros Hk Hdiv.
  - lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hdiv by lia.
    destruct k as [|k'].
    + rewrite Nat2Z.inj_0, Z.pow_0_r, Z.mul_1_r in Hdiv. exact Hdiv.
    + pose proof Hp as Hp'. apply prime_alt in Hp'.
      apply prime_mult in Hdiv; [| exact Hp'].
      destruct Hdiv as [Hr | Hpow]; [exact Hr | apply IH; [lia | exact Hpow]].
Qed.

(** ** Non-unit [e]-th root carries the input gcd

    Parallel to [mod_cbrt_nonunit_factors] at any [e > 0].
    Not [rsa_inverter_constructs_factor_open_named]. *)

Theorem eth_root_nonunit_factors :
  forall r h e,
    0 < e ->
    eth_root_rel r h e pin_N ->
    1 < Z.gcd h pin_N < pin_N ->
    Z.gcd r pin_N = Z.gcd h pin_N /\
    Problem_Factor pin_N (Z.gcd r pin_N).
Proof.
  intros r h e He Hr [Hlo Hhi].
  set (g := Z.gcd h pin_N).
  pose proof (Z.gcd_divide_l h pin_N) as Gh.
  pose proof (Z.gcd_divide_r h pin_N) as GN.
  assert (HN : Z.divide pin_N (r ^ e - h)).
  { unfold eth_root_rel, powm in Hr.
    apply mods_eq_iff_divides; [lia | exact Hr]. }
  assert (Hge : Z.divide g (r ^ e)).
  { replace (r ^ e) with ((r ^ e - h) + h) by ring.
    apply Z.divide_add_r.
    - apply Z.divide_trans with pin_N; [exact GN | exact HN].
    - exact Gh. }
  assert (Hprime : Z.prime g).
  { unfold g.
    destruct (pin_proper_gcd_is_p_or_q h (conj Hlo Hhi)) as [Hgp | Hgq];
      [rewrite Hgp; apply pin_p_prime | rewrite Hgq; apply pin_q_prime]. }
  pose proof (prime_divides_pow g r e Hprime He Hge) as Gr.
  set (g' := Z.gcd r pin_N).
  assert (Hg' : Z.divide g g').
  { apply Z.gcd_greatest; [exact Gr | exact GN]. }
  pose proof (Z.gcd_divide_r r pin_N) as G'N.
  assert (Hg'pos : 0 < g').
  { destruct (Z.eq_dec g' 0) as [Hz | Hnz].
    - unfold g' in Hz. apply Z.gcd_eq_0 in Hz. lia.
    - pose proof (Z.gcd_nonneg r pin_N). lia. }
  destruct (pin_divide_N_cases g' Hg'pos G'N)
    as [H1 | [Hp | [Hq | HNeq]]].
  - rewrite H1 in Hg'. apply Z.divide_1_r in Hg'. lia.
  - assert (g = pin_p).
    { destruct (pin_proper_gcd_is_p_or_q h (conj Hlo Hhi)) as [Hgp | Hgq];
        [unfold g; exact Hgp|].
      unfold g in Hg'. rewrite Hgq in Hg'. rewrite Hp in Hg'.
      pose proof (Z.divide_pos_le pin_q pin_p ltac:(lia) Hg').
      pose proof pin_p_lt_q. lia. }
    split.
    + unfold g, g' in H, Hp |- *. rewrite Hp, H. reflexivity.
    + unfold Problem_Factor, g' in Hp |- *. rewrite Hp.
      split; [lia | exists pin_q; reflexivity].
  - assert (g = pin_q).
    { destruct (pin_proper_gcd_is_p_or_q h (conj Hlo Hhi)) as [Hgp | Hgq];
        [| unfold g; exact Hgq].
      unfold g in Hg'. rewrite Hgp in Hg'. rewrite Hq in Hg'.
      destruct pin_q_prime as [_ Hqpr].
      exfalso. apply (Hqpr pin_p); [pose proof pin_p_lt_q; lia | exact Hg']. }
    split.
    + unfold g, g' in H, Hq |- *. rewrite Hq, H. reflexivity.
    + unfold Problem_Factor, g' in Hq |- *. rewrite Hq.
      split; [lia | exists pin_p; rewrite Z.mul_comm; reflexivity].
  - assert (HrN : Z.divide pin_N r).
    { unfold g' in HNeq. rewrite <- HNeq. apply Z.gcd_divide_l. }
    assert (HpowN : Z.divide pin_N (r ^ e)).
    { replace e with (Z.succ (e - 1)) by lia.
      rewrite Z.pow_succ_r by lia.
      apply Z.divide_mul_l. exact HrN. }
    assert (HhN : Z.divide pin_N h).
    { replace h with (r ^ e - (r ^ e - h)) by ring.
      apply Z.divide_sub_r; [exact HpowN | exact HN]. }
    rewrite (gcd_eq_n_of_div h pin_N ltac:(lia) HhN) in Hhi. lia.
Qed.

Theorem pin_eth_root_p_factors :
  eth_root_rel pin_cbrt_p pin_p pin_e pin_N /\
  Z.gcd pin_cbrt_p pin_N = pin_p.
Proof.
  split.
  - unfold eth_root_rel. apply pin_cbrt_p_rel.
  - apply pin_cbrt_p_gcd.
Qed.

(** ** RSA problem [y] is a residue *)

Theorem rsa_problem_y_is_residue :
  forall N e y x,
    1 < N ->
    rsa_problem N e y x ->
    0 <= y < N.
Proof.
  intros N e y x HN Hy.
  unfold rsa_problem, powm in Hy. rewrite <- Hy.
  apply Z.mod_pos_bound. lia.
Qed.

Theorem pin_N_plus_1_not_rsa_problem :
  forall x, ~ rsa_problem pin_N pin_e (pin_N + 1) x.
Proof.
  intros x Hx.
  pose proof (rsa_problem_y_is_residue pin_N pin_e (pin_N + 1) x
                ltac:(lia) Hx). lia.
Qed.

Theorem pin_N_plus_1_not_strong_RSA :
  forall x e, ~ Problem_StrongRSA pin_N (pin_N + 1) x e.
Proof.
  intros x e [_ Hpow].
  unfold powm in Hpow.
  pose proof (Z.mod_pos_bound (x ^ e) pin_N ltac:(lia)). lia.
Qed.

(** ** Reduced-units public-[e] inverter is the trapdoor map

    [rsa_inverter] as written demands [powm x e N = y] exactly, so
    [y] is a residue.  The reduced-units type makes that explicit
    and is inhabited by [y ↦ y^d].  Unique unit [e]-th root ⇒
    trapdoor; Miller-from-[d] splits.  Not
    [rsa_inverter_constructs_factor_open_named]. *)

Definition rsa_inverter_reduced_units (N e : Z) : Type :=
  forall y, 0 <= y < N -> Z.coprime y N ->
    { x : Z | rsa_problem N e y x }.

Definition pin_dec_inverter : rsa_inverter_reduced_units pin_N pin_e.
Proof.
  intros y Hrng Hy.
  exists (powm y pin_d pin_N).
  unfold rsa_problem.
  rewrite (pin_powm_de y Hy). rewrite Z.mod_small; lia.
Defined.

Theorem rsa_inverter_reduced_units_is_trapdoor :
  forall (Inv : rsa_inverter_reduced_units pin_N pin_e) y Hrng Hy,
    proj1_sig (Inv y Hrng Hy) mod pin_N = powm y pin_d pin_N.
Proof.
  intros Inv y Hrng Hy.
  destruct (Inv y Hrng Hy) as [x Hx].
  unfold rsa_problem in Hx.
  replace (powm y pin_d pin_N) with (powm y pin_d pin_N mod pin_N).
  2: { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
  apply (pin_unique_unit_eth_root x (powm y pin_d pin_N)).
  - apply (mod_cbrt_unit_coprime x y Hy).
    unfold mod_cbrt_rel. rewrite Hx. rewrite Z.mod_small; lia.
  - unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
    apply Z.coprime_pow_l; [lia | exact Hy].
  - rewrite Hx, (pin_powm_de y Hy). rewrite Z.mod_small; lia.
Qed.

Theorem rsa_inverter_reduced_units_constructs_factor :
  forall (Inv : rsa_inverter_reduced_units pin_N pin_e),
    (forall y Hrng Hy,
       proj1_sig (Inv y Hrng Hy) mod pin_N = powm y pin_d pin_N) /\
    exists f, Problem_Factor pin_N f.
Proof.
  intros Inv.
  split.
  - intros y Hrng Hy.
    apply rsa_inverter_reduced_units_is_trapdoor.
  - eexists. apply pin_miller_from_d_factors.
Qed.

(** ** [inverter_as_residual] writes [pin_lam]

    [inverter_as_residual] writes [pin_e] and [pin_lam] into a
    residual solver.  That is why the pin inverter theorem is not
    [rsa_inverter_extracts_factor_open_named] (no [λ] in that type).
    Not [rsa_inverter_extracts_factor_open_named]. *)
Definition inverter_as_residual
    (Inv : rsa_inverter_reduced_units pin_N pin_e)
    : residual_solver_reduced pin_N pin_lam.
Proof.
  intros y Hrng Hy.
  refine (exist _ (proj1_sig (Inv y Hrng Hy), pin_e) _).
  apply mod_cbrt_unit_is_residual_leaf; [exact Hrng | exact Hy |].
  unfold mod_cbrt_rel.
  transitivity y.
  - exact (proj2_sig (Inv y Hrng Hy)).
  - rewrite Z.mod_small; lia.
Defined.

Theorem inverter_as_residual_returns_e :
  forall Inv,
    residual_solver_reduced_returns_e (inverter_as_residual Inv) pin_e.
Proof. intros Inv y Hrng Hy. reflexivity. Qed.

(** ** Strong-RSA solver on units: [λ+1] inhabits, does not factor

    Knowing [λ] makes Strong RSA trivial on every unit
    ([lambda_solves_strong_RSA]).  That solver's output is the
    challenge itself, a unit, so [gcd] is 1.  The same witness is
    not a residual leaf ([lambda_plus_one_witness_not_residual]).
    [strong_rsa_solver_extracts_factor_open_named] has no [λ]; this
    inhabitant uses [pin_lam].  Do not prove [~ forall Solve, exists f].
    Not [strong_rsa_solver_constructs_factor_open_named].
    Not [strong_rsa_solver_extracts_factor_open_named]. *)

Definition strong_rsa_solver_units (N : Z) : Type :=
  forall y, 0 <= y < N -> Z.coprime y N ->
    { xe : Z * Z | let '(x, e) := xe in Problem_StrongRSA N y x e }.

Definition pin_lambda_strong_solver : strong_rsa_solver_units pin_N.
Proof.
  intros y Hrng Hy.
  refine (exist _ (y, pin_lam + 1) _).
  rewrite <- (Z.mod_small y pin_N) by lia.
  rewrite <- rsa_test_lambda.
  apply (lambda_solves_strong_RSA pin_p pin_q y
           pin_p_prime pin_q_prime pin_p_neq_q Hy).
Defined.

Theorem pin_lambda_strong_solver_output_is_unit :
  forall y Hrng Hy,
    fst (proj1_sig (pin_lambda_strong_solver y Hrng Hy)) = y /\
    Z.coprime y pin_N.
Proof.
  intros y Hrng Hy. cbn. split; [reflexivity | exact Hy].
Qed.

Theorem pin_lambda_plus_one_does_not_split :
  Z.gcd (pin_lam + 1) pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_lambda_strong_solver_not_residual :
  forall y Hrng Hy,
    ~ srsa_residual_leaf pin_N pin_lam y
        (fst (proj1_sig (pin_lambda_strong_solver y Hrng Hy)))
        (snd (proj1_sig (pin_lambda_strong_solver y Hrng Hy))).
Proof.
  intros y Hrng Hy. cbn.
  intros [_ [_ [_ [_ Hnd]]]]. apply Hnd. exists 1. lia.
Qed.

Definition strong_rsa_solver_units_returns_e
    (Solve : strong_rsa_solver_units pin_N) (e : Z) : Prop :=
  forall y Hrng Hy, snd (proj1_sig (Solve y Hrng Hy)) = e.

Definition strong_solver_as_inverter
    (Solve : strong_rsa_solver_units pin_N)
    (Hfix : strong_rsa_solver_units_returns_e Solve pin_e)
    : rsa_inverter_reduced_units pin_N pin_e.
Proof.
  intros y Hrng Hy.
  refine (exist _ (fst (proj1_sig (Solve y Hrng Hy))) _).
  unfold rsa_problem.
  pose proof (Hfix y Hrng Hy) as He.
  destruct (proj1_sig (Solve y Hrng Hy)) as [x e] eqn:Hxe.
  cbn [fst snd] in He |- *. subst e.
  generalize (proj2_sig (Solve y Hrng Hy)).
  rewrite Hxe. cbn.
  intros [_ Hpow]. exact Hpow.
Defined.

Theorem strong_rsa_solver_pin_e_constructs_factor :
  forall (Solve : strong_rsa_solver_units pin_N),
    strong_rsa_solver_units_returns_e Solve pin_e ->
    exists f, Problem_Factor pin_N f.
Proof.
  intros Solve Hfix.
  destruct (rsa_inverter_reduced_units_constructs_factor
              (strong_solver_as_inverter Solve Hfix)) as [_ Hex].
  exact Hex.
Qed.
