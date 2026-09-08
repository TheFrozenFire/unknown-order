From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import GenericRing.
Require Import SrsaRootPoly.

Open Scope Z_scope.

(** * Modular cube-root versus integer [GRoot], and a reduced residual solver

    Integer [GRoot] searches for a [Z]-cube and misses residues that
    are cubes only modulo [N].  A modular cube-root of a non-unit
    has the same gcd as the handle, a proper factor.  A modular
    cube-root of a unit is a residual leaf at public [e=3].  A
    residual solver on reduced residues that always returns that
    [e] is the trapdoor map.  Miller-from-[d] still splits.
    Not [residual_solver_constructs_factor_open_named]: a residual
    solver may choose [e] per [y], and Miller uses [d], not the
    solver.  Cross-confirmed by [cas/215]–[cas/221]. *)

(** ** Modular cube-root as a relation *)

Definition mod_cbrt_rel (r h N : Z) : Prop :=
  powm r 3 N = h mod N.

Lemma Z_pow_3_mul :
  forall r, r ^ 3 = r * r * r.
Proof.
  intros r.
  change 3 with (Z.succ (Z.succ 1)).
  rewrite !Z.pow_succ_r, Z.pow_1_r by lia. ring.
Qed.

Lemma prime_divides_cube :
  forall p r,
    Z.prime p ->
    (p | r ^ 3) ->
    (p | r).
Proof.
  intros p r Hp Hdiv.
  rewrite Z_pow_3_mul in Hdiv.
  apply prime_alt in Hp.
  apply prime_mult in Hdiv; [| exact Hp].
  destruct Hdiv as [Hdiv | Hdiv]; [| exact Hdiv].
  apply prime_mult in Hdiv; [| exact Hp].
  destruct Hdiv; assumption.
Qed.

Lemma gcd_prime_is_1_or_p :
  forall a p,
    Z.prime p ->
    Z.gcd a p = 1 \/ Z.gcd a p = p.
Proof.
  intros a p Hp.
  destruct Hp as [Hlt Hpr].
  pose proof (Z.gcd_divide_r a p) as Hdiv.
  pose proof (Z.gcd_nonneg a p) as Hnn.
  destruct (Z.eq_dec (Z.gcd a p) 0) as [Hz | Hnz].
  - apply Z.gcd_eq_0 in Hz. lia.
  - assert (0 < Z.gcd a p) by lia.
    pose proof (Z.divide_pos_le (Z.gcd a p) p ltac:(lia) Hdiv).
    destruct (Z.eq_dec (Z.gcd a p) 1) as [H1 | Hn1]; [left; exact H1|].
    destruct (Z.eq_dec (Z.gcd a p) p) as [Hp' | Hnp]; [right; exact Hp'|].
    exfalso. apply (Hpr (Z.gcd a p)); [lia | exact Hdiv].
Qed.

Lemma divide_eq_pos :
  forall a b,
    0 <= a ->
    0 <= b ->
    (a | b) ->
    (b | a) ->
    a = b.
Proof.
  intros a b Ha Hb Hab Hba.
  destruct (Z.divide_antisym _ _ Hab Hba); lia.
Qed.

Lemma gcd_eq_n_of_div :
  forall h n,
    0 < n ->
    (n | h) ->
    Z.gcd h n = n.
Proof.
  intros h n Hn Hdiv.
  apply divide_eq_pos; [apply Z.gcd_nonneg | lia | apply Z.gcd_divide_r |].
  apply Z.gcd_greatest; [exact Hdiv | apply Z.divide_refl].
Qed.

Lemma pin_divide_N_cases :
  forall d,
    0 < d ->
    (d | pin_N) ->
    d = 1 \/ d = pin_p \/ d = pin_q \/ d = pin_N.
Proof.
  intros d Hd Hdiv.
  pose proof pin_p_prime as Hp. pose proof pin_q_prime as Hq.
  pose proof (Z.prime_ge_2 pin_p Hp). pose proof (Z.prime_ge_2 pin_q Hq).
  destruct (gcd_prime_is_1_or_p d pin_p Hp) as [H1 | Hpp].
  - assert (d | pin_q) as Hdq.
    { apply Gauss with pin_p.
      - change pin_N with (pin_p * pin_q) in Hdiv. exact Hdiv.
      - apply rel_prime_iff_coprime. exact H1. }
    destruct (gcd_prime_is_1_or_p d pin_q Hq) as [H1q | Hqq].
    + left.
      pose proof (gcd_eq_n_of_div pin_q d Hd Hdq) as Hgcd.
      rewrite Z.gcd_comm in H1q. congruence.
    + assert (Hqd : Z.divide pin_q d).
      { rewrite <- Hqq. apply Z.gcd_divide_l. }
      assert (Heq : d = pin_q).
      { apply divide_eq_pos; [lia | lia | exact Hdq | exact Hqd]. }
      right. right. left. exact Heq.
  - assert (pin_p | d) as Hpd.
    { rewrite <- Hpp. apply Z.gcd_divide_l. }
    destruct Hpd as [t Ht].
    assert (Htpos : 0 < t) by nia.
    assert (t | pin_q) as Htq.
    { change pin_N with (pin_p * pin_q) in Hdiv. rewrite Ht in Hdiv.
      destruct Hdiv as [m Hm]. exists m. nia. }
    destruct (gcd_prime_is_1_or_p t pin_q Hq) as [H1t | Hqt].
    + assert (t = 1).
      { pose proof (gcd_eq_n_of_div pin_q t Htpos Htq) as Hgcdt.
        rewrite Z.gcd_comm in H1t. congruence. }
      subst t. right. left. nia.
    + assert (Hqt' : Z.divide pin_q t).
      { rewrite <- Hqt. apply Z.gcd_divide_l. }
      assert (t = pin_q).
      { apply divide_eq_pos; [lia | lia | exact Htq | exact Hqt']. }
      subst t. unfold pin_N. right. right. right. nia.
Qed.

Lemma pin_proper_gcd_is_p_or_q :
  forall h,
    1 < Z.gcd h pin_N < pin_N ->
    Z.gcd h pin_N = pin_p \/ Z.gcd h pin_N = pin_q.
Proof.
  intros h [Hlo Hhi].
  pose proof (Z.gcd_divide_r h pin_N) as Hdiv.
  destruct (pin_divide_N_cases (Z.gcd h pin_N) ltac:(lia) Hdiv)
    as [H1 | [Hp | [Hq | HN]]].
  - lia.
  - left. exact Hp.
  - right. exact Hq.
  - lia.
Qed.

(** ** Modular cube-root of a non-unit

    [gcd(h,N)] is already a factor of the *input*; the content is
    that the *output* carries it.  Parallel to
    [gra_inv_proper_gcd_factors].  Not
    [residual_solver_constructs_factor_open_named]. *)

Theorem mod_cbrt_nonunit_factors :
  forall r h,
    mod_cbrt_rel r h pin_N ->
    1 < Z.gcd h pin_N < pin_N ->
    Z.gcd r pin_N = Z.gcd h pin_N /\
    Problem_Factor pin_N (Z.gcd r pin_N).
Proof.
  intros r h Hr [Hlo Hhi].
  set (g := Z.gcd h pin_N).
  assert (Hgpos : 0 < g) by lia.
  pose proof (Z.gcd_divide_l h pin_N) as Gh.
  pose proof (Z.gcd_divide_r h pin_N) as GN.
  assert (HN : Z.divide pin_N (r ^ 3 - h)).
  { unfold mod_cbrt_rel, powm in Hr.
    apply mods_eq_iff_divides; [lia | exact Hr]. }
  assert (Hg3 : Z.divide g (r ^ 3)).
  { replace (r ^ 3) with ((r ^ 3 - h) + h) by ring.
    apply Z.divide_add_r.
    - apply Z.divide_trans with pin_N; [exact GN | exact HN].
    - exact Gh. }
  assert (Hprime : Z.prime g).
  { unfold g.
    destruct (pin_proper_gcd_is_p_or_q h (conj Hlo Hhi)) as [Hgp | Hgq];
      [rewrite Hgp; apply pin_p_prime | rewrite Hgq; apply pin_q_prime]. }
  pose proof (prime_divides_cube g r Hprime Hg3) as Gr.
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
    + unfold Problem_Factor, g' in Hp |- *. rewrite Hp. split; [lia | exists pin_q; reflexivity].
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
    assert (H3 : Z.divide pin_N (r ^ 3)).
    { rewrite Z_pow_3_mul. apply Z.divide_mul_r. exact HrN. }
    assert (HhN : Z.divide pin_N h).
    { replace h with (r ^ 3 - (r ^ 3 - h)) by ring.
      apply Z.divide_sub_r; [exact H3 | exact HN]. }
    rewrite (gcd_eq_n_of_div h pin_N ltac:(lia) HhN) in Hhi. lia.
Qed.

(** ** Pin inhabitants: integer miss versus modular hit *)

Definition pin_cbrt_p : Z := 165.

Theorem pin_cbrt_p_rel :
  mod_cbrt_rel pin_cbrt_p pin_p pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_cbrt_p_gcd :
  Z.gcd pin_cbrt_p pin_N = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_cbrt_p_factors :
  Problem_Factor pin_N (Z.gcd pin_cbrt_p pin_N).
Proof.
  rewrite pin_cbrt_p_gcd. unfold Problem_Factor.
  split; [lia | exists pin_q; reflexivity].
Qed.

Theorem pin_cbrt_p_neq_p :
  pin_cbrt_p <> pin_p.
Proof. discriminate. Qed.

Theorem integer_cube_root_p_miss :
  integer_cube_root pin_p = pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem integer_cbrt_p_neq_mod_cbrt_p :
  integer_cube_root pin_p <> pin_cbrt_p.
Proof. vm_compute. discriminate. Qed.

Theorem pin_cbrt_2p_rel :
  mod_cbrt_rel pin_p (2 * pin_p) pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_cbrt_2p_factors :
  Z.gcd (2 * pin_p) pin_N = pin_p /\
  Z.gcd pin_p pin_N = pin_p.
Proof. vm_compute. split; reflexivity. Qed.

Theorem pin_cbrt_0_rel :
  mod_cbrt_rel 0 0 pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_cbrt_0_gcd_is_N :
  Z.gcd 0 pin_N = pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_cbrt_y_is_x :
  mod_cbrt_rel pin_x pin_y pin_N.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_cbrt_y_unit :
  Z.gcd pin_x pin_N = 1.
Proof. vm_compute. reflexivity. Qed.

(** ** Unit modular cube-root is a residual leaf at public [e] *)

Lemma mod_cbrt_unit_coprime :
  forall r y,
    Z.coprime y pin_N ->
    mod_cbrt_rel r y pin_N ->
    Z.coprime r pin_N.
Proof.
  intros r y Hy Hr.
  unfold Z.coprime.
  apply (powm_unit_is_coprime r 3 pin_N); [apply pin_N_gt_1 | lia |].
  unfold mod_cbrt_rel in Hr. rewrite Hr. rewrite Z.gcd_mod_l. exact Hy.
Qed.

Theorem residual_leaf_y_is_residue :
  forall N lam y x e,
    1 < N ->
    srsa_residual_leaf N lam y x e ->
    0 <= y < N.
Proof.
  intros N lam y x e HN Hleaf.
  destruct Hleaf as [_ [[_ Hpow] _]].
  unfold powm in Hpow. rewrite <- Hpow.
  apply Z.mod_pos_bound. lia.
Qed.

Theorem pin_N_plus_1_not_a_leaf :
  forall x e, ~ srsa_residual_leaf pin_N pin_lam (pin_N + 1) x e.
Proof.
  intros x e Hleaf.
  pose proof (residual_leaf_y_is_residue pin_N pin_lam (pin_N + 1) x e
                ltac:(lia) Hleaf) as Hrng. lia.
Qed.

Theorem mod_cbrt_unit_is_residual_leaf :
  forall r y,
    0 <= y < pin_N ->
    Z.coprime y pin_N ->
    mod_cbrt_rel r y pin_N ->
    srsa_residual_leaf pin_N pin_lam y r pin_e.
Proof.
  intros r y Hrng Hy Hr.
  unfold srsa_residual_leaf, Problem_StrongRSA, mod_cbrt_rel in *.
  split; [exact Hy|].
  split.
  - split; [lia|].
    rewrite Hr. rewrite Z.mod_small; lia.
  - split; [exists 1; lia|].
    split; [vm_compute; reflexivity|].
    intros [k Hk]. nia.
Qed.

Theorem pin_x_is_residual_leaf_of_y :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof.
  apply mod_cbrt_unit_is_residual_leaf.
  - lia.
  - vm_compute. reflexivity.
  - apply pin_cbrt_y_is_x.
Qed.

Theorem trapdoor_inhabits_residual_leaf :
  forall y,
    0 <= y < pin_N ->
    Z.coprime y pin_N ->
    srsa_residual_leaf pin_N pin_lam y (powm y pin_d pin_N) pin_e.
Proof.
  intros y Hrng Hy.
  apply mod_cbrt_unit_is_residual_leaf; [exact Hrng | exact Hy |].
  unfold mod_cbrt_rel.
  rewrite (pin_powm_de y Hy). rewrite Z.mod_small; lia.
Qed.

(** ** Reduced residual solver at public [e] is the trapdoor map

    [residual_solver] as written demands [powm x e N = y] exactly, so
    [y] is already a residue ([residual_leaf_y_is_residue]).  The
    reduced type makes that side condition explicit and is inhabited
    by the trapdoor.  Not
    [residual_solver_constructs_factor_open_named]: a residual
    solver may choose [e] per [y], and Miller uses [d]. *)

Definition residual_solver_reduced (N lam : Z) : Type :=
  forall y, 0 <= y < N -> Z.coprime y N ->
    { xe : Z * Z | let '(x, e) := xe in srsa_residual_leaf N lam y x e }.

Definition residual_solver_reduced_returns_e
    (Solve : residual_solver_reduced pin_N pin_lam) (e : Z) : Prop :=
  forall y Hrng Hy, snd (proj1_sig (Solve y Hrng Hy)) = e.

Definition pin_trapdoor_residual_solver : residual_solver_reduced pin_N pin_lam.
Proof.
  intros y Hrng Hy.
  refine (exist _ (powm y pin_d pin_N, pin_e) _).
  apply trapdoor_inhabits_residual_leaf; assumption.
Defined.

Theorem pin_trapdoor_solver_returns_e :
  residual_solver_reduced_returns_e pin_trapdoor_residual_solver pin_e.
Proof. intros y Hrng Hy. reflexivity. Qed.

Theorem residual_solver_reduced_pin_e_is_mod_cbrt :
  forall (Solve : residual_solver_reduced pin_N pin_lam) y Hrng Hy,
    residual_solver_reduced_returns_e Solve pin_e ->
    mod_cbrt_rel (fst (proj1_sig (Solve y Hrng Hy))) y pin_N.
Proof.
  intros Solve y Hrng Hy Hfix.
  destruct (proj1_sig (Solve y Hrng Hy)) as [x e] eqn:Hxe.
  pose proof (proj2_sig (Solve y Hrng Hy)) as Hleaf.
  rewrite Hxe in Hleaf.
  unfold residual_solver_reduced_returns_e in Hfix.
  specialize (Hfix y Hrng Hy). rewrite Hxe in Hfix. cbn [snd] in Hfix. subst e.
  destruct Hleaf as [_ [[_ Hpow] _]].
  unfold mod_cbrt_rel. cbn [fst].
  rewrite Hpow. rewrite Z.mod_small; lia.
Qed.

Theorem residual_solver_reduced_pin_e_is_trapdoor :
  forall (Solve : residual_solver_reduced pin_N pin_lam) y Hrng Hy,
    residual_solver_reduced_returns_e Solve pin_e ->
    fst (proj1_sig (Solve y Hrng Hy)) mod pin_N = powm y pin_d pin_N.
Proof.
  intros Solve y Hrng Hy Hfix.
  pose proof (residual_solver_reduced_pin_e_is_mod_cbrt Solve y Hrng Hy Hfix) as Hcbrt.
  destruct (proj1_sig (Solve y Hrng Hy)) as [x e] eqn:Hxe.
  cbn [fst] in Hcbrt |- *.
  unfold residual_solver_reduced_returns_e in Hfix.
  specialize (Hfix y Hrng Hy). rewrite Hxe in Hfix. cbn [snd] in Hfix. subst e.
  unfold mod_cbrt_rel in Hcbrt.
  replace (powm y pin_d pin_N) with (powm y pin_d pin_N mod pin_N).
  2: { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
  apply (pin_unique_unit_eth_root x (powm y pin_d pin_N)).
  - apply (mod_cbrt_unit_coprime x y Hy).
    unfold mod_cbrt_rel. exact Hcbrt.
  - unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
    apply Z.coprime_pow_l; [lia | exact Hy].
  - rewrite Hcbrt, (pin_powm_de y Hy). reflexivity.
Qed.

Theorem residual_solver_reduced_pin_e_constructs_factor :
  forall (Solve : residual_solver_reduced pin_N pin_lam),
    residual_solver_reduced_returns_e Solve pin_e ->
    (forall y Hrng Hy,
       fst (proj1_sig (Solve y Hrng Hy)) mod pin_N = powm y pin_d pin_N) /\
    exists f, Problem_Factor pin_N f.
Proof.
  intros Solve Hfix.
  split.
  - intros y Hrng Hy.
    apply residual_solver_reduced_pin_e_is_trapdoor; assumption.
  - eexists. apply pin_miller_from_d_factors.
Qed.
