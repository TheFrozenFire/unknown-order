From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import Order.
Require Import TwoPrimary.
Require Import Miller.
Require Import MillerHeight.
Require Import SrsaResidualGRA.
Require Import SrsaRootPoly.
Require Import SrsaModCbrt.
Require Import SrsaInverter.
Require Import RocqProofs.ZPoly.

Open Scope Z_scope.

(** * Varying-[e] residual and the Strong-RSA output negative

    A [λ+1] Strong-RSA solver on units never returns a proper gcd
    (the outputs are the challenge and [λ+1]).  That is not a
    refutation of [exists f]: Miller-from-[d] still splits.
    Residual [e + kλ] keeps the same [x] and the residual shape.
    Same [x] at two exponents annihilates [x^{e'−e}]; a [λ]-multiple
    annihilator is two-sided ([gcd = N]).  A known multiple of [λ]
    Millers (base [2] on this pin).  A residual solver whose [e]
    stays in the public class [e ≡ pin_e (mod λ)] writes the
    trapdoor map on [x]; a non-minimal such [e] Millers from
    [e − pin_e] recovered from the solver.  [e = 7] is outside
    that class and writes a different [x].
    Not [residual_solver_constructs_factor_open_named].
    Not [strong_rsa_solver_constructs_factor_open_named].
    Not [rsa_inverter_constructs_factor_open_named].
    A residual solver that always returns one residual-shaped [e],
    given a known inverse of that [e] modulo [λ], is the trapdoor
    map [y ↦ y^{e^{-1}}]; Miller-from-[e d' − 1] splits.  Miller
    uses the inverse, not the solver.  Unique unit [e]-th roots
    from [gcd(e,λ)=1] (kernel of the [e]-power map, no handed
    inverse).  Bézout produces [d'] from [(e,λ)]; a fixed-[e]
    residual solver then Millers without a [d'] hypothesis.
    An invert-all-units polynomial at a residual [e] is
    [y ↦ y^{d'}].  Cross-confirmed by [cas/228]–[cas/239]. *)

(** ** Strong-RSA [λ+1] outputs never a proper gcd

    The solver inhabits; its pair [(y, λ+1)] has [gcd = 1] on both
    coordinates.  Miller-from-[d] still splits, independently.
    Not [strong_rsa_solver_constructs_factor_open_named]. *)

Theorem pin_lambda_strong_solver_outputs_never_proper_gcd :
  forall y Hrng Hy,
    let xe := proj1_sig (pin_lambda_strong_solver y Hrng Hy) in
    Z.gcd (fst xe) pin_N = 1 /\ Z.gcd (snd xe) pin_N = 1.
Proof.
  intros y Hrng Hy.
  cbn.
  split; [exact Hy | apply pin_lambda_plus_one_does_not_split].
Qed.

(** ** Residual [e + kλ] keeps the same [x]

    Not [residual_solver_constructs_factor_open_named]. *)

Lemma pin_lam_even : Z.Even pin_lam.
Proof. exists 40. reflexivity. Qed.

Theorem residual_shaped_e_plus_k_lam :
  forall e k,
    0 <= k ->
    residual_shaped_e e pin_lam ->
    residual_shaped_e (e + k * pin_lam) pin_lam.
Proof.
  intros e k Hk [He [Hodd [Hgcd Hnd]]].
  unfold residual_shaped_e.
  split; [nia|].
  split.
  - apply Z.odd_spec.
    rewrite Z.odd_add, Z.odd_mul.
    change (Z.odd pin_lam) with false.
    rewrite andb_false_r, xorb_false_r.
    apply Z.odd_spec. exact Hodd.
  - split.
    + rewrite Z.gcd_comm, (Z.gcd_add_mult_diag_r pin_lam e k), Z.gcd_comm.
      exact Hgcd.
    + intros Hdiv.
      apply Hnd.
      replace (e - 1) with ((e + k * pin_lam - 1) - k * pin_lam) by ring.
      apply Z.divide_sub_r; [exact Hdiv | exists k; ring].
Qed.

Theorem unit_powm_plus_k_lam :
  forall x e k,
    0 <= e ->
    0 <= k ->
    Z.coprime x pin_N ->
    powm x (e + k * pin_lam) pin_N = powm x e pin_N.
Proof.
  intros x e k He Hk Hx.
  rewrite powm_add_r by lia.
  rewrite (Z.mul_comm k pin_lam).
  rewrite powm_mul_r by lia.
  rewrite rsa_test_annihilator by exact Hx.
  rewrite powm_1_pow by lia.
  rewrite Z.mod_1_l by lia.
  rewrite Z.mul_1_r.
  unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem residual_leaf_plus_k_lam :
  forall y x e k,
    0 <= k ->
    srsa_residual_leaf pin_N pin_lam y x e ->
    srsa_residual_leaf pin_N pin_lam y x (e + k * pin_lam).
Proof.
  intros y x e k Hk Hleaf.
  destruct Hleaf as [Hy [[He Hpow] [Hodd [Hgcd Hnd]]]].
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [exact Hy|].
  split.
  - split; [nia|].
    pose proof (srsa_unit_y_forces_unit_x pin_N y x e
                  ltac:(lia) ltac:(lia) Hy Hpow) as Hx.
    rewrite (unit_powm_plus_k_lam x e k ltac:(lia) Hk Hx).
    exact Hpow.
  - pose proof (residual_shaped_e_plus_k_lam e k Hk
                  (conj He (conj Hodd (conj Hgcd Hnd)))) as Hs.
    destruct Hs as [_ [Hodd' [Hgcd' Hnd']]].
    split; [exact Hodd' | split; [exact Hgcd' | exact Hnd']].
Qed.

Theorem pin_e_plus_lam_residual :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x (pin_e + pin_lam).
Proof.
  apply (residual_leaf_plus_k_lam pin_y pin_x pin_e 1); [lia |].
  apply srsa_residual_pin.
Qed.

(** ** Same [x] at two exponents annihilates; two-sided gcd is [N]

    [e' − e = kλ] is two-sided: [gcd(x^{kλ}−1, N) = N], not a
    proper factor.  [e' − e = 4] (public [3] vs [7]) does not
    Miller.  Leftover [k = 5] does split ([leftover_x_mismatch_factors_pin]).
    Not [residual_solver_constructs_factor_open_named]. *)

Lemma mul_cancel_mod_unit :
  forall y a n,
    1 < n ->
    Z.coprime y n ->
    (y * a) mod n = y mod n ->
    a mod n = 1.
Proof.
  intros y a n Hn Hcop Heq.
  transitivity (1 mod n).
  2: apply Z.mod_1_l; lia.
  apply mods_eq_iff_divides; [lia|].
  apply (Z.gauss n y (a - 1)).
  - replace (y * (a - 1)) with (y * a - y) by ring.
    apply mods_eq_iff_divides; [lia | exact Heq].
  - rewrite Z.gcd_comm. exact Hcop.
Qed.

Theorem same_unit_x_two_exponents_annihilates :
  forall x e e' y,
    0 <= e ->
    0 <= e' ->
    e <= e' ->
    Z.coprime y pin_N ->
    powm x e pin_N = y ->
    powm x e' pin_N = y ->
    powm x (e' - e) pin_N = 1.
Proof.
  intros x e e' y He He' Hle Hcop Hy Hy'.
  assert (Hy_mod : y = y mod pin_N).
  { rewrite <- Hy. unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
  replace e' with (e + (e' - e)) in Hy' by lia.
  rewrite powm_add_r in Hy' by lia.
  rewrite Hy in Hy'.
  rewrite Hy_mod in Hy' at 2.
  pose proof (mul_cancel_mod_unit y (powm x (e' - e) pin_N) pin_N
                ltac:(lia) Hcop Hy') as Hone.
  unfold powm in Hone |- *. rewrite Z.mod_mod in Hone by lia. exact Hone.
Qed.

Theorem powm_one_gcd_is_N :
  forall a M n,
    1 < n ->
    powm a M n = 1 ->
    Z.gcd (a ^ M - 1) n = n.
Proof.
  intros a M n Hn Hpow.
  apply gcd_eq_n_of_div; [lia|].
  apply mods_eq_iff_divides; [lia|].
  unfold powm in Hpow.
  rewrite Hpow, Z.mod_1_l by lia. reflexivity.
Qed.

Theorem pin_x_lam_powm_one :
  powm pin_x pin_lam pin_N = 1.
Proof. apply rsa_test_annihilator. vm_compute. reflexivity. Qed.

Theorem pin_x_lam_gcd_is_N :
  Z.gcd (pin_x ^ pin_lam - 1) pin_N = pin_N /\
  ~ Problem_Factor pin_N (Z.gcd (pin_x ^ pin_lam - 1) pin_N).
Proof.
  assert (Hg : Z.gcd (pin_x ^ pin_lam - 1) pin_N = pin_N).
  { apply powm_one_gcd_is_N; [lia | apply pin_x_lam_powm_one]. }
  split; [exact Hg|].
  intros [Hlt _]. rewrite Hg in Hlt. lia.
Qed.

Theorem pin_e7_minus_pin_e_does_not_miller :
  Z.gcd (pin_x ^ 4 - 1) pin_N = 1 /\
  Z.gcd (60 ^ 4 - 1) pin_N = 1.
Proof. vm_compute. split; reflexivity. Qed.

(** ** Miller from a known multiple of [λ]

    Base-[2] heights on this pin stay [v₂(ord_p(2))] vs
    [v₂(ord_q(2))] at [odd_part(M)] for any positive multiple [M]
    of [λ].  On this pin [ed − 1 = λ], so Miller-from-[d] is
    Miller-from-[λ].  Writing [M] wrote a multiple of [λ].
    Not [residual_solver_constructs_factor_open_named]. *)

Lemma pin_base2_height_p_at_odd_part_of_lam_multiple :
  forall M,
    0 < M ->
    Z.divide pin_lam M ->
    two_height 2 (odd_part M) pin_p (val2 pin_ord2_p).
Proof.
  intros M HM Hdiv.
  assert (Hdivt : Z.divide (odd_part pin_ord2_p) (odd_part M)).
  { replace (odd_part pin_ord2_p) with (odd_part pin_lam)
      by (vm_compute; reflexivity).
    apply odd_part_of_divisor; [lia | lia | exact Hdiv]. }
  apply (proj2 (two_height_is_val2_ord pin_p 2 pin_ord2_p (odd_part M)
                  (val2 pin_ord2_p) pin_p_prime order_2_mod_11
                  ltac:(apply odd_part_pos; exact HM)
                  ltac:(apply odd_part_odd; exact HM)
                  Hdivt)).
  reflexivity.
Qed.

Lemma pin_base2_height_q_at_odd_part_of_lam_multiple :
  forall M,
    0 < M ->
    Z.divide pin_lam M ->
    two_height 2 (odd_part M) pin_q (val2 pin_ord2_q).
Proof.
  intros M HM Hdiv.
  assert (Hdivt : Z.divide (odd_part pin_ord2_q) (odd_part M)).
  { replace (odd_part pin_ord2_q) with 1 by (vm_compute; reflexivity).
    apply Z.divide_1_l. }
  apply (proj2 (two_height_is_val2_ord pin_q 2 pin_ord2_q (odd_part M)
                  (val2 pin_ord2_q) pin_q_prime order_2_mod_17
                  ltac:(apply odd_part_pos; exact HM)
                  ltac:(apply odd_part_odd; exact HM)
                  Hdivt)).
  reflexivity.
Qed.

Theorem pin_miller_from_lambda_multiple :
  forall M,
    0 < M ->
    Z.divide pin_lam M ->
    Z.gcd (2 ^ (odd_part M * pow2n (val2 pin_ord2_p)) - 1) pin_N = pin_p /\
    Problem_Factor pin_N
      (Z.gcd (2 ^ (odd_part M * pow2n (val2 pin_ord2_p)) - 1) pin_N).
Proof.
  intros M HM Hdiv.
  assert (Hg :
    Z.gcd (2 ^ (odd_part M * pow2n (val2 pin_ord2_p)) - 1)
          (rsa_N rsa_test) = rsa_p rsa_test).
  { apply (miller_from_multiple rsa_test M 2
             (val2 pin_ord2_p) (val2 pin_ord2_q)).
    - exact HM.
    - unfold rsa_lambda.
      change (rsa_p rsa_test) with pin_p.
      change (rsa_q rsa_test) with pin_q.
      rewrite rsa_test_lambda. exact Hdiv.
    - vm_compute. reflexivity.
    - change (rsa_p rsa_test) with pin_p.
      apply pin_base2_height_p_at_odd_part_of_lam_multiple; assumption.
    - change (rsa_q rsa_test) with pin_q.
      apply pin_base2_height_q_at_odd_part_of_lam_multiple; assumption.
    - vm_compute. lia. }
  change pin_N with (rsa_N rsa_test).
  rewrite Hg.
  unfold rsa_N, Problem_Factor.
  change (rsa_p rsa_test) with pin_p.
  change (rsa_q rsa_test) with pin_q.
  split; [reflexivity|].
  split; [lia | exists pin_q; reflexivity].
Qed.

Theorem pin_miller_from_lam_factors :
  Problem_Factor pin_N
    (Z.gcd (2 ^ (odd_part pin_lam * pow2n (val2 pin_ord2_p)) - 1) pin_N).
Proof.
  apply (proj2 (pin_miller_from_lambda_multiple pin_lam ltac:(lia) ltac:(exists 1; lia))).
Qed.

Theorem pin_miller_from_2lam_factors :
  Problem_Factor pin_N
    (Z.gcd (2 ^ (odd_part (2 * pin_lam) * pow2n (val2 pin_ord2_p)) - 1) pin_N).
Proof.
  apply (proj2 (pin_miller_from_lambda_multiple (2 * pin_lam)
                  ltac:(lia) ltac:(exists 2; lia))).
Qed.

Theorem pin_ed_minus_1_is_lam :
  pin_e * pin_d - 1 = pin_lam.
Proof. vm_compute. reflexivity. Qed.

(** ** Different residual [e] gives a different [x]

    [e = 7] is residual, [7^{-1} ≡ 23 (mod λ)], unique unit 7th
    root of [36] is [60 ≠ 42].  Outside the public congruence
    class.  Not [residual_solver_constructs_factor_open_named]. *)

Theorem pin_inv7_mod_lam :
  (7 * 23) mod pin_lam = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_y_to_23 :
  powm pin_y 23 pin_N = 60.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_e7_residual :
  srsa_residual_leaf pin_N pin_lam pin_y 60 7.
Proof.
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 3; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem pin_e7_x_neq_pin_x :
  60 <> pin_x.
Proof. discriminate. Qed.

Theorem pin_e7_not_cong_pin_e :
  ~ Z.divide pin_lam (7 - pin_e).
Proof. intros [k Hk]. nia. Qed.

(** ** Residual solver with [e ≡ pin_e (mod λ)]

    Writes the trapdoor map on [x].  A non-minimal such [e]
    Millers from [e − pin_e] recovered from the solver (no extra
    [d]).  The unrestricted residual solver may choose [e] outside
    this class ([pin_e7_residual]).
    Not [residual_solver_constructs_factor_open_named]. *)

Definition residual_solver_reduced_e_cong
    (Solve : residual_solver_reduced pin_N pin_lam) (e0 : Z) : Prop :=
  forall y Hrng Hy,
    Z.divide pin_lam (snd (proj1_sig (Solve y Hrng Hy)) - e0).

Lemma residual_e_cong_pin_e_ge :
  forall e,
    1 < e ->
    Z.divide pin_lam (e - pin_e) ->
    pin_e <= e.
Proof.
  intros e He [k Hk]. nia.
Qed.

Theorem residual_solver_reduced_e_cong_x_is_trapdoor :
  forall (Solve : residual_solver_reduced pin_N pin_lam) y Hrng Hy,
    residual_solver_reduced_e_cong Solve pin_e ->
    fst (proj1_sig (Solve y Hrng Hy)) mod pin_N = powm y pin_d pin_N.
Proof.
  intros Solve y Hrng Hy Hcong.
  pose proof (Hcong y Hrng Hy) as Hdiv.
  destruct (proj1_sig (Solve y Hrng Hy)) as [x e] eqn:Hxe.
  cbn [fst snd] in Hdiv |- *.
  pose proof (proj2_sig (Solve y Hrng Hy)) as Hleaf.
  rewrite Hxe in Hleaf.
  destruct Hleaf as [Hycop [[He Hpow] _]].
  pose proof (srsa_unit_y_forces_unit_x pin_N y x e
                ltac:(lia) ltac:(lia) Hycop Hpow) as Hx.
  destruct Hdiv as [k Hk].
  assert (Heq : e = pin_e + k * pin_lam) by lia.
  assert (Hk0 : 0 <= k) by nia.
  rewrite Heq in Hpow.
  rewrite (unit_powm_plus_k_lam x pin_e k ltac:(lia) Hk0 Hx) in Hpow.
  replace (powm y pin_d pin_N) with (powm y pin_d pin_N mod pin_N).
  2: { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
  apply (pin_unique_unit_eth_root x (powm y pin_d pin_N)).
  - exact Hx.
  - unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
    apply Z.coprime_pow_l; [lia | exact Hycop].
  - rewrite Hpow, (pin_powm_de y Hycop). rewrite Z.mod_small; lia.
Qed.

Theorem residual_solver_reduced_e_cong_nonminimal_constructs_factor :
  forall (Solve : residual_solver_reduced pin_N pin_lam) y Hrng Hy,
    residual_solver_reduced_e_cong Solve pin_e ->
    snd (proj1_sig (Solve y Hrng Hy)) <> pin_e ->
    exists f, Problem_Factor pin_N f.
Proof.
  intros Solve y Hrng Hy Hcong Hne.
  pose proof (Hcong y Hrng Hy) as Hdiv.
  destruct (proj1_sig (Solve y Hrng Hy)) as [x e] eqn:Hxe.
  cbn [fst snd] in Hne, Hdiv.
  pose proof (proj2_sig (Solve y Hrng Hy)) as Hleaf.
  rewrite Hxe in Hleaf.
  destruct Hleaf as [_ [[He _] _]].
  assert (Hpos : 0 < e - pin_e).
  { destruct Hdiv as [k Hk]. nia. }
  destruct (pin_miller_from_lambda_multiple (e - pin_e) Hpos Hdiv) as [_ Hf].
  eexists. exact Hf.
Qed.

Theorem residual_solver_reduced_e_cong_constructs_factor :
  forall (Solve : residual_solver_reduced pin_N pin_lam),
    residual_solver_reduced_e_cong Solve pin_e ->
    (forall y Hrng Hy,
       fst (proj1_sig (Solve y Hrng Hy)) mod pin_N = powm y pin_d pin_N) /\
    exists f, Problem_Factor pin_N f.
Proof.
  intros Solve Hcong.
  split.
  - intros y Hrng Hy.
    apply residual_solver_reduced_e_cong_x_is_trapdoor; assumption.
  - eexists. apply pin_miller_from_d_factors.
Qed.

Definition pin_e_plus_lam_residual_solver : residual_solver_reduced pin_N pin_lam.
Proof.
  intros y Hrng Hy.
  refine (exist _ (powm y pin_d pin_N, pin_e + pin_lam) _).
  apply (residual_leaf_plus_k_lam y (powm y pin_d pin_N) pin_e 1);
    [lia | apply trapdoor_inhabits_residual_leaf; assumption].
Defined.

Theorem pin_e_plus_lam_solver_e_cong :
  residual_solver_reduced_e_cong pin_e_plus_lam_residual_solver pin_e.
Proof.
  intros y Hrng Hy. cbn. exists 1. lia.
Qed.

Theorem pin_e_plus_lam_solver_nonminimal :
  forall y Hrng Hy,
    snd (proj1_sig (pin_e_plus_lam_residual_solver y Hrng Hy)) <> pin_e.
Proof.
  intros y Hrng Hy. cbn. lia.
Qed.

Theorem pin_e_plus_lam_solver_millers :
  exists f, Problem_Factor pin_N f.
Proof.
  apply (residual_solver_reduced_e_cong_nonminimal_constructs_factor
           pin_e_plus_lam_residual_solver pin_y
           ltac:(lia) ltac:(vm_compute; reflexivity)).
  - apply pin_e_plus_lam_solver_e_cong.
  - apply pin_e_plus_lam_solver_nonminimal.
Qed.

(** ** Fixed residual [e] with a known inverse

    [residual_solver_reduced_returns_e] at an arbitrary residual
    [e], plus [e d' ≡ 1 (mod λ)], is the trapdoor map
    [y ↦ y^{d'}].  Miller-from-[e d' − 1] splits because that
    [M] is a multiple of [λ].  Specializes to public [e] at
    [d' = d].  Inhabitant at [e = 7], [d' = 23].  Miller uses
    [d'], not the solver.  Not
    [residual_solver_constructs_factor_open_named]. *)

Lemma pin_ed_inv_divides_lam :
  forall e d',
    (e * d') mod pin_lam = 1 ->
    Z.divide pin_lam (e * d' - 1).
Proof.
  intros e d' Hinv.
  apply mods_eq_iff_divides; [lia|].
  rewrite Hinv. symmetry. apply Z.mod_1_l. lia.
Qed.

Lemma pin_ed_inv_M_pos :
  forall e d',
    1 < e ->
    0 <= d' ->
    (e * d') mod pin_lam = 1 ->
    0 < e * d' - 1.
Proof.
  intros e d' He Hd Hinv.
  pose proof (pin_ed_inv_divides_lam e d' Hinv) as [k Hk].
  destruct (Z.lt_trichotomy k 0) as [Hkneg | [Hkz | Hkpos]].
  - nia.
  - subst k. rewrite Z.mul_0_l in Hk.
    destruct (Z.eq_dec d' 0) as [Hz | Hnz].
    + subst d'. lia.
    + assert (2 <= e * d').
      { replace 2 with (2 * 1) by lia.
        apply Z.mul_le_mono_nonneg; lia. }
      lia.
  - nia.
Qed.

Lemma pin_powm_mul_inv :
  forall e d' x,
    1 < e ->
    0 <= d' ->
    (e * d') mod pin_lam = 1 ->
    Z.coprime x pin_N ->
    powm (powm x e pin_N) d' pin_N = x mod pin_N /\
    powm (powm x d' pin_N) e pin_N = x mod pin_N.
Proof.
  intros e d' x He Hd Hinv Hx.
  assert (HMpos : 0 < e * d' - 1) by (apply pin_ed_inv_M_pos; assumption).
  assert (Hdiv : Z.divide (lambda_semiprime pin_p pin_q) (e * d' - 1)).
  { rewrite rsa_test_lambda. apply pin_ed_inv_divides_lam. exact Hinv. }
  assert (Hround : powm x (e * d') pin_N = x mod pin_N).
  { replace (e * d') with (e * d' - 1 + 1) by lia.
    rewrite powm_add_r by lia.
    rewrite powm_1_r by lia.
    rewrite (annihilates_units pin_p pin_q x (e * d' - 1));
      [ rewrite Z.mul_1_l, Z.mod_mod by lia; reflexivity
      | apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q
      | exact Hx | lia | exact Hdiv ]. }
  split.
  - rewrite <- powm_mul_r by lia. exact Hround.
  - rewrite <- powm_mul_r by lia. rewrite (Z.mul_comm d' e). exact Hround.
Qed.

Theorem unique_unit_eth_root_inv :
  forall e d' x z,
    1 < e ->
    0 <= d' ->
    (e * d') mod pin_lam = 1 ->
    Z.coprime x pin_N ->
    Z.coprime z pin_N ->
    powm x e pin_N = powm z e pin_N ->
    x mod pin_N = z mod pin_N.
Proof.
  intros e d' x z He Hd Hinv Hx Hz Heq.
  rewrite <- (proj1 (pin_powm_mul_inv e d' x He Hd Hinv Hx)).
  rewrite <- (proj1 (pin_powm_mul_inv e d' z He Hd Hinv Hz)).
  rewrite Heq. reflexivity.
Qed.

Theorem trapdoor_inhabits_residual_leaf_at :
  forall e d' y,
    0 <= d' ->
    residual_shaped_e e pin_lam ->
    (e * d') mod pin_lam = 1 ->
    0 <= y < pin_N ->
    Z.coprime y pin_N ->
    srsa_residual_leaf pin_N pin_lam y (powm y d' pin_N) e.
Proof.
  intros e d' y Hd [He [Hodd [Hgcd Hnd]]] Hinv Hrng Hy.
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [exact Hy|].
  split.
  - split; [exact He|].
    rewrite (proj2 (pin_powm_mul_inv e d' y He Hd Hinv Hy)).
    rewrite Z.mod_small; lia.
  - split; [exact Hodd | split; [exact Hgcd | exact Hnd]].
Qed.

Theorem residual_shaped_e_7 :
  residual_shaped_e 7 pin_lam.
Proof.
  unfold residual_shaped_e.
  split; [lia|].
  split; [exists 3; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem residual_solver_reduced_fixed_e_is_trapdoor :
  forall (Solve : residual_solver_reduced pin_N pin_lam) e d' y Hrng Hy,
    0 <= d' ->
    (e * d') mod pin_lam = 1 ->
    residual_solver_reduced_returns_e Solve e ->
    fst (proj1_sig (Solve y Hrng Hy)) mod pin_N = powm y d' pin_N.
Proof.
  intros Solve e d' y Hrng Hy Hd Hinv Hfix.
  pose proof (Hfix y Hrng Hy) as He.
  destruct (proj1_sig (Solve y Hrng Hy)) as [x e'] eqn:Hxe.
  cbn [fst snd] in He |- *. subst e'.
  pose proof (proj2_sig (Solve y Hrng Hy)) as Hleaf.
  rewrite Hxe in Hleaf.
  destruct Hleaf as [Hycop [[Hegt Hpow] _]].
  pose proof (srsa_unit_y_forces_unit_x pin_N y x e
                ltac:(lia) ltac:(lia) Hycop Hpow) as Hx.
  replace (powm y d' pin_N) with (powm y d' pin_N mod pin_N).
  2: { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
  apply (unique_unit_eth_root_inv e d' x (powm y d' pin_N) Hegt Hd Hinv).
  - exact Hx.
  - unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
    apply Z.coprime_pow_l; [lia | exact Hycop].
  - rewrite Hpow, (proj2 (pin_powm_mul_inv e d' y Hegt Hd Hinv Hycop)).
    rewrite Z.mod_small; lia.
Qed.

Theorem residual_solver_reduced_fixed_e_constructs_factor :
  forall (Solve : residual_solver_reduced pin_N pin_lam) e d',
    0 <= d' ->
    (e * d') mod pin_lam = 1 ->
    residual_solver_reduced_returns_e Solve e ->
    (forall y Hrng Hy,
       fst (proj1_sig (Solve y Hrng Hy)) mod pin_N = powm y d' pin_N) /\
    exists f, Problem_Factor pin_N f.
Proof.
  intros Solve e d' Hd Hinv Hfix.
  split.
  - intros y Hrng Hy.
    apply (residual_solver_reduced_fixed_e_is_trapdoor Solve e d');
      assumption.
  - assert (Hegt : 1 < e).
    { assert (Hyrng : 0 <= pin_y < pin_N) by lia.
      assert (Hycop : Z.coprime pin_y pin_N) by (vm_compute; reflexivity).
      pose proof (Hfix pin_y Hyrng Hycop) as He.
      pose proof (proj2_sig (Solve pin_y Hyrng Hycop)) as Hleaf.
      destruct (proj1_sig (Solve pin_y Hyrng Hycop)) as [x e'] eqn:Hxe.
      cbn [fst snd] in He, Hleaf.
      subst e'.
      destruct Hleaf as [_ [[He1 _] _]]. exact He1. }
    pose proof (pin_ed_inv_M_pos e d' Hegt Hd Hinv) as HMpos.
    pose proof (pin_ed_inv_divides_lam e d' Hinv) as Hdiv.
    destruct (pin_miller_from_lambda_multiple (e * d' - 1) HMpos Hdiv)
      as [_ Hf].
    eexists. exact Hf.
Qed.

Definition pin_e7_residual_solver : residual_solver_reduced pin_N pin_lam.
Proof.
  intros y Hrng Hy.
  refine (exist _ (powm y 23 pin_N, 7) _).
  apply (trapdoor_inhabits_residual_leaf_at 7 23);
    [lia | apply residual_shaped_e_7 | apply pin_inv7_mod_lam
     | exact Hrng | exact Hy].
Defined.

Theorem pin_e7_solver_returns_e :
  residual_solver_reduced_returns_e pin_e7_residual_solver 7.
Proof. intros y Hrng Hy. cbn. reflexivity. Qed.

Theorem pin_e7_solver_constructs_factor :
  (forall y Hrng Hy,
     fst (proj1_sig (pin_e7_residual_solver y Hrng Hy)) mod pin_N
       = powm y 23 pin_N) /\
  exists f, Problem_Factor pin_N f.
Proof.
  apply (residual_solver_reduced_fixed_e_constructs_factor
           pin_e7_residual_solver 7 23);
    [lia | apply pin_inv7_mod_lam | apply pin_e7_solver_returns_e].
Qed.

Theorem pin_miller_from_e7_inv :
  Problem_Factor pin_N
    (Z.gcd (2 ^ (odd_part (7 * 23 - 1) * pow2n (val2 pin_ord2_p)) - 1)
           pin_N).
Proof.
  apply (proj2 (pin_miller_from_lambda_multiple (7 * 23 - 1)
                  ltac:(lia) ltac:(exists 2; vm_compute; reflexivity))).
Qed.

Theorem residual_shaped_e_11 :
  residual_shaped_e 11 pin_lam.
Proof.
  unfold residual_shaped_e.
  split; [lia|].
  split; [exists 5; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem pin_inv11_mod_lam :
  (11 * 51) mod pin_lam = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_miller_from_e11_inv :
  Problem_Factor pin_N
    (Z.gcd (2 ^ (odd_part (11 * 51 - 1) * pow2n (val2 pin_ord2_p)) - 1)
           pin_N).
Proof.
  assert (HM : 0 < 11 * 51 - 1) by lia.
  assert (Hdiv : Z.divide pin_lam (11 * 51 - 1)).
  { exists 7. reflexivity. }
  apply (proj2 (pin_miller_from_lambda_multiple (11 * 51 - 1) HM Hdiv)).
Qed.

Theorem residual_solver_reduced_pin_e_via_fixed_e :
  forall (Solve : residual_solver_reduced pin_N pin_lam),
    residual_solver_reduced_returns_e Solve pin_e ->
    (forall y Hrng Hy,
       fst (proj1_sig (Solve y Hrng Hy)) mod pin_N = powm y pin_d pin_N) /\
    exists f, Problem_Factor pin_N f.
Proof.
  intros Solve Hfix.
  apply (residual_solver_reduced_fixed_e_constructs_factor
           Solve pin_e pin_d);
    [lia | apply rsa_test_inv | exact Hfix].
Qed.

(** ** Unique unit [e]-th roots from [gcd(e,λ)=1]

    General for distinct primes ([unique_unit_eth_root_coprime]);
    the pin wrapper is [unique_unit_eth_root_from_coprime_e].
    Kernel of the [e]-power map on units is trivial when
    [gcd(e,λ)=1]: [ord(x z⁻¹) | gcd(e,λ)].  No inverse of [e] is
    handed over.  [e = 5] shares [λ], so [1] and [g^{16}] are
    distinct 5th roots of [1].  Not
    [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/237], [cas/253]. *)

Lemma powm_mul_l_mod :
  forall a b e n,
    n <> 0 ->
    0 <= e ->
    powm (a * b) e n = (powm a e n * powm b e n) mod n.
Proof.
  intros a b e n Hn He.
  unfold powm. rewrite Z.pow_mul_l by lia. apply Z.mul_mod; lia.
Qed.

Lemma unit_inverse_semiprime :
  forall p q a,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    Z.coprime a (p * q) ->
    exists w, (a * w) mod (p * q) = 1 /\ Z.coprime w (p * q).
Proof.
  intros p q a Hp Hq Hneq Ha.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  pose proof (lambda_semiprime_pos p q Hp Hq) as Hlam.
  exists (powm a (lambda_semiprime p q - 1) (p * q)).
  split.
  - transitivity (powm a (lambda_semiprime p q) (p * q)).
    + rewrite <- Z.mul_mod_idemp_l by nia.
      rewrite <- (powm_1_r a (p * q)) by nia.
      rewrite <- powm_add_r by nia.
      f_equal. lia.
    + apply carmichael_semiprime; assumption.
  - unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
    apply Z.coprime_pow_l; [lia | exact Ha].
Qed.

Lemma pin_unit_inverse :
  forall a,
    Z.coprime a pin_N ->
    exists w, (a * w) mod pin_N = 1 /\ Z.coprime w pin_N.
Proof.
  intros a Ha. change pin_N with (pin_p * pin_q).
  apply unit_inverse_semiprime;
    [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q | exact Ha].
Qed.

Theorem unique_unit_eth_root_coprime :
  forall p q e x z,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    0 < e ->
    Z.gcd e (lambda_semiprime p q) = 1 ->
    Z.coprime x (p * q) ->
    Z.coprime z (p * q) ->
    powm x e (p * q) = powm z e (p * q) ->
    x mod (p * q) = z mod (p * q).
Proof.
  intros p q e x z Hp Hq Hneq He Hgcd Hx Hz Heq.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  assert (HN : 1 < p * q) by nia.
  destruct (unit_inverse_semiprime p q z Hp Hq Hneq Hz) as [w [Hw Hwc]].
  set (u := (x * w) mod (p * q)).
  assert (Hu1 : powm u e (p * q) = 1).
  { unfold u.
    rewrite powm_mod_base by lia.
    rewrite powm_mul_l_mod by lia.
    assert (Hzw : powm (z * w) e (p * q) = 1).
    { rewrite <- powm_mod_base with (a := z * w) by lia.
      rewrite Hw. unfold powm. rewrite Z.pow_1_l by lia.
      apply Z.mod_1_l. lia. }
    rewrite powm_mul_l_mod in Hzw by lia.
    rewrite Heq.
    exact Hzw. }
  assert (Huc : Z.coprime u (p * q)).
  { unfold u, Z.coprime. rewrite Z.gcd_mod_l.
    apply Z.coprime_mul_l; [exact Hx | exact Hwc]. }
  destruct (order_exists_from_annihilator u (p * q) e
              HN He Hu1) as [k [Hord Hk_e]].
  assert (Hk_lam : (k | lambda_semiprime p q)).
  { apply (order_divides_lambda p q u k Hp Hq Hneq Huc Hord). }
  assert (Hk1 : (k | 1)).
  { destruct (Z.gcd_bezout e (lambda_semiprime p q) 1 Hgcd) as [s [t Hst]].
    rewrite <- Hst.
    apply Z.divide_add_r.
    - destruct Hk_e as [qe Hqe]. exists (s * qe). rewrite Hqe. lia.
    - destruct Hk_lam as [r Hr]. exists (t * r). rewrite Hr. lia. }
  assert (k = 1).
  { apply Z.divide_1_r in Hk1.
    destruct Hk1 as [Hk1 | Hk1]; [exact Hk1|].
    destruct Hord as [Hkpos _]. lia. }
  subst k.
  assert (Hu_one : u mod (p * q) = 1).
  { destruct Hord as [_ [Hank _]].
    rewrite powm_1_r in Hank by lia.
    exact Hank. }
  unfold u in Hu_one.
  rewrite Z.mod_mod in Hu_one by lia.
  apply (mul_cancel_unit_mod (p * q) w x z).
  - exact HN.
  - exact Hwc.
  - rewrite (Z.mul_comm w x), (Z.mul_comm w z).
    rewrite Hw, Hu_one. reflexivity.
Qed.

Theorem unique_unit_eth_root_from_coprime_e :
  forall e x z,
    0 < e ->
    Z.gcd e pin_lam = 1 ->
    Z.coprime x pin_N ->
    Z.coprime z pin_N ->
    powm x e pin_N = powm z e pin_N ->
    x mod pin_N = z mod pin_N.
Proof.
  intros e x z He Hgcd Hx Hz Heq.
  change pin_N with (pin_p * pin_q) in Hx, Hz, Heq |- *.
  rewrite <- rsa_test_lambda in Hgcd.
  apply (unique_unit_eth_root_coprime pin_p pin_q e x z);
    [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q
     | exact He | exact Hgcd | exact Hx | exact Hz | exact Heq].
Qed.

Theorem pin_e5_fifth_roots_not_unique :
  let u := powm pin_g 16 pin_N in
  powm 1 5 pin_N = powm u 5 pin_N /\
  Z.coprime 1 pin_N /\
  Z.coprime u pin_N /\
  1 mod pin_N <> u mod pin_N /\
  Z.gcd 5 pin_lam = 5.
Proof. vm_compute. repeat split; congruence. Qed.

Theorem pin_unique_unit_cube_from_coprime :
  forall x z,
    Z.coprime x pin_N ->
    Z.coprime z pin_N ->
    powm x pin_e pin_N = powm z pin_e pin_N ->
    x mod pin_N = z mod pin_N.
Proof.
  intros x z Hx Hz Heq.
  apply (unique_unit_eth_root_from_coprime_e pin_e x z);
    [lia | vm_compute; reflexivity | exact Hx | exact Hz | exact Heq].
Qed.

(** ** Bézout inverse of residual [e] modulo [λ]

    [gcd(e,λ)=1] produces [d'] with [e d' ≡ 1 (mod λ)].  A fixed-[e]
    residual solver then Millers with no [d'] hypothesis.  Miller
    uses [(e,λ)], not the solver's [x]-values.  Not
    [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/238]. *)

Theorem residual_inv_mod_lam :
  forall e,
    Z.gcd e pin_lam = 1 ->
    exists d', 0 <= d' < pin_lam /\ (e * d') mod pin_lam = 1.
Proof.
  intros e Hgcd.
  destruct (Z.gcd_bezout e pin_lam 1 Hgcd) as [u [v Hs]].
  exists (u mod pin_lam).
  split.
  - apply Z.mod_pos_bound. lia.
  - rewrite Z.mul_mod_idemp_r by lia.
    rewrite (Z.mul_comm e u).
    replace (u * e) with (1 + (- v) * pin_lam) by lia.
    rewrite Z.mod_add by lia.
    apply Z.mod_1_l. lia.
Qed.

Theorem residual_solver_reduced_fixed_e_constructs_factor_from_e :
  forall (Solve : residual_solver_reduced pin_N pin_lam) e,
    residual_shaped_e e pin_lam ->
    residual_solver_reduced_returns_e Solve e ->
    exists d',
      0 <= d' < pin_lam /\
      (e * d') mod pin_lam = 1 /\
      (forall y Hrng Hy,
         fst (proj1_sig (Solve y Hrng Hy)) mod pin_N = powm y d' pin_N) /\
      exists f, Problem_Factor pin_N f.
Proof.
  intros Solve e [He [Hodd [Hgcd Hnd]]] Hfix.
  destruct (residual_inv_mod_lam e Hgcd) as [d' [[Hdlo Hdhi] Hinv]].
  exists d'.
  split; [lia|].
  split; [exact Hinv|].
  destruct (residual_solver_reduced_fixed_e_constructs_factor
              Solve e d' Hdlo Hinv Hfix) as [Hmap Hex].
  split; [exact Hmap | exact Hex].
Qed.

Theorem pin_e7_solver_constructs_factor_from_e :
  exists d',
    0 <= d' < pin_lam /\
    (7 * d') mod pin_lam = 1 /\
    (forall y Hrng Hy,
       fst (proj1_sig (pin_e7_residual_solver y Hrng Hy)) mod pin_N
         = powm y d' pin_N) /\
    exists f, Problem_Factor pin_N f.
Proof.
  apply (residual_solver_reduced_fixed_e_constructs_factor_from_e
           pin_e7_residual_solver 7);
    [apply residual_shaped_e_7 | apply pin_e7_solver_returns_e].
Qed.

(** ** Invert-all-units polynomial at a residual [e]

    Uniqueness (kernel) plus Bézout [d'] : a polynomial that inverts
    every unit at residual [e] is the trapdoor map [y ↦ y^{d'}].
    Miller-from-[e d' − 1] splits.  Inhabitant [X^{23}] at [e = 7].
    Not [residual_solver_constructs_factor_open_named]: a solver is
    not a polynomial.  Cross-confirmed by [cas/239]. *)

Theorem invert_all_units_poly_at_e :
  forall P e,
    residual_shaped_e e pin_lam ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) e pin_N = y mod pin_N) ->
    exists d',
      0 <= d' < pin_lam /\
      (e * d') mod pin_lam = 1 /\
      (forall y, Z.coprime y pin_N ->
         poly_eval P y mod pin_N = powm y d' pin_N) /\
      exists f, Problem_Factor pin_N f.
Proof.
  intros P e [He [Hodd [Hgcd Hnd]]] Hall.
  destruct (residual_inv_mod_lam e Hgcd) as [d' [[Hdlo Hdhi] Hinv]].
  exists d'.
  split; [lia|].
  split; [exact Hinv|].
  assert (Hmap : forall y, Z.coprime y pin_N ->
                    poly_eval P y mod pin_N = powm y d' pin_N).
  { intros y Hy.
    assert (Hx : Z.coprime (poly_eval P y) pin_N).
    { apply (powm_unit_is_coprime (poly_eval P y) e pin_N);
        [apply pin_N_gt_1 | lia |].
      rewrite (Hall y Hy). rewrite Z.gcd_mod_l. exact Hy. }
    assert (Hz : Z.coprime (powm y d' pin_N) pin_N).
    { unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
      apply Z.coprime_pow_l; [lia | exact Hy]. }
    replace (powm y d' pin_N) with (powm y d' pin_N mod pin_N).
    2: { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
    apply (unique_unit_eth_root_from_coprime_e e (poly_eval P y)
             (powm y d' pin_N));
      [lia | exact Hgcd | exact Hx | exact Hz |].
    rewrite (Hall y Hy).
    rewrite (proj2 (pin_powm_mul_inv e d' y He Hdlo Hinv Hy)).
    reflexivity. }
  split; [exact Hmap|].
  pose proof (pin_ed_inv_M_pos e d' He Hdlo Hinv) as HMpos.
  pose proof (pin_ed_inv_divides_lam e d' Hinv) as Hdiv.
  destruct (pin_miller_from_lambda_multiple (e * d' - 1) HMpos Hdiv)
    as [_ Hf].
  eexists. exact Hf.
Qed.

Definition pin_e7_monomial : list Z := poly_Xn (Z.to_nat 23).

Theorem pin_X23_inverts_at_7 :
  forall y,
    Z.coprime y pin_N ->
    powm (poly_eval pin_e7_monomial y) 7 pin_N = y mod pin_N.
Proof.
  intros y Hy.
  unfold pin_e7_monomial.
  rewrite poly_eval_Xn, Z2Nat.id by lia.
  transitivity (powm (powm y 23 pin_N) 7 pin_N).
  - unfold powm at 2. rewrite <- powm_mod_base by lia. reflexivity.
  - apply (proj2 (pin_powm_mul_inv 7 23 y ltac:(lia) ltac:(lia)
                    pin_inv7_mod_lam Hy)).
Qed.

Theorem pin_X23_poly_at_7_constructs_factor :
  exists d',
    0 <= d' < pin_lam /\
    (7 * d') mod pin_lam = 1 /\
    (forall y, Z.coprime y pin_N ->
       poly_eval pin_e7_monomial y mod pin_N = powm y d' pin_N) /\
    exists f, Problem_Factor pin_N f.
Proof.
  apply (invert_all_units_poly_at_e pin_e7_monomial 7);
    [apply residual_shaped_e_7 | apply pin_X23_inverts_at_7].
Qed.
