From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.

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
Require Import SrsaModCbrt.
Require Import SrsaRootPoly.
Require Import SrsaVaryingE.

Open Scope Z_scope.

(** * Recover [d'] from a fixed-[e] solver's [x]-values

    Discrete log of [Solve(g)] in base [g] (order [λ]) is the
    inverse of [e] modulo [λ].  Miller-from-[e d' − 1] then splits.
    The multiple is read off the solver, not handed as a hyp.
    [e] is still fixed.  Not
    [residual_solver_constructs_factor_open_named].
    Not [rsa_inverter_constructs_factor_open_named].
    Cross-confirmed by [cas/240]. *)

(** ** Discrete log of a fixed-[e] solver at a generator

    Not [residual_solver_constructs_factor_open_named].
    Not [rsa_inverter_constructs_factor_open_named]. *)

Fixpoint dlog_search (g t N : Z) (k fuel : nat) : option Z :=
  match fuel with
  | O => None
  | S fuel' =>
      if powm g (Z.of_nat k) N =? t mod N
      then Some (Z.of_nat k)
      else dlog_search g t N (S k) fuel'
  end.

Definition pin_dlog_mod_lam (g t : Z) : option Z :=
  dlog_search g t pin_N 0%nat (Z.to_nat pin_lam).

Lemma dlog_search_correct :
  forall g t N k fuel k0,
    (k <= k0)%nat ->
    (k0 < k + fuel)%nat ->
    powm g (Z.of_nat k0) N = t mod N ->
    (forall j, (k <= j < k0)%nat ->
       powm g (Z.of_nat j) N <> t mod N) ->
    dlog_search g t N k fuel = Some (Z.of_nat k0).
Proof.
  intros g t N k fuel.
  revert k.
  induction fuel as [|fuel IH]; intros k k0 Hle Hlt Hit Hmiss.
  - lia.
  - cbn [dlog_search].
    destruct (powm g (Z.of_nat k) N =? t mod N) eqn:Heq.
    + apply Z.eqb_eq in Heq.
      assert (k = k0).
      { destruct (Nat.eq_dec k k0) as [E | Ne]; [exact E|].
        exfalso. apply (Hmiss k); [lia | exact Heq]. }
      subst k0. reflexivity.
    + apply Z.eqb_neq in Heq.
      assert (k < k0)%nat.
      { destruct (Nat.eq_dec k k0) as [E | Ne]; [| lia].
        subst k0. congruence. }
      apply IH.
      * lia.
      * lia.
      * exact Hit.
      * intros j Hj. apply Hmiss. lia.
Qed.

Lemma dlog_search_mod :
  forall g t N k fuel,
    N <> 0 ->
    dlog_search g t N k fuel = dlog_search g (t mod N) N k fuel.
Proof.
  intros g t N k fuel HN.
  revert k.
  induction fuel as [|fuel IH]; intros k.
  - reflexivity.
  - cbn [dlog_search].
    rewrite Z.mod_mod by lia.
    destruct (powm g (Z.of_nat k) N =? t mod N); [reflexivity | apply IH].
Qed.

Lemma pin_g_powm_coprime :
  forall i,
    0 <= i ->
    Z.coprime (powm pin_g i pin_N) pin_N.
Proof.
  intros i Hi.
  unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
  apply Z.coprime_pow_l; [lia | apply pin_unit_3_coprime].
Qed.

Lemma pin_powm_already_mod :
  forall a e,
    powm a e pin_N mod pin_N = powm a e pin_N.
Proof.
  intros a e. unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma pin_g_unique_exp :
  forall i j,
    0 <= i < pin_lam ->
    0 <= j < pin_lam ->
    powm pin_g i pin_N = powm pin_g j pin_N ->
    i = j.
Proof.
  intros i j Hi Hj Heq.
  destruct (Z.eq_dec i j) as [E | Ne]; [exact E|].
  destruct (Z.le_gt_cases i j) as [Hij | Hji].
  - assert (0 < j - i) by lia.
    assert (Hsum : powm pin_g j pin_N =
                   (powm pin_g i pin_N * powm pin_g (j - i) pin_N) mod pin_N).
    { transitivity (powm pin_g (i + (j - i)) pin_N).
      - f_equal. lia.
      - apply (powm_add_r pin_g i (j - i) pin_N); lia. }
    assert (Hann : powm pin_g (j - i) pin_N = 1).
    { assert (Heqmod : (powm pin_g i pin_N * powm pin_g (j - i) pin_N) mod pin_N
                       = powm pin_g i pin_N mod pin_N).
      { rewrite <- Hsum, <- Heq. symmetry. apply pin_powm_already_mod. }
      pose proof (mul_cancel_mod_unit (powm pin_g i pin_N)
                    (powm pin_g (j - i) pin_N) pin_N
                    pin_N_gt_1 (pin_g_powm_coprime i ltac:(lia)) Heqmod) as Ha1.
      rewrite pin_powm_already_mod in Ha1. exact Ha1. }
    pose proof (order_divides_annihilator pin_N pin_g pin_lam (j - i)
                  pin_N_gt_1 ltac:(lia) is_order_pin_3_80 Hann) as Hdiv.
    pose proof (Z.divide_pos_le pin_lam (j - i) ltac:(lia) Hdiv).
    lia.
  - assert (0 < i - j) by lia.
    assert (Hsum : powm pin_g i pin_N =
                   (powm pin_g j pin_N * powm pin_g (i - j) pin_N) mod pin_N).
    { transitivity (powm pin_g (j + (i - j)) pin_N).
      - f_equal. lia.
      - apply (powm_add_r pin_g j (i - j) pin_N); lia. }
    assert (Hann : powm pin_g (i - j) pin_N = 1).
    { assert (Heqmod : (powm pin_g j pin_N * powm pin_g (i - j) pin_N) mod pin_N
                       = powm pin_g j pin_N mod pin_N).
      { rewrite <- Hsum, Heq. symmetry. apply pin_powm_already_mod. }
      pose proof (mul_cancel_mod_unit (powm pin_g j pin_N)
                    (powm pin_g (i - j) pin_N) pin_N
                    pin_N_gt_1 (pin_g_powm_coprime j ltac:(lia)) Heqmod) as Ha1.
      rewrite pin_powm_already_mod in Ha1. exact Ha1. }
    pose proof (order_divides_annihilator pin_N pin_g pin_lam (i - j)
                  pin_N_gt_1 ltac:(lia) is_order_pin_3_80 Hann) as Hdiv.
    pose proof (Z.divide_pos_le pin_lam (i - j) ltac:(lia) Hdiv).
    lia.
Qed.

Lemma pin_dlog_mod_lam_of_power :
  forall d,
    0 <= d < pin_lam ->
    pin_dlog_mod_lam pin_g (powm pin_g d pin_N) = Some d.
Proof.
  intros d Hd.
  unfold pin_dlog_mod_lam.
  replace d with (Z.of_nat (Z.to_nat d)) at 2 by (rewrite Z2Nat.id; lia).
  apply dlog_search_correct.
  - lia.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite Nat.add_0_l, Z2Nat.id by lia.
    lia.
  - rewrite Z2Nat.id by lia.
    symmetry. apply pin_powm_already_mod.
  - intros j Hj Hcoll.
    rewrite pin_powm_already_mod in Hcoll.
    apply (pin_g_unique_exp (Z.of_nat j) d) in Hcoll.
    + subst d. lia.
    + split; [lia |].
      destruct Hj as [_ Hjk0].
      apply Nat2Z.inj_lt in Hjk0.
      rewrite Z2Nat.id in Hjk0 by lia.
      lia.
    + lia.
Qed.

Lemma pin_g_range : 0 <= pin_g < pin_N.
Proof. lia. Qed.

Lemma pin_g_coprime : Z.coprime pin_g pin_N.
Proof. apply pin_unit_3_coprime. Qed.

Theorem residual_solver_reduced_fixed_e_extracts_and_factors :
  forall (Solve : residual_solver_reduced pin_N pin_lam) e,
    residual_shaped_e e pin_lam ->
    residual_solver_reduced_returns_e Solve e ->
    exists d',
      pin_dlog_mod_lam pin_g
        (fst (proj1_sig (Solve pin_g pin_g_range pin_g_coprime)))
        = Some d' /\
      0 <= d' < pin_lam /\
      (e * d') mod pin_lam = 1 /\
      (forall y Hrng Hy,
         fst (proj1_sig (Solve y Hrng Hy)) mod pin_N = powm y d' pin_N) /\
      exists f, Problem_Factor pin_N f.
Proof.
  intros Solve e Hs Hfix.
  destruct Hs as [He [Hodd [Hgcd Hnd]]].
  destruct (residual_inv_mod_lam e Hgcd) as [dB [[Hdlo Hdhi] Hinv]].
  pose proof (residual_solver_reduced_fixed_e_is_trapdoor
                Solve e dB pin_g pin_g_range pin_g_coprime
                Hdlo Hinv Hfix) as Hxg.
  set (x := fst (proj1_sig (Solve pin_g pin_g_range pin_g_coprime))).
  fold x in Hxg.
  assert (Hdlog : pin_dlog_mod_lam pin_g x = Some dB).
  { unfold pin_dlog_mod_lam.
    rewrite (dlog_search_mod pin_g x pin_N 0%nat (Z.to_nat pin_lam)
               ltac:(lia)).
    rewrite Hxg.
    change (dlog_search pin_g (powm pin_g dB pin_N) pin_N 0%nat
              (Z.to_nat pin_lam))
      with (pin_dlog_mod_lam pin_g (powm pin_g dB pin_N)).
    apply pin_dlog_mod_lam_of_power. lia. }
  exists dB.
  split; [exact Hdlog|].
  split; [lia|].
  split; [exact Hinv|].
  destruct (residual_solver_reduced_fixed_e_constructs_factor
              Solve e dB Hdlo Hinv Hfix) as [Hmap Hex].
  split; [exact Hmap | exact Hex].
Qed.

Theorem pin_e7_solver_extracts_and_factors :
  exists d',
    pin_dlog_mod_lam pin_g
      (fst (proj1_sig (pin_e7_residual_solver pin_g pin_g_range pin_g_coprime)))
      = Some d' /\
    0 <= d' < pin_lam /\
    (7 * d') mod pin_lam = 1 /\
    (forall y Hrng Hy,
       fst (proj1_sig (pin_e7_residual_solver y Hrng Hy)) mod pin_N
         = powm y d' pin_N) /\
    exists f, Problem_Factor pin_N f.
Proof.
  apply (residual_solver_reduced_fixed_e_extracts_and_factors
           pin_e7_residual_solver 7);
    [apply residual_shaped_e_7 | apply pin_e7_solver_returns_e].
Qed.

(** ** Residual leaf at the generator extracts [d']

    [x^e = g] with [gcd(e,λ)=1]: Bézout plus uniqueness give
    [x ≡ g^{d'}]; discrete log reads [d']; Miller-from-[e d' − 1]
    splits on this pin.  Any residual solver supplies such a leaf
    at [g], so every reduced residual solver on this pin constructs
    a factor.  Not
    [residual_solver_constructs_factor_open_named]: that quantifies
    over every [RSAInstance], not this pin's height mismatch.
    Cross-confirmed by [cas/241]. *)

Theorem residual_leaf_at_g_extracts_and_factors :
  forall x e,
    srsa_residual_leaf pin_N pin_lam pin_g x e ->
    exists d',
      pin_dlog_mod_lam pin_g x = Some d' /\
      0 <= d' < pin_lam /\
      (e * d') mod pin_lam = 1 /\
      exists f, Problem_Factor pin_N f.
Proof.
  intros x e Hleaf.
  destruct Hleaf as [Hgcop [[He Hpow] [_ [Hgcd _]]]].
  destruct (residual_inv_mod_lam e Hgcd) as [d' [[Hdlo Hdhi] Hinv]].
  pose proof (srsa_unit_y_forces_unit_x pin_N pin_g x e
                ltac:(lia) ltac:(lia) Hgcop Hpow) as Hx.
  assert (Hxg : x mod pin_N = powm pin_g d' pin_N).
  { replace (powm pin_g d' pin_N) with (powm pin_g d' pin_N mod pin_N).
    2: { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
    apply (unique_unit_eth_root_from_coprime_e e x (powm pin_g d' pin_N));
      [lia | exact Hgcd | exact Hx | |].
    - unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
      apply Z.coprime_pow_l; [lia | exact Hgcop].
    - rewrite Hpow.
      rewrite (proj2 (pin_powm_mul_inv e d' pin_g He Hdlo Hinv Hgcop)).
      rewrite Z.mod_small; [reflexivity | exact pin_g_range]. }
  assert (Hdlog : pin_dlog_mod_lam pin_g x = Some d').
  { unfold pin_dlog_mod_lam.
    rewrite (dlog_search_mod pin_g x pin_N 0%nat (Z.to_nat pin_lam)
               ltac:(lia)).
    rewrite Hxg.
    change (dlog_search pin_g (powm pin_g d' pin_N) pin_N 0%nat
              (Z.to_nat pin_lam))
      with (pin_dlog_mod_lam pin_g (powm pin_g d' pin_N)).
    apply pin_dlog_mod_lam_of_power. lia. }
  exists d'.
  split; [exact Hdlog|].
  split; [lia|].
  split; [exact Hinv|].
  pose proof (pin_ed_inv_M_pos e d' He Hdlo Hinv) as HMpos.
  pose proof (pin_ed_inv_divides_lam e d' Hinv) as Hdiv.
  destruct (pin_miller_from_lambda_multiple (e * d' - 1) HMpos Hdiv)
    as [_ Hf].
  eexists. exact Hf.
Qed.

Theorem residual_solver_reduced_constructs_factor_pin :
  forall Solve : residual_solver_reduced pin_N pin_lam,
    exists f, Problem_Factor pin_N f.
Proof.
  intros Solve.
  destruct (Solve pin_g pin_g_range pin_g_coprime) as [xe Hleaf].
  destruct xe as [x e].
  cbn in Hleaf.
  destruct (residual_leaf_at_g_extracts_and_factors x e Hleaf)
    as [d' [_ [_ [_ Hex]]]].
  exact Hex.
Qed.
