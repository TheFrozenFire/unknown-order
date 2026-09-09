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

    [dlog_search] / [pin_dlog_mod_lam] live in [SrsaRootPoly], so
    an invert-all-units poly can miller from a [k] read off [P].
    Not [residual_solver_constructs_factor_open_named].
    Not [rsa_inverter_constructs_factor_open_named]. *)

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
    [x ≡ g^{d'}]; discrete log reads [d']; [miller_walk] at
    [M = e d' − 1] with base 2 splits on this pin.  The miller
    step does not take [kp] from [p].  [g] is the module constant
    [pin_g], not constructed from [N,λ] without factors.  Any
    residual solver supplies such a leaf at [g], so every reduced
    residual solver on this pin constructs a factor.  Not
    [residual_solver_constructs_factor_open_named]: that quantifies
    over every [RSAInstance].  Not
    [residual_solver_extracts_factor_open_named].
    Cross-confirmed by [cas/248]. *)

Theorem pin_miller_walk_from_lambda_multiple :
  forall M,
    0 < M ->
    Z.divide pin_lam M ->
    exists f,
      miller_walk pin_N M 2 = Some f /\
      Problem_Factor pin_N f.
Proof.
  intros M HM Hdiv.
  assert (Hlam : Z.divide (rsa_lambda rsa_test) M).
  { unfold rsa_lambda.
    change (rsa_p rsa_test) with pin_p.
    change (rsa_q rsa_test) with pin_q.
    rewrite rsa_test_lambda. exact Hdiv. }
  destruct (miller_walk_factors rsa_test M 2
              (val2 pin_ord2_p) (val2 pin_ord2_q)
              HM Hlam) as [f [Hwalk [Hf1 [Hf2 Hfd]]]].
  - vm_compute. reflexivity.
  - discriminate.
  - discriminate.
  - change (rsa_p rsa_test) with pin_p.
    apply pin_base2_height_p_at_odd_part_of_lam_multiple; assumption.
  - change (rsa_q rsa_test) with pin_q.
    apply pin_base2_height_q_at_odd_part_of_lam_multiple; assumption.
  - vm_compute. discriminate.
  - exists f.
    unfold rsa_N in Hwalk, Hf1, Hf2, Hfd.
    change (rsa_p rsa_test * rsa_q rsa_test) with pin_N in Hwalk, Hf1, Hf2, Hfd.
    split; [exact Hwalk|].
    unfold Problem_Factor. split; [lia | exact Hfd].
Qed.

Theorem residual_leaf_at_g_extracts_and_factors :
  forall x e,
    srsa_residual_leaf pin_N pin_lam pin_g x e ->
    exists d',
      pin_dlog_mod_lam pin_g x = Some d' /\
      0 <= d' < pin_lam /\
      (e * d') mod pin_lam = 1 /\
      exists f,
        miller_walk pin_N (e * d' - 1) 2 = Some f /\
        Problem_Factor pin_N f.
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
  destruct (pin_miller_walk_from_lambda_multiple (e * d' - 1) HMpos Hdiv)
    as [f [Hwalk Hf]].
  exists f. split; [exact Hwalk | exact Hf].
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
    as [d' [_ [_ [_ [f [_ Hf]]]]]].
  exists f. exact Hf.
Qed.

(** ** Residual leaf at a unit of order [λ], off pin 187

    Uniqueness plus Bézout give [x ≡ g^{d'}]; [dlog_search] reads
    [d']; [miller_search] at [e d'−1] hits because mixed [√1]
    exist for even [M].  [g] of order [λ] is a hypothesis (or
    [exists_unit_order_lambda], which uses [p,q]).  Not
    [residual_solver_extracts_factor_open_named].  Not
    [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/255]. *)

Theorem residual_leaf_order_lambda_extracts_and_factors :
  forall p q g x e,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p <> 2 ->
    q <> 2 ->
    is_order (p * q) g (lambda_semiprime p q) ->
    Z.coprime g (p * q) ->
    srsa_residual_leaf (p * q) (lambda_semiprime p q) g x e ->
    exists d' a f,
      dlog_search g x (p * q) 0%nat
        (Z.to_nat (lambda_semiprime p q)) = Some d' /\
      0 <= d' < lambda_semiprime p q /\
      (e * d') mod (lambda_semiprime p q) = 1 /\
      miller_search (p * q) (e * d' - 1) = Some (a, f) /\
      Problem_Factor (p * q) f.
Proof.
  intros p q g x e Hp Hq Hneq Hp2 Hq2 Hor Hgcog Hleaf.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  assert (HN : 1 < p * q) by nia.
  pose proof (lambda_odd_primes_gt_1 p q Hp Hq Hp2 Hq2) as Hlam.
  destruct Hleaf as [Hyg [[He Hpow] [_ [Hgcd _]]]].
  destruct (residual_inv_mod_lambda e (lambda_semiprime p q) Hlam Hgcd)
    as [d' [[Hdlo Hdhi] Hinv]].
  pose proof (srsa_unit_y_forces_unit_x (p * q) g x e HN ltac:(lia) Hyg Hpow)
    as Hxcop.
  assert (Hg_red : 0 <= g < p * q).
  { unfold powm in Hpow. rewrite <- Hpow. apply Z.mod_pos_bound. lia. }
  assert (Hxg : x mod (p * q) = powm g d' (p * q)).
  { replace (powm g d' (p * q)) with (powm g d' (p * q) mod (p * q)).
    2: { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
    apply (unique_unit_eth_root_coprime p q e x (powm g d' (p * q)));
      [exact Hp | exact Hq | exact Hneq | lia | exact Hgcd | exact Hxcop | |].
    - unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
      apply Z.coprime_pow_l; [lia | exact Hyg].
    - rewrite Hpow.
      rewrite (proj2 (powm_mul_inv_semiprime p q e d' g
                        Hp Hq Hneq He Hdlo Hinv Hyg)).
      rewrite Z.mod_small by exact Hg_red. reflexivity. }
  assert (Hdlog : dlog_search g x (p * q) 0%nat
                    (Z.to_nat (lambda_semiprime p q)) = Some d').
  { rewrite (dlog_search_mod g x (p * q) 0%nat
               (Z.to_nat (lambda_semiprime p q)) ltac:(lia)).
    rewrite Hxg.
    apply dlog_search_of_power_order; [exact HN | exact Hor | lia]. }
  pose proof (ed_inv_M_pos e d' (lambda_semiprime p q) He Hdlo ltac:(lia) Hinv)
    as HMpos.
  pose proof (ed_inv_divides_lam e d' (lambda_semiprime p q) ltac:(lia) Hinv)
    as Hdiv.
  pose proof (lambda_odd_primes_even p q Hp Hq Hp2 Hq2) as Hevlam.
  pose proof (divide_even_even (lambda_semiprime p q) (e * d' - 1)
                Hevlam Hdiv) as HevM.
  destruct (miller_search_hits_semiprime p q (e * d' - 1)
              Hp Hq Hneq Hp2 Hq2 HMpos HevM)
    as [a [f [Hs [_ Hf]]]].
  exists d', a, f.
  split; [exact Hdlog|].
  split; [lia|].
  split; [exact Hinv|].
  split; [exact Hs | exact Hf].
Qed.

Theorem residual_solver_reduced_constructs_factor_semiprime :
  forall p q g (Solve : residual_solver_reduced (p * q) (lambda_semiprime p q)),
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p <> 2 ->
    q <> 2 ->
    0 <= g < p * q ->
    Z.coprime g (p * q) ->
    is_order (p * q) g (lambda_semiprime p q) ->
    exists f, Problem_Factor (p * q) f.
Proof.
  intros p q g Solve Hp Hq Hneq Hp2 Hq2 Hrng Hcop Hor.
  destruct (Solve g Hrng Hcop) as [xe Hleaf].
  destruct xe as [x e].
  cbn in Hleaf.
  destruct (residual_leaf_order_lambda_extracts_and_factors
              p q g x e Hp Hq Hneq Hp2 Hq2 Hor Hcop Hleaf)
    as [_ [_ [f [_ [_ [_ [_ Hf]]]]]]].
  exists f. exact Hf.
Qed.
