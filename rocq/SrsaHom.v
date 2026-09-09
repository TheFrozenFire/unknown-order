From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import SrsaResidualGRA.
Require Import SrsaModCbrt.
Require Import SrsaInverter.
Require Import SrsaVaryingE.
Require Import SrsaRootPoly.
Require Import SrsaExtractD.

Open Scope Z_scope.

(** * Homomorphic residual solvers, and annihilator-[e] Strong RSA

    The trapdoor map is a group homomorphism on units.  A mixed
    cube-root / 7th-root table is not.  Homomorphic residual
    solvers are residual solvers, so they factor on this pin by
    [residual_solver_reduced_constructs_factor_pin].  A Strong-RSA
    solver whose output satisfies [λ | e − 1] Millers from [e − 1];
    residual leaves are outside that class.  Not
    [residual_solver_constructs_factor_open_named].
    Not [strong_rsa_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/242], [cas/243]. *)

(** ** Homomorphism of the [x]-map

    Not [residual_solver_constructs_factor_open_named]. *)

Lemma pin_mul_mod_range :
  forall y1 y2, 0 <= (y1 * y2) mod pin_N < pin_N.
Proof. intros. apply Z.mod_pos_bound. lia. Qed.

Lemma pin_mul_mod_coprime :
  forall y1 y2,
    Z.coprime y1 pin_N ->
    Z.coprime y2 pin_N ->
    Z.coprime ((y1 * y2) mod pin_N) pin_N.
Proof.
  intros y1 y2 H1 H2.
  unfold Z.coprime. rewrite Z.gcd_mod_l.
  apply Z.coprime_mul_l; [exact H1 | exact H2].
Qed.

Definition residual_x_homomorphic
    (Solve : residual_solver_reduced pin_N pin_lam) : Prop :=
  forall y1 y2 (H1 : 0 <= y1 < pin_N) (C1 : Z.coprime y1 pin_N)
         (H2 : 0 <= y2 < pin_N) (C2 : Z.coprime y2 pin_N),
    fst (proj1_sig
           (Solve ((y1 * y2) mod pin_N)
                  (pin_mul_mod_range y1 y2)
                  (pin_mul_mod_coprime y1 y2 C1 C2)))
      mod pin_N
    = (fst (proj1_sig (Solve y1 H1 C1)) *
       fst (proj1_sig (Solve y2 H2 C2))) mod pin_N.

Theorem pin_trapdoor_solver_x_homomorphic :
  residual_x_homomorphic pin_trapdoor_residual_solver.
Proof.
  intros y1 y2 H1 C1 H2 C2.
  cbn.
  rewrite powm_mod_base by lia.
  rewrite powm_mul_l_mod by lia.
  rewrite Z.mod_mod by lia.
  reflexivity.
Qed.

(** The hom hypothesis is unused after P5: every reduced residual
    solver on this pin already factors.  The name is a class
    inclusion, not a homomorphic reduction. *)
Theorem residual_x_homomorphic_constructs_factor :
  forall Solve : residual_solver_reduced pin_N pin_lam,
    residual_x_homomorphic Solve ->
    exists f, Problem_Factor pin_N f.
Proof.
  intros Solve _Hhom.
  exact (residual_solver_reduced_constructs_factor_pin Solve).
Qed.

(** ** Reduced-units inverter on this pin uses [pin_lam]

    Goes through [inverter_as_residual], which writes [pin_lam]
    into a residual solver.  [rsa_inverter_extracts_factor_open_named]
    is [forall N e Inv] with no [λ].  Uniqueness of unit [e]-th
    roots needs [gcd(e,λ)=1].  Rabin [e=2] is
    [rabin_oracle_nonassociate_factors].
    Not [rsa_inverter_extracts_factor_open_named].
    Not [rsa_inverter_constructs_factor_open_named]. *)

Theorem rsa_inverter_reduced_units_constructs_factor_pin :
  forall Inv : rsa_inverter_reduced_units pin_N pin_e,
    exists f, Problem_Factor pin_N f.
Proof.
  intros Inv.
  apply residual_solver_reduced_constructs_factor_pin.
  exact (inverter_as_residual Inv).
Qed.

(** ** Strong-RSA solver with [λ | e − 1] Millers from [e − 1]

    Inhabitant: [λ+1].  Residual leaves exclude this class.
    [strong_rsa_solver_extracts_factor_open_named] has no [λ] in
    the type; [λ+1] inhabits it without gcd-splitting.
    Do not prove [~ forall Solve, exists f].
    Not [strong_rsa_solver_constructs_factor_open_named].
    Not [strong_rsa_solver_extracts_factor_open_named]. *)

Definition strong_rsa_solver_annihilator_e
    (Solve : strong_rsa_solver_units pin_N) : Prop :=
  forall y Hrng Hy,
    Z.divide pin_lam (snd (proj1_sig (Solve y Hrng Hy)) - 1).

Theorem strong_rsa_solver_annihilator_e_constructs_factor :
  forall Solve : strong_rsa_solver_units pin_N,
    strong_rsa_solver_annihilator_e Solve ->
    exists f, Problem_Factor pin_N f.
Proof.
  intros Solve Hann.
  destruct (Solve pin_g pin_g_range pin_g_coprime) as [xe Hsrsa] eqn:HS.
  destruct xe as [x e].
  cbn in Hsrsa.
  pose proof (Hann pin_g pin_g_range pin_g_coprime) as Hdiv.
  rewrite HS in Hdiv. cbn in Hdiv.
  pose proof (proj1 Hsrsa) as He.
  assert (Hpos : 0 < e - 1) by lia.
  destruct (pin_miller_from_lambda_multiple (e - 1) Hpos Hdiv) as [_ Hf].
  eexists. exact Hf.
Qed.

Theorem pin_lambda_strong_solver_annihilator_e :
  strong_rsa_solver_annihilator_e pin_lambda_strong_solver.
Proof.
  intros y Hrng Hy. cbn. exists 1. lia.
Qed.

Theorem pin_lambda_strong_solver_millers_from_e_minus_1 :
  exists f, Problem_Factor pin_N f.
Proof.
  apply (strong_rsa_solver_annihilator_e_constructs_factor
           pin_lambda_strong_solver).
  apply pin_lambda_strong_solver_annihilator_e.
Qed.

Theorem residual_leaf_not_annihilator_e :
  forall y x e,
    srsa_residual_leaf pin_N pin_lam y x e ->
    ~ Z.divide pin_lam (e - 1).
Proof.
  intros y x e [_ [_ [_ [_ Hnd]]]]. exact Hnd.
Qed.

Theorem residual_solver_not_annihilator_e :
  forall (Solve : residual_solver_reduced pin_N pin_lam) y Hrng Hy,
    ~ Z.divide pin_lam (snd (proj1_sig (Solve y Hrng Hy)) - 1).
Proof.
  intros Solve y Hrng Hy.
  destruct (Solve y Hrng Hy) as [[x e] Hleaf].
  cbn. apply (residual_leaf_not_annihilator_e y x e). exact Hleaf.
Qed.
