From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import BinForms.
Require Import ClassGroupWall.
Require Import Presentation.
Require Import PowersOfTau.

Open Scope Z_scope.

(** * The same [τ]-string on a presentation

    [potP P g τ i = Pexp P g (τ^i)].  On [rsa_presentation] this
    is [pot].  On [cl_presentation] it is [bqf_exp].  Class-group
    inversion is public ([bqf_inv]); the public annihilator is
    [Some 2], not a Carmichael [λ].  Toxic waste is only the
    exponent [τ].  There is no factorization trapdoor to walk
    the string.

    Contribute at slot [0] is the identity on any presentation
    whose [Pexp _ 1] is the element.  The general Cl contribute
    identity [f^{ρ^i} = g^{(τρ)^i}] needs associativity of
    Dirichlet composition ([compose_assoc_named]); it is not
    taken as a hypothesis here.  The RSA instance is the theorem
    [pot_contribute_multiplies_tau].

    Cross-confirmed by [cas/92_pot_cl.gp]. *)

Definition potP (P : Presentation) (g : Pcar P) (tau i : nat) : Pcar P :=
  Pexp P g (Nat.pow tau i).

Definition potP_contribute (P : Presentation) (elem : Pcar P)
    (rho i : nat) : Pcar P :=
  Pexp P elem (Nat.pow rho i).

Theorem potP_rsa_is_pot :
  forall N g tau i,
    1 < N ->
    potP (rsa_presentation N) g tau i =
      pot N g (Z.of_nat tau) (Z.of_nat i).
Proof.
  intros N g tau i Hn.
  unfold potP, pot, rsa_presentation. simpl.
  rewrite Nat2Z.inj_pow.
  reflexivity.
Qed.

Theorem potP_cl_is_bqf_exp :
  forall D g tau i,
    potP (cl_presentation D) g tau i =
      bqf_exp D g (Nat.pow tau i).
Proof. intros. reflexivity. Qed.

Theorem potP_rsa_at_zero :
  forall N g tau,
    1 < N ->
    potP (rsa_presentation N) g tau 0%nat = g mod N.
Proof.
  intros N g tau Hn.
  rewrite potP_rsa_is_pot by exact Hn.
  apply pot_at_zero. lia.
Qed.

Theorem potP_rsa_at_one :
  forall N g tau,
    1 < N ->
    potP (rsa_presentation N) g tau 1%nat = powm g (Z.of_nat tau) N.
Proof.
  intros N g tau Hn.
  rewrite potP_rsa_is_pot by exact Hn.
  rewrite pot_at_one by lia.
  reflexivity.
Qed.

Theorem potP_cl_at_zero :
  forall D g tau,
    iq_disc D ->
    of_disc g D ->
    potP (cl_presentation D) g tau 0%nat = g.
Proof.
  intros D g tau Hiq Hof.
  unfold potP, cl_presentation. simpl.
  apply bqf_exp_1; assumption.
Qed.

Theorem potP_cl_at_one :
  forall D g tau,
    potP (cl_presentation D) g tau 1%nat = bqf_exp D g tau.
Proof.
  intros D g tau.
  unfold potP. rewrite Nat.pow_1_r. reflexivity.
Qed.

Theorem potP_rsa_contribute_multiplies :
  forall N g tau rho i,
    1 < N ->
    potP_contribute (rsa_presentation N)
      (potP (rsa_presentation N) g tau i) rho i =
      potP (rsa_presentation N) g (tau * rho)%nat i.
Proof.
  intros N g tau rho i Hn.
  unfold potP_contribute.
  rewrite (potP_rsa_is_pot N g tau i Hn).
  unfold potP, rsa_presentation. simpl.
  rewrite Nat2Z.inj_pow.
  rewrite (Nat2Z.inj_pow (tau * rho) i).
  rewrite Nat2Z.inj_mul.
  change (powm g ((Z.of_nat tau * Z.of_nat rho) ^ Z.of_nat i) N)
    with (pot N g (Z.of_nat tau * Z.of_nat rho) (Z.of_nat i)).
  rewrite <- (pot_contribute_multiplies_tau N g (Z.of_nat tau)
               (Z.of_nat rho) (Z.of_nat i));
    try (lia || apply Nat2Z.is_nonneg).
  unfold pot_contribute.
  reflexivity.
Qed.

Theorem potP_rsa_succ :
  forall N g tau i,
    1 < N ->
    potP (rsa_presentation N) g tau (S i) =
      powm (potP (rsa_presentation N) g tau i) (Z.of_nat tau) N.
Proof.
  intros N g tau i Hn.
  rewrite !potP_rsa_is_pot by exact Hn.
  rewrite Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat i)) with (Z.of_nat i + 1) by lia.
  apply pot_succ_is_tau_power; try (lia || apply Nat2Z.is_nonneg).
Qed.

Theorem pot_cl_no_lambda :
  forall D,
    Pannihilator (cl_presentation D) = Some 2 /\
    Pannihilator (cl_presentation D) <> Some 3.
Proof.
  intros D. split.
  - apply cl_public_annihilator_is_two.
  - intros H. unfold cl_presentation in H. simpl in H. injection H. lia.
Qed.

Theorem pot_cl_inv_is_public :
  forall D f,
    Pinv (cl_presentation D) f = bqf_inv f.
Proof. apply cl_inv_is_bqf_inv. Qed.

Theorem pot_cl_contribute_slot0 :
  forall D elem rho,
    iq_disc D ->
    of_disc elem D ->
    potP_contribute (cl_presentation D) elem rho 0%nat = elem.
Proof.
  intros D elem rho Hiq Hof.
  unfold potP_contribute, cl_presentation. simpl.
  apply bqf_exp_1; assumption.
Qed.

Theorem pot_cl_neg31_at_zero :
  potP (cl_presentation (-31)) form_neg31_ord3 2 0%nat = form_neg31_ord3.
Proof.
  apply potP_cl_at_zero.
  - apply iq_neg31.
  - apply form_neg31_ord3_of_disc.
Qed.

Theorem pot_cl_neg31_at_one :
  potP (cl_presentation (-31)) form_neg31_ord3 2 1%nat = form_neg31_sq.
Proof.
  rewrite potP_cl_at_one.
  apply form_neg31_exp2.
Qed.
