From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import Hardness.
Require Import BinForms.
Require Import Presentation.
Require Import PowersOfTau.

Open Scope Z_scope.

(** * Endomorphisms of [(Z/NZ)*] and of [Cl(Δ)]

    Inversion is public on both carriers we have: Bézout on units,
    [bqf_inv] on forms.  A search for a unit with no inverse is
    empty.  "Groups with infeasible inversion" is therefore not a
    property of RSA-land or of [Cl(Δ)].  The remaining neighbour
    (isogenies / a curve over [Z/NZ]) is
    [Refuse_elliptic_curve_branch].

    The public group endomorphism is [x ↦ x^k].  It is a
    homomorphism.  Using it as "next CRS power" forces [k ≡ τ]
    modulo the order.  That is exponentiation by a public integer,
    not a pairing of two hidden discrete logs.

    Cross-confirmed by [cas/89_endo.gp]. *)

Definition power_endo (N k x : Z) : Z :=
  powm x k N.

Definition infeasible_inversion_search (N a : Z) : Prop :=
  Z.coprime a N /\ forall w, (a * w) mod N <> 1.

Theorem rsa_inverse_is_constructible :
  forall a n,
    1 < n ->
    Z.gcd a n = 1 ->
    exists w, (a * w) mod n = 1.
Proof. apply unit_inverse_exists. Qed.

Theorem cl_inverse_is_constructible :
  forall D f,
    iq_disc D ->
    of_disc f D ->
    Peq (cl_presentation D)
      (Pmul (cl_presentation D) f (Pinv (cl_presentation D) f))
      (Pid (cl_presentation D)).
Proof. apply cl_mul_inv_equiv_id. Qed.

Theorem rsa_gii_search_empty :
  forall N a,
    1 < N ->
    ~ infeasible_inversion_search N a.
Proof.
  intros N a Hn [Hcop Hnone].
  destruct (unit_inverse_exists a N Hn Hcop) as [w Hw].
  apply (Hnone w). exact Hw.
Qed.

Theorem power_endo_hom :
  forall N k x y,
    1 < N ->
    0 <= k ->
    power_endo N k ((x * y) mod N) =
      (power_endo N k x * power_endo N k y) mod N.
Proof.
  intros N k x y Hn Hk.
  unfold power_endo.
  rewrite powm_mod_base by lia.
  unfold powm.
  rewrite Z.pow_mul_l.
  apply Z.mul_mod; lia.
Qed.

Theorem power_endo_on_dlog :
  forall N g a k,
    1 < N ->
    0 <= a ->
    0 <= k ->
    power_endo N k (powm g a N) = powm g (a * k) N.
Proof.
  intros N g a k Hn Ha Hk.
  unfold power_endo.
  rewrite <- powm_mul_r by lia.
  reflexivity.
Qed.

Theorem power_endo_not_product_of_dlogs :
  forall N g a b k ord,
    1 < N ->
    0 <= a ->
    0 <= b ->
    0 <= k ->
    Z.coprime g N ->
    is_order N g ord ->
    power_endo N k (powm g a N) = powm g (a * b) N ->
    (ord | a * (k - b)).
Proof.
  intros N g a b k ord Hn Ha Hb Hk Hcop Hord Heq.
  rewrite power_endo_on_dlog in Heq by lia.
  pose proof (powm_eq_implies_abs_annihilator N g (a * k) (a * b)
                Hn ltac:(nia) ltac:(nia) Hcop Heq) as Hann.
  pose proof (order_divides_annihilator N g ord
                (Z.abs (a * k - a * b))
                Hn (Z.abs_nonneg _) Hord Hann) as Hdiv.
  replace (a * k - a * b) with (a * (k - b)) in Hdiv by ring.
  destruct (Z.le_ge_cases (a * k) (a * b)) as [Hle | Hge].
  - rewrite Z.abs_neq in Hdiv by nia.
    destruct Hdiv as [m Hm]. exists (- m). nia.
  - rewrite Z.abs_eq in Hdiv by nia. exact Hdiv.
Qed.

Theorem power_endo_next_forces_k :
  forall N g tau i k ord,
    1 < N ->
    0 <= tau ->
    0 <= i ->
    0 <= k ->
    Z.coprime g N ->
    is_order N g ord ->
    power_endo N k (pot N g tau i) = pot N g tau (i + 1) ->
    (ord | tau ^ i * (k - tau)).
Proof.
  intros N g tau i k ord Hn Ht Hi Hk Hcop Hord Hnext.
  unfold power_endo, pot in Hnext.
  rewrite Z.add_1_r, Z.pow_succ_r in Hnext by lia.
  rewrite <- powm_mul_r in Hnext by (try apply Z.pow_nonneg; lia).
  rewrite (Z.mul_comm tau) in Hnext.
  pose proof (powm_eq_implies_abs_annihilator N g (tau ^ i * k) (tau ^ i * tau)
                Hn ltac:(nia) ltac:(nia) Hcop Hnext) as Hann.
  pose proof (order_divides_annihilator N g ord
                (Z.abs (tau ^ i * k - tau ^ i * tau))
                Hn (Z.abs_nonneg _) Hord Hann) as Hdiv.
  replace (tau ^ i * k - tau ^ i * tau)
    with (tau ^ i * (k - tau)) in Hdiv by ring.
  destruct (Z.le_ge_cases (tau ^ i * k) (tau ^ i * tau)) as [Hle | Hge].
  - rewrite Z.abs_neq in Hdiv by nia.
    destruct Hdiv as [m Hm]. exists (- m). nia.
  - rewrite Z.abs_eq in Hdiv by nia. exact Hdiv.
Qed.
