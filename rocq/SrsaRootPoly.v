From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.ZPoly.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Two writings of an [e]-th root polynomial on units

    Low-degree nodiv GRA cannot invert every unit
    ([SrsaResidualGRA]).  Once degree escapes that window, two
    polynomials invert every unit on this pin:

    - CRT binomial [c_p X^{d_p} + c_q X^{d_q}]: local inverses of
      residual [e].  Coefficients are [1,0] / [0,1] along the two
      primes, so [gcd(c_p, N)] and [gcd(c_q, N)] are proper factors.
    - Monomial [X^d]: trapdoor exponent.  Coefficients are [0,1],
      which do not split; the *degree* is [d], and [(e,d)] Miller-
      splits ([miller_from_d]).

    They agree as functions on [(Z/NZ)*] (unique unit [e]-th root)
    and differ as polynomials.  Neither is a proof of
    [residual_solver_constructs_factor_open_named]: the TM wrote
    the factors into the coefficients, or [d] into the degree.
    Cross-confirmed by [cas/164]. *)

(** ** Coefficient of a mixed CRT monomial splits *)

Lemma cong_1_mod_p_0_mod_q_gcd :
  forall p q c,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    c mod p = 1 ->
    c mod q = 0 ->
    Z.gcd c (p * q) = q.
Proof.
  intros p q c Hp Hq Hneq Hp1 Hq0.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  assert (Hqdiv : (q | c)) by (apply Z.mod_divide; [lia | exact Hq0]).
  destruct Hqdiv as [k Hk].
  assert (Hcp : Z.gcd c p = 1).
  { rewrite <- Z.gcd_mod_l, Hp1. apply Z.gcd_1_l. }
  rewrite Hk in Hcp |- *.
  rewrite (Z.gcd_mul_mono_r k p q).
  rewrite Z.abs_eq by lia.
  assert (Hkp : Z.gcd k p = 1).
  { pose proof (Z.gcd_divide_l k p) as Hkl.
    assert (Hmul : (Z.gcd k p | k * q)) by (apply Z.divide_mul_l; exact Hkl).
    assert (Hgcd : (Z.gcd k p | Z.gcd (k * q) p)).
    { apply Z.gcd_greatest; [exact Hmul | apply Z.gcd_divide_r]. }
    rewrite Hcp in Hgcd. apply Z.divide_1_r in Hgcd.
    pose proof (Z.gcd_nonneg k p). lia. }
  rewrite Hkp. lia.
Qed.

(** ** CRT binomial *)

Definition crt_binomial (ca da cb db : Z) : list Z :=
  poly_add (map_mul ca (poly_Xn (Z.to_nat da)))
           (map_mul cb (poly_Xn (Z.to_nat db))).

Lemma crt_binomial_eval :
  forall ca da cb db y,
    0 <= da ->
    0 <= db ->
    poly_eval (crt_binomial ca da cb db) y =
      ca * y ^ da + cb * y ^ db.
Proof.
  intros ca da cb db y Hda Hdb.
  unfold crt_binomial.
  rewrite poly_eval_add, !poly_eval_map_mul, !poly_eval_Xn.
  rewrite !Z2Nat.id by lia. reflexivity.
Qed.

Lemma crt_binomial_mod_p :
  forall ca da cb db y p,
    0 <= da ->
    0 <= db ->
    1 < p ->
    ca mod p = 1 ->
    cb mod p = 0 ->
    poly_eval (crt_binomial ca da cb db) y mod p = (y ^ da) mod p.
Proof.
  intros ca da cb db y p Hda Hdb Hp Hca Hcb.
  rewrite crt_binomial_eval by lia.
  apply mods_eq_iff_divides; [lia|].
  replace (ca * y ^ da + cb * y ^ db - y ^ da)
    with ((ca - 1) * y ^ da + cb * y ^ db) by ring.
  apply Z.divide_add_r.
  - apply Z.divide_mul_l. apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Hca, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity.
  - apply Z.divide_mul_l. apply Z.mod_divide; [lia | exact Hcb].
Qed.

Lemma crt_binomial_mod_q :
  forall ca da cb db y q,
    0 <= da ->
    0 <= db ->
    1 < q ->
    ca mod q = 0 ->
    cb mod q = 1 ->
    poly_eval (crt_binomial ca da cb db) y mod q = (y ^ db) mod q.
Proof.
  intros ca da cb db y q Hda Hdb Hq Hca Hcb.
  rewrite crt_binomial_eval by lia.
  apply mods_eq_iff_divides; [lia|].
  replace (ca * y ^ da + cb * y ^ db - y ^ db)
    with (ca * y ^ da + (cb - 1) * y ^ db) by ring.
  apply Z.divide_add_r.
  - apply Z.divide_mul_l. apply Z.mod_divide; [lia | exact Hca].
  - apply Z.divide_mul_l. apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Hcb, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity.
Qed.

Lemma local_eth_root :
  forall p e d y,
    Z.prime p ->
    Z.coprime y p ->
    0 <= e ->
    0 <= d ->
    (e * d) mod (p - 1) = 1 ->
    powm (powm y d p) e p = y mod p.
Proof.
  intros p e d y Hp Hcop He Hd Hinv.
  pose proof (Z.prime_ge_2 p Hp).
  rewrite <- powm_mul_r by lia.
  rewrite (Z.mul_comm d e).
  pose proof (Z.div_mod (e * d) (p - 1) ltac:(lia)) as Hdm.
  rewrite Hinv in Hdm.
  rewrite Hdm.
  assert (Hdivpos : 0 <= (e * d) / (p - 1)).
  { apply Z.div_pos; lia. }
  rewrite powm_add_r; [| lia | apply Z.mul_nonneg_nonneg; [lia | exact Hdivpos] | lia].
  rewrite powm_1_r by lia.
  rewrite powm_mul_r; [| lia | lia | exact Hdivpos].
  rewrite fermat_coprime by assumption.
  rewrite powm_1_pow by lia.
  rewrite Z.mod_1_l by lia.
  rewrite Z.mul_1_l, Z.mod_mod by lia.
  reflexivity.
Qed.

Theorem crt_binomial_inverts_units :
  forall p q e da db ca cb y,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    0 <= e ->
    0 <= da ->
    0 <= db ->
    Z.coprime y (p * q) ->
    (e * da) mod (p - 1) = 1 ->
    (e * db) mod (q - 1) = 1 ->
    ca mod p = 1 ->
    ca mod q = 0 ->
    cb mod p = 0 ->
    cb mod q = 1 ->
    powm (poly_eval (crt_binomial ca da cb db) y) e (p * q) =
      y mod (p * q).
Proof.
  intros p q e da db ca cb y Hp Hq Hneq He Hda Hdb Hcop Hda1 Hdb1 Hcap Hcaq Hcbp Hcbq.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  apply coprime_semiprime in Hcop; [|exact Hp|exact Hq|exact Hneq].
  destruct Hcop as [Hcopp Hcopq].
  unfold powm.
  apply crt_mod_eq; try assumption.
  - change ((poly_eval (crt_binomial ca da cb db) y ^ e) mod p)
      with (powm (poly_eval (crt_binomial ca da cb db) y) e p).
    rewrite <- powm_mod_base by lia.
    rewrite crt_binomial_mod_p by lia.
    change ((y ^ da) mod p) with (powm y da p).
    apply local_eth_root; assumption.
  - change ((poly_eval (crt_binomial ca da cb db) y ^ e) mod q)
      with (powm (poly_eval (crt_binomial ca da cb db) y) e q).
    rewrite <- powm_mod_base by lia.
    rewrite crt_binomial_mod_q by lia.
    change ((y ^ db) mod q) with (powm y db q).
    apply local_eth_root; assumption.
Qed.

(** ** Pin CRT binomial: coefficients split *)

Definition pin_crt_root_poly : list Z :=
  crt_binomial pin_root_ca pin_inv3_p pin_root_cb pin_inv3_q.

Theorem pin_root_ca_mod :
  pin_root_ca mod pin_p = 1 /\ pin_root_ca mod pin_q = 0.
Proof. vm_compute. split; reflexivity. Qed.

Theorem pin_root_cb_mod :
  pin_root_cb mod pin_p = 0 /\ pin_root_cb mod pin_q = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem pin_inv3_local :
  (pin_e * pin_inv3_p) mod (pin_p - 1) = 1 /\
  (pin_e * pin_inv3_q) mod (pin_q - 1) = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem pin_root_ca_splits :
  Z.gcd pin_root_ca pin_N = pin_q /\
  Problem_Factor pin_N (Z.gcd pin_root_ca pin_N).
Proof.
  assert (Hg : Z.gcd pin_root_ca pin_N = pin_q).
  { change pin_N with (pin_p * pin_q).
    apply cong_1_mod_p_0_mod_q_gcd;
      [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q |
       apply (proj1 pin_root_ca_mod) | apply (proj2 pin_root_ca_mod)]. }
  split; [exact Hg|]. rewrite Hg. unfold Problem_Factor.
  split; [lia|]. exists pin_p. reflexivity.
Qed.

Theorem pin_root_cb_splits :
  Z.gcd pin_root_cb pin_N = pin_p /\
  Problem_Factor pin_N (Z.gcd pin_root_cb pin_N).
Proof.
  assert (Hg : Z.gcd pin_root_cb pin_N = pin_p).
  { change pin_N with (pin_q * pin_p).
    apply cong_1_mod_p_0_mod_q_gcd;
      [apply pin_q_prime | apply pin_p_prime | apply not_eq_sym, pin_p_neq_q |
       apply (proj2 pin_root_cb_mod) | apply (proj1 pin_root_cb_mod)]. }
  split; [exact Hg|]. rewrite Hg. unfold Problem_Factor.
  split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem pin_crt_binomial_inverts_units :
  forall y,
    Z.coprime y pin_N ->
    powm (poly_eval pin_crt_root_poly y) pin_e pin_N = y mod pin_N.
Proof.
  intros y Hcop. unfold pin_crt_root_poly.
  apply (crt_binomial_inverts_units pin_p pin_q pin_e pin_inv3_p pin_inv3_q
           pin_root_ca pin_root_cb y).
  - apply pin_p_prime.
  - apply pin_q_prime.
  - apply pin_p_neq_q.
  - lia.
  - lia.
  - lia.
  - exact Hcop.
  - apply (proj1 pin_inv3_local).
  - apply (proj2 pin_inv3_local).
  - apply (proj1 pin_root_ca_mod).
  - apply (proj2 pin_root_ca_mod).
  - apply (proj1 pin_root_cb_mod).
  - apply (proj2 pin_root_cb_mod).
Qed.

Theorem pin_crt_binomial_eval_unit :
  forall y,
    Z.coprime y pin_N ->
    Z.coprime (poly_eval pin_crt_root_poly y) pin_N.
Proof.
  intros y Hcop.
  pose proof (pin_crt_binomial_inverts_units y Hcop) as Hinv.
  pose proof pin_N_gt_1.
  apply (powm_unit_is_coprime (poly_eval pin_crt_root_poly y) pin_e pin_N);
    [lia | lia |].
  rewrite Hinv. rewrite Z.gcd_mod_l. exact Hcop.
Qed.

Lemma pin_ed_minus_1_divides_lam :
  (lambda_semiprime pin_p pin_q | pin_e * pin_d - 1).
Proof.
  rewrite rsa_test_lambda.
  apply Z.mod_divide; [lia|].
  rewrite Zminus_mod, rsa_test_inv, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
  reflexivity.
Qed.

Lemma pin_powm_ed :
  forall x,
    Z.coprime x pin_N ->
    powm (powm x pin_e pin_N) pin_d pin_N = x mod pin_N.
Proof.
  intros x Hx.
  rewrite <- powm_mul_r by lia.
  replace (pin_e * pin_d) with (pin_e * pin_d - 1 + 1) by lia.
  rewrite powm_add_r by lia.
  rewrite powm_1_r by lia.
  rewrite (annihilates_units pin_p pin_q x (pin_e * pin_d - 1));
    [| apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q
     | exact Hx | lia | apply pin_ed_minus_1_divides_lam].
  rewrite Z.mul_1_l, Z.mod_mod by lia. reflexivity.
Qed.

Theorem pin_unique_unit_eth_root :
  forall x z,
    Z.coprime x pin_N ->
    Z.coprime z pin_N ->
    powm x pin_e pin_N = powm z pin_e pin_N ->
    x mod pin_N = z mod pin_N.
Proof.
  intros x z Hx Hz Heq.
  rewrite <- (pin_powm_ed x Hx), <- (pin_powm_ed z Hz).
  rewrite Heq. reflexivity.
Qed.

Theorem pin_crt_binomial_at_y :
  poly_eval pin_crt_root_poly pin_y mod pin_N = pin_x.
Proof.
  apply (pin_unique_unit_eth_root
           (poly_eval pin_crt_root_poly pin_y) pin_x).
  - apply pin_crt_binomial_eval_unit. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - rewrite pin_crt_binomial_inverts_units by (vm_compute; reflexivity).
    rewrite Z.mod_small by lia.
    vm_compute. reflexivity.
Qed.

Theorem pin_crt_binomial_residual :
  srsa_residual_leaf pin_N pin_lam pin_y
    (poly_eval pin_crt_root_poly pin_y mod pin_N) pin_e.
Proof.
  rewrite pin_crt_binomial_at_y. apply srsa_residual_pin.
Qed.

Theorem pin_crt_binomial_degree :
  poly_degree pin_crt_root_poly = Z.to_nat pin_inv3_q.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_crt_binomial_outside_window :
  (Z.to_nat pin_e * poly_degree pin_crt_root_poly
     >= Z.to_nat (pin_p - 1))%nat.
Proof. rewrite pin_crt_binomial_degree. vm_compute. lia. Qed.

Theorem pin_crt_binomial_coeff_da :
  nth (Z.to_nat pin_inv3_p) pin_crt_root_poly 0 = pin_root_ca.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_crt_binomial_coeff_db :
  nth (Z.to_nat pin_inv3_q) pin_crt_root_poly 0 = pin_root_cb.
Proof. vm_compute. reflexivity. Qed.

(** ** Trapdoor monomial [X^d]: degree is [d], coefficients do not split *)

Definition pin_trapdoor_monomial : list Z := poly_Xn (Z.to_nat pin_d).

Theorem pin_trapdoor_monomial_eval :
  forall y,
    poly_eval pin_trapdoor_monomial y = y ^ pin_d.
Proof.
  intros y. unfold pin_trapdoor_monomial.
  rewrite poly_eval_Xn, Z2Nat.id by lia. reflexivity.
Qed.

Theorem pin_trapdoor_ed_inv :
  (pin_e * pin_d) mod pin_lam = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma pin_powm_de :
  forall x,
    Z.coprime x pin_N ->
    powm (powm x pin_d pin_N) pin_e pin_N = x mod pin_N.
Proof.
  intros x Hx.
  rewrite <- powm_mul_r by lia.
  rewrite (Z.mul_comm pin_d pin_e).
  replace (pin_e * pin_d) with (pin_e * pin_d - 1 + 1) by lia.
  rewrite powm_add_r by lia.
  rewrite powm_1_r by lia.
  rewrite (annihilates_units pin_p pin_q x (pin_e * pin_d - 1));
    [| apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q
     | exact Hx | lia | apply pin_ed_minus_1_divides_lam].
  rewrite Z.mul_1_l, Z.mod_mod by lia. reflexivity.
Qed.

Theorem pin_trapdoor_monomial_inverts_units :
  forall y,
    Z.coprime y pin_N ->
    powm (powm y pin_d pin_N) pin_e pin_N = y mod pin_N.
Proof.
  apply pin_powm_de.
Qed.

Theorem pin_trapdoor_monomial_at_y :
  powm pin_y pin_d pin_N = pin_x.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_trapdoor_monomial_degree :
  poly_degree pin_trapdoor_monomial = Z.to_nat pin_d.
Proof. unfold pin_trapdoor_monomial. apply poly_degree_Xn. Qed.

Theorem pin_trapdoor_monomial_leading :
  nth (Z.to_nat pin_d) pin_trapdoor_monomial 0 = 1 /\
  Z.gcd 1 pin_N = 1.
Proof.
  split.
  - unfold pin_trapdoor_monomial. rewrite nth_Xn.
    destruct (Nat.eq_dec (Z.to_nat pin_d) (Z.to_nat pin_d)); [reflexivity | lia].
  - reflexivity.
Qed.

Theorem pin_trapdoor_degree_is_d :
  poly_degree pin_trapdoor_monomial = Z.to_nat pin_d /\
  (pin_e * pin_d) mod pin_lam = 1.
Proof.
  split; [apply pin_trapdoor_monomial_degree | apply pin_trapdoor_ed_inv].
Qed.

Theorem pin_trapdoor_monomial_outside_window :
  (Z.to_nat pin_e * poly_degree pin_trapdoor_monomial
     >= Z.to_nat (pin_p - 1))%nat.
Proof. rewrite pin_trapdoor_monomial_degree. vm_compute. lia. Qed.

(** ** They agree on units and differ as polynomials *)

Theorem pin_root_polys_agree_on_units :
  forall y,
    Z.coprime y pin_N ->
    poly_eval pin_crt_root_poly y mod pin_N = powm y pin_d pin_N.
Proof.
  intros y Hcop.
  assert (Hz : Z.coprime (powm y pin_d pin_N) pin_N).
  { unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
    apply Z.coprime_pow_l; [lia | exact Hcop]. }
  replace (powm y pin_d pin_N) with (powm y pin_d pin_N mod pin_N).
  2: { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
  apply (pin_unique_unit_eth_root
           (poly_eval pin_crt_root_poly y) (powm y pin_d pin_N)).
  - apply pin_crt_binomial_eval_unit. exact Hcop.
  - exact Hz.
  - rewrite (pin_crt_binomial_inverts_units y Hcop).
    rewrite (pin_powm_de y Hcop).
    reflexivity.
Qed.

Theorem pin_crt_binomial_neq_monomial :
  pin_crt_root_poly <> pin_trapdoor_monomial.
Proof.
  intros Heq.
  assert (poly_degree pin_crt_root_poly = poly_degree pin_trapdoor_monomial)
    by (rewrite Heq; reflexivity).
  rewrite pin_crt_binomial_degree, pin_trapdoor_monomial_degree in H.
  vm_compute in H. discriminate.
Qed.

Theorem pin_crt_binomial_inverts_2 :
  Z.coprime 2 pin_N /\
  powm (poly_eval pin_crt_root_poly 2) pin_e pin_N = 2.
Proof.
  split; [vm_compute; reflexivity|].
  rewrite pin_crt_binomial_inverts_units by (vm_compute; reflexivity).
  vm_compute. reflexivity.
Qed.
