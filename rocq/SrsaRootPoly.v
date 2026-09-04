From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
Import ListNotations.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.ZPoly.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import Order.

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
    and differ as polynomials.  Any polynomial of degree [≤ d_q]
    that inverts every unit has a coefficient whose [gcd] with [N]
    is a proper factor: on [𝔽_q*] minus residue [p] it must match
    [X^{d_q}], and [d_q < q−2] so the roots bound applies.
    Neither is a proof of
    [residual_solver_constructs_factor_open_named]: the TM wrote
    the factors into the coefficients, or [d] into the degree.
    Cross-confirmed by [cas/164] and [cas/165]. *)

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

(** ** Short [e]-th-root polynomials: a coefficient splits [N]

    [d_q < q−2], so [deg P ≤ d_q] is strictly below the number of
    residues in [𝔽_q*] that are units of [Z/NZ] (all of [1..q−1]
    except [p]).  An all-units root map must match [X^{d_q}] on
    those residues, hence [q] divides [P − X^{d_q}].  If the other
    coefficients are also [0] mod [p], the leftover monomial
    [c X^{d_q}] is [c X] on [𝔽_p*] and cannot cube-invert both
    [1] and [2].  Cross-confirmed by [cas/165]. *)

Lemma unique_eth_root_mod_prime :
  forall r e d x z,
    Z.prime r ->
    0 <= e ->
    0 <= d ->
    (e * d) mod (r - 1) = 1 ->
    Z.coprime x r ->
    Z.coprime z r ->
    powm x e r = powm z e r ->
    x mod r = z mod r.
Proof.
  intros r e d x z Hp He Hd Hinv Hx Hz Heq.
  rewrite <- (local_eth_root r d e x);
    [| exact Hp | exact Hx | exact Hd | exact He |].
  2: { rewrite (Z.mul_comm d e). exact Hinv. }
  rewrite <- (local_eth_root r d e z);
    [| exact Hp | exact Hz | exact Hd | exact He |].
  2: { rewrite (Z.mul_comm d e). exact Hinv. }
  rewrite Heq. reflexivity.
Qed.

Definition pin_Fq_units_of_N : list Z :=
  filter (fun a => negb (a =? pin_p)) (units_mod_prime pin_q).

Lemma pin_Fq_units_of_N_length :
  length pin_Fq_units_of_N = 15%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma pairwise_distinct_mod_filter :
  forall r f rs,
    pairwise_distinct_mod r rs ->
    pairwise_distinct_mod r (filter f rs).
Proof.
  intros r f rs.
  induction rs as [|a rest IH]; intros Hdist; simpl.
  - exact I.
  - destruct Hdist as [Hfa Hrest].
    destruct (f a) eqn:Hf.
    + split.
      * apply Forall_forall. intros b Hb.
        apply filter_In in Hb. destruct Hb as [Hin _].
        rewrite Forall_forall in Hfa. apply Hfa. exact Hin.
      * apply IH. exact Hrest.
    + apply IH. exact Hrest.
Qed.

Lemma pin_Fq_units_of_N_distinct :
  pairwise_distinct_mod pin_q pin_Fq_units_of_N.
Proof.
  unfold pin_Fq_units_of_N.
  apply pairwise_distinct_mod_filter, units_mod_prime_distinct, pin_q_prime.
Qed.

Lemma pin_Fq_units_of_N_coprime :
  forall a, In a pin_Fq_units_of_N -> Z.coprime a pin_N.
Proof.
  intros a Hin.
  unfold pin_Fq_units_of_N in Hin.
  apply filter_In in Hin. destruct Hin as [Hin Hq].
  apply negb_true_iff, Z.eqb_neq in Hq.
  pose proof (units_mod_prime_In pin_q a ltac:(lia) Hin) as Hb.
  apply (proj2 (coprime_semiprime pin_p pin_q a
                   pin_p_prime pin_q_prime pin_p_neq_q)).
  split.
  - rewrite coprime_comm. apply Z.coprime_prime_l_iff; [apply pin_p_prime|].
    intros [k Hk]. nia.
  - rewrite coprime_comm. apply Z.coprime_prime_l_iff; [apply pin_q_prime|].
    intros [k Hk]. nia.
Qed.

Lemma pin_inv3_q_lt_window :
  (Z.to_nat pin_inv3_q < 15)%nat.
Proof. vm_compute. lia. Qed.

Lemma nth_poly_sub :
  forall a b i,
    nth i (poly_sub a b) 0 = nth i a 0 - nth i b 0.
Proof.
  intros a b i. unfold poly_sub.
  rewrite nth_poly_add, nth_map_mul. lia.
Qed.

Lemma poly_degree_sub_le :
  forall a b,
    (poly_degree (poly_sub a b)
       <= Nat.max (poly_degree a) (poly_degree b))%nat.
Proof.
  intros a b. unfold poly_sub.
  pose proof (poly_degree_add_le a (map_mul (-1) b)) as Hadd.
  pose proof (poly_degree_map_mul_le (-1) b) as Hmap.
  lia.
Qed.

Lemma mod_product_r :
  forall a p q, 0 < p -> 0 < q -> (a mod (p * q)) mod q = a mod q.
Proof.
  intros a p q Hp Hq.
  apply mods_eq_iff_divides; [lia|].
  apply Z.divide_trans with (p * q).
  - exists p. ring.
  - apply Z.mod_divide; [nia|].
    rewrite Zminus_mod, Z.mod_mod, Z.sub_diag, Z.mod_0_l by nia.
    reflexivity.
Qed.

Lemma mod_product_l :
  forall a p q, 0 < p -> 0 < q -> (a mod (p * q)) mod p = a mod p.
Proof.
  intros a p q Hp Hq. rewrite (Z.mul_comm p q). apply mod_product_r; lia.
Qed.

Lemma short_root_local_mod_q :
  forall P y,
    Z.coprime y pin_N ->
    powm (poly_eval P y) pin_e pin_N = y mod pin_N ->
    poly_eval P y mod pin_q = powm y pin_inv3_q pin_q.
Proof.
  intros P y Hcop Hinv.
  pose proof pin_q_prime as Hq.
  pose proof pin_p_prime as Hp.
  pose proof (Z.prime_ge_2 _ Hq). pose proof (Z.prime_ge_2 _ Hp).
  apply coprime_semiprime in Hcop;
    [|exact Hp|exact Hq|apply pin_p_neq_q].
  destruct Hcop as [_ Hcopq].
  assert (Hred : powm (poly_eval P y) pin_e pin_q = y mod pin_q).
  { unfold powm in Hinv |- *.
    rewrite <- (mod_product_r (poly_eval P y ^ pin_e) pin_p pin_q) by lia.
    rewrite Hinv.
    apply mod_product_r; lia. }
  assert (Hloc : powm (powm y pin_inv3_q pin_q) pin_e pin_q = y mod pin_q).
  { apply local_eth_root; [exact Hq | exact Hcopq | lia | lia |].
    apply (proj2 pin_inv3_local). }
  assert (Hxcop : Z.coprime (poly_eval P y) pin_q).
  { apply (powm_unit_is_coprime (poly_eval P y) pin_e pin_q); [lia | lia |].
    rewrite Hred. rewrite Z.gcd_mod_l. exact Hcopq. }
  assert (Hzcop : Z.coprime (powm y pin_inv3_q pin_q) pin_q).
  { unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
    apply Z.coprime_pow_l; [lia | exact Hcopq]. }
  transitivity (powm y pin_inv3_q pin_q mod pin_q).
  - apply (unique_eth_root_mod_prime pin_q pin_e pin_inv3_q
             (poly_eval P y) (powm y pin_inv3_q pin_q)).
    -- apply pin_q_prime.
    -- lia.
    -- lia.
    -- apply (proj2 pin_inv3_local).
    -- exact Hxcop.
    -- exact Hzcop.
    -- rewrite Hred, Hloc. reflexivity.
  - unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma short_root_diff_vanishes :
  forall P,
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    Forall (fun a => (pin_q | poly_eval
      (poly_sub P (poly_Xn (Z.to_nat pin_inv3_q))) a))
      pin_Fq_units_of_N.
Proof.
  intros P Hall.
  apply Forall_forall. intros a Hin.
  pose proof (pin_Fq_units_of_N_coprime a Hin) as Hcop.
  pose proof (Hall a Hcop) as Hinv.
  pose proof (short_root_local_mod_q P a Hcop Hinv) as Hloc.
  unfold poly_sub.
  rewrite poly_eval_add, poly_eval_map_mul, poly_eval_Xn, Z2Nat.id by lia.
  replace (poly_eval P a + -1 * a ^ pin_inv3_q)
    with (poly_eval P a - a ^ pin_inv3_q) by ring.
  apply Z.mod_divide; [lia|].
  rewrite Zminus_mod, Hloc.
  unfold powm. rewrite Z.sub_diag, Z.mod_0_l by lia. reflexivity.
Qed.

Lemma short_root_q_divides_diff :
  forall P,
    (poly_degree P <= Z.to_nat pin_inv3_q)%nat ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    forall i, (pin_q | nth i (poly_sub P (poly_Xn (Z.to_nat pin_inv3_q))) 0).
Proof.
  intros P Hdeg Hall i.
  apply (poly_prime_roots_divides pin_q pin_Fq_units_of_N
           (poly_sub P (poly_Xn (Z.to_nat pin_inv3_q)))
           pin_q_prime pin_Fq_units_of_N_distinct).
  - pose proof (poly_degree_sub_le P (poly_Xn (Z.to_nat pin_inv3_q))) as Hs.
    rewrite poly_degree_Xn in Hs.
    rewrite pin_Fq_units_of_N_length.
    lia.
  - apply short_root_diff_vanishes. exact Hall.
Qed.

Lemma poly_eval_all_div :
  forall P y M,
    0 < M ->
    (forall i, (M | nth i P 0)) ->
    (M | poly_eval P y).
Proof.
  intros P y M HM Hall.
  induction P as [|c rest IH]; simpl.
  - apply Z.divide_0_r.
  - apply Z.divide_add_r.
    + apply (Hall 0%nat).
    + apply Z.divide_mul_r, IH. intros i. apply (Hall (S i)).
Qed.

Lemma poly_eval_single_support :
  forall P n y M,
    0 < M ->
    (forall i, i <> n -> (M | nth i P 0)) ->
    (M | poly_eval P y - nth n P 0 * y ^ Z.of_nat n).
Proof.
  intros P n y M HM Hall.
  revert n Hall.
  induction P as [|c rest IH]; intros n Hall.
  - replace (poly_eval [] y - nth n [] 0 * y ^ Z.of_nat n) with 0
      by (destruct n; simpl; ring).
    apply Z.divide_0_r.
  - destruct n as [|n].
    + simpl.
      replace (c + y * poly_eval rest y - c * 1)
        with (y * poly_eval rest y) by ring.
      apply Z.divide_mul_r, (poly_eval_all_div rest y M HM).
      intros i. apply (Hall (S i)). discriminate.
    + rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      change (poly_eval (c :: rest) y)
        with (c + y * poly_eval rest y).
      change (nth (S n) (c :: rest) 0) with (nth n rest 0).
      replace (c + y * poly_eval rest y
                 - nth n rest 0 * (y * y ^ Z.of_nat n))
        with (c + y * (poly_eval rest y
                         - nth n rest 0 * y ^ Z.of_nat n)) by ring.
      apply Z.divide_add_r.
      * apply (Hall 0%nat). discriminate.
      * apply Z.divide_mul_r, IH. intros i Hi. apply (Hall (S i)).
        intros Heq. apply Hi. congruence.
Qed.

Lemma pin_two_pow_db_mod_p :
  powm 2 pin_inv3_q pin_p = 2 mod pin_p.
Proof.
  replace pin_inv3_q with (pin_p - 1 + 1) by lia.
  rewrite powm_add_r by lia.
  rewrite fermat_coprime; [| apply pin_p_prime | vm_compute; reflexivity].
  rewrite powm_1_r by lia.
  rewrite Z.mul_1_l, Z.mod_mod by lia. reflexivity.
Qed.

Lemma gcd_q_not_p :
  forall p q a,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    (q | a) ->
    ~ (p | a) ->
    Z.gcd a (p * q) = q.
Proof.
  intros p q a Hp Hq Hneq Hqa Hnp.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  destruct Hqa as [k Hk].
  rewrite Hk.
  rewrite (Z.gcd_mul_mono_r k p q), Z.abs_eq by lia.
  assert (Hkp : Z.gcd k p = 1).
  { pose proof (Z.gcd_divide_l k p) as Hkl.
    assert (Hmul : (Z.gcd k p | k * q)) by (apply Z.divide_mul_l; exact Hkl).
    assert (Hgcd : (Z.gcd k p | Z.gcd (k * q) p)).
    { apply Z.gcd_greatest; [exact Hmul | apply Z.gcd_divide_r]. }
    rewrite <- Hk in Hgcd.
    assert (Hap : Z.gcd a p = 1).
    { rewrite Z.gcd_comm. apply Z.coprime_prime_l_iff; [exact Hp | exact Hnp]. }
    rewrite Hap in Hgcd. apply Z.divide_1_r in Hgcd.
    pose proof (Z.gcd_nonneg k p). lia. }
  rewrite Hkp. lia.
Qed.

Lemma powm_div_cong :
  forall a b e N,
    0 < N ->
    0 <= e ->
    (N | a - b) ->
    powm a e N = powm b e N.
Proof.
  intros a b e N HN He Hdiv.
  unfold powm.
  rewrite <- Z.mod_pow_l by lia.
  rewrite (proj2 (mods_eq_iff_divides a b N HN) Hdiv).
  rewrite Z.mod_pow_l by lia. reflexivity.
Qed.

Lemma finite_support_cases :
  forall (bound n : nat) P M,
    (exists i, (i <= bound)%nat /\ i <> n /\ ~ (M | nth i P 0)) \/
    (forall i, (i <= bound)%nat -> i <> n -> (M | nth i P 0)).
Proof.
  intros bound n P M.
  induction bound as [|b IH].
  - destruct (Nat.eq_dec 0 n) as [Heq | Hne].
    + right. intros i Hi Hne. lia.
    + destruct (Zdivide_dec M (nth 0%nat P 0)) as [Hd | Hnd].
      * right. intros i Hi Hnei. assert (i = 0)%nat by lia. subst. exact Hd.
      * left. exists 0%nat. split; [lia | split; [exact Hne | exact Hnd]].
  - destruct IH as [Hex | Hall].
    + left. destruct Hex as [i [Hle [Hnei Hnd]]].
      exists i. split; [lia | split; [exact Hnei | exact Hnd]].
    + destruct (Nat.eq_dec (S b) n) as [Heq | Hne].
      * right. intros i Hi Hnei. destruct (Nat.eq_dec i (S b)); [lia|].
        apply Hall; lia.
      * destruct (Zdivide_dec M (nth (S b) P 0)) as [Hd | Hnd].
        -- right. intros i Hi Hnei.
           destruct (Nat.eq_dec i (S b)); [subst; exact Hd | apply Hall; lia].
        -- left. exists (S b). split; [lia | split; [exact Hne | exact Hnd]].
Qed.

Theorem short_root_poly_some_coeff_splits :
  forall P,
    (poly_degree P <= Z.to_nat pin_inv3_q)%nat ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    exists i, 1 < Z.gcd (nth i P 0) pin_N < pin_N.
Proof.
  intros P Hdeg Hall.
  pose proof (short_root_q_divides_diff P Hdeg Hall) as Hqdiv.
  destruct (finite_support_cases (Z.to_nat pin_inv3_q)
              (Z.to_nat pin_inv3_q) P pin_p) as [Hex | Hallp].
  - destruct Hex as [i [_ [Hne Hnp]]].
    exists i.
    pose proof (Hqdiv i) as HqQ.
    rewrite nth_poly_sub, nth_Xn in HqQ.
    destruct (Nat.eq_dec i (Z.to_nat pin_inv3_q)); [lia|].
    replace (nth i P 0 - 0) with (nth i P 0) in HqQ by lia.
    assert (Hg : Z.gcd (nth i P 0) pin_N = pin_q).
    { change pin_N with (pin_p * pin_q).
      apply (gcd_q_not_p pin_p pin_q (nth i P 0));
        [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q
         | exact HqQ | exact Hnp]. }
    rewrite Hg. split; lia.
  - set (c := nth (Z.to_nat pin_inv3_q) P 0).
    assert (HNdiv : forall i, i <> Z.to_nat pin_inv3_q ->
                      (pin_N | nth i P 0)).
    { intros i Hne.
      destruct (Nat.le_gt_cases i (Z.to_nat pin_inv3_q)) as [Hle | Hgt].
      - pose proof (Hqdiv i) as HqQ.
        rewrite nth_poly_sub, nth_Xn in HqQ.
        destruct (Nat.eq_dec i (Z.to_nat pin_inv3_q)); [lia|].
        replace (nth i P 0 - 0) with (nth i P 0) in HqQ by lia.
        apply divide_by_coprime_product.
        + apply prime_coprime_distinct;
            [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q].
        + apply Hallp; [exact Hle | exact Hne].
        + exact HqQ.
      - rewrite (poly_nth_above P i); [apply Z.divide_0_r | lia]. }
    assert (HP1 : powm (poly_eval P 1) pin_e pin_N = 1).
    { rewrite Hall by (vm_compute; reflexivity). vm_compute. reflexivity. }
    assert (HP2 : powm (poly_eval P 2) pin_e pin_N = 2).
    { rewrite Hall by (vm_compute; reflexivity). vm_compute. reflexivity. }
    pose proof (poly_eval_single_support P (Z.to_nat pin_inv3_q) 1 pin_N
                  ltac:(lia) HNdiv) as He1.
    pose proof (poly_eval_single_support P (Z.to_nat pin_inv3_q) 2 pin_N
                  ltac:(lia) HNdiv) as He2.
    rewrite Z2Nat.id in He1, He2 by lia.
    fold c in He1, He2.
    replace (1 ^ pin_inv3_q) with 1 in He1 by (vm_compute; reflexivity).
    replace (c * 1) with c in He1 by ring.
    assert (Hc : powm c pin_e pin_N = 1).
    { rewrite <- HP1. apply powm_div_cong; [lia | lia |].
      apply (proj1 (Z.divide_opp_r pin_N (c - poly_eval P 1))).
      replace (- (c - poly_eval P 1)) with (poly_eval P 1 - c) by ring.
      exact He1. }
    assert (H2c : powm (c * 2 ^ pin_inv3_q) pin_e pin_N = 2).
    { transitivity (powm (poly_eval P 2) pin_e pin_N).
      - apply powm_div_cong; [lia | lia |].
        apply (proj1 (Z.divide_opp_r pin_N
                        (c * 2 ^ pin_inv3_q - poly_eval P 2))).
        replace (- (c * 2 ^ pin_inv3_q - poly_eval P 2))
          with (poly_eval P 2 - c * 2 ^ pin_inv3_q) by ring.
        exact He2.
      - exact HP2. }
    assert (Hcp : powm c pin_e pin_p = 1).
    { unfold powm in Hc |- *.
      rewrite <- (mod_product_l (c ^ pin_e) pin_p pin_q) by lia.
      rewrite Hc. vm_compute. reflexivity. }
    assert (H2p : powm (c * 2 ^ pin_inv3_q) pin_e pin_p = 2 mod pin_p).
    { unfold powm in H2c |- *.
      rewrite <- (mod_product_l ((c * 2 ^ pin_inv3_q) ^ pin_e)
                   pin_p pin_q) by lia.
      rewrite H2c. vm_compute. reflexivity. }
    assert (Hcong : (c * 2 ^ pin_inv3_q) mod pin_p = (c * 2) mod pin_p).
    { apply (proj2 (mods_eq_iff_divides (c * 2 ^ pin_inv3_q) (c * 2) pin_p
                      ltac:(lia))).
      replace (c * 2 ^ pin_inv3_q - c * 2)
        with (c * (2 ^ pin_inv3_q - 2)) by ring.
      apply Z.divide_mul_r, Z.mod_divide; [lia|].
      vm_compute. reflexivity. }
    assert (H8 : powm (c * 2) pin_e pin_p = 2 mod pin_p).
    { unfold powm in H2p |- *.
      rewrite <- Z.mod_pow_l by lia.
      rewrite <- Hcong.
      rewrite Z.mod_pow_l by lia. exact H2p. }
    unfold powm in H8, Hcp.
    rewrite Z.pow_mul_l in H8.
    replace (2 ^ pin_e) with 8 in H8 by (vm_compute; reflexivity).
    rewrite Z.mul_mod in H8 by lia.
    rewrite Hcp in H8.
    replace (8 mod pin_p) with 8 in H8 by (vm_compute; reflexivity).
    rewrite Z.mul_1_l in H8.
    vm_compute in H8. discriminate.
Qed.

Theorem pin_crt_root_poly_is_short :
  (poly_degree pin_crt_root_poly <= Z.to_nat pin_inv3_q)%nat.
Proof. rewrite pin_crt_binomial_degree. lia. Qed.

Theorem pin_crt_root_poly_short_splits :
  exists i, 1 < Z.gcd (nth i pin_crt_root_poly 0) pin_N < pin_N.
Proof.
  apply short_root_poly_some_coeff_splits.
  - apply pin_crt_root_poly_is_short.
  - apply pin_crt_binomial_inverts_units.
Qed.
