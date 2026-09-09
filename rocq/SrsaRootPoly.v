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
Require Import GenericRing.
Require Import TwoPrimary.
Require Import Miller.
Require Import MillerHeight.
Require Import CRTRSA.

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
    and differ as polynomials.  Any all-units invert poly is that
    same trapdoor map ([all_units_root_poly_is_trapdoor_map]).  Any polynomial of degree [≤ d_q]
    that inverts every unit has a coefficient whose [gcd] with [N]
    is a proper factor: on [𝔽_q*] minus residue [p] it must match
    [X^{d_q}], and [d_q < q−2] so the roots bound applies.
    Neither is a proof of
    [residual_solver_constructs_factor_open_named]: the TM wrote
    the factors into the coefficients, or [d] into the degree.
    The window is sharp: no polynomial of degree [< d_q] inverts
    every unit ([q] would divide [−1]).  The same roots bound
    widens the split from [deg ≤ d_q] to [deg < q−2].  A nodiv GRA
    whose degree bound is [≤ d_q] and that inverts every unit
    denotes a short root polynomial, so a coefficient splits.
    An invert-all-units monomial [X^k] is Miller-from-[(e,k)].
    Local inverses CRT to [d] mod [λ].  The missing [𝔽_q*]
    sample is the unit [p+q] ([p+q ≡ p (mod q)]); invert-all-units
    at that lift kills the leftover, so [fold_q ≡ X^{d_q}] as
    polynomials with no extra top-zero hypothesis.  Both Fermat
    folds are the local inverse monomials, and CRT of those
    degrees is [d] mod [λ].  The geometric kernel
    [K = Σ p^j X^{q−2−j}] vanishes on [𝔽_q* \ {p}] and binomial
    [+ K] misses the unit [p+q].  Structure theorems for distinct
    odd primes [p < q < 2p]: [short_root_poly_coeff_splits],
    [no_root_poly_below_dq], [invert_all_units_folds_local_monomials],
    [leftover_monic_is_geo_kernel], [invert_all_units_plus_c_kernel_iff].
    Pin 187 wrappers apply those.  Not
    [residual_solver_constructs_factor_open_named] and not the
    extraction nameds.  Cross-confirmed by [cas/164], [cas/165], [cas/166], [cas/172],
    [cas/173], [cas/174], [cas/175], [cas/176], [cas/177],
    [cas/178], [cas/179], [cas/180], [cas/181], [cas/182],
    [cas/183], [cas/184], [cas/185], [cas/186], [cas/187],
    [cas/188], [cas/189], [cas/190], [cas/191], [cas/192],
    [cas/193], [cas/194], [cas/195], [cas/196], [cas/197],
    [cas/198], [cas/199], [cas/200], [cas/201], [cas/202],
    [cas/203], [cas/204], [cas/205], [cas/206], [cas/207],
    [cas/208], [cas/209], [cas/210], [cas/211], [cas/212],
    [cas/213], [cas/214], and [cas/254]. *)

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

Theorem root_poly_eval_coprime :
  forall P y,
    (forall z, Z.coprime z pin_N ->
       powm (poly_eval P z) pin_e pin_N = z mod pin_N) ->
    Z.coprime y pin_N ->
    Z.coprime (poly_eval P y) pin_N.
Proof.
  intros P y Hall Hcop.
  apply (powm_unit_is_coprime (poly_eval P y) pin_e pin_N);
    [apply pin_N_gt_1 | lia |].
  rewrite Hall by exact Hcop.
  rewrite Z.gcd_mod_l. exact Hcop.
Qed.

Theorem all_units_root_poly_is_trapdoor_map :
  forall P y,
    (forall z, Z.coprime z pin_N ->
       powm (poly_eval P z) pin_e pin_N = z mod pin_N) ->
    Z.coprime y pin_N ->
    poly_eval P y mod pin_N = powm y pin_d pin_N.
Proof.
  intros P y Hall Hcop.
  assert (Hz : Z.coprime (powm y pin_d pin_N) pin_N).
  { unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
    apply Z.coprime_pow_l; [lia | exact Hcop]. }
  replace (powm y pin_d pin_N) with (powm y pin_d pin_N mod pin_N).
  2: { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
  apply (pin_unique_unit_eth_root (poly_eval P y) (powm y pin_d pin_N)).
  - apply (root_poly_eval_coprime P y Hall Hcop).
  - exact Hz.
  - rewrite (Hall y Hcop).
    rewrite (pin_powm_de y Hcop).
    reflexivity.
Qed.

Theorem all_units_root_poly_eval_g :
  forall P,
    (forall z, Z.coprime z pin_N ->
       powm (poly_eval P z) pin_e pin_N = z mod pin_N) ->
    poly_eval P pin_g mod pin_N = powm pin_g pin_d pin_N.
Proof.
  intros P Hall.
  apply (all_units_root_poly_is_trapdoor_map P pin_g Hall pin_unit_3_coprime).
Qed.

Theorem pin_trapdoor_monomial_is_trapdoor_map :
  forall y,
    Z.coprime y pin_N ->
    poly_eval pin_trapdoor_monomial y mod pin_N = powm y pin_d pin_N.
Proof.
  intros y _Hcop.
  rewrite pin_trapdoor_monomial_eval.
  unfold powm. reflexivity.
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

    [d_q < q−2], so [deg P < q−2] is strictly below the number of
    residues in [𝔽_q*] that are units of [Z/NZ] (all of [1..q−1]
    except [p]).  An all-units root map must match [X^{d_q}] on
    those residues, hence [q] divides [P − X^{d_q}].  If the other
    coefficients are also [0] mod [p], the leftover monomial
    [c X^{d_q}] inverts [1] only if [c^e ≡ 1], then inverts [2]
    only if [2^{d_q e} ≡ 2 (mod p)], which is false (does not
    need [d_q ≡ 1 (mod p−1)]; that was [11×17] accident).
    The bound [deg ≤ d_q] is the old window; [deg < q−2] is the
    same argument.  General for distinct odd primes [p < q < 2p]
    ([short_root_poly_coeff_splits], [no_root_poly_below_dq]);
    pin 187 is a wrapper.  Not the extraction nameds.
    Cross-confirmed by [cas/165], [cas/170], [cas/175], and
    [cas/254]. *)

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

Definition fq_units_of_N (p q : Z) : list Z :=
  filter (fun a => negb (a =? p)) (units_mod_prime q).

Definition pin_Fq_units_of_N : list Z := fq_units_of_N pin_p pin_q.

Lemma pin_Fq_units_of_N_length :
  length pin_Fq_units_of_N = Z.to_nat (pin_q - 2).
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

Lemma zseq_NoDup :
  forall start n, NoDup (zseq start n).
Proof.
  intros start n. revert start.
  induction n as [|n IH]; intros start; simpl.
  - constructor.
  - constructor.
    + intros Hin. pose proof (zseq_In_bounds (start + 1) n start Hin). lia.
    + apply IH.
Qed.

Lemma filter_neq_id :
  forall p xs,
    ~ In p xs ->
    filter (fun a => negb (a =? p)) xs = xs.
Proof.
  intros p xs Hnin.
  induction xs as [|x rest IH]; simpl; [reflexivity|].
  destruct (x =? p) eqn:Hx.
  - apply Z.eqb_eq in Hx. subst x. exfalso. apply Hnin. left. reflexivity.
  - simpl. f_equal. apply IH. intros Hin. apply Hnin. right. exact Hin.
Qed.

Lemma filter_neq_length_in :
  forall p xs,
    NoDup xs ->
    In p xs ->
    length (filter (fun a => negb (a =? p)) xs) = Nat.pred (length xs).
Proof.
  intros p xs.
  induction xs as [|x rest IH]; intros Hnd Hin; simpl in *.
  - contradiction.
  - inversion Hnd as [|x' rest' Hnin Hnd']; subst.
    destruct Hin as [Heq | Hin].
    + subst x. rewrite Z.eqb_refl. simpl.
      rewrite filter_neq_id by exact Hnin. reflexivity.
    + destruct (x =? p) eqn:Hx.
      * apply Z.eqb_eq in Hx. subst x. contradiction.
      * simpl. rewrite IH by assumption. destruct rest; [contradiction | reflexivity].
Qed.

Lemma units_mod_prime_contains :
  forall r a, 1 < r -> 1 <= a < r -> In a (units_mod_prime r).
Proof.
  intros r a Hr Ha. unfold units_mod_prime.
  apply zseq_In_interval. rewrite Z2Nat.id; lia.
Qed.

Lemma fq_units_of_N_length :
  forall p q,
    1 < p ->
    p < q ->
    length (fq_units_of_N p q) = Z.to_nat (q - 2).
Proof.
  intros p q Hp Hlt.
  unfold fq_units_of_N.
  assert (Hq : 1 < q) by lia.
  rewrite filter_neq_length_in.
  - rewrite units_mod_prime_length by lia.
    replace (Z.to_nat (q - 1)) with (S (Z.to_nat (q - 2))).
    + reflexivity.
    + replace (q - 1) with (Z.succ (q - 2)) by lia.
      rewrite Z2Nat.inj_succ by lia. reflexivity.
  - unfold units_mod_prime. apply zseq_NoDup.
  - apply units_mod_prime_contains; lia.
Qed.

Lemma fq_units_of_N_distinct :
  forall p q,
    Z.prime q ->
    pairwise_distinct_mod q (fq_units_of_N p q).
Proof.
  intros p q Hq. unfold fq_units_of_N.
  apply pairwise_distinct_mod_filter, units_mod_prime_distinct, Hq.
Qed.

Lemma fq_units_of_N_coprime :
  forall p q a,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    q < 2 * p ->
    In a (fq_units_of_N p q) ->
    Z.coprime a (p * q).
Proof.
  intros p q a Hp Hq Hneq Hlt H2p Hin.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  unfold fq_units_of_N in Hin.
  apply filter_In in Hin. destruct Hin as [Hin Hne].
  apply negb_true_iff, Z.eqb_neq in Hne.
  pose proof (units_mod_prime_In q a ltac:(lia) Hin) as Hb.
  apply (proj2 (coprime_semiprime p q a Hp Hq Hneq)).
  split.
  - rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hp|].
    intros [k Hk].
    assert (0 < k) by nia.
    destruct (Z.le_gt_cases 2 k) as [Hk2 | Hk1].
    + assert (2 * p <= a) by nia. lia.
    + assert (k = 1) by lia. subst k. lia.
  - rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hq|].
    intros [k Hk]. destruct k as [|k|k]; nia.
Qed.

Lemma fq_units_or_p :
  forall p q a,
    In a (units_mod_prime q) ->
    a = p \/ In a (fq_units_of_N p q).
Proof.
  intros p q a Hin.
  unfold fq_units_of_N.
  destruct (a =? p) eqn:Heq.
  - left. apply Z.eqb_eq. exact Heq.
  - right. apply filter_In. split; [exact Hin|].
    apply negb_true_iff. exact Heq.
Qed.

Lemma fp_units_of_N_coprime :
  forall p q a,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    In a (units_mod_prime p) ->
    Z.coprime a (p * q).
Proof.
  intros p q a Hp Hq Hneq Hlt Hin.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  pose proof (units_mod_prime_In p a ltac:(lia) Hin) as Hb.
  apply (proj2 (coprime_semiprime p q a Hp Hq Hneq)).
  split.
  - rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hp|].
    intros [k Hk]. destruct k as [|k|k]; nia.
  - rewrite coprime_comm. apply Z.coprime_prime_l_iff; [apply Hq|].
    intros [k Hk]. destruct k as [|k|k]; nia.
Qed.

Lemma two_coprime_odd_primes :
  forall p q,
    Z.prime p ->
    Z.prime q ->
    2 < p ->
    2 < q ->
    Z.coprime 2 (p * q).
Proof.
  intros p q Hp Hq H2p H2q.
  apply Z.coprime_mul_r.
  - rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hp|].
    intros [k Hk]. destruct k as [|k|k]; nia.
  - rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hq|].
    intros [k Hk]. destruct k as [|k|k]; nia.
Qed.

Lemma pin_inv3_q_lt_window :
  (Z.to_nat pin_inv3_q < Z.to_nat (pin_q - 2))%nat.
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
    (poly_degree P < Z.to_nat (pin_q - 2))%nat ->
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
    pose proof pin_inv3_q_lt_window.
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

Lemma pin_two_pow_dbe_neq_2 :
  powm 2 (pin_inv3_q * pin_e) pin_p <> 2 mod pin_p.
Proof. vm_compute. discriminate. Qed.

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

Lemma short_root_local_at_q :
  forall p q e dq P y,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    0 < e ->
    0 <= dq ->
    (e * dq) mod (q - 1) = 1 ->
    Z.coprime y (p * q) ->
    powm (poly_eval P y) e (p * q) = y mod (p * q) ->
    poly_eval P y mod q = powm y dq q.
Proof.
  intros p q e dq P y Hp Hq Hneq He Hd Hinv Hcop Hroot.
  pose proof (Z.prime_ge_2 _ Hq). pose proof (Z.prime_ge_2 _ Hp).
  apply coprime_semiprime in Hcop; [|exact Hp|exact Hq|exact Hneq].
  destruct Hcop as [_ Hcopq].
  assert (Hred : powm (poly_eval P y) e q = y mod q).
  { unfold powm in Hroot |- *.
    rewrite <- (mod_product_r (poly_eval P y ^ e) p q) by lia.
    rewrite Hroot.
    apply mod_product_r; lia. }
  assert (Hloc : powm (powm y dq q) e q = y mod q).
  { apply local_eth_root; [exact Hq | exact Hcopq | lia | exact Hd | exact Hinv]. }
  assert (Hxcop : Z.coprime (poly_eval P y) q).
  { apply (powm_unit_is_coprime (poly_eval P y) e q); [lia | lia |].
    rewrite Hred. rewrite Z.gcd_mod_l. exact Hcopq. }
  assert (Hzcop : Z.coprime (powm y dq q) q).
  { unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
    apply Z.coprime_pow_l; [lia | exact Hcopq]. }
  transitivity (powm y dq q mod q).
  - apply (unique_eth_root_mod_prime q e dq (poly_eval P y) (powm y dq q));
      [exact Hq | lia | exact Hd | exact Hinv | exact Hxcop | exact Hzcop|].
    rewrite Hred, Hloc. reflexivity.
  - unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma short_root_local_at_p :
  forall p q e da P y,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    0 < e ->
    0 <= da ->
    (e * da) mod (p - 1) = 1 ->
    Z.coprime y (p * q) ->
    powm (poly_eval P y) e (p * q) = y mod (p * q) ->
    poly_eval P y mod p = powm y da p.
Proof.
  intros p q e da P y Hp Hq Hneq He Hd Hinv Hcop Hroot.
  pose proof (Z.prime_ge_2 _ Hq). pose proof (Z.prime_ge_2 _ Hp).
  apply coprime_semiprime in Hcop; [|exact Hp|exact Hq|exact Hneq].
  destruct Hcop as [Hcopp _].
  assert (Hred : powm (poly_eval P y) e p = y mod p).
  { unfold powm in Hroot |- *.
    rewrite <- (mod_product_l (poly_eval P y ^ e) p q) by lia.
    rewrite Hroot.
    apply mod_product_l; lia. }
  assert (Hloc : powm (powm y da p) e p = y mod p).
  { apply local_eth_root; [exact Hp | exact Hcopp | lia | exact Hd | exact Hinv]. }
  assert (Hxcop : Z.coprime (poly_eval P y) p).
  { apply (powm_unit_is_coprime (poly_eval P y) e p); [lia | lia |].
    rewrite Hred. rewrite Z.gcd_mod_l. exact Hcopp. }
  assert (Hzcop : Z.coprime (powm y da p) p).
  { unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
    apply Z.coprime_pow_l; [lia | exact Hcopp]. }
  transitivity (powm y da p mod p).
  - apply (unique_eth_root_mod_prime p e da (poly_eval P y) (powm y da p));
      [exact Hp | lia | exact Hd | exact Hinv | exact Hxcop | exact Hzcop|].
    rewrite Hred, Hloc. reflexivity.
  - unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma short_root_diff_vanishes_semiprime :
  forall p q e dq P,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    q < 2 * p ->
    0 < e ->
    0 <= dq ->
    (e * dq) mod (q - 1) = 1 ->
    (forall y, Z.coprime y (p * q) ->
       powm (poly_eval P y) e (p * q) = y mod (p * q)) ->
    Forall (fun a => (q | poly_eval
      (poly_sub P (poly_Xn (Z.to_nat dq))) a))
      (fq_units_of_N p q).
Proof.
  intros p q e dq P Hp Hq Hneq Hlt H2p He Hd Hinv Hall.
  pose proof (Z.prime_ge_2 _ Hq).
  apply Forall_forall. intros a Hin.
  pose proof (fq_units_of_N_coprime p q a Hp Hq Hneq Hlt H2p Hin) as Hcop.
  pose proof (Hall a Hcop) as Hroot.
  pose proof (short_root_local_at_q p q e dq P a Hp Hq Hneq He Hd Hinv Hcop Hroot)
    as Hloc.
  unfold poly_sub.
  rewrite poly_eval_add, poly_eval_map_mul, poly_eval_Xn, Z2Nat.id by lia.
  replace (poly_eval P a + -1 * a ^ dq)
    with (poly_eval P a - a ^ dq) by ring.
  apply Z.mod_divide; [lia|].
  rewrite Zminus_mod, Hloc.
  unfold powm. rewrite Z.sub_diag, Z.mod_0_l by lia. reflexivity.
Qed.

Lemma short_root_q_divides_diff_semiprime :
  forall p q e dq P,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    q < 2 * p ->
    0 < e ->
    0 <= dq ->
    (e * dq) mod (q - 1) = 1 ->
    (Z.to_nat dq < Z.to_nat (q - 2))%nat ->
    (poly_degree P < Z.to_nat (q - 2))%nat ->
    (forall y, Z.coprime y (p * q) ->
       powm (poly_eval P y) e (p * q) = y mod (p * q)) ->
    forall i, (q | nth i (poly_sub P (poly_Xn (Z.to_nat dq))) 0).
Proof.
  intros p q e dq P Hp Hq Hneq Hlt H2p He Hd Hinv Hwin Hdeg Hall i.
  pose proof (Z.prime_ge_2 _ Hp). pose proof (Z.prime_ge_2 _ Hq).
  apply (poly_prime_roots_divides q (fq_units_of_N p q)
           (poly_sub P (poly_Xn (Z.to_nat dq)))
           Hq (fq_units_of_N_distinct p q Hq)).
  - pose proof (poly_degree_sub_le P (poly_Xn (Z.to_nat dq))) as Hs.
    rewrite poly_degree_Xn in Hs.
    rewrite (fq_units_of_N_length p q) by lia.
    lia.
  - apply (short_root_diff_vanishes_semiprime p q e dq P);
      [exact Hp | exact Hq | exact Hneq | exact Hlt | exact H2p
       | exact He | exact Hd | exact Hinv | exact Hall].
Qed.

Theorem short_root_poly_coeff_splits :
  forall p q e dq P,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    2 < p ->
    2 < q ->
    p < q ->
    q < 2 * p ->
    0 < e ->
    0 <= dq ->
    (e * dq) mod (q - 1) = 1 ->
    (Z.to_nat dq < Z.to_nat (q - 2))%nat ->
    powm 2 (dq * e) p <> 2 mod p ->
    (poly_degree P < Z.to_nat (q - 2))%nat ->
    (forall y, Z.coprime y (p * q) ->
       powm (poly_eval P y) e (p * q) = y mod (p * q)) ->
    exists i, 1 < Z.gcd (nth i P 0) (p * q) < p * q.
Proof.
  intros p q e dq P Hp Hq Hneq H2p H2q Hlt Hqp He Hd Hinv Hwin Htwo Hdeg Hall.
  pose proof (Z.prime_ge_2 _ Hp). pose proof (Z.prime_ge_2 _ Hq).
  pose proof (short_root_q_divides_diff_semiprime p q e dq P
                Hp Hq Hneq Hlt Hqp He Hd Hinv Hwin Hdeg Hall) as Hqdiv.
  destruct (finite_support_cases (Nat.pred (Z.to_nat (q - 2)))
              (Z.to_nat dq) P p) as [Hex | Hallp].
  - destruct Hex as [i [_ [Hne Hnp]]].
    exists i.
    pose proof (Hqdiv i) as HqQ.
    rewrite nth_poly_sub, nth_Xn in HqQ.
    destruct (Nat.eq_dec i (Z.to_nat dq)); [lia|].
    replace (nth i P 0 - 0) with (nth i P 0) in HqQ by lia.
    assert (Hg : Z.gcd (nth i P 0) (p * q) = q).
    { apply (gcd_q_not_p p q (nth i P 0));
        [exact Hp | exact Hq | exact Hneq | exact HqQ | exact Hnp]. }
    rewrite Hg. split; lia.
  - set (c := nth (Z.to_nat dq) P 0).
    assert (HNdiv : forall i, i <> Z.to_nat dq ->
                      (p * q | nth i P 0)).
    { intros i Hne.
      destruct (Nat.le_gt_cases i (Nat.pred (Z.to_nat (q - 2))))
        as [Hle | Hgt].
      - pose proof (Hqdiv i) as HqQ.
        rewrite nth_poly_sub, nth_Xn in HqQ.
        destruct (Nat.eq_dec i (Z.to_nat dq)); [lia|].
        replace (nth i P 0 - 0) with (nth i P 0) in HqQ by lia.
        apply divide_by_coprime_product.
        + apply prime_coprime_distinct; [exact Hp | exact Hq | exact Hneq].
        + apply Hallp; [exact Hle | exact Hne].
        + exact HqQ.
      - rewrite (poly_nth_above P i); [apply Z.divide_0_r | lia]. }
    assert (H1c : Z.coprime 1 (p * q)) by apply Z.coprime_1_l.
    assert (H2c : Z.coprime 2 (p * q))
      by (apply two_coprime_odd_primes; assumption).
    assert (HP1 : powm (poly_eval P 1) e (p * q) = 1).
    { rewrite Hall by exact H1c. apply Z.mod_1_l. lia. }
    assert (HP2 : powm (poly_eval P 2) e (p * q) = 2).
    { rewrite Hall by exact H2c. apply Z.mod_small. nia. }
    pose proof (poly_eval_single_support P (Z.to_nat dq) 1 (p * q)
                  ltac:(lia) HNdiv) as He1.
    pose proof (poly_eval_single_support P (Z.to_nat dq) 2 (p * q)
                  ltac:(lia) HNdiv) as He2.
    rewrite Z2Nat.id in He1, He2 by lia.
    fold c in He1, He2.
    rewrite Z.pow_1_l in He1 by lia.
    replace (c * 1) with c in He1 by ring.
    assert (Hc : powm c e (p * q) = 1).
    { rewrite <- HP1. apply powm_div_cong; [lia | lia |].
      apply (proj1 (Z.divide_opp_r (p * q) (c - poly_eval P 1))).
      replace (- (c - poly_eval P 1)) with (poly_eval P 1 - c) by ring.
      exact He1. }
    assert (H2ce : powm (c * 2 ^ dq) e (p * q) = 2).
    { transitivity (powm (poly_eval P 2) e (p * q)).
      - apply powm_div_cong; [lia | lia |].
        apply (proj1 (Z.divide_opp_r (p * q)
                        (c * 2 ^ dq - poly_eval P 2))).
        replace (- (c * 2 ^ dq - poly_eval P 2))
          with (poly_eval P 2 - c * 2 ^ dq) by ring.
        exact He2.
      - exact HP2. }
    assert (Hcp : powm c e p = 1).
    { unfold powm in Hc |- *.
      rewrite <- (mod_product_l (c ^ e) p q) by lia.
      rewrite Hc. apply Z.mod_1_l. lia. }
    assert (H2p' : powm (c * 2 ^ dq) e p = 2 mod p).
    { unfold powm in H2ce |- *.
      rewrite <- (mod_product_l ((c * 2 ^ dq) ^ e) p q) by lia.
      rewrite H2ce. reflexivity. }
    rewrite (powm_mul_base c (2 ^ dq) e p) in H2p' by lia.
    rewrite Hcp, Z.mul_1_l in H2p'.
    unfold powm in H2p'.
    rewrite Z.mod_mod in H2p' by lia.
    rewrite <- Z.pow_mul_r in H2p' by lia.
    change ((2 ^ (dq * e)) mod p) with (powm 2 (dq * e) p) in H2p'.
    contradict H2p'. exact Htwo.
Qed.

Theorem no_root_poly_below_dq :
  forall p q e dq P,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    q < 2 * p ->
    0 < e ->
    0 <= dq ->
    (e * dq) mod (q - 1) = 1 ->
    (Z.to_nat dq < Z.to_nat (q - 2))%nat ->
    (poly_degree P < Z.to_nat dq)%nat ->
    ~ (forall y, Z.coprime y (p * q) ->
         powm (poly_eval P y) e (p * q) = y mod (p * q)).
Proof.
  intros p q e dq P Hp Hq Hneq Hlt Hqp He Hd Hinv Hwin Hdeg Hall.
  pose proof (short_root_q_divides_diff_semiprime p q e dq P
                Hp Hq Hneq Hlt Hqp He Hd Hinv Hwin ltac:(lia) Hall
                (Z.to_nat dq)) as HqQ.
  rewrite nth_poly_sub, nth_Xn in HqQ.
  destruct (Nat.eq_dec (Z.to_nat dq) (Z.to_nat dq)); [|lia].
  rewrite (poly_nth_above P (Z.to_nat dq) Hdeg) in HqQ.
  replace (0 - 1) with (-1) in HqQ by lia.
  pose proof (Z.prime_ge_2 q Hq).
  destruct HqQ as [k Hk]. destruct k as [|k|k]; nia.
Qed.

Theorem short_root_poly_some_coeff_splits :
  forall P,
    (poly_degree P < Z.to_nat (pin_q - 2))%nat ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    exists i, 1 < Z.gcd (nth i P 0) pin_N < pin_N.
Proof.
  intros P Hdeg Hall.
  change pin_N with (pin_p * pin_q) in Hall |- *.
  apply (short_root_poly_coeff_splits pin_p pin_q pin_e pin_inv3_q P);
    [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q
     | lia | lia | lia | lia | lia | lia
     | apply (proj2 pin_inv3_local)
     | apply pin_inv3_q_lt_window
     | exact pin_two_pow_dbe_neq_2
     | exact Hdeg | exact Hall].
Qed.

Theorem pin_crt_root_poly_is_short :
  (poly_degree pin_crt_root_poly <= Z.to_nat pin_inv3_q)%nat.
Proof. rewrite pin_crt_binomial_degree. lia. Qed.

Theorem pin_crt_root_poly_short_splits :
  exists i, 1 < Z.gcd (nth i pin_crt_root_poly 0) pin_N < pin_N.
Proof.
  apply short_root_poly_some_coeff_splits.
  - pose proof pin_crt_root_poly_is_short.
    pose proof pin_inv3_q_lt_window.
    lia.
  - apply pin_crt_binomial_inverts_units.
Qed.

(** ** The window is sharp; nodiv GRA in it splits *)

Theorem no_root_poly_deg_lt_dq :
  forall P,
    (poly_degree P < Z.to_nat pin_inv3_q)%nat ->
    ~ (forall y, Z.coprime y pin_N ->
         powm (poly_eval P y) pin_e pin_N = y mod pin_N).
Proof.
  intros P Hdeg.
  change pin_N with (pin_p * pin_q).
  apply (no_root_poly_below_dq pin_p pin_q pin_e pin_inv3_q P);
    [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q
     | lia | lia | lia | lia
     | apply (proj2 pin_inv3_local)
     | apply pin_inv3_q_lt_window
     | exact Hdeg].
Qed.

Theorem pin_Xn_dp_does_not_invert_all_units :
  (poly_degree (poly_Xn (Z.to_nat pin_inv3_p)) < Z.to_nat pin_inv3_q)%nat /\
  ~ (forall y, Z.coprime y pin_N ->
       powm (poly_eval (poly_Xn (Z.to_nat pin_inv3_p)) y) pin_e pin_N
         = y mod pin_N).
Proof.
  split.
  - rewrite poly_degree_Xn. vm_compute. lia.
  - apply no_root_poly_deg_lt_dq. rewrite poly_degree_Xn. vm_compute. lia.
Qed.

Theorem nodiv_gra_short_dq_splits :
  forall ops out,
    Forall is_nodiv ops ->
    (nth out (gra_deg_bound ops slp_init_deg) 0%nat
       <= Z.to_nat pin_inv3_q)%nat ->
    (forall y, Z.coprime y pin_N ->
       powm (gra_eval pin_N ops y out) pin_e pin_N = y mod pin_N) ->
    exists i,
      1 < Z.gcd (nth i (nth out (gra_run_poly ops slp_init_poly) []) 0)
            pin_N
        < pin_N.
Proof.
  intros ops out Hop Hbound Hall.
  apply short_root_poly_some_coeff_splits.
  - pose proof (gra_nodiv_degree_le ops out Hop).
    pose proof pin_inv3_q_lt_window.
    lia.
  - intros y Hy.
    rewrite <- (gra_nodiv_denotes ops pin_N y out Hop).
    apply Hall. exact Hy.
Qed.

Theorem nodiv_identity_bound_lt_dq :
  (nth 2%nat (gra_deg_bound [] slp_init_deg) 0%nat
     < Z.to_nat pin_inv3_q)%nat.
Proof. vm_compute. lia. Qed.

Theorem nodiv_square_bound_lt_dq :
  (nth 3%nat (gra_deg_bound [GMul 2%nat 2%nat] slp_init_deg) 0%nat
     < Z.to_nat pin_inv3_q)%nat.
Proof. vm_compute. lia. Qed.

(** ** Monomial all-units invert iff the exponent is trapdoor

    [X^k] inverts every unit iff [e k ≡ 1 (mod λ)]: [k] is a
    decryption exponent ([d], or [d+tλ]).  Local inverses [d_p],
    [d_q] invert one prime field, not [(Z/NZ)*].  Knowing such a
    [k] is Miller-from-[(e,k)] ([miller_from_trapdoor_exponent]);
    the [d] case is [miller_from_d].  [k = d+2λ] changes
    [odd_part(M)] and still splits.  Not
    [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/167] and [cas/173]. *)

Theorem trapdoor_monomial_inverts_all_units :
  forall k y,
    0 <= k ->
    (pin_e * k) mod pin_lam = 1 ->
    Z.coprime y pin_N ->
    powm (powm y k pin_N) pin_e pin_N = y mod pin_N.
Proof.
  intros k y Hk Hinv Hcop.
  assert (Hek : 0 <= pin_e * k - 1).
  { pose proof (Z.div_mod (pin_e * k) pin_lam ltac:(lia)) as Hdm.
    rewrite Hinv in Hdm.
    assert (0 <= (pin_e * k) / pin_lam) by (apply Z.div_pos; lia).
    nia. }
  rewrite <- powm_mul_r by lia.
  rewrite (Z.mul_comm k pin_e).
  replace (pin_e * k) with (pin_e * k - 1 + 1) by lia.
  rewrite powm_add_r by lia.
  rewrite powm_1_r by lia.
  rewrite (annihilates_units pin_p pin_q y (pin_e * k - 1));
    [| apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q
     | exact Hcop | exact Hek |].
  - rewrite Z.mul_1_l, Z.mod_mod by lia. reflexivity.
  - rewrite rsa_test_lambda.
    apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Hinv, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity.
Qed.

Theorem monomial_all_units_invert_is_trapdoor :
  forall k,
    0 <= k ->
    (forall y, Z.coprime y pin_N ->
       powm (powm y k pin_N) pin_e pin_N = y mod pin_N) ->
    (pin_e * k) mod pin_lam = 1.
Proof.
  intros k Hk Hall.
  assert (Hkpos : 1 <= k).
  { destruct (Z.le_gt_cases 1 k) as [Hle | Hlt]; [exact Hle|].
    assert (k = 0) by lia. subst k.
    pose proof (Hall 2 ltac:(vm_compute; reflexivity)) as H2.
    unfold powm in H2. rewrite Z.pow_0_r in H2.
    vm_compute in H2. discriminate. }
  pose proof pin_unit_3_coprime as Hgcop.
  pose proof (Hall pin_g Hgcop) as Hg.
  assert (Hek : 0 <= pin_e * k - 1) by lia.
  rewrite <- powm_mul_r in Hg by lia.
  rewrite (Z.mul_comm k pin_e) in Hg.
  replace (pin_e * k) with (pin_e * k - 1 + 1) in Hg by lia.
  rewrite powm_add_r in Hg by lia.
  rewrite powm_1_r in Hg by lia.
  assert (Hann : powm pin_g (pin_e * k - 1) pin_N = 1).
  { transitivity (powm pin_g (pin_e * k - 1) pin_N mod pin_N).
    - unfold powm. rewrite Z.mod_mod by lia. reflexivity.
    - transitivity (1 mod pin_N).
      + apply (mul_cancel_r_coprime
                 (powm pin_g (pin_e * k - 1) pin_N) 1
                 (pin_g mod pin_N) pin_N);
          [apply pin_N_gt_1 | |].
        * rewrite Z.gcd_mod_l. exact Hgcop.
        * rewrite Z.mul_1_l, Z.mod_mod by lia. exact Hg.
      + apply Z.mod_1_l. apply pin_N_gt_1. }
  pose proof (order_divides_annihilator pin_N pin_g pin_lam (pin_e * k - 1)
                pin_N_gt_1 ltac:(lia) is_order_pin_3_80 Hann) as Hdiv.
  apply Z.mod_divide in Hdiv; [|lia].
  replace (pin_e * k) with (pin_e * k - 1 + 1) by lia.
  rewrite Z.add_mod, Hdiv, Z.add_0_l, Z.mod_mod, Z.mod_1_l by lia.
  reflexivity.
Qed.

Theorem pin_d_monomial_is_trapdoor :
  (pin_e * pin_d) mod pin_lam = 1.
Proof. apply pin_trapdoor_ed_inv. Qed.

Theorem pin_dp_monomial_not_trapdoor :
  (pin_e * pin_inv3_p) mod pin_lam <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem pin_dq_monomial_not_trapdoor :
  (pin_e * pin_inv3_q) mod pin_lam <> 1.
Proof. vm_compute. discriminate. Qed.

Theorem pin_d_plus_lam_is_trapdoor :
  (pin_e * (pin_d + pin_lam)) mod pin_lam = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_d_plus_2lam_is_trapdoor :
  (pin_e * (pin_d + 2 * pin_lam)) mod pin_lam = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma pin_trapdoor_k_M_pos :
  forall k,
    0 <= k ->
    (pin_e * k) mod pin_lam = 1 ->
    0 < pin_e * k - 1.
Proof.
  intros k Hk Hinv.
  destruct (Z.le_gt_cases k 0) as [Hle | Hgt].
  - assert (k = 0) by lia. subst k.
    vm_compute in Hinv. discriminate.
  - nia.
Qed.

Theorem monomial_all_units_invert_miller :
  forall k a kp kq,
    0 <= k ->
    (forall y, Z.coprime y pin_N ->
       powm (powm y k pin_N) pin_e pin_N = y mod pin_N) ->
    Z.coprime a pin_N ->
    two_height a (odd_part (pin_e * k - 1)) pin_p kp ->
    two_height a (odd_part (pin_e * k - 1)) pin_q kq ->
    (kp < kq)%nat ->
    Z.gcd (a ^ (odd_part (pin_e * k - 1) * pow2n kp) - 1) pin_N = pin_p.
Proof.
  intros k a kp kq Hk Hall Hcop Hpht Hqht Hlt.
  pose proof (monomial_all_units_invert_is_trapdoor k Hk Hall) as Hinv.
  pose proof (pin_trapdoor_k_M_pos k Hk Hinv) as HMpos.
  change pin_N with (rsa_N rsa_test).
  change pin_p with (rsa_p rsa_test).
  apply (miller_from_trapdoor_exponent rsa_test k a kp kq).
  - change (rsa_e rsa_test) with pin_e. exact HMpos.
  - change (rsa_e rsa_test) with pin_e.
    unfold rsa_lambda.
    change (rsa_p rsa_test) with pin_p.
    change (rsa_q rsa_test) with pin_q.
    rewrite rsa_test_lambda. exact Hinv.
  - rewrite <- rsa_test_N in Hcop. exact Hcop.
  - change (rsa_e rsa_test) with pin_e.
    change (rsa_p rsa_test) with pin_p. exact Hpht.
  - change (rsa_e rsa_test) with pin_e.
    change (rsa_q rsa_test) with pin_q. exact Hqht.
  - exact Hlt.
Qed.

Theorem pin_miller_from_d_plus_lam :
  Z.gcd (2 ^ (odd_part (pin_e * (pin_d + pin_lam) - 1)
                * pow2n (val2 pin_ord2_p)) - 1) pin_N
    = pin_p.
Proof.
  pose proof pin_d_plus_lam_is_trapdoor as Hinv.
  apply (monomial_all_units_invert_miller (pin_d + pin_lam) 2
           (val2 pin_ord2_p) (val2 pin_ord2_q)).
  - lia.
  - intros y Hy. apply trapdoor_monomial_inverts_all_units; [lia | exact Hinv | exact Hy].
  - vm_compute. reflexivity.
  - replace (odd_part (pin_e * (pin_d + pin_lam) - 1))
      with (miller_t rsa_test) by (rewrite rsa_test_miller_t; vm_compute; reflexivity).
    change pin_p with (rsa_p rsa_test).
    apply rsa_test_base2_heights.
  - replace (odd_part (pin_e * (pin_d + pin_lam) - 1))
      with (miller_t rsa_test) by (rewrite rsa_test_miller_t; vm_compute; reflexivity).
    change pin_q with (rsa_q rsa_test).
    apply rsa_test_base2_heights.
  - vm_compute. lia.
Qed.

Lemma pin_base2_height_p_at_35 :
  two_height 2 35 pin_p 1%nat.
Proof.
  split.
  - vm_compute. reflexivity.
  - intros j Hj. assert (j = 0)%nat by lia. subst. vm_compute. discriminate.
Qed.

Lemma pin_base2_height_q_at_35 :
  two_height 2 35 pin_q 3%nat.
Proof.
  split.
  - vm_compute. reflexivity.
  - intros j Hj.
    assert (j = 0 \/ j = 1 \/ j = 2)%nat by lia.
    destruct H as [H|[H|H]]; subst; vm_compute; discriminate.
Qed.

Theorem pin_odd_part_d_plus_2lam :
  odd_part (pin_e * (pin_d + 2 * pin_lam) - 1) = 35.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_miller_from_d_plus_2lam :
  Z.gcd (2 ^ (odd_part (pin_e * (pin_d + 2 * pin_lam) - 1)
                * pow2n 1) - 1) pin_N
    = pin_p.
Proof.
  pose proof pin_d_plus_2lam_is_trapdoor as Hinv.
  rewrite pin_odd_part_d_plus_2lam.
  apply (monomial_all_units_invert_miller (pin_d + 2 * pin_lam) 2 1%nat 3%nat).
  - lia.
  - intros y Hy. apply trapdoor_monomial_inverts_all_units; [lia | exact Hinv | exact Hy].
  - vm_compute. reflexivity.
  - rewrite pin_odd_part_d_plus_2lam. apply pin_base2_height_p_at_35.
  - rewrite pin_odd_part_d_plus_2lam. apply pin_base2_height_q_at_35.
  - lia.
Qed.

(** ** Local inverses CRT to the trapdoor exponent

    [d ≡ d_p (mod p−1)] and [d ≡ d_q (mod q−1)].  Any [x] with
    those residues is [x ≡ d (mod λ)].  Writing both local
    inverses writes [d].  Not
    [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/174]. *)

Theorem pin_d_mod_pminus1 :
  pin_d mod (pin_p - 1) = pin_inv3_p.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_d_mod_qminus1 :
  pin_d mod (pin_q - 1) = pin_inv3_q.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_inv3_p_is_crt_dp :
  pin_inv3_p = crt_dp pin_d pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_inv3_q_is_crt_dq :
  pin_inv3_q = crt_dq pin_d pin_q.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_local_inverses_recover_d :
  forall x,
    x mod (pin_p - 1) = pin_inv3_p ->
    x mod (pin_q - 1) = pin_inv3_q ->
    x mod pin_lam = pin_d.
Proof.
  intros x Hp Hq.
  transitivity (pin_d mod pin_lam); [| vm_compute; reflexivity].
  rewrite <- rsa_test_lambda.
  apply (crt_dp_dq_recover_d pin_p pin_q pin_d x).
  - apply pin_p_prime.
  - apply pin_q_prime.
  - lia.
  - lia.
  - unfold crt_dp. rewrite pin_d_mod_pminus1. exact Hp.
  - unfold crt_dq. rewrite pin_d_mod_qminus1. exact Hq.
Qed.

Theorem pin_local_inv_unique_p :
  forall da,
    (pin_e * da) mod (pin_p - 1) = 1 ->
    da mod (pin_p - 1) = pin_inv3_p.
Proof.
  intros da Hda.
  rewrite pin_inv3_p_is_crt_dp.
  apply (local_inv_is_crt_dp pin_e pin_d da pin_p pin_q);
    [apply pin_p_prime | apply pin_q_prime | lia | | exact Hda].
  rewrite rsa_test_lambda. apply pin_trapdoor_ed_inv.
Qed.

Theorem pin_local_inv_unique_q :
  forall db,
    (pin_e * db) mod (pin_q - 1) = 1 ->
    db mod (pin_q - 1) = pin_inv3_q.
Proof.
  intros db Hdb.
  rewrite pin_inv3_q_is_crt_dq.
  apply (local_inv_is_crt_dq pin_e pin_d db pin_p pin_q);
    [apply pin_p_prime | apply pin_q_prime | lia | | exact Hdb].
  rewrite rsa_test_lambda. apply pin_trapdoor_ed_inv.
Qed.

(** ** Mid-degree inhabitant of the widened window

    [P =] CRT binomial [+ N X^{12}] has degree 12, which sits in
    [d_q < deg < q−2], inverts every unit (the extra term is [0]
    mod [N]), and still splits.  Cross-confirmed by [cas/175]. *)

Definition pin_mid_root_poly : list Z :=
  poly_add pin_crt_root_poly (map_mul pin_N (poly_Xn 12%nat)).

Theorem pin_mid_root_poly_degree :
  poly_degree pin_mid_root_poly = 12%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_mid_root_poly_in_window :
  (poly_degree pin_mid_root_poly < Z.to_nat (pin_q - 2))%nat.
Proof. rewrite pin_mid_root_poly_degree. vm_compute. lia. Qed.

Theorem pin_mid_root_poly_inverts_units :
  forall y,
    Z.coprime y pin_N ->
    powm (poly_eval pin_mid_root_poly y) pin_e pin_N = y mod pin_N.
Proof.
  intros y Hcop.
  unfold pin_mid_root_poly.
  rewrite poly_eval_add, poly_eval_map_mul, poly_eval_Xn.
  transitivity (powm (poly_eval pin_crt_root_poly y) pin_e pin_N).
  - apply powm_div_cong; [lia | lia |].
    exists (y ^ Z.of_nat 12%nat). ring.
  - apply pin_crt_binomial_inverts_units. exact Hcop.
Qed.

Theorem pin_mid_root_poly_splits :
  exists i, 1 < Z.gcd (nth i pin_mid_root_poly 0) pin_N < pin_N.
Proof.
  apply short_root_poly_some_coeff_splits.
  - apply pin_mid_root_poly_in_window.
  - apply pin_mid_root_poly_inverts_units.
Qed.

(** ** Local match on [𝔽_p*], any degree

    Campaign pins have [p < q], so every residue of [𝔽_p*] is a
    unit of [Z/NZ].  An all-units invert poly matches [X^{d_p}]
    on that complete sample set, with no degree bound.
    Cross-confirmed by [cas/176]. *)

Theorem pin_p_lt_q : pin_p < pin_q.
Proof. lia. Qed.

Definition pin_Fp_units_of_N : list Z := units_mod_prime pin_p.

Lemma pin_Fp_units_of_N_length :
  length pin_Fp_units_of_N = Z.to_nat (pin_p - 1).
Proof. apply units_mod_prime_length. lia. Qed.

Lemma pin_Fp_units_of_N_distinct :
  pairwise_distinct_mod pin_p pin_Fp_units_of_N.
Proof. apply units_mod_prime_distinct, pin_p_prime. Qed.

Lemma pin_Fp_units_of_N_coprime :
  forall a, In a pin_Fp_units_of_N -> Z.coprime a pin_N.
Proof.
  intros a Hin.
  pose proof (units_mod_prime_In pin_p a ltac:(lia) Hin) as Hb.
  pose proof pin_p_lt_q.
  apply (proj2 (coprime_semiprime pin_p pin_q a
                   pin_p_prime pin_q_prime pin_p_neq_q)).
  split.
  - rewrite coprime_comm. apply Z.coprime_prime_l_iff; [apply pin_p_prime|].
    intros [k Hk]. nia.
  - rewrite coprime_comm. apply Z.coprime_prime_l_iff; [apply pin_q_prime|].
    intros [k Hk]. nia.
Qed.

Lemma short_root_local_mod_p :
  forall P y,
    Z.coprime y pin_N ->
    powm (poly_eval P y) pin_e pin_N = y mod pin_N ->
    poly_eval P y mod pin_p = powm y pin_inv3_p pin_p.
Proof.
  intros P y Hcop Hinv.
  pose proof pin_q_prime as Hq.
  pose proof pin_p_prime as Hp.
  pose proof (Z.prime_ge_2 _ Hq). pose proof (Z.prime_ge_2 _ Hp).
  apply coprime_semiprime in Hcop;
    [|exact Hp|exact Hq|apply pin_p_neq_q].
  destruct Hcop as [Hcopp _].
  assert (Hred : powm (poly_eval P y) pin_e pin_p = y mod pin_p).
  { unfold powm in Hinv |- *.
    rewrite <- (mod_product_l (poly_eval P y ^ pin_e) pin_p pin_q) by lia.
    rewrite Hinv.
    apply mod_product_l; lia. }
  assert (Hloc : powm (powm y pin_inv3_p pin_p) pin_e pin_p = y mod pin_p).
  { apply local_eth_root; [exact Hp | exact Hcopp | lia | lia |].
    apply (proj1 pin_inv3_local). }
  assert (Hxcop : Z.coprime (poly_eval P y) pin_p).
  { apply (powm_unit_is_coprime (poly_eval P y) pin_e pin_p); [lia | lia |].
    rewrite Hred. rewrite Z.gcd_mod_l. exact Hcopp. }
  assert (Hzcop : Z.coprime (powm y pin_inv3_p pin_p) pin_p).
  { unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
    apply Z.coprime_pow_l; [lia | exact Hcopp]. }
  transitivity (powm y pin_inv3_p pin_p mod pin_p).
  - apply (unique_eth_root_mod_prime pin_p pin_e pin_inv3_p
             (poly_eval P y) (powm y pin_inv3_p pin_p)).
    -- apply pin_p_prime.
    -- lia.
    -- lia.
    -- apply (proj1 pin_inv3_local).
    -- exact Hxcop.
    -- exact Hzcop.
    -- rewrite Hred, Hloc. reflexivity.
  - unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem invert_all_units_local_p :
  forall P y,
    (forall z, Z.coprime z pin_N ->
       powm (poly_eval P z) pin_e pin_N = z mod pin_N) ->
    Z.coprime y pin_N ->
    poly_eval P y mod pin_p = powm y pin_inv3_p pin_p.
Proof.
  intros P y Hall Hcop.
  apply (short_root_local_mod_p P y Hcop (Hall y Hcop)).
Qed.

Theorem invert_all_units_local_q :
  forall P y,
    (forall z, Z.coprime z pin_N ->
       powm (poly_eval P z) pin_e pin_N = z mod pin_N) ->
    Z.coprime y pin_N ->
    poly_eval P y mod pin_q = powm y pin_inv3_q pin_q.
Proof.
  intros P y Hall Hcop.
  apply (short_root_local_mod_q P y Hcop (Hall y Hcop)).
Qed.

(** ** Fermat fold on [𝔽_p*] is [X^{d_p}]

    Sum coefficients in each residue class modulo [p−1].  Fold
    degree is [< p−1] and [𝔽_p*] supplies [p−1] samples, so an
    all-units invert poly has [fold_p(P) ≡ X^{d_p}] as polynomials
    modulo [p].  No leftover at the Fermat boundary on this side.
    Cross-confirmed by [cas/177]. *)

Lemma powm_reduce_period :
  forall y k m n,
    1 < n ->
    0 <= k ->
    0 < m ->
    powm y m n = 1 ->
    powm y k n = powm y (k mod m) n.
Proof.
  intros y k m n Hn Hk Hm Hper.
  pose proof (Z.div_mod k m ltac:(lia)) as Hdm.
  rewrite Hdm at 1.
  assert (0 <= k mod m) by (apply Z.mod_pos_bound; lia).
  assert (0 <= k / m) by (apply Z.div_pos; lia).
  rewrite powm_add_r by nia.
  rewrite powm_mul_r by nia.
  rewrite Hper.
  rewrite powm_1_pow by nia.
  unfold powm.
  rewrite Z.mod_1_l by lia.
  rewrite Z.mul_1_l, Z.mod_mod by lia. reflexivity.
Qed.

Fixpoint class_sum_from (P : list Z) (m r i : nat) : Z :=
  match P with
  | [] => 0
  | c :: rest =>
      (if Nat.eqb r (Nat.modulo i m) then c else 0)
      + class_sum_from rest m r (S i)
  end.

Definition class_sum (P : list Z) (m r : nat) : Z :=
  class_sum_from P m r 0%nat.

Definition poly_fold (P : list Z) (m : nat) : list Z :=
  map (fun r => class_sum P m r) (seq 0 m).

Lemma nth_map_seq_Z :
  forall (f : nat -> Z) (start len i : nat) (d : Z),
    (i < len)%nat ->
    nth i (map f (seq start len)) d = f (start + i)%nat.
Proof.
  intros f start len. revert start.
  induction len as [|len' IH]; intros start i d Hi.
  - lia.
  - simpl seq. rewrite map_cons.
    destruct i as [|i'].
    + simpl. f_equal. lia.
    + simpl nth. rewrite IH by lia. f_equal. lia.
Qed.

Lemma nth_poly_fold :
  forall P m r,
    (0 < m)%nat ->
    (r < m)%nat ->
    nth r (poly_fold P m) 0 = class_sum P m r.
Proof.
  intros P m r Hm Hr.
  unfold poly_fold, class_sum.
  rewrite nth_map_seq_Z by lia. reflexivity.
Qed.

Lemma poly_fold_length :
  forall P m, length (poly_fold P m) = m.
Proof.
  intros P m. unfold poly_fold. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma poly_degree_fold_lt :
  forall P m,
    (0 < m)%nat ->
    (poly_degree (poly_fold P m) < m)%nat.
Proof.
  intros P m Hm.
  destruct (poly_is_zero (poly_fold P m)) eqn:Hz.
  - rewrite poly_degree_zero by exact Hz. lia.
  - pose proof (poly_degree_leading (poly_fold P m) Hz) as Hnz.
    destruct (Nat.lt_ge_cases (poly_degree (poly_fold P m)) m) as [Hlt | Hge];
      [exact Hlt|].
    rewrite nth_overflow in Hnz; [contradiction|].
    rewrite poly_fold_length. exact Hge.
Qed.

Lemma map_plus_is_poly_add :
  forall (f g : nat -> Z) (xs : list nat),
    map (fun r => f r + g r) xs = poly_add (map f xs) (map g xs).
Proof.
  intros f g xs.
  induction xs as [|x rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma map_seq_succ :
  forall (f : nat -> Z) k m,
    map f (seq (S k) m) = map (fun r => f (S r)) (seq k m).
Proof.
  intros f k m. revert k.
  induction m as [|m IH]; intros k; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma poly_eval_map_seq_S :
  forall f m y,
    poly_eval (map f (seq 0 (S m))) y
      = f 0%nat + y * poly_eval (map (fun r => f (S r)) (seq 0 m)) y.
Proof.
  intros f m y.
  simpl seq. rewrite map_cons. simpl poly_eval.
  f_equal. f_equal.
  rewrite map_seq_succ. reflexivity.
Qed.

Lemma poly_eval_zeros_seq :
  forall m y,
    poly_eval (map (fun _ : nat => 0) (seq 0 m)) y = 0.
Proof.
  intros m y. induction m as [|m IH].
  - reflexivity.
  - rewrite poly_eval_map_seq_S, IH. ring.
Qed.

Lemma poly_eval_delta_seq :
  forall m k c y,
    (k < m)%nat ->
    poly_eval (map (fun r => if Nat.eqb r k then c else 0) (seq 0 m)) y
      = c * y ^ Z.of_nat k.
Proof.
  intros m k c y.
  revert k.
  induction m as [|m IH]; intros k Hk.
  - lia.
  - rewrite poly_eval_map_seq_S.
    destruct k as [|k'].
    + replace (Nat.eqb 0%nat 0%nat) with true by reflexivity.
      replace (map (fun r => if Nat.eqb (S r) 0%nat then c else 0) (seq 0 m))
        with (map (fun _ : nat => 0) (seq 0 m))
        by (apply map_ext; intros r; reflexivity).
      rewrite poly_eval_zeros_seq. rewrite Z.pow_0_r. ring.
    + replace (Nat.eqb 0%nat (S k')) with false by reflexivity.
      replace (map (fun r => if Nat.eqb (S r) (S k') then c else 0) (seq 0 m))
        with (map (fun r => if Nat.eqb r k' then c else 0) (seq 0 m))
        by (apply map_ext; intros r; reflexivity).
      rewrite (IH k') by lia.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Fixpoint poly_eval_from (P : list Z) (y : Z) (i : nat) : Z :=
  match P with
  | [] => 0
  | c :: rest => c * y ^ Z.of_nat i + poly_eval_from rest y (S i)
  end.

Lemma poly_eval_from_scale :
  forall P y i,
    poly_eval_from P y i = y ^ Z.of_nat i * poly_eval P y.
Proof.
  intros P y i.
  revert i.
  induction P as [|c rest IH]; intros i; simpl.
  - ring.
  - rewrite IH. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma poly_eval_from_0 :
  forall P y, poly_eval_from P y 0 = poly_eval P y.
Proof.
  intros P y. rewrite poly_eval_from_scale. rewrite Z.pow_0_r. ring.
Qed.

Lemma poly_eval_fold_from :
  forall P m i y n,
    1 < n ->
    (0 < m)%nat ->
    powm y (Z.of_nat m) n = 1 ->
    poly_eval_from P y i mod n
      = poly_eval (map (fun r => class_sum_from P m r i) (seq 0 m)) y mod n.
Proof.
  intros P m i y n Hn Hm Hper.
  revert i.
  induction P as [|c rest IH]; intros i.
  - simpl class_sum_from. rewrite poly_eval_zeros_seq. reflexivity.
  - simpl poly_eval_from. simpl class_sum_from.
    set (k := Nat.modulo i m).
    assert (Hk : (k < m)%nat) by (apply Nat.mod_upper_bound; lia).
    rewrite map_plus_is_poly_add, poly_eval_add.
    rewrite poly_eval_delta_seq by exact Hk.
    pose proof (IH (S i)) as IHs.
    apply (proj2 (mods_eq_iff_divides
                    (c * y ^ Z.of_nat i + poly_eval_from rest y (S i))
                    (c * y ^ Z.of_nat k
                       + poly_eval (map (fun r => class_sum_from rest m r (S i))
                                      (seq 0 m)) y)
                    n ltac:(lia))).
    replace (c * y ^ Z.of_nat i + poly_eval_from rest y (S i)
               - (c * y ^ Z.of_nat k
                    + poly_eval (map (fun r => class_sum_from rest m r (S i))
                                   (seq 0 m)) y))
      with ((c * y ^ Z.of_nat i - c * y ^ Z.of_nat k)
              + (poly_eval_from rest y (S i)
                   - poly_eval (map (fun r => class_sum_from rest m r (S i))
                                  (seq 0 m)) y)) by ring.
    apply Z.divide_add_r.
    + replace (c * y ^ Z.of_nat i - c * y ^ Z.of_nat k)
        with (c * (y ^ Z.of_nat i - y ^ Z.of_nat k)) by ring.
      apply Z.divide_mul_r.
      apply (proj1 (mods_eq_iff_divides (y ^ Z.of_nat i) (y ^ Z.of_nat k)
                      n ltac:(lia))).
      change ((y ^ Z.of_nat i) mod n) with (powm y (Z.of_nat i) n).
      change ((y ^ Z.of_nat k) mod n) with (powm y (Z.of_nat k) n).
      unfold k.
      transitivity (powm y (Z.of_nat i mod Z.of_nat m) n).
      -- apply powm_reduce_period; [lia | lia | lia | exact Hper].
      -- rewrite <- Nat2Z.inj_mod by lia. reflexivity.
    + apply (proj1 (mods_eq_iff_divides (poly_eval_from rest y (S i))
                      (poly_eval (map (fun r => class_sum_from rest m r (S i))
                                    (seq 0 m)) y)
                      n ltac:(lia))).
      exact IHs.
Qed.

Lemma poly_eval_fold_mod :
  forall P m y n,
    1 < n ->
    (0 < m)%nat ->
    powm y (Z.of_nat m) n = 1 ->
    poly_eval P y mod n = poly_eval (poly_fold P m) y mod n.
Proof.
  intros P m y n Hn Hm Hper.
  unfold poly_fold, class_sum.
  rewrite <- poly_eval_from_0.
  apply poly_eval_fold_from; assumption.
Qed.

Lemma pin_inv3_p_lt_pminus1 :
  (Z.to_nat pin_inv3_p < Z.to_nat (pin_p - 1))%nat.
Proof. vm_compute. lia. Qed.

Lemma invert_fold_p_diff_vanishes :
  forall P,
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    Forall (fun a => (pin_p | poly_eval
      (poly_sub (poly_fold P (Z.to_nat (pin_p - 1)))
                (poly_Xn (Z.to_nat pin_inv3_p))) a))
      pin_Fp_units_of_N.
Proof.
  intros P Hall.
  apply Forall_forall. intros a Hin.
  pose proof (pin_Fp_units_of_N_coprime a Hin) as Hcop.
  pose proof (invert_all_units_local_p P a Hall Hcop) as Hloc.
  pose proof (units_mod_prime_In pin_p a ltac:(lia) Hin) as Hb.
  pose proof pin_p_prime as Hp.
  pose proof (Z.prime_ge_2 _ Hp).
  assert (Hper : powm a (Z.of_nat (Z.to_nat (pin_p - 1))) pin_p = 1).
  { rewrite Z2Nat.id by lia. apply fermat_coprime; [exact Hp|].
    rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hp|].
    intros [k Hk]. nia. }
  unfold poly_sub.
  rewrite poly_eval_add, poly_eval_map_mul, poly_eval_Xn, Z2Nat.id by lia.
  replace (poly_eval (poly_fold P (Z.to_nat (pin_p - 1))) a
             + -1 * a ^ pin_inv3_p)
    with (poly_eval (poly_fold P (Z.to_nat (pin_p - 1))) a - a ^ pin_inv3_p)
    by ring.
  apply Z.mod_divide; [lia|].
  rewrite Zminus_mod.
  rewrite <- (poly_eval_fold_mod P (Z.to_nat (pin_p - 1)) a pin_p);
    [| lia | vm_compute; lia | exact Hper].
  rewrite Hloc. unfold powm. rewrite Z.sub_diag, Z.mod_0_l by lia.
  reflexivity.
Qed.

Theorem invert_all_units_fold_p :
  forall P r,
    (r < Z.to_nat (pin_p - 1))%nat ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    (pin_p | nth r (poly_sub (poly_fold P (Z.to_nat (pin_p - 1)))
                              (poly_Xn (Z.to_nat pin_inv3_p))) 0).
Proof.
  intros P r Hr Hall.
  apply (poly_prime_roots_divides pin_p pin_Fp_units_of_N
           (poly_sub (poly_fold P (Z.to_nat (pin_p - 1)))
                     (poly_Xn (Z.to_nat pin_inv3_p)))
           pin_p_prime pin_Fp_units_of_N_distinct).
  - pose proof (poly_degree_sub_le
                  (poly_fold P (Z.to_nat (pin_p - 1)))
                  (poly_Xn (Z.to_nat pin_inv3_p))) as Hs.
    rewrite poly_degree_Xn in Hs.
    rewrite pin_Fp_units_of_N_length.
    pose proof (poly_degree_fold_lt P (Z.to_nat (pin_p - 1))
                  ltac:(vm_compute; lia)).
    pose proof pin_inv3_p_lt_pminus1.
    lia.
  - apply invert_fold_p_diff_vanishes. exact Hall.
Qed.

Theorem invert_all_units_fold_p_is_local_monomial :
  forall P r,
    (r < Z.to_nat (pin_p - 1))%nat ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    class_sum P (Z.to_nat (pin_p - 1)) r mod pin_p
      = (if Nat.eqb r (Z.to_nat pin_inv3_p) then 1 else 0).
Proof.
  intros P r Hr Hall.
  pose proof (invert_all_units_fold_p P r Hr Hall) as Hdiv.
  rewrite nth_poly_sub, nth_Xn in Hdiv.
  rewrite nth_poly_fold in Hdiv; [| vm_compute; lia | exact Hr].
  destruct (Nat.eq_dec r (Z.to_nat pin_inv3_p)) as [Heq | Hne].
  - replace (Nat.eqb r (Z.to_nat pin_inv3_p)) with true
      by (symmetry; apply Nat.eqb_eq; exact Heq).
    apply (proj2 (mods_eq_iff_divides (class_sum P (Z.to_nat (pin_p - 1)) r) 1
                    pin_p ltac:(lia))).
    exact Hdiv.
  - replace (Nat.eqb r (Z.to_nat pin_inv3_p)) with false
      by (symmetry; apply Nat.eqb_neq; exact Hne).
    replace (class_sum P (Z.to_nat (pin_p - 1)) r - 0)
      with (class_sum P (Z.to_nat (pin_p - 1)) r) in Hdiv by lia.
    apply (proj2 (Z.mod_divide (class_sum P (Z.to_nat (pin_p - 1)) r)
                    pin_p ltac:(lia))) in Hdiv.
    exact Hdiv.
Qed.

(** ** Fermat correction [p(X^{q−1}−1)] splits

    The extra term is [0] on units of [N] ([p] divides it, and
    Fermat on [𝔽_q*] kills [X^{q−1}−1]), so the binomial plus
    this correction still inverts.  Degree is [q−1]; the new
    coefficient is [p], which splits.  [N]-multiples do not hide
    a splitting [gcd].  Cross-confirmed by [cas/178]. *)

Lemma gcd_add_mul :
  forall c k M, Z.gcd (c + k * M) M = Z.gcd c M.
Proof.
  intros c k M.
  rewrite (Z.gcd_comm (c + k * M) M), (Z.gcd_comm c M).
  apply Z.gcd_add_mult_diag_r.
Qed.

Definition pin_fermat_root_poly : list Z :=
  poly_add pin_crt_root_poly
    (map_mul pin_p (poly_Xn_minus_1 (Z.to_nat (pin_q - 1)))).

Lemma pin_fermat_extra_divides_N :
  forall y,
    Z.coprime y pin_N ->
    (pin_N | pin_p * (y ^ (pin_q - 1) - 1)).
Proof.
  intros y Hcop.
  pose proof pin_p_prime as Hp.
  pose proof pin_q_prime as Hq.
  pose proof (Z.prime_ge_2 _ Hp). pose proof (Z.prime_ge_2 _ Hq).
  apply coprime_semiprime in Hcop;
    [|exact Hp|exact Hq|apply pin_p_neq_q].
  destruct Hcop as [_ Hcopq].
  change pin_N with (pin_p * pin_q).
  apply divide_by_coprime_product.
  - apply prime_coprime_distinct; [exact Hp | exact Hq | apply pin_p_neq_q].
  - apply Z.divide_mul_l, Z.divide_refl.
  - apply Z.divide_mul_r.
    apply (proj1 (mods_eq_iff_divides (y ^ (pin_q - 1)) 1 pin_q ltac:(lia))).
    change ((y ^ (pin_q - 1)) mod pin_q) with (powm y (pin_q - 1) pin_q).
    rewrite (fermat_coprime pin_q y Hq Hcopq).
    symmetry. apply Z.mod_1_l. lia.
Qed.

Theorem pin_fermat_root_poly_inverts_units :
  forall y,
    Z.coprime y pin_N ->
    powm (poly_eval pin_fermat_root_poly y) pin_e pin_N = y mod pin_N.
Proof.
  intros y Hcop.
  unfold pin_fermat_root_poly.
  rewrite poly_eval_add, poly_eval_map_mul, poly_eval_Xn_minus_1, Z2Nat.id by lia.
  transitivity (powm (poly_eval pin_crt_root_poly y) pin_e pin_N).
  - apply powm_div_cong; [lia | lia |].
    replace (poly_eval pin_crt_root_poly y + pin_p * (y ^ (pin_q - 1) - 1)
               - poly_eval pin_crt_root_poly y)
      with (pin_p * (y ^ (pin_q - 1) - 1)) by ring.
    apply pin_fermat_extra_divides_N. exact Hcop.
  - apply pin_crt_binomial_inverts_units. exact Hcop.
Qed.

Theorem pin_fermat_root_poly_degree :
  poly_degree pin_fermat_root_poly = Z.to_nat (pin_q - 1).
Proof. vm_compute. reflexivity. Qed.

Theorem pin_fermat_root_poly_splits :
  exists i, 1 < Z.gcd (nth i pin_fermat_root_poly 0) pin_N < pin_N.
Proof.
  exists (Z.to_nat (pin_q - 1)).
  assert (Hg : Z.gcd (nth (Z.to_nat (pin_q - 1)) pin_fermat_root_poly 0) pin_N
                 = pin_p)
    by (vm_compute; reflexivity).
  rewrite Hg. split; lia.
Qed.

Theorem pin_gcd_add_mul_N :
  forall c k, Z.gcd (c + k * pin_N) pin_N = Z.gcd c pin_N.
Proof. intros c k. apply gcd_add_mul. Qed.

(** ** Fermat fold on [𝔽_q*] agrees on samples

    Only [q−2] samples (residue [p] is missing), so this is
    functional agreement of [fold_q] with [X^{d_q}], not a
    polynomial identity.  Cross-confirmed by [cas/179]. *)

Lemma pin_inv3_q_lt_qminus1 :
  (Z.to_nat pin_inv3_q < Z.to_nat (pin_q - 1))%nat.
Proof. vm_compute. lia. Qed.

Lemma invert_fold_q_diff_vanishes :
  forall P,
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    Forall (fun a => (pin_q | poly_eval
      (poly_sub (poly_fold P (Z.to_nat (pin_q - 1)))
                (poly_Xn (Z.to_nat pin_inv3_q))) a))
      pin_Fq_units_of_N.
Proof.
  intros P Hall.
  apply Forall_forall. intros a Hin.
  pose proof (pin_Fq_units_of_N_coprime a Hin) as Hcop.
  pose proof (invert_all_units_local_q P a Hall Hcop) as Hloc.
  pose proof pin_q_prime as Hq.
  pose proof (Z.prime_ge_2 _ Hq).
  assert (Hper : powm a (Z.of_nat (Z.to_nat (pin_q - 1))) pin_q = 1).
  { rewrite Z2Nat.id by lia. apply fermat_coprime; [exact Hq|].
    unfold pin_Fq_units_of_N in Hin.
    apply filter_In in Hin. destruct Hin as [HinU _].
    pose proof (units_mod_prime_In pin_q a ltac:(lia) HinU) as Hb.
    rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hq|].
    intros [k Hk]. nia. }
  unfold poly_sub.
  rewrite poly_eval_add, poly_eval_map_mul, poly_eval_Xn, Z2Nat.id by lia.
  replace (poly_eval (poly_fold P (Z.to_nat (pin_q - 1))) a
             + -1 * a ^ pin_inv3_q)
    with (poly_eval (poly_fold P (Z.to_nat (pin_q - 1))) a - a ^ pin_inv3_q)
    by ring.
  apply Z.mod_divide; [lia|].
  rewrite Zminus_mod.
  rewrite <- (poly_eval_fold_mod P (Z.to_nat (pin_q - 1)) a pin_q);
    [| lia | vm_compute; lia | exact Hper].
  rewrite Hloc. unfold powm. rewrite Z.sub_diag, Z.mod_0_l by lia.
  reflexivity.
Qed.

Theorem invert_all_units_fold_q_eval :
  forall P y,
    (forall z, Z.coprime z pin_N ->
       powm (poly_eval P z) pin_e pin_N = z mod pin_N) ->
    In y pin_Fq_units_of_N ->
    poly_eval (poly_fold P (Z.to_nat (pin_q - 1))) y mod pin_q
      = powm y pin_inv3_q pin_q.
Proof.
  intros P y Hall Hin.
  pose proof (invert_fold_q_diff_vanishes P Hall) as Hvan.
  rewrite Forall_forall in Hvan.
  specialize (Hvan y Hin).
  unfold poly_sub in Hvan.
  rewrite poly_eval_add, poly_eval_map_mul, poly_eval_Xn, Z2Nat.id in Hvan
    by lia.
  replace (poly_eval (poly_fold P (Z.to_nat (pin_q - 1))) y
             + -1 * y ^ pin_inv3_q)
    with (poly_eval (poly_fold P (Z.to_nat (pin_q - 1))) y - y ^ pin_inv3_q)
    in Hvan by ring.
  apply (proj2 (mods_eq_iff_divides
                  (poly_eval (poly_fold P (Z.to_nat (pin_q - 1))) y)
                  (y ^ pin_inv3_q) pin_q ltac:(lia))) in Hvan.
  unfold powm. exact Hvan.
Qed.

(** ** Top fold class [q−2] zero kills the [𝔽_q*] leftover

    [q−2] samples vs fold degree [≤ q−2] leaves a possible
    leftover.  If [q] divides the top class, strip it: the
    remainder has degree [< q−2] and the same roots, so
    [fold_q ≡ X^{d_q}] as polynomials modulo [q].
    Cross-confirmed by [cas/180]. *)

Lemma poly_degree_below_if_high_zero :
  forall P n,
    (0 < n)%nat ->
    (forall i, (n <= i)%nat -> nth i P 0 = 0) ->
    (poly_degree P < n)%nat.
Proof.
  intros P n Hn Hall.
  destruct (poly_is_zero P) eqn:Hz.
  - rewrite poly_degree_zero by exact Hz. lia.
  - pose proof (poly_degree_leading P Hz) as Hnz.
    destruct (Nat.lt_ge_cases (poly_degree P) n) as [Hlt | Hge];
      [exact Hlt|].
    rewrite Hall in Hnz; [contradiction | exact Hge].
Qed.

Lemma pin_inv3_q_neq_qminus2 :
  Z.to_nat pin_inv3_q <> Z.to_nat (pin_q - 2).
Proof. vm_compute. discriminate. Qed.

Theorem invert_all_units_fold_q_top_zero :
  forall P r,
    (pin_q | class_sum P (Z.to_nat (pin_q - 1)) (Z.to_nat (pin_q - 2))) ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    (r < Z.to_nat (pin_q - 1))%nat ->
    (pin_q | nth r (poly_sub (poly_fold P (Z.to_nat (pin_q - 1)))
                              (poly_Xn (Z.to_nat pin_inv3_q))) 0).
Proof.
  intros P r Htop Hall Hr.
  set (m := Z.to_nat (pin_q - 1)).
  set (top := Z.to_nat (pin_q - 2)).
  set (dq := Z.to_nat pin_inv3_q).
  set (F := poly_fold P m).
  set (D := poly_sub F (poly_Xn dq)).
  set (c := nth top D 0).
  set (D' := poly_sub D (map_mul c (poly_Xn top))).
  assert (Htoppos : (0 < top)%nat) by (vm_compute; lia).
  assert (Hmpos : (0 < m)%nat) by (vm_compute; lia).
  assert (Hcnth : c = class_sum P m top).
  { unfold c, D, F.
    rewrite nth_poly_sub, nth_Xn.
    destruct (Nat.eq_dec top dq) as [Hteq | Htne];
      [exfalso; apply pin_inv3_q_neq_qminus2; unfold top, dq in Hteq; symmetry; exact Hteq|].
    rewrite nth_poly_fold by (unfold m, top; try exact Hmpos; lia).
    lia. }
  assert (HqC : (pin_q | c)) by (rewrite Hcnth; exact Htop).
  assert (HvanD : Forall (fun a => (pin_q | poly_eval D a)) pin_Fq_units_of_N).
  { unfold D, F, m, dq. apply invert_fold_q_diff_vanishes. exact Hall. }
  assert (HvanD' : Forall (fun a => (pin_q | poly_eval D' a)) pin_Fq_units_of_N).
  { apply Forall_forall. intros a Hin.
    rewrite Forall_forall in HvanD.
    pose proof (HvanD a Hin) as Hd.
    unfold D', poly_sub.
    rewrite poly_eval_add, !poly_eval_map_mul, poly_eval_Xn.
    replace (poly_eval D a + -1 * (c * a ^ Z.of_nat top))
      with (poly_eval D a - c * a ^ Z.of_nat top) by ring.
    apply Z.divide_sub_r; [exact Hd | apply Z.divide_mul_l; exact HqC]. }
  assert (Hhigh : forall i, (top <= i)%nat -> nth i D' 0 = 0).
  { intros i Hi.
    unfold D', D, F.
    rewrite nth_poly_sub, nth_map_mul, nth_Xn.
    rewrite nth_poly_sub, nth_Xn.
    destruct (Nat.eq_dec i top) as [Hit | Hnit].
    - subst i.
      destruct (Nat.eq_dec top dq) as [Hteq | Htne];
        [exfalso; apply pin_inv3_q_neq_qminus2; unfold top, dq in Hteq; symmetry; exact Hteq|].
      rewrite nth_poly_fold by (unfold m, top; try exact Hmpos; lia).
      unfold c, D, F. rewrite nth_poly_sub, nth_Xn.
      destruct (Nat.eq_dec top dq) as [Hteq2 | Htne2];
        [exfalso; apply pin_inv3_q_neq_qminus2; unfold top, dq in Hteq2; symmetry; exact Hteq2|].
      rewrite nth_poly_fold by (unfold m, top; try exact Hmpos; lia).
      ring.
    - destruct (Nat.eq_dec i dq) as [Hid | Hnid].
      + subst i. pose proof pin_inv3_q_lt_window. unfold top, dq in *. lia.
      + rewrite nth_overflow with (l := F).
        2: { unfold F. rewrite poly_fold_length. unfold m, top in *. lia. }
        ring. }
  pose proof (poly_degree_below_if_high_zero D' top Htoppos Hhigh) as Hdeg'.
  assert (Hdiv' : forall i, (pin_q | nth i D' 0)).
  { apply (poly_prime_roots_divides pin_q pin_Fq_units_of_N D'
             pin_q_prime pin_Fq_units_of_N_distinct).
    - rewrite pin_Fq_units_of_N_length. unfold top in Hdeg'. lia.
    - exact HvanD'. }
  change (poly_sub (poly_fold P (Z.to_nat (pin_q - 1)))
            (poly_Xn (Z.to_nat pin_inv3_q)))
    with D.
  replace (nth r D 0) with (nth r D' 0 + c * nth r (poly_Xn top) 0).
  2: { unfold D'. rewrite nth_poly_sub, nth_map_mul. ring. }
  apply Z.divide_add_r.
  - apply Hdiv'.
  - apply Z.divide_mul_l. exact HqC.
Qed.

Theorem invert_all_units_fold_q_is_local_monomial :
  forall P r,
    (pin_q | class_sum P (Z.to_nat (pin_q - 1)) (Z.to_nat (pin_q - 2))) ->
    (r < Z.to_nat (pin_q - 1))%nat ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    class_sum P (Z.to_nat (pin_q - 1)) r mod pin_q
      = (if Nat.eqb r (Z.to_nat pin_inv3_q) then 1 else 0).
Proof.
  intros P r Htop Hr Hall.
  pose proof (invert_all_units_fold_q_top_zero P r Htop Hall Hr) as Hdiv.
  rewrite nth_poly_sub, nth_Xn in Hdiv.
  rewrite nth_poly_fold in Hdiv; [| vm_compute; lia | exact Hr].
  destruct (Nat.eq_dec r (Z.to_nat pin_inv3_q)) as [Heq | Hne].
  - replace (Nat.eqb r (Z.to_nat pin_inv3_q)) with true
      by (symmetry; apply Nat.eqb_eq; exact Heq).
    apply (proj2 (mods_eq_iff_divides (class_sum P (Z.to_nat (pin_q - 1)) r) 1
                    pin_q ltac:(lia))).
    exact Hdiv.
  - replace (Nat.eqb r (Z.to_nat pin_inv3_q)) with false
      by (symmetry; apply Nat.eqb_neq; exact Hne).
    replace (class_sum P (Z.to_nat (pin_q - 1)) r - 0)
      with (class_sum P (Z.to_nat (pin_q - 1)) r) in Hdiv by lia.
    apply (proj2 (Z.mod_divide (class_sum P (Z.to_nat (pin_q - 1)) r)
                    pin_q ltac:(lia))) in Hdiv.
    exact Hdiv.
Qed.

(** ** Invert-all-units monomial degree is [d] mod [λ]

    [e k ≡ 1 (mod λ)] and [e d ≡ 1 (mod λ)], so [k ≡ d (mod λ)]
    by uniqueness of the inverse.  Writing such a [k] wrote [d].
    Not [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/181]. *)

Theorem invert_all_units_monomial_degree_mod_lam :
  forall k,
    0 <= k ->
    (forall y, Z.coprime y pin_N ->
       powm (powm y k pin_N) pin_e pin_N = y mod pin_N) ->
    k mod pin_lam = pin_d.
Proof.
  intros k Hk Hall.
  pose proof (monomial_all_units_invert_is_trapdoor k Hk Hall) as Hinv.
  transitivity (pin_d mod pin_lam); [| vm_compute; reflexivity].
  apply (inverse_unique_mod pin_e k pin_d pin_lam);
    [lia | exact Hinv | apply pin_trapdoor_ed_inv].
Qed.

(** ** Evaluation congruence and the geometric kernel

    [n | x − y] implies [n] divides [P(x) − P(y)].  The geometric
    sum [K_n = Σ_{j=0}^{n} base^j X^{n−j}] satisfies
    [(a − base) K_n(a) = a^{n+1} − base^{n+1}].  Cross-confirmed
    by [cas/182] and [cas/183]. *)

Lemma poly_eval_cong :
  forall P x y n,
    0 < n ->
    (n | x - y) ->
    (n | poly_eval P x - poly_eval P y).
Proof.
  intros P x y n Hn Hdiv.
  induction P as [|c rest IH]; simpl.
  - apply Z.divide_0_r.
  - replace (c + x * poly_eval rest x - (c + y * poly_eval rest y))
      with (x * (poly_eval rest x - poly_eval rest y)
            + (x - y) * poly_eval rest y) by ring.
    apply Z.divide_add_r.
    + apply Z.divide_mul_r. exact IH.
    + apply Z.divide_mul_l. exact Hdiv.
Qed.

Lemma poly_eval_app :
  forall a b x,
    poly_eval (a ++ b) x =
      poly_eval a x + x ^ Z.of_nat (length a) * poly_eval b x.
Proof.
  intros a b x.
  induction a as [|ha ta IH].
  - cbn [app poly_eval length].
    replace (x ^ Z.of_nat 0%nat) with 1 by (rewrite Z.pow_0_r; reflexivity).
    ring.
  - cbn [app poly_eval length].
    rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma map_mul_length :
  forall k cs, length (map_mul k cs) = length cs.
Proof.
  intros k cs. induction cs as [|c rest IH]; simpl; lia.
Qed.

Fixpoint geo_kernel (base : Z) (n : nat) : list Z :=
  match n with
  | O => [1]
  | S n' => map_mul base (geo_kernel base n') ++ [1]
  end.

Lemma geo_kernel_length :
  forall base n, length (geo_kernel base n) = S n.
Proof.
  intros base n.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite length_app, map_mul_length, IH. simpl. lia.
Qed.

Lemma geo_kernel_identity :
  forall base a n,
    (a - base) * poly_eval (geo_kernel base n) a
      = a ^ Z.of_nat (S n) - base ^ Z.of_nat (S n).
Proof.
  intros base a n.
  induction n as [|n IH].
  - cbn [geo_kernel poly_eval]. rewrite !Z.pow_1_r. ring.
  - cbn [geo_kernel].
    rewrite poly_eval_app, poly_eval_map_mul, map_mul_length, geo_kernel_length.
    change (poly_eval [1] a) with (1 + a * 0).
    replace (1 + a * 0) with 1 by ring.
    replace ((a - base)
               * (base * poly_eval (geo_kernel base n) a
                    + a ^ Z.of_nat (S n) * 1))
      with (base * ((a - base) * poly_eval (geo_kernel base n) a)
            + (a - base) * a ^ Z.of_nat (S n)) by ring.
    rewrite IH.
    rewrite (Nat2Z.inj_succ (S n)), !Z.pow_succ_r by lia.
    ring.
Qed.

Lemma geo_kernel_at_base :
  forall base n,
    poly_eval (geo_kernel base n) base
      = (Z.of_nat n + 1) * base ^ Z.of_nat n.
Proof.
  intros base n.
  induction n as [|n IH].
  - cbn [geo_kernel poly_eval].
    replace (base ^ Z.of_nat 0%nat) with 1 by (rewrite Z.pow_0_r; reflexivity).
    ring.
  - cbn [geo_kernel].
    rewrite poly_eval_app, poly_eval_map_mul, map_mul_length, geo_kernel_length.
    change (poly_eval [1] base) with (1 + base * 0).
    replace (1 + base * 0) with 1 by ring.
    rewrite IH.
    rewrite (Nat2Z.inj_succ n), !Z.pow_succ_r by lia.
    ring.
Qed.

(** ** [p+q] is a unit of [N] lifting residue [p]

    Campaign pins have [p < q], so residue [p] is missing from the
    canonical [𝔽_q*] samples used as units of [N].  [p+q] is coprime
    to [N] and [p+q ≡ p (mod q)], so it fills that sample.
    Cross-confirmed by [cas/182]. *)

Lemma p_plus_q_coprime :
  forall p q,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    Z.coprime (p + q) (p * q).
Proof.
  intros p q Hp Hq Hneq.
  apply (proj2 (coprime_semiprime p q (p + q) Hp Hq Hneq)).
  split.
  - unfold Z.coprime.
    replace (p + q) with (q + 1 * p) by ring.
    rewrite gcd_add_mul, Z.gcd_comm.
    apply prime_coprime_distinct; [exact Hp | exact Hq | exact Hneq].
  - unfold Z.coprime.
    replace (p + q) with (p + 1 * q) by ring.
    rewrite gcd_add_mul.
    apply prime_coprime_distinct; [exact Hp | exact Hq | exact Hneq].
Qed.

Lemma p_plus_q_mod_q :
  forall p q, 0 < q -> 0 <= p < q -> (p + q) mod q = p.
Proof.
  intros p q Hq Hp.
  rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod, Z.mod_small; lia.
Qed.

Lemma pin_p_plus_q_coprime :
  Z.coprime (pin_p + pin_q) pin_N.
Proof.
  change pin_N with (pin_p * pin_q).
  apply p_plus_q_coprime;
    [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q].
Qed.

Lemma pin_p_plus_q_mod_q :
  (pin_p + pin_q) mod pin_q = pin_p.
Proof.
  apply p_plus_q_mod_q; [lia | split; [lia | apply pin_p_lt_q]].
Qed.

Definition pin_geo_kernel : list Z :=
  geo_kernel pin_p (Z.to_nat (pin_q - 2)).

Lemma pin_geo_kernel_vanishes :
  Forall (fun a => (pin_q | poly_eval pin_geo_kernel a)) pin_Fq_units_of_N.
Proof.
  apply Forall_forall. intros a Hin.
  unfold pin_Fq_units_of_N in Hin.
  apply filter_In in Hin. destruct Hin as [HinU Hne].
  apply negb_true_iff, Z.eqb_neq in Hne.
  pose proof (units_mod_prime_In pin_q a ltac:(lia) HinU) as Hb.
  pose proof pin_q_prime as Hq.
  pose proof pin_p_prime as Hp.
  pose proof (Z.prime_ge_2 _ Hq). pose proof (Z.prime_ge_2 _ Hp).
  pose proof pin_p_lt_q as Hlt.
  pose proof (geo_kernel_identity pin_p a (Z.to_nat (pin_q - 2))) as Hid.
  unfold pin_geo_kernel.
  rewrite Nat2Z.inj_succ, Z2Nat.id in Hid by lia.
  replace (Z.succ (pin_q - 2)) with (pin_q - 1) in Hid by lia.
  assert (Hfa : powm a (pin_q - 1) pin_q = 1).
  { apply fermat_coprime; [exact Hq|].
    rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hq|].
    intros [k Hk]. nia. }
  assert (Hfp : powm pin_p (pin_q - 1) pin_q = 1).
  { apply fermat_coprime; [exact Hq|].
    apply prime_coprime_distinct; [exact Hp | exact Hq | apply pin_p_neq_q]. }
  assert (Hdiff : (pin_q | a ^ (pin_q - 1) - pin_p ^ (pin_q - 1))).
  { apply Z.mod_divide; [lia|].
    rewrite Zminus_mod.
    change ((a ^ (pin_q - 1)) mod pin_q)
      with (powm a (pin_q - 1) pin_q).
    change ((pin_p ^ (pin_q - 1)) mod pin_q)
      with (powm pin_p (pin_q - 1) pin_q).
    rewrite Hfa, Hfp, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity. }
  apply (Z.gauss pin_q (a - pin_p) (poly_eval (geo_kernel pin_p (Z.to_nat (pin_q - 2))) a)).
  - rewrite Hid. exact Hdiff.
  - unfold Z.coprime.
    apply Z.coprime_prime_l_iff; [exact Hq|].
    intros Hqp.
    apply (proj2 (mods_eq_iff_divides a pin_p pin_q ltac:(lia))) in Hqp.
    rewrite !Z.mod_small in Hqp; [contradiction | lia | lia].
Qed.

Theorem pin_geo_kernel_at_p_nonzero :
  poly_eval pin_geo_kernel pin_p mod pin_q <> 0.
Proof. vm_compute. discriminate. Qed.

Theorem pin_p_Kp_mod_q_nonzero :
  (pin_p * poly_eval pin_geo_kernel pin_p) mod pin_q <> 0.
Proof. vm_compute. discriminate. Qed.

Theorem pin_geo_kernel_at_2_mod_p :
  poly_eval pin_geo_kernel 2 mod pin_p = powm 2 (pin_q - 2) pin_p.
Proof. vm_compute. reflexivity. Qed.

Theorem pin_two_pow_qminus2_mod_p_nonzero :
  powm 2 (pin_q - 2) pin_p <> 0.
Proof. vm_compute. discriminate. Qed.

Definition pin_binomial_plus_kernel : list Z :=
  poly_add pin_crt_root_poly pin_geo_kernel.

Theorem pin_binomial_plus_kernel_misses_lift :
  powm (poly_eval pin_binomial_plus_kernel (pin_p + pin_q)) pin_e pin_N
    <> (pin_p + pin_q) mod pin_N.
Proof. vm_compute. discriminate. Qed.

(** ** Invert-all-units fills the missing [𝔽_q*] sample

    An all-units invert poly matches [X^{d_q}] at the lift [p+q],
    hence at residue [p] by evaluation congruence.  Together with
    the canonical [q−2] samples that is all of [𝔽_q*], so
    [fold_q ≡ X^{d_q}] as polynomials: leftover killed, no extra
    top-zero hypothesis.  Cross-confirmed by [cas/184] and
    [cas/185]. *)

Lemma pin_Fq_units_or_p :
  forall a,
    In a (units_mod_prime pin_q) ->
    a = pin_p \/ In a pin_Fq_units_of_N.
Proof.
  intros a Hin.
  unfold pin_Fq_units_of_N.
  destruct (a =? pin_p) eqn:Heq.
  - left. apply Z.eqb_eq. exact Heq.
  - right. apply filter_In. split; [exact Hin|].
    apply negb_true_iff. exact Heq.
Qed.

Lemma invert_fold_q_at_lift :
  forall P y,
    (forall z, Z.coprime z pin_N ->
       powm (poly_eval P z) pin_e pin_N = z mod pin_N) ->
    Z.coprime y pin_N ->
    y mod pin_q = pin_p ->
    (pin_q | poly_eval
      (poly_sub (poly_fold P (Z.to_nat (pin_q - 1)))
                (poly_Xn (Z.to_nat pin_inv3_q))) pin_p).
Proof.
  intros P y Hall Hcop Hmod.
  pose proof (invert_all_units_local_q P y Hall Hcop) as Hloc.
  pose proof pin_q_prime as Hq.
  pose proof pin_p_prime as Hp.
  pose proof (Z.prime_ge_2 _ Hq). pose proof (Z.prime_ge_2 _ Hp).
  pose proof pin_p_lt_q as Hlt.
  assert (Hydiv : (pin_q | y - pin_p)).
  { apply (proj1 (mods_eq_iff_divides y pin_p pin_q ltac:(lia))).
    rewrite (Z.mod_small pin_p pin_q) by lia. exact Hmod. }
  assert (Hper : powm y (Z.of_nat (Z.to_nat (pin_q - 1))) pin_q = 1).
  { rewrite Z2Nat.id by lia.
    apply fermat_coprime; [exact Hq|].
    pose proof Hcop as HcopN.
    change pin_N with (pin_p * pin_q) in HcopN.
    apply coprime_semiprime in HcopN;
      [destruct HcopN as [_ Hcopq]; exact Hcopq
      |exact Hp|exact Hq|apply pin_p_neq_q]. }
  unfold poly_sub.
  rewrite poly_eval_add, poly_eval_map_mul, poly_eval_Xn, Z2Nat.id by lia.
  replace (poly_eval (poly_fold P (Z.to_nat (pin_q - 1))) pin_p
             + -1 * pin_p ^ pin_inv3_q)
    with (poly_eval (poly_fold P (Z.to_nat (pin_q - 1))) pin_p
            - pin_p ^ pin_inv3_q) by ring.
  apply Z.mod_divide; [lia|].
  rewrite Zminus_mod.
  assert (HcongF :
            poly_eval (poly_fold P (Z.to_nat (pin_q - 1))) pin_p mod pin_q
              = poly_eval (poly_fold P (Z.to_nat (pin_q - 1))) y mod pin_q).
  { apply (proj2 (mods_eq_iff_divides
                    (poly_eval (poly_fold P (Z.to_nat (pin_q - 1))) pin_p)
                    (poly_eval (poly_fold P (Z.to_nat (pin_q - 1))) y)
                    pin_q ltac:(lia))).
    apply poly_eval_cong; [lia|].
    replace (pin_p - y) with (- (y - pin_p)) by ring.
    apply Z.divide_opp_r. exact Hydiv. }
  assert (HcongX :
            pin_p ^ pin_inv3_q mod pin_q = y ^ pin_inv3_q mod pin_q).
  { apply (proj2 (mods_eq_iff_divides (pin_p ^ pin_inv3_q) (y ^ pin_inv3_q)
                    pin_q ltac:(lia))).
    replace (pin_p ^ pin_inv3_q)
      with (poly_eval (poly_Xn (Z.to_nat pin_inv3_q)) pin_p)
      by (rewrite poly_eval_Xn, Z2Nat.id; [reflexivity | lia]).
    replace (y ^ pin_inv3_q)
      with (poly_eval (poly_Xn (Z.to_nat pin_inv3_q)) y)
      by (rewrite poly_eval_Xn, Z2Nat.id; [reflexivity | lia]).
    apply poly_eval_cong; [lia|].
    replace (pin_p - y) with (- (y - pin_p)) by ring.
    apply Z.divide_opp_r. exact Hydiv. }
  rewrite HcongF, HcongX.
  rewrite <- (poly_eval_fold_mod P (Z.to_nat (pin_q - 1)) y pin_q);
    [| lia | vm_compute; lia | exact Hper].
  rewrite Hloc. unfold powm. rewrite Z.sub_diag, Z.mod_0_l by lia.
  reflexivity.
Qed.

Lemma invert_fold_q_at_p :
  forall P,
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    (pin_q | poly_eval
      (poly_sub (poly_fold P (Z.to_nat (pin_q - 1)))
                (poly_Xn (Z.to_nat pin_inv3_q))) pin_p).
Proof.
  intros P Hall.
  apply (invert_fold_q_at_lift P (pin_p + pin_q) Hall);
    [apply pin_p_plus_q_coprime | apply pin_p_plus_q_mod_q].
Qed.

Lemma invert_fold_q_diff_vanishes_all :
  forall P,
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    Forall (fun a => (pin_q | poly_eval
      (poly_sub (poly_fold P (Z.to_nat (pin_q - 1)))
                (poly_Xn (Z.to_nat pin_inv3_q))) a))
      (units_mod_prime pin_q).
Proof.
  intros P Hall.
  apply Forall_forall. intros a Hin.
  destruct (pin_Fq_units_or_p a Hin) as [Heq | Hin'].
  - subst a. apply invert_fold_q_at_p. exact Hall.
  - pose proof (invert_fold_q_diff_vanishes P Hall) as Hvan.
    rewrite Forall_forall in Hvan. apply Hvan. exact Hin'.
Qed.

Theorem invert_all_units_fold_q :
  forall P r,
    (r < Z.to_nat (pin_q - 1))%nat ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    (pin_q | nth r (poly_sub (poly_fold P (Z.to_nat (pin_q - 1)))
                              (poly_Xn (Z.to_nat pin_inv3_q))) 0).
Proof.
  intros P r Hr Hall.
  apply (poly_prime_roots_divides pin_q (units_mod_prime pin_q)
           (poly_sub (poly_fold P (Z.to_nat (pin_q - 1)))
                     (poly_Xn (Z.to_nat pin_inv3_q)))
           pin_q_prime (units_mod_prime_distinct pin_q pin_q_prime)).
  - pose proof (poly_degree_sub_le
                  (poly_fold P (Z.to_nat (pin_q - 1)))
                  (poly_Xn (Z.to_nat pin_inv3_q))) as Hs.
    rewrite poly_degree_Xn in Hs.
    rewrite units_mod_prime_length by lia.
    pose proof (poly_degree_fold_lt P (Z.to_nat (pin_q - 1))
                  ltac:(vm_compute; lia)).
    pose proof pin_inv3_q_lt_qminus1.
    lia.
  - apply invert_fold_q_diff_vanishes_all. exact Hall.
Qed.

Theorem invert_all_units_fold_q_classes :
  forall P r,
    (r < Z.to_nat (pin_q - 1))%nat ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    class_sum P (Z.to_nat (pin_q - 1)) r mod pin_q
      = (if Nat.eqb r (Z.to_nat pin_inv3_q) then 1 else 0).
Proof.
  intros P r Hr Hall.
  pose proof (invert_all_units_fold_q P r Hr Hall) as Hdiv.
  rewrite nth_poly_sub, nth_Xn in Hdiv.
  rewrite nth_poly_fold in Hdiv; [| vm_compute; lia | exact Hr].
  destruct (Nat.eq_dec r (Z.to_nat pin_inv3_q)) as [Heq | Hne].
  - replace (Nat.eqb r (Z.to_nat pin_inv3_q)) with true
      by (symmetry; apply Nat.eqb_eq; exact Heq).
    apply (proj2 (mods_eq_iff_divides (class_sum P (Z.to_nat (pin_q - 1)) r) 1
                    pin_q ltac:(lia))).
    exact Hdiv.
  - replace (Nat.eqb r (Z.to_nat pin_inv3_q)) with false
      by (symmetry; apply Nat.eqb_neq; exact Hne).
    replace (class_sum P (Z.to_nat (pin_q - 1)) r - 0)
      with (class_sum P (Z.to_nat (pin_q - 1)) r) in Hdiv by lia.
    apply (proj2 (Z.mod_divide (class_sum P (Z.to_nat (pin_q - 1)) r)
                    pin_q ltac:(lia))) in Hdiv.
    exact Hdiv.
Qed.

Lemma invert_fold_p_diff_vanishes_semiprime :
  forall p q e da P,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    0 < e ->
    0 <= da ->
    (e * da) mod (p - 1) = 1 ->
    (forall y, Z.coprime y (p * q) ->
       powm (poly_eval P y) e (p * q) = y mod (p * q)) ->
    Forall (fun a => (p | poly_eval
      (poly_sub (poly_fold P (Z.to_nat (p - 1)))
                (poly_Xn (Z.to_nat da))) a))
      (units_mod_prime p).
Proof.
  intros p q e da P Hp Hq Hneq Hlt He Hd Hinv Hall.
  pose proof (Z.prime_ge_2 _ Hp). pose proof (Z.prime_ge_2 _ Hq).
  apply Forall_forall. intros a Hin.
  pose proof (fp_units_of_N_coprime p q a Hp Hq Hneq Hlt Hin) as Hcop.
  pose proof (Hall a Hcop) as Hroot.
  pose proof (short_root_local_at_p p q e da P a Hp Hq Hneq He Hd Hinv Hcop Hroot)
    as Hloc.
  pose proof (units_mod_prime_In p a ltac:(lia) Hin) as Hb.
  assert (Hper : powm a (Z.of_nat (Z.to_nat (p - 1))) p = 1).
  { rewrite Z2Nat.id by lia. apply fermat_coprime; [exact Hp|].
    rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hp|].
    intros [k Hk]. destruct k as [|k|k]; nia. }
  unfold poly_sub.
  rewrite poly_eval_add, poly_eval_map_mul, poly_eval_Xn, Z2Nat.id by lia.
  replace (poly_eval (poly_fold P (Z.to_nat (p - 1))) a
             + -1 * a ^ da)
    with (poly_eval (poly_fold P (Z.to_nat (p - 1))) a - a ^ da)
    by ring.
  apply Z.mod_divide; [lia|].
  rewrite Zminus_mod.
  rewrite <- (poly_eval_fold_mod P (Z.to_nat (p - 1)) a p);
    [| lia | | exact Hper].
  2: { apply Nat2Z.inj_lt. rewrite Z2Nat.id; lia. }
  rewrite Hloc. unfold powm. rewrite Z.sub_diag, Z.mod_0_l by lia.
  reflexivity.
Qed.

Lemma invert_all_units_fold_p_semiprime :
  forall p q e da P r,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    0 < e ->
    0 <= da < p - 1 ->
    (e * da) mod (p - 1) = 1 ->
    (r < Z.to_nat (p - 1))%nat ->
    (forall y, Z.coprime y (p * q) ->
       powm (poly_eval P y) e (p * q) = y mod (p * q)) ->
    (p | nth r (poly_sub (poly_fold P (Z.to_nat (p - 1)))
                          (poly_Xn (Z.to_nat da))) 0).
Proof.
  intros p q e da P r Hp Hq Hneq Hlt He Hd Hinv Hr Hall.
  pose proof (Z.prime_ge_2 _ Hp).
  apply (poly_prime_roots_divides p (units_mod_prime p)
           (poly_sub (poly_fold P (Z.to_nat (p - 1)))
                     (poly_Xn (Z.to_nat da)))
           Hp (units_mod_prime_distinct p Hp)).
  - pose proof (poly_degree_sub_le
                  (poly_fold P (Z.to_nat (p - 1)))
                  (poly_Xn (Z.to_nat da))) as Hs.
    rewrite poly_degree_Xn in Hs.
    rewrite units_mod_prime_length by lia.
    pose proof (poly_degree_fold_lt P (Z.to_nat (p - 1))).
    assert (0 < Z.to_nat (p - 1))%nat by (apply Nat2Z.inj_lt; rewrite Z2Nat.id; lia).
    pose proof (Z2Nat.inj_lt da (p - 1) ltac:(lia) ltac:(lia)).
    lia.
  - apply (invert_fold_p_diff_vanishes_semiprime p q e da P);
      [exact Hp | exact Hq | exact Hneq | exact Hlt | exact He
       | lia | exact Hinv | exact Hall].
Qed.

Lemma invert_all_units_fold_p_classes_semiprime :
  forall p q e da P r,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    0 < e ->
    0 <= da < p - 1 ->
    (e * da) mod (p - 1) = 1 ->
    (r < Z.to_nat (p - 1))%nat ->
    (forall y, Z.coprime y (p * q) ->
       powm (poly_eval P y) e (p * q) = y mod (p * q)) ->
    class_sum P (Z.to_nat (p - 1)) r mod p
      = (if Nat.eqb r (Z.to_nat da) then 1 else 0).
Proof.
  intros p q e da P r Hp Hq Hneq Hlt He Hd Hinv Hr Hall.
  pose proof (Z.prime_ge_2 _ Hp).
  pose proof (invert_all_units_fold_p_semiprime p q e da P r
                Hp Hq Hneq Hlt He Hd Hinv Hr Hall) as Hdiv.
  rewrite nth_poly_sub, nth_Xn in Hdiv.
  assert (Hm : (0 < Z.to_nat (p - 1))%nat)
    by (apply Nat2Z.inj_lt; rewrite Z2Nat.id; lia).
  rewrite nth_poly_fold in Hdiv; [| exact Hm | exact Hr].
  destruct (Nat.eq_dec r (Z.to_nat da)) as [Heq | Hne].
  - replace (Nat.eqb r (Z.to_nat da)) with true
      by (symmetry; apply Nat.eqb_eq; exact Heq).
    transitivity (1 mod p).
    + apply (proj2 (mods_eq_iff_divides (class_sum P (Z.to_nat (p - 1)) r) 1
                      p ltac:(lia))).
      exact Hdiv.
    + apply Z.mod_1_l. lia.
  - replace (Nat.eqb r (Z.to_nat da)) with false
      by (symmetry; apply Nat.eqb_neq; exact Hne).
    replace (class_sum P (Z.to_nat (p - 1)) r - 0)
      with (class_sum P (Z.to_nat (p - 1)) r) in Hdiv by lia.
    apply (proj2 (Z.mod_divide (class_sum P (Z.to_nat (p - 1)) r)
                    p ltac:(lia))) in Hdiv.
    exact Hdiv.
Qed.

Lemma invert_fold_q_diff_vanishes_semiprime :
  forall p q e dq P,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    q < 2 * p ->
    0 < e ->
    0 <= dq ->
    (e * dq) mod (q - 1) = 1 ->
    (forall y, Z.coprime y (p * q) ->
       powm (poly_eval P y) e (p * q) = y mod (p * q)) ->
    Forall (fun a => (q | poly_eval
      (poly_sub (poly_fold P (Z.to_nat (q - 1)))
                (poly_Xn (Z.to_nat dq))) a))
      (fq_units_of_N p q).
Proof.
  intros p q e dq P Hp Hq Hneq Hlt Hqp He Hd Hinv Hall.
  pose proof (Z.prime_ge_2 _ Hq). pose proof (Z.prime_ge_2 _ Hp).
  apply Forall_forall. intros a Hin.
  pose proof (fq_units_of_N_coprime p q a Hp Hq Hneq Hlt Hqp Hin) as Hcop.
  pose proof (Hall a Hcop) as Hroot.
  pose proof (short_root_local_at_q p q e dq P a Hp Hq Hneq He Hd Hinv Hcop Hroot)
    as Hloc.
  unfold fq_units_of_N in Hin.
  apply filter_In in Hin. destruct Hin as [HinU _].
  pose proof (units_mod_prime_In q a ltac:(lia) HinU) as Hb.
  assert (Hper : powm a (Z.of_nat (Z.to_nat (q - 1))) q = 1).
  { rewrite Z2Nat.id by lia. apply fermat_coprime; [exact Hq|].
    rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hq|].
    intros [k Hk]. destruct k as [|k|k]; nia. }
  unfold poly_sub.
  rewrite poly_eval_add, poly_eval_map_mul, poly_eval_Xn, Z2Nat.id by lia.
  replace (poly_eval (poly_fold P (Z.to_nat (q - 1))) a
             + -1 * a ^ dq)
    with (poly_eval (poly_fold P (Z.to_nat (q - 1))) a - a ^ dq)
    by ring.
  apply Z.mod_divide; [lia|].
  rewrite Zminus_mod.
  rewrite <- (poly_eval_fold_mod P (Z.to_nat (q - 1)) a q);
    [| lia | | exact Hper].
  2: { apply Nat2Z.inj_lt. rewrite Z2Nat.id; lia. }
  rewrite Hloc. unfold powm. rewrite Z.sub_diag, Z.mod_0_l by lia.
  reflexivity.
Qed.

Lemma invert_fold_q_at_lift_semiprime :
  forall p q e dq P y,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    0 < e ->
    0 <= dq ->
    (e * dq) mod (q - 1) = 1 ->
    (forall z, Z.coprime z (p * q) ->
       powm (poly_eval P z) e (p * q) = z mod (p * q)) ->
    Z.coprime y (p * q) ->
    y mod q = p ->
    (q | poly_eval
      (poly_sub (poly_fold P (Z.to_nat (q - 1)))
                (poly_Xn (Z.to_nat dq))) p).
Proof.
  intros p q e dq P y Hp Hq Hneq Hlt He Hd Hinv Hall Hcop Hmod.
  pose proof (Z.prime_ge_2 _ Hq). pose proof (Z.prime_ge_2 _ Hp).
  pose proof (Hall y Hcop) as Hroot.
  pose proof (short_root_local_at_q p q e dq P y Hp Hq Hneq He Hd Hinv Hcop Hroot)
    as Hloc.
  assert (Hydiv : (q | y - p)).
  { apply (proj1 (mods_eq_iff_divides y p q ltac:(lia))).
    rewrite (Z.mod_small p q) by lia. exact Hmod. }
  assert (Hper : powm y (Z.of_nat (Z.to_nat (q - 1))) q = 1).
  { rewrite Z2Nat.id by lia.
    apply fermat_coprime; [exact Hq|].
    apply coprime_semiprime in Hcop; [|exact Hp|exact Hq|exact Hneq].
    destruct Hcop as [_ Hcopq]. exact Hcopq. }
  unfold poly_sub.
  rewrite poly_eval_add, poly_eval_map_mul, poly_eval_Xn, Z2Nat.id by lia.
  replace (poly_eval (poly_fold P (Z.to_nat (q - 1))) p
             + -1 * p ^ dq)
    with (poly_eval (poly_fold P (Z.to_nat (q - 1))) p - p ^ dq) by ring.
  apply Z.mod_divide; [lia|].
  rewrite Zminus_mod.
  assert (HcongF :
            poly_eval (poly_fold P (Z.to_nat (q - 1))) p mod q
              = poly_eval (poly_fold P (Z.to_nat (q - 1))) y mod q).
  { apply (proj2 (mods_eq_iff_divides
                    (poly_eval (poly_fold P (Z.to_nat (q - 1))) p)
                    (poly_eval (poly_fold P (Z.to_nat (q - 1))) y)
                    q ltac:(lia))).
    apply poly_eval_cong; [lia|].
    replace (p - y) with (- (y - p)) by ring.
    apply Z.divide_opp_r. exact Hydiv. }
  assert (HcongX : p ^ dq mod q = y ^ dq mod q).
  { apply (proj2 (mods_eq_iff_divides (p ^ dq) (y ^ dq) q ltac:(lia))).
    replace (p ^ dq) with (poly_eval (poly_Xn (Z.to_nat dq)) p)
      by (rewrite poly_eval_Xn, Z2Nat.id; [reflexivity | lia]).
    replace (y ^ dq) with (poly_eval (poly_Xn (Z.to_nat dq)) y)
      by (rewrite poly_eval_Xn, Z2Nat.id; [reflexivity | lia]).
    apply poly_eval_cong; [lia|].
    replace (p - y) with (- (y - p)) by ring.
    apply Z.divide_opp_r. exact Hydiv. }
  rewrite HcongF, HcongX.
  rewrite <- (poly_eval_fold_mod P (Z.to_nat (q - 1)) y q);
    [| lia | | exact Hper].
  2: { apply Nat2Z.inj_lt. rewrite Z2Nat.id; lia. }
  rewrite Hloc. unfold powm. rewrite Z.sub_diag, Z.mod_0_l by lia.
  reflexivity.
Qed.

Lemma invert_fold_q_diff_vanishes_all_semiprime :
  forall p q e dq P,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    q < 2 * p ->
    0 < e ->
    0 <= dq ->
    (e * dq) mod (q - 1) = 1 ->
    (forall y, Z.coprime y (p * q) ->
       powm (poly_eval P y) e (p * q) = y mod (p * q)) ->
    Forall (fun a => (q | poly_eval
      (poly_sub (poly_fold P (Z.to_nat (q - 1)))
                (poly_Xn (Z.to_nat dq))) a))
      (units_mod_prime q).
Proof.
  intros p q e dq P Hp Hq Hneq Hlt Hqp He Hd Hinv Hall.
  apply Forall_forall. intros a Hin.
  destruct (fq_units_or_p p q a Hin) as [Heq | Hin'].
  - subst a.
    apply (invert_fold_q_at_lift_semiprime p q e dq P (p + q));
      [exact Hp | exact Hq | exact Hneq | exact Hlt | exact He | exact Hd
       | exact Hinv | exact Hall | apply p_plus_q_coprime; assumption
       | apply p_plus_q_mod_q; lia].
  - pose proof (invert_fold_q_diff_vanishes_semiprime p q e dq P
                  Hp Hq Hneq Hlt Hqp He Hd Hinv Hall) as Hvan.
    rewrite Forall_forall in Hvan. apply Hvan. exact Hin'.
Qed.

Lemma invert_all_units_fold_q_classes_semiprime :
  forall p q e dq P r,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    q < 2 * p ->
    0 < e ->
    0 <= dq < q - 1 ->
    (e * dq) mod (q - 1) = 1 ->
    (r < Z.to_nat (q - 1))%nat ->
    (forall y, Z.coprime y (p * q) ->
       powm (poly_eval P y) e (p * q) = y mod (p * q)) ->
    class_sum P (Z.to_nat (q - 1)) r mod q
      = (if Nat.eqb r (Z.to_nat dq) then 1 else 0).
Proof.
  intros p q e dq P r Hp Hq Hneq Hlt Hqp He Hd Hinv Hr Hall.
  pose proof (Z.prime_ge_2 _ Hq). pose proof (Z.prime_ge_2 _ Hp).
  assert (Hdiv : (q | nth r (poly_sub (poly_fold P (Z.to_nat (q - 1)))
                                       (poly_Xn (Z.to_nat dq))) 0)).
  { apply (poly_prime_roots_divides q (units_mod_prime q)
             (poly_sub (poly_fold P (Z.to_nat (q - 1)))
                       (poly_Xn (Z.to_nat dq)))
             Hq (units_mod_prime_distinct q Hq)).
    - pose proof (poly_degree_sub_le
                    (poly_fold P (Z.to_nat (q - 1)))
                    (poly_Xn (Z.to_nat dq))) as Hs.
      rewrite poly_degree_Xn in Hs.
      rewrite units_mod_prime_length by lia.
      pose proof (poly_degree_fold_lt P (Z.to_nat (q - 1))).
      assert (0 < Z.to_nat (q - 1))%nat
        by (apply Nat2Z.inj_lt; rewrite Z2Nat.id; lia).
      pose proof (Z2Nat.inj_lt dq (q - 1) ltac:(lia) ltac:(lia)).
      lia.
    - apply (invert_fold_q_diff_vanishes_all_semiprime p q e dq P);
        [exact Hp | exact Hq | exact Hneq | exact Hlt | exact Hqp
         | exact He | lia | exact Hinv | exact Hall]. }
  rewrite nth_poly_sub, nth_Xn in Hdiv.
  assert (Hm : (0 < Z.to_nat (q - 1))%nat)
    by (apply Nat2Z.inj_lt; rewrite Z2Nat.id; lia).
  rewrite nth_poly_fold in Hdiv; [| exact Hm | exact Hr].
  destruct (Nat.eq_dec r (Z.to_nat dq)) as [Heq | Hne].
  - replace (Nat.eqb r (Z.to_nat dq)) with true
      by (symmetry; apply Nat.eqb_eq; exact Heq).
    transitivity (1 mod q).
    + apply (proj2 (mods_eq_iff_divides (class_sum P (Z.to_nat (q - 1)) r) 1
                      q ltac:(lia))).
      exact Hdiv.
    + apply Z.mod_1_l. lia.
  - replace (Nat.eqb r (Z.to_nat dq)) with false
      by (symmetry; apply Nat.eqb_neq; exact Hne).
    replace (class_sum P (Z.to_nat (q - 1)) r - 0)
      with (class_sum P (Z.to_nat (q - 1)) r) in Hdiv by lia.
    apply (proj2 (Z.mod_divide (class_sum P (Z.to_nat (q - 1)) r)
                    q ltac:(lia))) in Hdiv.
    exact Hdiv.
Qed.

(** ** Both Fermat folds are the local inverse monomials

    General for distinct odd primes [p < q < 2p]
    ([invert_all_units_folds_local_monomials]); the pin wrapper
    is [invert_all_units_both_folds_are_local_monomials].
    [fold_p ≡ X^{d_p}] and [fold_q ≡ X^{d_q}] as polynomials.
    CRT of those local inverse degrees recovers [d] mod [λ].
    Writing an invert-all-units poly writes both local inverse
    maps, hence writes [d].  Not
    [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/186], [cas/254]. *)

Theorem invert_all_units_folds_local_monomials :
  forall p q e da dq P,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    2 < p ->
    2 < q ->
    p < q ->
    q < 2 * p ->
    0 < e ->
    0 <= da < p - 1 ->
    0 <= dq < q - 1 ->
    (e * da) mod (p - 1) = 1 ->
    (e * dq) mod (q - 1) = 1 ->
    (forall y, Z.coprime y (p * q) ->
       powm (poly_eval P y) e (p * q) = y mod (p * q)) ->
    (forall r, (r < Z.to_nat (p - 1))%nat ->
       class_sum P (Z.to_nat (p - 1)) r mod p
         = (if Nat.eqb r (Z.to_nat da) then 1 else 0)) /\
    (forall r, (r < Z.to_nat (q - 1))%nat ->
       class_sum P (Z.to_nat (q - 1)) r mod q
         = (if Nat.eqb r (Z.to_nat dq) then 1 else 0)).
Proof.
  intros p q e da dq P Hp Hq Hneq H2p H2q Hlt Hqp He Hda Hdq Hinvp Hinvq Hall.
  split.
  - intros r Hr.
    apply (invert_all_units_fold_p_classes_semiprime p q e da P r);
      assumption.
  - intros r Hr.
    apply (invert_all_units_fold_q_classes_semiprime p q e dq P r);
      assumption.
Qed.

Theorem invert_all_units_both_folds_are_local_monomials :
  forall P,
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    (forall r, (r < Z.to_nat (pin_p - 1))%nat ->
       class_sum P (Z.to_nat (pin_p - 1)) r mod pin_p
         = (if Nat.eqb r (Z.to_nat pin_inv3_p) then 1 else 0)) /\
    (forall r, (r < Z.to_nat (pin_q - 1))%nat ->
       class_sum P (Z.to_nat (pin_q - 1)) r mod pin_q
         = (if Nat.eqb r (Z.to_nat pin_inv3_q) then 1 else 0)).
Proof.
  intros P Hall.
  change pin_N with (pin_p * pin_q) in Hall.
  apply (invert_all_units_folds_local_monomials pin_p pin_q pin_e
           pin_inv3_p pin_inv3_q P);
    [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q
     | lia | lia | lia | lia | lia | lia | lia
     | apply (proj1 pin_inv3_local)
     | apply (proj2 pin_inv3_local)
     | exact Hall].
Qed.

Theorem invert_all_units_fold_degrees_crt_d :
  forall x,
    x mod (pin_p - 1) = pin_inv3_p ->
    x mod (pin_q - 1) = pin_inv3_q ->
    x mod pin_lam = pin_d.
Proof.
  intros x Hp Hq. apply pin_local_inverses_recover_d; assumption.
Qed.

(** ** Other lifts of residue [p]

    [p + k q] is a unit of [N] iff [gcd(k,p)=1], and every such
    lift fills the missing [𝔽_q*] sample.  Cross-confirmed by
    [cas/187] and [cas/188]. *)

Lemma p_plus_k_q_mod_q :
  forall p q k, 0 < q -> (p + k * q) mod q = p mod q.
Proof.
  intros p q k Hq.
  rewrite Z.add_mod, Z.mul_mod, Z.mod_same, Z.mul_0_r, Z.add_0_r, Z.mod_mod;
    lia.
Qed.

Lemma p_plus_k_q_coprime :
  forall p q k,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    Z.coprime k p ->
    Z.coprime (p + k * q) (p * q).
Proof.
  intros p q k Hp Hq Hneq Hk.
  apply (proj2 (coprime_semiprime p q (p + k * q) Hp Hq Hneq)).
  split.
  - unfold Z.coprime.
    replace (p + k * q) with (k * q + 1 * p) by ring.
    rewrite gcd_add_mul, Z.gcd_comm.
    apply (proj2 (coprime_mul_iff p k q)).
    split.
    + rewrite coprime_comm. exact Hk.
    + apply prime_coprime_distinct; [exact Hp | exact Hq | exact Hneq].
  - unfold Z.coprime. rewrite gcd_add_mul.
    apply prime_coprime_distinct; [exact Hp | exact Hq | exact Hneq].
Qed.

Lemma pin_p_plus_2q_coprime :
  Z.coprime (pin_p + 2 * pin_q) pin_N.
Proof.
  change pin_N with (pin_p * pin_q).
  apply p_plus_k_q_coprime;
    [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q |].
  vm_compute. reflexivity.
Qed.

Lemma pin_p_plus_2q_mod_q :
  (pin_p + 2 * pin_q) mod pin_q = pin_p.
Proof.
  rewrite p_plus_k_q_mod_q, Z.mod_small; [reflexivity | lia | lia].
Qed.

Lemma pin_p_plus_pq_shares_p :
  Z.gcd (pin_p + pin_p * pin_q) pin_N = pin_p.
Proof. vm_compute. reflexivity. Qed.

Lemma invert_fold_q_at_2q :
  forall P,
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    (pin_q | poly_eval
      (poly_sub (poly_fold P (Z.to_nat (pin_q - 1)))
                (poly_Xn (Z.to_nat pin_inv3_q))) pin_p).
Proof.
  intros P Hall.
  apply (invert_fold_q_at_lift P (pin_p + 2 * pin_q) Hall);
    [apply pin_p_plus_2q_coprime | apply pin_p_plus_2q_mod_q].
Qed.

(** ** Unique monic leftover kernel, and [K ≡ X^{q−2} (mod p)]

    [K] is monic of degree [q−2] and vanishes on [𝔽_q* \ {p}].
    Lower coefficients are positive powers of [p], so [K ≡ X^{q−2}]
    as polynomials modulo [p].  Cross-confirmed by [cas/189] and
    [cas/190]. *)

Lemma geo_kernel_nth :
  forall base n i,
    (i <= n)%nat ->
    nth i (geo_kernel base n) 0 = base ^ Z.of_nat (n - i).
Proof.
  intros base n.
  induction n as [|n IH]; intros i Hi.
  - assert (Hi0 : i = 0%nat) by lia. subst i.
    cbn [geo_kernel nth].
    replace (base ^ Z.of_nat (0 - 0)%nat) with 1
      by (rewrite Nat.sub_diag, Z.pow_0_r; reflexivity).
    reflexivity.
  - cbn [geo_kernel].
    destruct (Nat.eq_dec i (S n)) as [Heq | Hne].
    + subst i.
      rewrite app_nth2.
      2: { rewrite map_mul_length, geo_kernel_length. lia. }
      rewrite map_mul_length, geo_kernel_length, Nat.sub_diag.
      cbn [nth].
      replace ((S n - S n)%nat) with 0%nat by lia.
      replace (base ^ Z.of_nat 0%nat) with 1
        by (rewrite Z.pow_0_r; reflexivity).
      reflexivity.
    + assert (Hlt : (i < S n)%nat) by lia.
      rewrite app_nth1.
      2: { rewrite map_mul_length, geo_kernel_length. exact Hlt. }
      rewrite nth_map_mul, (IH i) by lia.
      replace (S n - i)%nat with (S (n - i)) by lia.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      ring.
Qed.

Lemma geo_kernel_degree :
  forall base n, poly_degree (geo_kernel base n) = n.
Proof.
  intros base n.
  assert (Hlead : nth n (geo_kernel base n) 0 = 1).
  { rewrite geo_kernel_nth by lia. rewrite Nat.sub_diag, Z.pow_0_r. reflexivity. }
  assert (Hnz : poly_is_zero (geo_kernel base n) = false).
  { destruct (poly_is_zero (geo_kernel base n)) eqn:Hz; [|reflexivity].
    rewrite (poly_is_zero_nth _ n Hz) in Hlead. discriminate. }
  pose proof (poly_degree_nth_le (geo_kernel base n) n ltac:(lia)) as Hle.
  pose proof (poly_degree_leading (geo_kernel base n) Hnz) as HleadD.
  destruct (Nat.lt_ge_cases n (poly_degree (geo_kernel base n))) as [Hlt | Hge].
  - rewrite nth_overflow in HleadD.
    2: { rewrite geo_kernel_length. lia. }
    contradiction.
  - lia.
Qed.

Lemma geo_kernel_vanishes_semiprime :
  forall p q,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    Forall (fun a => (q | poly_eval (geo_kernel p (Z.to_nat (q - 2))) a))
      (fq_units_of_N p q).
Proof.
  intros p q Hp Hq Hneq Hlt.
  pose proof (Z.prime_ge_2 _ Hq). pose proof (Z.prime_ge_2 _ Hp).
  apply Forall_forall. intros a Hin.
  unfold fq_units_of_N in Hin.
  apply filter_In in Hin. destruct Hin as [HinU Hne].
  apply negb_true_iff, Z.eqb_neq in Hne.
  pose proof (units_mod_prime_In q a ltac:(lia) HinU) as Hb.
  pose proof (geo_kernel_identity p a (Z.to_nat (q - 2))) as Hid.
  rewrite Nat2Z.inj_succ, Z2Nat.id in Hid by lia.
  replace (Z.succ (q - 2)) with (q - 1) in Hid by lia.
  assert (Hfa : powm a (q - 1) q = 1).
  { apply fermat_coprime; [exact Hq|].
    rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hq|].
    intros [k Hk]. destruct k as [|k|k]; nia. }
  assert (Hfp : powm p (q - 1) q = 1).
  { apply fermat_coprime; [exact Hq|].
    apply prime_coprime_distinct; [exact Hp | exact Hq | exact Hneq]. }
  assert (Hdiff : (q | a ^ (q - 1) - p ^ (q - 1))).
  { apply Z.mod_divide; [lia|].
    rewrite Zminus_mod.
    change ((a ^ (q - 1)) mod q) with (powm a (q - 1) q).
    change ((p ^ (q - 1)) mod q) with (powm p (q - 1) q).
    rewrite Hfa, Hfp, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity. }
  apply (Z.gauss q (a - p) (poly_eval (geo_kernel p (Z.to_nat (q - 2))) a)).
  - rewrite Hid. exact Hdiff.
  - unfold Z.coprime.
    apply Z.coprime_prime_l_iff; [exact Hq|].
    intros Hqp.
    apply (proj2 (mods_eq_iff_divides a p q ltac:(lia))) in Hqp.
    rewrite !Z.mod_small in Hqp; [contradiction | lia | lia].
Qed.

Lemma geo_kernel_inv_mod_semiprime :
  forall p q,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    2 < q ->
    (poly_eval (geo_kernel p (Z.to_nat (q - 2))) p * (q - p)) mod q = 1.
Proof.
  intros p q Hp Hq Hneq Hq2.
  pose proof (Z.prime_ge_2 _ Hp). pose proof (Z.prime_ge_2 _ Hq).
  pose proof (geo_kernel_at_base p (Z.to_nat (q - 2))) as Hk.
  rewrite Z2Nat.id in Hk by lia.
  rewrite Hk.
  replace (q - 2 + 1) with (q - 1) by lia.
  transitivity (p ^ (q - 1) mod q).
  - apply (proj2 (mods_eq_iff_divides
                    ((q - 1) * p ^ (q - 2) * (q - p))
                    (p ^ (q - 1)) q ltac:(lia))).
    assert (Hpow : p ^ (q - 1) = p * p ^ (q - 2)).
    { replace (q - 1) with (Z.succ (q - 2)) by lia.
      rewrite Z.pow_succ_r by lia. reflexivity. }
    rewrite Hpow.
    exists ((q - p - 1) * p ^ (q - 2)). ring.
  - change ((p ^ (q - 1)) mod q) with (powm p (q - 1) q).
    apply fermat_coprime; [exact Hq|].
    apply prime_coprime_distinct; [exact Hp | exact Hq | exact Hneq].
Qed.

Lemma geo_kernel_at_2_mod_odd :
  forall p q,
    Z.prime p ->
    2 < p ->
    2 < q ->
    poly_eval (geo_kernel p (Z.to_nat (q - 2))) 2 mod p
      = powm 2 (q - 2) p.
Proof.
  intros p q Hp Hp2 Hq2.
  pose proof (Z.prime_ge_2 _ Hp).
  pose proof (geo_kernel_identity p 2 (Z.to_nat (q - 2))) as Hid.
  rewrite Nat2Z.inj_succ, Z2Nat.id in Hid by lia.
  replace (Z.succ (q - 2)) with (q - 1) in Hid by lia.
  set (K2 := poly_eval (geo_kernel p (Z.to_nat (q - 2))) 2).
  assert (Hpdiv : (p | p ^ (q - 1))).
  { exists (p ^ (q - 2)).
    replace (q - 1) with (Z.succ (q - 2)) by lia.
    rewrite Z.pow_succ_r by lia. ring. }
  assert (H2K : (p | 2 * K2 - 2 ^ (q - 1))).
  { replace (2 * K2 - 2 ^ (q - 1))
      with ((2 - p) * K2 - (2 ^ (q - 1) - p ^ (q - 1))
            + p * K2 - p ^ (q - 1)) by ring.
    unfold K2. rewrite Hid.
    replace (2 ^ (q - 1) - p ^ (q - 1) - (2 ^ (q - 1) - p ^ (q - 1))
               + p * poly_eval (geo_kernel p (Z.to_nat (q - 2))) 2
               - p ^ (q - 1))
      with (p * poly_eval (geo_kernel p (Z.to_nat (q - 2))) 2
            - p ^ (q - 1)) by ring.
    apply Z.divide_sub_r.
    - apply Z.divide_mul_l, Z.divide_refl.
    - exact Hpdiv. }
  assert (H2pow : 2 ^ (q - 1) = 2 * 2 ^ (q - 2)).
  { replace (q - 1) with (Z.succ (q - 2)) by lia.
    rewrite Z.pow_succ_r by lia. reflexivity. }
  rewrite H2pow in H2K.
  replace (2 * K2 - 2 * 2 ^ (q - 2))
    with (2 * (K2 - 2 ^ (q - 2))) in H2K by ring.
  apply (Z.gauss p 2 (K2 - 2 ^ (q - 2))) in H2K.
  2: { apply Z.coprime_prime_l_iff; [exact Hp|].
       intros [k Hk]. destruct k as [|k|k]; nia. }
  apply (proj2 (mods_eq_iff_divides K2 (2 ^ (q - 2)) p ltac:(lia))) in H2K.
  unfold powm, K2 in *. exact H2K.
Qed.

Theorem pin_geo_kernel_degree :
  poly_degree pin_geo_kernel = Z.to_nat (pin_q - 2).
Proof.
  unfold pin_geo_kernel. apply geo_kernel_degree.
Qed.

Theorem pin_geo_kernel_leading :
  nth (Z.to_nat (pin_q - 2)) pin_geo_kernel 0 = 1.
Proof.
  unfold pin_geo_kernel.
  rewrite geo_kernel_nth by lia.
  replace (Z.to_nat (pin_q - 2) - Z.to_nat (pin_q - 2))%nat with 0%nat by lia.
  rewrite Z.pow_0_r. reflexivity.
Qed.

Theorem pin_geo_kernel_lower_div_p :
  forall i,
    (i < Z.to_nat (pin_q - 2))%nat ->
    (pin_p | nth i pin_geo_kernel 0).
Proof.
  intros i Hi.
  unfold pin_geo_kernel.
  rewrite geo_kernel_nth by lia.
  destruct (Z.to_nat (pin_q - 2) - i)%nat as [|k] eqn:Hk; [lia|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  apply Z.divide_mul_l, Z.divide_refl.
Qed.

Theorem pin_geo_kernel_plus_q_cong :
  forall i,
    nth i (poly_add pin_geo_kernel (map_mul pin_q (poly_Xn 3%nat))) 0 mod pin_q
      = nth i pin_geo_kernel 0 mod pin_q.
Proof.
  intros i.
  rewrite nth_poly_add, nth_map_mul.
  rewrite Z.add_mod, Z.mul_mod, Z.mod_same, Z.mul_0_l, Z.add_0_r, Z.mod_mod;
    lia.
Qed.

(** ** CRT binomial inhabitant writes both local inverse folds

    The CRT binomial inverts every unit, so both Fermat folds are
    the local inverse monomials.  The coefficients already split.
    Not [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/191]. *)

Theorem pin_crt_binomial_both_folds :
  (forall r, (r < Z.to_nat (pin_p - 1))%nat ->
     class_sum pin_crt_root_poly (Z.to_nat (pin_p - 1)) r mod pin_p
       = (if Nat.eqb r (Z.to_nat pin_inv3_p) then 1 else 0)) /\
  (forall r, (r < Z.to_nat (pin_q - 1))%nat ->
     class_sum pin_crt_root_poly (Z.to_nat (pin_q - 1)) r mod pin_q
       = (if Nat.eqb r (Z.to_nat pin_inv3_q) then 1 else 0)).
Proof.
  apply invert_all_units_both_folds_are_local_monomials.
  apply pin_crt_binomial_inverts_units.
Qed.

(** ** Leftover kernel is 1-dimensional

    Any [P] of degree [< q−1] vanishing on [𝔽_q* \ {p}] is a
    scalar multiple of [K] modulo [q]: the missing sample at [p]
    pins the scalar.  A monic such [P] of degree [q−2] is [K]
    itself.  Uniqueness of a leftover kernel, not a residual
    solver.  Not [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/192] and [cas/193]. *)

Lemma poly_degree_gt_nth_zero :
  forall P i, (poly_degree P < i)%nat -> nth i P 0 = 0.
Proof.
  intros P i Hi.
  destruct (Z.eq_dec (nth i P 0) 0) as [Hz | Hnz]; [exact Hz|].
  pose proof (poly_degree_nth_le P i Hnz). lia.
Qed.

Lemma leftover_kernel_span_mod_q :
  forall p q P c,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    (poly_degree P < Z.to_nat (q - 1))%nat ->
    Forall (fun a => (q | poly_eval P a)) (fq_units_of_N p q) ->
    (q | poly_eval P p
           - c * poly_eval (geo_kernel p (Z.to_nat (q - 2))) p) ->
    forall i,
      (q | nth i (poly_sub P (map_mul c (geo_kernel p (Z.to_nat (q - 2))))) 0).
Proof.
  intros p q P c Hp Hq Hneq Hlt Hdeg Hvan Hcp i.
  pose proof (Z.prime_ge_2 _ Hq). pose proof (Z.prime_ge_2 _ Hp).
  apply (poly_prime_roots_divides q (units_mod_prime q)
           (poly_sub P (map_mul c (geo_kernel p (Z.to_nat (q - 2)))))
           Hq (units_mod_prime_distinct q Hq)).
  - pose proof (poly_degree_sub_le P (map_mul c (geo_kernel p (Z.to_nat (q - 2)))))
      as Hs.
    pose proof (poly_degree_map_mul_le c (geo_kernel p (Z.to_nat (q - 2)))) as Hm.
    pose proof (geo_kernel_degree p (Z.to_nat (q - 2))) as HdK.
    rewrite units_mod_prime_length by lia.
    lia.
  - apply Forall_forall. intros a Hin.
    destruct (fq_units_or_p p q a Hin) as [Heq | Hin'].
    + subst a. rewrite poly_eval_sub, poly_eval_map_mul. exact Hcp.
    + rewrite poly_eval_sub, poly_eval_map_mul.
      apply Z.divide_sub_r.
      * rewrite Forall_forall in Hvan. apply Hvan. exact Hin'.
      * apply Z.divide_mul_r.
        pose proof (geo_kernel_vanishes_semiprime p q Hp Hq Hneq Hlt) as HK.
        rewrite Forall_forall in HK. apply HK. exact Hin'.
Qed.

Theorem leftover_monic_is_geo_kernel :
  forall p q P,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    2 < q ->
    poly_degree P = Z.to_nat (q - 2) ->
    nth (Z.to_nat (q - 2)) P 0 = 1 ->
    Forall (fun a => (q | poly_eval P a)) (fq_units_of_N p q) ->
    forall i,
      (q | nth i (poly_sub P (geo_kernel p (Z.to_nat (q - 2)))) 0).
Proof.
  intros p q P Hp Hq Hneq Hlt Hq2 Hdeg Hlead Hvan i.
  pose proof (Z.prime_ge_2 _ Hq). pose proof (Z.prime_ge_2 _ Hp).
  set (K := geo_kernel p (Z.to_nat (q - 2))).
  set (D := poly_sub P K).
  assert (Htoppos : (0 < Z.to_nat (q - 2))%nat)
    by (apply Nat2Z.inj_lt; rewrite Z2Nat.id; lia).
  assert (HKlead : nth (Z.to_nat (q - 2)) K 0 = 1).
  { unfold K. rewrite geo_kernel_nth by lia.
    replace (Z.to_nat (q - 2) - Z.to_nat (q - 2))%nat with 0%nat by lia.
    rewrite Z.pow_0_r. reflexivity. }
  assert (Hhigh : forall j, (Z.to_nat (q - 2) <= j)%nat -> nth j D 0 = 0).
  { intros j Hj.
    unfold D. rewrite nth_poly_sub.
    destruct (Nat.eq_dec j (Z.to_nat (q - 2))) as [Heq | Hne].
    - subst j. rewrite Hlead, HKlead. ring.
    - rewrite (poly_degree_gt_nth_zero P j) by (rewrite Hdeg; lia).
      rewrite (poly_degree_gt_nth_zero K j)
        by (unfold K; rewrite geo_kernel_degree; lia).
      ring. }
  pose proof (poly_degree_below_if_high_zero D (Z.to_nat (q - 2))
                Htoppos Hhigh) as HdegD.
  apply (poly_prime_roots_divides q (fq_units_of_N p q) D
           Hq (fq_units_of_N_distinct p q Hq)).
  - rewrite (fq_units_of_N_length p q) by lia. exact HdegD.
  - apply Forall_forall. intros a Hin.
    unfold D. rewrite poly_eval_sub.
    apply Z.divide_sub_r.
    + rewrite Forall_forall in Hvan. apply Hvan. exact Hin.
    + pose proof (geo_kernel_vanishes_semiprime p q Hp Hq Hneq Hlt) as HK.
      rewrite Forall_forall in HK. apply HK. exact Hin.
Qed.

Theorem leftover_kernel_exists_scalar_mod_q :
  forall p q P,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p < q ->
    2 < q ->
    (poly_degree P < Z.to_nat (q - 1))%nat ->
    Forall (fun a => (q | poly_eval P a)) (fq_units_of_N p q) ->
    exists c,
      0 <= c < q /\
      forall i,
        (q | nth i (poly_sub P (map_mul c (geo_kernel p (Z.to_nat (q - 2))))) 0).
Proof.
  intros p q P Hp Hq Hneq Hlt Hq2 Hdeg Hvan.
  pose proof (Z.prime_ge_2 _ Hq).
  set (K := geo_kernel p (Z.to_nat (q - 2))).
  set (c := (poly_eval P p * (q - p)) mod q).
  exists c.
  split.
  - apply Z.mod_pos_bound. lia.
  - apply (leftover_kernel_span_mod_q p q P c);
      [exact Hp | exact Hq | exact Hneq | exact Hlt | exact Hdeg | exact Hvan |].
    apply (proj1 (mods_eq_iff_divides (poly_eval P p)
                    (c * poly_eval K p) q ltac:(lia))).
    unfold c, K.
    rewrite Z.mul_mod_idemp_l by lia.
    rewrite <- Z.mul_assoc, (Z.mul_comm (q - p)).
    rewrite <- Z.mul_mod_idemp_r by lia.
    rewrite (geo_kernel_inv_mod_semiprime p q Hp Hq Hneq Hq2), Z.mul_1_r by lia.
    reflexivity.
Qed.

Lemma leftover_kernel_span :
  forall P c,
    (poly_degree P < Z.to_nat (pin_q - 1))%nat ->
    Forall (fun a => (pin_q | poly_eval P a)) pin_Fq_units_of_N ->
    (pin_q | poly_eval P pin_p
               - c * poly_eval pin_geo_kernel pin_p) ->
    forall i,
      (pin_q | nth i (poly_sub P (map_mul c pin_geo_kernel)) 0).
Proof.
  intros P c Hdeg Hvan Hcp i.
  unfold pin_geo_kernel, pin_Fq_units_of_N in *.
  apply (leftover_kernel_span_mod_q pin_p pin_q P c);
    [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q
     | lia | exact Hdeg | exact Hvan | exact Hcp].
Qed.

Theorem leftover_monic_is_kernel :
  forall P,
    poly_degree P = Z.to_nat (pin_q - 2) ->
    nth (Z.to_nat (pin_q - 2)) P 0 = 1 ->
    Forall (fun a => (pin_q | poly_eval P a)) pin_Fq_units_of_N ->
    forall i,
      (pin_q | nth i (poly_sub P pin_geo_kernel) 0).
Proof.
  intros P Hdeg Hlead Hvan i.
  unfold pin_geo_kernel, pin_Fq_units_of_N in *.
  apply (leftover_monic_is_geo_kernel pin_p pin_q P);
    [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q
     | lia | lia | exact Hdeg | exact Hlead | exact Hvan].
Qed.

Theorem pin_geo_kernel_inv_mod :
  (poly_eval pin_geo_kernel pin_p * (pin_q - pin_p)) mod pin_q = 1.
Proof.
  unfold pin_geo_kernel.
  apply geo_kernel_inv_mod_semiprime;
    [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q | lia].
Qed.

Theorem leftover_kernel_exists_scalar :
  forall P,
    (poly_degree P < Z.to_nat (pin_q - 1))%nat ->
    Forall (fun a => (pin_q | poly_eval P a)) pin_Fq_units_of_N ->
    exists c,
      0 <= c < pin_q /\
      forall i, (pin_q | nth i (poly_sub P (map_mul c pin_geo_kernel)) 0).
Proof.
  intros P Hdeg Hvan.
  unfold pin_geo_kernel, pin_Fq_units_of_N in *.
  apply (leftover_kernel_exists_scalar_mod_q pin_p pin_q P);
    [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q
     | lia | lia | exact Hdeg | exact Hvan].
Qed.

(** ** Binomial [+ c K]: leftover extra, invert iff [N | c]

    Agreement with the binomial on [𝔽_q* \ {p}] is [K] vanishing,
    not invert-all-units on [N].  Extra at the lift [p+q] is
    [c K(p)] (mod [q]); extra at [2] is [c · 2^{q−2}] (mod [p]).
    Invert-all-units for this family needs both extras [0], hence
    [N | c].  [p K] misses the lift; [q K] misses unit [2];
    [N K] is the same function as the binomial.  Cross-confirmed
    by [cas/194], [cas/195], [cas/196], and [cas/197]. *)

Lemma pin_ck_agrees_canonical :
  forall c a,
    In a pin_Fq_units_of_N ->
    (pin_q | poly_eval (poly_add pin_crt_root_poly
                          (map_mul c pin_geo_kernel)) a
             - poly_eval pin_crt_root_poly a).
Proof.
  intros c a Hin.
  rewrite poly_eval_add, poly_eval_map_mul.
  replace (poly_eval pin_crt_root_poly a
             + c * poly_eval pin_geo_kernel a
             - poly_eval pin_crt_root_poly a)
    with (c * poly_eval pin_geo_kernel a) by ring.
  apply Z.divide_mul_r.
  pose proof pin_geo_kernel_vanishes as HK.
  rewrite Forall_forall in HK. apply HK. exact Hin.
Qed.

Lemma pin_ck_extra_at_lift :
  forall c,
    (pin_q | poly_eval (poly_add pin_crt_root_poly
                          (map_mul c pin_geo_kernel))
                        (pin_p + pin_q)
             - poly_eval pin_crt_root_poly (pin_p + pin_q)
             - c * poly_eval pin_geo_kernel pin_p).
Proof.
  intros c.
  rewrite poly_eval_add, poly_eval_map_mul.
  replace (poly_eval pin_crt_root_poly (pin_p + pin_q)
             + c * poly_eval pin_geo_kernel (pin_p + pin_q)
             - poly_eval pin_crt_root_poly (pin_p + pin_q)
             - c * poly_eval pin_geo_kernel pin_p)
    with (c * (poly_eval pin_geo_kernel (pin_p + pin_q)
                 - poly_eval pin_geo_kernel pin_p)) by ring.
  apply Z.divide_mul_r.
  apply poly_eval_cong; [lia|].
  exists 1. ring.
Qed.

Lemma pin_ck_extra_at_2_mod_p :
  forall c,
    (poly_eval (poly_add pin_crt_root_poly (map_mul c pin_geo_kernel)) 2
       - poly_eval pin_crt_root_poly 2) mod pin_p
      = (c * powm 2 (pin_q - 2) pin_p) mod pin_p.
Proof.
  intros c.
  rewrite poly_eval_add, poly_eval_map_mul.
  replace (poly_eval pin_crt_root_poly 2
             + c * poly_eval pin_geo_kernel 2
             - poly_eval pin_crt_root_poly 2)
    with (c * poly_eval pin_geo_kernel 2) by ring.
  rewrite <- (Z.mul_mod_idemp_r c (poly_eval pin_geo_kernel 2) pin_p) by lia.
  rewrite pin_geo_kernel_at_2_mod_p.
  reflexivity.
Qed.

Definition pin_binomial_plus_p_kernel : list Z :=
  poly_add pin_crt_root_poly (map_mul pin_p pin_geo_kernel).

Definition pin_binomial_plus_q_kernel : list Z :=
  poly_add pin_crt_root_poly (map_mul pin_q pin_geo_kernel).

Definition pin_binomial_plus_N_kernel : list Z :=
  poly_add pin_crt_root_poly (map_mul pin_N pin_geo_kernel).

Theorem poly_eval_plus_N_mul_inverts :
  forall P K e N y,
    0 < N ->
    0 <= e ->
    powm (poly_eval P y) e N = y mod N ->
    powm (poly_eval (poly_add P (map_mul N K)) y) e N = y mod N.
Proof.
  intros P K e N y HN He HP.
  rewrite poly_eval_add, poly_eval_map_mul.
  transitivity (powm (poly_eval P y) e N).
  - apply powm_div_cong; [lia | lia |].
    exists (poly_eval K y). ring.
  - exact HP.
Qed.

Theorem invert_all_units_plus_c_kernel_iff :
  forall p q e da dq P c,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    2 < p ->
    2 < q ->
    p < q ->
    q < 2 * p ->
    0 < e ->
    0 <= da ->
    0 <= dq ->
    (e * da) mod (p - 1) = 1 ->
    (e * dq) mod (q - 1) = 1 ->
    (forall y, Z.coprime y (p * q) ->
       powm (poly_eval P y) e (p * q) = y mod (p * q)) ->
    (forall y, Z.coprime y (p * q) ->
       powm (poly_eval (poly_add P (map_mul c (geo_kernel p (Z.to_nat (q - 2))))) y)
         e (p * q) = y mod (p * q))
    <-> (p * q | c).
Proof.
  intros p q e da dq P c Hp Hq Hneq Hp2 Hq2 Hlt Hqp He Hda Hdq Hinvp Hinvq Hall.
  pose proof (Z.prime_ge_2 _ Hp). pose proof (Z.prime_ge_2 _ Hq).
  set (K := geo_kernel p (Z.to_nat (q - 2))).
  split.
  - intros Hallc.
    assert (Hqc : (q | c)).
    { set (y := p + q).
      pose proof (p_plus_q_coprime p q Hp Hq Hneq) as Hcop.
      pose proof (Hallc y Hcop) as Hrootc.
      pose proof (Hall y Hcop) as Hroot.
      pose proof (short_root_local_at_q p q e dq
                    (poly_add P (map_mul c K)) y
                    Hp Hq Hneq He Hdq Hinvq Hcop Hrootc) as Hlocc.
      pose proof (short_root_local_at_q p q e dq P y
                    Hp Hq Hneq He Hdq Hinvq Hcop Hroot) as Hloc.
      assert (Hex : (q | c * poly_eval K y)).
      { assert (Hex0 : (q | poly_eval (poly_add P (map_mul c K)) y
                              - poly_eval P y)).
        { apply (proj1 (mods_eq_iff_divides
                          (poly_eval (poly_add P (map_mul c K)) y)
                          (poly_eval P y) q ltac:(lia))).
          rewrite Hlocc, Hloc. reflexivity. }
        rewrite poly_eval_add, poly_eval_map_mul in Hex0.
        replace (poly_eval P y + c * poly_eval K y - poly_eval P y)
          with (c * poly_eval K y) in Hex0 by ring.
        exact Hex0. }
      assert (Hcong : (q | poly_eval K y - poly_eval K p)).
      { apply poly_eval_cong; [lia|]. exists 1. unfold y. ring. }
      assert (HqK : (q | c * poly_eval K p)).
      { replace (c * poly_eval K p)
          with (c * poly_eval K y
                - c * (poly_eval K y - poly_eval K p)) by ring.
        apply Z.divide_sub_r; [exact Hex | apply Z.divide_mul_r; exact Hcong]. }
      rewrite (Z.mul_comm c) in HqK.
      apply (Z.gauss q (poly_eval K p) c) in HqK.
      2: { pose proof (geo_kernel_inv_mod_semiprime p q Hp Hq Hneq Hq2) as HinvK.
           unfold Z.coprime.
           apply Z.coprime_prime_l_iff; [exact Hq|].
           intros Hdiv.
           apply (proj2 (Z.mod_divide (poly_eval K p) q ltac:(lia))) in Hdiv.
           unfold K in Hdiv.
           assert (H1 : 1 mod q = 0).
           { rewrite <- HinvK.
             rewrite Z.mul_mod, Hdiv, Z.mul_0_l, Z.mod_0_l by lia.
             reflexivity. }
           rewrite Z.mod_1_l in H1; [discriminate | lia]. }
      exact HqK. }
    assert (Hpc : (p | c)).
    { assert (Hcop2 : Z.coprime 2 (p * q))
        by (apply two_coprime_odd_primes; assumption).
      pose proof (Hallc 2 Hcop2) as Hrootc.
      pose proof (Hall 2 Hcop2) as Hroot.
      pose proof (short_root_local_at_p p q e da
                    (poly_add P (map_mul c K)) 2
                    Hp Hq Hneq He Hda Hinvp Hcop2 Hrootc) as Hlocc.
      pose proof (short_root_local_at_p p q e da P 2
                    Hp Hq Hneq He Hda Hinvp Hcop2 Hroot) as Hloc.
      assert (Hex : (p | c * poly_eval K 2)).
      { assert (Hex0 : (p | poly_eval (poly_add P (map_mul c K)) 2
                              - poly_eval P 2)).
        { apply (proj1 (mods_eq_iff_divides
                          (poly_eval (poly_add P (map_mul c K)) 2)
                          (poly_eval P 2) p ltac:(lia))).
          rewrite Hlocc, Hloc. reflexivity. }
        rewrite poly_eval_add, poly_eval_map_mul in Hex0.
        replace (poly_eval P 2 + c * poly_eval K 2 - poly_eval P 2)
          with (c * poly_eval K 2) in Hex0 by ring.
        exact Hex0. }
      rewrite (Z.mul_comm c) in Hex.
      apply (Z.gauss p (poly_eval K 2) c) in Hex.
      2: { pose proof (geo_kernel_at_2_mod_odd p q Hp Hp2 Hq2) as HK2.
           unfold Z.coprime.
           apply Z.coprime_prime_l_iff; [exact Hp|].
           intros Hdiv.
           apply (proj2 (Z.mod_divide (poly_eval K 2) p ltac:(lia))) in Hdiv.
           unfold K in Hdiv. rewrite HK2 in Hdiv.
           unfold powm in Hdiv.
           apply Z.mod_divide in Hdiv; [|lia].
           assert (Hcop2p : Z.coprime 2 p).
           { rewrite coprime_comm. apply Z.coprime_prime_l_iff; [exact Hp|].
             intros [k Hk]. destruct k as [|k|k]; nia. }
           assert (Hg : Z.gcd (2 ^ (q - 2)) p = 1).
           { apply Z.coprime_pow_l; [lia | exact Hcop2p]. }
           assert (Hp1 : (p | 1)).
           { rewrite <- Hg. apply Z.gcd_greatest;
               [exact Hdiv | apply Z.divide_refl]. }
           apply Z.divide_1_r in Hp1. lia. }
      exact Hex. }
    apply divide_by_coprime_product;
      [apply prime_coprime_distinct; [exact Hp | exact Hq | exact Hneq]
       | exact Hpc | exact Hqc].
  - intros HNc y Hcop.
    rewrite poly_eval_add, poly_eval_map_mul.
    transitivity (powm (poly_eval P y) e (p * q)).
    + apply powm_div_cong; [lia | lia |].
      replace (poly_eval P y + c * poly_eval K y - poly_eval P y)
        with (c * poly_eval K y) by ring.
      apply Z.divide_mul_l. exact HNc.
    + apply Hall. exact Hcop.
Qed.

Theorem pin_binomial_plus_N_kernel_inverts :
  forall y,
    Z.coprime y pin_N ->
    powm (poly_eval pin_binomial_plus_N_kernel y) pin_e pin_N
      = y mod pin_N.
Proof.
  intros y Hcop.
  unfold pin_binomial_plus_N_kernel.
  apply (poly_eval_plus_N_mul_inverts pin_crt_root_poly pin_geo_kernel
           pin_e pin_N y);
    [lia | lia | apply pin_crt_binomial_inverts_units; exact Hcop].
Qed.

Theorem pin_binomial_plus_p_kernel_misses_lift :
  powm (poly_eval pin_binomial_plus_p_kernel (pin_p + pin_q)) pin_e pin_N
    <> (pin_p + pin_q) mod pin_N.
Proof.
  intros Heq.
  set (y := pin_p + pin_q).
  pose proof pin_p_plus_q_coprime as Hcop.
  pose proof (short_root_local_mod_q pin_binomial_plus_p_kernel y Hcop Heq)
    as Hloc.
  pose proof (short_root_local_mod_q pin_crt_root_poly y Hcop
                (pin_crt_binomial_inverts_units y Hcop)) as Hbin.
  unfold pin_binomial_plus_p_kernel in Hloc.
  rewrite poly_eval_add, poly_eval_map_mul in Hloc.
  assert (Hex0 : (pin_q | pin_p * poly_eval pin_geo_kernel y)).
  { apply (proj1 (mods_eq_iff_divides
                    (poly_eval pin_crt_root_poly y
                       + pin_p * poly_eval pin_geo_kernel y)
                    (poly_eval pin_crt_root_poly y)
                    pin_q ltac:(lia))).
    rewrite Hloc, Hbin. reflexivity. }
  assert (Hcong : (pin_q | poly_eval pin_geo_kernel y
                            - poly_eval pin_geo_kernel pin_p)).
  { apply poly_eval_cong; [lia|]. exists 1. unfold y. ring. }
  assert (HqK : (pin_q | pin_p * poly_eval pin_geo_kernel pin_p)).
  { replace (pin_p * poly_eval pin_geo_kernel pin_p)
      with (pin_p * poly_eval pin_geo_kernel y
            - pin_p * (poly_eval pin_geo_kernel y
                         - poly_eval pin_geo_kernel pin_p)) by ring.
    apply Z.divide_sub_r; [exact Hex0 | apply Z.divide_mul_r; exact Hcong]. }
  apply (proj2 (Z.mod_divide (pin_p * poly_eval pin_geo_kernel pin_p)
                  pin_q ltac:(lia))) in HqK.
  apply pin_p_Kp_mod_q_nonzero. exact HqK.
Qed.

Theorem pin_binomial_plus_q_kernel_misses_2 :
  powm (poly_eval pin_binomial_plus_q_kernel 2) pin_e pin_N <> 2 mod pin_N.
Proof.
  intros Heq.
  assert (Hcop : Z.coprime 2 pin_N) by (vm_compute; reflexivity).
  pose proof (short_root_local_mod_p pin_binomial_plus_q_kernel 2 Hcop Heq)
    as Hloc.
  pose proof (short_root_local_mod_p pin_crt_root_poly 2 Hcop
                (pin_crt_binomial_inverts_units 2 Hcop)) as Hbin.
  unfold pin_binomial_plus_q_kernel in Hloc.
  rewrite poly_eval_add, poly_eval_map_mul in Hloc.
  assert (Hex0 : (pin_p | pin_q * poly_eval pin_geo_kernel 2)).
  { apply (proj1 (mods_eq_iff_divides
                    (poly_eval pin_crt_root_poly 2
                       + pin_q * poly_eval pin_geo_kernel 2)
                    (poly_eval pin_crt_root_poly 2)
                    pin_p ltac:(lia))).
    rewrite Hloc, Hbin. reflexivity. }
  apply (Z.gauss pin_p pin_q (poly_eval pin_geo_kernel 2)) in Hex0.
  2: { apply prime_coprime_distinct;
       [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q]. }
  apply (proj2 (Z.mod_divide (poly_eval pin_geo_kernel 2) pin_p
                  ltac:(lia))) in Hex0.
  rewrite pin_geo_kernel_at_2_mod_p in Hex0.
  apply pin_two_pow_qminus2_mod_p_nonzero. exact Hex0.
Qed.

(** ** Difference of invert polys has both Fermat folds zero

    Any two all-units invert polys have the same local inverse
    folds, so their difference is Fermat-period on both sides.
    Writing two invert maps wrote the same local inverses, hence
    [d].  Not [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/198] and [cas/199]. *)

Lemma class_sum_from_add :
  forall A B m r i,
    class_sum_from (poly_add A B) m r i
      = class_sum_from A m r i + class_sum_from B m r i.
Proof.
  intros A.
  induction A as [|ha ta IH]; intros B m r i.
  - simpl. lia.
  - destruct B as [|hb tb].
    + simpl. lia.
    + simpl. rewrite IH.
      destruct (Nat.eqb r (Nat.modulo i m)); ring.
Qed.

Lemma class_sum_from_map_mul :
  forall k A m r i,
    class_sum_from (map_mul k A) m r i = k * class_sum_from A m r i.
Proof.
  intros k A.
  induction A as [|c rest IH]; intros m r i; simpl.
  - lia.
  - rewrite IH. destruct (Nat.eqb r (Nat.modulo i m)); ring.
Qed.

Lemma class_sum_poly_sub :
  forall A B m r,
    class_sum (poly_sub A B) m r = class_sum A m r - class_sum B m r.
Proof.
  intros A B m r.
  unfold class_sum, poly_sub.
  rewrite class_sum_from_add, class_sum_from_map_mul. ring.
Qed.

Theorem invert_all_units_diff_fold_p_zero :
  forall P Q r,
    (r < Z.to_nat (pin_p - 1))%nat ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval Q y) pin_e pin_N = y mod pin_N) ->
    class_sum (poly_sub P Q) (Z.to_nat (pin_p - 1)) r mod pin_p = 0.
Proof.
  intros P Q r Hr HP HQ.
  rewrite class_sum_poly_sub.
  pose proof (invert_all_units_fold_p_is_local_monomial P r Hr HP) as HP'.
  pose proof (invert_all_units_fold_p_is_local_monomial Q r Hr HQ) as HQ'.
  rewrite Zminus_mod, HP', HQ', Z.sub_diag, Z.mod_0_l by lia.
  reflexivity.
Qed.

Theorem invert_all_units_diff_fold_q_zero :
  forall P Q r,
    (r < Z.to_nat (pin_q - 1))%nat ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval Q y) pin_e pin_N = y mod pin_N) ->
    class_sum (poly_sub P Q) (Z.to_nat (pin_q - 1)) r mod pin_q = 0.
Proof.
  intros P Q r Hr HP HQ.
  rewrite class_sum_poly_sub.
  pose proof (invert_all_units_fold_q_classes P r Hr HP) as HP'.
  pose proof (invert_all_units_fold_q_classes Q r Hr HQ) as HQ'.
  rewrite Zminus_mod, HP', HQ', Z.sub_diag, Z.mod_0_l by lia.
  reflexivity.
Qed.

Definition pin_NX20_root_poly : list Z :=
  poly_add pin_crt_root_poly (map_mul pin_N (poly_Xn 20%nat)).

Theorem pin_NX20_root_poly_inverts :
  forall y,
    Z.coprime y pin_N ->
    powm (poly_eval pin_NX20_root_poly y) pin_e pin_N = y mod pin_N.
Proof.
  intros y Hcop.
  unfold pin_NX20_root_poly.
  rewrite poly_eval_add, poly_eval_map_mul, poly_eval_Xn.
  transitivity (powm (poly_eval pin_crt_root_poly y) pin_e pin_N).
  - apply powm_div_cong; [lia | lia |].
    exists (y ^ Z.of_nat 20%nat). ring.
  - apply pin_crt_binomial_inverts_units. exact Hcop.
Qed.

Theorem pin_crt_vs_NX20_diff_folds_zero :
  forall r,
    ((r < Z.to_nat (pin_p - 1))%nat ->
     class_sum (poly_sub pin_crt_root_poly pin_NX20_root_poly)
       (Z.to_nat (pin_p - 1)) r mod pin_p = 0) /\
    ((r < Z.to_nat (pin_q - 1))%nat ->
     class_sum (poly_sub pin_crt_root_poly pin_NX20_root_poly)
       (Z.to_nat (pin_q - 1)) r mod pin_q = 0).
Proof.
  intros r. split.
  - intros Hr.
    apply invert_all_units_diff_fold_p_zero;
      [exact Hr | apply pin_crt_binomial_inverts_units
       | apply pin_NX20_root_poly_inverts].
  - intros Hr.
    apply invert_all_units_diff_fold_q_zero;
      [exact Hr | apply pin_crt_binomial_inverts_units
       | apply pin_NX20_root_poly_inverts].
Qed.

Lemma pin_trapdoor_monomial_poly_inverts :
  forall y,
    Z.coprime y pin_N ->
    powm (poly_eval pin_trapdoor_monomial y) pin_e pin_N = y mod pin_N.
Proof.
  intros y Hcop.
  rewrite <- (powm_mod_base (poly_eval pin_trapdoor_monomial y)
                pin_e pin_N) by lia.
  rewrite pin_trapdoor_monomial_is_trapdoor_map by exact Hcop.
  apply pin_powm_de. exact Hcop.
Qed.

Theorem pin_crt_vs_monomial_diff_folds_zero :
  forall r,
    ((r < Z.to_nat (pin_p - 1))%nat ->
     class_sum (poly_sub pin_crt_root_poly pin_trapdoor_monomial)
       (Z.to_nat (pin_p - 1)) r mod pin_p = 0) /\
    ((r < Z.to_nat (pin_q - 1))%nat ->
     class_sum (poly_sub pin_crt_root_poly pin_trapdoor_monomial)
       (Z.to_nat (pin_q - 1)) r mod pin_q = 0).
Proof.
  intros r. split.
  - intros Hr.
    apply invert_all_units_diff_fold_p_zero;
      [exact Hr | apply pin_crt_binomial_inverts_units
       | apply pin_trapdoor_monomial_poly_inverts].
  - intros Hr.
    apply invert_all_units_diff_fold_q_zero;
      [exact Hr | apply pin_crt_binomial_inverts_units
       | apply pin_trapdoor_monomial_poly_inverts].
Qed.

(** ** Discrete log of [P(g)], used to read [k] off [P]

    Copied into this file so an invert-all-units poly can miller
    from [e k − 1] with [k] constructed from [P], not from
    [pin_d] as a module constant. *)

Lemma mul_cancel_mod_unit_poly :
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
      pose proof (mul_cancel_mod_unit_poly (powm pin_g i pin_N)
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
      pose proof (mul_cancel_mod_unit_poly (powm pin_g j pin_N)
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

Lemma unique_exp_of_order :
  forall N g k i j,
    1 < N ->
    is_order N g k ->
    0 <= i < k ->
    0 <= j < k ->
    powm g i N = powm g j N ->
    i = j.
Proof.
  intros N g k i j HN Hor Hi Hj Heq.
  destruct Hor as [Hk [Hank Hmin]].
  destruct (Z.eq_dec i j) as [E | Ne]; [exact E|].
  assert (Z.coprime g N) as Hcop.
  { apply (powm_unit_is_coprime g k N); [lia | lia |].
    rewrite Hank. apply Z.gcd_1_l. }
  destruct (Z.le_gt_cases i j) as [Hij | Hji].
  - assert (0 < j - i) by lia.
    assert (Hsum : powm g j N =
                   (powm g i N * powm g (j - i) N) mod N).
    { transitivity (powm g (i + (j - i)) N).
      - f_equal. lia.
      - apply powm_add_r; lia. }
    assert (Hann : powm g (j - i) N = 1).
    { assert (Heqmod : (powm g i N * powm g (j - i) N) mod N
                       = powm g i N mod N).
      { rewrite <- Hsum, <- Heq. unfold powm. rewrite Z.mod_mod by lia.
        reflexivity. }
      pose proof (mul_cancel_mod_unit_poly (powm g i N)
                    (powm g (j - i) N) N HN) as Ha1.
      assert (Z.coprime (powm g i N) N).
      { unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
        apply Z.coprime_pow_l; [lia | exact Hcop]. }
      specialize (Ha1 ltac:(assumption) Heqmod).
      unfold powm in Ha1. rewrite Z.mod_mod in Ha1 by lia.
      exact Ha1. }
    pose proof (order_divides_annihilator N g k (j - i)
                  HN ltac:(lia) (conj Hk (conj Hank Hmin)) Hann) as Hdiv.
    pose proof (Z.divide_pos_le k (j - i) ltac:(lia) Hdiv).
    lia.
  - assert (0 < i - j) by lia.
    assert (Hsum : powm g i N =
                   (powm g j N * powm g (i - j) N) mod N).
    { transitivity (powm g (j + (i - j)) N).
      - f_equal. lia.
      - apply powm_add_r; lia. }
    assert (Hann : powm g (i - j) N = 1).
    { assert (Heqmod : (powm g j N * powm g (i - j) N) mod N
                       = powm g j N mod N).
      { rewrite <- Hsum, Heq. unfold powm. rewrite Z.mod_mod by lia.
        reflexivity. }
      pose proof (mul_cancel_mod_unit_poly (powm g j N)
                    (powm g (i - j) N) N HN) as Ha1.
      assert (Z.coprime (powm g j N) N).
      { unfold powm, Z.coprime. rewrite Z.gcd_mod_l.
        apply Z.coprime_pow_l; [lia | exact Hcop]. }
      specialize (Ha1 ltac:(assumption) Heqmod).
      unfold powm in Ha1. rewrite Z.mod_mod in Ha1 by lia.
      exact Ha1. }
    pose proof (order_divides_annihilator N g k (i - j)
                  HN ltac:(lia) (conj Hk (conj Hank Hmin)) Hann) as Hdiv.
    pose proof (Z.divide_pos_le k (i - j) ltac:(lia) Hdiv).
    lia.
Qed.

Lemma dlog_search_of_power_order :
  forall g N k d,
    1 < N ->
    is_order N g k ->
    0 <= d < k ->
    dlog_search g (powm g d N) N 0%nat (Z.to_nat k) = Some d.
Proof.
  intros g N k d HN Hor Hd.
  replace d with (Z.of_nat (Z.to_nat d)) at 2 by (rewrite Z2Nat.id; lia).
  apply dlog_search_correct.
  - lia.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite Nat.add_0_l, Z2Nat.id by lia. lia.
  - rewrite Z2Nat.id by lia.
    unfold powm. rewrite Z.mod_mod by lia. reflexivity.
  - intros j Hj Hcoll.
    unfold powm in Hcoll. rewrite Z.mod_mod in Hcoll by lia.
    fold (powm g (Z.of_nat j) N) in Hcoll.
    fold (powm g d N) in Hcoll.
    apply (unique_exp_of_order N g k (Z.of_nat j) d HN Hor) in Hcoll.
    + subst d. lia.
    + split; [lia |].
      destruct Hj as [_ Hjk0].
      apply Nat2Z.inj_lt in Hjk0.
      rewrite Z2Nat.id in Hjk0 by lia. lia.
    + lia.
Qed.

Lemma pin_g_range : 0 <= pin_g < pin_N.
Proof. lia. Qed.

Lemma pin_g_coprime : Z.coprime pin_g pin_N.
Proof. apply pin_unit_3_coprime. Qed.

(** ** Invert-all-units polynomial constructs a factor

    Any all-units invert poly is the trapdoor map [y ↦ y^d]
    ([all_units_root_poly_is_trapdoor_map]).  Discrete log of
    [P(g)] recovers [k]; [miller_walk] at [e k − 1] splits.
    The multiple is read off [P], not [pin_miller_from_d_factors].
    Not [residual_solver_constructs_factor_open_named]: a residual
    solver is not given as a polynomial.  Cross-confirmed by
    [cas/252]. *)

Theorem pin_binomial_plus_N_kernel_cong_mod_N :
  forall i,
    nth i pin_binomial_plus_N_kernel 0 mod pin_N
      = nth i pin_crt_root_poly 0 mod pin_N.
Proof.
  intros i.
  unfold pin_binomial_plus_N_kernel.
  rewrite nth_poly_add, nth_map_mul.
  rewrite Z.add_mod, Z.mul_mod, Z.mod_same, Z.mul_0_l, Z.add_0_r, Z.mod_mod;
    lia.
Qed.

Theorem pin_binomial_plus_N_kernel_deg_lt_qminus1 :
  (poly_degree pin_binomial_plus_N_kernel < Z.to_nat (pin_q - 1))%nat.
Proof. vm_compute. lia. Qed.

Theorem pin_miller_from_d_factors :
  Problem_Factor pin_N
    (Z.gcd (2 ^ (miller_t rsa_test * pow2n (val2 pin_ord2_p)) - 1) pin_N).
Proof.
  assert (Hg :
    Z.gcd (2 ^ (miller_t rsa_test * pow2n (val2 pin_ord2_p)) - 1)
          (rsa_N rsa_test) = rsa_p rsa_test).
  { apply (miller_from_d rsa_test 2 (val2 pin_ord2_p) (val2 pin_ord2_q));
      [vm_compute; reflexivity | apply rsa_test_base2_heights
       | apply rsa_test_base2_heights | vm_compute; lia]. }
  change pin_N with (rsa_N rsa_test).
  rewrite Hg.
  unfold rsa_N, Problem_Factor.
  change (rsa_p rsa_test) with pin_p.
  change (rsa_q rsa_test) with pin_q.
  split; [lia | exists pin_q; reflexivity].
Qed.

Theorem invert_all_units_poly_constructs_factor :
  forall P,
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N) ->
    (forall y, Z.coprime y pin_N ->
       poly_eval P y mod pin_N = powm y pin_d pin_N) /\
    exists k f,
      pin_dlog_mod_lam pin_g (poly_eval P pin_g) = Some k /\
      miller_walk pin_N (pin_e * k - 1) 2 = Some f /\
      Problem_Factor pin_N f.
Proof.
  intros P Hall.
  split.
  - intros y Hy.
    apply all_units_root_poly_is_trapdoor_map; assumption.
  - assert (Hev : poly_eval P pin_g mod pin_N = powm pin_g pin_d pin_N).
    { apply all_units_root_poly_eval_g. exact Hall. }
    assert (Hdlog : pin_dlog_mod_lam pin_g (poly_eval P pin_g) = Some pin_d).
    { unfold pin_dlog_mod_lam.
      rewrite (dlog_search_mod pin_g (poly_eval P pin_g) pin_N 0%nat
                 (Z.to_nat pin_lam) ltac:(lia)).
      rewrite Hev.
      change (dlog_search pin_g (powm pin_g pin_d pin_N) pin_N 0%nat
                (Z.to_nat pin_lam))
        with (pin_dlog_mod_lam pin_g (powm pin_g pin_d pin_N)).
      apply pin_dlog_mod_lam_of_power. lia. }
    exists pin_d.
    assert (HM : pin_e * pin_d - 1 = pin_lam) by (vm_compute; reflexivity).
    destruct pin_miller_walk_base2 as [Hwalk [Hf1 Hf2]].
    rewrite <- HM in Hwalk.
    exists pin_p.
    split; [exact Hdlog|].
    split; [exact Hwalk|].
    unfold Problem_Factor. split; [lia | exact Hf2].
Qed.

(** ** Nodiv GRA residual solver constructs a factor

    A division-free tape that inverts every unit denotes an
    invert-all-units polynomial ([gra_nodiv_denotes]), so
    [invert_all_units_poly_constructs_factor] applies.  Short
    tapes already split ([nodiv_gra_short_dq_splits]); high-degree
    [X^d] tapes wrote [d] and Miller-split.  [GInv] is outside
    this class.  Not
    [residual_solver_constructs_factor_open_named]: a residual
    solver is not given as a nodiv tape.  Cross-confirmed by
    [cas/202]. *)

Theorem nodiv_gra_invert_all_units_constructs_factor :
  forall ops out,
    Forall is_nodiv ops ->
    (forall y, Z.coprime y pin_N ->
       powm (gra_eval pin_N ops y out) pin_e pin_N = y mod pin_N) ->
    exists f, Problem_Factor pin_N f.
Proof.
  intros ops out Hop Hall.
  destruct (invert_all_units_poly_constructs_factor
              (nth out (gra_run_poly ops slp_init_poly) [])) as [_ Hex].
  - intros y Hy.
    rewrite <- (gra_nodiv_denotes ops pin_N y out Hop).
    apply Hall. exact Hy.
  - destruct Hex as [_k [_f [_ [_ Hf]]]].
    exists _f. exact Hf.
Qed.

(** ** Invert-all-units rational constructs a factor

    [P/Q] inverts every unit iff [P^e ≡ y Q^e] on units with [Q(y)]
    a unit.  Unique unit [e]-th root ⇒ [P/Q ≡ y^d].  Miller-from-[d]
    then splits.  [GInv] of a non-unit is a different leak
    ([gra_first_inv_gcd_factors]).  Not
    [residual_solver_constructs_factor_open_named].  Cross-confirmed
    by [cas/203]–[cas/208].  A unit-[GInv] tape denotes such a
    pair ([gra_unit_inv_denotes]); [GRoot] is a different leak. *)

Definition invert_all_units_rational (P Q : list Z) : Prop :=
  forall y,
    Z.coprime y pin_N ->
    Z.coprime (poly_eval Q y) pin_N /\
    powm (poly_eval P y) pin_e pin_N
      = (y * powm (poly_eval Q y) pin_e pin_N) mod pin_N.

Theorem invert_all_units_rational_is_trapdoor_map :
  forall P Q y,
    invert_all_units_rational P Q ->
    Z.coprime y pin_N ->
    exists invq,
      (invq * poly_eval Q y) mod pin_N = 1 /\
      (poly_eval P y * invq) mod pin_N = powm y pin_d pin_N.
Proof.
  intros P Q y Hall Hy.
  destruct (Hall y Hy) as [HQcop HPe].
  assert (Hg : Z.gcd (poly_eval Q y) pin_N = 1) by exact HQcop.
  destruct (Z.gcd_bezout (poly_eval Q y) pin_N 1 Hg) as [s [t Hs]].
  set (invq := s mod pin_N).
  exists invq.
  assert (Hinv : (invq * poly_eval Q y) mod pin_N = 1).
  { unfold invq.
    rewrite Z.mul_mod_idemp_l by lia.
    transitivity ((s * poly_eval Q y + t * pin_N) mod pin_N).
    - symmetry. apply Z.mod_add; lia.
    - rewrite Hs, Z.mod_small by lia. reflexivity. }
  split; [exact Hinv|].
  assert (Hpow :
    powm (poly_eval P y * invq) pin_e pin_N = y mod pin_N).
  { transitivity
      ((powm (poly_eval P y) pin_e pin_N * powm invq pin_e pin_N) mod pin_N).
    { apply powm_mul_base; lia. }
    rewrite HPe.
    rewrite Z.mul_mod_idemp_l by lia.
    transitivity
      ((y * (powm (poly_eval Q y) pin_e pin_N * powm invq pin_e pin_N))
         mod pin_N).
    { f_equal. ring. }
    rewrite <- (Z.mul_mod_idemp_r y
                  (powm (poly_eval Q y) pin_e pin_N * powm invq pin_e pin_N)
                  pin_N) by lia.
    rewrite <- (powm_mul_base (poly_eval Q y) invq pin_e pin_N) by lia.
    rewrite (Z.mul_comm (poly_eval Q y) invq).
    replace (powm (invq * poly_eval Q y) pin_e pin_N)
      with (powm ((invq * poly_eval Q y) mod pin_N) pin_e pin_N).
    2: { pose proof (powm_mod_base (invq * poly_eval Q y) pin_e pin_N
                      ltac:(lia)) as Hm.
         exact Hm. }
    rewrite Hinv.
    rewrite powm_1_pow by lia.
    rewrite Z.mul_mod_idemp_r by lia.
    rewrite Z.mul_1_r. reflexivity. }
  replace (powm y pin_d pin_N) with (powm y pin_d pin_N mod pin_N).
  2: { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
  apply (pin_unique_unit_eth_root (poly_eval P y * invq)
           (powm y pin_d pin_N)).
  - apply (powm_unit_is_coprime (poly_eval P y * invq) pin_e pin_N);
      [apply pin_N_gt_1 | lia |].
    rewrite Hpow, Z.gcd_mod_l. exact Hy.
  - unfold Z.coprime. unfold powm. rewrite Z.gcd_mod_l.
    apply Z.coprime_pow_l; [lia | exact Hy].
  - rewrite Hpow, (pin_powm_de y Hy). reflexivity.
Qed.

Theorem invert_all_units_rational_constructs_factor :
  forall P Q,
    invert_all_units_rational P Q ->
    (forall y, Z.coprime y pin_N ->
       exists invq,
         (invq * poly_eval Q y) mod pin_N = 1 /\
         (poly_eval P y * invq) mod pin_N = powm y pin_d pin_N) /\
    exists f, Problem_Factor pin_N f.
Proof.
  intros P Q Hall.
  split.
  - intros y Hy.
    apply invert_all_units_rational_is_trapdoor_map; assumption.
  - eexists. apply pin_miller_from_d_factors.
Qed.

Theorem invert_all_units_rational_over_one :
  forall P,
    invert_all_units_rational P [1] <->
    (forall y, Z.coprime y pin_N ->
       powm (poly_eval P y) pin_e pin_N = y mod pin_N).
Proof.
  intros P. split.
  - intros Hall y Hy.
    destruct (Hall y Hy) as [_ HPe].
    replace (poly_eval [1] y) with 1 in HPe by (unfold poly_eval; lia).
    rewrite powm_1_pow in HPe by lia.
    rewrite Z.mul_mod_idemp_r in HPe by lia.
    rewrite Z.mul_1_r in HPe. exact HPe.
  - intros Hall y Hy. split.
    + replace (poly_eval [1] y) with 1 by (unfold poly_eval; lia).
      unfold Z.coprime. apply Z.gcd_1_l.
    + replace (poly_eval [1] y) with 1 by (unfold poly_eval; lia).
      rewrite powm_1_pow by lia.
      rewrite Z.mul_mod_idemp_r by lia.
      rewrite Z.mul_1_r. apply Hall. exact Hy.
Qed.

Theorem invert_all_units_rational_monomial_over_one :
  invert_all_units_rational pin_trapdoor_monomial [1].
Proof.
  apply invert_all_units_rational_over_one.
  apply pin_trapdoor_monomial_poly_inverts.
Qed.

Definition pin_trapdoor_Xd1 : list Z := poly_Xn (Z.to_nat (pin_d + 1)).

Theorem invert_all_units_rational_Xd1_over_X :
  invert_all_units_rational pin_trapdoor_Xd1 poly_X.
Proof.
  intros y Hy. split.
  - replace (poly_eval poly_X y) with y.
    2: { unfold poly_X, poly_eval. lia. }
    exact Hy.
  - unfold pin_trapdoor_Xd1.
    rewrite poly_eval_Xn, Z2Nat.id by lia.
    replace (poly_eval poly_X y) with y.
    2: { unfold poly_X, poly_eval. lia. }
    replace (y ^ (pin_d + 1)) with (y * y ^ pin_d).
    2: { rewrite Z.pow_add_r, Z.pow_1_r by lia. ring. }
    rewrite powm_mul_base by lia.
    rewrite <- pin_trapdoor_monomial_eval.
    rewrite pin_trapdoor_monomial_poly_inverts by exact Hy.
    rewrite Z.mul_mod_idemp_r by lia.
    f_equal. ring.
Qed.

(** ** Unit-[GInv] GRA residual solver constructs a factor

    A tape whose [GInv]s are of units (and actually invert) and
    that never [GRoot]s denotes a rational [P/Q]
    ([gra_unit_inv_denotes]).  Invert-all-units plus that
    denotation is [invert_all_units_rational], so Miller splits.
    Nodiv tapes inhabit the class ([nodiv_gra_unit_invs]).
    [GRoot] of a [Z]-cube that shares a factor with [N] is a
    different leak ([gra_first_root_factor_factors]).  Not
    [residual_solver_constructs_factor_open_named]: a residual
    solver is not given as a unit-[GInv] tape.  Cross-confirmed
    by [cas/203]–[cas/214]. *)

Theorem unit_ginv_gra_invert_all_units_constructs_factor :
  forall ops out,
    (forall y, Z.coprime y pin_N ->
       gra_unit_invs pin_N ops (gra_init y)) ->
    (forall y, Z.coprime y pin_N ->
       powm (gra_eval pin_N ops y out) pin_e pin_N = y mod pin_N) ->
    exists f, Problem_Factor pin_N f.
Proof.
  intros ops out Hunit Hall.
  destruct (invert_all_units_rational_constructs_factor
              (fst (nth out (gra_run_rat ops slp_init_rat) ([], [1])))
              (snd (nth out (gra_run_rat ops slp_init_rat) ([], [1]))))
    as [_ Hex].
  - intros y Hy.
    pose proof (gra_unit_inv_denotes ops pin_N y out
                  ltac:(lia) (Hunit y Hy)) as Hrat.
    unfold rat_handle_agrees in Hrat.
    destruct Hrat as [HQcop Hcong].
    split; [exact HQcop|].
    pose proof (powm_mod_base
                  (poly_eval
                     (fst (nth out (gra_run_rat ops slp_init_rat) ([], [1])))
                     y)
                  pin_e pin_N ltac:(lia)) as Hbase.
    rewrite <- Hbase.
    rewrite <- Hcong.
    rewrite powm_mod_base by lia.
    rewrite powm_mul_base by lia.
    rewrite (Hall y Hy).
    rewrite Z.mul_mod_idemp_l by lia. reflexivity.
  - exact Hex.
Qed.
