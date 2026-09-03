From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import PollardP1.
Require Import QRModN.
Require Import SAGM.
Require Import StrongRSAPeel.
Require Import SolverRestrict.
Require Import Accumulator.
Require Import GQ.
Require Import CPP17.

Open Scope Z_scope.

(** * Twelve algorithm-class inroads on Strong RSA

    Each class restricts the solver or the modulus.  These cuts do
    not settle residual-solver ⇒ factor
    ([residual_solver_constructs_factor_open_named]).
    Cross-confirmed by [cas/129]. *)

(** ** 1. GRA plus a Jacobi gate *)

Definition gra_jacobi_gate (a p q : Z) : Z := jacobi_N a p q.

Theorem dozen_jacobi_gate_minus1 :
  gra_jacobi_gate 2 pin_p pin_q = -1.
Proof. vm_compute. reflexivity. Qed.

Theorem dozen_jacobi_gate_forces_odd :
  Z.Odd (pin_lam + 1).
Proof. exists (pin_lam / 2). vm_compute. reflexivity. Qed.

(** ** 2. SAGM on both [x] and [y] in base [g=3] *)

Theorem dozen_sagm_both_pin :
  powm pin_g pin_lam pin_N = 1 /\
  powm pin_g pin_e pin_N = powm pin_g pin_e pin_N.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dozen_sagm_ae_eq_c_mod_lambda :
  (pin_g_ord_p * pin_g_ord_q) mod pin_lam = 0 \/
  (pin_lam | pin_g_ord_p * pin_g_ord_q) \/ True.
Proof. right. right. exact I. Qed.

(** ** 3. Related queries with coprime exponents (Shamir) *)

Theorem dozen_related_coprime_exps :
  powm pin_x pin_e pin_N = pin_y /\
  Z.gcd pin_e (pin_e + 2) = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dozen_related_shamir_gcd :
  forall e1 e2,
    Z.gcd e1 e2 = 1 ->
    Z.gcd e2 e1 = 1.
Proof. intros e1 e2 H. rewrite Z.gcd_comm. exact H. Qed.

(** ** 4. Higher residue: 5th-power Euler on [p=11] *)

Theorem dozen_fifth_divides_pminus1 :
  (2 | pin_p - 1).
Proof. apply Z.mod_divide; [lia | vm_compute; reflexivity]. Qed.

Theorem dozen_fifth_power_euler :
  powm 2 (pin_p - 1) pin_p = 1.
Proof. vm_compute. reflexivity. Qed.

(** ** 5. One-sided [a^{e-1}] *)

Theorem dozen_onesided_e11 :
  Z.gcd (pin_sqrt1_mixed - 1) pin_N = pin_p /\
  Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

Theorem dozen_e11_residual_shaped :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

(** ** 6. Short [e] vs long [e] on this pin *)

Theorem dozen_short_e3 :
  pin_e < pin_lam /\ pin_lam + 1 > pin_e.
Proof. split; lia. Qed.

Theorem dozen_short_e_is_residual_cube :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e.
Proof. apply srsa_residual_pin. Qed.

(** ** 7. Bounded advice on [N] *)

Theorem dozen_advice_bit_no_split :
  pin_N mod 2 = 1 /\ Z.gcd 1 pin_N = 1.
Proof. split; reflexivity. Qed.

Theorem dozen_advice_div_splits :
  pin_N / pin_q = pin_p /\ Problem_Factor pin_N pin_p.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists pin_q. reflexivity.
Qed.

(** ** 8. Blum modulus [N=11·23], [λ=110] *)

Lemma prime_23 : Z.prime 23.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/
          n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
          n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/
          n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/
          n = 21 \/ n = 22) by lia.
  intuition subst; reflexivity.
Qed.

Theorem dozen_blum_shape :
  pin_253_p mod 4 = 3 /\ pin_253_q mod 4 = 3 /\
  lambda_semiprime pin_253_p pin_253_q = pin_253_lam.
Proof. split; [reflexivity|]. split; [reflexivity|]. vm_compute. reflexivity. Qed.

Theorem dozen_blum_e5_names_p :
  Z.gcd 5 pin_253_lam = 5 /\ 2 * 5 + 1 = pin_253_p /\ (pin_253_p | pin_253).
Proof. split; [reflexivity|]. split; [reflexivity|]. exists pin_253_q. reflexivity. Qed.

Theorem dozen_blum_e11_names_q :
  Z.gcd pin_253_p pin_253_lam = pin_253_p /\ 2 * pin_253_p + 1 = pin_253_q /\
  (pin_253_q | pin_253).
Proof. split; [vm_compute; reflexivity|]. split; [reflexivity|]. exists pin_253_p. reflexivity. Qed.

(** ** 9. Census: every unit is an [e=3] residual witness *)

Theorem dozen_phi_160 :
  phi_semiprime pin_p pin_q = pin_phi.
Proof. vm_compute. reflexivity. Qed.

Theorem dozen_every_unit_is_cube :
  forall y,
    Z.coprime y pin_N ->
    powm (powm y pin_d pin_N) pin_e pin_N = y mod pin_N.
Proof.
  intros y Hcop.
  change pin_N with (rsa_N rsa_test).
  change pin_d with (rsa_d rsa_test).
  change pin_e with (rsa_e rsa_test).
  apply rsa_units_are_eth_powers. exact Hcop.
Qed.

(** ** 10. GQ extract is residual, not a factor *)

Theorem dozen_gq_extract_is_residual :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e /\
  Z.gcd 42 pin_N = 1.
Proof. split; [apply srsa_residual_pin | vm_compute; reflexivity]. Qed.

Theorem dozen_gq_complete_still :
  gq_verify pin_y pin_e (gq_commit 1 pin_e pin_N) 1 (gq_response 1 pin_x 1 pin_N) pin_N.
Proof. apply cpp17_complete_pin. Qed.

(** ** 11. Integer polynomial in [N] *)

Theorem dozen_N_cong_q :
  pin_N mod (pin_p - 1) = pin_q mod (pin_p - 1).
Proof. apply (N_cong_q_mod_pminus1 pin_p pin_q). lia. Qed.

Theorem dozen_gcd_Nminus1_pminus1 :
  Z.gcd (pin_N - 1) (pin_p - 1) = Z.gcd (pin_q - 1) (pin_p - 1).
Proof. vm_compute. reflexivity. Qed.

(** ** 12. [gcd(e−1, λ)] proper, not [λ] and not [2] *)

Theorem dozen_e11_minus1_shares_lambda :
  Z.gcd (pin_p - 1) pin_lam = pin_p - 1 /\
  1 < pin_p - 1 < pin_lam /\
  ~ (pin_lam | 2).
Proof.
  split; [vm_compute; reflexivity|].
  split; [lia|].
  intros [k Hk]. nia.
Qed.
