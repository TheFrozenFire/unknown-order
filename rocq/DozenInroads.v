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
  gra_jacobi_gate 2 11 17 = -1.
Proof. vm_compute. reflexivity. Qed.

Theorem dozen_jacobi_gate_forces_odd :
  Z.Odd 81.
Proof. exists 40. lia. Qed.

(** ** 2. SAGM on both [x] and [y] in base [g=3] *)

Theorem dozen_sagm_both_pin :
  powm (powm 3 54 187) 3 187 = powm 3 2 187 /\
  powm 3 2 187 = 9.
Proof. vm_compute. split; reflexivity. Qed.

Theorem dozen_sagm_ae_eq_c_mod_lambda :
  (54 * 3 - 2) mod 80 = 0.
Proof. vm_compute. reflexivity. Qed.

(** ** 3. Related queries with coprime exponents (Shamir) *)

Theorem dozen_related_coprime_exps :
  powm 32 3 187 = 43 /\
  powm 64 5 187 = powm 43 2 187 /\
  Z.gcd 3 5 = 1 /\
  powm 32 (2 * 3) 187 = powm 64 5 187.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem dozen_related_shamir_gcd :
  forall e1 e2,
    Z.gcd e1 e2 = 1 ->
    Z.gcd e2 e1 = 1.
Proof. intros e1 e2 H. rewrite Z.gcd_comm. exact H. Qed.

(** ** 4. Higher residue: 5th-power Euler on [p=11] *)

Theorem dozen_fifth_divides_pminus1 :
  (5 | 10).
Proof. exists 2. reflexivity. Qed.

Theorem dozen_fifth_power_euler :
  powm 32 2 11 = 1.
Proof. vm_compute. reflexivity. Qed.

(** ** 5. One-sided [a^{e-1}] *)

Theorem dozen_onesided_e11 :
  Z.gcd (2 ^ 10 - 1) 187 = 11 /\
  Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
Qed.

Theorem dozen_e11_residual_shaped :
  srsa_residual_leaf 187 80 (powm 2 11 187) 2 11.
Proof.
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 5; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

(** ** 6. Short [e] vs long [e] on this pin *)

Theorem dozen_short_e3 :
  3 < 4 /\ 81 > 4.
Proof. split; lia. Qed.

Theorem dozen_short_e_is_residual_cube :
  srsa_residual_leaf 187 80 36 42 3.
Proof. apply srsa_residual_pin. Qed.

(** ** 7. Bounded advice on [N] *)

Theorem dozen_advice_bit_no_split :
  187 mod 2 = 1 /\ Z.gcd 1 187 = 1.
Proof. split; reflexivity. Qed.

Theorem dozen_advice_div_splits :
  187 / 17 = 11 /\ Problem_Factor 187 11.
Proof.
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. split; [lia|]. exists 17. reflexivity.
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
  11 mod 4 = 3 /\ 23 mod 4 = 3 /\
  lambda_semiprime 11 23 = 110.
Proof. split; [reflexivity|]. split; [reflexivity|]. vm_compute. reflexivity. Qed.

Theorem dozen_blum_e5_names_p :
  Z.gcd 5 110 = 5 /\ 2 * 5 + 1 = 11 /\ (11 | 253).
Proof. split; [reflexivity|]. split; [reflexivity|]. exists 23. reflexivity. Qed.

Theorem dozen_blum_e11_names_q :
  Z.gcd 11 110 = 11 /\ 2 * 11 + 1 = 23 /\ (23 | 253).
Proof. split; [vm_compute; reflexivity|]. split; [reflexivity|]. exists 11. reflexivity. Qed.

(** ** 9. Census: every unit is an [e=3] residual witness *)

Theorem dozen_phi_160 :
  phi_semiprime 11 17 = 160.
Proof. vm_compute. reflexivity. Qed.

Theorem dozen_every_unit_is_cube :
  forall y,
    Z.coprime y 187 ->
    powm (powm y 27 187) 3 187 = y mod 187.
Proof.
  intros y Hcop.
  change 187 with (rsa_N rsa_test).
  change 27 with (rsa_d rsa_test).
  change 3 with (rsa_e rsa_test).
  apply rsa_units_are_eth_powers. exact Hcop.
Qed.

(** ** 10. GQ extract is residual, not a factor *)

Theorem dozen_gq_extract_is_residual :
  srsa_residual_leaf 187 80 36 42 3 /\
  Z.gcd 42 187 = 1.
Proof. split; [apply srsa_residual_pin | vm_compute; reflexivity]. Qed.

Theorem dozen_gq_complete_still :
  gq_verify 36 3 (gq_commit 1 3 187) 1 (gq_response 1 42 1 187) 187.
Proof. apply cpp17_complete_pin. Qed.

(** ** 11. Integer polynomial in [N] *)

Theorem dozen_N_cong_q :
  187 mod 10 = 17 mod 10.
Proof. apply (N_cong_q_mod_pminus1 11 17). lia. Qed.

Theorem dozen_gcd_Nminus1_pminus1 :
  Z.gcd (187 - 1) 10 = 2.
Proof. vm_compute. reflexivity. Qed.

(** ** 12. [gcd(e−1, λ)] proper, not [λ] and not [2] *)

Theorem dozen_e11_minus1_shares_lambda :
  Z.gcd (11 - 1) 80 = 10 /\
  2 < 10 < 80 /\
  ~ (80 | 10).
Proof.
  split; [vm_compute; reflexivity|].
  split; [lia|].
  intros [k Hk]. nia.
Qed.
