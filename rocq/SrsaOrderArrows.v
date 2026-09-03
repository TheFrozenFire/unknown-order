From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import Order.
Require Import StrongRSAPeel.

Open Scope Z_scope.

(** * Order / residual Strong RSA / Factor arrows

    Invert in [⟨y⟩] from [ord(y)] always (equality / multiply).
    A leftover pair factors [N] only under KeyGen mismatch
    ([one_sided_low_order]).  Matching local orders on [N=pin_247] do
    not yield a proper factor.  A leftover pair is not a residual
    *solver*; solver ⇒ factor is
    [residual_solver_constructs_factor_open_named].
    Cross-confirmed by [cas/145]. *)

(** ** Order of the pin challenge *)

Theorem is_order_pin_y_40 :
  is_order pin_N pin_y pin_y_ord.
Proof.
  replace pin_y_ord with (Z.lcm pin_y_ord_p pin_y_ord_q) by (vm_compute; reflexivity).
  apply (order_semiprime_from_locals pin_p pin_q pin_y pin_y_ord_p pin_y_ord_q);
    [apply pin_p_prime | apply pin_q_prime | apply pin_p_neq_q | vm_compute; reflexivity | | ].
  - apply is_order_by_vm; [lia | vm_compute; reflexivity | vm_compute; reflexivity].
  - apply is_order_by_vm; [lia | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Theorem order_yields_residual_sRSA :
  forall N y k e d lam,
    1 < N ->
    0 <= y < N ->
    is_order N y k ->
    Z.coprime y N ->
    1 < e ->
    0 <= d ->
    (e * d) mod k = 1 ->
    Z.Odd e ->
    Z.gcd e lam = 1 ->
    ~ (lam | e - 1) ->
    srsa_residual_leaf N lam y (powm y d N) e.
Proof.
  intros N y k e d lam HN Hy Hord Hcop He Hd Hinv Hodd Hgcd Hndiv.
  unfold srsa_residual_leaf.
  split; [exact Hcop|].
  split; [apply (order_yields_strong_RSA N y k e d); assumption|].
  split; [exact Hodd|].
  split; [exact Hgcd | exact Hndiv].
Qed.

Theorem order_yields_residual_pin :
  srsa_residual_leaf pin_N pin_lam pin_y (powm pin_y pin_d pin_N) pin_e.
Proof.
  apply (order_yields_residual_sRSA pin_N pin_y pin_y_ord pin_e pin_d pin_lam).
  - lia.
  - lia.
  - apply is_order_pin_y_40.
  - vm_compute; reflexivity.
  - lia.
  - lia.
  - reflexivity.
  - exists 1; lia.
  - reflexivity.
  - intros [t Ht]. nia.
Qed.

Theorem order_invert_pin_is_cube_root :
  powm pin_y pin_d pin_N = pin_x /\
  powm pin_x pin_e pin_N = pin_y.
Proof. vm_compute. split; reflexivity. Qed.

(** ** Mismatch ⇒ Factor; matching local orders do not *)

(** The residual leaf is unused: mismatch is the load-bearing
    hypothesis.  The leaf is in the type so the arrow is not
    [srsa_residual_leaf] as [Problem_Factor] on its own.  The
    factor is the public [gcd(x^k−1, N)], not a named prime. *)
Theorem residual_mismatch_factors :
  forall p q y x e k lam,
    Z.prime p -> Z.prime q -> p <> q ->
    srsa_residual_leaf (p * q) lam y x e ->
    one_sided_low_order p q x k ->
    Z.gcd (powm x k (p * q) - 1) (p * q) = p /\
    Problem_Factor (p * q) (Z.gcd (powm x k (p * q) - 1) (p * q)).
Proof.
  intros p q y x e k lam Hp Hq Hneq _ Hone.
  apply leftover_mismatch_factors with (x := x) (k := k); assumption.
Qed.

Theorem leftover_x_one_sided_pin :
  one_sided_low_order pin_p pin_q pin_x pin_x_k.
Proof.
  unfold one_sided_low_order.
  split; [vm_compute; reflexivity|].
  split; [lia|].
  split; [vm_compute; reflexivity | vm_compute; discriminate].
Qed.

Theorem leftover_x_mismatch_factors_pin :
  Z.gcd (powm pin_x pin_x_k pin_N - 1) pin_N = pin_p /\
  Problem_Factor pin_N (Z.gcd (powm pin_x pin_x_k pin_N - 1) pin_N).
Proof.

  apply leftover_mismatch_factors with (x := pin_x) (k := pin_x_k);
    [apply pin_p_prime | apply pin_q_prime | discriminate | apply leftover_x_one_sided_pin].
Qed.

Theorem residual_mismatch_factors_pin :
  srsa_residual_leaf pin_N pin_lam pin_y pin_x pin_e ->
  one_sided_low_order pin_p pin_q pin_x pin_x_k ->
  Z.gcd (powm pin_x pin_x_k pin_N - 1) pin_N = pin_p /\
  Problem_Factor pin_N (Z.gcd (powm pin_x pin_x_k pin_N - 1) pin_N).
Proof.
  intros _ Hone.

  apply leftover_mismatch_factors with (x := pin_x) (k := pin_x_k);
    [apply pin_p_prime | apply pin_q_prime | discriminate | exact Hone].
Qed.

Theorem leftover_y_one_sided_pin :
  one_sided_low_order pin_p pin_q pin_y pin_x_k.
Proof.
  unfold one_sided_low_order.
  split; [vm_compute; reflexivity|].
  split; [lia|].
  split; [vm_compute; reflexivity | vm_compute; discriminate].
Qed.

Theorem order_mismatch_factors_pin :
  Z.gcd (powm pin_y pin_x_k pin_N - 1) pin_N = pin_p /\
  Problem_Factor pin_N (Z.gcd (powm pin_y pin_x_k pin_N - 1) pin_N).
Proof.

  apply leftover_mismatch_factors with (x := pin_y) (k := pin_x_k);
    [apply pin_p_prime | apply pin_q_prime | discriminate | apply leftover_y_one_sided_pin].
Qed.

Theorem leftover_77_one_sided :
  one_sided_low_order pin_77_p pin_77_q pin_77_x 3.
Proof.
  unfold one_sided_low_order.
  split; [vm_compute; reflexivity|].
  split; [lia|].
  split; [vm_compute; reflexivity | vm_compute; discriminate].
Qed.

Theorem leftover_77_mismatch_factors :
  Z.gcd (powm pin_77_x 3 pin_77 - 1) pin_77 = pin_77_p /\
  Problem_Factor pin_77 (Z.gcd (powm pin_77_x 3 pin_77 - 1) pin_77).
Proof.

  apply leftover_mismatch_factors with (x := pin_77_x) (k := 3);
    [apply prime_7 | apply prime_11 | discriminate | apply leftover_77_one_sided].
Qed.

(** Matching local orders: the [k=5] that splits leftover [x] on
    [N=pin_N] is not one-sided on [N=pin_247], and the gcd is not a
    proper factor. *)

Theorem matching_247_not_one_sided :
  ~ one_sided_low_order pin_247_p pin_247_q pin_247_x pin_247_e.
Proof.
  unfold one_sided_low_order.
  intros [_ [_ [Hp Hq]]].
  vm_compute in Hp. discriminate.
Qed.

Theorem matching_247_gcd_not_proper :
  Z.gcd (powm pin_247_x pin_247_e pin_247 - 1) pin_247 = 1 /\
  ~ Problem_Factor pin_247 (Z.gcd (powm pin_247_x pin_247_e pin_247 - 1) pin_247).
Proof.
  assert (Hg : Z.gcd (powm pin_247_x pin_247_e pin_247 - 1) pin_247 = 1)
    by (vm_compute; reflexivity).
  split; [exact Hg|].
  intros [Hlt _]. rewrite Hg in Hlt. lia.
Qed.

Theorem matching_247_two_sided_gcd_is_N :
  Z.gcd (powm pin_247_x 6 pin_247 - 1) pin_247 = pin_247 /\
  ~ Problem_Factor pin_247 pin_247.
Proof.
  split; [vm_compute; reflexivity|].
  intros [Hlt _]. lia.
Qed.
