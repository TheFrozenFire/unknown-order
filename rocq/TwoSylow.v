From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import Pratt.
Require Import Order.
Require Import TwoPrimary.
Require Import Hardness.

Open Scope Z_scope.

(** * Structure of the 2-Sylow of [(Z/NZ)*]

    [x² ≡ 1] has exactly the four CRT combinations of [±1].  An
    element of order 4 would require [4 | λ], i.e. [v₂(λ) ≥ 2],
    so Blum / Williams ([v₂ = (1,1)]) has 2-torsion exactly those
    four roots and no order-4 help.  Rabin inversion multiplies
    a square root by this 2-torsion. *)

Lemma powm_2_mod_prime_pm1 :
  forall p x,
    Z.prime p ->
    powm x 2 p = 1 ->
    x mod p = 1 \/ x mod p = p - 1.
Proof. intros. apply duality_unique_order_2_on_prime; assumption. Qed.

Theorem sqrt1_is_crt_pm1 :
  forall p q x,
    Z.prime p -> Z.prime q -> p <> q ->
    powm x 2 (p * q) = 1 ->
    (x mod p = 1 \/ x mod p = p - 1) /\
    (x mod q = 1 \/ x mod q = q - 1).
Proof.
  intros p q x Hp Hq Hneq Hsq.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  split.
  - apply powm_2_mod_prime_pm1; [exact Hp|].
    unfold powm in Hsq |- *.
    rewrite Z.pow_2_r in Hsq |- *.
    transitivity (((x * x) mod (p * q)) mod p).
    + symmetry. apply Z.mod_mod_divide. exists q. ring.
    + rewrite Hsq. apply Z.mod_1_l. lia.
  - apply powm_2_mod_prime_pm1; [exact Hq|].
    unfold powm in Hsq |- *.
    rewrite Z.pow_2_r in Hsq |- *.
    transitivity (((x * x) mod (p * q)) mod q).
    + symmetry. apply Z.mod_mod_divide. exists p. ring.
    + rewrite Hsq. apply Z.mod_1_l. lia.
Qed.

Theorem four_divides_lambda_iff_deep :
  forall p q,
    Z.prime p -> Z.prime q ->
    (4 | lambda_semiprime p q) <-> (2 <= Nat.max (val2 (p - 1)) (val2 (q - 1)))%nat.
Proof.
  intros p q Hp Hq.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  rewrite <- val2_lambda_semiprime by assumption.
  set (s := val2 (lambda_semiprime p q)).
  pose proof (lambda_semiprime_pos p q Hp Hq) as Hlam.
  pose proof (split2_of_reconstructs (lambda_semiprime p q) ltac:(lia)) as Hs.
  split.
  - intros [k Hk].
    destruct (Nat.le_gt_cases 2 s) as [Hle | Hlt]; [exact Hle|].
    assert (s = 0 \/ s = 1)%nat by lia.
    destruct H1 as [Hs0 | Hs1].
    + unfold s in Hs0. rewrite Hs0, Z.pow_0_r in Hs. rewrite Hs in Hk.
      (* λ = 1 * odd, 4 | odd ⇒ odd even, contradiction *)
      pose proof (odd_part_odd (lambda_semiprime p q) Hlam) as Ho.
      destruct Ho as [u Hu]. rewrite Hu in Hk. lia.
    + unfold s in Hs1. rewrite Hs1, Z.pow_1_r in Hs. rewrite Hs in Hk.
      pose proof (odd_part_odd (lambda_semiprime p q) Hlam) as Ho.
      destruct Ho as [u Hu]. rewrite Hu in Hk. lia.
  - intros Hge.
    rewrite Hs.
    unfold s in Hge.
    replace (Z.of_nat (val2 (lambda_semiprime p q)))
      with (2 + Z.of_nat (val2 (lambda_semiprime p q) - 2)) by lia.
    rewrite Z.pow_add_r by lia.
    change (2 ^ 2) with 4.
    exists (2 ^ Z.of_nat (val2 (lambda_semiprime p q) - 2)
              * odd_part (lambda_semiprime p q)). ring.
Qed.

Theorem no_order_4_when_lambda_val2_1 :
  forall p q a,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime a (p * q) ->
    val2 (lambda_semiprime p q) = 1%nat ->
    is_order (p * q) a 4 ->
    False.
Proof.
  intros p q a Hp Hq Hneq Hcop Hs Hord.
  pose proof (order_divides_lambda p q a 4 Hp Hq Hneq Hcop Hord) as Hdiv.
  assert (~ (4 | lambda_semiprime p q)).
  { rewrite four_divides_lambda_iff_deep by assumption.
    rewrite <- val2_lambda_semiprime, Hs by assumption. lia. }
  contradiction.
Qed.

Theorem blum_has_no_order_4 :
  forall p q a,
    Z.prime p -> Z.prime q -> p <> q ->
    Z.coprime a (p * q) ->
    kg_blum_2adic p q ->
    is_order (p * q) a 4 ->
    False.
Proof.
  intros p q a Hp Hq Hneq Hcop Hbl Hord.
  apply (no_order_4_when_lambda_val2_1 p q a); try assumption.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  destruct Hbl as [Hp1 Hq1].
  assert (0 < p - 1) by lia. assert (0 < q - 1) by lia.
  rewrite val2_lambda_semiprime, Hp1, Hq1 by assumption. reflexivity.
Qed.

(** Multiplying a square root by a mixed [√1] yields another square
    root, not associated through [±1] — Rabin's splitting handle. *)
Theorem sqrt1_pm_translates_square :
  forall p q y,
    Z.prime p -> Z.prime q -> p <> q ->
    let N := p * q in
    powm (y * sqrt1_pm p q) 2 N = powm y 2 N.
Proof.
  intros p q y Hp Hq Hneq N.
  pose proof (four_sqrt1 p q Hp Hq Hneq) as [_ [_ [Hpm _]]].
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  unfold N, powm. rewrite !Z.pow_2_r.
  replace ((y * sqrt1_pm p q) * (y * sqrt1_pm p q))
    with ((y * y) * (sqrt1_pm p q * sqrt1_pm p q)) by ring.
  rewrite Z.mul_mod by nia.
  unfold powm in Hpm. rewrite Z.pow_2_r in Hpm.
  rewrite Hpm, Z.mul_1_r, Z.mod_mod by nia.
  reflexivity.
Qed.
