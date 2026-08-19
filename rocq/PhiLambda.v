From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * [φ = λ · gcd] on a semiprime

    [φ(pq) = (p−1)(q−1)] and [λ(pq) = lcm(p−1, q−1)], so
    [φ = λ · gcd(p−1, q−1)].  Safe primes force the gcd to be [2]
    ([safe_pair_lambda]).

    Cross-confirmed by [cas/75_phi_lambda.gp]. *)

Theorem phi_eq_lambda_times_gcd :
  forall p q,
    2 <= p ->
    2 <= q ->
    phi_semiprime p q = lambda_semiprime p q * Z.gcd (p - 1) (q - 1).
Proof.
  intros p q Hp Hq.
  unfold phi_semiprime, lambda_semiprime.
  pose proof (lcm_gcd_prod (p - 1) (q - 1) ltac:(lia) ltac:(lia)) as H.
  lia.
Qed.

Theorem phi_div_lambda_is_gcd :
  forall p q,
    2 <= p ->
    2 <= q ->
    phi_semiprime p q / lambda_semiprime p q = Z.gcd (p - 1) (q - 1).
Proof.
  intros p q Hp Hq.
  rewrite phi_eq_lambda_times_gcd by lia.
  rewrite (Z.mul_comm (lambda_semiprime p q)).
  apply Z.div_mul.
  pose proof (lambda_semiprime_pos p q).
  (* lambda_semiprime_pos wants primes; positivity of lcm is enough *)
  unfold lambda_semiprime.
  pose proof (Z.lcm_nonneg (p - 1) (q - 1)).
  destruct (Z.eq_dec (Z.lcm (p - 1) (q - 1)) 0) as [Hz | Hnz]; [| lia].
  apply Z.lcm_eq_0 in Hz. lia.
Qed.
