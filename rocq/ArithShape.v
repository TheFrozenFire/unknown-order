From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Hardness.
Require Import StrongRSAPeel.
Require Import ExtraRelations.
Require Import StrongPrimes.
Require Import MultiPrime.
Require Import Takagi.

Open Scope Z_scope.

(** * Twelve arith, peel-gap, and modulus-shape inroads

    Newton / Euclidean arithmetic of [y], a missing [x=y]
    period-of-[y] peel, Takagi and triprime tapes, and a public
    base that cannot represent the residual [y].  None inhabits
    [srsa_residual_leaf] as [Problem_Factor].  Cross-confirmed
    by [cas/132]. *)

(** ** 1. Newton iteration in [(Z/NZ)] *)

Theorem arith_newton_inv3 :
  (3 * 125) mod 187 = 1.
Proof. reflexivity. Qed.

Theorem arith_newton_from_one :
  ((2 * 1 + 36 * 1) * 125) mod 187 = 75 /\
  powm 75 3 187 = 3 /\
  3 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

(** ** 2. [e | (y−1)] *)

Theorem arith_e5_divides_yminus1 :
  (5 | 35) /\ Z.gcd 5 80 = 5.
Proof. split; [exists 7; reflexivity | reflexivity]. Qed.

Theorem arith_e7_divides_yminus1 :
  (7 | 35) /\ Z.gcd 7 80 = 1.
Proof. split; [exists 5; reflexivity | reflexivity]. Qed.

Theorem arith_e7_residual :
  srsa_residual_leaf 187 80 36 60 7.
Proof.
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 3; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

(** ** 3. [x=y] with [e = ord(y)+1] (missing peel leaf) *)

Theorem arith_xy_period_residual :
  srsa_residual_leaf 187 80 36 36 41.
Proof.
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 20; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem arith_xy_period_no_split :
  powm 36 40 187 = 1 /\
  Z.gcd (powm 36 40 187 - 1) 187 = 187 /\
  ~ Problem_Factor 187 187.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  unfold Problem_Factor. intros [H _]. lia.
Qed.

(** ** 4. Fermat-on-the-witness [gcd(x−y, N)] *)

Theorem arith_witness_gap_no_split :
  Z.gcd (42 - 36) 187 = 1.
Proof. reflexivity. Qed.

(** ** 5. Takagi [N=p²q], Hensel tape *)

Theorem arith_takagi_shape :
  takagi_N 3 5 = 45 /\
  lambda_p2 3 = 6 /\
  lambda_takagi 3 5 = 12.
Proof. split; [reflexivity|]. split; [reflexivity | vm_compute; reflexivity]. Qed.

Theorem arith_takagi_euler_p2 :
  powm 2 6 9 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem arith_takagi_p_on_tape :
  Problem_Factor 45 3.
Proof. unfold Problem_Factor. split; [lia|]. exists 15. reflexivity. Qed.

(** ** 6. Public scaling [x = 2y] *)

Theorem arith_double_y_not_root :
  powm 72 3 187 = 183 /\
  183 <> 36.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

(** ** 7. [e = nextprime(y)] *)

Lemma prime_37 : Z.prime 37.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/
          n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
          n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/
          n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/
          n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/
          n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/
          n = 31 \/ n = 32 \/ n = 33 \/ n = 34 \/ n = 35 \/
          n = 36) by lia.
  intuition subst; reflexivity.
Qed.

Theorem arith_nextprime_e37 :
  36 < 37 /\ Z.gcd 37 80 = 1 /\ (37 * 13) mod 80 = 1.
Proof. split; [lia|]. split; [reflexivity | reflexivity]. Qed.

Theorem arith_nextprime_residual :
  srsa_residual_leaf 187 80 36 (powm 36 13 187) 37.
Proof.
  unfold srsa_residual_leaf, Problem_StrongRSA.
  split; [vm_compute; reflexivity|].
  split; [split; [lia|]; vm_compute; reflexivity|].
  split; [exists 18; lia|].
  split; [vm_compute; reflexivity|].
  intros [k Hk]. nia.
Qed.

Theorem arith_nextprime_root_is_49 :
  powm 36 13 187 = 49 /\
  powm 49 37 187 = 36.
Proof. vm_compute. split; reflexivity. Qed.

(** ** 8. Continued fraction of [y/N] *)

Theorem arith_cf_euclidean :
  187 = 5 * 36 + 7 /\
  36 = 5 * 7 + 1 /\
  7 = 7 * 1 + 0.
Proof. split; [reflexivity|]. split; reflexivity. Qed.

Theorem arith_cf_convergents_not_root :
  powm 5 3 187 <> 36 /\
  powm 26 3 187 = 185 /\
  185 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.

(** ** 9. Same [x], two coprime moduli *)

Theorem arith_two_moduli_coprime :
  Z.gcd 187 247 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem arith_two_moduli_same_x :
  powm 42 3 187 = 36 /\
  powm 42 3 247 = 235.
Proof. vm_compute. split; reflexivity. Qed.

(** ** 10. Multiprime [N=pqr], mixed [√1] *)

Lemma three_prime_357 : three_prime 3 5 7.
Proof.
  unfold three_prime.
  repeat split;
    [apply prime_3 | apply prime_5 | apply prime_7 | lia | lia | lia].
Qed.

Theorem arith_mixed_pqr_is_factor :
  let g := Z.gcd (mixed_pqr 3 5 7 - 1) (3 * 5 * 7) in
  Problem_Factor (3 * 5 * 7) g.
Proof.
  pose proof (mixed_pqr_splits 3 5 7 three_prime_357 ltac:(lia)) as H.
  unfold Problem_Factor.
  destruct H as [_ [Hlt [Hgt Hdiv]]].
  split; [lia | exact Hdiv].
Qed.

(** ** 11. Factored composite [e = 15] *)

Theorem arith_composite_e15_shares_lambda :
  15 = 3 * 5 /\
  Z.gcd 15 80 = 5 /\
  Z.gcd 15 80 <> 1.
Proof. split; [reflexivity|]. split; [reflexivity | discriminate]. Qed.

(** ** 12. DL of [y] in public base [2] *)

Fixpoint arith_pow2_hits (fuel : nat) (y : Z) : bool :=
  match fuel with
  | O => powm 2 0 187 =? y
  | S n =>
      if powm 2 (Z.of_nat (S n)) 187 =? y then true
      else arith_pow2_hits n y
  end.

Theorem arith_36_not_in_ltwo :
  arith_pow2_hits 40%nat 36 = false.
Proof. vm_compute. reflexivity. Qed.

Theorem arith_two_and_thirtysix_same_order_period :
  powm 2 40 187 = 1 /\
  powm 36 40 187 = 1 /\
  powm 2 1 187 <> 36.
Proof. vm_compute. repeat split; discriminate. Qed.
