From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import StrongPrimes.
Require Import Cyclotomic.

Open Scope Z_scope.

(** * Lucas [V] and the Williams [p+1] period

    Pollard [p−1] is exponentiation in [F_p]* (order [p−1]).
    Williams [p+1] is the same idea in the order-[p+1] torus of
    [F_{p²}]*, evaluated with a Lucas sequence so the arithmetic
    stays in [Z/NZ].  That is Type B at [n = 2]: the period is
    [Φ₂(p) = p+1], already named [cyc2] / [pp1_resistant].

    This file gives the [V] recurrence and computed doubling
    identities the CAS engine uses.  The closed addition formula
    [V_{m+n} = V_m V_n − Q^n V_{|m−n|}] is a design target, not
    a theorem.  Cross-confirmed by [cas/22_lucas.gp]. *)

Fixpoint lucasV (P Q : Z) (n : nat) : Z :=
  match n with
  | O => 2
  | S O => P
  | S (S n' as n1) => P * lucasV P Q n1 - Q * lucasV P Q n'
  end.

Lemma lucasV_0 : forall P Q, lucasV P Q 0 = 2.
Proof. reflexivity. Qed.

Lemma lucasV_1 : forall P Q, lucasV P Q 1 = P.
Proof. reflexivity. Qed.

Lemma lucasV_rec :
  forall P Q n,
    lucasV P Q (S (S n)) = P * lucasV P Q (S n) - Q * lucasV P Q n.
Proof. intros. reflexivity. Qed.

Lemma lucasV_2 :
  forall P Q, lucasV P Q 2%nat = P * P - Q * 2.
Proof. intros. reflexivity. Qed.

(** Doubling at [Q = 1]: [V_{2n} = V_n² − 2], checked on the
    first several [n].  The general identity is the addition
    formula at [m = n], not proved. *)
Theorem lucasV_double_Q1_table :
  (forall P, lucasV P 1 0%nat = lucasV P 1 0%nat * lucasV P 1 0%nat - 2) /\
  (forall P, lucasV P 1 2%nat = lucasV P 1 1%nat * lucasV P 1 1%nat - 2) /\
  (forall P, lucasV P 1 4%nat = lucasV P 1 2%nat * lucasV P 1 2%nat - 2) /\
  (forall P, lucasV P 1 6%nat = lucasV P 1 3%nat * lucasV P 1 3%nat - 2).
Proof.
  repeat split; intros P; unfold lucasV; ring.
Qed.

(** The Williams handle is exactly the [n=2] cyclotomic handle. *)
Theorem williams_handle_is_cyc2 :
  forall p M, cyc_handle (cyc2 p) M <-> 0 <= M /\ (p + 1 | M).
Proof. intros. apply cyc2_handle_is_williams. Qed.

Theorem safe_prime_refuses_pminus1_only :
  forall p B,
    safe_prime p ->
    (p - 1) / 2 > B ->
    p1_resistant p B.
Proof. intros. apply safe_prime_resists_p1; assumption. Qed.

(** A safe prime need not refuse [p+1].  [p = 2r+1] makes
    [p+1 = 2(r+1)], and [r+1] may be smooth.  That is why
    "strong" asks for a large prime factor of [p+1] as well. *)
Definition lucas_period (p : Z) : Z := p + 1.

Theorem lucas_period_is_cyc2 :
  forall p, lucas_period p = cyc2 p.
Proof. reflexivity. Qed.
