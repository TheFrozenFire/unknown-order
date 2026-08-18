From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import BinForms.

Open Scope Z_scope.

(** * Directed sixth-type leftovers (Methods 3–8)

    Cheap public objects built from [N] that are not polynomials
    and not the Euler quotient.  Each method's CAS lives under
    [cas/46]–[cas/51].  See [notes/sixth-type-plan.md]. *)

(** ** Method 3: [(N, 0, 1)] of disc [−4N] is the principal class *)

Definition form_N01 (N : Z) : bqf :=
  {| bqf_a := N; bqf_b := 0; bqf_c := 1 |}.

Theorem form_N01_disc :
  forall N, bqf_disc (form_N01 N) = -4 * N.
Proof.
  intros N. unfold bqf_disc, form_N01. cbn [bqf_a bqf_b bqf_c]. ring.
Qed.

Lemma minus4N_mod4 :
  forall N, (-4 * N) mod 4 = 0.
Proof.
  intros N. replace (-4 * N) with ((-N) * 4) by ring. apply Z.mod_mul; lia.
Qed.

Lemma minus4N_div4 :
  forall N, - (-4 * N / 4) = N.
Proof.
  intros N.
  pose proof (Z.div_mod (-4 * N) 4 ltac:(lia)) as H.
  rewrite (minus4N_mod4 N), Z.add_0_r in H.
  nia.
Qed.

Theorem form_N01_equiv_principal :
  forall N,
    bqf_equiv (form_N01 N) (bqf_id (-4 * N)).
Proof.
  intros N.
  exists sl2_S. split; [apply sl2_S_ok|].
  unfold form_N01, bqf_act, sl2_S.
  cbn [sl2_a sl2_b sl2_c sl2_d bqf_a bqf_b bqf_c].
  unfold bqf_id.
  rewrite (minus4N_mod4 N).
  replace ((0 =? 0)) with true by reflexivity.
  cbn [andb].
  replace (N * 0 * 0 + 0 * 0 * 1 + 1 * 1 * 1) with 1 by ring.
  replace (2 * N * 0 * -1 + 0 * (0 * 0 + -1 * 1) + 2 * 1 * 1 * 0) with 0 by ring.
  replace (N * -1 * -1 + 0 * -1 * 0 + 1 * 0 * 0) with N by ring.
  rewrite minus4N_div4. reflexivity.
Qed.

(** Public factorization of [N²−4]; genus theory on that
    discriminant sees only [N±2], not [p]. *)

Theorem Nsq_minus_4_factors :
  forall N, N * N - 4 = (N - 2) * (N + 2).
Proof. intros N. ring. Qed.

Theorem gcd_N_minus_2_N :
  forall N, N <> 0 -> Z.gcd (N - 2) N = Z.gcd (-2) N.
Proof.
  intros N HN.
  rewrite (Z.gcd_comm (N - 2) N), (Z.gcd_comm (-2) N).
  rewrite <- (Z.gcd_mod (N - 2) N), <- (Z.gcd_mod (-2) N) by lia.
  replace (N - 2) with (N + (-2)) by lia.
  rewrite Z.add_mod, Z.mod_same, Z.add_0_l, Z.mod_mod by lia.
  reflexivity.
Qed.

Theorem odd_N_gcd_Nminus2 :
  forall N, N mod 2 = 1 -> Z.gcd (N - 2) N = 1.
Proof.
  intros N Hodd.
  assert (HN : N <> 0) by (intro Hz; rewrite Hz in Hodd; discriminate).
  rewrite (Z.gcd_comm (N - 2) N).
  rewrite <- (Z.gcd_mod (N - 2) N) by lia.
  replace ((N - 2) mod N) with ((-2) mod N).
  2:{ replace (N - 2) with (N + -2) by lia.
      rewrite Z.add_mod, Z.mod_same, Z.add_0_l, Z.mod_mod by lia. reflexivity. }
  rewrite (Z.gcd_mod (-2) N) by lia.
  rewrite Z.gcd_comm.
  change (-2) with (- (2)).
  rewrite Z.gcd_opp_l.
  rewrite <- (Z.gcd_mod N 2) by lia.
  rewrite Hodd. reflexivity.
Qed.

(** ** Method 11: every factorization [4N = αβ] gives
    [(α+β)² − 16N = (α−β)²], i.e. a point on [s² − 4N = □]
    after [s = (α+β)/2].  In [ℤ_ℓ^×] there are many units [α]. *)

Theorem factor_4N_gives_square_disc :
  forall N a b,
    a * b = 4 * N ->
    (a + b) * (a + b) - 16 * N = (a - b) * (a - b).
Proof.
  intros N a b Hfac.
  replace (16 * N) with (4 * (a * b)) by lia.
  ring.
Qed.

(** ** Polynomial characters collapse: [D(N) ≡ D(0) (mod p)]

    Same obstruction as Method 1, in Jacobi language.
    [(N+1 / p) = (1 / p) = 1] whenever [p | N]. *)

Theorem N_plus_one_powm :
  forall p N k,
    Z.prime p -> 0 <= k -> (p | N) ->
    powm (N + 1) k p = 1 mod p.
Proof.
  intros p N k Hp Hk Hd.
  pose proof (Z.prime_ge_2 p Hp).
  rewrite <- powm_mod_base by lia.
  replace ((N + 1) mod p) with 1.
  - apply powm_1_pow; lia.
  - rewrite Z.add_mod, (proj2 (Z.mod_divide N p ltac:(lia)) Hd),
      Z.add_0_l, Z.mod_mod, Z.mod_small by lia.
    reflexivity.
Qed.

Theorem N_plus_one_euler_is_one :
  forall p N,
    Z.prime p -> 2 < p -> (p | N) ->
    powm (N + 1) ((p - 1) / 2) p = 1.
Proof.
  intros p N Hp Hp2 Hd.
  pose proof (Z.prime_ge_2 p Hp).
  assert (Hk : 0 <= (p - 1) / 2) by (apply Z.div_pos; lia).
  rewrite (N_plus_one_powm p N ((p - 1) / 2) Hp Hk Hd).
  apply Z.mod_small; lia.
Qed.

(** ** [Δ=−4N]: non-principal [Cl[2]] *is* the factorization

    [(p, 0, q)] has disc [−4pq], is ambiguous, and is reduced
    once [p ≤ q].  Writing it down requires [p].  The public
    form [(N, 0, 1)] is principal ([form_N01_equiv_principal]). *)

Definition form_p0q (p q : Z) : bqf :=
  {| bqf_a := p; bqf_b := 0; bqf_c := q |}.

Theorem form_p0q_disc :
  forall p q, bqf_disc (form_p0q p q) = -4 * p * q.
Proof.
  intros p q. unfold bqf_disc, form_p0q. cbn [bqf_a bqf_b bqf_c]. ring.
Qed.

Theorem form_p0q_ambiguous :
  forall p q, bqf_ambiguous (form_p0q p q).
Proof. intros p q. unfold bqf_ambiguous, form_p0q. cbn. now left. Qed.

Theorem form_p0q_reduced_when_ordered :
  forall p q,
    0 < p -> p <= q ->
    bqf_reduced (form_p0q p q).
Proof.
  intros p q Hp Hle.
  unfold bqf_reduced, form_p0q. cbn.
  split; [lia | intros Hneg; lia].
Qed.

(** Field of [fund(−4N)] (maximal order).  Gauss 2-rank is [t−1]
    on the *fundamental* disc: [N ≡ 1 (mod 4)] ⇒ [Δ₀ = −4N]
    (primes [2,p,q], rank 2); [N ≡ 3 (mod 4)] ⇒ [Δ₀ = −N]
    (primes [p,q], rank 1).  Williams ([p,q ≡ 3 (mod 4)]) and
    both [≡ 1] live in the same public bucket [N ≡ 1 (mod 4)].
    The form class group of the *non-fundamental* order of disc
    [−4N] still has 2-rank from [ω(−4N)], which needs [p,q]. *)

Definition fund_disc_minusN (N : Z) : Z :=
  if N mod 4 =? 3 then - N else -4 * N.

Theorem williams_N_mod4 :
  forall p q,
    p mod 4 = 3 -> q mod 4 = 3 -> (p * q) mod 4 = 1.
Proof.
  intros p q Hp Hq.
  rewrite Z.mul_mod, Hp, Hq by lia. reflexivity.
Qed.

Theorem both_1_mod4_N_mod4 :
  forall p q,
    p mod 4 = 1 -> q mod 4 = 1 -> (p * q) mod 4 = 1.
Proof.
  intros p q Hp Hq.
  rewrite Z.mul_mod, Hp, Hq by lia. reflexivity.
Qed.

Theorem mixed_mod4_N_mod4 :
  forall p q,
    p mod 4 = 1 -> q mod 4 = 3 -> (p * q) mod 4 = 3.
Proof.
  intros p q Hp Hq.
  rewrite Z.mul_mod, Hp, Hq by lia. reflexivity.
Qed.
