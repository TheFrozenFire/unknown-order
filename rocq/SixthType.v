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
