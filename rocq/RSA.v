From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import Pin.

Open Scope Z_scope.

(** * RSA: instance, private exponent [d], and the RSA problem

    An RSA modulus is [N = p*q] for distinct primes.  The public exponent
    [e] is coprime to [λ(N)]; the private exponent [d] is its inverse
    modulo [λ(N)] (the [φ(N)] variant is recorded separately and not
    blurred).  Exponentiation by [d] is the [e]-th-root map on units of
    [(Z/NZ)*] — [d] itself is not "a cube root".

    Cross-confirmed by [cas/01_rsa_instance.gp] and [cas/02_annihilator.gp]. *)

Record RSAInstance : Type := {
  rsa_p : Z;
  rsa_q : Z;
  rsa_e : Z;
  rsa_d : Z;
  rsa_p_prime : Z.prime rsa_p;
  rsa_q_prime : Z.prime rsa_q;
  rsa_distinct : rsa_p <> rsa_q;
  rsa_e_coprime : Z.coprime rsa_e (lambda_semiprime rsa_p rsa_q);
  rsa_d_inv : (rsa_e * rsa_d) mod (lambda_semiprime rsa_p rsa_q) = 1;
  rsa_d_pos : 0 < rsa_d;
  rsa_e_pos : 1 < rsa_e
}.

Definition rsa_N (R : RSAInstance) : Z := rsa_p R * rsa_q R.
Definition rsa_phi (R : RSAInstance) : Z := phi_semiprime (rsa_p R) (rsa_q R).
Definition rsa_lambda (R : RSAInstance) : Z := lambda_semiprime (rsa_p R) (rsa_q R).

Lemma rsa_N_gt_1 : forall R, 1 < rsa_N R.
Proof.
  intros R. unfold rsa_N.
  pose proof (Z.prime_ge_2 _ (rsa_p_prime R)).
  pose proof (Z.prime_ge_2 _ (rsa_q_prime R)). nia.
Qed.

Lemma rsa_lambda_pos : forall R, 0 < rsa_lambda R.
Proof.
  intros R. unfold rsa_lambda.
  apply lambda_semiprime_pos; [apply rsa_p_prime | apply rsa_q_prime].
Qed.

Lemma rsa_lambda_gt_1 : forall R, 1 < rsa_lambda R.
Proof.
  intros R.
  pose proof (Z.prime_ge_2 _ (rsa_p_prime R)).
  pose proof (Z.prime_ge_2 _ (rsa_q_prime R)).
  pose proof (rsa_distinct R).
  unfold rsa_lambda, lambda_semiprime.
  assert (Hge : 2 <= Z.lcm (rsa_p R - 1) (rsa_q R - 1)).
  { destruct (Z.eq_dec (rsa_p R) 2) as [Hp2 | Hp2].
    - rewrite Hp2. change (2 - 1) with 1. rewrite Z.lcm_1_l_nonneg by lia. lia.
    - apply Z.le_trans with (rsa_p R - 1); [lia|].
      apply Z.divide_pos_le.
      + pose proof (lambda_semiprime_pos (rsa_p R) (rsa_q R)
                      (rsa_p_prime R) (rsa_q_prime R)).
        unfold lambda_semiprime in H2. lia.
      + apply Z.divide_lcm_l. }
  lia.
Qed.

Lemma rsa_phi_pos : forall R, 0 < rsa_phi R.
Proof.
  intros R. unfold rsa_phi.
  apply phi_semiprime_pos; [apply rsa_p_prime | apply rsa_q_prime].
Qed.

Lemma rsa_lambda_divides_phi : forall R, (rsa_lambda R | rsa_phi R).
Proof. intros R. unfold rsa_lambda, rsa_phi. apply lambda_divides_phi. Qed.

Lemma rsa_ed_minus_1_divides :
  forall R, (rsa_lambda R | rsa_e R * rsa_d R - 1).
Proof.
  intros R.
  pose proof (rsa_lambda_gt_1 R).
  apply mods_eq_iff_divides; [lia|].
  rewrite rsa_d_inv. symmetry. apply Z.mod_small; lia.
Qed.

Lemma rsa_ed_gt_1 : forall R, 1 < rsa_e R * rsa_d R.
Proof.
  intros R. pose proof (rsa_e_pos R). pose proof (rsa_d_pos R). nia.
Qed.

Definition rsa_enc (R : RSAInstance) (m : Z) : Z := powm m (rsa_e R) (rsa_N R).
Definition rsa_dec (R : RSAInstance) (c : Z) : Z := powm c (rsa_d R) (rsa_N R).

Definition rsa_problem (N e y x : Z) : Prop := powm x e N = y.

Definition rsa_inverter (N e : Z) : Type :=
  forall y, { x : Z | rsa_problem N e y x }.

Theorem rsa_dec_enc_units :
  forall R m,
    Z.coprime m (rsa_N R) ->
    rsa_dec R (rsa_enc R m) = m mod rsa_N R.
Proof.
  intros R m Hcop.
  unfold rsa_dec, rsa_enc, rsa_N in *.
  pose proof (rsa_N_gt_1 R).
  unfold rsa_N in *.
  pose proof (rsa_e_pos R). pose proof (rsa_d_pos R).
  rewrite <- powm_mul_r; [| lia | lia | lia].
  replace (rsa_e R * rsa_d R) with ((rsa_e R * rsa_d R - 1) + 1) by ring.
  rewrite powm_add_r; [| lia | lia | lia].
  rewrite powm_1_r by lia.
  rewrite (annihilates_units (rsa_p R) (rsa_q R) m (rsa_e R * rsa_d R - 1)).
  - rewrite Z.mul_1_l, Z.mod_mod by lia. reflexivity.
  - apply rsa_p_prime.
  - apply rsa_q_prime.
  - apply rsa_distinct.
  - exact Hcop.
  - pose proof (rsa_ed_gt_1 R). lia.
  - apply rsa_ed_minus_1_divides.
Qed.

Theorem rsa_enc_dec_units :
  forall R c,
    Z.coprime c (rsa_N R) ->
    rsa_enc R (rsa_dec R c) = c mod rsa_N R.
Proof.
  intros R c Hcop.
  unfold rsa_dec, rsa_enc, rsa_N in *.
  pose proof (rsa_N_gt_1 R).
  unfold rsa_N in *.
  pose proof (rsa_e_pos R). pose proof (rsa_d_pos R).
  rewrite <- powm_mul_r; [| lia | lia | lia].
  rewrite (Z.mul_comm (rsa_d R) (rsa_e R)).
  replace (rsa_e R * rsa_d R) with ((rsa_e R * rsa_d R - 1) + 1) by ring.
  rewrite powm_add_r; [| lia | lia | lia].
  rewrite powm_1_r by lia.
  rewrite (annihilates_units (rsa_p R) (rsa_q R) c (rsa_e R * rsa_d R - 1)).
  - rewrite Z.mul_1_l, Z.mod_mod by lia. reflexivity.
  - apply rsa_p_prime.
  - apply rsa_q_prime.
  - apply rsa_distinct.
  - exact Hcop.
  - pose proof (rsa_ed_gt_1 R). lia.
  - apply rsa_ed_minus_1_divides.
Qed.

Definition is_cube_root (N c m : Z) : Prop := powm m 3 N = c.

Lemma rsa_d_is_cube_root_map :
  forall R c,
    rsa_e R = 3 ->
    is_cube_root (rsa_N R) (rsa_enc R (rsa_dec R c)) (rsa_dec R c).
Proof.
  intros R c He. unfold is_cube_root, rsa_enc. rewrite He. reflexivity.
Qed.

(** Textbook instance: numbers from [Pin.v] ([pin_p], [pin_q],
    [pin_e], [pin_d]). *)

Lemma prime_11 : Z.prime 11.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/
          n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10) by lia.
  intuition subst; reflexivity.
Qed.

Lemma prime_17 : Z.prime 17.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/
          n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
          n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16) by lia.
  intuition subst; reflexivity.
Qed.

Lemma rsa_test_lambda : lambda_semiprime pin_p pin_q = pin_lam.
Proof. vm_compute. reflexivity. Qed.

Lemma rsa_test_phi : phi_semiprime pin_p pin_q = pin_phi.
Proof. vm_compute. reflexivity. Qed.

Lemma rsa_test_inv : (pin_e * pin_d) mod pin_lam = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma rsa_test_coprime_e : Z.coprime pin_e pin_lam.
Proof. unfold Z.coprime. vm_compute. reflexivity. Qed.

Definition rsa_test : RSAInstance.
Proof.
  refine {|
    rsa_p := pin_p; rsa_q := pin_q; rsa_e := pin_e; rsa_d := pin_d;
    rsa_p_prime := prime_11; rsa_q_prime := prime_17;
    rsa_distinct := ltac:(discriminate);
    rsa_e_coprime := ltac:(rewrite rsa_test_lambda; exact rsa_test_coprime_e);
    rsa_d_inv := ltac:(rewrite rsa_test_lambda; exact rsa_test_inv);
    rsa_d_pos := ltac:(unfold pin_d; lia); rsa_e_pos := ltac:(unfold pin_e; lia)
  |}.
Defined.

Theorem rsa_test_N : rsa_N rsa_test = pin_N.
Proof. reflexivity. Qed.

Theorem rsa_test_vector :
  rsa_enc rsa_test pin_x = pin_y /\ rsa_dec rsa_test pin_y = pin_x.
Proof. vm_compute. split; reflexivity. Qed.

Theorem rsa_test_roundtrip :
  rsa_dec rsa_test (rsa_enc rsa_test pin_x) = pin_x.
Proof. vm_compute. reflexivity. Qed.

Theorem rsa_test_annihilator :
  forall a, Z.coprime a pin_N -> powm a pin_lam pin_N = 1.
Proof.
  intros a Hcop.
  rewrite <- rsa_test_lambda.
  apply carmichael_semiprime; [exact prime_11 | exact prime_17 | discriminate | exact Hcop].
Qed.

(** ** Why a polynomial in [N] cannot be a handle

    [N = (p-1)q + q], so [N ≡ q (mod p−1)].  Any polynomial [f]
    therefore satisfies [f(N) ≡ f(q) (mod p−1)], and
    [gcd(f(N), p−1) = gcd(f(q), p−1)].  For independent primes that
    gcd is chance-sized.  See [cas/45_identity_sweep.gp]. *)

Theorem N_cong_q_mod_pminus1 :
  forall p q, p <> 1 -> (p * q) mod (p - 1) = q mod (p - 1).
Proof.
  intros p q Hp.
  replace (p * q) with ((p - 1) * q + q) by lia.
  rewrite Z.add_mod, Z.mul_mod, Z.mod_same by lia.
  rewrite Z.mul_0_l, Z.mod_0_l by lia.
  rewrite Z.add_0_l, Z.mod_mod by lia.
  reflexivity.
Qed.

Theorem gcd_polyN_pminus1_is_gcd_at_q :
  forall p fN fq,
    p <> 1 ->
    fN mod (p - 1) = fq mod (p - 1) ->
    Z.gcd fN (p - 1) = Z.gcd fq (p - 1).
Proof.
  intros p fN fq Hp Hcong.
  rewrite (Z.gcd_comm fN (p - 1)), (Z.gcd_comm fq (p - 1)).
  rewrite <- (Z.gcd_mod fN (p - 1)), <- (Z.gcd_mod fq (p - 1)) by lia.
  rewrite Hcong. reflexivity.
Qed.
