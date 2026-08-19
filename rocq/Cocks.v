From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.QuadRecip.
Require Import QuadResidue.
Require Import RabinWilliams.
Require Import QRModN.

Open Scope Z_scope.

(** * Cocks 2001 IBE — algebra only

    The carefully chosen element is an [a] with Jacobi [(a/N) = +1]
    on a Blum pair.  Then exactly one of [{a, −a}] is a global
    square ([blum_jacobi_one_exactly_one_pm]).  The encryptor who
    cannot tell which sends a ciphertext for both.  The PKG who
    can factor extracts the square root of the one that is.

    Decrypt identity: if [s² ≡ a] and [c = t + a t⁻¹], then
    [(c + 2s) t ≡ (t + s)²], so Jacobi[(c+2s)/N] = Jacobi[(t/N)]
    on units.

    Hash-to-[a] is [cocks_hash_named]; IND-ID-CPA is
    [cocks_ind_id_cpa_named].

    Cross-confirmed by [cas/84_cocks.gp]. *)

Definition cocks_hash_named : Prop :=
  forall (id : Z), False.

Definition cocks_ind_id_cpa_named : Prop :=
  forall (N a : Z), False.

Definition cocks_ciphertext (N a t tinv : Z) : Z :=
  (t + a * tinv) mod N.

Theorem cocks_carefully_chosen :
  forall a p q,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p mod 4 = 3 ->
    q mod 4 = 3 ->
    Z.coprime a p ->
    Z.coprime a q ->
    jacobi_N a p q = 1 ->
    (is_qr_N a (p * q) /\ ~ is_qr_N (- a) (p * q)) \/
    (is_qr_N (- a) (p * q) /\ ~ is_qr_N a (p * q)).
Proof. apply blum_jacobi_one_exactly_one_pm. Qed.

Lemma cocks_ct_times_t :
  forall N a t tinv s,
    1 < N ->
    (t * tinv) mod N = 1 ->
    (s * s) mod N = a mod N ->
    ((cocks_ciphertext N a t tinv + 2 * s) * t) mod N =
      ((t + s) * (t + s)) mod N.
Proof.
  intros N a t tinv s Hn Hinv Hsq.
  unfold cocks_ciphertext.
  rewrite <- (Z.mul_mod_idemp_l ((t + a * tinv) mod N + 2 * s) t N) by lia.
  rewrite Z.add_mod_idemp_l by lia.
  rewrite Z.mul_mod_idemp_l by lia.
  rewrite Z.mul_add_distr_r.
  rewrite Z.mul_add_distr_r.
  replace (a * tinv * t) with (a * (t * tinv)) by ring.
  rewrite <- (Z.add_mod_idemp_l (t * t + a * (t * tinv)) (2 * s * t) N) by lia.
  rewrite <- (Z.add_mod_idemp_r (t * t) (a * (t * tinv)) N) by lia.
  rewrite <- (Z.mul_mod_idemp_r a (t * tinv) N) by lia.
  rewrite Hinv, Z.mul_1_r.
  rewrite Z.add_mod_idemp_r by lia.
  rewrite Z.add_mod_idemp_l by lia.
  rewrite (Z.add_comm (t * t) a).
  replace (a + t * t + 2 * s * t) with (a + (t * t + 2 * s * t)) by ring.
  rewrite <- (Z.add_mod_idemp_l a (t * t + 2 * s * t) N) by lia.
  rewrite <- Hsq.
  rewrite Z.add_mod_idemp_l by lia.
  replace (s * s + (t * t + 2 * s * t)) with ((t + s) * (t + s)) by ring.
  reflexivity.
Qed.

Lemma euler_sign_cong_mod :
  forall x y p,
    Z.prime p ->
    p <> 2 ->
    x mod p = y mod p ->
    euler_sign x p = euler_sign y p.
Proof.
  intros x y p Hp Hne Heq.
  unfold euler_sign, QuadRecip.euler_crit, powm.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (half_pm1_nonneg p Hp Hne).
  rewrite <- (Z.mod_pow_l x ((p - 1) / 2) p) by lia.
  rewrite <- (Z.mod_pow_l y ((p - 1) / 2) p) by lia.
  rewrite Heq. reflexivity.
Qed.

Lemma jacobi_cong :
  forall x y p q,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    0 < p ->
    0 < q ->
    x mod (p * q) = y mod (p * q) ->
    jacobi_N x p q = jacobi_N y p q.
Proof.
  intros x y p q Hp Hq Hp2 Hq2 Hpp Hqq Heq.
  unfold jacobi_N.
  f_equal.
  - apply euler_sign_cong_mod; try assumption.
    rewrite <- (mod_pq_to_p x p q Hpp Hqq).
    rewrite <- (mod_pq_to_p y p q Hpp Hqq).
    rewrite Heq. reflexivity.
  - apply euler_sign_cong_mod; try assumption.
    rewrite <- (mod_pq_to_p x q p Hqq Hpp).
    rewrite <- (mod_pq_to_p y q p Hqq Hpp).
    rewrite (Z.mul_comm q p), Heq, (Z.mul_comm p q). reflexivity.
Qed.

Lemma jacobi_mul :
  forall a b p q,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    Z.coprime a p ->
    Z.coprime a q ->
    Z.coprime b p ->
    Z.coprime b q ->
    jacobi_N (a * b) p q = jacobi_N a p q * jacobi_N b p q.
Proof.
  intros a b p q Hp Hq Hp2 Hq2 Hap Haq Hbp Hbq.
  unfold jacobi_N.
  rewrite (euler_sign_mul a b p Hp Hp2 Hap Hbp).
  rewrite (euler_sign_mul a b q Hq Hq2 Haq Hbq).
  ring.
Qed.

Lemma jacobi_sq_one :
  forall x p q,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    p <> q ->
    Z.coprime x p ->
    Z.coprime x q ->
    jacobi_N (x * x) p q = 1.
Proof.
  intros x p q Hp Hq Hp2 Hq2 Hneq Hxp Hxq.
  apply jacobi_of_qr_N; try assumption.
  - rewrite coprime_comm. apply coprime_mul_iff.
    split; rewrite coprime_comm; assumption.
  - rewrite coprime_comm. apply coprime_mul_iff.
    split; rewrite coprime_comm; assumption.
  - exists x. reflexivity.
Qed.

Lemma jacobi_self_sq :
  forall a p q,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    Z.coprime a p ->
    Z.coprime a q ->
    jacobi_N a p q * jacobi_N a p q = 1.
Proof.
  intros a p q Hp Hq Hp2 Hq2 Hap Haq.
  unfold jacobi_N.
  pose proof (euler_sign_of_pm1 a p Hp Hp2 Hap) as Hsp.
  pose proof (euler_sign_of_pm1 a q Hq Hq2 Haq) as Hsq.
  destruct Hsp as [Hsp|Hsp]; destruct Hsq as [Hsq|Hsq]; rewrite Hsp, Hsq; reflexivity.
Qed.

Theorem cocks_decrypt_jacobi :
  forall p q a t tinv s,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p <> 2 ->
    q <> 2 ->
    Z.coprime t p ->
    Z.coprime t q ->
    Z.coprime (t + s) p ->
    Z.coprime (t + s) q ->
    Z.coprime (cocks_ciphertext (p * q) a t tinv + 2 * s) p ->
    Z.coprime (cocks_ciphertext (p * q) a t tinv + 2 * s) q ->
    (t * tinv) mod (p * q) = 1 ->
    (s * s) mod (p * q) = a mod (p * q) ->
    jacobi_N (cocks_ciphertext (p * q) a t tinv + 2 * s) p q =
      jacobi_N t p q.
Proof.
  intros p q a t tinv s Hp Hq Hneq Hp2 Hq2 Htp Htq Hsp Hsq Hcp Hcq Hinv Hroot.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  pose proof (cocks_ct_times_t (p * q) a t tinv s ltac:(nia) Hinv Hroot) as Hprod.
  set (c2 := cocks_ciphertext (p * q) a t tinv + 2 * s).
  change (cocks_ciphertext (p * q) a t tinv + 2 * s) with c2 in Hprod, Hcp, Hcq.
  assert (jacobi_N (c2 * t) p q = jacobi_N ((t + s) * (t + s)) p q) as Hjcong.
  { apply jacobi_cong; try assumption; try lia. }
  rewrite (jacobi_mul c2 t p q Hp Hq Hp2 Hq2 Hcp Hcq Htp Htq) in Hjcong.
  rewrite (jacobi_sq_one (t + s) p q Hp Hq Hp2 Hq2 Hneq Hsp Hsq) in Hjcong.
  pose proof (jacobi_self_sq t p q Hp Hq Hp2 Hq2 Htp Htq) as Ht2.
  destruct (euler_sign_of_pm1 t p Hp Hp2 Htp) as [E1|E1];
  destruct (euler_sign_of_pm1 t q Hq Hq2 Htq) as [E2|E2];
    unfold jacobi_N in Hjcong, Ht2 |- *; rewrite E1, E2 in Hjcong, Ht2 |- *;
    lia.
Qed.
