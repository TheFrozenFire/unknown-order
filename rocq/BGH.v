From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Require Import RocqProofs.NumberTheory.
Require Import QuadResidue.
Require Import QRModN.
Require Import Cocks.
Require Import PowersOfTau.

Open Scope Z_scope.

(** * Cocks / Boneh–Gentry–Hamburg — 1-bit pairing catalog

    Jacobi [(·/N) : (Z/NZ)* → {±1}] is bilinear and lands in a
    group of order dividing 2.  Additive form:
    [jacobi(g^a) · jacobi(g^b) = jacobi(g^{a+b})].  Multiplicative
    form is [jacobi_mul].  On a Blum pair [(-1/N) = +1], so the
    encryptor who cannot tell which of [{a, −a}] is a global
    square sends a Cocks ciphertext for both.

    These are 1-bit pairings.  They do not check a sampled-[τ]
    string ([jacobi_sees_only_parity]).  Hash-to-identity and
    IND-ID-CPA stay at [cocks_hash_named] / [cocks_ind_id_cpa_named].

    Cross-confirmed by [cas/93_bgh.gp]. *)

Theorem jacobi_additive_pairing :
  forall g a b p q,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    p <> q ->
    Z.coprime g p ->
    Z.coprime g q ->
    0 <= a ->
    0 <= b ->
    jacobi_N (powm g a (p * q)) p q *
      jacobi_N (powm g b (p * q)) p q =
      jacobi_N (powm g (a + b) (p * q)) p q.
Proof.
  intros g a b p q Hp Hq Hp2 Hq2 Hneq Hgp Hgq Ha Hb.
  rewrite (jacobi_sees_only_parity g a p q Hp Hq Hp2 Hq2 Hneq Hgp Hgq Ha).
  rewrite (jacobi_sees_only_parity g b p q Hp Hq Hp2 Hq2 Hneq Hgp Hgq Hb).
  rewrite (jacobi_sees_only_parity g (a + b) p q
             Hp Hq Hp2 Hq2 Hneq Hgp Hgq ltac:(lia)).
  pose proof (Z.even_add a b) as Hadd.
  destruct (Z.even a) eqn:Ea; destruct (Z.even b) eqn:Eb;
    simpl in Hadd; rewrite Hadd.
  - reflexivity.
  - rewrite Z.mul_1_l. reflexivity.
  - rewrite Z.mul_1_r. reflexivity.
  - apply jacobi_self_sq; assumption.
Qed.

Theorem jacobi_neg1_on_blum :
  forall p q,
    Z.prime p ->
    Z.prime q ->
    p mod 4 = 3 ->
    q mod 4 = 3 ->
    jacobi_N (-1) p q = 1.
Proof.
  intros p q Hp Hq Hpm Hqm.
  unfold jacobi_N.
  rewrite (euler_sign_neg1_blum p Hp Hpm).
  rewrite (euler_sign_neg1_blum q Hq Hqm).
  reflexivity.
Qed.

Theorem jacobi_one_mul_closed :
  forall a b p q,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    Z.coprime a p ->
    Z.coprime a q ->
    Z.coprime b p ->
    Z.coprime b q ->
    jacobi_N a p q = 1 ->
    jacobi_N b p q = 1 ->
    jacobi_N (a * b) p q = 1.
Proof.
  intros a b p q Hp Hq Hp2 Hq2 Hap Haq Hbp Hbq Ha Hb.
  rewrite (jacobi_mul a b p q Hp Hq Hp2 Hq2 Hap Haq Hbp Hbq).
  rewrite Ha, Hb. reflexivity.
Qed.

Definition cocks_pair (N a t tinv : Z) : Z * Z :=
  (cocks_ciphertext N a t tinv, cocks_ciphertext N (- a) t tinv).

Theorem cocks_pair_first_decrypts :
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
    jacobi_N (fst (cocks_pair (p * q) a t tinv) + 2 * s) p q =
      jacobi_N t p q.
Proof.
  intros p q a t tinv s Hp Hq Hneq Hp2 Hq2 Htp Htq Hsp Hsq Hcp Hcq Hinv Hroot.
  unfold cocks_pair. simpl.
  apply (cocks_decrypt_jacobi p q a t tinv s); assumption.
Qed.

Theorem cocks_pair_second_decrypts :
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
    Z.coprime (cocks_ciphertext (p * q) (- a) t tinv + 2 * s) p ->
    Z.coprime (cocks_ciphertext (p * q) (- a) t tinv + 2 * s) q ->
    (t * tinv) mod (p * q) = 1 ->
    (s * s) mod (p * q) = (- a) mod (p * q) ->
    jacobi_N (snd (cocks_pair (p * q) a t tinv) + 2 * s) p q =
      jacobi_N t p q.
Proof.
  intros p q a t tinv s Hp Hq Hneq Hp2 Hq2 Htp Htq Hsp Hsq Hcp Hcq Hinv Hroot.
  unfold cocks_pair. simpl.
  apply (cocks_decrypt_jacobi p q (- a) t tinv s); assumption.
Qed.

Theorem cocks_pair_covers_blum :
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
Proof. apply cocks_carefully_chosen. Qed.
