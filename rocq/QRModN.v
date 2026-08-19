From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.QuadRecip.
Require Import QuadResidue.
Require Import RabinWilliams.
Require Import RSA.
Require Import Hardness.
Require Import Accumulator.

Open Scope Z_scope.

(** * Quadratic residuosity modulo [N = pq]

    Jacobi [(a/N) = (a/p)(a/q)] is a pairing into [{±1}].  It is
    not the predicate [is_qr_N]: [(a/N) = 1] means both local
    symbols agree, so [a] is a global square *or* a double
    non-residue.  On Blum primes [(-1/p) = (−1/q) = −1], so
    exactly one of [{a, −a}] is a global square when
    [(a/N) = 1].  That is the carefully chosen identity of Cocks
    and the 1-bit pairing Williams spends on [{±a, ±2a}].

    [(g^k/N)] depends on [k] only modulo 2, so Jacobi cannot
    check a sampled-[τ] string.  Cubing is a permutation when
    [gcd(3, λ) = 1], so a cubic decision problem is vacuous on
    units.  A square root and a cube root of the same unit yield
    a sixth root ([shamir_trick] at [(2,3)]).

    Cross-confirmed by [cas/83_qr_modn.gp]. *)

Definition is_qr_N (a N : Z) : Prop :=
  exists x, (x * x) mod N = a mod N.

Definition euler_sign (a p : Z) : Z :=
  if QuadRecip.euler_crit a p =? 1 then 1 else -1.

Lemma euler_crit_agree :
  forall a p, QuadResidue.euler_crit a p = QuadRecip.euler_crit a p.
Proof. intros. reflexivity. Qed.

Definition jacobi_N (a p q : Z) : Z :=
  euler_sign a p * euler_sign a q.

Lemma mod_pq_to_p :
  forall a p q,
    0 < p ->
    0 < q ->
    (a mod (p * q)) mod p = a mod p.
Proof.
  intros a p q Hp Hq.
  apply Z.mod_mod_divide.
  exists q. ring.
Qed.

Lemma qr_N_implies_local :
  forall a p q,
    Z.prime p ->
    Z.prime q ->
    is_qr_N a (p * q) ->
    is_qr a p /\ is_qr a q.
Proof.
  intros a p q Hp Hq [x Hx].
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  split.
  - exists x.
    rewrite <- (mod_pq_to_p (x * x) p q ltac:(lia) ltac:(lia)).
    rewrite <- (mod_pq_to_p a p q ltac:(lia) ltac:(lia)).
    rewrite Hx. reflexivity.
  - exists x.
    rewrite <- (mod_pq_to_p (x * x) q p ltac:(lia) ltac:(lia)).
    rewrite <- (mod_pq_to_p a q p ltac:(lia) ltac:(lia)).
    rewrite (Z.mul_comm q p), Hx, (Z.mul_comm p q). reflexivity.
Qed.

Lemma qr_N_of_local :
  forall a p q,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    is_qr a p ->
    is_qr a q ->
    is_qr_N a (p * q).
Proof.
  intros a p q Hp Hq Hneq [xp Hxp] [xq Hxq].
  pose proof (prime_coprime_distinct p q Hp Hq Hneq) as Hcop.
  set (x := Z.combinecong p q xp xq).
  pose proof (Z.combinecong_sound_coprime p q xp xq Hcop) as [Hxp' Hxq'].
  exists x.
  apply crt_mod_eq; try assumption.
  - rewrite Z.mul_mod by (pose proof (Z.prime_ge_2 p Hp); lia).
    unfold x. rewrite Hxp'.
    rewrite <- Z.mul_mod by (pose proof (Z.prime_ge_2 p Hp); lia).
    exact Hxp.
  - rewrite Z.mul_mod by (pose proof (Z.prime_ge_2 q Hq); lia).
    unfold x. rewrite Hxq'.
    rewrite <- Z.mul_mod by (pose proof (Z.prime_ge_2 q Hq); lia).
    exact Hxq.
Qed.

Theorem qr_N_iff_both :
  forall a p q,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    is_qr_N a (p * q) <-> (is_qr a p /\ is_qr a q).
Proof.
  intros a p q Hp Hq Hneq.
  split.
  - apply qr_N_implies_local; assumption.
  - intros [Hpqr Hqqr]. apply qr_N_of_local; assumption.
Qed.

Lemma euler_sign_of_pm1 :
  forall a p,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    euler_sign a p = 1 \/ euler_sign a p = -1.
Proof.
  intros a p Hp Hne Hcop.
  unfold euler_sign.
  destruct (euler_is_pm1 a p Hp Hne Hcop) as [H1 | Hm].
  - rewrite H1. left. reflexivity.
  - rewrite Hm.
    destruct (p - 1 =? 1) eqn:Heq.
    + apply Z.eqb_eq in Heq. pose proof (Z.prime_ge_2 p Hp). lia.
    + right. reflexivity.
Qed.

Lemma euler_sign_of_qr :
  forall a p,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    is_qr a p ->
    euler_sign a p = 1.
Proof.
  intros a p Hp Hne Hcop Hqr.
  unfold euler_sign.
  rewrite (qr_implies_euler_one a p Hp Hne Hcop Hqr).
  reflexivity.
Qed.

Theorem jacobi_of_qr_N :
  forall a p q,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    Z.coprime a p ->
    Z.coprime a q ->
    is_qr_N a (p * q) ->
    jacobi_N a p q = 1.
Proof.
  intros a p q Hp Hq Hp2 Hq2 Hap Haq Hqr.
  apply qr_N_implies_local in Hqr; [| exact Hp | exact Hq].
  destruct Hqr as [Hrp Hrq].
  unfold jacobi_N.
  rewrite (euler_sign_of_qr a p Hp Hp2 Hap Hrp).
  rewrite (euler_sign_of_qr a q Hq Hq2 Haq Hrq).
  reflexivity.
Qed.

Theorem euler_one_implies_qr_blum :
  forall a p,
    Z.prime p ->
    p mod 4 = 3 ->
    Z.coprime a p ->
    QuadRecip.euler_crit a p = 1 ->
    is_qr a p.
Proof.
  intros a p Hp Hm Hcop Heu.
  pose proof (Z.prime_ge_2 p Hp).
  set (a0 := a mod p).
  assert (0 <= a0 < p) by (apply Z.mod_pos_bound; lia).
  assert (QuadResidue.euler_crit a0 p = 1) as Heu0.
  { unfold QuadResidue.euler_crit, QuadRecip.euler_crit, a0 in *.
    rewrite powm_mod_base by lia. exact Heu. }
  exists (sqrt_mod4_3 a0 p).
  pose proof (sqrt_mod4_3_correct a0 p Hp Hm ltac:(lia) Heu0) as Hsqrt.
  unfold powm in Hsqrt.
  rewrite Z.pow_2_r in Hsqrt.
  unfold a0 in Hsqrt. rewrite Z.mod_mod in Hsqrt by lia. exact Hsqrt.
Qed.

Lemma euler_sign_one_is_crit_one :
  forall a p,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    euler_sign a p = 1 ->
    QuadRecip.euler_crit a p = 1.
Proof.
  intros a p Hp Hne Hcop Hs.
  unfold euler_sign in Hs.
  destruct (euler_is_pm1 a p Hp Hne Hcop) as [H1 | Hm].
  - exact H1.
  - rewrite Hm in Hs.
    destruct (p - 1 =? 1) eqn:Heq; [| discriminate].
    apply Z.eqb_eq in Heq. pose proof (Z.prime_ge_2 p Hp). lia.
Qed.

Lemma euler_sign_minus_is_crit_pm1 :
  forall a p,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    euler_sign a p = -1 ->
    QuadRecip.euler_crit a p = p - 1.
Proof.
  intros a p Hp Hne Hcop Hs.
  unfold euler_sign in Hs.
  destruct (euler_is_pm1 a p Hp Hne Hcop) as [H1 | Hm].
  - rewrite H1 in Hs. discriminate.
  - exact Hm.
Qed.

Lemma euler_sign_one_implies_qr_blum :
  forall a p,
    Z.prime p ->
    p mod 4 = 3 ->
    Z.coprime a p ->
    euler_sign a p = 1 ->
    is_qr a p.
Proof.
  intros a p Hp Hm Hcop Hs.
  apply euler_one_implies_qr_blum; try assumption.
  apply euler_sign_one_is_crit_one; try assumption.
  intro Heq; subst p; discriminate.
Qed.

Lemma euler_sign_minus_implies_qnr :
  forall a p,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    euler_sign a p = -1 ->
    is_qnr a p.
Proof.
  intros a p Hp Hne Hcop Hs.
  apply euler_minus_implies_qnr; try assumption.
  apply euler_sign_minus_is_crit_pm1; assumption.
Qed.

Lemma coprime_neg1 :
  forall p, Z.gcd (-1) p = 1.
Proof.
  intros p.
  replace (-1) with (- (1)) by lia.
  rewrite Z.gcd_opp_l. apply Z.gcd_1_l.
Qed.

Lemma coprime_opp :
  forall a n, Z.coprime a n -> Z.coprime (- a) n.
Proof. intros a n H. unfold Z.coprime in *. rewrite Z.gcd_opp_l. exact H. Qed.

Lemma euler_sign_neg1_blum :
  forall p,
    Z.prime p ->
    p mod 4 = 3 ->
    euler_sign (-1) p = -1.
Proof.
  intros p Hp Hm.
  unfold euler_sign.
  rewrite <- euler_crit_agree.
  rewrite (neg1_euler_mod4_3 p Hp Hm).
  destruct (p - 1 =? 1) eqn:Heq.
  - apply Z.eqb_eq in Heq.
    pose proof (Z.prime_ge_2 p Hp).
    assert (p = 2) by lia. subst p. discriminate.
  - reflexivity.
Qed.

Lemma euler_crit_mul :
  forall a b p,
    Z.prime p ->
    p <> 2 ->
    QuadRecip.euler_crit (a * b) p =
      (powm a ((p - 1) / 2) p * powm b ((p - 1) / 2) p) mod p.
Proof.
  intros a b p Hp Hne.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (half_pm1_nonneg p Hp Hne).
  unfold QuadRecip.euler_crit, powm.
  rewrite Z.pow_mul_l.
  apply Z.mul_mod; lia.
Qed.

Lemma euler_sign_mul :
  forall a b p,
    Z.prime p ->
    p <> 2 ->
    Z.coprime a p ->
    Z.coprime b p ->
    euler_sign (a * b) p = euler_sign a p * euler_sign b p.
Proof.
  intros a b p Hp Hne Ha Hb.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (half_pm1_nonneg p Hp Hne).
  assert (Z.coprime (a * b) p) as Hab.
  { rewrite coprime_comm. apply coprime_mul_iff.
    split; rewrite coprime_comm; assumption. }
  destruct (euler_is_pm1 a p Hp Hne Ha) as [Ha1 | Ham];
  destruct (euler_is_pm1 b p Hp Hne Hb) as [Hb1 | Hbm].
  - unfold euler_sign. rewrite Ha1, Hb1.
    rewrite (euler_crit_mul a b p Hp Hne).
    unfold QuadRecip.euler_crit in Ha1, Hb1.
    rewrite Ha1, Hb1, Z.mul_1_l, Z.mod_1_l by lia. reflexivity.
  - unfold euler_sign. rewrite Ha1, Hbm.
    destruct (p - 1 =? 1) eqn:Heq;
      [apply Z.eqb_eq in Heq; pose proof (Z.prime_ge_2 p Hp); lia|].
    rewrite (euler_crit_mul a b p Hp Hne).
    unfold QuadRecip.euler_crit in Ha1, Hbm.
    rewrite Ha1, Hbm, Z.mul_1_l, Z.mod_small by lia.
    rewrite Heq. reflexivity.
  - unfold euler_sign. rewrite Ham, Hb1.
    destruct (p - 1 =? 1) eqn:Heq;
      [apply Z.eqb_eq in Heq; pose proof (Z.prime_ge_2 p Hp); lia|].
    rewrite (euler_crit_mul a b p Hp Hne).
    unfold QuadRecip.euler_crit in Ham, Hb1.
    rewrite Ham, Hb1, Z.mul_1_r, Z.mod_small by lia.
    rewrite Heq. reflexivity.
  - unfold euler_sign. rewrite Ham, Hbm.
    destruct (p - 1 =? 1) eqn:Heq;
      [apply Z.eqb_eq in Heq; pose proof (Z.prime_ge_2 p Hp); lia|].
    rewrite (euler_crit_mul a b p Hp Hne).
    unfold QuadRecip.euler_crit in Ham, Hbm.
    rewrite Ham, Hbm.
    replace ((p - 1) * (p - 1)) with (1 + (p - 2) * p) by ring.
    rewrite Z.mod_add, Z.mod_1_l by lia. reflexivity.
Qed.

Lemma euler_sign_neg_a :
  forall a p,
    Z.prime p ->
    p <> 2 ->
    p mod 4 = 3 ->
    Z.coprime a p ->
    euler_sign (- a) p = - euler_sign a p.
Proof.
  intros a p Hp Hne Hm Hcop.
  replace (- a) with ((-1) * a) by ring.
  rewrite (euler_sign_mul (-1) a p Hp Hne (coprime_neg1 p) Hcop).
  rewrite (euler_sign_neg1_blum p Hp Hm).
  ring.
Qed.

Theorem jacobi_neg1_blum :
  forall p q,
    Z.prime p ->
    Z.prime q ->
    p mod 4 = 3 ->
    q mod 4 = 3 ->
    jacobi_N (-1) p q = 1.
Proof.
  intros p q Hp Hq Hmp Hmq.
  unfold jacobi_N.
  rewrite (euler_sign_neg1_blum p Hp Hmp).
  rewrite (euler_sign_neg1_blum q Hq Hmq).
  reflexivity.
Qed.

Theorem neg1_not_qr_N_blum :
  forall p q,
    Z.prime p ->
    Z.prime q ->
    p mod 4 = 3 ->
    ~ is_qr_N (-1) (p * q).
Proof.
  intros p q Hp Hq Hmp Hqr.
  apply qr_N_implies_local in Hqr; [| exact Hp | exact Hq].
  destruct Hqr as [Hrp _].
  pose proof (Z.prime_ge_2 p Hp).
  assert (p <> 2) as Hp2 by (intro Heq; subst p; discriminate).
  pose proof (qr_implies_euler_one (-1) p Hp Hp2 (coprime_neg1 p) Hrp)
    as Heu.
  pose proof (neg1_euler_mod4_3 p Hp Hmp) as Hneg.
  rewrite euler_crit_agree in Hneg. lia.
Qed.

(** The carefully chosen element: [(a/N) = 1] on a Blum pair means
    exactly one of [{a, −a}] is a global square. *)
Theorem blum_jacobi_one_exactly_one_pm :
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
Proof.
  intros a p q Hp Hq Hneq Hmp Hmq Hap Haq Hj.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  assert (p <> 2) as Hp2 by (intro Heq; subst p; discriminate).
  assert (q <> 2) as Hq2 by (intro Heq; subst q; discriminate).
  destruct (euler_sign_of_pm1 a p Hp Hp2 Hap) as [Hsp | Hsp];
  destruct (euler_sign_of_pm1 a q Hq Hq2 Haq) as [Hsq | Hsq].
  - left. split.
    + apply qr_N_of_local; try assumption.
      * apply euler_sign_one_implies_qr_blum; assumption.
      * apply euler_sign_one_implies_qr_blum; assumption.
    + intro Hneg.
      apply qr_N_implies_local in Hneg; [| exact Hp | exact Hq].
      destruct Hneg as [Hrp _].
      pose proof (euler_sign_of_qr (- a) p Hp Hp2 (coprime_opp a p Hap) Hrp)
        as Hsn.
      rewrite (euler_sign_neg_a a p Hp Hp2 Hmp Hap) in Hsn.
      rewrite Hsp in Hsn. lia.
  - unfold jacobi_N in Hj. rewrite Hsp, Hsq in Hj. lia.
  - unfold jacobi_N in Hj. rewrite Hsp, Hsq in Hj. lia.
  - right. split.
    + apply qr_N_of_local; try assumption.
      * pose proof (euler_sign_neg_a a p Hp Hp2 Hmp Hap) as Hna_p.
        rewrite Hsp in Hna_p.
        apply euler_sign_one_implies_qr_blum; try assumption.
        apply coprime_opp; exact Hap.
      * pose proof (euler_sign_neg_a a q Hq Hq2 Hmq Haq) as Hna_q.
        rewrite Hsq in Hna_q.
        apply euler_sign_one_implies_qr_blum; try assumption.
        apply coprime_opp; exact Haq.
    + intro Hpos.
      apply qr_N_implies_local in Hpos; [| exact Hp | exact Hq].
      destruct Hpos as [Hrp _].
      pose proof (euler_sign_of_qr a p Hp Hp2 Hap Hrp) as Hsgn.
      rewrite Hsp in Hsgn. discriminate.
Qed.

(** Williams spends the 1-bit pairing: [both_qr] of the two
    Euler symbols is exactly [is_qr_N], on a Blum pair. *)
Theorem williams_both_qr_is_qr_N :
  forall a p q,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    p mod 4 = 3 ->
    q mod 4 = 3 ->
    Z.coprime a p ->
    Z.coprime a q ->
    both_qr (euler_sign a p, euler_sign a q) <-> is_qr_N a (p * q).
Proof.
  intros a p q Hp Hq Hneq Hmp Hmq Hap Haq.
  pose proof (Z.prime_ge_2 p Hp).
  assert (p <> 2) as Hp2 by (intro Heq; subst p; discriminate).
  assert (q <> 2) as Hq2 by (intro Heq; subst q; discriminate).
  split.
  - intros [Hsp Hsq]. simpl in Hsp, Hsq.
    apply qr_N_of_local; try assumption.
    + apply euler_sign_one_implies_qr_blum; assumption.
    + apply euler_sign_one_implies_qr_blum; assumption.
  - intros Hqr.
    apply qr_N_implies_local in Hqr; [| exact Hp | exact Hq].
    destruct Hqr as [Hrp Hrq].
    unfold both_qr. simpl.
    split.
    + apply euler_sign_of_qr; assumption.
    + apply euler_sign_of_qr; assumption.
Qed.

(** ** Jacobi degeneracy: [(g^k/N)] sees [k] only modulo 2 *)

Lemma coprime_powm_prime :
  forall a e p,
    Z.prime p ->
    0 <= e ->
    Z.coprime a p ->
    Z.coprime (powm a e p) p.
Proof.
  intros a e p Hp He Hcop.
  unfold Z.coprime, powm.
  rewrite Z.gcd_mod by (pose proof (Z.prime_ge_2 p Hp); lia).
  rewrite Z.gcd_comm.
  destruct (Z.eq_dec e 0) as [Hz | Hnz].
  - subst. rewrite Z.pow_0_r. apply Z.gcd_1_l.
  - apply Z.coprime_pow_l; [lia | exact Hcop].
Qed.

Lemma coprime_powm_N_prime :
  forall a e p q,
    Z.prime p ->
    0 < q ->
    0 <= e ->
    Z.coprime a p ->
    Z.coprime (powm a e (p * q)) p.
Proof.
  intros a e p q Hp Hq He Hcop.
  pose proof (Z.prime_ge_2 p Hp).
  unfold Z.coprime, powm.
  rewrite (Z.gcd_comm (a ^ e mod (p * q)) p).
  rewrite <- (Z.gcd_mod (a ^ e mod (p * q)) p) by lia.
  rewrite (mod_pq_to_p (a ^ e) p q ltac:(lia) Hq).
  rewrite (Z.gcd_mod (a ^ e) p) by lia.
  rewrite Z.gcd_comm.
  destruct (Z.eq_dec e 0) as [Hz | Hnz].
  - subst. rewrite Z.pow_0_r. apply Z.gcd_1_l.
  - apply Z.coprime_pow_l; [lia | exact Hcop].
Qed.

Theorem jacobi_even_power :
  forall g k p q,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    p <> q ->
    Z.coprime g p ->
    Z.coprime g q ->
    0 <= k ->
    Z.Even k ->
    jacobi_N (powm g k (p * q)) p q = 1.
Proof.
  intros g k p q Hp Hq Hp2 Hq2 Hneq Hgp Hgq Hk [t Ht].
  subst k.
  assert (0 <= t) by lia.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  assert (is_qr_N (powm g (2 * t) (p * q)) (p * q)) as Hqr.
  { exists (powm g t (p * q)).
    unfold powm.
    rewrite <- Z.mul_mod by nia.
    rewrite <- Z.pow_add_r by lia.
    replace (t + t) with (2 * t) by lia.
    rewrite Z.mod_mod by nia. reflexivity. }
  apply jacobi_of_qr_N; try assumption.
  - apply coprime_powm_N_prime; lia || assumption.
  - rewrite (Z.mul_comm p q).
    apply coprime_powm_N_prime; lia || assumption.
Qed.

Theorem jacobi_odd_power :
  forall g k p q,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    Z.coprime g p ->
    Z.coprime g q ->
    0 <= k ->
    Z.Odd k ->
    jacobi_N (powm g k (p * q)) p q = jacobi_N g p q.
Proof.
  intros g k p q Hp Hq Hp2 Hq2 Hgp Hgq Hk Hodd.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  unfold jacobi_N, euler_sign.
  pose proof (half_pm1_nonneg p Hp Hp2).
  pose proof (half_pm1_nonneg q Hq Hq2).
  assert (QuadRecip.euler_crit (powm g k (p * q)) p =
            QuadRecip.euler_crit g p) as Hpown.
  { unfold QuadRecip.euler_crit.
    replace (powm (powm g k (p * q)) ((p - 1) / 2) p)
      with (powm (powm g k p) ((p - 1) / 2) p).
    2:{ unfold powm.
        rewrite <- (Z.mod_pow_l (g ^ k mod (p * q)) ((p - 1) / 2) p) by lia.
        rewrite (mod_pq_to_p (g ^ k) p q ltac:(lia) ltac:(lia)).
        rewrite (Z.mod_pow_l (g ^ k) ((p - 1) / 2) p) by lia. reflexivity. }
    rewrite <- powm_mul_r by lia.
    rewrite (Z.mul_comm k), powm_mul_r by lia.
    destruct (euler_is_pm1 g p Hp Hp2 Hgp) as [Hgp1 | Hgm].
    - unfold QuadRecip.euler_crit in Hgp1. rewrite Hgp1.
      rewrite powm_1_pow by lia. apply Z.mod_small; lia.
    - unfold QuadRecip.euler_crit in Hgm. rewrite Hgm.
      unfold powm.
      destruct Hodd as [t Ht]. subst k.
      assert (0 <= t) by lia.
      rewrite Z.pow_add_r, Z.pow_mul_r, Z.pow_2_r by lia.
      replace ((p - 1) * (p - 1)) with (1 + (p - 2) * p) by ring.
      rewrite Z.mul_mod by lia.
      rewrite <- (Z.mod_pow_l (1 + (p - 2) * p) t p) by lia.
      rewrite Z.mod_add, Z.mod_1_l by lia.
      rewrite Z.pow_1_l, Z.mod_1_l by lia.
      rewrite Z.pow_1_r, Z.mul_1_l.
      rewrite Z.mod_mod by lia.
      apply Z.mod_small; lia. }
  rewrite Hpown.
  assert (QuadRecip.euler_crit (powm g k (p * q)) q =
            QuadRecip.euler_crit g q) as Hqown.
  { unfold QuadRecip.euler_crit.
    replace (powm (powm g k (p * q)) ((q - 1) / 2) q)
      with (powm (powm g k q) ((q - 1) / 2) q).
    2:{ unfold powm.
        rewrite <- (Z.mod_pow_l (g ^ k mod (p * q)) ((q - 1) / 2) q) by lia.
        rewrite (Z.mul_comm p q).
        rewrite (mod_pq_to_p (g ^ k) q p ltac:(lia) ltac:(lia)).
        rewrite (Z.mod_pow_l (g ^ k) ((q - 1) / 2) q) by lia. reflexivity. }
    rewrite <- powm_mul_r by lia.
    rewrite (Z.mul_comm k), powm_mul_r by lia.
    destruct (euler_is_pm1 g q Hq Hq2 Hgq) as [Hgq1 | Hqm].
    - unfold QuadRecip.euler_crit in Hgq1. rewrite Hgq1.
      rewrite powm_1_pow by lia. apply Z.mod_small; lia.
    - unfold QuadRecip.euler_crit in Hqm. rewrite Hqm.
      destruct Hodd as [t Ht]. subst k.
      assert (0 <= t) by lia.
      unfold powm.
      rewrite Z.pow_add_r, Z.pow_mul_r, Z.pow_2_r by lia.
      replace ((q - 1) * (q - 1)) with (1 + (q - 2) * q) by ring.
      rewrite Z.mul_mod by lia.
      rewrite <- (Z.mod_pow_l (1 + (q - 2) * q) t q) by lia.
      rewrite Z.mod_add, Z.mod_1_l by lia.
      rewrite Z.pow_1_l, Z.mod_1_l by lia.
      rewrite Z.pow_1_r, Z.mul_1_l.
      rewrite Z.mod_mod by lia.
      apply Z.mod_small; lia. }
  rewrite Hqown. reflexivity.
Qed.

Theorem jacobi_sees_only_parity :
  forall g k p q,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    p <> q ->
    Z.coprime g p ->
    Z.coprime g q ->
    0 <= k ->
    jacobi_N (powm g k (p * q)) p q =
      (if Z.even k then 1 else jacobi_N g p q).
Proof.
  intros g k p q Hp Hq Hp2 Hq2 Hneq Hgp Hgq Hk.
  destruct (Z.even k) eqn:Hev.
  - apply Z.even_spec in Hev.
    apply jacobi_even_power; assumption.
  - assert (Z.Odd k).
    { destruct (Z.Even_or_Odd k) as [Hevenk | Hoddk]; [| exact Hoddk].
      apply Z.even_spec in Hevenk. rewrite Hevenk in Hev. discriminate. }
    apply jacobi_odd_power; assumption.
Qed.

(** A sampled-[τ] tail has constant Jacobi: for [i ≥ 1], [τ^i] is
    even iff [τ] is even. *)
Lemma even_pow_succ :
  forall tau i,
    0 <= tau ->
    (1 <= i)%nat ->
    Z.Even tau ->
    Z.Even (tau ^ Z.of_nat i).
Proof.
  intros tau i Ht Hi [t Ht'].
  subst tau.
  exists (2 ^ (Z.of_nat i - 1) * t ^ Z.of_nat i).
  rewrite Z.pow_mul_l.
  assert (0 <= Z.of_nat i - 1) by lia.
  replace (2 ^ Z.of_nat i) with (2 * 2 ^ (Z.of_nat i - 1)).
  2:{ rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  ring.
Qed.

Lemma odd_pow_pos :
  forall tau i,
    0 <= tau ->
    (0 < i)%nat ->
    Z.Odd tau ->
    Z.Odd (tau ^ Z.of_nat i).
Proof.
  intros tau i Ht Hi Hodd.
  revert Hi.
  induction i as [|i IH]; intros Hi.
  - lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    destruct i as [|i'].
    + rewrite Z.pow_0_r, Z.mul_1_r. exact Hodd.
    + destruct Hodd as [u Hu].
      assert (Z.Odd (tau ^ Z.of_nat (S i'))) as IHod.
      { apply IH. lia. }
      destruct IHod as [v Hv].
      rewrite Hv. rewrite Hu.
      exists (2 * u * v + u + v). ring.
Qed.

Theorem pot_jacobi_tail_constant :
  forall g tau i p q,
    Z.prime p ->
    Z.prime q ->
    p <> 2 ->
    q <> 2 ->
    p <> q ->
    Z.coprime g p ->
    Z.coprime g q ->
    0 <= tau ->
    (1 <= i)%nat ->
    jacobi_N (powm g (tau ^ Z.of_nat i) (p * q)) p q =
      jacobi_N (powm g tau (p * q)) p q.
Proof.
  intros g tau i p q Hp Hq Hp2 Hq2 Hneq Hgp Hgq Ht Hi.
  assert (0 <= tau ^ Z.of_nat i) as Hpow by (apply Z.pow_nonneg; exact Ht).
  rewrite (jacobi_sees_only_parity g (tau ^ Z.of_nat i) p q
             Hp Hq Hp2 Hq2 Hneq Hgp Hgq Hpow).
  rewrite (jacobi_sees_only_parity g tau p q
             Hp Hq Hp2 Hq2 Hneq Hgp Hgq Ht).
  destruct (Z.even tau) eqn:Hev.
  - apply Z.even_spec in Hev.
    pose proof (even_pow_succ tau i Ht Hi Hev) as Hevi.
    apply Z.even_spec in Hevi. rewrite Hevi. reflexivity.
  - assert (Z.Odd tau) as Ho.
    { destruct (Z.Even_or_Odd tau) as [Hevenk | Hoddk]; [| exact Hoddk].
      apply Z.even_spec in Hevenk. rewrite Hevenk in Hev. discriminate. }
    pose proof (odd_pow_pos tau i Ht ltac:(lia) Ho) as Hoi.
    apply Z.odd_spec in Hoi.
    rewrite <- Z.negb_odd, Hoi. reflexivity.
Qed.

(** ** Shamir at [(2,3)]: a square root and a cube root yield a sixth root *)

Theorem sixth_root_from_square_and_cube :
  forall N y s c,
    1 < N ->
    Z.coprime s N ->
    Z.coprime c N ->
    powm s 2 N = y ->
    powm c 3 N = y ->
    exists w, powm w 6 N = y.
Proof.
  intros N y s c Hn Hs Hc H2 H3.
  assert (powm s 2 N = powm c 3 N) as Heq by (rewrite H2, H3; reflexivity).
  assert (Z.gcd 2 3 = 1) as Hg23 by (vm_compute; reflexivity).
  destruct (shamir_trick N 2 3 s c Hn ltac:(lia) ltac:(lia) Hg23
              Hc Hs Heq) as [w Hw].
  exists w.
  change 6 with (2 * 3).
  rewrite powm_mul_r by lia.
  rewrite Hw.
  rewrite powm_mod_base by lia.
  exact H3.
Qed.

(** Cubing is a permutation of units when [3] is an RSA exponent. *)
Theorem cubic_decision_vacuous :
  forall R y,
    rsa_e R = 3 ->
    Z.coprime y (rsa_N R) ->
    exists x, powm x 3 (rsa_N R) = y mod rsa_N R.
Proof.
  intros R y He Hcop.
  exists (rsa_dec R y).
  pose proof (rsa_enc_dec_units R y Hcop) as H.
  unfold rsa_enc in H. rewrite He in H. exact H.
Qed.

(** ** Obstruction: Jacobi is an additive pairing into [{±1}]

    [jacobi_sees_only_parity] and [pot_jacobi_tail_constant] are
    the theorem: any Jacobi combination of CRS elements is a
    function of the parities of the exponents.  The target is
    [{±1}].  That cannot check a sampled-[τ] string. *)
