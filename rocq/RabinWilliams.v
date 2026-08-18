From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.QuadRecip.
Require Import QuadResidue.
Require Import Hardness.

Open Scope Z_scope.

(** * Rabin–Williams: squaring in [(Z/NZ)*] with the Williams tweak

    Rabin is RSA at [e = 2], except [e = 2] is *excluded* from an
    [RSAInstance] ([gcd(2, λ) = 2]).  Squaring is 4-to-1 on units,
    so inversion is a search problem equivalent (randomised) to
    factoring: two distinct square roots that are not negatives
    split [N].

    Williams (1980) chooses [p ≡ 3 (mod 8)], [q ≡ 7 (mod 8)] so
    that among [{±a, ±2a}] exactly one pair of Legendre symbols is
    [(+1,+1)].  That unique representative is a square mod [p] and
    mod [q], and the [p ≡ 3 (mod 4)] formula extracts a root.

    The principal-root convention, hash wrapper, and signature
    game are [Refuse_RW_signature_scheme].  Algebra of the tweak
    and the split is what this file proves.

    Cross-confirmed by [cas/19_rabin_williams.gp]. *)

(** ** The Rabin problem *)

Definition Problem_Rabin (N y x : Z) : Prop :=
  powm x 2 N = y.

(** A planted square is always a Rabin instance. *)
Lemma rabin_of_square :
  forall N r, 0 <= 2 -> Problem_Rabin N (powm r 2 N) r.
Proof. intros. unfold Problem_Rabin. reflexivity. Qed.

(** ** Prime shape *)

Definition rw_p_shape (p : Z) : Prop := Z.prime p /\ p mod 8 = 3.
Definition rw_q_shape (q : Z) : Prop := Z.prime q /\ q mod 8 = 7.

Definition rw_pair (p q : Z) : Prop :=
  rw_p_shape p /\ rw_q_shape q /\ p <> q.

Definition blum_prime (p : Z) : Prop := Z.prime p /\ p mod 4 = 3.

Lemma rw_p_is_blum :
  forall p, rw_p_shape p -> blum_prime p.
Proof.
  intros p [Hp Hm]. split; [exact Hp|]. apply mod8_3_is_mod4_3; exact Hm.
Qed.

Lemma rw_q_is_blum :
  forall q, rw_q_shape q -> blum_prime q.
Proof.
  intros q [Hq Hm]. split; [exact Hq|]. apply mod8_7_is_mod4_3; exact Hm.
Qed.

Lemma rw_pair_odd :
  forall p q, rw_pair p q -> p <> 2 /\ q <> 2.
Proof.
  intros p q [[Hp Hpm] [[Hq Hqm] Hne]].
  split; intro Heq; subst; discriminate.
Qed.

(** [λ] is even for odd primes, so [e = 2] is never a valid RSA
    public exponent.  Rabin is *not* an [RSAInstance]. *)
Lemma lcm_even_of_even_l :
  forall n m, Z.Even n -> Z.Even (Z.lcm n m).
Proof.
  intros n m [k Hk].
  unfold Z.Even. rewrite Hk.
  pose proof (Z.divide_lcm_l (2 * k) m) as Hdiv.
  destruct Hdiv as [t Ht]. exists (k * t). lia.
Qed.

Theorem lambda_even_odd_primes :
  forall p q,
    Z.prime p -> Z.prime q -> p <> 2 -> q <> 2 ->
    Z.Even (lambda_semiprime p q).
Proof.
  intros p q Hp Hq Hnp Hnq.
  unfold lambda_semiprime.
  pose proof (odd_prime_minus1_even p Hp Hnp) as He.
  apply lcm_even_of_even_l. exact He.
Qed.

Theorem two_not_rsa_exponent :
  forall p q,
    Z.prime p -> Z.prime q -> p <> 2 -> q <> 2 ->
    ~ Z.coprime 2 (lambda_semiprime p q).
Proof.
  intros p q Hp Hq Hnp Hnq Hcop.
  pose proof (lambda_even_odd_primes p q Hp Hq Hnp Hnq) as Hev.
  destruct Hev as [k Hk].
  unfold Z.coprime in Hcop.
  rewrite Hk in Hcop.
  assert (2 | Z.gcd 2 (2 * k)).
  { apply Z.gcd_greatest; [apply Z.divide_refl | exists k; lia]. }
  rewrite Hcop in H. apply Z.divide_1_r in H. lia.
Qed.

(** ** Williams tweak: among [{±a, ±2a}] exactly one Legendre pair
    is [(+1,+1)], once the mod-8 symbols are the Williams ones.

    The symbols for [2] are the classical
    [(2/p) = (−1)^{(p²−1)/8}], now a theorem ([two_supplement],
    [two_legendre_williams_p], [two_legendre_williams_q]).
    [(−1/p) = −1] when [p ≡ 3 (mod 4)] is [neg1_euler_mod4_3]. *)

Definition legs_a   (ap aq : Z) : Z * Z := (ap, aq).
Definition legs_neg (ap aq : Z) : Z * Z := (- ap, - aq).
Definition legs_2   (ap aq : Z) : Z * Z := (- ap, aq).
Definition legs_m2  (ap aq : Z) : Z * Z := (ap, - aq).

Definition both_qr (uv : Z * Z) : Prop :=
  fst uv = 1 /\ snd uv = 1.

Lemma pm1_cases :
  forall a, a = 1 \/ a = -1 ->
  forall P : Z -> Prop,
    P 1 -> P (-1) -> P a.
Proof. intros a [H|H]; subst; auto. Qed.

Theorem williams_tweak_exists :
  forall ap aq,
    (ap = 1 \/ ap = -1) ->
    (aq = 1 \/ aq = -1) ->
    both_qr (legs_a ap aq) \/
    both_qr (legs_neg ap aq) \/
    both_qr (legs_2 ap aq) \/
    both_qr (legs_m2 ap aq).
Proof.
  intros ap aq Hap Haq.
  unfold both_qr, legs_a, legs_neg, legs_2, legs_m2. cbn.
  destruct Hap as [Hp | Hp]; destruct Haq as [Hq | Hq]; subst; lia.
Qed.

Theorem williams_tweak_unique :
  forall ap aq,
    (ap = 1 \/ ap = -1) ->
    (aq = 1 \/ aq = -1) ->
    (both_qr (legs_a ap aq) ->
      ~ both_qr (legs_neg ap aq) /\
      ~ both_qr (legs_2 ap aq) /\
      ~ both_qr (legs_m2 ap aq)) /\
    (both_qr (legs_neg ap aq) ->
      ~ both_qr (legs_a ap aq) /\
      ~ both_qr (legs_2 ap aq) /\
      ~ both_qr (legs_m2 ap aq)) /\
    (both_qr (legs_2 ap aq) ->
      ~ both_qr (legs_a ap aq) /\
      ~ both_qr (legs_neg ap aq) /\
      ~ both_qr (legs_m2 ap aq)) /\
    (both_qr (legs_m2 ap aq) ->
      ~ both_qr (legs_a ap aq) /\
      ~ both_qr (legs_neg ap aq) /\
      ~ both_qr (legs_2 ap aq)).
Proof.
  intros ap aq Hap Haq.
  unfold both_qr, legs_a, legs_neg, legs_2, legs_m2. cbn.
  destruct Hap as [Hp | Hp]; destruct Haq as [Hq | Hq]; subst; repeat split;
    intros [A B]; lia.
Qed.

(** Which tweak is the square, as a function of the two Legendres. *)
Definition williams_which (ap aq : Z) : Z :=
  if ap =? 1 then (if aq =? 1 then 0 else 3)
  else (if aq =? 1 then 2 else 1).

Theorem williams_which_correct :
  forall ap aq,
    (ap = 1 \/ ap = -1) ->
    (aq = 1 \/ aq = -1) ->
    let w := williams_which ap aq in
    (w = 0 -> both_qr (legs_a ap aq)) /\
    (w = 1 -> both_qr (legs_neg ap aq)) /\
    (w = 2 -> both_qr (legs_2 ap aq)) /\
    (w = 3 -> both_qr (legs_m2 ap aq)).
Proof.
  intros ap aq Hap Haq.
  unfold williams_which, both_qr, legs_a, legs_neg, legs_2, legs_m2.
  destruct Hap as [Hp | Hp]; destruct Haq as [Hq | Hq]; subst; simpl;
    repeat split; intros; lia.
Qed.

Theorem williams_two_symbol_p :
  forall p, Z.prime p -> p mod 8 = 3 -> legendre_two p = -1.
Proof. apply two_legendre_williams_p. Qed.

Theorem williams_two_symbol_q :
  forall q, Z.prime q -> q mod 8 = 7 -> legendre_two q = 1.
Proof. apply two_legendre_williams_q. Qed.

Theorem williams_neg1_on_blum :
  forall p,
    Z.prime p ->
    p mod 8 = 3 \/ p mod 8 = 7 ->
    euler_crit (-1) p = p - 1.
Proof.
  intros p Hp [H | H].
  - apply neg1_euler_mod4_3; [exact Hp | apply mod8_3_is_mod4_3; exact H].
  - apply neg1_euler_mod4_3; [exact Hp | apply mod8_7_is_mod4_3; exact H].
Qed.

(** ** Rabin reduction: two non-associated square roots factor [N]

    If [x² ≡ y² (mod N)] and [x ≢ ± y (mod N)] then
    [gcd(x−y, N)] is a proper factor.  An inversion oracle, queried
    on a random square [r²], returns a root independent of [±r]
    with probability 1/2 and so factors.  This is the tightness
    RSA does *not* have. *)

Theorem rabin_roots_split :
  forall p q x y,
    Z.prime p -> Z.prime q -> p <> q ->
    (x * x) mod (p * q) = (y * y) mod (p * q) ->
    ~ (p * q | x - y) ->
    ~ (p * q | x + y) ->
    let g := Z.gcd (x - y) (p * q) in
    1 < g /\ g < p * q /\ (g | p * q).
Proof.
  intros p q x y Hp Hq Hneq Hsq Hny Hnm g.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  assert (HN : 1 < p * q) by lia.
  assert (p * q | (x - y) * (x + y)) as Hdiv.
  { replace ((x - y) * (x + y)) with (x * x - y * y) by ring.
    apply mods_eq_iff_divides; [lia | exact Hsq]. }
  unfold g.
  split; [| split].
  - destruct (Z.le_gt_cases (Z.gcd (x - y) (p * q)) 1) as [Hle | Hgt];
      [| exact Hgt].
    pose proof (Z.gcd_nonneg (x - y) (p * q)).
    assert (Z.gcd (x - y) (p * q) <> 0).
    { intro Hz. apply Z.gcd_eq_0_r in Hz. lia. }
    assert (Hg1 : Z.gcd (x - y) (p * q) = 1) by lia.
    assert (p * q | x + y).
    { apply Gauss with (x - y).
      - exact Hdiv.
      - apply rel_prime_iff_coprime. unfold Z.coprime.
        rewrite Z.gcd_comm. exact Hg1. }
    contradiction.
  - destruct (Z.lt_ge_cases (Z.gcd (x - y) (p * q)) (p * q)) as [Hlt | Hge];
      [exact Hlt|].
    pose proof (Z.gcd_divide_r (x - y) (p * q)) as HdN.
    pose proof (Z.gcd_nonneg (x - y) (p * q)).
    assert (0 < Z.gcd (x - y) (p * q)).
    { assert (Z.gcd (x - y) (p * q) <> 0).
      { intro Hz. apply Z.gcd_eq_0_r in Hz. lia. }
      lia. }
    pose proof (Z.divide_pos_le (Z.gcd (x - y) (p * q)) (p * q) ltac:(lia) HdN).
    assert (HgN : Z.gcd (x - y) (p * q) = p * q) by lia.
    assert (p * q | x - y).
    { rewrite <- HgN. apply Z.gcd_divide_l. }
    contradiction.
  - apply Z.gcd_divide_r.
Qed.

(** An inversion oracle on [e = 2], queried at a planted square [r²]
    and returning a non-associate root, factors.  RSA has no such
    theorem for an [e]-th-root inverter ([rsa_inverter_constructs_factor_named]
    in [TranscriptOracle]). *)

Theorem rabin_oracle_nonassociate_factors :
  forall p q r x,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    powm x 2 (p * q) = powm r 2 (p * q) ->
    ~ (p * q | x - r) ->
    ~ (p * q | x + r) ->
    let g := Z.gcd (x - r) (p * q) in
    1 < g < p * q /\ (g | p * q).
Proof.
  intros p q r x Hp Hq Hneq Hsq Hny Hnm.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  cbn.
  assert (Hsq' : (x * x) mod (p * q) = (r * r) mod (p * q)).
  { rewrite <- !powm_2 by nia. exact Hsq. }
  pose proof (rabin_roots_split p q x r Hp Hq Hneq Hsq' Hny Hnm) as Hsp.
  destruct Hsp as [H1 [H2 H3]].
  repeat split; [exact H1 | exact H2 | exact H3].
Qed.

(** Specialisation: a non-trivial square root of 1 (already in
    [NumberTheory]) is the [y = 1] case. *)

(** ** Verification shape: [s²] is one of the four tweaks of [H]. *)

Definition rw_tweak (i H : Z) : Z :=
  if i =? 0 then H
  else if i =? 1 then - H
  else if i =? 2 then 2 * H
  else - (2 * H).

Definition rw_verify (N H s : Z) : Prop :=
  exists i, 0 <= i < 4 /\ powm s 2 N = rw_tweak i H mod N.

Lemma rw_verify_of_root :
  forall N H s i,
    0 <= i < 4 ->
    powm s 2 N = rw_tweak i H mod N ->
    rw_verify N H s.
Proof. intros N H s i Hi Heq. exists i. split; assumption. Qed.

(** ** Keygen obligation on top of the RSA rulers: the mod-8 split. *)

Definition kg_rw (p q : Z) : Prop := rw_pair p q.

Lemma kg_rw_implies_blum :
  forall p q, kg_rw p q -> blum_prime p /\ blum_prime q.
Proof.
  intros p q H. unfold kg_rw, rw_pair in H.
  destruct H as [Hp [Hq _]].
  split; [apply rw_p_is_blum | apply rw_q_is_blum]; assumption.
Qed.

Lemma kg_rw_pminus1_almost_odd :
  forall p q,
    kg_rw p q ->
    Z.Odd ((p - 1) / 2) /\ Z.Odd ((q - 1) / 2).
Proof.
  intros p q Hrw.
  destruct (kg_rw_implies_blum p q Hrw) as [[_ Hpm] [_ Hqm]].
  pose proof (blum_prime_pminus1_form p Hpm) as [_ Ho1].
  pose proof (blum_prime_pminus1_form q Hqm) as [_ Ho2].
  split; assumption.
Qed.
