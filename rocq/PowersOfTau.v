From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import UnknownOrder.
Require Import Hardness.

Open Scope Z_scope.

(** * Powers of a sampled [τ] in [(Z/NZ)*]

    The published string is [g^{τ^i}] for [i = 0,1,2,…].  [τ] is
    sampled.  It is not [e⁻¹ (mod λ)].  A contributor holding [ρ]
    replaces each [P_i] by [P_i^{ρ^i}], which equals [g^{(τρ)^i}].
    The only integer that walks the chain backward is an inverse of
    [τ] modulo [ord(g)].  There is no pairing check
    ([pot_bilinear_verify_named], [Refuse_elliptic_curve_branch],
    [Refuse_pairing_accumulators]).  Equal-DL completeness and
    two-transcript extraction are algebra; simulation is
    [Refuse_HVZK_simulation] / [pot_hvzk_eqdl_named].

    Cross-confirmed by [cas/82_powers_of_tau.gp]. *)

Definition pot (N g tau i : Z) : Z :=
  powm g (tau ^ i) N.

Definition pot_contribute (N elem rho i : Z) : Z :=
  powm elem (rho ^ i) N.

Definition Problem_DLog_pot (N g h k : Z) : Prop :=
  powm g k N = h.

(** Pairing verification and HVZK of the equal-DL transcript stay
    named.  Unused: refuse. *)
Definition pot_bilinear_verify_named : Prop :=
  forall (N g tau : Z),
    1 < N ->
    False.

Definition pot_hvzk_eqdl_named : Prop :=
  forall (N g h u v : Z),
    1 < N ->
    False.

(** ** The string is [g^{τ^i}]; the next element is a [τ]-power *)

Lemma pot_at_zero :
  forall N g tau,
    N <> 0 ->
    pot N g tau 0 = g mod N.
Proof.
  intros N g tau Hn.
  unfold pot. rewrite Z.pow_0_r. apply powm_1_r; exact Hn.
Qed.

Lemma pot_at_one :
  forall N g tau,
    N <> 0 ->
    pot N g tau 1 = powm g tau N.
Proof.
  intros N g tau Hn.
  unfold pot. rewrite Z.pow_1_r. reflexivity.
Qed.

Theorem pot_succ_is_tau_power :
  forall N g tau i,
    1 < N ->
    0 <= tau ->
    0 <= i ->
    pot N g tau (i + 1) = powm (pot N g tau i) tau N.
Proof.
  intros N g tau i Hn Ht Hi.
  unfold pot.
  rewrite Z.add_1_r.
  rewrite Z.pow_succ_r by lia.
  rewrite (Z.mul_comm tau).
  apply powm_mul_r; lia.
Qed.

Theorem pot_first_is_dlog :
  forall N g tau,
    N <> 0 ->
    Problem_DLog_pot N g (pot N g tau 1) tau.
Proof.
  intros N g tau Hn.
  unfold Problem_DLog_pot.
  rewrite pot_at_one by exact Hn.
  reflexivity.
Qed.

(** ** Contribution multiplies the secret *)

Theorem pot_contribute_multiplies_tau :
  forall N g tau rho i,
    1 < N ->
    0 <= tau ->
    0 <= rho ->
    0 <= i ->
    pot_contribute N (pot N g tau i) rho i = pot N g (tau * rho) i.
Proof.
  intros N g tau rho i Hn Ht Hr Hi.
  unfold pot_contribute, pot.
  rewrite <- powm_mul_r by (try apply Z.pow_nonneg; lia).
  rewrite <- Z.pow_mul_l by lia.
  rewrite (Z.mul_comm tau rho).
  reflexivity.
Qed.

Theorem two_contributors_product :
  forall N g tau1 tau2 i,
    1 < N ->
    0 <= tau1 ->
    0 <= tau2 ->
    0 <= i ->
    pot_contribute N (pot N g tau1 i) tau2 i =
      pot N g (tau1 * tau2) i.
Proof.
  intros N g tau1 tau2 i Hn H1 H2 Hi.
  apply pot_contribute_multiplies_tau; assumption.
Qed.

Theorem three_contributors_product :
  forall N g tau1 tau2 tau3 i,
    1 < N ->
    0 <= tau1 ->
    0 <= tau2 ->
    0 <= tau3 ->
    0 <= i ->
    pot_contribute N
      (pot_contribute N (pot N g tau1 i) tau2 i) tau3 i =
      pot N g (tau1 * tau2 * tau3) i.
Proof.
  intros N g tau1 tau2 tau3 i Hn H1 H2 H3 Hi.
  rewrite pot_contribute_multiplies_tau by assumption.
  rewrite pot_contribute_multiplies_tau by (try apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_assoc.
  reflexivity.
Qed.

(** ** One honest contribution changes the string *)

Lemma coprime_powm :
  forall a e n,
    1 < n ->
    0 <= e ->
    Z.coprime a n ->
    Z.coprime (powm a e n) n.
Proof.
  intros a e n Hn He Hcop.
  unfold powm, Z.coprime.
  rewrite Z.gcd_mod by lia.
  unfold Z.coprime in Hcop.
  destruct (Z.le_gt_cases e 0) as [He0 | Hepos].
  - assert (e = 0) by lia.
    subst. rewrite Z.pow_0_r, Z.gcd_1_r. reflexivity.
  - assert (forall k : nat, Z.gcd (a ^ Z.of_nat k) n = 1) as Hall.
    { intro k. induction k as [|k IH].
      - rewrite Z.pow_0_r. apply Z.gcd_1_l.
      - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
        rewrite Z.gcd_comm. fold (Z.coprime n (a * a ^ Z.of_nat k)).
        apply coprime_mul_iff. split.
        + unfold Z.coprime. rewrite Z.gcd_comm. exact Hcop.
        + unfold Z.coprime. rewrite Z.gcd_comm. exact IH. }
    rewrite <- (Z2Nat.id e) by lia.
    rewrite Z.gcd_comm. apply Hall.
Qed.

Lemma powm_eq_implies_abs_annihilator :
  forall N g k d,
    1 < N ->
    0 <= k ->
    0 <= d ->
    Z.coprime g N ->
    powm g k N = powm g d N ->
    powm g (Z.abs (k - d)) N = 1.
Proof.
  intros N g k d HN Hk Hd Hcop Heq.
  destruct (Z.le_ge_cases k d) as [Hle | Hge].
  - assert (powm g (d - k) N = 1) as Hann.
    { replace d with (k + (d - k)) in Heq by ring.
      rewrite powm_add_r in Heq by lia.
      assert (Z.coprime (powm g k N) N) as Hcok.
      { apply coprime_powm; [exact HN | exact Hk | exact Hcop]. }
      assert ((powm g (d - k) N * powm g k N) mod N =
                (1 * powm g k N) mod N) as Hmul.
      { rewrite (Z.mul_comm (powm g (d - k) N)), <- Heq.
        unfold powm. rewrite Z.mul_1_l, Z.mod_mod by lia. reflexivity. }
      unfold Z.coprime in Hcok.
      pose proof (mul_cancel_r_coprime (powm g (d - k) N) 1
                    (powm g k N) N HN Hcok Hmul) as Hcan.
      unfold powm in Hcan |- *.
      rewrite Z.mod_mod, Z.mod_1_l in Hcan by lia. exact Hcan. }
    rewrite Z.abs_neq by lia.
    replace (- (k - d)) with (d - k) by ring. exact Hann.
  - assert (powm g (k - d) N = 1) as Hann.
    { replace k with (d + (k - d)) in Heq by ring.
      rewrite powm_add_r in Heq by lia.
      assert (Z.coprime (powm g d N) N) as Hcod.
      { apply coprime_powm; [exact HN | exact Hd | exact Hcop]. }
      assert ((powm g (k - d) N * powm g d N) mod N =
                (1 * powm g d N) mod N) as Hmul.
      { rewrite (Z.mul_comm (powm g (k - d) N)), Heq.
        unfold powm. rewrite Z.mul_1_l, Z.mod_mod by lia. reflexivity. }
      unfold Z.coprime in Hcod.
      pose proof (mul_cancel_r_coprime (powm g (k - d) N) 1
                    (powm g d N) N HN Hcod Hmul) as Hcan.
      unfold powm in Hcan |- *.
      rewrite Z.mod_mod, Z.mod_1_l in Hcan by lia. exact Hcan. }
    rewrite Z.abs_eq by lia. exact Hann.
Qed.

Theorem honest_contribution_moves_string :
  forall N g tau_h tau_d ord,
    1 < N ->
    0 <= tau_h ->
    0 <= tau_d ->
    Z.coprime g N ->
    is_order N g ord ->
    pot N g (tau_h * tau_d) 1 = pot N g tau_d 1 ->
    (ord | tau_d * (tau_h - 1)).
Proof.
  intros N g tau_h tau_d ord Hn Hh Hd Hcop Hord Heq.
  rewrite pot_at_one in Heq by lia.
  rewrite pot_at_one in Heq by lia.
  pose proof (powm_eq_implies_abs_annihilator N g (tau_h * tau_d) tau_d
                Hn ltac:(nia) Hd Hcop Heq) as Hann.
  pose proof (order_divides_annihilator N g ord
                (Z.abs (tau_h * tau_d - tau_d)) Hn (Z.abs_nonneg _)
                Hord Hann) as Hdiv.
  destruct (Z.le_ge_cases (tau_h * tau_d) tau_d) as [Hle | Hge].
  - rewrite Z.abs_neq in Hdiv by lia.
    destruct Hdiv as [m Hm].
    exists (- m).
    nia.
  - rewrite Z.abs_eq in Hdiv by lia.
    destruct Hdiv as [m Hm].
    exists m.
    nia.
Qed.

Theorem honest_tau_one_if_coprime :
  forall N g tau_h tau_d ord,
    1 < N ->
    0 <= tau_h ->
    0 <= tau_d ->
    Z.coprime g N ->
    is_order N g ord ->
    Z.gcd tau_d ord = 1 ->
    pot N g (tau_h * tau_d) 1 = pot N g tau_d 1 ->
    (ord | tau_h - 1).
Proof.
  intros N g tau_h tau_d ord Hn Hh Hd Hcop Hord Hgcd Heq.
  pose proof (honest_contribution_moves_string N g tau_h tau_d ord
                Hn Hh Hd Hcop Hord Heq) as Hdiv.
  apply (Z.gauss ord tau_d (tau_h - 1)).
  - exact Hdiv.
  - rewrite Z.gcd_comm. exact Hgcd.
Qed.

(** ** The only backward walker is [τ⁻¹] modulo the order *)

Lemma powm_reduce_mod_order :
  forall N g ord k,
    1 < N ->
    0 <= k ->
    is_order N g ord ->
    powm g k N = powm g (k mod ord) N.
Proof.
  intros N g ord k Hn Hk Hord.
  destruct Hord as [Ho [Hann Hmin]].
  assert (0 <= k / ord) by (apply Z.div_pos; lia).
  assert (0 <= k mod ord) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod k ord ltac:(lia)) as Hdm.
  rewrite Hdm at 1.
  rewrite powm_add_r by nia.
  rewrite powm_mul_r by nia.
  rewrite Hann.
  rewrite powm_1_pow by nia.
  rewrite Z.mod_1_l by lia.
  rewrite Z.mul_1_l.
  unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem tau_inv_walks_backward :
  forall N g tau e i ord,
    1 < N ->
    0 <= tau ->
    0 <= e ->
    0 <= i ->
    is_order N g ord ->
    (e * tau) mod ord = 1 ->
    powm (pot N g tau (i + 1)) e N = pot N g tau i.
Proof.
  intros N g tau e i ord Hn Ht He Hi Hord Hinv.
  unfold pot.
  rewrite Z.add_1_r.
  rewrite Z.pow_succ_r by lia.
  rewrite <- (powm_mul_r g (tau * tau ^ i) e N)
    by (try apply Z.pow_nonneg; nia).
  rewrite (powm_reduce_mod_order N g ord ((tau * tau ^ i) * e) Hn
             ltac:(nia) Hord).
  rewrite (powm_reduce_mod_order N g ord (tau ^ i) Hn
             ltac:(apply Z.pow_nonneg; lia) Hord).
  assert (((tau * tau ^ i) * e) mod ord = tau ^ i mod ord) as Hexp.
  { replace ((tau * tau ^ i) * e) with ((e * tau) * (tau ^ i)) by ring.
    rewrite <- Z.mul_mod_idemp_l by (destruct Hord as [Ho _]; lia).
    rewrite Hinv.
    rewrite Z.mul_1_l.
    reflexivity. }
  rewrite Hexp. reflexivity.
Qed.

Theorem backward_walker_is_tau_inv :
  forall N g tau e i ord,
    1 < N ->
    0 <= tau ->
    0 <= e ->
    0 <= i ->
    Z.coprime g N ->
    is_order N g ord ->
    Z.gcd (tau ^ i) ord = 1 ->
    powm (pot N g tau (i + 1)) e N = pot N g tau i ->
    (ord | e * tau - 1).
Proof.
  intros N g tau e i ord Hn Ht He Hi Hcop Hord Hgcd Hwalk.
  unfold pot in Hwalk.
  rewrite Z.add_1_r in Hwalk.
  rewrite Z.pow_succ_r in Hwalk by lia.
  rewrite (Z.mul_comm tau) in Hwalk.
  rewrite <- powm_mul_r in Hwalk by (try apply Z.pow_nonneg; lia).
  replace (tau ^ i * tau * e) with (e * (tau ^ i * tau)) in Hwalk by ring.
  pose proof (powm_eq_implies_abs_annihilator N g (e * (tau ^ i * tau))
                (tau ^ i) Hn ltac:(nia) ltac:(apply Z.pow_nonneg; lia)
                Hcop Hwalk) as Hann.
  pose proof (order_divides_annihilator N g ord
                (Z.abs (e * (tau ^ i * tau) - tau ^ i))
                Hn (Z.abs_nonneg _) Hord Hann) as Hdiv.
  assert (ord | e * (tau ^ i * tau) - tau ^ i) as Hdiff.
  { destruct (Z.le_ge_cases (e * (tau ^ i * tau)) (tau ^ i)) as [Hle | Hge].
    - rewrite Z.abs_neq in Hdiv by lia.
      destruct Hdiv as [m Hm]. exists (- m). lia.
    - rewrite Z.abs_eq in Hdiv by lia. exact Hdiv. }
  replace (e * (tau ^ i * tau) - tau ^ i)
    with ((e * tau - 1) * (tau ^ i)) in Hdiff by ring.
  rewrite Z.mul_comm in Hdiff.
  apply (Z.gauss ord (tau ^ i) (e * tau - 1)).
  - exact Hdiff.
  - rewrite Z.gcd_comm. exact Hgcd.
Qed.

(** ** Equal discrete logs: completeness and two-transcript extraction

    Chaum–Pedersen equations only.  No simulator
    ([pot_hvzk_eqdl_named]). *)

Definition eqdl_commit (N g u w : Z) : Z * Z :=
  (powm g w N, powm u w N).

Definition eqdl_response (w c tau : Z) : Z :=
  w + c * tau.

Definition eqdl_verify (N g h u v t1 t2 c z : Z) : Prop :=
  powm g z N = (t1 * powm h c N) mod N /\
  powm u z N = (t2 * powm v c N) mod N.

Theorem eqdl_complete :
  forall N g u tau w c,
    1 < N ->
    0 <= tau ->
    0 <= w ->
    0 <= c ->
    let h := powm g tau N in
    let v := powm u tau N in
    let t := eqdl_commit N g u w in
    eqdl_verify N g h u v (fst t) (snd t) c (eqdl_response w c tau).
Proof.
  intros N g u tau w c Hn Ht Hw Hc h v t.
  subst h v t.
  unfold eqdl_verify, eqdl_commit, eqdl_response. simpl.
  split.
  - rewrite powm_add_r by nia.
    rewrite (Z.mul_comm c tau).
    rewrite powm_mul_r by lia.
    reflexivity.
  - rewrite powm_add_r by nia.
    rewrite (Z.mul_comm c tau).
    rewrite powm_mul_r by lia.
    reflexivity.
Qed.

Theorem eqdl_extracts_tau :
  forall N g tau t1 c c' z z' ord,
    1 < N ->
    0 <= tau ->
    0 <= c' ->
    c' < c ->
    0 <= z' ->
    z' <= z ->
    Z.coprime g N ->
    is_order N g ord ->
    powm g z N = (t1 * powm (powm g tau N) c N) mod N ->
    powm g z' N = (t1 * powm (powm g tau N) c' N) mod N ->
    (ord | (z - z') - tau * (c - c')).
Proof.
  intros N g tau t1 c c' z z' ord Hn Ht Hc' Hcc Hz' Hzle Hcop Hord Hv Hv'.
  assert (0 <= c) by lia.
  assert (0 <= z) by lia.
  rewrite <- (powm_mul_r g tau c N) in Hv by lia.
  rewrite <- (powm_mul_r g tau c' N) in Hv' by lia.
  assert (powm g (z + tau * c') N = powm g (z' + tau * c) N) as Hpow.
  { rewrite !powm_add_r by nia.
    rewrite Hv, Hv'.
    rewrite !Z.mul_mod_idemp_l by lia.
    rewrite <- !Z.mul_assoc.
    rewrite (Z.mul_comm (powm g (tau * c) N) (powm g (tau * c') N)).
    reflexivity. }
  pose proof (powm_eq_implies_abs_annihilator N g (z + tau * c')
                (z' + tau * c) Hn ltac:(nia) ltac:(nia) Hcop Hpow) as Hann.
  pose proof (order_divides_annihilator N g ord
                (Z.abs ((z + tau * c') - (z' + tau * c)))
                Hn (Z.abs_nonneg _) Hord Hann) as Hdiv.
  replace ((z + tau * c') - (z' + tau * c))
    with ((z - z') - tau * (c - c')) in Hdiv by ring.
  destruct (Z.le_ge_cases ((z - z') - tau * (c - c')) 0) as [Hle | Hge].
  - rewrite Z.abs_neq in Hdiv by lia.
    destruct Hdiv as [m Hm]. exists (- m). lia.
  - rewrite Z.abs_eq in Hdiv by lia. exact Hdiv.
Qed.

(** ** Self-bilinear maps evaluate the sampled-[τ] string

    A map [e] with [e(g^a, g^b) = e(g,g)^{ab}] checks consecutive
    powers: [e(P_i, P_1) = e(P_{i+1}, P_0)].  If additionally
    [e(g,g) = g], it *computes* [P_{i+1}] from [P_i] and [P_1],
    so a public self-pairing of that strength would make the
    string publicly extendable.  Existence is a hypothesis, not
    an axiom.  iO constructions are deferred, not refused. *)

Definition self_bilinear (e : Z -> Z -> Z) (N g : Z) : Prop :=
  forall a b,
    0 <= a ->
    0 <= b ->
    e (powm g a N) (powm g b N) = powm (e g g) (a * b) N.

Theorem self_bil_checks_pot :
  forall e N g tau i,
    1 < N ->
    0 <= tau ->
    0 <= i ->
    self_bilinear e N g ->
    e (pot N g tau i) (pot N g tau 1) =
      e (pot N g tau (i + 1)) (pot N g tau 0).
Proof.
  intros e N g tau i Hn Ht Hi He.
  unfold pot.
  rewrite Z.pow_1_r, Z.pow_0_r.
  rewrite (He (tau ^ i) tau ltac:(apply Z.pow_nonneg; lia) Ht).
  rewrite Z.add_1_r, Z.pow_succ_r by lia.
  rewrite (He (tau * tau ^ i) 1 ltac:(nia) ltac:(lia)).
  rewrite Z.mul_1_r, (Z.mul_comm tau).
  reflexivity.
Qed.

Theorem self_bil_evaluates_pot :
  forall e N g tau i,
    1 < N ->
    0 <= tau ->
    0 <= i ->
    self_bilinear e N g ->
    e g g = g mod N ->
    e (pot N g tau i) (pot N g tau 1) = pot N g tau (i + 1).
Proof.
  intros e N g tau i Hn Ht Hi He Hgg.
  unfold pot.
  rewrite Z.pow_1_r.
  rewrite (He (tau ^ i) tau ltac:(apply Z.pow_nonneg; lia) Ht).
  rewrite Hgg.
  rewrite powm_mod_base by lia.
  rewrite Z.add_1_r, Z.pow_succ_r by lia.
  rewrite (Z.mul_comm tau).
  reflexivity.
Qed.
