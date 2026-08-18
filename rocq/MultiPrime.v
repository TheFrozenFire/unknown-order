From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Zmod.

Require Import RocqProofs.NumberTheory.
Require Import TwoSylow.
Require Import Hardness.

Open Scope Z_scope.

(** * Multi-prime stress test: [N = pqr] has eight roots of [1]

    [sqrt1_is_crt_pm1] is two-prime: four combinations of [±1].
    Three distinct odd primes give [2³] sign patterns.  A mixed
    pattern (not [±1] on every prime) splits [N] via [gcd(x−1, N)].
    Carmichael [λ(pqr)] annihilates the units; a one-sided period
    still splits off a proper factor. *)

Definition three_prime (p q r : Z) : Prop :=
  Z.prime p /\ Z.prime q /\ Z.prime r /\
  p <> q /\ p <> r /\ q <> r.

Theorem two_prime_sqrt1_is_pm1_each :
  forall p q x,
    Z.prime p -> Z.prime q -> p <> q ->
    powm x 2 (p * q) = 1 ->
    (x mod p = 1 \/ x mod p = p - 1) /\
    (x mod q = 1 \/ x mod q = q - 1).
Proof. apply sqrt1_is_crt_pm1. Qed.

Theorem three_prime_sqrt1_is_pm1_each :
  forall p q r x,
    three_prime p q r ->
    powm x 2 (p * q * r) = 1 ->
    (x mod p = 1 \/ x mod p = p - 1) /\
    (x mod q = 1 \/ x mod q = q - 1) /\
    (x mod r = 1 \/ x mod r = r - 1).
Proof.
  intros p q r x [Hp [Hq [Hr [Hpq [Hpr Hqr]]]]] Hsq.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  pose proof (Z.prime_ge_2 r Hr).
  assert (powm x 2 p = 1) as Hp1.
  { unfold powm in Hsq |- *.
    rewrite Z.pow_2_r in Hsq |- *.
    transitivity (((x * x) mod (p * q * r)) mod p).
    - symmetry. apply Z.mod_mod_divide. exists (q * r). ring.
    - rewrite Hsq. apply Z.mod_1_l. lia. }
  assert (powm x 2 q = 1) as Hq1.
  { unfold powm in Hsq |- *.
    rewrite Z.pow_2_r in Hsq |- *.
    transitivity (((x * x) mod (p * q * r)) mod q).
    - symmetry. apply Z.mod_mod_divide. exists (p * r). ring.
    - rewrite Hsq. apply Z.mod_1_l. lia. }
  assert (powm x 2 r = 1) as Hr1.
  { unfold powm in Hsq |- *.
    rewrite Z.pow_2_r in Hsq |- *.
    transitivity (((x * x) mod (p * q * r)) mod r).
    - symmetry. apply Z.mod_mod_divide. exists (p * q). ring.
    - rewrite Hsq. apply Z.mod_1_l. lia. }
  split; [|split].
  - apply powm_2_mod_prime_pm1; assumption.
  - apply powm_2_mod_prime_pm1; assumption.
  - apply powm_2_mod_prime_pm1; assumption.
Qed.

Definition sign_pat : Type := (bool * bool * bool).

Definition eight_pats : list sign_pat :=
  (false, false, false) :: (false, false, true) ::
  (false, true, false) :: (false, true, true) ::
  (true, false, false) :: (true, false, true) ::
  (true, true, false) :: (true, true, true) :: nil.

Theorem eight_pats_length : List.length eight_pats = 8%nat.
Proof. reflexivity. Qed.

Theorem two_prime_arity_is_four :
  forall p q,
    Z.prime p -> Z.prime q -> p <> q ->
    (forall x, powm x 2 (p * q) = 1 ->
      (x mod p = 1 \/ x mod p = p - 1) /\
      (x mod q = 1 \/ x mod q = q - 1)).
Proof. intros. apply sqrt1_is_crt_pm1; assumption. Qed.

Theorem two_sylow_is_two_prime :
  forall p q x,
    Z.prime p -> Z.prime q -> p <> q ->
    powm x 2 (p * q) = 1 ->
    (x mod p = 1 \/ x mod p = p - 1).
Proof. intros. apply sqrt1_is_crt_pm1 in H2; tauto. Qed.

Lemma prime_gcd_1 :
  forall p q, Z.prime p -> Z.prime q -> p <> q -> Z.gcd p q = 1.
Proof.
  intros p q Hp Hq Hneq.
  apply Z.coprime_prime_l_iff; [exact Hp|].
  intro Hdiv. apply Z.divide_prime_prime in Hdiv;
    [lia | exact Hp | exact Hq].
Qed.

Lemma crt_coprime_exists :
  forall m n a b,
    1 < m ->
    1 < n ->
    Z.gcd m n = 1 ->
    exists x, x mod m = a mod m /\ x mod n = b mod n.
Proof.
  intros m n a b Hm Hn Hg.
  destruct (Z.gcd_bezout m n 1 Hg) as [s [t Hs]].
  exists (a + m * ((b - a) * s)).
  split.
  - rewrite (Z.mul_comm m ((b - a) * s)).
    rewrite Z.mod_add by lia. reflexivity.
  - assert ((m * s) mod n = 1).
    { transitivity (1 mod n).
      - apply (proj2 (mods_eq_iff_divides (m * s) 1 n ltac:(lia))).
        exists (- t). rewrite (Z.mul_comm s m) in Hs. lia.
      - apply Z.mod_small; lia. }
    replace (m * ((b - a) * s)) with ((b - a) * (m * s)) by ring.
    rewrite <- Z.add_mod_idemp_r, <- Z.mul_mod_idemp_r, H, Z.mul_1_r by lia.
    rewrite Z.add_mod_idemp_r by lia.
    replace (a + (b - a)) with b by ring.
    reflexivity.
Qed.

Lemma crt2_exists :
  forall p q a b,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    exists x, x mod p = a mod p /\ x mod q = b mod q.
Proof.
  intros p q a b Hp Hq Hneq.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  apply crt_coprime_exists; try lia.
  apply prime_gcd_1; assumption.
Qed.

Lemma mod_mod_product :
  forall x u v,
    0 < u -> 0 < v ->
    (x mod (u * v)) mod u = x mod u.
Proof.
  intros x u v Hu Hv.
  pose proof (Z.div_mod x (u * v) ltac:(nia)) as Hx.
  rewrite Hx at 2.
  replace ((u * v) * (x / (u * v))) with ((v * (x / (u * v))) * u) by ring.
  rewrite Z.add_comm.
  rewrite Z.mod_add by lia.
  reflexivity.
Qed.

Lemma three_prime_pq_coprime_r :
  forall p q r,
    three_prime p q r -> Z.coprime (p * q) r.
Proof.
  intros p q r [Hp [Hq [Hr [Hpq [Hpr Hqr]]]]].
  apply coprime_comm. apply coprime_mul_iff.
  split; apply coprime_comm; apply prime_coprime_distinct; assumption.
Qed.

Lemma crt3_exists :
  forall p q r a b c,
    three_prime p q r ->
    exists x,
      x mod p = a mod p /\
      x mod q = b mod q /\
      x mod r = c mod r.
Proof.
  intros p q r a b c H3.
  destruct H3 as [Hp [Hq [Hr [Hpq [Hpr Hqr]]]]].
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  pose proof (Z.prime_ge_2 r Hr).
  destruct (crt2_exists p q a b Hp Hq Hpq) as [y [Hyp Hyq]].
  assert (Z.gcd (p * q) r = 1) as Hg.
  { apply three_prime_pq_coprime_r.
    unfold three_prime. tauto. }
  destruct (crt_coprime_exists (p * q) r y c ltac:(nia) ltac:(lia) Hg)
    as [x [Hxy Hxr]].
  exists x. split; [| split].
  - rewrite <- Hyp. rewrite <- (mod_mod_product x p q) by lia.
    rewrite Hxy. apply mod_mod_product; lia.
  - rewrite <- Hyq. rewrite <- (mod_mod_product x q p) by lia.
    rewrite (Z.mul_comm q p), Hxy, (Z.mul_comm p q).
    rewrite (mod_mod_product y q p) by lia. reflexivity.
  - exact Hxr.
Qed.

(** A √1 that is [+1] on at least one prime and [−1] on another
    has [gcd(x−1, pqr)] a proper factor.  [q <> 2] so [−1 ≢ 1]
    on that side. *)

Theorem mixed_triple_splits :
  forall p q r x,
    three_prime p q r ->
    q <> 2 ->
    powm x 2 (p * q * r) = 1 ->
    x mod p = 1 ->
    x mod q = q - 1 ->
    let g := Z.gcd (x - 1) (p * q * r) in
    1 < g /\ g < p * q * r /\ (g | p * q * r).
Proof.
  intros p q r x [Hp [Hq [Hr [Hpq [Hpr Hqr]]]]] Hq2 Hsq Hp1 Hq1 g.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  pose proof (Z.prime_ge_2 r Hr).
  unfold g.
  assert (p | x - 1) as Hpx.
  { apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Hp1, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity. }
  assert (~ (q | x - 1)) as Hqn.
  { intro Hdiv. apply Z.mod_divide in Hdiv; [|lia].
    rewrite Zminus_mod, Hq1, Z.mod_1_l in Hdiv by lia.
    replace ((q - 1 - 1) mod q) with ((q - 2) mod q) in Hdiv
      by (f_equal; ring).
    rewrite Z.mod_small in Hdiv by lia. lia. }
  pose proof (Z.gcd_divide_l (x - 1) (p * q * r)) as Hgx.
  pose proof (Z.gcd_divide_r (x - 1) (p * q * r)) as HgN.
  split; [| split].
  - pose proof (Z.gcd_nonneg (x - 1) (p * q * r)).
    destruct (Z.le_gt_cases (Z.gcd (x - 1) (p * q * r)) 1) as [Hle | Hgt];
      [| exact Hgt].
    assert (Z.gcd (x - 1) (p * q * r) <> 0) as Hgnz.
    { intro Hz. apply Z.gcd_eq_0 in Hz. nia. }
    assert (Z.gcd (x - 1) (p * q * r) = 1) as Hg1 by lia.
    assert (p | Z.gcd (x - 1) (p * q * r)) as Hpg.
    { apply Z.gcd_greatest; [exact Hpx |].
      exists (q * r). ring. }
    rewrite Hg1 in Hpg. apply Z.divide_1_r in Hpg. lia.
  - destruct (Z.lt_ge_cases (Z.gcd (x - 1) (p * q * r)) (p * q * r))
      as [Hlt | Hge]; [exact Hlt|].
    assert (Z.gcd (x - 1) (p * q * r) = p * q * r) as Hgeq.
    { pose proof (Z.divide_pos_le (Z.gcd (x - 1) (p * q * r)) (p * q * r)
                    ltac:(nia) HgN). lia. }
    assert (q | x - 1).
    { rewrite Hgeq in Hgx.
      apply (Z.divide_trans q (p * q * r) (x - 1)); [| exact Hgx].
      exists (p * r). ring. }
    contradiction.
  - exact HgN.
Qed.

(** ** Constructive eight roots *)

Definition sign_residue (neg : bool) (p : Z) : Z :=
  if neg then p - 1 else 1.

Definition crt3 (p q r a b c : Z) : Z :=
  Z.combinecong (p * q) r (Z.combinecong p q a b) c.

Lemma crt3_mod :
  forall p q r a b c,
    three_prime p q r ->
    let x := crt3 p q r a b c in
    x mod p = a mod p /\
    x mod q = b mod q /\
    x mod r = c mod r.
Proof.
  intros p q r a b c H3 x.
  pose proof (Z.prime_ge_2 p (proj1 H3)).
  pose proof (Z.prime_ge_2 q (proj1 (proj2 H3))).
  pose proof (Z.prime_ge_2 r (proj1 (proj2 (proj2 H3)))).
  assert (Z.coprime p q) as Hpq.
  { destruct H3 as [Hp [Hq [_ [Hneq _]]]].
    apply prime_coprime_distinct; assumption. }
  assert (Z.coprime (p * q) r) as Hpqr by (apply three_prime_pq_coprime_r; exact H3).
  unfold x, crt3.
  pose proof (Z.combinecong_sound_coprime (p * q) r
                (Z.combinecong p q a b) c Hpqr) as [Hxy Hxr].
  pose proof (Z.combinecong_sound_coprime p q a b Hpq) as [Hyp Hyq].
  split; [| split].
  - rewrite <- Hyp. rewrite <- (mod_mod_product _ p q) by lia.
    rewrite Hxy. apply mod_mod_product; lia.
  - rewrite <- Hyq. rewrite <- (mod_mod_product _ q p) by lia.
    rewrite (Z.mul_comm q p), Hxy, (Z.mul_comm p q).
    apply mod_mod_product; lia.
  - exact Hxr.
Qed.

Definition eight_sqrt1 (p q r : Z) (s : sign_pat) : Z :=
  let '(sp, sq, sr) := s in
  crt3 p q r (sign_residue sp p) (sign_residue sq q) (sign_residue sr r).

Lemma sign_residue_pm1 :
  forall neg p, sign_residue neg p = 1 \/ sign_residue neg p = p - 1.
Proof. intros []; simpl; auto. Qed.

Lemma square_mod_one_of_pm1 :
  forall x n r,
    1 < n ->
    x mod n = r ->
    (r = 1 \/ r = n - 1) ->
    (x * x) mod n = 1 mod n.
Proof.
  intros x n r Hn Hxr [Hr | Hr].
  - rewrite Hr in Hxr.
    rewrite Z.mul_mod, Hxr, !Z.mod_1_l by lia. reflexivity.
  - rewrite Hr in Hxr.
    rewrite Z.mul_mod, Hxr by lia.
    replace ((n - 1) * (n - 1)) with (1 + (n - 2) * n) by ring.
    rewrite Z.mod_add, !Z.mod_1_l by lia. reflexivity.
Qed.

Lemma eight_sqrt1_mod :
  forall p q r s,
    three_prime p q r ->
    let '(sp, sq, sr) := s in
    let x := eight_sqrt1 p q r s in
    x mod p = sign_residue sp p mod p /\
    x mod q = sign_residue sq q mod q /\
    x mod r = sign_residue sr r mod r.
Proof.
  intros p q r [[sp sq] sr] H3. simpl.
  apply crt3_mod; exact H3.
Qed.

Theorem eight_sqrt1_squares :
  forall p q r s,
    three_prime p q r ->
    powm (eight_sqrt1 p q r s) 2 (p * q * r) = 1.
Proof.
  intros p q r [[sp sq] sr] H3.
  pose proof (Z.prime_ge_2 p (proj1 H3)).
  pose proof (Z.prime_ge_2 q (proj1 (proj2 H3))).
  pose proof (Z.prime_ge_2 r (proj1 (proj2 (proj2 H3)))).
  set (N := p * q * r).
  assert (1 < N) by (unfold N; nia).
  pose proof (eight_sqrt1_mod p q r (sp, sq, sr) H3) as Hx.
  simpl in Hx. destruct Hx as [Hxp [Hxq Hxr]].
  unfold powm. rewrite Z.pow_2_r.
  transitivity (1 mod N); [| apply Z.mod_small; nia].
  apply mods_eq_iff_divides; [nia|].
  apply divide_by_coprime_product.
  - apply three_prime_pq_coprime_r; exact H3.
  - apply divide_by_coprime_product.
    + destruct H3 as [Hp [Hq [_ [Hneq _]]]].
      apply prime_coprime_distinct; assumption.
    + apply mods_eq_iff_divides; [lia|].
      apply (square_mod_one_of_pm1 _ p (sign_residue sp p mod p));
        [lia | exact Hxp |].
      rewrite Z.mod_small by (destruct sp; simpl; lia).
      apply sign_residue_pm1.
    + apply mods_eq_iff_divides; [lia|].
      apply (square_mod_one_of_pm1 _ q (sign_residue sq q mod q));
        [lia | exact Hxq |].
      rewrite Z.mod_small by (destruct sq; simpl; lia).
      apply sign_residue_pm1.
  - apply mods_eq_iff_divides; [lia|].
    apply (square_mod_one_of_pm1 _ r (sign_residue sr r mod r));
      [lia | exact Hxr |].
    rewrite Z.mod_small by (destruct sr; simpl; lia).
    apply sign_residue_pm1.
Qed.

Definition mixed_pqr (p q r : Z) : Z :=
  eight_sqrt1 p q r (false, true, false).

Theorem mixed_pqr_splits :
  forall p q r,
    three_prime p q r ->
    q <> 2 ->
    let x := mixed_pqr p q r in
    powm x 2 (p * q * r) = 1 /\
    let g := Z.gcd (x - 1) (p * q * r) in
    1 < g /\ g < p * q * r /\ (g | p * q * r).
Proof.
  intros p q r H3 Hq2 x.
  subst x. unfold mixed_pqr.
  pose proof (Z.prime_ge_2 p (proj1 H3)).
  pose proof (Z.prime_ge_2 q (proj1 (proj2 H3))).
  pose proof (eight_sqrt1_squares p q r (false, true, false) H3) as Hsq.
  pose proof (eight_sqrt1_mod p q r (false, true, false) H3) as Hx.
  simpl in Hx. destruct Hx as [Hxp [Hxq _]].
  unfold sign_residue in Hxp, Hxq. simpl in Hxp, Hxq.
  rewrite Z.mod_1_l in Hxp by lia.
  rewrite (Z.mod_small (q - 1) q) in Hxq by lia.
  split; [exact Hsq|].
  apply (mixed_triple_splits p q r (eight_sqrt1 p q r (false, true, false))
           H3 Hq2 Hsq Hxp Hxq).
Qed.

(** ** [λ(pqr)] annihilates units; a one-sided period still splits *)

Definition lambda_threeprime (p q r : Z) : Z :=
  Z.lcm (lambda_semiprime p q) (r - 1).

Lemma lambda_threeprime_divides_pminus1 :
  forall p q r, (p - 1 | lambda_threeprime p q r).
Proof.
  intros p q r. unfold lambda_threeprime.
  apply (Z.divide_trans _ (lambda_semiprime p q)).
  - apply lambda_divides_pminus1.
  - apply Z.divide_lcm_l.
Qed.

Lemma lambda_threeprime_divides_qminus1 :
  forall p q r, (q - 1 | lambda_threeprime p q r).
Proof.
  intros p q r. unfold lambda_threeprime.
  apply (Z.divide_trans _ (lambda_semiprime p q)).
  - apply lambda_divides_qminus1.
  - apply Z.divide_lcm_l.
Qed.

Lemma lambda_threeprime_divides_rminus1 :
  forall p q r, (r - 1 | lambda_threeprime p q r).
Proof. intros. unfold lambda_threeprime. apply Z.divide_lcm_r. Qed.

Lemma lambda_threeprime_pos :
  forall p q r,
    Z.prime p -> Z.prime q -> Z.prime r ->
    0 < lambda_threeprime p q r.
Proof.
  intros p q r Hp Hq Hr.
  unfold lambda_threeprime.
  pose proof (lambda_semiprime_pos p q Hp Hq).
  pose proof (Z.prime_ge_2 r Hr).
  pose proof (Z.lcm_nonneg (lambda_semiprime p q) (r - 1)).
  destruct (Z.eq_dec (Z.lcm (lambda_semiprime p q) (r - 1)) 0) as [Hz | Hnz].
  - apply Z.lcm_eq_0 in Hz. lia.
  - lia.
Qed.

Lemma crt_one_three :
  forall p q r a,
    three_prime p q r ->
    a mod p = 1 ->
    a mod q = 1 ->
    a mod r = 1 ->
    a mod (p * q * r) = 1.
Proof.
  intros p q r a H3 Hp1 Hq1 Hr1.
  pose proof (Z.prime_ge_2 p (proj1 H3)).
  pose proof (Z.prime_ge_2 q (proj1 (proj2 H3))).
  pose proof (Z.prime_ge_2 r (proj1 (proj2 (proj2 H3)))).
  transitivity (1 mod (p * q * r)).
  - apply mods_eq_iff_divides; [nia|].
    apply divide_by_coprime_product.
    + apply three_prime_pq_coprime_r; exact H3.
    + apply divide_by_coprime_product.
      * destruct H3 as [Hp [Hq [_ [Hneq _]]]].
        apply prime_coprime_distinct; assumption.
      * apply mods_eq_iff_divides; [lia|].
        rewrite Hp1, Z.mod_1_l by lia. reflexivity.
      * apply mods_eq_iff_divides; [lia|].
        rewrite Hq1, Z.mod_1_l by lia. reflexivity.
    + apply mods_eq_iff_divides; [lia|].
      rewrite Hr1, Z.mod_1_l by lia. reflexivity.
  - apply Z.mod_small; nia.
Qed.

Theorem carmichael_threeprime :
  forall p q r a,
    three_prime p q r ->
    Z.coprime a (p * q * r) ->
    powm a (lambda_threeprime p q r) (p * q * r) = 1.
Proof.
  intros p q r a H3 Hcop.
  destruct H3 as [Hp [Hq [Hr [Hpq [Hpr Hqr]]]]].
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (Z.prime_ge_2 q Hq).
  pose proof (Z.prime_ge_2 r Hr).
  pose proof (lambda_threeprime_pos p q r Hp Hq Hr).
  assert (Z.coprime a p /\ Z.coprime a q /\ Z.coprime a r) as [Hap [Haq Har]].
  { apply coprime_mul_iff in Hcop. destruct Hcop as [Hapq Har].
    apply coprime_mul_iff in Hapq. tauto. }
  assert (0 <= lambda_threeprime p q r) by lia.
  destruct (lambda_threeprime_divides_pminus1 p q r) as [kp Hkp].
  destruct (lambda_threeprime_divides_qminus1 p q r) as [kq Hkq].
  destruct (lambda_threeprime_divides_rminus1 p q r) as [kr Hkr].
  assert (0 <= kp) by nia.
  assert (0 <= kq) by nia.
  assert (0 <= kr) by nia.
  assert (powm a (lambda_threeprime p q r) p = 1) as Hp1.
  { rewrite Hkp, Z.mul_comm.
    rewrite (powm_one_mul a (p - 1) kp p);
      [apply Z.mod_small; lia | lia | lia | lia | apply fermat_coprime; assumption]. }
  assert (powm a (lambda_threeprime p q r) q = 1) as Hq1.
  { rewrite Hkq, Z.mul_comm.
    rewrite (powm_one_mul a (q - 1) kq q);
      [apply Z.mod_small; lia | lia | lia | lia | apply fermat_coprime; assumption]. }
  assert (powm a (lambda_threeprime p q r) r = 1) as Hr1.
  { rewrite Hkr, Z.mul_comm.
    rewrite (powm_one_mul a (r - 1) kr r);
      [apply Z.mod_small; lia | lia | lia | lia | apply fermat_coprime; assumption]. }
  unfold powm in Hp1, Hq1, Hr1 |- *.
  apply crt_one_three.
  - unfold three_prime. tauto.
  - exact Hp1.
  - exact Hq1.
  - exact Hr1.
Qed.

Theorem onesided_period_splits_triple :
  forall p q r a M,
    three_prime p q r ->
    0 <= M ->
    powm a M p = 1 ->
    powm a M (p * q * r) <> 1 ->
    let g := Z.gcd (powm a M (p * q * r) - 1) (p * q * r) in
    1 < g /\ g < p * q * r /\ (g | p * q * r).
Proof.
  intros p q r a M Ht HM Hp1 Hneq g.
  pose proof (Z.prime_ge_2 p (proj1 Ht)).
  pose proof (Z.prime_ge_2 q (proj1 (proj2 Ht))).
  pose proof (Z.prime_ge_2 r (proj1 (proj2 (proj2 Ht)))).
  set (N := p * q * r).
  set (y := powm a M N).
  assert (1 < N) by (unfold N; nia).
  assert (p | y - 1) as Hpy.
  { unfold y.
    assert (powm a M p = (powm a M N) mod p) as Hred.
    { unfold powm, N.
      replace (p * q * r) with (p * (q * r)) by ring.
      symmetry. apply mod_mod_product; nia. }
    rewrite Hp1 in Hred.
    apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, <- Hred, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity. }
  unfold g, y, N.
  pose proof (Z.gcd_nonneg (powm a M (p * q * r) - 1) (p * q * r)) as Hgnn.
  pose proof (Z.gcd_divide_r (powm a M (p * q * r) - 1) (p * q * r)) as HgN.
  split; [| split].
  - destruct (Z.le_gt_cases (Z.gcd (powm a M (p * q * r) - 1) (p * q * r)) 1)
      as [Hle | Hgt]; [| exact Hgt].
    assert (Z.gcd (powm a M (p * q * r) - 1) (p * q * r) <> 0) as Hgnz.
    { intro Hz. apply Z.gcd_eq_0 in Hz. nia. }
    assert (Z.gcd (powm a M (p * q * r) - 1) (p * q * r) = 1) as Hg1 by lia.
    assert (p | Z.gcd (powm a M (p * q * r) - 1) (p * q * r)) as Hpg.
    { apply Z.gcd_greatest; [exact Hpy |].
      exists (q * r). ring. }
    rewrite Hg1 in Hpg. apply Z.divide_1_r in Hpg. lia.
  - destruct (Z.lt_ge_cases (Z.gcd (powm a M (p * q * r) - 1) (p * q * r))
                            (p * q * r)) as [Hlt | Hge]; [exact Hlt|].
    assert (Z.gcd (powm a M (p * q * r) - 1) (p * q * r) = p * q * r)
      as Hgeq.
    { pose proof (Z.divide_pos_le
                    (Z.gcd (powm a M (p * q * r) - 1) (p * q * r))
                    (p * q * r) ltac:(nia) HgN). lia. }
    assert (p * q * r | powm a M (p * q * r) - 1) as HdivN.
    { pose proof (Z.gcd_divide_l (powm a M (p * q * r) - 1) (p * q * r))
        as Hgx.
      rewrite Hgeq in Hgx. exact Hgx. }
    apply mods_eq_iff_divides in HdivN; [| nia].
    unfold powm in HdivN, Hneq.
    rewrite Z.mod_mod in HdivN by nia.
    rewrite Z.mod_1_l in HdivN by nia.
    contradiction.
  - exact HgN.
Qed.
