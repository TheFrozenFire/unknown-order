From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import Zmod.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import MultiPrime.
Require Import Wiener.
Require Import KeyGen.
Require Import KeyGenCtor.

Open Scope Z_scope.

(** * Shared RSA key from two KeyGen-valid parts

    Alice holds [R_A], Bob holds [R_B], same public [e],
    [gcd(N_A, N_B) = 1].  Shared modulus [N* = N_A N_B].
    Local inverses of [e] CRT-combine to [d*] modulo
    [λ* = lcm(λ_A, λ_B)].  Garner of the two local decryptions
    is global decryption.  Neither party publishes [λ] or [d].

    Multiplying a *single* extra prime onto [N_A] hands that prime
    to Alice ([N*/N_A]).  A triplet is the same theorem at arity 3.

    Cross-confirmed by [cas/78_shared_lambda.gp],
    [cas/79_shared_decrypt.gp], [cas/80_shared_keygen.gp]. *)

Definition shared_N (RA RB : RSAInstance) : Z :=
  rsa_N RA * rsa_N RB.

Definition lambda_product (RA RB : RSAInstance) : Z :=
  Z.lcm (rsa_lambda RA) (rsa_lambda RB).

Definition shared_dec (RA RB : RSAInstance) (c : Z) : Z :=
  Z.combinecong (rsa_N RA) (rsa_N RB) (rsa_dec RA c) (rsa_dec RB c).

Definition d_star_spec (RA RB : RSAInstance) (dstar : Z) : Prop :=
  dstar mod rsa_lambda RA = rsa_d RA mod rsa_lambda RA /\
  dstar mod rsa_lambda RB = rsa_d RB mod rsa_lambda RB.

(** ** Layer 1 — Carmichael of a coprime product *)

Lemma lambda_A_divides_product :
  forall RA RB, (rsa_lambda RA | lambda_product RA RB).
Proof. intros. unfold lambda_product. apply Z.divide_lcm_l. Qed.

Lemma lambda_B_divides_product :
  forall RA RB, (rsa_lambda RB | lambda_product RA RB).
Proof. intros. unfold lambda_product. apply Z.divide_lcm_r. Qed.

Lemma lambda_product_pos :
  forall RA RB, 0 < lambda_product RA RB.
Proof.
  intros RA RB.
  unfold lambda_product.
  pose proof (rsa_lambda_pos RA).
  pose proof (rsa_lambda_pos RB).
  pose proof (Z.lcm_nonneg (rsa_lambda RA) (rsa_lambda RB)).
  destruct (Z.eq_dec (Z.lcm (rsa_lambda RA) (rsa_lambda RB)) 0) as [Hz | Hnz].
  - apply Z.lcm_eq_0 in Hz. lia.
  - lia.
Qed.

Lemma lambda_product_gt_1 :
  forall RA RB, 1 < lambda_product RA RB.
Proof.
  intros RA RB.
  pose proof (rsa_lambda_gt_1 RA).
  pose proof (Z.divide_pos_le (rsa_lambda RA) (lambda_product RA RB)
                (lambda_product_pos RA RB) (lambda_A_divides_product RA RB)).
  lia.
Qed.

Lemma coprime_product_split :
  forall a n m,
    Z.coprime a (n * m) ->
    Z.coprime a n /\ Z.coprime a m.
Proof. intros a n m H. apply coprime_mul_iff. exact H. Qed.

Lemma crt_mod_eq_coprime :
  forall a b n m,
    1 < n ->
    1 < m ->
    Z.gcd n m = 1 ->
    a mod n = b mod n ->
    a mod m = b mod m ->
    a mod (n * m) = b mod (n * m).
Proof.
  intros a b n m Hn Hm Hg Hn1 Hm1.
  apply mods_eq_iff_divides; [nia|].
  apply divide_by_coprime_product.
  - unfold Z.coprime. exact Hg.
  - apply mods_eq_iff_divides; [lia | exact Hn1].
  - apply mods_eq_iff_divides; [lia | exact Hm1].
Qed.

Lemma crt_one_coprime_moduli :
  forall n m a,
    1 < n ->
    1 < m ->
    Z.gcd n m = 1 ->
    a mod n = 1 ->
    a mod m = 1 ->
    a mod (n * m) = 1.
Proof.
  intros n m a Hn Hm Hg Hn1 Hm1.
  transitivity (1 mod (n * m)).
  - apply mods_eq_iff_divides; [nia|].
    apply divide_by_coprime_product.
    + unfold Z.coprime. exact Hg.
    + apply mods_eq_iff_divides; [lia|].
      rewrite Hn1, Z.mod_1_l by lia. reflexivity.
    + apply mods_eq_iff_divides; [lia|].
      rewrite Hm1, Z.mod_1_l by lia. reflexivity.
  - apply Z.mod_small; nia.
Qed.

Theorem carmichael_shared :
  forall RA RB a,
    Z.gcd (rsa_N RA) (rsa_N RB) = 1 ->
    Z.coprime a (shared_N RA RB) ->
    powm a (lambda_product RA RB) (shared_N RA RB) = 1.
Proof.
  intros RA RB a Hg Hcop.
  pose proof (rsa_N_gt_1 RA).
  pose proof (rsa_N_gt_1 RB).
  pose proof (lambda_product_pos RA RB).
  destruct (coprime_product_split a (rsa_N RA) (rsa_N RB) Hcop) as [HaA HaB].
  assert (powm a (lambda_product RA RB) (rsa_N RA) = 1) as HA.
  { unfold rsa_N.
    apply (annihilates_units (rsa_p RA) (rsa_q RA) a (lambda_product RA RB));
      [apply rsa_p_prime | apply rsa_q_prime | apply rsa_distinct
      | exact HaA | lia | apply lambda_A_divides_product]. }
  assert (powm a (lambda_product RA RB) (rsa_N RB) = 1) as HB.
  { unfold rsa_N.
    apply (annihilates_units (rsa_p RB) (rsa_q RB) a (lambda_product RA RB));
      [apply rsa_p_prime | apply rsa_q_prime | apply rsa_distinct
      | exact HaB | lia | apply lambda_B_divides_product]. }
  unfold shared_N, powm in HA, HB |- *.
  apply crt_one_coprime_moduli; [lia | lia | exact Hg | exact HA | exact HB].
Qed.

(** ** Layer 2 — CRT of inverses of a common [e] *)

Lemma gcd_of_divisor :
  forall e l g,
    Z.gcd e l = 1 ->
    (g | l) ->
    Z.gcd e g = 1.
Proof.
  intros e l g He Hgl.
  pose proof (Z.gcd_divide_l e g) as H1.
  pose proof (Z.gcd_divide_r e g) as H2.
  assert (Z.gcd e g | l) as H3.
  { eapply Z.divide_trans; [exact H2 | exact Hgl]. }
  assert (Z.gcd e g | Z.gcd e l) as H4.
  { apply Z.gcd_greatest; [exact H1 | exact H3]. }
  rewrite He in H4.
  apply Z.divide_1_r in H4.
  pose proof (Z.gcd_nonneg e g). lia.
Qed.

Lemma inverses_agree_mod_gcd :
  forall e dA dB lA lB,
    1 < lA ->
    1 < lB ->
    (e * dA) mod lA = 1 ->
    (e * dB) mod lB = 1 ->
    Z.gcd e lA = 1 ->
    (Z.gcd lA lB | dA - dB).
Proof.
  intros e dA dB lA lB HlA HlB HA HB HeA.
  set (g := Z.gcd lA lB).
  assert (g | e * dA - 1) as HgA.
  { apply (Z.divide_trans g lA).
    - apply Z.gcd_divide_l.
    - apply mods_eq_iff_divides; [lia|].
      rewrite HA, Z.mod_1_l by lia. reflexivity. }
  assert (g | e * dB - 1) as HgB.
  { apply (Z.divide_trans g lB).
    - apply Z.gcd_divide_r.
    - apply mods_eq_iff_divides; [lia|].
      rewrite HB, Z.mod_1_l by lia. reflexivity. }
  assert (g | e * (dA - dB)) as Hge.
  { replace (e * (dA - dB)) with ((e * dA - 1) - (e * dB - 1)) by ring.
    apply Z.divide_sub_r; assumption. }
  assert (Z.gcd g e = 1) as Hge1.
  { rewrite Z.gcd_comm. apply (gcd_of_divisor e lA g).
    - exact HeA.
    - apply Z.gcd_divide_l. }
  apply (Z.gauss g e (dA - dB)); [exact Hge | exact Hge1].
Qed.

Lemma rsa_e_gcd_lambda :
  forall R, Z.gcd (rsa_e R) (rsa_lambda R) = 1.
Proof. intros R. apply rsa_e_coprime. Qed.

Lemma crt_exists_gcd :
  forall m n a b,
    1 < m ->
    1 < n ->
    (Z.gcd m n | a - b) ->
    exists x, x mod m = a mod m /\ x mod n = b mod n.
Proof.
  intros m n a b Hm Hn Hdiv.
  set (g := Z.gcd m n).
  assert (0 < g) as Hgpos.
  { pose proof (Z.gcd_nonneg m n).
    destruct (Z.eq_dec g 0) as [Hz | Hnz]; [| lia].
    apply Z.gcd_eq_0 in Hz. lia. }
  assert (g <> 0) as Hgnz by lia.
  pose proof (Z.gcd_div_gcd m n g Hgnz eq_refl) as Hg1.
  assert (g | b - a) as Hdiv'.
  { apply Z.divide_opp_r. replace (- (b - a)) with (a - b) by ring.
    exact Hdiv. }
  assert (b - a = g * ((b - a) / g)) as Hsplit.
  { apply Z.div_exact; [exact Hgnz|].
    apply Z.mod_divide; [exact Hgnz | exact Hdiv']. }
  destruct (Z.gcd_bezout (m / g) (n / g) 1 Hg1) as [s [t Hs]].
  set (q := (b - a) / g).
  exists (a + m * (q * s)).
  split.
  - rewrite (Z.mul_comm m). rewrite Z.mod_add by lia. reflexivity.
  - apply mods_eq_iff_divides; [lia|].
    exists (- t * q).
    assert (m = g * (m / g)) as Hmdef.
    { apply Z.div_exact; [exact Hgnz|].
      apply Z.mod_divide; [exact Hgnz | apply Z.gcd_divide_l]. }
    assert (n = g * (n / g)) as Hndef.
    { apply Z.div_exact; [exact Hgnz|].
      apply Z.mod_divide; [exact Hgnz | apply Z.gcd_divide_r]. }
    rewrite Hmdef, Hndef.
    replace (a + g * (m / g) * (q * s) - b)
      with (g * q * (m / g * s - 1)).
    2:{
      assert (b - a = g * q) as Habq by (unfold q; exact Hsplit).
      replace (g * q * (m / g * s - 1))
        with (g * (m / g) * (q * s) - g * q) by ring.
      rewrite <- Habq. ring.
    }
    replace (m / g * s - 1) with (- t * (n / g)) by lia.
    ring.
Qed.

Theorem d_star_exists :
  forall RA RB,
    rsa_e RA = rsa_e RB ->
    exists dstar, d_star_spec RA RB dstar.
Proof.
  intros RA RB He.
  unfold d_star_spec.
  pose proof (rsa_lambda_gt_1 RA) as HlA.
  pose proof (rsa_lambda_gt_1 RB) as HlB.
  assert (Z.gcd (rsa_lambda RA) (rsa_lambda RB) | rsa_d RA - rsa_d RB)
    as Hdiv.
  { apply (inverses_agree_mod_gcd (rsa_e RA) (rsa_d RA) (rsa_d RB)
             (rsa_lambda RA) (rsa_lambda RB));
      [lia | lia | apply rsa_d_inv | rewrite He; apply rsa_d_inv
      | apply rsa_e_gcd_lambda]. }
  destruct (crt_exists_gcd (rsa_lambda RA) (rsa_lambda RB)
              (rsa_d RA) (rsa_d RB) HlA HlB Hdiv) as [x Hx].
  exists x. exact Hx.
Qed.

Theorem d_star_exists_nonneg :
  forall RA RB,
    rsa_e RA = rsa_e RB ->
    exists dstar, 0 <= dstar /\ d_star_spec RA RB dstar.
Proof.
  intros RA RB He.
  destruct (d_star_exists RA RB He) as [x [HxA HxB]].
  pose proof (lambda_product_pos RA RB) as Hlp.
  exists (x + Z.abs x * lambda_product RA RB).
  split; [nia|].
  unfold d_star_spec.
  pose proof (rsa_lambda_gt_1 RA) as HlA.
  pose proof (rsa_lambda_gt_1 RB) as HlB.
  destruct (lambda_A_divides_product RA RB) as [kA HkA].
  destruct (lambda_B_divides_product RA RB) as [kB HkB].
  split.
  - rewrite HkA.
    replace (x + Z.abs x * (kA * rsa_lambda RA))
      with (x + (Z.abs x * kA) * rsa_lambda RA) by ring.
    rewrite Z.mod_add by lia.
    exact HxA.
  - rewrite HkB.
    replace (x + Z.abs x * (kB * rsa_lambda RB))
      with (x + (Z.abs x * kB) * rsa_lambda RB) by ring.
    rewrite Z.mod_add by lia.
    exact HxB.
Qed.

Theorem d_star_inverts :
  forall RA RB dstar,
    rsa_e RA = rsa_e RB ->
    d_star_spec RA RB dstar ->
    (rsa_e RA * dstar) mod lambda_product RA RB = 1.
Proof.
  intros RA RB dstar He [HA HB].
  pose proof (lambda_product_gt_1 RA RB).
  pose proof (rsa_lambda_gt_1 RA).
  pose proof (rsa_lambda_gt_1 RB).
  assert (rsa_lambda RA | rsa_e RA * dstar - 1) as HdA.
  { apply mods_eq_iff_divides; [lia|].
    rewrite Z.mul_mod, HA, <- Z.mul_mod by lia.
    rewrite rsa_d_inv, Z.mod_1_l by lia. reflexivity. }
  assert (rsa_lambda RB | rsa_e RA * dstar - 1) as HdB.
  { apply mods_eq_iff_divides; [lia|].
    rewrite Z.mul_mod, HB, <- Z.mul_mod by lia.
    rewrite He, rsa_d_inv, Z.mod_1_l by lia. reflexivity. }
  transitivity (1 mod lambda_product RA RB);
    [| apply Z.mod_small; lia].
  apply (proj2 (mods_eq_iff_divides (rsa_e RA * dstar) 1
                   (lambda_product RA RB) ltac:(lia))).
  unfold lambda_product.
  apply Z.lcm_least; [exact HdA | exact HdB].
Qed.

(** ** Layer 3 — local decrypt + CRT = global [c^{d*}] *)

Lemma powm_mod_lambda :
  forall R c d,
    Z.coprime c (rsa_N R) ->
    0 <= d ->
    powm c d (rsa_N R) = powm c (d mod rsa_lambda R) (rsa_N R).
Proof.
  intros R c d Hcop Hd.
  pose proof (rsa_lambda_gt_1 R).
  pose proof (rsa_N_gt_1 R).
  pose proof (Z.div_mod d (rsa_lambda R) ltac:(lia)) as Hdm.
  rewrite Hdm at 1.
  assert (0 <= d mod rsa_lambda R) by (apply Z.mod_pos_bound; lia).
  assert (0 <= d / rsa_lambda R) by (apply Z.div_pos; lia).
  rewrite powm_add_r by nia.
  rewrite (powm_mul_r c (rsa_lambda R) (d / rsa_lambda R) (rsa_N R))
    by nia.
  unfold rsa_N, rsa_lambda.
  rewrite (carmichael_semiprime (rsa_p R) (rsa_q R) c
             (rsa_p_prime R) (rsa_q_prime R) (rsa_distinct R) Hcop).
  fold (rsa_lambda R).
  assert (rsa_p R * rsa_q R <> 0) by (unfold rsa_N in *; nia).
  rewrite (powm_1_pow (d / rsa_lambda R) (rsa_p R * rsa_q R)) by lia.
  fold (rsa_N R).
  rewrite Z.mod_1_l by lia.
  rewrite Z.mul_1_l.
  unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma shared_dec_mod_A :
  forall RA RB c,
    Z.gcd (rsa_N RA) (rsa_N RB) = 1 ->
    shared_dec RA RB c mod rsa_N RA = rsa_dec RA c mod rsa_N RA.
Proof.
  intros RA RB c Hg.
  unfold shared_dec.
  pose proof (rsa_N_gt_1 RA).
  pose proof (rsa_N_gt_1 RB).
  pose proof (Z.combinecong_sound_coprime (rsa_N RA) (rsa_N RB)
                (rsa_dec RA c) (rsa_dec RB c) Hg) as [HA _].
  exact HA.
Qed.

Lemma shared_dec_mod_B :
  forall RA RB c,
    Z.gcd (rsa_N RA) (rsa_N RB) = 1 ->
    shared_dec RA RB c mod rsa_N RB = rsa_dec RB c mod rsa_N RB.
Proof.
  intros RA RB c Hg.
  unfold shared_dec.
  pose proof (Z.combinecong_sound_coprime (rsa_N RA) (rsa_N RB)
                (rsa_dec RA c) (rsa_dec RB c) Hg) as [_ HB].
  exact HB.
Qed.

Theorem shared_dec_eq_powm :
  forall RA RB c dstar,
    rsa_e RA = rsa_e RB ->
    Z.gcd (rsa_N RA) (rsa_N RB) = 1 ->
    Z.coprime c (shared_N RA RB) ->
    0 <= dstar ->
    d_star_spec RA RB dstar ->
    shared_dec RA RB c mod shared_N RA RB =
      powm c dstar (shared_N RA RB).
Proof.
  intros RA RB c dstar He Hg Hcop Hd Hspec.
  pose proof (rsa_N_gt_1 RA).
  pose proof (rsa_N_gt_1 RB).
  destruct (coprime_product_split c (rsa_N RA) (rsa_N RB) Hcop) as [HcA HcB].
  destruct Hspec as [HsA HsB].
  assert (powm c dstar (rsa_N RA) = rsa_dec RA c) as HredA.
  { unfold rsa_dec.
    rewrite (powm_mod_lambda RA c dstar HcA Hd).
    rewrite HsA. symmetry.
    apply powm_mod_lambda; [exact HcA | pose proof (rsa_d_pos RA); lia]. }
  assert (powm c dstar (rsa_N RB) = rsa_dec RB c) as HredB.
  { unfold rsa_dec.
    rewrite (powm_mod_lambda RB c dstar HcB Hd).
    rewrite HsB. symmetry.
    apply powm_mod_lambda; [exact HcB | pose proof (rsa_d_pos RB); lia]. }
  unfold shared_N.
  transitivity (powm c dstar (rsa_N RA * rsa_N RB)
                  mod (rsa_N RA * rsa_N RB));
    [| unfold powm; rewrite Z.mod_mod by nia; reflexivity].
  apply (crt_mod_eq_coprime (shared_dec RA RB c)
           (powm c dstar (rsa_N RA * rsa_N RB))
           (rsa_N RA) (rsa_N RB));
    [lia | lia | exact Hg | |].
  - rewrite shared_dec_mod_A by exact Hg.
    rewrite <- HredA. unfold powm.
    rewrite Z.mod_mod by lia. symmetry.
    apply Z.mod_mod_divide. exists (rsa_N RB). ring.
  - rewrite shared_dec_mod_B by exact Hg.
    rewrite <- HredB. unfold powm.
    rewrite Z.mod_mod by lia. symmetry.
    apply Z.mod_mod_divide. exists (rsa_N RA). ring.
Qed.

(** ** Layer 4 — one local [d] does not determine [d*] *)

Lemma prime_5 : Z.prime 5.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
  intuition subst; reflexivity.
Qed.

Lemma prime_23 : Z.prime 23.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/
          n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
          n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/
          n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/
          n = 21 \/ n = 22) by lia.
  intuition subst; reflexivity.
Qed.

Lemma prime_41 : Z.prime 41.
Proof.
  apply prime_alt. apply prime_intro; [lia|].
  intros n Hn. apply rel_prime_iff_coprime. unfold Z.coprime.
  assert (1 <= n <= 40) by lia.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/
          n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
          n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/
          n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/
          n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/
          n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/
          n = 31 \/ n = 32 \/ n = 33 \/ n = 34 \/ n = 35 \/
          n = 36 \/ n = 37 \/ n = 38 \/ n = 39 \/ n = 40) by lia.
  intuition subst; reflexivity.
Qed.

Definition rsa_5_23 : RSAInstance.
Proof.
  refine {|
    rsa_p := 5; rsa_q := 23; rsa_e := 3; rsa_d := 15;
    rsa_p_prime := prime_5; rsa_q_prime := prime_23;
    rsa_distinct := ltac:(discriminate);
    rsa_e_coprime := ltac:(unfold Z.coprime, lambda_semiprime; vm_compute; reflexivity);
    rsa_d_inv := ltac:(vm_compute; reflexivity);
    rsa_d_pos := ltac:(lia); rsa_e_pos := ltac:(lia)
  |}.
Defined.

Definition rsa_5_41 : RSAInstance.
Proof.
  refine {|
    rsa_p := 5; rsa_q := 41; rsa_e := 3; rsa_d := 27;
    rsa_p_prime := prime_5; rsa_q_prime := prime_41;
    rsa_distinct := ltac:(discriminate);
    rsa_e_coprime := ltac:(unfold Z.coprime, lambda_semiprime; vm_compute; reflexivity);
    rsa_d_inv := ltac:(vm_compute; reflexivity);
    rsa_d_pos := ltac:(lia); rsa_e_pos := ltac:(lia)
  |}.
Defined.

Theorem rsa_5_23_N : rsa_N rsa_5_23 = 115.
Proof. reflexivity. Qed.

Theorem rsa_5_41_N : rsa_N rsa_5_41 = 205.
Proof. reflexivity. Qed.

Theorem d_star_depends_on_both :
  rsa_e rsa_test = rsa_e rsa_5_23 /\
  rsa_e rsa_test = rsa_e rsa_5_41 /\
  Z.gcd (rsa_N rsa_test) (rsa_N rsa_5_23) = 1 /\
  Z.gcd (rsa_N rsa_test) (rsa_N rsa_5_41) = 1 /\
  rsa_d rsa_5_23 <> rsa_d rsa_5_41.
Proof.
  repeat split; vm_compute; try reflexivity; discriminate.
Qed.

Theorem two_partners_two_dstars :
  forall d1 d2,
    d_star_spec rsa_test rsa_5_23 d1 ->
    d_star_spec rsa_test rsa_5_41 d2 ->
    d1 mod 80 = 27 /\
    d2 mod 80 = 27 /\
    d1 mod 44 = 15 /\
    d2 mod 40 = 27.
Proof.
  intros d1 d2 [H1A H1B] [H2A H2B].
  unfold rsa_lambda, lambda_semiprime, rsa_d in *.
  cbn in *.
  repeat split; assumption.
Qed.

(** ** Layer 5 — lifted KeyGen spec *)

Definition satisfies_keygen_product (S : KeyGenSpec) (RA RB : RSAInstance) : Prop :=
  satisfies_keygen_full S RA /\
  satisfies_keygen_full S RB /\
  rsa_e RA = rsa_e RB /\
  Z.gcd (rsa_N RA) (rsa_N RB) = 1.

Theorem product_carries_component_keygen :
  forall S RA RB,
    satisfies_keygen_product S RA RB ->
    satisfies_keygen_full S RA /\ satisfies_keygen_full S RB.
Proof. intros S RA RB [HA [HB _]]. split; assumption. Qed.

Theorem product_common_e_inverts :
  forall S RA RB dstar,
    satisfies_keygen_product S RA RB ->
    d_star_spec RA RB dstar ->
    (rsa_e RA * dstar) mod lambda_product RA RB = 1.
Proof.
  intros S RA RB dstar [HA [HB [He _]]] Hspec.
  apply d_star_inverts; assumption.
Qed.

Theorem product_refuses_shared_prime :
  forall S RA RB,
    satisfies_keygen_product S RA RB ->
    Z.gcd (rsa_N RA) (rsa_N RB) = 1.
Proof. intros S RA RB H. apply H. Qed.

Theorem d_star_gt_lambda_div_e :
  forall e d lam,
    1 < e ->
    1 < lam ->
    0 < d ->
    d < lam ->
    (e * d) mod lam = 1 ->
    (1 + lam) / e <= d.
Proof.
  intros e d lam He Hl Hd Hdl Hinv.
  assert (lam | e * d - 1) as Hdiv.
  { apply mods_eq_iff_divides; [lia|].
    rewrite Hinv, Z.mod_1_l by lia. reflexivity. }
  destruct Hdiv as [k Hk].
  assert (1 <= k) as Hk1.
  { destruct (Z.le_gt_cases k 0) as [Hkn | Hkp].
    - assert (e * d - 1 <= 0) by nia. nia.
    - lia. }
  assert (e * d = 1 + k * lam) by lia.
  assert (1 + lam <= e * d) by nia.
  assert ((1 + lam) / e <= (e * d) / e).
  { apply Z.div_le_mono; lia. }
  rewrite (Z.mul_comm e d), Z.div_mul in H1 by lia.
  exact H1.
Qed.

(** ** Layer 6 — arity 3 *)

Definition shared_N3 (RA RB RC : RSAInstance) : Z :=
  rsa_N RA * rsa_N RB * rsa_N RC.

Definition lambda_product3 (RA RB RC : RSAInstance) : Z :=
  Z.lcm (lambda_product RA RB) (rsa_lambda RC).

Definition shared_dec3 (RA RB RC : RSAInstance) (c : Z) : Z :=
  Z.combinecong (rsa_N RA * rsa_N RB) (rsa_N RC)
    (shared_dec RA RB c) (rsa_dec RC c).

Theorem carmichael_shared3 :
  forall RA RB RC a,
    Z.gcd (rsa_N RA) (rsa_N RB) = 1 ->
    Z.gcd (rsa_N RA * rsa_N RB) (rsa_N RC) = 1 ->
    Z.coprime a (shared_N3 RA RB RC) ->
    powm a (lambda_product3 RA RB RC) (shared_N3 RA RB RC) = 1.
Proof.
  intros RA RB RC a HgAB HgC Hcop.
  pose proof (rsa_N_gt_1 RA) as HnA.
  pose proof (rsa_N_gt_1 RB) as HnB.
  pose proof (rsa_N_gt_1 RC) as HnC.
  pose proof (lambda_product_pos RA RB) as HlpAB.
  pose proof (rsa_lambda_pos RC) as HlC.
  assert (0 < lambda_product3 RA RB RC) as Hlp.
  { unfold lambda_product3.
    pose proof (Z.lcm_nonneg (lambda_product RA RB) (rsa_lambda RC)).
    destruct (Z.eq_dec (Z.lcm (lambda_product RA RB) (rsa_lambda RC)) 0)
      as [Hz | Hnz]; [apply Z.lcm_eq_0 in Hz; lia | lia]. }
  unfold shared_N3 in Hcop.
  apply coprime_mul_iff in Hcop. destruct Hcop as [HcopAB HcopC].
  assert (powm a (lambda_product3 RA RB RC) (rsa_N RA * rsa_N RB) = 1)
    as HAB.
  { unfold lambda_product3.
    pose proof (carmichael_shared RA RB a HgAB HcopAB) as Hsh.
    destruct (Z.divide_lcm_l (lambda_product RA RB) (rsa_lambda RC))
      as [k Hk].
    assert (0 <= k).
    { pose proof (Z.lcm_nonneg (lambda_product RA RB) (rsa_lambda RC)).
      nia. }
    rewrite Hk, Z.mul_comm.
    rewrite (powm_one_mul a (lambda_product RA RB) k (rsa_N RA * rsa_N RB));
      [apply Z.mod_small; nia | nia | nia | nia | exact Hsh]. }
  assert (powm a (lambda_product3 RA RB RC) (rsa_N RC) = 1) as HC.
  { unfold lambda_product3, rsa_N.
    apply (annihilates_units (rsa_p RC) (rsa_q RC) a (lambda_product3 RA RB RC));
      [apply rsa_p_prime | apply rsa_q_prime | apply rsa_distinct
      | exact HcopC | lia |].
    unfold lambda_product3. apply Z.divide_lcm_r. }
  unfold shared_N3, powm in HAB, HC |- *.
  apply crt_one_coprime_moduli; [nia | lia | exact HgC | exact HAB | exact HC].
Qed.
