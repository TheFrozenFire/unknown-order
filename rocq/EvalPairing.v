From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import UnknownOrder.
Require Import Order.
Require Import CubicResidue.
Require Import TwoPrimary.

Open Scope Z_scope.

(** * Evaluation pairing on [μ_n]: [e(x,k) = x^k]

    If [x^n ≡ 1] then [x^k] stays in [μ_n] and depends on [k]
    only modulo [n].  The target has order dividing [n].  For
    [n ∈ {2,3,4,6}] that is at most six elements.  One argument
    is an integer, so this is RSA-shaped exponentiation, not a
    pairing of two hidden discrete logs.

    An alternating bilinear map on cyclic [μ₃ ⊂ 𝔽_p*] is the
    constant-[1] pairing ([alternating_bilinear_mu3_trivial],
    [cas/157]).  A non-degenerate pairing of two hidden [μ₃]
    elements needs an extension field / curve, which stays
    [Refuse_elliptic_curve_branch].

    Cross-confirmed by [cas/87_eval_pairing.gp] and
    [cas/157_mu3_pairing.gp]. *)

Definition mu (n x N : Z) : Prop :=
  powm x n N = 1.

Definition eval_pair (x k N : Z) : Z :=
  powm x k N.

Theorem eval_pair_stays_in_mu :
  forall n x k N,
    1 < N ->
    0 <= k ->
    0 <= n ->
    mu n x N ->
    mu n (eval_pair x k N) N.
Proof.
  intros n x k N Hn Hk Hnn Hmu.
  unfold mu, eval_pair in *.
  rewrite <- powm_mul_r by lia.
  rewrite (Z.mul_comm k), powm_mul_r by lia.
  rewrite Hmu.
  rewrite powm_1_pow by lia.
  apply Z.mod_1_l; lia.
Qed.

Theorem eval_pair_add :
  forall x a b N,
    1 < N ->
    0 <= a ->
    0 <= b ->
    eval_pair x (a + b) N =
      (eval_pair x a N * eval_pair x b N) mod N.
Proof.
  intros x a b N Hn Ha Hb.
  unfold eval_pair.
  apply powm_add_r; lia.
Qed.

Theorem eval_pair_mul_base :
  forall x y k N,
    1 < N ->
    0 <= k ->
    eval_pair ((x * y) mod N) k N =
      (eval_pair x k N * eval_pair y k N) mod N.
Proof.
  intros x y k N Hn Hk.
  unfold eval_pair.
  rewrite powm_mod_base by lia.
  unfold powm.
  rewrite Z.pow_mul_l.
  apply Z.mul_mod; lia.
Qed.

Theorem eval_pair_reduce_mod_n :
  forall n x k N,
    1 < N ->
    0 < n ->
    0 <= k ->
    mu n x N ->
    eval_pair x k N = eval_pair x (k mod n) N.
Proof.
  intros n x k N Hn Hnn Hk Hmu.
  unfold eval_pair, mu in *.
  assert (0 <= k / n) by (apply Z.div_pos; lia).
  assert (0 <= k mod n) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod k n ltac:(lia)) as Hdm.
  rewrite Hdm at 1.
  rewrite powm_add_r by nia.
  rewrite powm_mul_r by nia.
  rewrite Hmu.
  rewrite powm_1_pow by nia.
  rewrite Z.mod_1_l by lia.
  rewrite Z.mul_1_l.
  unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem eval_pair_image_divides_n :
  forall n x k N,
    1 < N ->
    0 <= k ->
    0 <= n ->
    mu n x N ->
    powm (eval_pair x k N) n N = 1.
Proof. apply eval_pair_stays_in_mu. Qed.

(** [n = 2]: the four square roots of 1.  [x^k] is [1] or [x]. *)
Theorem eval_pair_mu2 :
  forall p q x k,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    0 <= k ->
    powm x 2 (p * q) = 1 ->
    eval_pair x k (p * q) = eval_pair x (k mod 2) (p * q).
Proof.
  intros p q x k Hp Hq Hneq Hk Hx.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  apply eval_pair_reduce_mod_n; try lia.
  exact Hx.
Qed.

Theorem eval_pair_mu2_on_mixed :
  forall p q k,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    0 <= k ->
    eval_pair (sqrt1_pm p q) k (p * q) =
      eval_pair (sqrt1_pm p q) (k mod 2) (p * q).
Proof.
  intros p q k Hp Hq Hneq Hk.
  pose proof (four_sqrt1 p q Hp Hq Hneq) as [_ [_ [Hsq _]]].
  apply eval_pair_mu2; assumption.
Qed.

(** [n = 3]: a root of [X² + X + 1] is a primitive cube root of 1. *)
Theorem omega_cube_is_one :
  forall omega N,
    1 < N ->
    (omega * omega + omega + 1) mod N = 0 ->
    mu 3 omega N.
Proof.
  intros omega N Hn Hpoly.
  unfold mu, powm.
  change 3 with (Z.succ 2).
  rewrite Z.pow_succ_r, Z.pow_2_r by lia.
  rewrite <- (Z.mod_1_l N) by lia.
  apply mods_eq_iff_divides; [lia|].
  apply Z.mod_divide in Hpoly; [| lia].
  destruct Hpoly as [t Ht].
  exists ((omega - 1) * t).
  replace (omega * (omega * omega) - 1)
    with ((omega - 1) * (omega * omega + omega + 1)) by ring.
  rewrite Ht. ring.
Qed.

Theorem eval_pair_mu3 :
  forall omega k N,
    1 < N ->
    0 <= k ->
    (omega * omega + omega + 1) mod N = 0 ->
    eval_pair omega k N = eval_pair omega (k mod 3) N.
Proof.
  intros omega k N Hn Hk Hpoly.
  apply eval_pair_reduce_mod_n; try lia.
  apply omega_cube_is_one; assumption.
Qed.

(** [n = 6]: [x^6 = (x^2)^3 = (x^3)^2], so [μ_2 ∪ μ_3 ⊂ μ_6]. *)
Theorem mu2_is_mu6 :
  forall x N,
    1 < N ->
    mu 2 x N ->
    mu 6 x N.
Proof.
  intros x N Hn H2.
  unfold mu in *.
  change 6 with (2 * 3).
  rewrite powm_mul_r by lia.
  rewrite H2.
  rewrite powm_1_pow by lia.
  apply Z.mod_1_l; lia.
Qed.

Theorem mu3_is_mu6 :
  forall x N,
    1 < N ->
    mu 3 x N ->
    mu 6 x N.
Proof.
  intros x N Hn H3.
  unfold mu in *.
  change 6 with (3 * 2).
  rewrite powm_mul_r by lia.
  rewrite H3.
  rewrite powm_1_pow by lia.
  apply Z.mod_1_l; lia.
Qed.

Theorem eval_pair_mu6 :
  forall x k N,
    1 < N ->
    0 <= k ->
    mu 6 x N ->
    eval_pair x k N = eval_pair x (k mod 6) N.
Proof.
  intros x k N Hn Hk H6.
  apply eval_pair_reduce_mod_n; try lia.
  exact H6.
Qed.

(** The integer argument is in the clear.  This pairing cannot
    take two CRS group elements and return a check of [τ]. *)
Definition eval_pair_needs_integer_named : Prop :=
  forall (x k N : Z), mu 2 x N -> False.

(** ** Alternating bilinear maps on cyclic [μ₃] are trivial *)

Definition in_mu3 (p x : Z) : Prop :=
  Z.coprime x p /\ powm x 3 p = 1.

Definition bilinear_mu3 (e : Z -> Z -> Z) (p : Z) : Prop :=
  (forall x y, in_mu3 p x -> in_mu3 p y -> in_mu3 p (e x y)) /\
  (forall x y z, in_mu3 p x -> in_mu3 p y -> in_mu3 p z ->
     e ((x * y) mod p) z mod p = (e x z * e y z) mod p) /\
  (forall x y z, in_mu3 p x -> in_mu3 p y -> in_mu3 p z ->
     e x ((y * z) mod p) mod p = (e x y * e x z) mod p).

Definition alternating_mu3 (e : Z -> Z -> Z) (p : Z) : Prop :=
  forall x, in_mu3 p x -> e x x mod p = 1.

Lemma in_mu3_one : forall p, 1 < p -> in_mu3 p 1.
Proof.
  intros p Hp. split.
  - unfold Z.coprime. apply Z.gcd_1_l.
  - unfold powm. rewrite Z.pow_1_l by lia. apply Z.mod_1_l; lia.
Qed.

Lemma in_mu3_mod :
  forall p x, 1 < p -> in_mu3 p x -> in_mu3 p (x mod p).
Proof.
  intros p x Hp [Hcop Hmu]. split.
  - unfold Z.coprime in *. rewrite Z.gcd_mod_l by lia. exact Hcop.
  - rewrite powm_mod_base by lia. exact Hmu.
Qed.

Lemma pairing_one_left :
  forall e p y,
    1 < p ->
    bilinear_mu3 e p ->
    in_mu3 p y ->
    e 1 y mod p = 1.
Proof.
  intros e p y Hp [Hrng [Hleft _]] Hy.
  pose proof (in_mu3_one p Hp) as H1.
  pose proof (Hrng 1 y H1 Hy) as Hz.
  pose proof (Hleft 1 1 y H1 H1 Hy) as Hbil.
  rewrite Z.mul_1_l, (Z.mod_small 1 p) in Hbil by lia.
  destruct Hz as [Hcz _].
  set (z := e 1 y).
  fold z in Hbil, Hcz.
  assert ((z * (z - 1)) mod p = 0) as Hdiff.
  { replace (z * (z - 1)) with (z * z - z) by ring.
    rewrite Zminus_mod, <- Hbil, Z.sub_diag, Z.mod_0_l; lia. }
  apply Z.mod_divide in Hdiff; [| lia].
  apply Z.gauss in Hdiff.
  2: { unfold Z.coprime in Hcz. rewrite Z.gcd_comm. exact Hcz. }
  change (e 1 y) with z.
  rewrite <- (Z.mod_1_l p) by lia.
  apply mods_eq_iff_divides; [lia | exact Hdiff].
Qed.

Lemma pairing_one_right :
  forall e p x,
    1 < p ->
    bilinear_mu3 e p ->
    in_mu3 p x ->
    e x 1 mod p = 1.
Proof.
  intros e p x Hp [Hrng [_ Hright]] Hx.
  pose proof (in_mu3_one p Hp) as H1.
  pose proof (Hrng x 1 Hx H1) as Hz.
  pose proof (Hright x 1 1 Hx H1 H1) as Hbil.
  rewrite Z.mul_1_l, (Z.mod_small 1 p) in Hbil by lia.
  destruct Hz as [Hcz _].
  set (z := e x 1).
  fold z in Hbil, Hcz.
  assert ((z * (z - 1)) mod p = 0) as Hdiff.
  { replace (z * (z - 1)) with (z * z - z) by ring.
    rewrite Zminus_mod, <- Hbil, Z.sub_diag, Z.mod_0_l; lia. }
  apply Z.mod_divide in Hdiff; [| lia].
  apply Z.gauss in Hdiff.
  2: { unfold Z.coprime in Hcz. rewrite Z.gcd_comm. exact Hcz. }
  change (e x 1) with z.
  rewrite <- (Z.mod_1_l p) by lia.
  apply mods_eq_iff_divides; [lia | exact Hdiff].
Qed.

Lemma two_omega_is_sq :
  forall p g,
    1 < p ->
    0 <= (p - 1) / 3 ->
    powm g (2 * ((p - 1) / 3)) p =
      (powm g ((p - 1) / 3) p * powm g ((p - 1) / 3) p) mod p.
Proof.
  intros p g Hp Ht.
  replace (2 * ((p - 1) / 3)) with ((p - 1) / 3 + (p - 1) / 3) by ring.
  apply powm_add_r; lia.
Qed.

Lemma in_mu3_omega :
  forall p g,
    Z.prime p ->
    Z.coprime g p ->
    is_order p g (p - 1) ->
    (3 | p - 1) ->
    in_mu3 p (powm g ((p - 1) / 3) p).
Proof.
  intros p g Hp Hg Hor Hdiv.
  pose proof (Z.prime_ge_2 p Hp).
  destruct Hdiv as [t Ht].
  assert (0 <= (p - 1) / 3) as Htpos.
  { rewrite Ht. apply Z.div_pos; nia. }
  split.
  - apply coprime_powm; [lia | exact Htpos | exact Hg].
  - pose proof (omega_from_primitive_root p g Hp Hg Hor (ex_intro _ t Ht)) as Hor3.
    apply Hor3.
Qed.

Lemma in_mu3_omega2 :
  forall p g,
    Z.prime p ->
    Z.coprime g p ->
    is_order p g (p - 1) ->
    (3 | p - 1) ->
    in_mu3 p (powm g (2 * ((p - 1) / 3)) p).
Proof.
  intros p g Hp Hg Hor Hdiv.
  pose proof (Z.prime_ge_2 p Hp).
  destruct Hdiv as [t Ht].
  assert (0 <= (p - 1) / 3) as Htpos.
  { rewrite Ht. apply Z.div_pos; nia. }
  split.
  - apply coprime_powm; [lia | nia | exact Hg].
  - rewrite <- powm_mul_r by nia.
    replace ((2 * ((p - 1) / 3)) * 3) with (2 * (p - 1)).
    2: { rewrite Ht. rewrite Z.div_mul by lia. ring. }
    rewrite (Z.mul_comm 2 (p - 1)), powm_mul_r by nia.
    destruct Hor as [_ [H1 _]].
    rewrite H1, powm_1_pow by nia.
    apply Z.mod_1_l; lia.
Qed.

Lemma pairing_omega_omega2 :
  forall e p w1,
    1 < p ->
    bilinear_mu3 e p ->
    alternating_mu3 e p ->
    in_mu3 p w1 ->
    e w1 ((w1 * w1) mod p) mod p = 1.
Proof.
  intros e p w1 Hp Hbil Halt Hw1.
  destruct Hbil as [_ [_ Hright]].
  pose proof (Hright w1 w1 w1 Hw1 Hw1 Hw1) as Hbil.
  rewrite Hbil, Z.mul_mod, (Halt w1 Hw1) by lia.
  rewrite Z.mul_1_l, Z.mod_1_l by lia. reflexivity.
Qed.

Lemma pairing_omega2_omega :
  forall e p w1,
    1 < p ->
    bilinear_mu3 e p ->
    alternating_mu3 e p ->
    in_mu3 p w1 ->
    e ((w1 * w1) mod p) w1 mod p = 1.
Proof.
  intros e p w1 Hp Hbil Halt Hw1.
  destruct Hbil as [_ [Hleft _]].
  pose proof (Hleft w1 w1 w1 Hw1 Hw1 Hw1) as Hbil.
  rewrite Hbil, Z.mul_mod, (Halt w1 Hw1) by lia.
  rewrite Z.mul_1_l, Z.mod_1_l by lia. reflexivity.
Qed.

Lemma pairing_omega2_omega2 :
  forall e p w1,
    1 < p ->
    bilinear_mu3 e p ->
    alternating_mu3 e p ->
    in_mu3 p w1 ->
    in_mu3 p ((w1 * w1) mod p) ->
    e ((w1 * w1) mod p) ((w1 * w1) mod p) mod p = 1.
Proof.
  intros e p w1 Hp Hbil Halt Hw1 Hw2.
  apply Halt. exact Hw2.
Qed.

Theorem alternating_bilinear_mu3_trivial :
  forall e p g x y,
    Z.prime p ->
    p <> 2 ->
    (3 | p - 1) ->
    Z.coprime g p ->
    is_order p g (p - 1) ->
    bilinear_mu3 e p ->
    alternating_mu3 e p ->
    in_mu3 p x ->
    in_mu3 p y ->
    e (x mod p) (y mod p) mod p = 1.
Proof.
  intros e p g x y Hp Hne Hdiv Hg Hor Hbil Halt [Hcx Hx3] [Hcy Hy3].
  pose proof (Z.prime_ge_2 p Hp).
  destruct (proj1 (cube_kernel_three p g x Hp Hne Hg Hor Hdiv Hcx) Hx3)
    as [mx [Hmx Heq_x]].
  destruct (proj1 (cube_kernel_three p g y Hp Hne Hg Hor Hdiv Hcy) Hy3)
    as [my [Hmy Heq_y]].
  rewrite <- Heq_x, <- Heq_y.
  set (t := (p - 1) / 3).
  set (w1 := powm g t p).
  assert (0 <= t) as Htpos.
  { unfold t. apply Z.div_pos; lia. }
  pose proof (in_mu3_one p ltac:(lia)) as H1mu.
  pose proof (in_mu3_omega p g Hp Hg Hor Hdiv) as Hw1.
  pose proof (in_mu3_omega2 p g Hp Hg Hor Hdiv) as Hw2.
  assert (powm g (2 * t) p = (w1 * w1) mod p) as Hw2sq.
  { unfold w1, t. apply two_omega_is_sq; lia. }
  assert (mx = 0 \/ mx = 1 \/ mx = 2) as Hmx3 by lia.
  assert (my = 0 \/ my = 1 \/ my = 2) as Hmy3 by lia.
  destruct Hmx3 as [Hmx0 | [Hmx1 | Hmx2]];
    destruct Hmy3 as [Hmy0 | [Hmy1 | Hmy2]]; subst mx my.
  - rewrite !Z.mul_0_l, !powm_0_r, !Z.mod_1_l by lia.
    apply pairing_one_left; [lia | exact Hbil | exact H1mu].
  - rewrite Z.mul_0_l, powm_0_r, Z.mod_1_l by lia.
    rewrite Z.mul_1_l. apply pairing_one_left; [lia | exact Hbil | exact Hw1].
  - rewrite Z.mul_0_l, powm_0_r, Z.mod_1_l by lia.
    apply pairing_one_left; [lia | exact Hbil | exact Hw2].
  - rewrite Z.mul_1_l, Z.mul_0_l, powm_0_r, Z.mod_1_l by lia.
    apply pairing_one_right; [lia | exact Hbil | exact Hw1].
  - rewrite !Z.mul_1_l. apply Halt. exact Hw1.
  - rewrite Z.mul_1_l.
    rewrite Hw2sq. apply pairing_omega_omega2; [lia | exact Hbil | exact Halt | exact Hw1].
  - rewrite Z.mul_0_l, powm_0_r, Z.mod_1_l by lia.
    apply pairing_one_right; [lia | exact Hbil | exact Hw2].
  - rewrite Z.mul_1_l.
    rewrite Hw2sq. apply pairing_omega2_omega; [lia | exact Hbil | exact Halt | exact Hw1].
  - rewrite Hw2sq. apply pairing_omega2_omega2; [lia | exact Hbil | exact Halt | exact Hw1 |].
    rewrite <- Hw2sq. exact Hw2.
Qed.

Theorem eval_pair_omega_13_not_alternating :
  powm 3 3 13 = 1 /\ eval_pair 3 1 13 <> 1.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

Theorem pin_mu3_only_one :
  forall x, Z.coprime x 11 -> powm x 3 11 = 1 -> x mod 11 = 1.
Proof.
  intros x Hcop Hmu.
  apply (mu3_unique_one_prime 11 x prime_11 ltac:(lia) ltac:(vm_compute; reflexivity)
           Hcop Hmu).
Qed.
