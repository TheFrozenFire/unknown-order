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
    [cas/157]).  On cyclic [𝔽_p*] a pairing of two hidden [μ₃]
    elements needs a curve ([Refuse_elliptic_curve_branch]).  On
    [N=pq] the kernel is [C₃×C₃]: the determinant of local
    exponents is alternating and [e(g_p,g_q)=ω ≠ 1] ([cas/158],
    trapdoor uses the factors).  Local [μ₃]-logs are additive
    ([mu3_log_mul], [cas/159]), so the determinant is bilinear.
    A mixed kernel element is a 1-query factoring witness
    ([mixed_mu3_splits], [cas/160]); a diagonal leftover does not
    split.  The pairing formula is not required.

    Cross-confirmed by [cas/87_eval_pairing.gp],
    [cas/157_mu3_pairing.gp], [cas/158_mu3n_pairing.gp],
    [cas/159_mu3_log.gp], and [cas/160_mu3_split.gp]. *)

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

(** ** Determinant pairing on [μ₃(Z/NZ)* ≅ C₃×C₃]

    Local logs of the two [C₃] factors.  The pairing is a
    trapdoor: it uses reduction mod [p] and [q].  Cross-confirmed
    by [cas/158_mu3n_pairing.gp]. *)

Definition mu3_log (om x p : Z) : Z :=
  if Z.eqb (powm om 0 p) (x mod p) then 0
  else if Z.eqb (powm om 1 p) (x mod p) then 1
  else 2.

Definition mu3N_det (om_p om_q p q x y : Z) : Z :=
  let a := mu3_log om_p x p in
  let b := mu3_log om_q x q in
  let c := mu3_log om_p y p in
  let d := mu3_log om_q y q in
  powm om_p (Z.modulo (a * d - b * c) 3) p.

Lemma mu3_log_range :
  forall om x p, 0 <= mu3_log om x p < 3.
Proof.
  intros om x p. unfold mu3_log.
  destruct (Z.eqb (powm om 0 p) (x mod p)); [| destruct (Z.eqb (powm om 1 p) (x mod p))]; lia.
Qed.

Theorem mu3N_det_alternating :
  forall om_p om_q p q x,
    1 < p ->
    mu3N_det om_p om_q p q x x = 1.
Proof.
  intros om_p om_q p q x Hp.
  unfold mu3N_det.
  set (a := mu3_log om_p x p).
  set (b := mu3_log om_q x q).
  replace (a * b - b * a) with 0 by ring.
  change (Z.modulo 0 3) with 0.
  unfold powm. rewrite Z.pow_0_r. apply Z.mod_1_l; lia.
Qed.

Theorem gp_91_order_3 : is_order 91 29 3.
Proof.
  split; [lia|]. split; [vm_compute; reflexivity|].
  intros k' [Hk' Hk'lt] Hpow.
  assert (k' = 1 \/ k' = 2) by lia.
  destruct H as [H | H]; subst k'; vm_compute in Hpow; discriminate.
Qed.

Theorem gq_91_order_3 : is_order 91 79 3.
Proof.
  split; [lia|]. split; [vm_compute; reflexivity|].
  intros k' [Hk' Hk'lt] Hpow.
  assert (k' = 1 \/ k' = 2) by lia.
  destruct H as [H | H]; subst k'; vm_compute in Hpow; discriminate.
Qed.

Theorem mu3N_det_gp_gq :
  mu3N_det 3 2 13 7 29 79 = 3.
Proof. vm_compute. reflexivity. Qed.

Theorem mu3N_det_gq_gp :
  mu3N_det 3 2 13 7 79 29 = 9.
Proof. vm_compute. reflexivity. Qed.

Theorem mu3_91_kernel_not_cyclic :
  forall x,
    Z.coprime x 91 ->
    powm x 3 91 = 1 ->
    ~ is_order 91 x 9.
Proof.
  intros x Hcop Hmu [Hk [H9 Hmin]].
  apply (Hmin 3); [lia | exact Hmu].
Qed.

(** ** Local [μ₃]-logs are additive, so [mu3N_det] is bilinear

    Reconstruction [x ≡ ω^{log x}] uses that the kernel is
    [{1,ω,ω²}] ([cube_kernel_three] via a primitive root).  Either
    generator still adds.  Cross-confirmed by
    [cas/159_mu3_log.gp].  Trapdoor still uses the factors. *)

Lemma mu3_order_coprime :
  forall p a k,
    Z.prime p ->
    is_order p a k ->
    Z.coprime a p.
Proof.
  intros p a k Hp [Hk [Hank _]].
  pose proof (Z.prime_ge_2 p Hp).
  unfold Z.coprime. rewrite Z.gcd_comm.
  apply Z.coprime_prime_l_iff; [exact Hp|].
  intro Hdiv.
  unfold powm in Hank.
  assert (a mod p = 0) as Ha0.
  { apply Z.mod_divide; [lia | exact Hdiv]. }
  rewrite <- Z.mod_pow_l in Hank.
  rewrite Ha0, Z.pow_0_l in Hank by lia.
  rewrite Z.mod_0_l in Hank by lia.
  discriminate.
Qed.

Lemma mu3_order_divides_pminus1 :
  forall p om,
    Z.prime p ->
    is_order p om 3 ->
    (3 | p - 1).
Proof.
  intros p om Hp Hor.
  pose proof (Z.prime_ge_2 p Hp).
  apply (proj2 (order_iff_divides p om 3 (p - 1) ltac:(lia) ltac:(lia) Hor)).
  apply fermat_coprime; [exact Hp | apply (mu3_order_coprime p om 3 Hp Hor)].
Qed.

Lemma mu3_prime_ne_2 :
  forall p om,
    Z.prime p ->
    is_order p om 3 ->
    p <> 2.
Proof.
  intros p om Hp Hor Heq.
  pose proof (mu3_order_divides_pminus1 p om Hp Hor) as Hdiv.
  subst p. destruct Hdiv as [t Ht]. lia.
Qed.

Lemma mu3_pow_1_ne_2 :
  forall p om,
    Z.prime p ->
    is_order p om 3 ->
    powm om 1 p <> powm om 2 p.
Proof.
  intros p om Hp Hor Hn.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (mu3_order_coprime p om 3 Hp Hor) as Hcop.
  destruct Hor as [_ [_ Hmin]].
  unfold powm in Hn.
  rewrite Z.pow_1_r, Z.pow_2_r in Hn.
  assert ((om * om - om) mod p = 0) as Hdiff.
  { rewrite Zminus_mod, <- Hn, Z.sub_diag, Z.mod_0_l by lia. reflexivity. }
  apply Z.mod_divide in Hdiff; [| lia].
  replace (om * om - om) with (om * (om - 1)) in Hdiff by ring.
  apply Z.gauss in Hdiff.
  2: { unfold Z.coprime in Hcop. rewrite Z.gcd_comm. exact Hcop. }
  apply (Hmin 1); [lia|].
  rewrite powm_1_r by lia.
  rewrite <- (Z.mod_1_l p) by lia.
  apply mods_eq_iff_divides; [lia | exact Hdiff].
Qed.

Lemma mu3_log_of_pow :
  forall om p k,
    Z.prime p ->
    is_order p om 3 ->
    0 <= k < 3 ->
    mu3_log om (powm om k p) p = k.
Proof.
  intros om p k Hp Hor Hk.
  pose proof (Z.prime_ge_2 p Hp).
  unfold mu3_log.
  assert (powm om k p mod p = powm om k p) as Hred.
  { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
  rewrite Hred.
  assert (k = 0 \/ k = 1 \/ k = 2) as Hk3 by lia.
  destruct Hk3 as [Hk0 | [Hk1 | Hk2]]; subst k.
  - destruct (Z.eqb (powm om 0 p) (powm om 0 p)) eqn:E.
    + reflexivity.
    + apply Z.eqb_neq in E. contradiction.
  - destruct (Z.eqb (powm om 0 p) (powm om 1 p)) eqn:E0.
    + apply Z.eqb_eq in E0.
      rewrite powm_0_r, Z.mod_1_l in E0 by lia.
      destruct Hor as [_ [_ Hmin]].
      exfalso. apply (Hmin 1); [lia | symmetry; exact E0].
    + destruct (Z.eqb (powm om 1 p) (powm om 1 p)) eqn:E1.
      * reflexivity.
      * apply Z.eqb_neq in E1. contradiction.
  - destruct (Z.eqb (powm om 0 p) (powm om 2 p)) eqn:E0.
    + apply Z.eqb_eq in E0.
      rewrite powm_0_r, Z.mod_1_l in E0 by lia.
      destruct Hor as [_ [_ Hmin]].
      exfalso. apply (Hmin 2); [lia | symmetry; exact E0].
    + destruct (Z.eqb (powm om 1 p) (powm om 2 p)) eqn:E1.
      * apply Z.eqb_eq in E1. exfalso. exact (mu3_pow_1_ne_2 p om Hp Hor E1).
      * reflexivity.
Qed.

Lemma mu3_is_omega_power :
  forall p om x,
    Z.prime p ->
    is_order p om 3 ->
    Z.coprime x p ->
    powm x 3 p = 1 ->
    exists k, 0 <= k < 3 /\ x mod p = powm om k p.
Proof.
  intros p om x Hp Hor Hx Hmu.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (mu3_prime_ne_2 p om Hp Hor) as Hne.
  pose proof (mu3_order_coprime p om 3 Hp Hor) as Hcom.
  pose proof (mu3_order_divides_pminus1 p om Hp Hor) as Hdiv.
  destruct (primitive_root_exists p Hp) as [g [Hcg Horg]].
  destruct Hor as [Hkpos [Hank Hmin]].
  destruct (proj1 (cube_kernel_three p g om Hp Hne Hcg Horg Hdiv Hcom) Hank)
    as [mo [Hmo Hom]].
  destruct (proj1 (cube_kernel_three p g x Hp Hne Hcg Horg Hdiv Hx) Hmu)
    as [mx [Hmx Hxeq]].
  set (t := (p - 1) / 3).
  assert (0 <= t) as Htpos.
  { unfold t. apply Z.div_pos; lia. }
  assert (mo = 0 \/ mo = 1 \/ mo = 2) as Hmo3 by lia.
  destruct Hmo3 as [Hmo0 | [Hmo1 | Hmo2]].
  - subst mo. rewrite Z.mul_0_l, powm_0_r, Z.mod_1_l in Hom by lia.
    exfalso. apply (Hmin 1); [lia|].
    rewrite powm_1_r by lia. symmetry; exact Hom.
  - subst mo. exists mx. split; [exact Hmx|].
    rewrite <- Hxeq.
    rewrite <- (powm_mod_base om mx p) by lia.
    rewrite <- Hom, Z.mul_1_l.
    rewrite <- powm_mul_r by lia.
    f_equal. ring.
  - subst mo. assert (mx = 0 \/ mx = 1 \/ mx = 2) as Hmx3 by lia.
    destruct Hmx3 as [Hmx0 | [Hmx1 | Hmx2]].
    + subst mx. exists 0. split; [lia|].
      rewrite <- Hxeq, Z.mul_0_l, powm_0_r by lia.
      rewrite powm_0_r, Z.mod_1_l by lia. reflexivity.
    + subst mx. exists 2. split; [lia|].
      rewrite <- Hxeq, Z.mul_1_l.
      rewrite <- (powm_mod_base om 2 p) by lia.
      rewrite <- Hom.
      rewrite <- powm_mul_r by lia.
      fold t.
      replace ((2 * t) * 2) with (t + 3 * t) by ring.
      pose proof Hdiv as Hdiv'.
      destruct Hdiv' as [t' Ht'].
      assert (t = t') as Htq.
      { unfold t. rewrite Ht'. apply Z.div_mul; lia. }
      rewrite Htq.
      replace (t' + 3 * t') with (t' + (p - 1)) by (rewrite Ht'; ring).
      rewrite powm_add_r by nia.
      destruct Horg as [_ [Hg1 _]].
      rewrite Hg1, Z.mul_1_r.
      unfold powm. rewrite Z.mod_mod by lia.
      reflexivity.
    + subst mx. exists 1. split; [lia|].
      rewrite <- Hxeq.
      rewrite <- (powm_mod_base om 1 p) by lia.
      rewrite <- Hom, powm_1_r by lia.
      unfold powm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma mu3_log_reconstructs :
  forall p om x,
    Z.prime p ->
    is_order p om 3 ->
    Z.coprime x p ->
    powm x 3 p = 1 ->
    powm om (mu3_log om x p) p = x mod p.
Proof.
  intros p om x Hp Hor Hx Hmu.
  pose proof (Z.prime_ge_2 p Hp).
  destruct (mu3_is_omega_power p om x Hp Hor Hx Hmu) as [k [Hk Heq]].
  transitivity (powm om k p); [| symmetry; exact Heq].
  f_equal.
  assert (mu3_log om x p = mu3_log om (powm om k p) p) as Hlogeq.
  { unfold mu3_log. rewrite Heq.
    replace (powm om k p mod p) with (powm om k p).
    2: { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
    reflexivity. }
  rewrite Hlogeq.
  apply mu3_log_of_pow; [exact Hp | exact Hor | exact Hk].
Qed.

Lemma mu3_log_mul :
  forall p om x y,
    Z.prime p ->
    is_order p om 3 ->
    Z.coprime x p ->
    Z.coprime y p ->
    powm x 3 p = 1 ->
    powm y 3 p = 1 ->
    mu3_log om ((x * y) mod p) p =
      Z.modulo (mu3_log om x p + mu3_log om y p) 3.
Proof.
  intros p om x y Hp Hor Hx Hy Hmux Hmuy.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (mu3_log_reconstructs p om x Hp Hor Hx Hmux) as Hrx.
  pose proof (mu3_log_reconstructs p om y Hp Hor Hy Hmuy) as Hry.
  set (a := mu3_log om x p).
  set (b := mu3_log om y p).
  pose proof (mu3_log_range om x p) as Ha.
  pose proof (mu3_log_range om y p) as Hb.
  assert ((x * y) mod p = powm om (a + b) p) as Hprod.
  { rewrite Z.mul_mod by lia.
    rewrite <- Hrx, <- Hry.
    symmetry. unfold a, b. apply powm_add_r; lia. }
  assert (powm om (a + b) p = powm om (Z.modulo (a + b) 3) p) as Hred.
  { change (powm om (a + b) p) with (eval_pair om (a + b) p).
    change (powm om (Z.modulo (a + b) 3) p) with (eval_pair om (Z.modulo (a + b) 3) p).
    apply eval_pair_reduce_mod_n; try lia.
    unfold mu. destruct Hor as [_ [Hank _]]. exact Hank. }
  assert (mu3_log om ((x * y) mod p) p =
            mu3_log om (powm om (Z.modulo (a + b) 3) p) p) as Hlogeq.
  { unfold mu3_log.
    rewrite Hprod, Hred.
    replace (powm om (Z.modulo (a + b) 3) p mod p)
      with (powm om (Z.modulo (a + b) 3) p).
    2: { unfold powm. rewrite Z.mod_mod by lia. reflexivity. }
    reflexivity. }
  rewrite Hlogeq.
  apply mu3_log_of_pow; [exact Hp | exact Hor |].
  apply Z.mod_pos_bound; lia.
Qed.

Lemma zmod3_mul :
  forall a d, Z.modulo (Z.modulo a 3 * d) 3 = Z.modulo (a * d) 3.
Proof.
  intros a d.
  rewrite (Z.mul_mod (Z.modulo a 3) d 3) by lia.
  rewrite Z.mod_mod by lia.
  rewrite <- (Z.mul_mod a d 3) by lia.
  reflexivity.
Qed.

Lemma zmod3_mul_l :
  forall a d, Z.modulo (a * Z.modulo d 3) 3 = Z.modulo (a * d) 3.
Proof.
  intros a d.
  rewrite (Z.mul_comm a), zmod3_mul, (Z.mul_comm d). reflexivity.
Qed.

Lemma det_exp_left_add :
  forall a a' b b' c d,
    Z.modulo (Z.modulo (a + a') 3 * d - Z.modulo (b + b') 3 * c) 3 =
    Z.modulo (Z.modulo (a * d - b * c) 3 + Z.modulo (a' * d - b' * c) 3) 3.
Proof.
  intros a a' b b' c d.
  rewrite (Zminus_mod (Z.modulo (a + a') 3 * d) (Z.modulo (b + b') 3 * c) 3).
  rewrite !zmod3_mul.
  rewrite <- Zminus_mod.
  replace ((a + a') * d - (b + b') * c)
    with ((a * d - b * c) + (a' * d - b' * c)) by ring.
  rewrite Z.add_mod by lia.
  reflexivity.
Qed.

Lemma det_exp_right_add :
  forall a b c c' d d',
    Z.modulo (a * Z.modulo (d + d') 3 - b * Z.modulo (c + c') 3) 3 =
    Z.modulo (Z.modulo (a * d - b * c) 3 + Z.modulo (a * d' - b * c') 3) 3.
Proof.
  intros a b c c' d d'.
  rewrite (Zminus_mod (a * Z.modulo (d + d') 3) (b * Z.modulo (c + c') 3) 3).
  rewrite !zmod3_mul_l.
  rewrite <- Zminus_mod.
  replace (a * (d + d') - b * (c + c'))
    with ((a * d - b * c) + (a * d' - b * c')) by ring.
  rewrite Z.add_mod by lia.
  reflexivity.
Qed.

Lemma mu3_log_mod_reduce :
  forall om x p q,
    0 < p ->
    0 < q ->
    mu3_log om (x mod (p * q)) p = mu3_log om x p.
Proof.
  intros om x p q Hp Hq.
  unfold mu3_log.
  rewrite <- (powm_1_r x (p * q)) by nia.
  rewrite powm_reduce_factor by nia.
  rewrite powm_1_r by lia.
  reflexivity.
Qed.

Lemma mu3_log_base_mod :
  forall om x p,
    p <> 0 ->
    mu3_log om x p = mu3_log om (x mod p) p.
Proof.
  intros om x p Hp.
  unfold mu3_log. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem omega_7_order_3 : is_order 7 2 3.
Proof.
  split; [lia|]. split; [vm_compute; reflexivity|].
  intros k' [Hk' Hk'lt] Hpow.
  assert (k' = 1 \/ k' = 2) by lia.
  destruct H as [H | H]; subst k'; vm_compute in Hpow; discriminate.
Qed.

Theorem pin_mu3_log_one : mu3_log 2 1 11 = 0.
Proof. vm_compute. reflexivity. Qed.

Theorem mu3N_det_left_bilinear :
  forall om_p om_q p q x y z,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    is_order p om_p 3 ->
    is_order q om_q 3 ->
    Z.coprime x (p * q) ->
    Z.coprime y (p * q) ->
    Z.coprime z (p * q) ->
    powm x 3 (p * q) = 1 ->
    powm y 3 (p * q) = 1 ->
    powm z 3 (p * q) = 1 ->
    mu3N_det om_p om_q p q ((x * y) mod (p * q)) z =
      (mu3N_det om_p om_q p q x z * mu3N_det om_p om_q p q y z) mod p.
Proof.
  intros om_p om_q p q x y z Hp Hq Hneq Horp Horq Hcx Hcy Hcz Hmux Hmuy Hmuz.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  destruct (proj1 (coprime_semiprime p q x Hp Hq Hneq) Hcx) as [Hcxp Hcxq].
  destruct (proj1 (coprime_semiprime p q y Hp Hq Hneq) Hcy) as [Hcyp Hcyq].
  destruct (proj1 (coprime_semiprime p q z Hp Hq Hneq) Hcz) as [Hczp Hczq].
  destruct (proj1 (mu3_N_iff_locals x p q Hp Hq Hneq) Hmux) as [Hxp Hxq].
  destruct (proj1 (mu3_N_iff_locals y p q Hp Hq Hneq) Hmuy) as [Hyp Hyq].
  destruct (proj1 (mu3_N_iff_locals z p q Hp Hq Hneq) Hmuz) as [Hzp Hzq].
  unfold mu3N_det.
  set (ax := mu3_log om_p x p).
  set (ay := mu3_log om_p y p).
  set (az := mu3_log om_p z p).
  set (bx := mu3_log om_q x q).
  set (byq := mu3_log om_q y q).
  set (bz := mu3_log om_q z q).
  assert (mu3_log om_p ((x * y) mod (p * q)) p = Z.modulo (ax + ay) 3) as Hlp.
  { rewrite (mu3_log_mod_reduce om_p (x * y) p q ltac:(lia) ltac:(lia)).
    rewrite mu3_log_base_mod by lia.
    apply mu3_log_mul; assumption. }
  assert (mu3_log om_q ((x * y) mod (p * q)) q = Z.modulo (bx + byq) 3) as Hlq.
  { rewrite (Z.mul_comm p q).
    rewrite (mu3_log_mod_reduce om_q (x * y) q p ltac:(lia) ltac:(lia)).
    rewrite mu3_log_base_mod by lia.
    apply mu3_log_mul; assumption. }
  rewrite Hlp, Hlq.
  rewrite det_exp_left_add.
  change (powm om_p (Z.modulo (Z.modulo (ax * bz - bx * az) 3
      + Z.modulo (ay * bz - byq * az) 3) 3) p)
    with (eval_pair om_p (Z.modulo (Z.modulo (ax * bz - bx * az) 3
      + Z.modulo (ay * bz - byq * az) 3) 3) p).
  rewrite <- eval_pair_reduce_mod_n with
    (k := Z.modulo (ax * bz - bx * az) 3 + Z.modulo (ay * bz - byq * az) 3)
    (n := 3) (N := p) (x := om_p).
  2: lia.
  2: lia.
  2: { pose proof (Z.mod_pos_bound (ax * bz - bx * az) 3 ltac:(lia)).
       pose proof (Z.mod_pos_bound (ay * bz - byq * az) 3 ltac:(lia)). lia. }
  2: { unfold mu. destruct Horp as [_ [Hank _]]. exact Hank. }
  unfold eval_pair.
  rewrite powm_add_r.
  2: lia.
  2: apply Z.mod_pos_bound; lia.
  2: apply Z.mod_pos_bound; lia.
  reflexivity.
Qed.

Theorem mu3N_det_right_bilinear :
  forall om_p om_q p q x y z,
    Z.prime p ->
    Z.prime q ->
    p <> q ->
    is_order p om_p 3 ->
    is_order q om_q 3 ->
    Z.coprime x (p * q) ->
    Z.coprime y (p * q) ->
    Z.coprime z (p * q) ->
    powm x 3 (p * q) = 1 ->
    powm y 3 (p * q) = 1 ->
    powm z 3 (p * q) = 1 ->
    mu3N_det om_p om_q p q x ((y * z) mod (p * q)) =
      (mu3N_det om_p om_q p q x y * mu3N_det om_p om_q p q x z) mod p.
Proof.
  intros om_p om_q p q x y z Hp Hq Hneq Horp Horq Hcx Hcy Hcz Hmux Hmuy Hmuz.
  pose proof (Z.prime_ge_2 p Hp). pose proof (Z.prime_ge_2 q Hq).
  destruct (proj1 (coprime_semiprime p q x Hp Hq Hneq) Hcx) as [Hcxp Hcxq].
  destruct (proj1 (coprime_semiprime p q y Hp Hq Hneq) Hcy) as [Hcyp Hcyq].
  destruct (proj1 (coprime_semiprime p q z Hp Hq Hneq) Hcz) as [Hczp Hczq].
  destruct (proj1 (mu3_N_iff_locals x p q Hp Hq Hneq) Hmux) as [Hxp Hxq].
  destruct (proj1 (mu3_N_iff_locals y p q Hp Hq Hneq) Hmuy) as [Hyp Hyq].
  destruct (proj1 (mu3_N_iff_locals z p q Hp Hq Hneq) Hmuz) as [Hzp Hzq].
  unfold mu3N_det.
  set (ax := mu3_log om_p x p).
  set (ay := mu3_log om_p y p).
  set (az := mu3_log om_p z p).
  set (bx := mu3_log om_q x q).
  set (byq := mu3_log om_q y q).
  set (bz := mu3_log om_q z q).
  assert (mu3_log om_p ((y * z) mod (p * q)) p = Z.modulo (ay + az) 3) as Hlp.
  { rewrite (mu3_log_mod_reduce om_p (y * z) p q ltac:(lia) ltac:(lia)).
    rewrite mu3_log_base_mod by lia.
    apply mu3_log_mul; assumption. }
  assert (mu3_log om_q ((y * z) mod (p * q)) q = Z.modulo (byq + bz) 3) as Hlq.
  { rewrite (Z.mul_comm p q).
    rewrite (mu3_log_mod_reduce om_q (y * z) q p ltac:(lia) ltac:(lia)).
    rewrite mu3_log_base_mod by lia.
    apply mu3_log_mul; assumption. }
  rewrite Hlp, Hlq.
  rewrite det_exp_right_add.
  change (powm om_p (Z.modulo (Z.modulo (ax * byq - bx * ay) 3
      + Z.modulo (ax * bz - bx * az) 3) 3) p)
    with (eval_pair om_p (Z.modulo (Z.modulo (ax * byq - bx * ay) 3
      + Z.modulo (ax * bz - bx * az) 3) 3) p).
  rewrite <- eval_pair_reduce_mod_n with
    (k := Z.modulo (ax * byq - bx * ay) 3 + Z.modulo (ax * bz - bx * az) 3)
    (n := 3) (N := p) (x := om_p).
  2: lia.
  2: lia.
  2: { pose proof (Z.mod_pos_bound (ax * byq - bx * ay) 3 ltac:(lia)).
       pose proof (Z.mod_pos_bound (ax * bz - bx * az) 3 ltac:(lia)). lia. }
  2: { unfold mu. destruct Horp as [_ [Hank _]]. exact Hank. }
  unfold eval_pair.
  rewrite powm_add_r.
  2: lia.
  2: apply Z.mod_pos_bound; lia.
  2: apply Z.mod_pos_bound; lia.
  reflexivity.
Qed.

Theorem mu3N_det_skew :
  forall om_p om_q p q x y,
    Z.prime p ->
    is_order p om_p 3 ->
    mu3N_det om_p om_q p q y x =
      powm (mu3N_det om_p om_q p q x y) 2 p.
Proof.
  intros om_p om_q p q x y Hp Hor.
  pose proof (Z.prime_ge_2 p Hp).
  unfold mu3N_det.
  set (a := mu3_log om_p x p).
  set (b := mu3_log om_q x q).
  set (c := mu3_log om_p y p).
  set (d := mu3_log om_q y q).
  set (k := a * d - b * c).
  replace (c * b - d * a) with (- k) by (unfold k; ring).
  transitivity (powm om_p (Z.modulo (2 * k) 3) p).
  - apply f_equal with (f := fun e => powm om_p e p).
    apply mods_eq_iff_divides; [lia|].
    replace (- k - 2 * k) with (-3 * k) by ring.
    exists (- k). ring.
  - rewrite <- powm_mul_r by (try lia; apply Z.mod_pos_bound; lia).
    replace ((2 * k) mod 3) with ((2 * (k mod 3)) mod 3).
    2: { rewrite Z.mul_mod, Z.mod_mod by lia.
         replace (2 mod 3) with 2 by (vm_compute; reflexivity).
         rewrite (Z.mul_mod 2 k 3) by lia.
         replace (2 mod 3) with 2 by (vm_compute; reflexivity).
         reflexivity. }
    replace (k mod 3 * 2) with (2 * (k mod 3)) by ring.
    symmetry.
    change (eval_pair om_p (2 * (k mod 3)) p =
              eval_pair om_p ((2 * (k mod 3)) mod 3) p).
    apply eval_pair_reduce_mod_n; try lia.
    + pose proof (Z.mod_pos_bound k 3 ltac:(lia)). nia.
    + unfold mu. destruct Hor as [_ [Hank _]]. exact Hank.
Qed.
