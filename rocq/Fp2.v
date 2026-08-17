From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import PeanoNat.

Require Import RocqProofs.NumberTheory.
Require Import RocqProofs.QuadRecip.
Require Import Lucas.

Open Scope Z_scope.

(** * [F_p[√D]] and [V_{p+1} ≡ 2] when [D] is a QNR

    Elements are [x + y √D].  Frobenius sends [√D] to
    [D^{(p−1)/2} √D ≡ −√D], so it is conjugation.  Then
    [α^p = β], [α^{p+1} = 1], and [V_{p+1} = α^{p+1}+β^{p+1} = 2]. *)

Record fp2 : Type := { fp_x : Z; fp_y : Z }.

Definition fp2_eq (p : Z) (u v : fp2) : Prop :=
  fp_x u mod p = fp_x v mod p /\ fp_y u mod p = fp_y v mod p.

Definition fp2_zero : fp2 := {| fp_x := 0; fp_y := 0 |}.
Definition fp2_one : fp2 := {| fp_x := 1; fp_y := 0 |}.
Definition fp2_embed (n : Z) : fp2 := {| fp_x := n; fp_y := 0 |}.
Definition fp2_sqrt : fp2 := {| fp_x := 0; fp_y := 1 |}.

Definition fp2_add (u v : fp2) : fp2 :=
  {| fp_x := fp_x u + fp_x v; fp_y := fp_y u + fp_y v |}.

Definition fp2_opp (u : fp2) : fp2 :=
  {| fp_x := - fp_x u; fp_y := - fp_y u |}.

Definition fp2_mul (D : Z) (u v : fp2) : fp2 :=
  {| fp_x := fp_x u * fp_x v + D * fp_y u * fp_y v;
     fp_y := fp_x u * fp_y v + fp_y u * fp_x v |}.

Definition fp2_conj (u : fp2) : fp2 :=
  {| fp_x := fp_x u; fp_y := - fp_y u |}.

Fixpoint fp2_pow (D : Z) (u : fp2) (n : nat) : fp2 :=
  match n with
  | O => fp2_one
  | S n' => fp2_mul D u (fp2_pow D u n')
  end.

Lemma fp2_eq_refl : forall p u, p <> 0 -> fp2_eq p u u.
Proof. intros. unfold fp2_eq. split; reflexivity. Qed.

Lemma fp2_mul_embed_l :
  forall D n v,
    fp2_mul D (fp2_embed n) v =
      {| fp_x := n * fp_x v; fp_y := n * fp_y v |}.
Proof. intros. unfold fp2_mul, fp2_embed. simpl. f_equal; ring. Qed.

Lemma fp2_add_conj :
  forall u, fp2_add u (fp2_conj u) = fp2_embed (2 * fp_x u).
Proof. intros [x y]. unfold fp2_add, fp2_conj, fp2_embed. cbn [fp_x fp_y]. f_equal; ring. Qed.

Lemma fp2_mul_conj :
  forall D u,
    fp2_mul D u (fp2_conj u) = fp2_embed (fp_x u * fp_x u - D * fp_y u * fp_y u).
Proof. intros D [x y]. unfold fp2_mul, fp2_conj, fp2_embed. simpl. f_equal; ring. Qed.

Lemma inv2_exists :
  forall p, Z.prime p -> p <> 2 -> exists i, (2 * i) mod p = 1.
Proof.
  intros p Hp Hne.
  pose proof (Z.prime_ge_2 p Hp).
  assert (Z.coprime 2 p).
  { apply Z.coprime_prime_l_iff; [exact Z.prime_2|].
    intro Hd. apply Z.divide_prime_prime in Hd;
      [lia | exact Z.prime_2 | exact Hp]. }
  apply (proj1 (Z.Bezout_coprime_iff 2 p)) in H0.
  destruct H0 as [u [v Huv]].
  exists (u mod p).
  transitivity ((2 * u) mod p).
  - apply Z.mul_mod_idemp_r. lia.
  - replace (2 * u) with (1 + (- v) * p)
      by (rewrite Z.mul_comm in Huv; lia).
    rewrite Z.mod_add by lia.
    apply Z.mod_1_l. lia.
Qed.

(** [α = (P + √D)/2], [β = (P − √D)/2], [D = P² − 4], [Q = 1]. *)
Definition alpha (P i : Z) : fp2 :=
  {| fp_x := P * i; fp_y := i |}.
Definition beta (P i : Z) : fp2 :=
  {| fp_x := P * i; fp_y := - i |}.

Lemma alpha_plus_beta :
  forall P i,
    fp2_add (alpha P i) (beta P i) = fp2_embed (2 * P * i).
Proof. intros. unfold alpha, beta, fp2_add, fp2_embed. cbn [fp_x fp_y]. f_equal; ring. Qed.

Lemma alpha_mul_beta :
  forall P i D,
    D = P * P - 4 ->
    fp2_mul D (alpha P i) (beta P i) =
      fp2_embed (P * P * i * i - D * i * i).
Proof. intros. unfold alpha, beta, fp2_mul, fp2_embed. simpl. f_equal; ring. Qed.

Lemma alpha_beta_is_one :
  forall P i p D,
    Z.prime p ->
    p <> 2 ->
    D = P * P - 4 ->
    (2 * i) mod p = 1 ->
    fp2_eq p (fp2_mul D (alpha P i) (beta P i)) fp2_one.
Proof.
  intros P i p D Hp Hne HD Hi.
  unfold fp2_eq, fp2_one. rewrite (alpha_mul_beta P i D HD).
  unfold fp2_embed. cbn [fp_x fp_y].
  rewrite HD.
  split; [| reflexivity].
  replace (P * P * i * i - (P * P - 4) * i * i) with (4 * i * i) by ring.
  replace (4 * i * i) with ((2 * i) * (2 * i)) by ring.
  rewrite Z.mul_mod by (pose proof (Z.prime_ge_2 p Hp); lia).
  rewrite Hi, Z.mul_1_l.
  reflexivity.
Qed.

Lemma alpha_plus_beta_is_P :
  forall P i p,
    Z.prime p ->
    (2 * i) mod p = 1 ->
    fp2_eq p (fp2_add (alpha P i) (beta P i)) (fp2_embed P).
Proof.
  intros P i p Hp Hi.
  rewrite alpha_plus_beta. unfold fp2_eq, fp2_embed. cbn [fp_x fp_y].
  split; [| reflexivity].
  replace (2 * P * i) with (P * (2 * i)) by ring.
  rewrite Z.mul_mod by (pose proof (Z.prime_ge_2 p Hp); lia).
  rewrite Hi, Z.mul_1_r.
  pose proof (Z.prime_ge_2 p Hp).
  rewrite Z.mod_mod; lia.
Qed.

(** Addition formula in the extension: [α^{m+n} + β^{m+n} =
    (α+β)(α^m+β^m wait no).  The recurrence
    [s_{n+2} = P s_{n+1} − s_n] holds for [s_n = α^n + β^n]. *)

Lemma fp2_pow_0 : forall D u, fp2_pow D u 0 = fp2_one.
Proof. reflexivity. Qed.

Lemma fp2_pow_1 : forall D u, fp2_pow D u 1%nat = fp2_mul D u fp2_one.
Proof. reflexivity. Qed.

Lemma fp2_mul_one_r :
  forall D u, fp2_mul D u fp2_one = {| fp_x := fp_x u; fp_y := fp_y u |}.
Proof. intros D [x y]. unfold fp2_mul, fp2_one. simpl. f_equal; ring. Qed.

Lemma fp2_mul_comm :
  forall D u v, fp2_mul D u v = fp2_mul D v u.
Proof. intros D [x1 y1] [x2 y2]. unfold fp2_mul. simpl. f_equal; ring. Qed.

Lemma fp2_eq_trans :
  forall p u v w,
    fp2_eq p u v -> fp2_eq p v w -> fp2_eq p u w.
Proof. intros p u v w [A B] [C D]. unfold fp2_eq. split; congruence. Qed.

Lemma fp2_eq_sym :
  forall p u v, fp2_eq p u v -> fp2_eq p v u.
Proof. intros p u v [A B]. unfold fp2_eq. split; congruence. Qed.

Lemma opp_mod_compat :
  forall a p, p <> 0 -> (- a) mod p = (- (a mod p)) mod p.
Proof.
  intros a p Hp.
  rewrite (Z.div_mod a p Hp) at 1.
  rewrite Z.opp_add_distr.
  replace (- (p * (a / p)) + - (a mod p))
    with (- (a mod p) + (- (a / p)) * p) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma fp2_eq_opp :
  forall p u v,
    p <> 0 ->
    fp2_eq p u v ->
    fp2_eq p (fp2_opp u) (fp2_opp v).
Proof.
  intros p u v Hp [A B]. unfold fp2_eq, fp2_opp. simpl.
  split.
  - rewrite (opp_mod_compat (fp_x u) p Hp), A,
      <- (opp_mod_compat (fp_x v) p Hp). reflexivity.
  - rewrite (opp_mod_compat (fp_y u) p Hp), B,
      <- (opp_mod_compat (fp_y v) p Hp). reflexivity.
Qed.

Lemma fp2_pow_succ :
  forall D u n, fp2_pow D u (S n) = fp2_mul D u (fp2_pow D u n).
Proof. reflexivity. Qed.

Lemma fp2_eq_mul :
  forall p D u u' v v',
    p <> 0 ->
    fp2_eq p u u' ->
    fp2_eq p v v' ->
    fp2_eq p (fp2_mul D u v) (fp2_mul D u' v').
Proof.
  intros p D u u' v v' Hp [Hx Hy] [Hx' Hy'].
  unfold fp2_eq, fp2_mul. simpl.
  split.
  - assert (Hxmul : (fp_x u * fp_x v) mod p = (fp_x u' * fp_x v') mod p).
    { rewrite Z.mul_mod, Hx, Hx', <- Z.mul_mod; lia. }
    assert (Hymul : (D * fp_y u * fp_y v) mod p =
                    (D * fp_y u' * fp_y v') mod p).
    { replace (D * fp_y u * fp_y v) with (D * (fp_y u * fp_y v)) by ring.
      replace (D * fp_y u' * fp_y v') with (D * (fp_y u' * fp_y v')) by ring.
      rewrite (Z.mul_mod D (fp_y u * fp_y v) p) by lia.
      rewrite (Z.mul_mod (fp_y u) (fp_y v) p) by lia.
      rewrite Hy, Hy'.
      rewrite <- (Z.mul_mod (fp_y u') (fp_y v') p) by lia.
      rewrite <- (Z.mul_mod D (fp_y u' * fp_y v') p) by lia.
      reflexivity. }
    rewrite Z.add_mod, Hxmul, Hymul, <- Z.add_mod; lia.
  - assert (H1 : (fp_x u * fp_y v) mod p = (fp_x u' * fp_y v') mod p).
    { rewrite Z.mul_mod, Hx, Hy', <- Z.mul_mod; lia. }
    assert (H2 : (fp_y u * fp_x v) mod p = (fp_y u' * fp_x v') mod p).
    { rewrite Z.mul_mod, Hy, Hx', <- Z.mul_mod; lia. }
    rewrite Z.add_mod, H1, H2, <- Z.add_mod; lia.
Qed.

Lemma fp2_eq_opp_mul :
  forall p D u u' v v',
    p <> 0 ->
    fp2_eq p u u' ->
    fp2_eq p v v' ->
    fp2_eq p (fp2_opp (fp2_mul D u v)) (fp2_opp (fp2_mul D u' v')).
Proof.
  intros. apply fp2_eq_opp; [lia|]. apply fp2_eq_mul; assumption.
Qed.

Lemma fp2_eq_add :
  forall p u u' v v',
    p <> 0 ->
    fp2_eq p u u' ->
    fp2_eq p v v' ->
    fp2_eq p (fp2_add u v) (fp2_add u' v').
Proof.
  intros p u u' v v' Hp [Hx Hy] [Hx' Hy'].
  unfold fp2_eq, fp2_add. simpl.
  split.
  - rewrite Z.add_mod, Hx, Hx', <- Z.add_mod; lia.
  - rewrite Z.add_mod, Hy, Hy', <- Z.add_mod; lia.
Qed.

Lemma fp2_mul_assoc :
  forall D u v w,
    fp2_mul D (fp2_mul D u v) w = fp2_mul D u (fp2_mul D v w).
Proof.
  intros D [x1 y1] [x2 y2] [x3 y3].
  unfold fp2_mul. simpl. f_equal; ring.
Qed.

Lemma fp2_mul_add_r :
  forall D u v w,
    fp2_mul D u (fp2_add v w) = fp2_add (fp2_mul D u v) (fp2_mul D u w).
Proof.
  intros D [x1 y1] [x2 y2] [x3 y3].
  unfold fp2_mul, fp2_add. simpl. f_equal; ring.
Qed.

Lemma fp2_mul_add_l :
  forall D u v w,
    fp2_mul D (fp2_add u v) w = fp2_add (fp2_mul D u w) (fp2_mul D v w).
Proof.
  intros D [x1 y1] [x2 y2] [x3 y3].
  unfold fp2_mul, fp2_add. simpl. f_equal; ring.
Qed.

Lemma fp2_pow_add_r :
  forall D u n,
    fp2_pow D u (S n) = fp2_mul D (fp2_pow D u n) u.
Proof.
  intros D u n. induction n as [| n IH].
  - simpl. apply fp2_mul_comm.
  - simpl. rewrite IH at 1. rewrite fp2_mul_assoc. reflexivity.
Qed.

Lemma fp2_pow_SS :
  forall D u n,
    fp2_pow D u (S (S n)) = fp2_mul D u (fp2_pow D u (S n)).
Proof. intros. reflexivity. Qed.

Lemma alpha_beta_rec :
  forall D P i n,
    fp2_add (fp2_pow D (alpha P i) (S (S n)))
            (fp2_pow D (beta P i) (S (S n))) =
    fp2_add
      (fp2_mul D (fp2_add (alpha P i) (beta P i))
                 (fp2_add (fp2_pow D (alpha P i) (S n))
                          (fp2_pow D (beta P i) (S n))))
      (fp2_opp (fp2_mul D (fp2_mul D (alpha P i) (beta P i))
                          (fp2_add (fp2_pow D (alpha P i) n)
                                   (fp2_pow D (beta P i) n)))).
Proof.
  intros D P i n.
  rewrite !fp2_pow_SS.
  rewrite (fp2_pow_succ D (alpha P i) n).
  rewrite (fp2_pow_succ D (beta P i) n).
  rewrite !fp2_mul_add_r, !fp2_mul_add_l.
  destruct (fp2_pow D (alpha P i) n) as [ax ay].
  destruct (fp2_pow D (beta P i) n) as [bx byy].
  unfold fp2_add, fp2_opp, fp2_mul, alpha, beta.
  cbn [fp_x fp_y].
  f_equal; ring.
Qed.

Lemma lucasV_as_fp2 :
  forall P i p D n,
    Z.prime p ->
    p <> 2 ->
    D = P * P - 4 ->
    (2 * i) mod p = 1 ->
    fp2_eq p
      (fp2_add (fp2_pow D (alpha P i) n) (fp2_pow D (beta P i) n))
      (fp2_embed (lucasV P 1 n)).
Proof.
  intros P i p D n Hp Hne HD Hi.
  pose proof (Z.prime_ge_2 p Hp) as Hp2.
  induction n as [n IH] using (well_founded_ind Wf_nat.lt_wf).
  destruct n as [| n'].
  - simpl. unfold fp2_eq, fp2_add, fp2_one, fp2_embed. simpl.
    split; reflexivity.
  - destruct n' as [| n''].
    + simpl. rewrite !fp2_mul_one_r. apply alpha_plus_beta_is_P; assumption.
    + rewrite lucasV_rec. rewrite Z.mul_1_l.
      rewrite alpha_beta_rec.
      pose proof (IH n'' ltac:(lia)) as IHn.
      pose proof (IH (S n'') ltac:(lia)) as IHsn.
      pose proof (alpha_plus_beta_is_P P i p Hp Hi) as HP.
      pose proof (alpha_beta_is_one P i p D Hp Hne HD Hi) as HQ.
      apply fp2_eq_trans with
        (v := fp2_add
                (fp2_mul D (fp2_embed P) (fp2_embed (lucasV P 1 (S n''))))
                (fp2_opp (fp2_mul D fp2_one (fp2_embed (lucasV P 1 n''))))).
      { apply fp2_eq_add;
          [lia
          | apply fp2_eq_mul; [lia | exact HP | exact IHsn]
          | apply fp2_eq_opp_mul; [lia | exact HQ | exact IHn]]. }
      { unfold fp2_eq, fp2_embed, fp2_add, fp2_opp, fp2_mul, fp2_one.
        cbn [fp_x fp_y].
        split.
        { replace (P * lucasV P 1 (S n'') + D * 0 * 0 +
                    - (1 * lucasV P 1 n'' + D * 0 * 0))
            with (P * lucasV P 1 (S n'') - lucasV P 1 n'') by ring.
          reflexivity. }
        { replace (P * 0 + 0 * lucasV P 1 (S n'') +
                    - (1 * 0 + 0 * lucasV P 1 n'')) with 0 by ring.
          reflexivity. } }
Qed.

(** ** Binomial coefficients and Freshman's dream *)

Fixpoint binom (n k : nat) : Z :=
  match n with
  | O => match k with O => 1 | S _ => 0 end
  | S n' =>
      match k with
      | O => 1
      | S k' => binom n' k' + binom n' (S k')
      end
  end.

Lemma binom_n_0 : forall n, binom n 0 = 1.
Proof. destruct n; reflexivity. Qed.

Lemma binom_0_S : forall k, binom 0 (S k) = 0.
Proof. reflexivity. Qed.

Lemma binom_gt : forall n k, (n < k)%nat -> binom n k = 0.
Proof.
  induction n as [| n IH]; intros k Hlt.
  - destruct k; [lia | reflexivity].
  - destruct k as [| k]; [lia|].
    simpl. rewrite (IH (S k) ltac:(lia)), (IH k ltac:(lia)). ring.
Qed.

Lemma binom_n_n : forall n, binom n n = 1.
Proof.
  induction n as [| n IH]; [reflexivity|].
  simpl. rewrite IH, binom_gt by lia. ring.
Qed.

Lemma binom_n_1 : forall n, binom n 1%nat = Z.of_nat n.
Proof.
  induction n as [| n IH]; [reflexivity|].
  simpl. rewrite binom_n_0, IH. lia.
Qed.

Lemma binom_S_S_expand :
  forall n k, binom (S n) (S k) = binom n k + binom n (S k).
Proof. reflexivity. Qed.

Lemma binom_mul_row :
  forall n k,
    Z.of_nat (S k) * binom (S n) (S k) = Z.of_nat (S n) * binom n k.
Proof.
  induction n as [| n IHn]; intros k.
  - destruct k; simpl; lia.
  - destruct k as [| k].
    + rewrite binom_n_1. simpl. lia.
    + rewrite binom_S_S_expand, Z.mul_add_distr_l.
      pose proof (IHn (S k)) as IH2.
      pose proof (IHn k) as IH1.
      rewrite IH2.
      replace (Z.of_nat (S (S k)) * binom (S n) (S k))
        with (Z.of_nat (S k) * binom (S n) (S k) + binom (S n) (S k))
        by lia.
      rewrite IH1.
      rewrite (binom_S_S_expand n k).
      lia.
Qed.

Lemma prime_divides_binom :
  forall (q k : nat),
    Z.prime (Z.of_nat q) ->
    (0 < k < q)%nat ->
    (Z.of_nat q | binom q k).
Proof.
  intros q k Hq Hkk.
  destruct q as [| q']; [pose proof (Z.prime_ge_2 0 Hq); lia|].
  destruct k as [| k']; [lia|].
  pose proof (binom_mul_row q' k') as Hrow.
  assert (Z.of_nat (S q') | Z.of_nat (S k') * binom (S q') (S k')).
  { rewrite Hrow. apply Z.divide_factor_l. }
  apply Z.gauss in H.
  - exact H.
  - apply Z.coprime_prime_l_iff; [exact Hq|].
    intros [t Ht].
    assert (Z.of_nat (S k') < Z.of_nat (S q')) by lia.
    assert (0 < Z.of_nat (S k')) by lia.
    assert (0 < Z.of_nat (S q')) by lia.
    destruct (Z.lt_trichotomy t 0) as [Htneg | [Ht0 | Htpos]];
      [nia | subst t; lia | nia].
Qed.

Definition fp2_scale (k : Z) (u : fp2) : fp2 :=
  {| fp_x := k * fp_x u; fp_y := k * fp_y u |}.

Lemma fp2_scale_as_mul :
  forall D k u, fp2_scale k u = fp2_mul D (fp2_embed k) u.
Proof.
  intros D k [x y]. unfold fp2_scale, fp2_mul, fp2_embed.
  cbn [fp_x fp_y]. f_equal; ring.
Qed.

Lemma fp2_scale_add :
  forall k u v,
    fp2_scale k (fp2_add u v) = fp2_add (fp2_scale k u) (fp2_scale k v).
Proof.
  intros k [x1 y1] [x2 y2]. unfold fp2_scale, fp2_add. cbn [fp_x fp_y].
  f_equal; ring.
Qed.

Lemma fp2_eq_scale :
  forall p k u v,
    p <> 0 -> fp2_eq p u v -> fp2_eq p (fp2_scale k u) (fp2_scale k v).
Proof.
  intros p k u v Hp [Hx Hy]. unfold fp2_eq, fp2_scale. cbn [fp_x fp_y].
  split.
  - rewrite Z.mul_mod, Hx, <- Z.mul_mod; lia.
  - rewrite Z.mul_mod, Hy, <- Z.mul_mod; lia.
Qed.

Lemma fp2_eq_scale_mod :
  forall p k u,
    p <> 0 -> fp2_eq p (fp2_scale k u) (fp2_scale (k mod p) u).
Proof.
  intros p k u Hp. unfold fp2_eq, fp2_scale. cbn [fp_x fp_y].
  split.
  - rewrite (Z.mul_mod k (fp_x u) p) by lia.
    rewrite (Z.mul_mod (k mod p) (fp_x u) p) by lia.
    rewrite Z.mod_mod by lia. reflexivity.
  - rewrite (Z.mul_mod k (fp_y u) p) by lia.
    rewrite (Z.mul_mod (k mod p) (fp_y u) p) by lia.
    rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma fp2_scale_p_zero :
  forall p u, Z.prime p -> fp2_eq p (fp2_scale p u) fp2_zero.
Proof.
  intros p u Hp. pose proof (Z.prime_ge_2 p Hp).
  unfold fp2_eq, fp2_scale, fp2_zero. cbn [fp_x fp_y].
  split.
  - rewrite Z.mul_comm, Z.mod_mul by lia. rewrite Z.mod_0_l; lia.
  - rewrite Z.mul_comm, Z.mod_mul by lia. rewrite Z.mod_0_l; lia.
Qed.

Lemma fp2_scale_mul_div :
  forall p k u,
    Z.prime p ->
    (p | k) ->
    fp2_eq p (fp2_scale k u) fp2_zero.
Proof.
  intros p k u Hp [t Ht]. subst k.
  pose proof (Z.prime_ge_2 p Hp).
  apply fp2_eq_trans with (v := fp2_scale p (fp2_scale t u)).
  - unfold fp2_eq, fp2_scale. cbn [fp_x fp_y]. split; f_equal; ring.
  - apply fp2_scale_p_zero. exact Hp.
Qed.

Fixpoint fp2_sum (f : nat -> fp2) (n : nat) : fp2 :=
  match n with
  | O => f 0%nat
  | S n' => fp2_add (fp2_sum f n') (f (S n'))
  end.

Lemma fp2_eq_sum :
  forall p f g n,
    p <> 0 ->
    (forall k, (k <= n)%nat -> fp2_eq p (f k) (g k)) ->
    fp2_eq p (fp2_sum f n) (fp2_sum g n).
Proof.
  intros p f g n Hp Hfg. induction n as [| n IH].
  - simpl. apply Hfg. lia.
  - simpl. apply fp2_eq_add;
      [exact Hp | apply IH; intros; apply Hfg; lia | apply Hfg; lia].
Qed.

Lemma fp2_sum_zero :
  forall p f n,
    Z.prime p ->
    (forall k, (k <= n)%nat -> fp2_eq p (f k) fp2_zero) ->
    fp2_eq p (fp2_sum f n) fp2_zero.
Proof.
  intros p f n Hp Hf. induction n as [| n IH].
  - simpl. apply Hf. lia.
  - simpl.
    apply fp2_eq_trans with (v := fp2_add fp2_zero fp2_zero).
    + apply fp2_eq_add;
        [pose proof (Z.prime_ge_2 p Hp); lia
        | apply IH; intros; apply Hf; lia
        | apply Hf; lia].
    + unfold fp2_eq, fp2_add, fp2_zero. cbn [fp_x fp_y]. split; reflexivity.
Qed.

Lemma fermat_pow_id :
  forall a p,
    Z.prime p ->
    (a ^ p) mod p = a mod p.
Proof.
  intros a p Hp.
  pose proof (Z.prime_ge_2 p Hp) as Hp2.
  change (a ^ p mod p) with (powm a p p).
  rewrite <- (powm_mod_base a p p) by lia.
  unfold powm.
  set (b := a mod p).
  destruct (Z.eq_dec b 0) as [Hz | Hnz].
  - rewrite Hz, Z.pow_0_l by lia. reflexivity.
  - assert (Z.coprime b p) as Hcop.
    { rewrite coprime_comm.
      apply Z.coprime_prime_l_iff; [exact Hp|].
      intro Hpb.
      apply Z.mod_divide in Hpb; [|lia].
      unfold b in Hnz, Hpb. rewrite Z.mod_mod in Hpb by lia. lia. }
    pose proof (fermat_coprime p b Hp Hcop) as Hf.
    replace (b ^ p) with (b ^ ((p - 1) + 1)) by (f_equal; lia).
    rewrite Z.pow_add_r by lia.
    rewrite Z.mul_mod, Z.pow_1_r by lia.
    unfold powm in Hf. rewrite Hf, Z.mul_1_l, Z.mod_mod by lia.
    unfold b. rewrite Z.mod_mod; lia.
Qed.

Lemma fp2_pow_sqrt_even :
  forall D k,
    fp2_pow D fp2_sqrt (2 * k) =
      {| fp_x := D ^ Z.of_nat k; fp_y := 0 |}.
Proof.
  intros D k. induction k as [| k IH].
  - simpl. reflexivity.
  - assert ((2 * S k = S (S (2 * k)))%nat) as He by lia.
    rewrite He.
    cbn [fp2_pow]. rewrite IH.
    unfold fp2_mul, fp2_sqrt. cbn [fp_x fp_y].
    f_equal; [| ring].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma fp2_pow_sqrt_odd :
  forall D k,
    fp2_pow D fp2_sqrt (S (2 * k)) =
      {| fp_x := 0; fp_y := D ^ Z.of_nat k |}.
Proof.
  intros D k.
  cbn [fp2_pow].
  replace (k + (k + 0))%nat with (2 * k)%nat by lia.
  rewrite fp2_pow_sqrt_even.
  unfold fp2_mul, fp2_sqrt. cbn [fp_x fp_y].
  f_equal; ring.
Qed.

Lemma nat_odd_prime :
  forall p, Z.prime p -> p <> 2 ->
    Z.to_nat p = S (2 * Z.to_nat ((p - 1) / 2)).
Proof.
  intros p Hp Hne.
  pose proof (Z.prime_ge_2 p Hp).
  pose proof (two_times_half_pm1 p Hp Hne).
  pose proof (half_pm1_nonneg p Hp Hne).
  apply Nat2Z.inj.
  rewrite Z2Nat.id by lia.
  rewrite Nat2Z.inj_succ.
  rewrite Nat2Z.inj_mul.
  rewrite Z2Nat.id by lia.
  change (Z.of_nat 2) with 2.
  lia.
Qed.

Lemma fp2_pow_sqrt_p :
  forall D p,
    Z.prime p ->
    p <> 2 ->
    fp2_eq p
      (fp2_pow D fp2_sqrt (Z.to_nat p))
      {| fp_x := 0; fp_y := D ^ ((p - 1) / 2) |}.
Proof.
  intros D p Hp Hne.
  rewrite (nat_odd_prime p Hp Hne).
  rewrite fp2_pow_sqrt_odd.
  unfold fp2_eq. cbn [fp_x fp_y].
  split; [reflexivity|].
  rewrite Z2Nat.id by (apply half_pm1_nonneg; assumption).
  reflexivity.
Qed.

Lemma fp2_mul_embed_embed :
  forall D a b,
    fp2_mul D (fp2_embed a) (fp2_embed b) = fp2_embed (a * b).
Proof.
  intros. unfold fp2_mul, fp2_embed. cbn [fp_x fp_y]. f_equal; ring.
Qed.

Lemma fp2_mul_embed_comm :
  forall D a u,
    fp2_mul D (fp2_embed a) u = fp2_mul D u (fp2_embed a).
Proof. intros. apply fp2_mul_comm. Qed.

Lemma fp2_embed_pow :
  forall D n k,
    fp2_pow D (fp2_embed n) k = fp2_embed (n ^ Z.of_nat k).
Proof.
  intros D n k. induction k as [| k IH].
  - simpl. unfold fp2_embed, fp2_one. reflexivity.
  - cbn [fp2_pow]. rewrite IH.
    unfold fp2_mul, fp2_embed. cbn [fp_x fp_y].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    f_equal; ring.
Qed.

Lemma fp2_scale_pow :
  forall D n u k,
    fp2_pow D (fp2_mul D (fp2_embed n) u) k =
    fp2_mul D (fp2_embed (n ^ Z.of_nat k)) (fp2_pow D u k).
Proof.
  intros D n u k. induction k as [| k IH].
  - simpl. rewrite fp2_mul_one_r. unfold fp2_embed. reflexivity.
  - cbn [fp2_pow]. rewrite IH.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite <- fp2_mul_assoc.
    rewrite (fp2_mul_assoc D (fp2_embed n) u (fp2_embed (n ^ Z.of_nat k))).
    rewrite (fp2_mul_comm D u (fp2_embed (n ^ Z.of_nat k))).
    rewrite <- fp2_mul_assoc.
    rewrite fp2_mul_embed_embed.
    apply fp2_mul_assoc.
Qed.

Fixpoint zsum (f : nat -> Z) (n : nat) : Z :=
  match n with
  | O => f 0%nat
  | S n' => zsum f n' + f (S n')
  end.

Lemma zsum_ext :
  forall f g n,
    (forall k, (k <= n)%nat -> f k = g k) ->
    zsum f n = zsum g n.
Proof.
  intros f g n H. induction n as [| n IH].
  - simpl. apply H. lia.
  - simpl. rewrite (IH (fun k Hk => H k ltac:(lia))).
    rewrite (H (S n) ltac:(lia)). reflexivity.
Qed.

Lemma zsum_mod :
  forall p f n,
    p <> 0 ->
    (zsum f n) mod p =
    (zsum (fun k => f k mod p) n) mod p.
Proof.
  intros p f n Hp. induction n as [| n IH].
  - simpl. rewrite Z.mod_mod; lia.
  - simpl. rewrite Z.add_mod by lia. rewrite IH.
    rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma zsum_zero_mod :
  forall p f n,
    p <> 0 ->
    (forall k, (k <= n)%nat -> (p | f k)) ->
    (zsum f n) mod p = 0.
Proof.
  intros p f n Hp Hf. induction n as [| n IH].
  - simpl. destruct (Hf 0%nat ltac:(lia)) as [t Ht]. rewrite Ht.
    apply Z.mod_mul; lia.
  - simpl. rewrite Z.add_mod by lia.
    rewrite IH by (intros; apply Hf; lia).
    rewrite Z.add_0_l.
    destruct (Hf (S n) ltac:(lia)) as [t Ht]. rewrite Ht.
    rewrite Z.mod_mod by lia.
    apply Z.mod_mul; lia.
Qed.

Definition gamma (P : Z) : fp2 := {| fp_x := P; fp_y := 1 |}.

Lemma gamma_split :
  forall P, gamma P = fp2_add (fp2_embed P) fp2_sqrt.
Proof. intros. unfold gamma, fp2_add, fp2_embed, fp2_sqrt. cbn [fp_x fp_y]. f_equal; ring. Qed.

Lemma alpha_as_scale :
  forall D P i, alpha P i = fp2_mul D (fp2_embed i) (gamma P).
Proof.
  intros. unfold alpha, fp2_mul, fp2_embed, gamma. cbn [fp_x fp_y].
  f_equal; ring.
Qed.

Lemma beta_as_scale :
  forall D P i, beta P i = fp2_mul D (fp2_embed i) (fp2_conj (gamma P)).
Proof.
  intros. unfold beta, fp2_mul, fp2_embed, fp2_conj, gamma. cbn [fp_x fp_y].
  f_equal; ring.
Qed.

Lemma zsum_uncons :
  forall f n, zsum f (S n) = f 0%nat + zsum (fun k => f (S k)) n.
Proof.
  intros f n. induction n as [| n IH].
  - simpl. ring.
  - change (zsum f (S (S n))) with (zsum f (S n) + f (S (S n))).
    rewrite IH. simpl. ring.
Qed.

Lemma zsum_mul_l :
  forall c f n, c * zsum f n = zsum (fun k => c * f k) n.
Proof.
  intros c f n. induction n as [| n IH].
  - simpl. reflexivity.
  - simpl. rewrite Z.mul_add_distr_l, IH. reflexivity.
Qed.

Lemma zsum_add :
  forall f g n, zsum f n + zsum g n = zsum (fun k => f k + g k) n.
Proof.
  intros f g n. induction n as [| n IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. ring.
Qed.

Lemma zsum_shift :
  forall f n,
    zsum f n =
    zsum (fun k => match k with O => 0 | S k' => f k' end) (S n).
Proof.
  intros f n.
  rewrite zsum_uncons. simpl. reflexivity.
Qed.

Lemma zsum_pad :
  forall f n, f (S n) = 0 -> zsum f n = zsum f (S n).
Proof.
  intros f n Hz. simpl. rewrite Hz. ring.
Qed.

Lemma z_binom :
  forall x y n,
    (x + y) ^ Z.of_nat n =
    zsum (fun k => binom n k * x ^ Z.of_nat (n - k) * y ^ Z.of_nat k) n.
Proof.
  intros x y n. induction n as [| n IH].
  - simpl. ring.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite IH, Z.mul_add_distr_r, !zsum_mul_l.
    rewrite (zsum_ext (fun k => x * (binom n k * x ^ Z.of_nat (n - k) * y ^ Z.of_nat k))
                      (fun k => binom n k * x ^ Z.of_nat (S n - k) * y ^ Z.of_nat k) n).
    2: { intros k Hk.
         replace (S n - k)%nat with (S (n - k)) by lia.
         rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring. }
    rewrite (zsum_ext (fun k => y * (binom n k * x ^ Z.of_nat (n - k) * y ^ Z.of_nat k))
                      (fun k => binom n k * x ^ Z.of_nat (n - k) * y ^ Z.of_nat (S k)) n).
    2: { intros k Hk. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring. }
    rewrite (zsum_pad (fun k => binom n k * x ^ Z.of_nat (S n - k) * y ^ Z.of_nat k) n).
    2: { rewrite binom_gt by lia. ring. }
    rewrite (zsum_shift
               (fun k => binom n k * x ^ Z.of_nat (n - k) * y ^ Z.of_nat (S k)) n).
    rewrite zsum_add.
    apply zsum_ext. intros k Hk.
    destruct k as [| k'].
    + rewrite !binom_n_0. ring.
    + rewrite binom_S_S_expand.
      replace (S n - S k')%nat with (n - k')%nat by lia.
      ring.
Qed.

Lemma z_freshman :
  forall x y p,
    Z.prime p ->
    ((x + y) ^ p) mod p = (x ^ p + y ^ p) mod p.
Proof.
  intros x y p Hp.
  pose proof (Z.prime_ge_2 p Hp) as Hp2.
  set (q := Z.to_nat p).
  assert (Hq : Z.of_nat q = p) by (subst q; apply Z2Nat.id; lia).
  assert (Hqn : (2 <= q)%nat).
  { subst q. apply Nat2Z.inj_le. rewrite Z2Nat.id; lia. }
  rewrite <- Hq, z_binom.
  destruct q as [| q']; [lia|].
  destruct q' as [| q'']; [lia|].
  rewrite zsum_uncons.
  rewrite binom_n_0, Nat.sub_0_r, Z.pow_0_r, !Z.mul_1_r, Z.mul_1_l.
  replace (zsum
             (fun k => binom (S (S q'')) (S k) *
                       x ^ Z.of_nat (S (S q'') - S k) * y ^ Z.of_nat (S k))
             (S q''))
    with (zsum
            (fun k => binom (S (S q'')) (S k) *
                      x ^ Z.of_nat (S (S q'') - S k) * y ^ Z.of_nat (S k))
            q'' +
          binom (S (S q'')) (S (S q'')) * x ^ Z.of_nat (S (S q'') - S (S q'')) *
          y ^ Z.of_nat (S (S q'')))
    by reflexivity.
  rewrite Nat.sub_diag, binom_n_n, Z.pow_0_r, !Z.mul_1_l.
  rewrite Hq.
  set (mid := zsum
                (fun k => binom (S (S q'')) (S k) *
                          x ^ Z.of_nat (S (S q'') - S k) * y ^ Z.of_nat (S k))
                q'').
  assert (Hmid : mid mod p = 0).
  { apply zsum_zero_mod; [lia|].
    intros k Hk.
    destruct (prime_divides_binom (S (S q'')) (S k)
                ltac:(rewrite Hq; exact Hp) ltac:(lia)) as [t Ht].
    exists (t * x ^ Z.of_nat (S (S q'') - S k) * y ^ Z.of_nat (S k)).
    rewrite Ht, Hq. ring. }
  unfold mid.
  rewrite Z.add_assoc, (Z.add_mod (x ^ p + mid)) by lia.
  replace ((x ^ p + mid) mod p) with (x ^ p mod p).
  2: { rewrite Z.add_mod, Hmid, Z.add_0_r, Z.mod_mod; lia. }
  rewrite <- Z.add_mod; lia.
Qed.

Lemma fp2_sum_uncons :
  forall f n,
    fp2_sum f (S n) = fp2_add (f 0%nat) (fp2_sum (fun k => f (S k)) n).
Proof.
  intros f n. induction n as [| n IH].
  - simpl. unfold fp2_add. destruct (f 0%nat), (f 1%nat). cbn. f_equal; ring.
  - cbn [fp2_sum].
    change (fp2_add (fp2_sum f n) (f (S n))) with (fp2_sum f (S n)).
    rewrite IH. unfold fp2_add.
    destruct (f 0%nat), (fp2_sum (fun k => f (S k)) n), (f (S (S n))).
    cbn [fp_x fp_y]. f_equal; ring.
Qed.

Lemma fp2_sum_shift :
  forall f n,
    fp2_sum f n =
    fp2_sum (fun k => match k with O => fp2_zero | S k' => f k' end) (S n).
Proof.
  intros f n. rewrite fp2_sum_uncons. simpl.
  unfold fp2_add, fp2_zero. destruct (fp2_sum f n). cbn. f_equal; ring.
Qed.

Lemma fp2_sum_pad :
  forall f n, f (S n) = fp2_zero -> fp2_sum f n = fp2_sum f (S n).
Proof.
  intros f n Hz. simpl. rewrite Hz.
  unfold fp2_add, fp2_zero. destruct (fp2_sum f n). cbn. f_equal; ring.
Qed.

Lemma fp2_sum_add :
  forall f g n,
    fp2_add (fp2_sum f n) (fp2_sum g n) =
    fp2_sum (fun k => fp2_add (f k) (g k)) n.
Proof.
  intros f g n. induction n as [| n IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. unfold fp2_add.
    destruct (fp2_sum f n), (fp2_sum g n), (f (S n)), (g (S n)).
    cbn. f_equal; ring.
Qed.

Lemma fp2_mul_scale :
  forall D u c w,
    fp2_mul D u (fp2_scale c w) = fp2_scale c (fp2_mul D u w).
Proof.
  intros D [x1 y1] c [x2 y2].
  unfold fp2_mul, fp2_scale. cbn [fp_x fp_y]. f_equal; ring.
Qed.

Lemma fp2_scale_zero :
  forall c, fp2_scale c fp2_zero = fp2_zero.
Proof. intros. unfold fp2_scale, fp2_zero. cbn. f_equal; ring. Qed.

Definition fp2_binterm (D : Z) (u v : fp2) (n k : nat) : fp2 :=
  fp2_scale (binom n k) (fp2_mul D (fp2_pow D u (n - k)) (fp2_pow D v k)).

Lemma fp2_sum_ext_eq :
  forall f g n,
    (forall k, (k <= n)%nat -> f k = g k) ->
    fp2_sum f n = fp2_sum g n.
Proof.
  intros f g n H. induction n as [| n IH].
  - simpl. apply H. lia.
  - simpl. rewrite (IH (fun k Hk => H k ltac:(lia))), (H (S n) ltac:(lia)).
    reflexivity.
Qed.

Lemma fp2_sum_scale_mul :
  forall D u f n,
    fp2_mul D u (fp2_sum f n) = fp2_sum (fun k => fp2_mul D u (f k)) n.
Proof.
  intros D u f n. induction n as [| n IH].
  - simpl. reflexivity.
  - simpl. rewrite fp2_mul_add_r, IH. reflexivity.
Qed.

Lemma fp2_binterm_gt :
  forall D u v n k,
    (n < k)%nat -> fp2_binterm D u v n k = fp2_zero.
Proof.
  intros D u v n k Hlt. unfold fp2_binterm.
  rewrite binom_gt by lia.
  unfold fp2_scale, fp2_zero. cbn [fp_x fp_y]. f_equal; ring.
Qed.

Lemma fp2_binom :
  forall D u v n,
    fp2_pow D (fp2_add u v) n = fp2_sum (fp2_binterm D u v n) n.
Proof.
  intros D u v n. induction n as [| n IH].
  - unfold fp2_pow, fp2_sum, fp2_binterm.
    rewrite Nat.sub_diag. cbn [fp2_pow].
    rewrite fp2_mul_one_r.
    unfold fp2_scale, fp2_one. destruct u. cbn [fp_x fp_y]. f_equal; ring.
  - cbn [fp2_pow]. rewrite IH.
    rewrite fp2_mul_add_l.
    rewrite (fp2_sum_scale_mul D u (fp2_binterm D u v n) n).
    rewrite (fp2_sum_scale_mul D v (fp2_binterm D u v n) n).
    rewrite (fp2_sum_ext_eq
               (fun k => fp2_mul D u (fp2_binterm D u v n k))
               (fun k => fp2_scale (binom n k)
                           (fp2_mul D (fp2_pow D u (S n - k)) (fp2_pow D v k))) n).
    2: { intros k Hk. unfold fp2_binterm. rewrite fp2_mul_scale.
         replace (S n - k)%nat with (S (n - k)) by lia.
         cbn [fp2_pow]. rewrite <- fp2_mul_assoc. reflexivity. }
    rewrite (fp2_sum_ext_eq
               (fun k => fp2_mul D v (fp2_binterm D u v n k))
               (fun k => fp2_scale (binom n k)
                           (fp2_mul D (fp2_pow D u (n - k)) (fp2_pow D v (S k)))) n).
    2: { intros k Hk. unfold fp2_binterm. rewrite fp2_mul_scale.
         rewrite (fp2_mul_comm D v (fp2_mul D (fp2_pow D u (n - k)) (fp2_pow D v k))).
         rewrite fp2_mul_assoc.
         rewrite <- (fp2_pow_add_r D v k). reflexivity. }
    rewrite (fp2_sum_pad
               (fun k => fp2_scale (binom n k)
                           (fp2_mul D (fp2_pow D u (S n - k)) (fp2_pow D v k))) n).
    2: { rewrite binom_gt by lia.
         unfold fp2_scale, fp2_zero. cbn [fp_x fp_y]. f_equal; ring. }
    rewrite (fp2_sum_shift
               (fun k => fp2_scale (binom n k)
                           (fp2_mul D (fp2_pow D u (n - k)) (fp2_pow D v (S k)))) n).
    rewrite fp2_sum_add.
    apply fp2_sum_ext_eq. intros k Hk.
    destruct k as [| k'].
    + unfold fp2_binterm. rewrite !binom_n_0.
      unfold fp2_add, fp2_zero, fp2_scale. cbn [fp_x fp_y].
      destruct (fp2_mul D (fp2_pow D u (S n - 0)) (fp2_pow D v 0)).
      cbn. f_equal; ring.
    + unfold fp2_binterm. rewrite binom_S_S_expand.
      replace (S n - S k')%nat with (n - k')%nat by lia.
      unfold fp2_scale, fp2_add.
      destruct (fp2_mul D (fp2_pow D u (n - k')) (fp2_pow D v (S k'))).
      cbn [fp_x fp_y]. f_equal; ring.
Qed.

Lemma fp2_scale_one :
  forall u, fp2_scale 1 u = {| fp_x := fp_x u; fp_y := fp_y u |}.
Proof. intros [x y]. unfold fp2_scale. cbn [fp_x fp_y]. f_equal; ring. Qed.

Lemma fp2_freshman :
  forall D u v p,
    Z.prime p ->
    fp2_eq p
      (fp2_pow D (fp2_add u v) (Z.to_nat p))
      (fp2_add (fp2_pow D u (Z.to_nat p)) (fp2_pow D v (Z.to_nat p))).
Proof.
  intros D u v p Hp.
  pose proof (Z.prime_ge_2 p Hp) as Hp2.
  set (q := Z.to_nat p).
  assert (Hq : Z.of_nat q = p) by (subst q; apply Z2Nat.id; lia).
  assert ((2 <= q)%nat).
  { subst q. apply Nat2Z.inj_le. rewrite Z2Nat.id; lia. }
  rewrite fp2_binom.
  destruct q as [| q']; [lia|].
  destruct q' as [| q'']; [lia|].
  rewrite fp2_sum_uncons.
  unfold fp2_binterm at 1.
  rewrite binom_n_0, Nat.sub_0_r.
  change (fp2_pow D v 0) with fp2_one.
  rewrite fp2_mul_one_r, fp2_scale_one.
  set (uq := fp2_pow D u (S (S q''))).
  set (vq := fp2_pow D v (S (S q''))).
  replace {| fp_x := fp_x uq; fp_y := fp_y uq |} with uq
    by (subst uq; destruct (fp2_pow D u (S (S q''))); reflexivity).
  replace (fp2_sum (fun k => fp2_binterm D u v (S (S q'')) (S k)) (S q''))
    with (fp2_add (fp2_sum (fun k => fp2_binterm D u v (S (S q'')) (S k)) q'')
                  (fp2_binterm D u v (S (S q'')) (S (S q''))))
    by reflexivity.
  replace (fp2_binterm D u v (S (S q'')) (S (S q''))) with vq.
  2: { unfold fp2_binterm. rewrite binom_n_n, Nat.sub_diag.
       change (fp2_pow D u 0) with fp2_one.
       rewrite (fp2_mul_comm D fp2_one (fp2_pow D v (S (S q'')))).
       rewrite fp2_mul_one_r, fp2_scale_one.
       subst vq. destruct (fp2_pow D v (S (S q''))); reflexivity. }
  apply fp2_eq_trans with (v := fp2_add uq (fp2_add fp2_zero vq)).
  - apply fp2_eq_add; [lia | apply fp2_eq_refl; lia |].
    apply fp2_eq_add; [lia | | apply fp2_eq_refl; lia].
    apply fp2_sum_zero; [exact Hp|].
    intros k Hk.
    unfold fp2_binterm.
    destruct (prime_divides_binom (S (S q'')) (S k)
                ltac:(rewrite Hq; exact Hp) ltac:(lia)) as [t Ht].
    rewrite Ht, Hq.
    apply fp2_scale_mul_div; [exact Hp|].
    exists t. reflexivity.
  - unfold fp2_eq, fp2_add, fp2_zero. cbn [fp_x fp_y].
    split; rewrite Z.add_0_l; reflexivity.
Qed.

Lemma fp2_eq_embed :
  forall p a b,
    p <> 0 ->
    a mod p = b mod p ->
    fp2_eq p (fp2_embed a) (fp2_embed b).
Proof. intros. unfold fp2_eq, fp2_embed. cbn. split; [assumption | reflexivity]. Qed.

Lemma fp2_pow_S_to_nat :
  forall D u p,
    0 <= p ->
    fp2_pow D u (Z.to_nat (p + 1)) = fp2_mul D u (fp2_pow D u (Z.to_nat p)).
Proof.
  intros D u p Hp.
  replace (Z.to_nat (p + 1)) with (S (Z.to_nat p)).
  - reflexivity.
  - rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. lia.
Qed.

Lemma euler_pow_half :
  forall a p,
    Z.prime p ->
    p <> 2 ->
    euler_crit a p = (a ^ ((p - 1) / 2)) mod p.
Proof. intros. unfold euler_crit, powm. reflexivity. Qed.

Lemma fp2_conj_mul_ok :
  forall D u v, fp2_conj (fp2_mul D u v) = fp2_mul D (fp2_conj u) (fp2_conj v).
Proof.
  intros D [x1 y1] [x2 y2].
  unfold fp2_conj, fp2_mul. cbn [fp_x fp_y]. f_equal; ring.
Qed.

Lemma fp2_pow_conj :
  forall D u n,
    fp2_pow D (fp2_conj u) n = fp2_conj (fp2_pow D u n).
Proof.
  intros D u n. induction n as [| n IH].
  - simpl. unfold fp2_conj, fp2_one. cbn. f_equal; ring.
  - cbn [fp2_pow]. rewrite IH, fp2_conj_mul_ok. reflexivity.
Qed.

Lemma gamma_pow_p :
  forall P D p,
    D = P * P - 4 ->
    Z.prime p ->
    p <> 2 ->
    euler_crit D p = p - 1 ->
    fp2_eq p (fp2_pow D (gamma P) (Z.to_nat p))
             {| fp_x := P; fp_y := -1 |}.
Proof.
  intros P D p HD Hp Hne Heu.
  pose proof (Z.prime_ge_2 p Hp) as Hp2.
  rewrite gamma_split.
  pose proof (fp2_freshman D (fp2_embed P) fp2_sqrt p Hp) as Hfr.
  apply fp2_eq_trans with
    (v := fp2_add (fp2_pow D (fp2_embed P) (Z.to_nat p))
                  (fp2_pow D fp2_sqrt (Z.to_nat p))); [exact Hfr|].
  rewrite fp2_embed_pow, Z2Nat.id by lia.
  pose proof (fp2_pow_sqrt_p D p Hp Hne) as Hsq.
  apply fp2_eq_trans with
    (v := fp2_add (fp2_embed (P ^ p))
                  {| fp_x := 0; fp_y := D ^ ((p - 1) / 2) |}).
  { apply fp2_eq_add; [lia | apply fp2_eq_refl; lia | exact Hsq]. }
  unfold fp2_eq, fp2_add, fp2_embed. cbn [fp_x fp_y].
  unfold euler_crit, powm in Heu.
  split.
  - rewrite Z.add_0_r. apply fermat_pow_id. exact Hp.
  - rewrite Z.add_0_l, Heu.
    replace (-1) with (p - 1 + (-1) * p) by ring.
    rewrite Z.mod_add by lia.
    rewrite (Z.mod_small (p - 1) p) by lia. reflexivity.
Qed.

Lemma alpha_pow_p_is_beta :
  forall P i p D,
    D = P * P - 4 ->
    Z.prime p ->
    p <> 2 ->
    (2 * i) mod p = 1 ->
    euler_crit D p = p - 1 ->
    fp2_eq p (fp2_pow D (alpha P i) (Z.to_nat p)) (beta P i).
Proof.
  intros P i p D HD Hp Hne Hi Heu.
  pose proof (Z.prime_ge_2 p Hp) as Hp2.
  rewrite (alpha_as_scale D), fp2_scale_pow, Z2Nat.id by lia.
  pose proof (gamma_pow_p P D p HD Hp Hne Heu) as Hg.
  apply fp2_eq_trans with
    (v := fp2_mul D (fp2_embed (i ^ p)) {| fp_x := P; fp_y := -1 |}).
  { apply fp2_eq_mul; [lia | apply fp2_eq_refl; lia | exact Hg]. }
  unfold fp2_eq, fp2_mul, fp2_embed, beta. cbn [fp_x fp_y].
  split.
  - rewrite Z.mul_0_r, Z.add_0_r.
    rewrite Z.mul_mod, (fermat_pow_id i p Hp), <- Z.mul_mod by lia.
    rewrite (Z.mul_comm i P). reflexivity.
  - assert (i ^ p * -1 + 0 * P = - (i ^ p)) as Hyeq by ring.
    rewrite Hyeq.
    transitivity ((- (i ^ p mod p)) mod p).
    { apply opp_mod_compat. lia. }
    rewrite (fermat_pow_id i p Hp).
    symmetry. apply opp_mod_compat. lia.
Qed.

Lemma beta_is_conj_alpha :
  forall P i, beta P i = fp2_conj (alpha P i).
Proof. intros. unfold beta, alpha, fp2_conj. reflexivity. Qed.

Lemma fp2_conj_one :
  fp2_conj fp2_one = fp2_one.
Proof. unfold fp2_conj, fp2_one. cbn. f_equal; ring. Qed.

Lemma fp2_eq_conj :
  forall p u v,
    p <> 0 ->
    fp2_eq p u v ->
    fp2_eq p (fp2_conj u) (fp2_conj v).
Proof.
  intros p u v Hp [A B]. unfold fp2_eq, fp2_conj. cbn [fp_x fp_y].
  split; [exact A|].
  rewrite (opp_mod_compat (fp_y u) p Hp), B,
    <- (opp_mod_compat (fp_y v) p Hp). reflexivity.
Qed.

Theorem williams_eval_of_qnr :
  forall P p,
    Z.prime p ->
    2 < p ->
    Z.coprime (P * P - 4) p ->
    euler_crit (P * P - 4) p = p - 1 ->
    williams_eval P p.
Proof.
  intros P p Hp Hgt Hcop Heu.
  assert (Hne : p <> 2) by lia.
  unfold williams_eval. split; [exact Hgt|].
  destruct (inv2_exists p Hp Hne) as [i Hi].
  set (D := P * P - 4).
  pose proof (Z.prime_ge_2 p Hp) as Hp2.
  pose proof (lucasV_as_fp2 P i p D (Z.to_nat (p + 1))
                Hp Hne eq_refl Hi) as HV.
  pose proof (alpha_pow_p_is_beta P i p D eq_refl Hp Hne Hi Heu) as Hap.
  pose proof (fp2_pow_S_to_nat D (alpha P i) p ltac:(lia)) as HSa.
  assert (Ha1 : fp2_eq p (fp2_pow D (alpha P i) (Z.to_nat (p + 1))) fp2_one).
  { rewrite HSa.
    apply fp2_eq_trans with (v := fp2_mul D (alpha P i) (beta P i)).
    { apply fp2_eq_mul; [lia | apply fp2_eq_refl; lia | exact Hap]. }
    apply alpha_beta_is_one; [exact Hp | exact Hne | reflexivity | exact Hi]. }
  assert (Hb1 : fp2_eq p (fp2_pow D (beta P i) (Z.to_nat (p + 1))) fp2_one).
  { rewrite beta_is_conj_alpha, fp2_pow_conj.
    apply fp2_eq_trans with (v := fp2_conj fp2_one).
    { apply fp2_eq_conj; [lia | exact Ha1]. }
    unfold fp2_eq, fp2_conj, fp2_one. cbn. split; reflexivity. }
  unfold fp2_eq, fp2_embed in HV.
  cbn [fp_x fp_y] in HV.
  destruct HV as [HVx _].
  rewrite <- HVx.
  unfold fp2_eq, fp2_one in Ha1, Hb1.
  destruct Ha1 as [Ha1x _], Hb1 as [Hb1x _].
  unfold fp2_add. cbn [fp_x fp_y].
  rewrite Z.add_mod, Ha1x, Hb1x by lia.
  rewrite <- Z.add_mod by lia.
  apply Z.mod_small. lia.
Qed.
