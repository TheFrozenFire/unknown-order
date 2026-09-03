From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(** Trial-to-[√p] primality, so [pin_p_prime] / [pin_q_prime] follow
    [pin_p] / [pin_q] by [vm_compute] of [Z.sqrt] rather than a
    handwritten [1..p−1] case split. *)
Lemma Zprime_sqrt :
  forall p,
    1 < p ->
    (forall d, 1 < d <= Z.sqrt p -> ~ (d | p)) ->
    Z.prime p.
Proof.
  intros p Hp Hall. split; [exact Hp|].
  intros n [Hn1 Hn2] Hdiv.
  assert (Hp0 : 0 <= p) by lia.
  pose proof (Z.sqrt_spec p Hp0) as Hs.
  change (Z.sqrt p * Z.sqrt p <= p < Z.succ (Z.sqrt p) * Z.succ (Z.sqrt p)) in Hs.
  destruct Hs as [Hs1 Hs2].
  destruct (Z.le_gt_cases n (Z.sqrt p)) as [Hle | Hgt].
  - apply (Hall n); [lia | exact Hdiv].
  - unfold Z.divide in Hdiv. destruct Hdiv as [k Hk].
    assert (Hnpos : 1 < n) by lia.
    assert (1 < k) by nia.
    assert (Hnbound : Z.succ (Z.sqrt p) <= n) by lia.
    assert (Hks : k * Z.succ (Z.sqrt p) <= k * n).
    { apply Z.mul_le_mono_nonneg_l; nia. }
    rewrite <- Hk in Hks.
    assert (Hstrict : k * Z.succ (Z.sqrt p) < Z.succ (Z.sqrt p) * Z.succ (Z.sqrt p)) by lia.
    assert (Hspos : 0 < Z.succ (Z.sqrt p)) by lia.
    rewrite (Z.mul_comm k (Z.succ (Z.sqrt p))) in Hstrict.
    apply Z.mul_lt_mono_pos_l in Hstrict; [|exact Hspos].
    apply (Hall k); [lia|].
    unfold Z.divide. exists n. rewrite Z.mul_comm. exact Hk.
Qed.



(** * Campaign pin — numerical source of truth

    Twin of [cas/lib/pin.gp].  This file is the only place the
    textbook inhabitant's integers are written.  [RSA.v] builds
    [rsa_test] from these names; other files import [Pin] and
    consume [pin_N], [pin_p], … rather than restating [187].

    To change the campaign pin: edit this file and [cas/lib/pin.gp]
    together.  Algebra that mentions [pin_N] re-validates on
    [vm_compute]; algebra that still writes a literal [187] will
    not follow.

    **Classes of [N] in this tree**

    - Default: odd distinct-prime semiprime ([pin_p], [pin_q]).
    - Named extras (same file, not a second default): [pin_extra_77]
      (safeprime-shaped), [pin_extra_91] (cubic kernel),
      [pin_extra_247] (matching orders), [pin_extra_253] (Williams),
      [pin_extra_45] (Takagi [p²q]), [pin_extra_105] (triprime),
      [pin_extra_Nsq] (Paillier carrier).

    Computed attachments (Dixon residues, NFS quadratics) live here
    because they are *data of this inhabitant*, not a different
    modulus class. *)

(** ** Default semiprime

    Abbreviations so [lia] sees the integers (a [Definition] stays
    opaque to [lia]).  Edit these lines to change the inhabitant. *)

Notation pin_p := 11.
Notation pin_q := 17.
Notation pin_N := (pin_p * pin_q).
Notation pin_e := 3.
Notation pin_d := 27.
Notation pin_y := 36.
Notation pin_x := 42.
Notation pin_lam := 80.
Notation pin_phi := 160.
(** Unit of order [λ]; local orders; leftover mismatch exponent;
    [3⁻¹] mod [p−1] / [q−1]; order of [2] locally; order of leftover [y]. *)
Notation pin_g := 3.
Notation pin_g_ord_p := 5.
Notation pin_g_ord_q := 16.
Notation pin_y_ord := 40.
Notation pin_y_ord_p := 5.
Notation pin_y_ord_q := 8.
Notation pin_x_k := 5.
Notation pin_inv3_p := 7.
Notation pin_inv3_q := 11.
Notation pin_ord2_p := 10.
Notation pin_ord2_q := 8.
(** CRT binomial [c_p X^{d_p} + c_q X^{d_q}] of the [e]-th root map:
    [c_p ≡ 1 (mod p)], [0 (mod q)]; [c_q] swapped.  Coefficients
    split [N]; the monomial [X^d] does not. *)
Definition pin_root_ca : Z := 34.
Definition pin_root_cb : Z := 154.

Lemma pin_N_pos : 0 < pin_N.
Proof. lia. Qed.

Lemma pin_N_gt_1 : 1 < pin_N.
Proof. lia. Qed.

Lemma pin_p_neq_q : pin_p <> pin_q.
Proof. discriminate. Qed.

Lemma pin_p_lt_q : pin_p < pin_q.
Proof. lia. Qed.

Lemma pin_p_prime : Z.prime pin_p.
Proof.
  apply Zprime_sqrt; [lia|].
  intros d Hd Hdiv.
  apply Z.mod_divide in Hdiv; [|lia].
  change (Z.sqrt pin_p) with 3 in Hd.
  assert (d = 2 \/ d = 3) by lia.
  intuition subst; vm_compute in Hdiv; discriminate.
Qed.

Lemma pin_q_prime : Z.prime pin_q.
Proof.
  apply Zprime_sqrt; [lia|].
  intros d Hd Hdiv.
  apply Z.mod_divide in Hdiv; [|lia].
  change (Z.sqrt pin_q) with 4 in Hd.
  assert (d = 2 \/ d = 3 \/ d = 4) by lia.
  intuition subst; vm_compute in Hdiv; discriminate.
Qed.

(** ** Residual pair on the default pin *)

Definition pin_residual_y : Z := pin_y.
Definition pin_residual_x : Z := pin_x.
Definition pin_residual_e : Z := pin_e.

(** ** Mixed square roots of 1 on [pin_N] *)

Definition pin_sqrt1_mixed : Z := 67.
Definition pin_sqrt1_mixed2 : Z := 120.

(** ** Named extra moduli (p, q, N, λ, and shared witnesses)

    Each extra is a second inhabitant of the same *class* (odd
    distinct-prime product, except Takagi / triprime / [N²]).
    Consumers import these names rather than restating [13*7]. *)

Notation pin_77_p := 7.
Notation pin_77_q := 11.
Notation pin_77 := (pin_77_p * pin_77_q).
Notation pin_77_lam := 30.
Notation pin_77_y := 51.
Notation pin_77_x := 2.
Notation pin_77_e := 7.

Notation pin_91_p := 13.
Notation pin_91_q := 7.
Notation pin_91 := (pin_91_p * pin_91_q).
Notation pin_91_lam := 12.
Notation pin_91_om_p := 3.
Notation pin_91_om_q := 2.
Notation pin_91_gp := 29.
Notation pin_91_gq := 79.
Notation pin_91_diag := 16.

Notation pin_247_p := 13.
Notation pin_247_q := 19.
Notation pin_247 := (pin_247_p * pin_247_q).
Notation pin_247_lam := 36.
Notation pin_247_y := 69.
Notation pin_247_x := 179.
Notation pin_247_e := 5.
Notation pin_247_noncube := 7.

Notation pin_253_p := 11.
Notation pin_253_q := 23.
Notation pin_253 := (pin_253_p * pin_253_q).
Notation pin_253_lam := 110.

Notation pin_45_p := 3.
Notation pin_45_q := 5.
Notation pin_45 := (pin_45_p * pin_45_p * pin_45_q).
Notation pin_45_lam := 12.

Notation pin_105_p := 3.
Notation pin_105_q := 5.
Notation pin_105_r := 7.
Notation pin_105 := (pin_105_p * pin_105_q * pin_105_r).
Notation pin_105_lam := 12.

Notation pin_Nsq := (pin_N * pin_N).

Definition pin_extra_77 : Z := pin_77.
Definition pin_extra_91 : Z := pin_91.
Definition pin_extra_247 : Z := pin_247.
Definition pin_extra_253 : Z := pin_253.
Definition pin_extra_45 : Z := pin_45.
Definition pin_extra_105 : Z := pin_105.
Definition pin_extra_Nsq : Z := pin_Nsq.

(** ** Dixon / QS witnesses on [pin_N]

    B-smooth squares that combine to a square.  Replace these
    integers when [pin_N] changes; [SieveRelation] consumes the
    names. *)

Definition pin_dixon_a : Z := 15.
Definition pin_dixon_b : Z := 47.
Definition pin_dixon_r : Z := 38.
Definition pin_dixon_s : Z := 152.
Definition pin_dixon_t : Z := 76.

Definition pin_dixon_b2 : Z := 47.
Definition pin_dixon_s2 : Z := 152.
Definition pin_dixon_t2 : Z := 76.

Definition pin_asquare_a : Z := 14.
Definition pin_asquare_t : Z := 3.

(** ** NFS quadratics on [pin_N] *)

Definition pin_nfs_irr_c0 : Z := 5.
Definition pin_nfs_irr_c1 : Z := 1.
Definition pin_nfs_irr_c2 : Z := 1.
Definition pin_nfs_irr_m : Z := 13.

Definition pin_nfs_red_c0 : Z := -5.
Definition pin_nfs_red_c1 : Z := 4.
Definition pin_nfs_red_c2 : Z := 1.
Definition pin_nfs_red_m : Z := 12.

Definition pin_ts_a1 : Z := 1.
Definition pin_ts_b1 : Z := 0.
Definition pin_ts_a2 : Z := 1.
Definition pin_ts_b2 : Z := 0.
Definition pin_ts_T : Z := 1.
Definition pin_ts_U : Z := 1.
Definition pin_ts_y : Z := 1.

Definition pin_os_a : Z := 1.
Definition pin_os_b : Z := 1.
Definition pin_os_gs : Z := 3.
Definition pin_os_fs : Z := 4.
