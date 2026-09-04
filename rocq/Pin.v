From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(** Trial-to-[√p] primality, so [pin_p_prime] / [pin_q_prime] follow
    the campaign alias by [vm_compute] of [Z.sqrt] rather than a
    handwritten [1..p−1] case split.  Frozen pins have their own
    [pin187_p_prime] / [pin1363_p_prime] / … copies. *)
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



(** * Pins

    Twin of [cas/lib/pin.gp].  Frozen pins ([pin187_*], [pin1363_*],
    [pin2491_*], and the named extras) are never rewritten by
    [swap_pin.py].  Accident residues (cubing cycles, leftover map
    outputs) live on the frozen pin they belong to.

    [pin_*] is the *campaign alias*.  [swap_pin.py] retargets only
    the alias block.  Theorems that are identities of an appropriate
    [N=pq] consume [pin_*].  Theorems about 187-only residues consume
    [pin187_*].

    Default alias: [pin187] ([11·17=187]).  Test pins: [pin1363]
    ([29·47]), [pin2491] ([47·53]).  After a swap test, retarget
    back to [pin187].

    Named extras (same file, not a campaign default): [pin_77]
    (safeprime-shaped), [pin_91] (cubic kernel), [pin_247]
    (matching orders), [pin_253] (Williams), [pin_45] (Takagi
    [p²q]), [pin_105] (triprime), [pin_Nsq] (Paillier carrier). *)

(** ** pin187 — textbook inhabitant [11·17=187] *)

Notation pin187_p := 11.
Notation pin187_q := 17.
Notation pin187_N := (pin187_p * pin187_q).
Notation pin187_e := 3.
Notation pin187_d := 27.
Notation pin187_y := 36.
Notation pin187_x := 42.
Notation pin187_lam := 80.
Notation pin187_phi := 160.
Notation pin187_g := 3.
Notation pin187_g_ord_p := 5.
Notation pin187_g_ord_q := 16.
Notation pin187_y_ord := 40.
Notation pin187_y_ord_p := 5.
Notation pin187_y_ord_q := 8.
Notation pin187_x_k := 5.
Notation pin187_inv3_p := 7.
Notation pin187_inv3_q := 11.
Notation pin187_ord2_p := 10.
Notation pin187_ord2_q := 8.

Definition pin187_root_ca : Z := 34.
Definition pin187_root_cb : Z := 154.
Definition pin187_sqrt1_mixed : Z := 67.
Definition pin187_sqrt1_mixed2 : Z := 120.
Definition pin187_dixon_a : Z := 15.
Definition pin187_dixon_b : Z := 47.
Definition pin187_dixon_r : Z := 38.
Definition pin187_dixon_s : Z := 152.
Definition pin187_dixon_t : Z := 76.
Definition pin187_dixon_b2 : Z := 47.
Definition pin187_dixon_s2 : Z := 152.
Definition pin187_dixon_t2 : Z := 76.
Definition pin187_asquare_a : Z := 14.
Definition pin187_asquare_t : Z := 3.
Definition pin187_nfs_irr_c0 : Z := 5.
Definition pin187_nfs_irr_c1 : Z := 1.
Definition pin187_nfs_irr_c2 : Z := 1.
Definition pin187_nfs_irr_m : Z := 13.
Definition pin187_nfs_red_c0 : Z := -5.
Definition pin187_nfs_red_c1 : Z := 4.
Definition pin187_nfs_red_c2 : Z := 1.
Definition pin187_nfs_red_m : Z := 12.
Definition pin187_ts_a1 : Z := 1.
Definition pin187_ts_b1 : Z := 0.
Definition pin187_ts_a2 : Z := 1.
Definition pin187_ts_b2 : Z := 0.
Definition pin187_ts_T : Z := 1.
Definition pin187_ts_U : Z := 1.
Definition pin187_ts_y : Z := 1.
Definition pin187_os_a : Z := 1.
Definition pin187_os_b : Z := 1.
Definition pin187_os_gs : Z := 3.
Definition pin187_os_fs : Z := 4.

Lemma pin187_N_pos : 0 < pin187_N.
Proof. lia. Qed.

Lemma pin187_N_gt_1 : 1 < pin187_N.
Proof. lia. Qed.

Lemma pin187_p_neq_q : pin187_p <> pin187_q.
Proof. discriminate. Qed.

Lemma pin187_p_lt_q : pin187_p < pin187_q.
Proof. lia. Qed.

Lemma pin187_p_prime : Z.prime pin187_p.
Proof.
  apply Zprime_sqrt; [lia|].
  intros d Hd Hdiv.
  apply Z.mod_divide in Hdiv; [|lia].
  change (Z.sqrt pin187_p) with 3 in Hd.
  assert (d = 2 \/ d = 3) by lia.
  intuition subst; vm_compute in Hdiv; discriminate.
Qed.

Lemma pin187_q_prime : Z.prime pin187_q.
Proof.
  apply Zprime_sqrt; [lia|].
  intros d Hd Hdiv.
  apply Z.mod_divide in Hdiv; [|lia].
  change (Z.sqrt pin187_q) with 4 in Hd.
  assert (d = 2 \/ d = 3 \/ d = 4) by lia.
  intuition subst; vm_compute in Hdiv; discriminate.
Qed.


(** ** pin1363 — swap-test [29·47=1363] *)

Notation pin1363_p := 29.
Notation pin1363_q := 47.
Notation pin1363_N := (pin1363_p * pin1363_q).
Notation pin1363_e := 3.
Notation pin1363_d := 215.
Notation pin1363_y := 486.
Notation pin1363_x := 42.
Notation pin1363_lam := 644.
Notation pin1363_phi := 1288.
Notation pin1363_g := 3.
Notation pin1363_g_ord_p := 28.
Notation pin1363_g_ord_q := 23.
Notation pin1363_y_ord := 322.
Notation pin1363_y_ord_p := 14.
Notation pin1363_y_ord_q := 23.
Notation pin1363_x_k := 14.
Notation pin1363_inv3_p := 19.
Notation pin1363_inv3_q := 31.
Notation pin1363_ord2_p := 28.
Notation pin1363_ord2_q := 23.

Definition pin1363_root_ca : Z := 987.
Definition pin1363_root_cb : Z := 377.
Definition pin1363_sqrt1_mixed : Z := 610.
Definition pin1363_sqrt1_mixed2 : Z := 753.
Definition pin1363_dixon_a : Z := 37.
Definition pin1363_dixon_b : Z := 43.
Definition pin1363_dixon_r : Z := 6.
Definition pin1363_dixon_s : Z := 486.
Definition pin1363_dixon_t : Z := 54.
Definition pin1363_dixon_b2 : Z := 43.
Definition pin1363_dixon_s2 : Z := 486.
Definition pin1363_dixon_t2 : Z := 54.
Definition pin1363_asquare_a : Z := 38.
Definition pin1363_asquare_t : Z := 9.
Definition pin1363_nfs_irr_c0 : Z := 31.
Definition pin1363_nfs_irr_c1 : Z := 1.
Definition pin1363_nfs_irr_c2 : Z := 1.
Definition pin1363_nfs_irr_m : Z := 36.
Definition pin1363_nfs_red_c0 : Z := -17.
Definition pin1363_nfs_red_c1 : Z := 16.
Definition pin1363_nfs_red_c2 : Z := 1.
Definition pin1363_nfs_red_m : Z := 30.
Definition pin1363_ts_a1 : Z := 1.
Definition pin1363_ts_b1 : Z := 0.
Definition pin1363_ts_a2 : Z := 1.
Definition pin1363_ts_b2 : Z := 0.
Definition pin1363_ts_T : Z := 1.
Definition pin1363_ts_U : Z := 1.
Definition pin1363_ts_y : Z := 1.
Definition pin1363_os_a : Z := 1.
Definition pin1363_os_b : Z := 1.
Definition pin1363_os_gs : Z := 3.
Definition pin1363_os_fs : Z := 4.

Lemma pin1363_N_pos : 0 < pin1363_N.
Proof. lia. Qed.

Lemma pin1363_N_gt_1 : 1 < pin1363_N.
Proof. lia. Qed.

Lemma pin1363_p_neq_q : pin1363_p <> pin1363_q.
Proof. discriminate. Qed.

Lemma pin1363_p_lt_q : pin1363_p < pin1363_q.
Proof. lia. Qed.

Lemma pin1363_p_prime : Z.prime pin1363_p.
Proof.
  apply Zprime_sqrt; [lia|].
  intros d Hd Hdiv.
  apply Z.mod_divide in Hdiv; [|lia].
  change (Z.sqrt pin1363_p) with 5 in Hd.
  assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5) by lia.
  intuition subst; vm_compute in Hdiv; discriminate.
Qed.

Lemma pin1363_q_prime : Z.prime pin1363_q.
Proof.
  apply Zprime_sqrt; [lia|].
  intros d Hd Hdiv.
  apply Z.mod_divide in Hdiv; [|lia].
  change (Z.sqrt pin1363_q) with 6 in Hd.
  assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia.
  intuition subst; vm_compute in Hdiv; discriminate.
Qed.


(** ** pin2491 — swap-test [47·53=2491] *)

Notation pin2491_p := 47.
Notation pin2491_q := 53.
Notation pin2491_N := (pin2491_p * pin2491_q).
Notation pin2491_e := 3.
Notation pin2491_d := 399.
Notation pin2491_y := 1849.
Notation pin2491_x := 42.
Notation pin2491_lam := 1196.
Notation pin2491_phi := 2392.
Notation pin2491_g := 3.
Notation pin2491_g_ord_p := 23.
Notation pin2491_g_ord_q := 52.
Notation pin2491_y_ord := 299.
Notation pin2491_y_ord_p := 23.
Notation pin2491_y_ord_q := 13.
Notation pin2491_x_k := 23.
Notation pin2491_inv3_p := 31.
Notation pin2491_inv3_q := 35.
Notation pin2491_ord2_p := 23.
Notation pin2491_ord2_q := 52.

Definition pin2491_root_ca : Z := 424.
Definition pin2491_root_cb : Z := 2068.
Definition pin2491_sqrt1_mixed : Z := 847.
Definition pin2491_sqrt1_mixed2 : Z := 1644.
Definition pin2491_dixon_a : Z := 51.
Definition pin2491_dixon_b : Z := 59.
Definition pin2491_dixon_r : Z := 110.
Definition pin2491_dixon_s : Z := 990.
Definition pin2491_dixon_t : Z := 330.
Definition pin2491_dixon_b2 : Z := 59.
Definition pin2491_dixon_s2 : Z := 990.
Definition pin2491_dixon_t2 : Z := 330.
Definition pin2491_asquare_a : Z := 50.
Definition pin2491_asquare_t : Z := 3.
Definition pin2491_nfs_irr_c0 : Z := 41.
Definition pin2491_nfs_irr_c1 : Z := 1.
Definition pin2491_nfs_irr_c2 : Z := 1.
Definition pin2491_nfs_irr_m : Z := 49.
Definition pin2491_nfs_red_c0 : Z := -5.
Definition pin2491_nfs_red_c1 : Z := 4.
Definition pin2491_nfs_red_c2 : Z := 1.
Definition pin2491_nfs_red_m : Z := 48.
Definition pin2491_ts_a1 : Z := 1.
Definition pin2491_ts_b1 : Z := 0.
Definition pin2491_ts_a2 : Z := 1.
Definition pin2491_ts_b2 : Z := 0.
Definition pin2491_ts_T : Z := 1.
Definition pin2491_ts_U : Z := 1.
Definition pin2491_ts_y : Z := 1.
Definition pin2491_os_a : Z := 1.
Definition pin2491_os_b : Z := 1.
Definition pin2491_os_gs : Z := 3.
Definition pin2491_os_fs : Z := 4.

Lemma pin2491_N_pos : 0 < pin2491_N.
Proof. lia. Qed.

Lemma pin2491_N_gt_1 : 1 < pin2491_N.
Proof. lia. Qed.

Lemma pin2491_p_neq_q : pin2491_p <> pin2491_q.
Proof. discriminate. Qed.

Lemma pin2491_p_lt_q : pin2491_p < pin2491_q.
Proof. lia. Qed.

Lemma pin2491_p_prime : Z.prime pin2491_p.
Proof.
  apply Zprime_sqrt; [lia|].
  intros d Hd Hdiv.
  apply Z.mod_divide in Hdiv; [|lia].
  change (Z.sqrt pin2491_p) with 6 in Hd.
  assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia.
  intuition subst; vm_compute in Hdiv; discriminate.
Qed.

Lemma pin2491_q_prime : Z.prime pin2491_q.
Proof.
  apply Zprime_sqrt; [lia|].
  intros d Hd Hdiv.
  apply Z.mod_divide in Hdiv; [|lia].
  change (Z.sqrt pin2491_q) with 7 in Hd.
  assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7) by lia.
  intuition subst; vm_compute in Hdiv; discriminate.
Qed.


(** ** Named extra moduli *)

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

(** ** Campaign alias

    [swap_pin.py] rewrites only the block between
    [CAMPAIGN_ALIAS_BEGIN] and [CAMPAIGN_ALIAS_END].  Lia sees
    integers because these are [Notation]s onto frozen [Notation]s. *)

(* CAMPAIGN_ALIAS_BEGIN pin187 *)
Notation pin_p := pin187_p.
Notation pin_q := pin187_q.
Notation pin_N := pin187_N.
Notation pin_e := pin187_e.
Notation pin_d := pin187_d.
Notation pin_y := pin187_y.
Notation pin_x := pin187_x.
Notation pin_lam := pin187_lam.
Notation pin_phi := pin187_phi.
Notation pin_g := pin187_g.
Notation pin_g_ord_p := pin187_g_ord_p.
Notation pin_g_ord_q := pin187_g_ord_q.
Notation pin_y_ord := pin187_y_ord.
Notation pin_y_ord_p := pin187_y_ord_p.
Notation pin_y_ord_q := pin187_y_ord_q.
Notation pin_x_k := pin187_x_k.
Notation pin_inv3_p := pin187_inv3_p.
Notation pin_inv3_q := pin187_inv3_q.
Notation pin_ord2_p := pin187_ord2_p.
Notation pin_ord2_q := pin187_ord2_q.
Notation pin_root_ca := pin187_root_ca.
Notation pin_root_cb := pin187_root_cb.
Notation pin_sqrt1_mixed := pin187_sqrt1_mixed.
Notation pin_sqrt1_mixed2 := pin187_sqrt1_mixed2.
Notation pin_dixon_a := pin187_dixon_a.
Notation pin_dixon_b := pin187_dixon_b.
Notation pin_dixon_r := pin187_dixon_r.
Notation pin_dixon_s := pin187_dixon_s.
Notation pin_dixon_t := pin187_dixon_t.
Notation pin_dixon_b2 := pin187_dixon_b2.
Notation pin_dixon_s2 := pin187_dixon_s2.
Notation pin_dixon_t2 := pin187_dixon_t2.
Notation pin_asquare_a := pin187_asquare_a.
Notation pin_asquare_t := pin187_asquare_t.
Notation pin_nfs_irr_c0 := pin187_nfs_irr_c0.
Notation pin_nfs_irr_c1 := pin187_nfs_irr_c1.
Notation pin_nfs_irr_c2 := pin187_nfs_irr_c2.
Notation pin_nfs_irr_m := pin187_nfs_irr_m.
Notation pin_nfs_red_c0 := pin187_nfs_red_c0.
Notation pin_nfs_red_c1 := pin187_nfs_red_c1.
Notation pin_nfs_red_c2 := pin187_nfs_red_c2.
Notation pin_nfs_red_m := pin187_nfs_red_m.
Notation pin_ts_a1 := pin187_ts_a1.
Notation pin_ts_b1 := pin187_ts_b1.
Notation pin_ts_a2 := pin187_ts_a2.
Notation pin_ts_b2 := pin187_ts_b2.
Notation pin_ts_T := pin187_ts_T.
Notation pin_ts_U := pin187_ts_U.
Notation pin_ts_y := pin187_ts_y.
Notation pin_os_a := pin187_os_a.
Notation pin_os_b := pin187_os_b.
Notation pin_os_gs := pin187_os_gs.
Notation pin_os_fs := pin187_os_fs.

Lemma pin_p_prime : Z.prime pin_p.
Proof. exact pin187_p_prime. Qed.

Lemma pin_q_prime : Z.prime pin_q.
Proof. exact pin187_q_prime. Qed.
(* CAMPAIGN_ALIAS_END *)
Lemma pin_N_pos : 0 < pin_N.
Proof. lia. Qed.

Lemma pin_N_gt_1 : 1 < pin_N.
Proof. lia. Qed.

Lemma pin_p_neq_q : pin_p <> pin_q.
Proof. discriminate. Qed.

Lemma pin_p_lt_q : pin_p < pin_q.
Proof. lia. Qed.

(** ** Residual pair on the campaign pin *)

Definition pin_residual_y : Z := pin_y.
Definition pin_residual_x : Z := pin_x.
Definition pin_residual_e : Z := pin_e.

Notation pin_Nsq := (pin_N * pin_N).

Definition pin_extra_77 : Z := pin_77.
Definition pin_extra_91 : Z := pin_91.
Definition pin_extra_247 : Z := pin_247.
Definition pin_extra_253 : Z := pin_253.
Definition pin_extra_45 : Z := pin_45.
Definition pin_extra_105 : Z := pin_105.
Definition pin_extra_Nsq : Z := pin_Nsq.
