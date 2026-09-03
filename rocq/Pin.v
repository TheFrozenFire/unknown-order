From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

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

Lemma pin_N_pos : 0 < pin_N.
Proof. lia. Qed.

Lemma pin_N_gt_1 : 1 < pin_N.
Proof. lia. Qed.

Lemma pin_p_neq_q : pin_p <> pin_q.
Proof. discriminate. Qed.

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

Definition pin_dixon_a : Z := 24.
Definition pin_dixon_b : Z := 37.
Definition pin_dixon_r : Z := 15.
Definition pin_dixon_s : Z := 60.
Definition pin_dixon_t : Z := 30.

Definition pin_dixon_b2 : Z := 38.
Definition pin_dixon_s2 : Z := 135.
Definition pin_dixon_t2 : Z := 45.

Definition pin_asquare_a : Z := 14.
Definition pin_asquare_t : Z := 3.

(** ** NFS quadratics on [pin_N] *)

Definition pin_nfs_irr_c0 : Z := 5.
Definition pin_nfs_irr_c1 : Z := 1.
Definition pin_nfs_irr_c2 : Z := 1.
Definition pin_nfs_irr_m : Z := 13.

Definition pin_nfs_red_c0 : Z := 7.
Definition pin_nfs_red_c1 : Z := 8.
Definition pin_nfs_red_c2 : Z := 1.
Definition pin_nfs_red_m : Z := 10.

Definition pin_ts_a1 : Z := -15.
Definition pin_ts_b1 : Z := 1.
Definition pin_ts_a2 : Z := -6.
Definition pin_ts_b2 : Z := 1.
Definition pin_ts_T : Z := 20.
Definition pin_ts_U : Z := 6.
Definition pin_ts_y : Z := 1.

Definition pin_os_a : Z := 1.
Definition pin_os_b : Z := 1.
Definition pin_os_gs : Z := 3.
Definition pin_os_fs : Z := 4.
