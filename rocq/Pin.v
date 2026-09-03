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

(** ** Default semiprime *)

Definition pin_p : Z := 11.
Definition pin_q : Z := 17.
Definition pin_N : Z := pin_p * pin_q.
Definition pin_e : Z := 3.
Definition pin_d : Z := 27.
Definition pin_y : Z := 36.
Definition pin_x : Z := 42.
Definition pin_lam : Z := 80.
Definition pin_phi : Z := 160.

Lemma pin_N_pos : 0 < pin_N.
Proof. unfold pin_N, pin_p, pin_q. lia. Qed.

Lemma pin_N_gt_1 : 1 < pin_N.
Proof. unfold pin_N, pin_p, pin_q. lia. Qed.

Lemma pin_p_neq_q : pin_p <> pin_q.
Proof. unfold pin_p, pin_q. discriminate. Qed.

(** ** Residual pair on the default pin *)

Definition pin_residual_y : Z := pin_y.
Definition pin_residual_x : Z := pin_x.
Definition pin_residual_e : Z := pin_e.

(** ** Named extra moduli *)

Definition pin_extra_77 : Z := 7 * 11.
Definition pin_extra_91 : Z := 13 * 7.
Definition pin_extra_247 : Z := 13 * 19.
Definition pin_extra_253 : Z := 11 * 23.
Definition pin_extra_45 : Z := 3 * 3 * 5.
Definition pin_extra_105 : Z := 3 * 5 * 7.
Definition pin_extra_Nsq : Z := pin_N * pin_N.

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
