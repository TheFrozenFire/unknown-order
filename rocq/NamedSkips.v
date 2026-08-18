From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.

Open Scope Z_scope.

(** * First-class skips

    Rocq has no keyword for "we will not prove this."  Comments are
    invisible to [Print Assumptions].  This file, plus every
    [Definition *_named] in the tree, *is* the gap list.

    Classification is by *use* (harness [named-skips] tool):

    - [Definition foo_named] unused → refuse
    - [Definition foo_named] taken as a hypothesis → weakness
    - [NamedRefuse] constructor → refuse that is not a proposition
    - [Axiom] / [Admitted] → load-bearing trust (none in this tree)

    File-local mathematical skips live next to the algebra they
    bound ([compose_assoc_named], [coppersmith_named],
    [pratt_complete_named], …).  Cross-cutting refuses live here.

    Do not cite a hand-written theory map from other [.v] files.
    The TOC is generated ([generated/COVERAGE.md]). *)

(** Refuses that are not Gallina claims: no group, no cost model, no
    hash, no PPT class.  The constructors *are* the register. *)
Inductive NamedRefuse : Set :=
  | Refuse_ROM
  | Refuse_SHA_in_Rocq
  | Refuse_PPT_advantage
  | Refuse_NFS_cost
  | Refuse_RSA_eq_factoring_standard_model
  | Refuse_AM09_generic_ring_as_standard_model
  | Refuse_BP97_vs_modern_sRSA
  | Refuse_undirected_611_hunt
  | Refuse_elliptic_curve_branch
  | Refuse_lattice_lll_development
  | Refuse_FO_DF_simulation
  | Refuse_pairing_accumulators
  | Refuse_this_is_a_VDF
  | Refuse_HVZK_simulation
  | Refuse_PRF_stretch
  | Refuse_hash_as_oracle
  | Refuse_NIZK_Fiat_Shamir
  | Refuse_Camenisch_Michels_protocol
  | Refuse_Mollin_general_2020_1310
  | Refuse_r_power_hardness
  | Refuse_polynomial_gcd_over_ZN
  | Refuse_RW_signature_scheme
  | Refuse_EN_card_from_N.

(** Dirichlet: a prime in a coprime AP.  Unused: refuse of
    existence in a constructor window.  Image-in-class of a
    *given* seed remains a theorem. *)
Definition dirichlet_ap_prime_named : Prop :=
  forall a M,
    0 < M ->
    Z.gcd a M = 1 ->
    exists p, Z.prime p /\ 0 <= p /\ (p - a) mod M = 0.
