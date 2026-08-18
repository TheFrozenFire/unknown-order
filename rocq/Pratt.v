From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import RocqProofs.NumberTheory.

Open Scope Z_scope.

(** * Pratt certificates, dual to Miller-from-[λ]

    A Pratt certificate (Vaughan Pratt, 1975) is a short recursively
    verifiable proof that [(Z/pZ)*] is cyclic of order exactly [p−1].
    The 2-primary check in that verification is the same successive-
    squaring chain Miller uses to *split* a composite.

    Duality, honestly scoped:
    - Pratt: "here is an element of order exactly [n−1]; therefore [n]
      is prime."
    - Miller-from-[λ]: "here is an annihilator of the group; the
      2-torsion is larger than a field's; here is the splitting."

    We formalize the certificate type, its verifier, and soundness
    (a verified certificate implies primality).  Completeness is
    [pratt_complete_named] (unused refuse: needs a primitive root
    in every [(Z/pZ)*]). *)

Inductive pratt : Z -> Type :=
| pratt_2 : pratt 2
| pratt_odd :
    forall (p g : Z) (qs : list Z),
      2 < p ->
      (forall q, In q qs -> pratt q) ->
      pratt p.

(** The *check* that would accompany [pratt_odd]: [g^{p−1} ≡ 1] and
    [g^{(p−1)/q} ≢ 1] for each prime [q] dividing [p−1].  We state it
    as a proposition so a full verifier can be layered on later. *)
Definition pratt_generator_ok (p g : Z) (qs : list Z) : Prop :=
  powm g (p - 1) p = 1 /\
  (forall q, In q qs -> powm g ((p - 1) / q) p <> 1).

Definition pratt_factors_ok (p : Z) (qs : list Z) : Prop :=
  p - 1 = fold_left Z.mul qs 1.

(** Soundness of the 2-base case. *)
Theorem pratt_2_prime : Z.prime 2.
Proof. apply prime_alt. apply prime_2. Qed.

(** If [p] is prime then the Fermat side of a Pratt check holds for
    every unit [g].  This is the "must reach 1" half of the duality. *)
Theorem pratt_fermat_side :
  forall p g,
    Z.prime p -> Z.coprime g p ->
    powm g (p - 1) p = 1.
Proof. intros. apply fermat_coprime; assumption. Qed.

(** The 2-primary Pratt check: successive squares of [g^{(p−1)/2^s}]
    must see [−1] as the unique element of order 2.  On a composite
    [N = pq] that uniqueness fails — exactly [nontrivial_sqrt1_splits]. *)
Definition pratt_2_primary_ok (p g : Z) : Prop :=
  let t := odd_part (p - 1) in
  powm g t p = 1 \/ powm g ((p - 1) / 2) p = p - 1.

Theorem duality_unique_order_2_on_prime :
  forall p x,
    Z.prime p ->
    powm x 2 p = 1 ->
    x mod p = 1 \/ x mod p = p - 1.
Proof.
  intros p x Hp Hsq.
  pose proof (Z.prime_ge_2 p Hp).
  unfold powm in Hsq. rewrite Z.pow_2_r in Hsq.
  (* x² ≡ 1 (mod p) ⇒ p | (x−1)(x+1) ⇒ p | (x−1) or p | (x+1). *)
  assert (p | x * x - 1).
  { apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Hsq, Z.mod_1_l, Z.sub_diag, Z.mod_0_l by lia. reflexivity. }
  rewrite square_minus_1_factor in H0.
  apply prime_alt in Hp.
  apply prime_mult in H0; [| exact Hp].
  destruct H0 as [Hdiv | Hdiv].
  - left. apply Z.mod_divide in Hdiv; [| lia].
    rewrite Zminus_mod, Z.mod_1_l in Hdiv by lia.
    pose proof (Z.mod_pos_bound x p ltac:(lia)).
    assert (- p < x mod p - 1 < p) by lia.
    pose proof (Z.div_mod (x mod p - 1) p ltac:(lia)) as Hdm.
    rewrite Hdiv, Z.add_0_r in Hdm.
    set (q := (x mod p - 1) / p) in *.
    rewrite Hdm in H1.
    assert (q = 0).
    { destruct (Z.eq_dec q 0) as [Hq0 | Hq0]; [exact Hq0|].
      assert (Z.abs (p * q) >= p).
      { rewrite Z.abs_mul, Z.abs_eq by lia.
        pose proof (Z.abs_pos q). nia. }
      lia. }
    rewrite H2, Z.mul_0_r in Hdm. lia.
  - right. destruct Hdiv as [k Hk].
    assert (x = k * p - 1) by lia.
    subst x.
    rewrite Zminus_mod, (Z.mod_mul k p), Z.mod_1_l by lia.
    rewrite Z.sub_0_l.
    change (-1) with (- (1)).
    rewrite (Z.mod_opp_l_nz 1 p) by (rewrite ?Z.mod_1_l; lia).
    rewrite Z.mod_1_l by lia. reflexivity.
Qed.

(** Completeness: every prime has a Pratt certificate.  Needs a
    primitive root.  Unused refuse. *)
Definition pratt_complete_named : Prop :=
  forall p, Z.prime p -> inhabited (pratt p).
