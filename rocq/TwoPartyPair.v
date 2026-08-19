From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.
Require Import SharedKey.
Require Import PowersOfTau.
Require Import UnknownOrder.
Require Import Hardness.

Open Scope Z_scope.

(** * 2-of-2 root oracle is not a pairing of two group elements

    [shared_dec] raises to [d*].  That is a homomorphism
    [X ↦ X^{d*}] which Alice and Bob evaluate jointly.  Using it
    as "next CRS power" forces [τ ≡ d*] — the old public-[e]
    string, whose relation is the public exponent.  A sampled-[τ]
    string is a different map.

    Cross-confirmed by [cas/88_two_party_pair.gp]. *)

Definition two_party_root (RA RB : RSAInstance) (X : Z) : Z :=
  shared_dec RA RB X.

Theorem two_party_root_is_eth :
  forall RA RB X dstar,
    rsa_e RA = rsa_e RB ->
    Z.gcd (rsa_N RA) (rsa_N RB) = 1 ->
    Z.coprime X (shared_N RA RB) ->
    0 < dstar ->
    d_star_spec RA RB dstar ->
    powm (two_party_root RA RB X) (rsa_e RA) (shared_N RA RB) =
      X mod shared_N RA RB.
Proof.
  intros RA RB X dstar He Hg Hcop Hd Hspec.
  unfold two_party_root.
  apply (shared_dec_is_eth_root RA RB X dstar); assumption.
Qed.

Theorem two_party_root_is_dstar_power :
  forall RA RB X dstar,
    rsa_e RA = rsa_e RB ->
    Z.gcd (rsa_N RA) (rsa_N RB) = 1 ->
    Z.coprime X (shared_N RA RB) ->
    0 <= dstar ->
    d_star_spec RA RB dstar ->
    two_party_root RA RB X mod shared_N RA RB =
      powm X dstar (shared_N RA RB).
Proof.
  intros RA RB X dstar He Hg Hcop Hd Hspec.
  unfold two_party_root.
  apply (shared_dec_eq_powm RA RB X dstar); assumption.
Qed.

Theorem two_party_root_hom :
  forall RA RB X Y dstar,
    rsa_e RA = rsa_e RB ->
    Z.gcd (rsa_N RA) (rsa_N RB) = 1 ->
    Z.coprime X (shared_N RA RB) ->
    Z.coprime Y (shared_N RA RB) ->
    0 <= dstar ->
    d_star_spec RA RB dstar ->
    two_party_root RA RB ((X * Y) mod shared_N RA RB)
      mod shared_N RA RB =
      (two_party_root RA RB X * two_party_root RA RB Y)
        mod shared_N RA RB.
Proof.
  intros RA RB X Y dstar He Hg Hx Hy Hd Hspec.
  pose proof (shared_N_gt_1 RA RB).
  rewrite (two_party_root_is_dstar_power RA RB _ dstar He Hg);
    [| | lia | exact Hspec].
  2:{ unfold Z.coprime.
      rewrite Z.gcd_mod by lia.
      rewrite Z.gcd_comm.
      apply Z.coprime_mul_l; assumption. }
  rewrite (Z.mul_mod (two_party_root RA RB X) (two_party_root RA RB Y)
             (shared_N RA RB)) by lia.
  rewrite (two_party_root_is_dstar_power RA RB X dstar He Hg Hx Hd Hspec).
  rewrite (two_party_root_is_dstar_power RA RB Y dstar He Hg Hy Hd Hspec).
  rewrite powm_mod_base by lia.
  unfold powm.
  rewrite Z.pow_mul_l.
  rewrite <- Z.mul_mod by lia.
  reflexivity.
Qed.

(** Using the oracle as "next power" on a sampled-[τ] string
    forces [τ ≡ d*] modulo [ord(g) / gcd(τ^i, ord)]. *)
Theorem two_party_next_forces_dstar :
  forall RA RB g tau i dstar ord,
    rsa_e RA = rsa_e RB ->
    Z.gcd (rsa_N RA) (rsa_N RB) = 1 ->
    Z.coprime g (shared_N RA RB) ->
    0 <= tau ->
    0 <= i ->
    0 < dstar ->
    d_star_spec RA RB dstar ->
    is_order (shared_N RA RB) g ord ->
    two_party_root RA RB (pot (shared_N RA RB) g tau i)
      mod shared_N RA RB =
      pot (shared_N RA RB) g tau (i + 1) ->
    (ord | tau ^ i * (dstar - tau)).
Proof.
  intros RA RB g tau i dstar ord He Hg Hcop Ht Hi Hd Hspec Hord Hnext.
  pose proof (shared_N_gt_1 RA RB) as Hn.
  assert (Z.coprime (pot (shared_N RA RB) g tau i) (shared_N RA RB)) as Hcp.
  { unfold pot, Z.coprime, powm.
    rewrite Z.gcd_mod by lia.
    rewrite Z.gcd_comm.
    destruct (Z.eq_dec (tau ^ i) 0) as [Hz | Hnz].
    - rewrite Hz, Z.pow_0_r. apply Z.gcd_1_l.
    - apply Z.coprime_pow_l; [lia | exact Hcop]. }
  rewrite (two_party_root_is_dstar_power RA RB _ dstar He Hg Hcp ltac:(lia) Hspec)
    in Hnext.
  unfold pot in Hnext.
  rewrite Z.add_1_r, Z.pow_succ_r in Hnext by lia.
  rewrite <- powm_mul_r in Hnext by (try apply Z.pow_nonneg; lia).
  rewrite (Z.mul_comm tau) in Hnext.
  pose proof (powm_eq_implies_abs_annihilator
                (shared_N RA RB) g (tau ^ i * dstar) (tau ^ i * tau)
                Hn ltac:(nia) ltac:(nia) Hcop Hnext) as Hann.
  pose proof (order_divides_annihilator (shared_N RA RB) g ord
                (Z.abs (tau ^ i * dstar - tau ^ i * tau))
                Hn (Z.abs_nonneg _) Hord Hann) as Hdiv.
  replace (tau ^ i * dstar - tau ^ i * tau)
    with (tau ^ i * (dstar - tau)) in Hdiv by ring.
  destruct (Z.le_ge_cases (tau ^ i * dstar) (tau ^ i * tau)) as [Hle | Hge].
  - rewrite Z.abs_neq in Hdiv by nia.
    destruct Hdiv as [m Hm]. exists (- m). nia.
  - rewrite Z.abs_eq in Hdiv by nia. exact Hdiv.
Qed.
