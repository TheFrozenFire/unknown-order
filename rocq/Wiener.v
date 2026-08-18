From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.

Open Scope Z_scope.

(** * Small [d]: [e/N] approximates [k/d]

    Write [e d = 1 + k φ(N)].  Then
    [|e/N − k/d| = |k(N−φ)−1| / (N d)]
    and [N−φ = p+q−1].  A short [d] makes [k] short, and the public
    ratio [e/N] falls inside the continued-fraction basin
    [|α − k/d| < 1/(2d²)] (Wiener: [d < ⅓ N^{1/4}]).

    We prove the identities and the basin implication under an explicit
    bound on [p+q].  Continued-fraction recovery itself is not
    formalized.  Cross-confirmed by [cas/11_wiener.gp].

    Honest: this development uses the [φ]-form of [d]
    ([ed ≡ 1 (mod φ)]), which is stronger than the [λ]-inverse in
    [RSAInstance]. *)

Definition wiener_k (e d phi : Z) : Z := (e * d - 1) / phi.

Lemma wiener_relation :
  forall e d phi k,
    phi <> 0 ->
    e * d - 1 = k * phi ->
    e * d = 1 + k * phi.
Proof. intros. lia. Qed.

Lemma N_minus_phi :
  forall p q, p * q - phi_semiprime p q = p + q - 1.
Proof. intros. unfold phi_semiprime. ring. Qed.

(** The exact numerator of [|e/N − k/d|]. *)
Lemma wiener_numerator :
  forall e d k p q,
    e * d = 1 + k * phi_semiprime p q ->
    e * d - k * (p * q) = 1 - k * (p + q - 1).
Proof.
  intros e d k p q Heq.
  rewrite Heq. unfold phi_semiprime. ring.
Qed.

(** If [d < φ] then the cofactor [k] is strictly smaller than [e].
    That is the generation leak: short [d] ⇒ short [k]. *)
Lemma small_d_small_k :
  forall e d phi,
    0 < d -> 0 < phi -> d < phi ->
    0 < e ->
    e * d - 1 = ((e * d - 1) / phi) * phi ->
    (e * d - 1) / phi < e.
Proof.
  intros e d phi Hd Hphi Hdp He Heq.
  apply Z.div_lt_upper_bound; [lia|].
  nia.
Qed.

(** Basin sufficient for continued fractions: [|α − k/d| < 1/(2d²)]
    iff [|e d − k N| * 2 d < N], when everything is positive.  We stay
    on integers (no rationals). *)
Definition in_wiener_basin (e d k N : Z) : Prop :=
  0 < d -> 0 < N ->
  Z.abs (e * d - k * N) * (2 * d) < N.

(** Under a bound [p+q−1 ≤ S] and [k ≥ 1],
    [|ed − kN| ≤ k S − 1] (since [k(p+q−1) ≥ 1]). *)
Lemma wiener_abs_numerator :
  forall e d k p q,
    0 < k -> 2 <= p -> 2 <= q ->
    e * d = 1 + k * phi_semiprime p q ->
    Z.abs (e * d - k * (p * q)) = k * (p + q - 1) - 1.
Proof.
  intros e d k p q Hk Hp Hq Heq.
  rewrite wiener_numerator by exact Heq.
  assert (1 <= k * (p + q - 1)) by nia.
  rewrite Z.abs_neq by lia. ring.
Qed.

Theorem wiener_basin_from_gap :
  forall e d k p q S,
    0 < d -> 0 < k -> 2 <= p -> 2 <= q ->
    e * d = 1 + k * phi_semiprime p q ->
    0 <= p + q - 1 <= S ->
    k * S * (2 * d) < p * q + 2 * d ->
    in_wiener_basin e d k (p * q).
Proof.
  intros e d k p q S Hd Hk Hp Hq Heq HS Hsmall.
  unfold in_wiener_basin. intros _ _.
  rewrite (wiener_abs_numerator e d k p q Hk Hp Hq Heq).
  nia.
Qed.

(** Wiener's classical numeric trigger, as a *sufficient* integer
    condition we can check: [d³ < N / 18] (since [⅓ N^{1/4}] cubed is
    [N^{3/4}/27], weaker and integer-only we use [18 d³ < N] as a
    conservative stand-in).  Not claimed equivalent to [d < ⅓ N^{1/4}]. *)
Definition wiener_small_d (d N : Z) : Prop :=
  0 < d /\ 18 * d * d * d < N.

(** If [e < φ] then the cofactor is smaller than [d] itself — the
    usual case ([e] reduced modulo [φ]). *)
Lemma k_lt_d_of_e_lt_phi :
  forall e d phi k,
    0 < d -> 0 < phi -> e < phi ->
    e * d = 1 + k * phi ->
    k < d.
Proof.
  intros e d phi k Hd Hphi Helt Heq.
  assert (k * phi = e * d - 1) by lia.
  nia.
Qed.

(** Classical Wiener sufficient condition, integer form.
    Balanced primes give [p+q−1 ≤ 3 √N].  Combined with [k ≤ d]
    and [36 d⁴ < N] (i.e. [6 d² < √N]), the pair lands in the
    continued-fraction basin.  Not claimed equivalent to
    [d < ⅓ N^{1/4}]; it is a proved sufficient criterion. *)
Theorem wiener_classical_sufficient :
  forall e d k p q,
    0 < d -> 0 < k -> k <= d ->
    2 <= p -> 2 <= q ->
    e * d = 1 + k * phi_semiprime p q ->
    p + q - 1 <= 3 * Z.sqrt (p * q) ->
    36 * d * d * d * d < p * q ->
    in_wiener_basin e d k (p * q).
Proof.
  intros e d k p q Hd Hk Hkd Hp Hq Heq Hsum Htrig.
  assert (0 <= p * q) as HNnn by nia.
  pose proof (Z.sqrt_nonneg (p * q)) as Hsn.
  pose proof (Z.sqrt_spec (p * q) HNnn) as Hsp. cbn in Hsp.
  assert (6 * d * d <= Z.sqrt (p * q)) as H6.
  { destruct (Z.lt_ge_cases (Z.sqrt (p * q)) (6 * d * d)) as [Hlt | Hge];
      [| exact Hge].
    assert (Z.sqrt (p * q) + 1 <= 6 * d * d) by lia.
    assert ((Z.sqrt (p * q) + 1) * (Z.sqrt (p * q) + 1)
              <= (6 * d * d) * (6 * d * d)) by nia.
    assert ((6 * d * d) * (6 * d * d) = 36 * d * d * d * d) by ring.
    nia. }
  apply (wiener_basin_from_gap e d k p q (3 * Z.sqrt (p * q)));
    try assumption.
  - split; [nia | exact Hsum].
  - assert (k * (3 * Z.sqrt (p * q)) * (2 * d)
              <= 6 * d * d * Z.sqrt (p * q)) by nia.
    assert (6 * d * d * Z.sqrt (p * q)
              <= Z.sqrt (p * q) * Z.sqrt (p * q)) by nia.
    nia.
Qed.

(** Boneh–Durfee numeric slogan, unused refuse of the lattice
    step ([Refuse_lattice_lll_development], [coppersmith_named]).
    [bd_past_wiener] only says "[d] is larger than the Wiener
    trigger and still [o(N^{1/3})]".  It is *not* this bound. *)
Definition boneh_durfee_named (d N : Z) : Prop :=
  0 < d /\ 0 < N /\ d ^ 1000 < N ^ 292.

Definition bd_past_wiener (d N : Z) : Prop :=
  0 < d /\ ~ (18 * d * d * d < N) /\ d * d * d < N.

Definition boneh_durfee_delta_milli : Z := 292.
