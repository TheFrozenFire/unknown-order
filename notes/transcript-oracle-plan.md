# Handles from transcripts and oracles

The sixth-type hunt asked for a public object computed from `N`
alone. That program is paused (`notes/sixth-type-plan.md`,
Methods 1–12 exhausted). This plan is the pivot: **bit leakage
after the key is used**.

This is well-trodden. The first job is to name the classical
types and say which algebra this tree already owns. The second
is to mark any type that is a *new source* of bits of `{p, d,
λ}` — especially one that crafts a message against a **specific
key shape** (constructor slots, Williams, 2-adic height, CRT
recombination). A hit that only recovers the message `m` is
RSA-inversion on a restricted challenge, not a new handle on
the key. A hit that only works because `p ≈ q` or `p−1` is
smooth is still an incarnation of Types A–E.

Do not resume this as “look at OpenSSL padding.” Implementation
bugs are listed only so their *algebraic core* can be named.

## Decision

A–E partition *locations of a handle given public `(N, e)`*.
They do not mention a ciphertext, a signature, or a query.
Those are extra inputs. The winning conditions stay the same:
factor, a one-sided annihilator, bits of `p` or `d` enough for
Coppersmith (`≈ n/4`), or a multiple of a one-sided order.

Success of a *type* is a named interface `I` and a theorem of
the form: answers under `I` determine a winning condition, for
a reason that is none of

- geometric closeness of `p`, `q` (Type A)
- a cyclotomic period of `p` (Type B) *without* the oracle
  being a one-sided test
- shortness in `ed − 1 = kφ` (Type C)
- a gcd across two moduli (Type D)
- a small root of a low-degree public polynomial in `ℤ[x]`
  (Type E)
- **you inverted the RSA map** (the problem)

“Leaks bits of `m`” is recorded. It is the first test, not
automatically a key handle. Håstad already shows a Type E
challenge distribution can refute RSA without factoring
(`notes/hardness.md`).

Honest `kg_far` balanced primes, `e = 65537`, unless a row
explicitly uses another shape.

## Constraints that stay in force

From `AGENTS.md` / `NamedSkips.v`. Do not discharge these to
make an oracle “work.”

- No SHA-in-Rocq, ROM, PPT/advantage. An oracle is a **named
  Gallina function** (bit, interval, error, full inverse), not
  a game against a PPT adversary.
- No NFS / LLL development. Coppersmith *consumes* recovered
  bits; it is not this plan’s algorithm.
- No running production keygen or production TLS padding oracles.
- No merging PoE `ℓ` with RSA `p`.
- No undirected KeyGen sampler pass; no sixth-type restart.
- Named refusals stay named.

CAS first, then Rocq. Chance model on every numerical claim.
`Print Assumptions` on any new theorem.

## Chance model

For a predicate oracle `P` on honest far pairs:

- A random bit agrees with a named bit of `{p, q, p+q, d, m}`
  at rate `1/2 ± O(1/√n)`. A hit is an identity, or a bias
  far above that on every sample.
- `gcd(f, N) ∈ {1, p, q, N}`; nontrivial without a smoothness
  or CRT-side hypothesis is a hit.
- Recovering `m` from `(N, e, c)` and `P` is message recovery.
  Score it as such. It becomes a key handle only if `m` was
  planted as a function of `{p, d}` (it is not, on honest
  encryption) or if the *same* answers determine `p` without
  determining `m`.

## Already owned (do not redo)

| Algebra | Where | Why it is not this plan |
|---|---|---|
| Miller from a multiple of `λ` | `Miller.v`, `cas/04` | needs `ed−1` or `λ`, not a transcript |
| Mixed `√1` splits | `TwoPrimary`, `RabinWilliams.rabin_roots_split` | the *split*; not how an oracle produces the second root |
| RW inversion oracle ⇒ factor (1/2) | `notes/rabin-williams.md` | RSA has no such theorem for an inversion oracle |
| Håstad broadcast, FR shape | `SmallExponent.v`, `cas/12` | Type E on the *message*, no interactive oracle |
| Partial bits of `p` / ROCA AP | `BitLeak.v` | generation-side shape; lattice refused |
| Wiener / BD | `Wiener.v`, `Lattice.v` | public `(N, e)`, short `d` |
| GQ two-transcript extract | `GQ.v` | special soundness; simulation refused |
| LLX extract / Peng–Bao | `Accumulator.v`, `cas/42` | published `μ` or two witnesses |
| AR game / smooth `C` | `Hardness.v`, paper-overlaps #3 | the game *is* a restricted root oracle |
| Euler quotient `a^{N+1} ≡ a^{p+q}` | `EulerQuotient.v` | public from `N`, no query |
| One-sided `a^k ≡ 1 (mod p)` factors | `Hardness.one_sided_low_order_factors` | the implication; not the oracle that supplies it |
| Constructor AP, public `M` | `KeyGenCtor`, `cas/28` | Type A/E, no transcript |

Textbook RSA inversion and textbook signing are the problems
`Problem_RSA` / `trapdoor_inverts_RSA`. Formalizing “if I can
decrypt I can decrypt” is not a type.

## Interfaces

Every row below names one of these. An attack that needs a
stronger interface than it claims is misclassified.

| # | Interface | What the adversary is given |
|---|---|---|
| I0 | Transcript only | `(N, e)` and one or more `c = m^e` or `σ = m^d` (or padded), no queries |
| I1 | Predicate | adaptive `P(c) ∈ {0,1}` (padding valid, LSB, MSB, Jacobi, error class, extra-reduction bit) |
| I2 | Partial value | adaptive `k` bits of `m` or of `d`, or membership of `m` in a public interval |
| I3 | Full inverse | adaptive `c ↦ m` or `m ↦ σ` on a named domain (raw units, padded strings, QR, …) |
| I4 | Fault | one (or few) incorrect `σ` or `m` computed with CRT, a flipped bit of `d`, or a skipped multiply |
| I5 | Related algebraic | several transcripts whose plaintexts satisfy a *known* polynomial or multiplicative relation |

I3 on raw units *is* RSA (decrypt) or a multiplicative group
(sign). Rows that assume I3 must say what restriction keeps
them from being the problem.

I1 is the interesting default. One bit per query, multiplicativity
`P(c · α^e) = P(α · m)`, is the shape of almost every padding /
LSB / Manger attack.

---

## Part I — General types (message or key)

### I0 — Transcript only

| # | Type | Leaks | Win | Collapse / status | Formalize? |
|---|---|---|---|---|---|
| T1 | Stereotyped / small `m` (`m < N^{1/e}` or known prefix) | bits of `m` | `m` | Type E. Lattice is `coppersmith_named` | Shape only (have `SmallExponent`) |
| T2 | Håstad broadcast, same `m`, `k ≥ e` moduli | `m` | `m` | Type E. Integer CRT when `m^e < ∏ N_i` is a theorem | **Owned** `hastad_cube_if_small` |
| T3 | Franklin–Reiter, `m₂ = am₁+b` known | `m` | `m` | Type E. gcd in `(ℤ/Nℤ)[x]` is `Refuse_polynomial_gcd_over_ZN` | Shape **owned** `related_message_common_root` |
| T4 | Common modulus, same `m`, coprime `e₁, e₂` | `m` | `m` | Bézout: `m = c₁^a c₂^b`. Not a key handle | **Yes** — missing Closed lemma |
| T5 | Jacobi of ciphertext | 1 bit of `m` | — | For odd `e`, `(c/N) = (m/N)`. Public, no query | **Yes** — one Closed lemma |
| T6 | Signature of `−1`, `2`, small primes | `(-1)^d`, `2^d` | — | `d` odd ⇒ `σ(−1) = −1`. `2^d` is DL | T5-like pin; DL is the problem |
| T7 | Many raw signatures, multiplicative dependence among `m_i` | annihilator or forge | forge / `λ` | Desmedt–Odlyzko. Needs small factors of the `m_i` (or of hashes: `Refuse_hash_as_oracle`) | Algebra of `∏ σ_i^{a_i} = σ(∏ m_i^{a_i})` **yes**; hash-DO **no** |
| T8 | PKCS#1 v1.5 / `e=3` signature *forgery* (Bleichenbacher ’06) | forge | forge | Type E on the padded integer, not a key handle | Shape only; no hash |
| T9 | Euler-quotient ciphertext `c = a^{N+1}` | — | — | Decrypting gives `a^{(p+q)d}`, not a cheap `p+q`. Identity already a theorem | Do not resume |

T5 is the contrast class: a bit of `m` that **is** public from
`c`. LSB of `m` is not (T12). That pair is the hardcore-bit
story without PPT slogans: one character is a function of `N`,
one is not.

### I1 — Predicate oracles

| # | Type | Oracle | Leaks | Win | Collapse / status | Formalize? |
|---|---|---|---|---|---|---|
| T10 | PKCS#1 v1.5 padding (Bleichenbacher ’98) | `pad^{-1}(m)` well-formed? | interval of `m` | `m` | Multiplicative interval-set update. Recovers `m`, not `p` | **Yes** — the interval algebra, not a TLS parser |
| T11 | OAEP leading-zero (Manger) | `m < B` | MSB-side interval | `m` | Binary search on a half-line. Cleaner than T10 | **Yes** — interval-halving lemma |
| T12 | LSB / parity | `m mod 2` | all bits of `m` | `m` | `lsb(2^{-1} m)` after multiplying `c` by `2^{-e}`. ACGS | **Yes** — Closed recovery; hardness slogan stays refused |
| T13 | MSB / `m < N/2` | one bit | all bits of `m` | `m` | Same as T11 with `B = N/2` | Fold into T11 |
| T14 | Jacobi of plaintext | `(m/N)` | 0 extra bits | — | Equals T5 for odd `e`. Oracle is redundant | Cite T5 |
| T15 | Error-*class* distinguisher (padding vs other) | which exception | often T10 | `m` | Same multiplicative structure if the class tracks an interval | Collapse to T10/T11 |
| T16 | QR-mod-`p` bit | `(m/p)` | `(m/p)` | factor / QR | Given public `(m/N)`, this *is* `(m/q)`. Equivalent to factoring on average (RW-adjacent) | **Yes** as a relation; do not claim PPT equivalence |
| T17 | Timing / cache / EM of `d` | noisy bits of `d` | bits of `d` | Type A/E + Coppersmith | Implementation. Algebra is `BitLeak` of `d` | Core already named; microarch **no** |
| T18 | Extra Montgomery reduction (Schindler / Brumley–Boneh) | comparison in CRT recombination | bits of `q` | Type A/E | Algebra: extra reduction iff intermediate `> N` | **Yes** — the comparison predicate; not the timer |

T10–T13 recover `m`. They are worth formalizing because the
*mechanism* (multiplicativity + interval) is the same gadget
every later key-shape row will try to aim at `p` instead of
`m`.

### I2 — Partial-value oracles

| # | Type | Oracle | Win | Status | Formalize? |
|---|---|---|---|---|---|
| T19 | `k` LSBs of `m` | `m` once `k ≳ n` via T12-style | I1 with a wider output | Fold into T12 |
| T20 | `k` MSBs of `m` | Coppersmith if `k ≳ n/e` | Type E | Shape; lattice refused |
| T21 | `k` bits of `d` or of `p` | Coppersmith / Boneh–Durfee–Frankel | Type A/E, `BitLeak` | **Owned** shape |
| T22 | Interval membership `m ∈ [A,B]` | T11 | I1 | Fold into T11 |

### I3 — Full inverse, restricted domain

| # | Type | Restriction | Win | Status | Formalize? |
|---|---|---|---|---|---|
| T23 | Textbook decrypt | none | `m` for every `c` | the problem | No |
| T24 | Textbook sign | none | `σ(m₁m₂)=σ(m₁)σ(m₂)` | forge any `m` | **Yes** — homomorphism lemmas |
| T25 | Blinding | decrypt `c r^e`, divide by `r` | `m` | CCA on raw RSA | **Yes** — one lemma, companion to T24 |
| T26 | Padded decrypt (honest impl.) | only well-padded `c` invert | T10 if the *failure* is visible | I1 | Do not model a full TLS stack |
| T27 | RW / Rabin invert | random square | factor w.p. 1/2 | **Owned** as prose + `rabin_roots_split` | Optional: oracle-shaped wrapper |
| T28 | GQ / FS signing oracle | hash challenge | extract or forge | `Refuse_NIZK_Fiat_Shamir` | Two-transcript extract **owned** |

Coron–May / Miller-from-`(e,d)` is **not** “I3 ⇒ factor” for
RSA. That is already in `notes/hardness.md`. Do not write a
false converse.

### I4 — Faults

| # | Type | Fault | Win | Status | Formalize? |
|---|---|---|---|---|---|
| T29 | Bellcore / BDL CRT signature | `σ ≡ m^d (mod p)`, wrong `(mod q)` | `gcd(σ^e − m, N) ∈ {p,q}` | mixed root of `m` | **Yes** — this is the missing wrapper around `rabin_roots_split` |
| T30 | Lenstra (known message) | same | same | T29 | Fold into T29 |
| T31 | Bit-flip in `d` | `σ = m^{d⊕2^i}` | bits of `d` / factor | needs the model of the flip | Optional, after T29 |
| T32 | Safe-error / skipped multiply | presence of a fault depends on a bit of `d` | bits of `d` | I1 on `d` | Collapse to T17/T21 |

T29 is the signature-side twin of “one-sided annihilator
factors.” It is the highest-value missing theorem on I4.

### I5 — Related algebraic (already half-owned)

T2, T3, T4, T7. No new interface. Finish T4.

---

## Part II — Key-shape, crafted messages

These aim the I1 gadget at `{p, q, d, M, r, s}` rather than at
`m`. Honest `kg_far`, `e = 65537`, plus one named shape.

### CRT-asymmetric predicates (the real family)

Decrypt and CRT-sign compute `m_p = c^{d_p} (mod p)` and
`m_q` independently, then recombine. A predicate that is
**not a function of the recombined `m`** can see one side.

| # | Craft | Shape | What it would leak | Collapse | Formalize? |
|---|---|---|---|---|---|
| K1 | `P` holds of `m_p` not of `m_q` (padding checked per side; some historical PKCS / BERserk-shaped bugs) | any CRT impl. | one-sided set membership | Type B via `one_sided_low_order_factors` if `P` is “`= 1`”; otherwise a one-sided interval | **Yes** — abstract `P_p ↛ P_q ⇒ gcd` / bits |
| K2 | Extra reduction / recombination comparison (T18) aimed at `q` | CRT-RSA | bits of `q` | Type A/E consumer | Comparison predicate **yes** |
| K3 | Fault only on the `q`-side (T29) | CRT-sign | factor | T29 | T29 |
| K4 | Choose `c` so `m ≡ 1 (mod p)` | needs `p` | — | cannot craft without the secret | Death |

K1 is the candidate that looks closest to a “new handle.” It
is not a sixth type: the handle is the **oracle**, and the
reason is one-sidedness (Type B’s winning condition). It *is*
a new *source* of that winning condition, which the `N`-only
hunt could not produce.

### Characters the implementation evaluates on a side

| # | Craft | Shape | Leak | Collapse | Formalize? |
|---|---|---|---|---|---|
| K5 | RW tweak choice among `{±m, ±2m}` | Williams `p≡3, q≡7 (mod 8)` | which pair is `(+1,+1)` | `(2/p)` is **already public** from `p mod 8` (`two_supplement`). The tweak is a function of `(m/p), (m/q)` | Pin: tweak bit vs public `N mod 8`. Not a new bit of `p` |
| K6 | Tonelli / `a^{(p+1)/4}` timing | Blum `p≡3 (mod 4)` | bits of `p` or of `m_p` | T17 | No microarch |
| K7 | Query `(m/p)` via any API that “fixes” a residue | QR / RW | T16 | T16 | T16 |

K5 is a useful *negative*: Williams KeyGen makes `(2/p)` public
from `N` (product of two public bits). A tweak oracle does not
buy a secret character of `p` that `N` did not already determine
at the 2-adic / `mod 8` level. Residual information is `(m/p)`,
which is T16.

### Constructor slots (`p = a + k M`, `r \| p−1`, `s \| p+1`, `Φ_i`)

`M` public is already ROCA (Type A/E). Assume `M` secret, honest
placement.

| # | Craft | Query | Leak? | Collapse | Formalize? |
|---|---|---|---|---|---|
| K8 | `c = (1 + t r)^e` for guessed small `r` | T10/T11/T12 on that `c` | validity is a fact about `1+tr`, not about `p` | I0 on a known `m` | Death as a key handle |
| K9 | I3 sign of `1+tr` | `σ = (1+tr)^d` | DL / order of a constructed unit | the problem | No |
| K10 | K1 with `P(x) = (x ≡ 1 (mod r))` | one-sided | whether `r \| p−1` | Type B, constructor row of `keygen-weaknesses` | Only if an impl. exposes K1. Abstract K1 covers it |
| K11 | Lucas / Williams `V` on a chosen `P`, test `V_s ≡ 2` | torus period | `s \| p+1` one-sided | Type B, `Torus.v` | Only if the box *is* a Lucas impl. Do not grow a new torus API unless a named scheme has one |
| K12 | `Φ_k` slot: `c` a root of `Φ_k` mod `N` | T12 recover `m` | you recover a public cyclotomic integer | Method 6 already killed `Φ_k(N)` as a handle | Do not redo Method 6 |

No constructor row leaks `k` or secret `M` from a standard
padding/LSB/sign oracle without already being K1 or I3.

### 2-adic / Miller shape

| # | Craft | Query | Leak? | Collapse | Formalize? |
|---|---|---|---|---|---|
| K13 | Sign or decrypt a chosen base `a` | `a^d` | `ord(a^d) = ord(a)/gcd(ord(a),d)`. `d` odd ⇒ same order | no height leak | Pin: `d` odd ⇒ `v₂(ord(σ))=v₂(ord(a))` |
| K14 | I3 + known `ed−1` | Miller | factor | **Owned** Miller; needs `d` | No |
| K15 | Matched-deep `v₂` | T29 / Miller | thinner success | `TwoPrimary` | **Owned** as KeyGen shape |

### Shanks / class-group presentations

| # | Craft | Query | Leak? | Formalize? |
|---|---|---|---|---|
| K16 | Low-order query in `Cl(1−4u³)` | I3 in the class group | constructible 3-torsion | **Owned** `shanks_family_has_3`. Not RSA-of-`N` |
| K17 | Pietrzak / Wesolowski transcript | midpoint / `π` | paper-overlaps #2–#5 | **Owned** |

Do not grow an ECC or `Cl(−4N)` signing scheme. `Δ=−4N`
non-principal `Cl[2]` is factoring (`SixthType.form_p0q_*`).

### Far vs close, one-sided smooth

A transcript does not create Type A. T10–T13 work on `kg_far`.
If `p−1` is smooth, Pollard is Type B *without* an oracle
(`keygen-weaknesses` row 3). An oracle is not required and
is not a new letter.

---

## Part III — Novel-handle scan

A sixth type here would be: answers under a named `I` determine
bits of `p` or `d` **without** recovering `m`, **without** a
CRT-asymmetric predicate, **without** a low-degree polynomial
in a small unknown, **without** being `(·/p)`, and **without**
inverting RSA.

No row in Parts I–II is that object.

What the `N`-only hunt could not see, and this plan can:

1. **I1 multiplicativity recovers `m`** (T10–T13). New *source*
   of a Type E / inversion challenge, not a new key handle.
2. **CRT-asymmetric `P`** (K1, T18, T29). New *source* of the
   one-sided winning condition already in `Hardness.v`.
3. **T5 vs T12**: which bits of `m` are functions of `(N,c)`.
   Public character vs hardcore-shaped bit. Worth lemmas.
4. **T27 vs RSA I3**: Rabin inversion factors; RSA inversion
   does not (as a theorem). Already documented; optional wrapper.

Nothing in the constructor, Williams, Shanks, or Euler-quotient
algebra produced a crafted-message handle that is not K1 or DL.
That is the scan, not a promise that none exists. A later row
has to name a new `P` that is a function of `m_p` and not of
`m`, and show it on honest `kg_far`.

## What we will formalize (order)

CAS first, then Rocq. Stop a row when it collapses.

1. **T5** `(c/N)=(m/N)` for odd `e`. Closed. CAS: 40 far pairs.
2. **T24 / T25** sign homomorphism and decrypt blinding.
3. **T12** LSB oracle recovers `m` (binary search / doubling).
   CAS on 16-bit `N`, then the lemma.
4. **T11** interval / half-line oracle recovers `m`.
5. **T29** Bellcore: `gcd(σ_bad^e − m, N)` factors.
6. **T4** common modulus, coprime exponents.
7. **K1** abstract one-sided predicate: if `P(m mod p) ≠ P(m
   mod q)` for a named decidable `P`, extract a factor or a
   one-sided bit. This is the key-shape hook.
8. **T10** interval-*set* update (Bleichenbacher core) only if
   T11+K1 are not enough to classify the later rows.
9. **K5 / K13** as Closed negatives (tweak / 2-height do not
   add a secret bit).
10. **T18** comparison predicate, optional after K1.

Do not implement class-number algorithms, a TLS stack, a
cache model, or ACGS-as-PPT. `Refuse_PPT_advantage` stays
the leftover on “LSB is as hard as RSA.”

## Outcome (2026-08-18)

`rocq/TranscriptOracle.v` + `cas/57`. Closed.

| # | Theorem | Note |
|---|---|---|
| T5 | `euler_odd_power`, `rsa_cipher_euler_eq_message` | odd `e` ⇒ Euler of `c` equals Euler of `m` |
| T24 | `sign_homomorphism`, `sign_inverse`, `sign_of_one` | raw RSA signing is a group hom |
| T25 | `decrypt_blinding`, `decrypt_double_is_double` | `dec(c r^e) = r dec(c)` |
| T12 | `lsb_double_decides_half` | `lsb(2m mod N)=0` iff `m < N/2` |
| T11 | `recover_interval_correct` | comparison oracle recovers `m` |
| T4 | `common_modulus_identity`, `common_modulus_recovers`, `coprime_to_nonneg_bezout` | Bézout recover |
| T29 | `bellcore_factors` | `gcd(σ_bad^e−m, N)=p` |
| K1 | `one_sided_congruence_factors` | `m≡a (mod p)`, not `(mod q)` ⇒ factor |
| K5 | `williams_N_mod8`, `non_williams_N_mod8_5`, `williams_two_is_shape` | `(2/p)` is KeyGen shape |
| K13 | `sign_neg1_odd`, `odd_exp_preserves_minus1` | odd `d` sends `−1` to `−1` |

T10 (Bleichenbacher interval-set) and T18 (Montgomery comparison)
not started: T11+K1 classify the later rows. ACGS-as-hardness stays
`Refuse_PPT_advantage`.

### Follow-up (same day)

| # | Result | Note |
|---|---|---|
| T16 | `other_legendre_from_product`, `cipher_jacobi_eq_message` | `(m/q)=(m/p)·(m/N)`; product is public from `c` |
| T8 | `e3_small_cube_verifies` | `s³ < N` ⇒ `s` is a raw `e=3` signature of `s³` |
| K1+ctor | `onesided_plain_one_factors`; `ctor_slot_mod_r_need_not_factor` | `m≡1 (mod p)` factors; `m_p≡1 (mod r)` with `r\|p−1` need not |
| T27 | `rabin_oracle_nonassociate_factors` | inversion of a planted square, non-associate root, factors |
| — | `rsa_inverter_constructs_factor_named` unused | RSA inverter recovers `m`, does not construct a factor |
| sweep | `cas/58` | no cheap predicate of `m_p` is a function of `m` or of `(N,c)` (80 far 12-bit samples) |

The sweep is the oracle-world Method 1: `lsb(m_p)`, `m_p < p/2`, `(m/p)`, `m_p mod 3` match neither the recombined payload nor `(c/N)` / `c`. No public CRT-side handle.

| T7 | `sign_hom_3`, `sign_of_msg_product_one`, `sign_weighted_product` | raw signatures multiply; msg-product 1 annihilates |

### Self-review (adversary reading)

Read every `TranscriptOracle` headline as something an adversary could fail.

- **Fixed:** `rsa_inverter_recovers_message` previously restated the inverter spec (`x^e = c`). It now says `x ≡ m (mod N)`, using uniqueness of the `e`-th root on units (`rsa_dec_enc_units`). The old statement constrained nothing.
- **Kept, scoped:** `recover_interval_correct` is integer binary search, not RSA. It is the *engine* of T11; the RSA content is `lsb_double_decides_half` feeding the comparison. Not vacuous, not a key handle.
- **Kept, thin:** `sign_homomorphism` is `powm_mul_l`. T7 (`sign_hom_3`, product-one, weighted) is the same algebra stacked; CAS 62 pins a concrete product.
- **Kept, encoding:** `other_legendre_from_product` is `(p-sign)² = 1`. The load-bearing sibling is `cipher_jacobi_eq_message`.
- **Honest refuse:** `rsa_inverter_constructs_factor_named` unused; `ctor_slot_mod_r_need_not_factor` is a Closed negative.

No PPT added.

## What this plan is not

- A restart of Methods 1–12 on `N`
- Boneh–Durfee / LLL development
- “RSA ≡ factoring” via an inversion oracle
- A hash, ROM, or Fiat–Shamir signing game
- Growing an ECC or class-group *scheme* so we have something
  to query
- Scanning live padding-oracle CVEs (population, different
  project)

## How to record an outcome

Same three marks as `sixth-type-plan.md`: identity (theorem +
CAS, classify), negative (chance model), collapse (it is A–E,
I3, or K1). Update this file and
`generated/COVERAGE.md`. Do not grow `THEORY.md`.

Named leftovers already in force: `Refuse_PPT_advantage`,
`Refuse_lattice_lll_development`,
`Refuse_polynomial_gcd_over_ZN`, `Refuse_hash_as_oracle`,
`Refuse_RW_signature_scheme`, `Refuse_NIZK_Fiat_Shamir`.
