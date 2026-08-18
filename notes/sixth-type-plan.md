# Directed hunt for a sixth algebraic handle

This is the durable plan for the §6.11 remainder. It is **not**
`Refuse_undirected_611_hunt`. That refuse is wandering through KeyGen
samplers. This plan names public objects and a winning condition, then
tries to write each leak as Type A–E. If one cannot be written that
way, the catalog’s closing sentence is false and we have a sixth type.

Do not resume this as “look at OpenSSL.” Popular keygens are a
different direction, not forbidden, not this plan.

## Decision

A–E partition *locations of a handle* given public `(N, e)` and secret
a function of `{p, q}`. That partition is a definitional move, not a
theorem. A polynomial in `N` cannot be an identical handle:
`f(N) ≡ f(q) (mod p−1)` and `q` is independent of `p`. So if a sixth
type exists, the public object is not a polynomial in `N`.

Success is a public object computed from `N` (and cheap public data)
that inverts a winning condition — factor, one-sided annihilator,
bits of `p` or `p+q` enough for Coppersmith (`≈ n/4` bits), or a
multiple of a one-sided order — **for a reason that is none of**:

- geometric closeness of `p`, `q` to a public quantity (Type A)
- a cyclotomic period of `p` (`p±1`, `Φ_k(p)`) (Type B)
- shortness in `ed − 1 = kφ` (Type C)
- a gcd across two moduli (Type D)
- a small root of a low-degree public polynomial in `ℤ[x]` (Type E)

“Leaks bits” is the first test, not the winning condition.

A hit that only works when `p ≈ q`, when `p−1 | q−1`, or when a
generation choice makes `p−1` smooth, is an incarnation, not a sixth
type. Work on **honest `kg_far` balanced primes** with `e = 65537`
unless a method explicitly contrasts a special shape.

## Constraints that stay in force

From `AGENTS.md` / `NamedSkips.v`. Do not discharge these in order
to “make a method work.”

- No SHA-in-Rocq, ROM, PPT/advantage
- No NFS / LLL *development* (`Refuse_lattice_lll_development`,
  `Refuse_NFS_cost`). Using a recovered `φ` is a theorem; rebuilding
  Coppersmith/BD as a research program is not this plan
- No running production keygen
- No public map that hides `M`, no forcing placement by CRT alone
- No merging PoE `ℓ` with RSA `p`
- No undirected KeyGen sampler pass
- No elliptic-curve or lattice *branching of the corpus* (Method 4
  may *evaluate* a curve determined by `N`; it must not become an
  ECC project)
- No FO/DF simulation
- Named refusals stay named unless the user asks them discharged

CAS first, then Rocq. Chance model before claiming a gcd hit.
`Print Assumptions` on any new theorem.

## Chance model (required for every numerical claim)

For random `p, q` of the same bit length, far apart:

- `gcd(f(q), p−1)` is a gcd of two random integers of size `~p`.
  Typical size `O(log p)`. A hit is a gcd `≫ log p`, identically
  or with probability far above `1/B` for bound `B`.
- `gcd(N−1, p−1) = gcd(p−1, q−1)` is usually `2` (odd primes).
- Jacobi `(D/N) = (D/p)(D/q)` is one bit of a product, chance `1/2`.
- `gcd(f, N) ∈ {1, p, q, N}`; nontrivial without a smoothness
  hypothesis is a hit.

Record the model next to every CAS probe. `gcd = 2` is not a hit.

## Existing identities to use, not rediscover

- `N ≡ q (mod p−1)` because `pq = (p−1)q + q`. Hence
  `f(N) ≡ f(q) (mod p−1)` for any polynomial `f`.
- `N−1 = φ + p + q − 2`.
- For every `a` (including those sharing a factor with `N`):

  ```
  a^{N+1} ≡ a^{p+q}     (mod N)
  a^{N−1} ≡ a^{p+q−2}   (mod N)
  ```

  CRT + Fermat on each side. **Not yet a Rocq theorem** in this
  tree; pin in CAS, then prove. `N+1` does *not* annihilate the
  Williams torus (`Torus.v`, `cas/27`). That is a different claim
  (`V_{N+1} ≡ 2` fails). Do not conflate them.
- `λ+1` annihilates units if `λ` is known; `a^λ ≡ 1`.
- Catalog and avenues already closed: `notes/keygen-weaknesses.md`.
  Nextprime / shared-prefix / increment-window are incarnations.

## Priority

| # | Method | Start? |
|---|---|---|
| 2 | Public element `a^{N+1} ≡ a^{p+q}` | **first** |
| 1 | Non-polynomial identity sweep | in parallel with 2, low-complexity half |
| 3 | `Cl(Δ(N))` cheap invariants | after 1–2 negatives or a lead |
| 4 | `E_N` with `#E(𝔽_p) = p+1−t` | after 3 |
| 5 | Recurrences whose char poly involves `N` | after 3 |
| 6 | Cyclotomic / exponential gcd algebra | can piggyback on 1 |
| 7 | Character families | after 3 (overlaps genus) |
| 8 | Dedekind sums / modular symbols | after 3 (overlaps CF) |

---

## Method 1 — Identity sweep in a non-polynomial language

**Public functions.** Enumerate, filter, prove. Language in order:

1. `N±1`, `2N±1`, `N²±N+1`, `N²+1`, `4N±1`, `4N±4`
2. `gcd` of those
3. `a^{N±1}−1`, `a^N−a`, `Φ_k(N)`, `gcd(a^{N±1}−1, b^{N±1}−1)` for small `a,b`
4. Fibonacci / Lucas / Lehmer `U_k(N)`, `V_k(N)`
5. one cheap invariant of a discriminant `Δ(N)` (2-rank, a named
   ambiguous form, a Dedekind sum) — overlap 3 and 8, keep one probe

**Test.** On honest `kg_far` pairs *and* a few special shapes
(close, shared-prefix, ROCA-form), measure each expression against
`{p−1, p+1, q−1, q+1, p+q, p−q, λ, φ}`:

- `gcd(f, ·)` versus the chance model
- `a^f ≡ 1 (mod p)`
- `|f − 2√N|`, whether `4N+f` is square
- Hamming agreement of `f` with `p` or `p+q`
- whether `gcd(f, N)` is nontrivial

**Success.** A hit that beats chance by a lot, then an identity.

**Death.** Nothing in this language hits ⇒ a sixth type is not
low-complexity. Hits only on close primes ⇒ Type A.

**Artifact.** `cas/43` (or next free) plus a table in this note.

---

## Method 2 — The public element that *is* `p+q` in the exponent

**Public function.** `a ↦ a^{N+1} mod N`, which equals `a^{p+q}`.
Also `a^{N−1} ≡ a^{p+q−2}`. Information-theoretically this *is*
the secret sum, written in the exponent.

**Why it might be new.** Every classical death is “you assumed
`p ≈ q`” (Fermat in the exponent) or “you took a discrete log.”
If those are the only deaths, a bit-extraction that needs neither
is a new *source* for A/E, or a sixth type.

**Attempt.**

1. Prove / pin `a^{N+1} ≡ a^{p+q} (mod N)` (all `a`).
2. On `kg_far` primes, test whether any cheap map of
   `{a^{N+1} mod N}_a` (several small `a`, ratios,
   `gcd(a^{N+1}−1, b^{N+1}−1)` in `ℤ`, MSB/LSB of the residue,
   pairing-like bilinears of these elements) predicts a bit of
   `p+q` better than chance.
3. If bits appear, ask Coppersmith-on-bits only as a *consumer*
   (`coppersmith_named` stays a refuse of the algorithm).

**Death.** No bit above chance for far-apart primes; or the only
predictor is proximity of `p+q` to `2√N`.

**Do not.** Discrete log in `(ℤ/Nℤ)*`. That is the problem.

**Artifact.** `rocq/EulerQuotient.v`; `cas/43_euler_quotient.gp`.

**Outcome (exhausted, 2026-08-18).** Negative as a sixth type.

Theorems, all Closed under the global context:

- `euler_quotient` / `euler_quotient_rsa`: `a^{N+1} ≡ a^{p+q} (mod N)`
  for every `a` (units via `N+1 = φ+s`; non-units via Fermat+CRT)
- `euler_quotient_pred`: `a^{N-1} ≡ a^{p+q-2} (mod N)`
- `odd_primes_sum_even`: `s` even for odd primes
- `sum_mod4_of_N`: `N ≡ 1 (mod 4) ⇒ s ≡ 2 (mod 4)`;
  `N ≡ 3 (mod 4) ⇒ s ≡ 0 (mod 4)`

CAS `43` (honest `kg_far` pairs, chance model recorded in-file):

- identity on the textbook range and on 40 random 12-bit pairs
  including `a ∈ {0, ±1, p, q}`
- homomorphism `(ab)^{N+1} ≡ a^{N+1} b^{N+1}` — many bases add
  nothing
- 400 samples × 8 bases × 12 bits of `g(a)` vs bits of
  `s`, `p`, `|p−q|`: max `|rate−1/2| = 0.073` (below 0.16)
- `sign(g(2)−N/2)`, Hamming parity, Jacobi `(g(2)/N)`,
  `g(65537)` bit 0: all chance
- `gcd(2^{N+1}−1, N)` never splits; `x^{N+1}≡x` on 0/1200 probes
- `g(2) mod 32` does not pin `s mod 8` on `N`-ambiguous samples
- Fermat-in-the-exponent: 20/20 recoveries on nextprime-close
  16-bit pairs (`k` in `±2^{10}`); 0/16 on 24-bit `gap=20`
  (`k` in `±2^{12}`)
- `(-1)^{N+1} ≡ 1` matches `s` even — constructible torsion
  gives nothing more

What this is: the public element *is* `p+q` in the exponent.
What it is not: a cheap reading of bits of `p+q` on `kg_far`
primes. The only cheap readings are functions of `N` itself
(`s` even, `s mod 4`) and Fermat-in-the-exponent when
`p≈q` (Type A). A remaining extractor is a discrete log
in `(ℤ/Nℤ)*` (the problem) or an unnamed map outside this
class. That existence claim is `Refuse_PPT_advantage`, not
a sixth type.

Do not resume Method 2 unless a *named* new reading of
`{a^{N+1} mod N}` is proposed.

**Scale supplement (`cas/44_euler_quotient_scale.gp`).** The
identity is a theorem at every size; bit length cannot produce a
counterexample. CAS still pinned it with N-derived bases at
128, 256, 512, 1024, 2048-bit primes, sparsely at 4096, and
`a=2` at 8192. Imbalanced pins: 32+96, 64+192, 256+1792,
16+2048. N-derived bases (`2√N`, `√N`, `N/2`, `nextprime(√N)`)
show no bit leak at 32/64-bit. Imbalanced 32+96 same; Fermat-in-
exponent fails *harder* off the diagonal (AM-GM). `g(N±1)=1`
is torsion, not a new bit. **16384-bit pin not run** — PARI
modular exp at that size is the wrong tool; do not resume it
in `gp`. A structural leak would have shown at 16–64-bit. A
bias `ε ~ 2^{-n/2}` is *easier* to see at 16-bit than at
2048-bit. What 2048-bit statistics cannot add, cheaply, is a
test of an unnamed polytime extractor (`Refuse_PPT_advantage`).

---

## Method 3 — Quadratic forms of `Δ(N)`

**Public functions.** `Cl(Δ)` for
`Δ ∈ {−4N, 1−4N, 4N−1, N²−4, 5−4N, −N}`. Composition and
reduction need no `p`. The form `(N, 0, 1)` of disc `−4N` is
public and ambiguous.

**Why it might be new.** The public object is a *group*, not an
integer `M`. Genus characters, 2-rank, and named ambiguous forms
are cheap relative to `h(Δ)`. If an invariant factors `N` (or
leaks `p+q`) **without** walking the CF of `√N`, the reason is
not Type A’s geometry.

**Attempt.** Write down the cheap invariants for each `Δ`. Test
whether they determine a nontrivial factor or a bit of `p+q` on
`kg_far` pairs. Contrast with reducing `(N,0,1)` (known to be
SQUFOF / CFRAC).

**Death.** The only working invariant is reduction of `(N,0,1)`
(= CF of `√N`, Type A). `N²−4 = (N−2)(N+2)` factors publicly;
genus theory there only sees `N±2`.

**Do not.** Implement class-number algorithms or Sutherland
(`Refuse` adjacent: `h(Δ)` cost stays named). Do not resume
`compose_assoc_named`.

**Artifact.** Use existing `BinForms.v`; CAS pins; no new
associativity proof unless a headline is blocked on it.

---

## Method 4 — An elliptic curve determined by `N`

**Public function.** A curve `E_N` with coefficients in `ℤ[N]`:
`y² = x³ + N x`, `y² = x³ + a x + N`, or a fixed-`D` CM twist
selected by `N`. Then `#E(𝔽_p) = p+1−t` with `|t| ≤ 2√p`.

**Why it might be new.** `p+1−t` is **not** a cyclotomic period
of `p`. The catalog stuffed ECM under unbalanced Type A; that is
a fudge. A cheap public *multiple* of `p+1−t` as a function of
`N` (not of `p`) would force a widening of B or a new letter.

**Attempt.** For named `E_N`, ask whether any formula in `N`
(CM trace identities, a division polynomial at a public point,
a resultant with `N`) is a multiple of `#E_N(𝔽_p)` for honest
balanced primes. Evaluating `[k]P` on `E(ℤ/Nℤ)` is allowed only
as a probe, not as “run ECM.”

**Death.** Fixed curve + vary `k` = ECM (smooth `p+1−t`, Type B
on a new module). `4p = t² − D s²` becoming Cornacchia = Type A.
Do not grow an ECC corpus.

**Artifact.** One CAS file; a `NamedRefuse` or a theorem, not a
curve library.

---

## Method 5 — Linear recurrences whose char poly involves `N`

**Public functions.** Companion of `x² − N x + 1`, `x² − x + N`,
`x² + N`; Lucas with parameter `P = N`. Values `U_k(N)`, `V_k(N)`
for moderate `k`.

**Why it might be new.** When the characteristic polynomial
depends on `N`, the period modulo `p` is a function of
`N mod p`, i.e. of `q`. That is a different module from
Williams (`P` fixed, period `| p±1`).

**Attempt.** `gcd(U_k(N), N)` for a designed sequence of `k`.
Rank of appearance of `p` in `U_·(N)` versus `p±1`. Whether
that rank is a cheap function of `N`. Jacobi of the discriminant
`q²−4` is `(N²−4 / p)` and is *not* obviously public
(`N²−4 ≡ 0 (mod N)`, not `(mod p)`). Chase that carefully.

**Death.** Period `| p±1` = Williams (Type B). Period `| p+1−t`
= Method 4.

**Artifact.** Distinct from `Lucas.v` / `Torus.v` (those are `P`
fixed). New CAS; Rocq only if an identity appears.

---

## Method 6 — Cyclotomic and exponential gcd algebra

**Public functions.** `Φ_k(N)`, `a^{N±1}−1`,
`gcd(a^{N−1}−1, N−1)`, smooth kernel of `N±1`.

**Why it might be new.** The only identity already in hand is
`gcd(f(N), p−1) = gcd(f(q), p−1)`. A novel handle is an `f`
for which that gcd is *identically* large, or `f(N)` is easy
to factor and those small factors divide `p−1` above chance.

**Attempt.** Piggyback the Method 1 sweep. Factor the smooth
part of `N±1`, `Φ_k(N)` for small `k`, and score factors
against `p±1`.

**Death.** `gcd(N−1, p−1) = gcd(p−1, q−1)` usually `2`. Any
hit that requires `p−1 | q−1` or `p−1 | Φ_k(q)` is a
generation condition (Type B), not a function of `N` alone.

---

## Method 7 — Character families that try to split `(·/p)` from `(·/q)`

**Public functions.** `(D/N) = (D/p)(D/q)` for every `D`.
Genus characters of `Δ(N)` are the structured case (overlap 3).

**Why it might be new.** A family `{D_i(N)}` and a cheap
combination that equals `(D/p)` *alone*, or `≈ n/4` bits of
`p`, would be a bit-handle that is not CF(`√N`).

**Attempt.** After Method 3’s genus characters, ask whether any
combination separates the `p` character from the `q` character
on `kg_far` pairs.

**Death.** Quadratic residuosity is deciding `(·/p)` given
`(·/N)`. Product-only is not a factor. A family that works
only when `p≈q` or when `D` is a square mod `N` is Type A
or nothing.

---

## Method 8 — Polylog modular symbols / Dedekind sums at `N`

**Public functions.** Dedekind sums `s(h, N)` via reciprocity,
time `polylog(N)`. Not polynomials in `N`. Known to encode
continued-fraction data.

**Why it might be new.** A modular symbol that carries bits of
`p` or `p+q` *other than* the CF of `√N`.

**Attempt.** Compute `s(1,N)`, `s(h,N)` for small `h`, and
standard transforms. Correlate with bits of `p`, `p+q`, and
with the CF of `√N` (to detect collapse).

**Death.** If `s(·,N)` is a rewrite of CF(`√N`) or of `e/N`,
it is Type A or C.

---

## What this plan is not

- Another `KeyGenSampler` / increment-window / nextprime pass
- Boneh–Durfee / LLL development
- A recurrence that is not `p±1` *without* a public evaluator
  determined by `N`
- Attacking `KeyGenCtor` with public `M` (already Type A,
  `roca_form`, `public_map_difference_divides`)
- Inventing a sixth letter before a public object and a
  winning condition exist
- Scanning Certificate Transparency / TPM-EK (population
  detector; different project)

## How to record an outcome

For each method, write one of:

1. **Identity.** Rocq theorem + CAS. Classify as A–E or argue
   why it is not. If not, mint a type letter and a
   `NamedRefuse` is the wrong tool — it is a theorem.
2. **Negative.** CAS chance-model holds on honest pairs. Add
   a sentence here and, if the negative is load-bearing, a
   `Definition *_named` unused refuse or a theorem of the
   form “this function is not an annihilator.”
3. **Collapse.** The method works only as A–E. Cite the row
   of `keygen-weaknesses.md`. Do not keep probing that
   encoding.

Do not grow `THEORY.md`. Update this file and the catalog.
Regenerate `generated/COVERAGE.md` if `.v` files change.
