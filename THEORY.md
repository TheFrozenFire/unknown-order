# Groups of unknown order (working document)

This is the evolving account of the *generalizable* structure behind computational problems in
groups whose order is not given to the algorithm. It grows as we add problems. The first object
is the RSA problem on `(ℤ/Nℤ)*`.

Seeded from the grok.com conversation
[RSA key generation and decryption explained](https://grok.com/share/bGVnYWN5LWNvcHk_50720cb1-f620-400a-b3c9-ee69981b5b0d)
(notes in [`notes/grok-share-rsa-seed.md`](notes/grok-share-rsa-seed.md)). Everything asserted
here will be machine-checked; until a claim has a Rocq theorem and a CAS witness, it is a
**design target**, not a fact.

## 1. The domain

A **group of unknown order** is a group `G` in which the group operation is efficient, but `|G|`
(and typically a factorization of `|G|`) is not part of the public input. Hardness assumptions
in this setting — RSA, strong RSA, adaptive root, order, low-order — are statements about
algorithms that see `G` and some extra elements, and must produce a root, an order, or a
factorization.

`(ℤ/Nℤ)*` with `N = pq` is the defining example. RSA is not merely related to this class; it is
the original concrete instantiation. Later groups (class groups, certain Jacobians, RSA-UFOs)
were introduced largely to obtain the same algebraic setting without a trusted setup.

## 2. The RSA instance and the private exponent `d`

- Primes `p`, `q` of roughly equal size; public modulus `N = p q`.
- Public exponent `e` coprime to `φ(N) = (p−1)(q−1)`, or more tightly to `λ(N) = lcm(p−1, q−1)`.
  Usual `e ∈ {3, 65537}`.
- Private exponent `d` is the modular inverse:

  `d ≡ e⁻¹ (mod λ(N))`   or   `d ≡ e⁻¹ (mod φ(N))`

  so `e d ≡ 1` modulo that annihilator. Formalization must pick one (or carry both) and never
  blur them: `λ` divides `φ`, so an inverse mod `φ` is an inverse mod `λ`, but not conversely
  the same integer.

- Encryption: `c ≡ m^e (mod N)`. Decryption: `m ≡ c^d (mod N)`.
- For `e = 3`, exponentiation by `d` *is* the modular cube-root map on units. `d` itself is not
  “a cube root”; it is the exponent that realizes the inverse of the `e`-power map.

The **RSA problem**: given `(N, e, y)`, find `x` with `x^e ≡ y (mod N)`, without the factors
(or any multiple of `λ(N)`).

## 3. From `(N, e, d)` to `{p, q}`

The integer `M = e d − 1` is a multiple of `λ(N)` and therefore annihilates the unit group:

`∀ a ∈ (ℤ/Nℤ)* ,  a^M ≡ 1 (mod N)`.

`ℤ/Nℤ ≃ ℤ/pℤ × ℤ/qℤ`, so the same polynomial `X^M − 1` vanishes component-wise. A witness
that the two components *disagree* about a power of some element (1 on one side, −1 or another
non-trivial root of unity on the other) is a non-trivial idempotent of `ℤ/Nℤ` and therefore a
factor of `N`.

Every algorithm below is a different procedure for turning a known annihilator of the unit
group into a witness that the ring is not a field. Possession of `d` is computationally
equivalent to possession of `{p, q}`.

### 3.1 Multiplier enumeration — deterministic

Parameter: the cofactor `k` itself.

If `d < φ(N)` then `1 ≤ k < e`. For each candidate `k = 1, …, e−1` test whether
`φ' = (e d − 1) / k` is an integer; if so, solve

`x² − (N − φ' + 1) x + N = 0`.

Roots are `p` and `q` iff the discriminant is a square and both roots are integers `> 1`
multiplying to `N`. Time `O(e · polylog N)` — practical for small `e`, not a claim for
arbitrary `e`.

### 3.2 Miller successive-squaring — randomized

Parameter: a base `a ∈ {2, …, N−2}` with `gcd(a, N) = 1`.

Write `M = 2^s · t` with `t` odd. Compute `g₀ ≡ a^t (mod N)`, `g_{i+1} ≡ g_i² (mod N)`.
The first `j` with `g_j ≡ 1` and `g_{j−1} ≢ ±1` yields `gcd(g_{j−1} − 1, N)` as a
non-trivial factor.

A base succeeds iff the 2-adic valuations of the orders of `a` mod `p` and mod `q` differ.
At least half the units have this property (design target; to be counted, not sloganeered).

### 3.3 Sequential-base Miller — deterministic

Same process; bases are the successive primes `2, 3, 5, …`. Always deterministic. Polynomial
runtime is ERH-conditional (Miller 1976). Without ERH the worst-case trial count is not known
to be polynomial.

### 3.4 Coron–May / May lattice — deterministic

Parameters: lattice dimension (shift count) and the size bound `X` on the unknown small root
of a Coppersmith polynomial built from `e d − 1 = k · φ(N)`. Recovers `k` or `p+q`; then the
same quadratic as 3.1. Conversation-claimed regime: polynomial time for `e d ≤ N²` (balanced
RSA), faster `O(log² N)` for `e d ≤ N^{3/2}`. Formalize the exact bound from the paper, do
not inherit the slogan.

## 4. Dualities that constrain the model

- **Miller–Rabin polarity.** Same successive-squaring engine. Primality: “does the sequence
  misbehave for exponent `n−1`?” Factoring from `d`: “does a known annihilator `M` produce a
  non-trivial square root of 1?” Miller 1976 already notes the factoring direction; RSA 1978
  cites it.
- **Pratt polarity.** Pratt (1975) certifies “`(ℤ/pℤ)*` is cyclic of order exactly `p−1`”
  (PRIMES ∈ NP). Miller-from-`λ` exhibits that the 2-torsion of `(ℤ/Nℤ)*` is larger than a
  field’s, and splits the ring. The 2-primary Pratt check and the Miller square-chain are the
  same computational primitive.

## 5. Honest scope

Machine-checked: Euler/Carmichael for `N=pq`, the annihilator `M=ed−1`, the quadratic recovery
of `{p,q}` from `φ` or `p+q`, non-trivial `√1` splits `N`, unique `√1=±1` on a prime, RSA
enc/dec on units, Miller witness ⇒ factor, Miller–Rabin polarity of the engine.

Not proved, and not claimed: general ≥1/2 density of Miller bases (CAS-exhaustive on 187:
150/158); ERH-conditional polynomial bound for sequential Miller; Coppersmith/LLL;
completeness of Pratt certificates; any hardness of RSA / strong RSA / order (see §9).

`φ` vs `λ` is distinguished in the statements: `d` is the inverse modulo `λ`; enumeration
via `φ` requires the stronger `φ | ed−1`.

## 6. Key generation as the place the annihilator leaks

The RSA problem is hard only if the public pair `(N, e)` hides every useful handle on
`λ(N)`. Key generation is the only step that *chooses* `p`, `q`, `e`, and thereby `d`.
Every classical “bad RSA key” is a generation choice that makes one of those handles
cheap to compute from the public pair alone. The rest of this section is the taxonomy
of those choices, and the reason each one is algebraically forced — not a list of
software bugs.

The unifying picture is still §3. Factoring `N` is turning an annihilator of `(ℤ/Nℤ)*`
into a CRT disagreement. Full knowledge of `d` *is* a full annihilator (`ed−1` is a
multiple of `λ`). Bad generation gives the attacker a *partial* annihilator, or a
*short* description of one, without ever seeing `d`:

```
full annihilator λ | M          (§3, given d)
        ▲
        │  key-gen leak
        │
one-sided annihilator p−1 | M   (Pollard p−1; Williams p+1)
short annihilator k small       (Wiener / Boneh–Durfee; small d)
near-square N ≈ a²              (Fermat; close primes)
shared annihilator              (batch GCD; shared p)
low-degree root                 (small e + stereotyped message)
```

A generation procedure is “strong” exactly when it refuses every row of that table.
Smaller parameters can then be honest, because the bits you *would* have spent
papering over a leak are no longer needed.

### 6.1 Close primes — Fermat

If `|p−q|` is small then `N = pq` is a small perturbation of a square:

```
((p+q)/2)² − N  =  ((p−q)/2)²
```

So `⌈√N⌉` is only `((√p−√q)²)/2` below `(p+q)/2`. Fermat factoring increments
`a` from `⌈√N⌉` until `a²−N` is square; the number of increments *is* that gap.
The weakness is not “Fermat is clever” — it is that generation sampled `p` and `q`
from a tiny interval around `√N`, so the hidden sum `p+q` is nearly determined by
the public product.

Balanced generation (`|p−q|` on the order of `N^{1/2}`) makes the gap
exponential in the bit length. “Balanced” in the bit-length sense (`|p|≈|q|`) is
necessary but not sufficient: `q = nextprime(p+2)` is bit-balanced and still
Fermat-food.

### 6.2 Shared primes — batch GCD

Two moduli `N₁ = p q₁`, `N₂ = p q₂` have `gcd(N₁,N₂) = p`. This is unique
factorization, not an algorithm. It arises whenever two keygens draw from a
shared, low-entropy source of primes (a broken RNG, a factory default, a
prime-generation cache). The hidden-order groups are not independent: they
share a CRT component, so the public product already names that component.

### 6.3 Smooth `p−1` — Pollard’s `p−1`

Fermat says `a^{p−1} ≡ 1 (mod p)` for `p ∤ a`. If `p−1` is `B`-smooth then a
cheap multiple `M` of `p−1` is known *without knowing `p`* (e.g. `M = lcm(1..B)`
or `B!`). Then `a^M ≡ 1 (mod p)` while, for a generic `a`, `a^M ≢ 1 (mod q)`.
Hence `gcd(a^M − 1, N) = p`.

This is §3 run on **one** CRT component. Generation that lets `p−1` (or `q−1`)
be smooth hands the attacker a one-sided annihilator. The same story with
Lucas sequences in `ℤ[√Δ]` is Williams’ `p+1` method, when `p+1` is smooth.

A **safe prime** `p = 2r+1` with `r` prime makes `p−1 = 2r`; the only way it is
`B`-smooth is if `r ≤ B`. A **strong prime** asks the same of `p+1` and of
`(p−1)/2`. These are not decorations — they are the generation-side refusal
of the one-sided annihilator.

### 6.4 Small private exponent — Wiener / Boneh–Durfee

Write `e d = 1 + k φ(N)`. Then

```
|e/N − k/d|  =  |k(N−φ) − 1| / (N d),     N−φ = p+q−1.
```

For balanced primes `p+q−1 < 3√N`, so the public ratio `e/N` approximates the
unknown rational `k/d` to within `~ k/(d √N)`. If `d` is small then `k < e` is
also small (because `d < φ` forces `k = (ed−1)/φ < e`), and the approximation
falls inside the continued-fraction basin `|α − k/d| < 1/(2d²)`. Wiener:
`d < ⅓ N^{1/4}` is enough. Boneh–Durfee push the exponent to `N^{0.292}` by
feeding the same bilinear relation to Coppersmith.

The weakness is that a short `d` makes the cofactor `k` a *short description*
of the annihilator `ed−1`. Generation that picks `d` first to be small (for
fast decryption) is choosing that short description.

### 6.5 Small public exponent — low-degree roots

`e = 3` is a legitimate inverse-mod-`λ` choice and does not, by itself, factor
`N`. It *does* make the RSA map a degree-3 polynomial. Coppersmith then finds
small or stereotyped roots: Hastad (the same message to ≥3 moduli),
Franklin–Reiter (related messages), stereotyped high bits. This is a
*message*-generation weakness as much as a key-generation one; it is listed
here because choosing `e = 3` is a generation decision that enables it.
`e = 65537` is the usual refusal.

### 6.6 Unbalanced primes — the small factor

If `p ≪ q` then `N` has a small prime factor. ECM (and, for tiny `p`, trial
division) has cost governed by `p`, not by `N`. Generation that uses a 256-bit
`p` and a 1792-bit `q` to make a 2048-bit `N` has a 256-bit secret, not a
2048-bit one.

### 6.7 Partial bits / special form — Coppersmith, ROCA

Knowing the high or low half of `p` (or a structured form `p = k M + (65537^a
mod M)`, as in ROCA) puts a small unknown in a modular polynomial of which
`N` is a multiple. Coppersmith recovers the unknown. Generation that leaks
bits of `p` — or samples `p` from a thin arithmetic progression — is again
choosing a short description of a CRT component.

### 6.8 CRT-RSA with small `d_p`, `d_q`

Implementations store `d_p = d mod (p−1)` for CRT decryption. If `d_p` is
small then `e d_p − 1` is a small multiple of `p−1`: a one-sided annihilator
with a short cofactor, i.e. §6.3 and §6.4 at once.

### 6.9 What “stronger keys with smaller parameters” has to mean here

A smaller `N` is safe only if none of the rows above apply. The generation
checklist that follows is the intent-spec for a keygen (rule 3): each item is
the refusal of one leak, and each has a theorem in `rocq/` stating the leak
it blocks.

| Generation obligation | Leak it refuses | Formal object |
|---|---|---|
| `|p−q|` large vs `√N` | Fermat | `FermatFactor` |
| independent prime draws | batch GCD | `SharedPrime` |
| `p−1` and `q−1` have a large prime factor | Pollard `p−1` | `PollardP1`, `StrongPrimes` |
| `p+1` and `q+1` likewise | Williams `p+1` | `StrongPrimes` (definition) |
| `d > N^{1/4}` (ideally `> N^{0.292}`) | Wiener / Boneh–Durfee | `Wiener` |
| `e` not tiny, or messages not stereotyped | Hastad / Coppersmith | `SmallExponent` |
| `p` and `q` within 1 bit | ECM on the small prime | `KeyGen.balanced` |
| no thin AP / leaked bits of `p` | ROCA / Coppersmith-on-`p` | recorded, lattice skipped |

The novel-weakness hunt is then: find a generation choice that is *not* on
this list, still produces a short or one-sided annihilator, and is cheap
enough that a smaller `N` would feel it. The formal objects above are the
rulers that tell you when you have found one.

### 6.10 Why these leaks are forced (not accidental)

RSA's public object is a product `N = p q` and a unit `e` of `ℤ/λ(N)ℤ`.
Everything an attacker is not supposed to have is a function of `{p, q}`:

```
λ(N)  = lcm(p−1, q−1)
φ(N)  = (p−1)(q−1)
d     = e⁻¹  (mod λ)
d_p   = d mod (p−1)
```

The group law on `(ℤ/Nℤ)*` is public. Fermat's little theorem is public:
`a^{p−1} ≡ 1 (mod p)` for every `a` not divisible by `p`. The *only* secret
is the integer `p−1` (and its twin `q−1`). An annihilator of the unit group
is any `M` with `λ | M`; an annihilator of one CRT component is any `M`
with `p−1 | M`. Section 3 showed that a full annihilator factors `N`. The
same argument run on one component factors `N` as soon as the other
component *disagrees*. So the cryptanalytic content of every classical
key-generation attack is one sentence:

> Generation chose `{p, q, e}` so that a useful `M` (or a useful
> description of `p` itself) is computable from `(N, e)` alone.

That is why the catalog is a list of *generation choices*, not of
clever algorithms. Fermat, Pollard, Wiener, Hastad, batch-GCD, ROCA
are different procedures for reading out a handle the generator left
lying on the public pair. They fail differently, but they all fail
the moment the handle is not there.

The leaks fall into five algebraic types. Every named attack in the
catalog is an instance of one type; a novel weakness has to be one
too, or it is not a weakness of this problem.

**Type A — the factors are geometrically close to a public quantity.**
`N` determines `√N`. If generation sampled `p` and `q` from a short
interval around `√N`, then `p+q` is nearly `2√N` and the identity

```
((p+q)/2)² − N  =  ((p−q)/2)²
```

makes the hidden sum a small search from a public starting point.
Unbalanced primes are the same type with a different public quantity:
the small prime *is* at most `√N`, and if it is much smaller the
search (trial / ECM) is over `p`, not over `N`. Bit leaks and thin
APs (ROCA) are Type A with a *shifted* public quantity: a known
prefix, suffix, or residue class of `p` leaves a small unknown.

**Type B — a one-sided annihilator is public.**
Fermat's little theorem does not need a secret to *state*. It needs a
secret to *instantiate*, because you must know `p−1`. Smoothness of
`p−1` removes that requirement: every prime factor of `p−1` is at
most `B`, so `lcm(1..B)` is a public multiple of `p−1`. Williams
`p+1` is the same fact in the rank-2 Lucas module (the other cyclotomic
that a prime divides). A short CRT exponent `d_p` is Type B with a
short cofactor: `e d_p − 1` is a multiple of `p−1` of size `< e · d_p`.

**Type C — the full annihilator has a short description.**
`e d = 1 + k φ(N)` is a bilinear relation between public `e` and
secret `(d, k, φ)`. A short `d` forces a short `k` (`d < φ ⇒ k < e`).
The public ratio `e/N` is then a continued-fraction approximation to
the unknown rational `k/d`. Wiener reads it off; Boneh–Durfee feed the
same relation to a lattice. Generation that picks `d` first, to make
decryption cheap, is volunteering that short description.

**Type D — two public objects share a CRT component.**
Unique factorization is an algorithm the moment you hold two multiples
of `p`. Independent generation is the only defence. A broken RNG, a
cloned VM snapshot, a factory default, a shared prime cache — all
produce Type D. There is no search and no lattice.

**Type E — the public map is a low-degree polynomial with a small root.**
`e` is the degree of `m ↦ m^e (mod N)`. Coppersmith extracts roots
smaller than `N^{1/e}` (and stereotyped or related roots after a
change of variables). Choosing `e = 3` does not factor `N`; it makes
the *message* the small unknown. This is as much a padding obligation
as a key-generation one, but `e` is chosen at generation time.

These five types share a single generation-side invariant:

```
no short, one-sided, shared, or geometric handle on {p, q, λ}
is a function of the public pair (N, e) and of cheap public
computation (smooth lcm, continued fractions, gcd, √N, LLL
in small dimension).
```

`KeyGen.satisfies_keygen` is the formal refusal of that invariant's
negation, item by item. A generator that discharges it may use a
smaller `N` *honestly*: the bits you would have spent as margin
against a Type-A–E leak are no longer doing any work, and the
remaining attack is GNFS on `N` itself.

### 6.11 What a novel weakness would have to be

A new key-generation attack that justified smaller honest parameters
must do one of the following, and the existing theorems are the
rulers that say when it has:

1. **A new Type-A geometry.** A public function `f(N, e)` that lands
   close to `p`, `q`, `p+q`, or `p−q` for a generation distribution
   that current keygens actually use. Fermat is the case `f = ⌈√N⌉`.
   ROCA is the case `f =` “the public residue class”. Close-prime
   *bit-balanced* generation (`q = nextprime(p+2)`) is already
   classified; the open question is whether some other common
   sampling (increment-from-random-start with a short walk, shared
   high bits between `p` and `q`, a hidden linear relation) produces
   a similarly short gap.
2. **A new Type-B module.** A cheaply-evaluated sequence congruent to
   `0` or `1` modulo `p` whose period divides a smooth function of
   `p` other than `p−1` or `p+1`. Cyclotomic extensions of higher
   order (Aurifeuillean factorizations, higher Lucas / Lehmer
   sequences) are the classical candidates; they are *not* a new
   type, they are Type B with a different recurrence. A genuinely
   new Type B would be a public annihilator that is *not* a
   cyclotomic period of `p`.
3. **A new Type-C relation.** A bilinear (or low-degree) identity
   linking `(N, e)` to a short unknown other than `(k, d)`. The
   Boneh–Durfee lattice is the present frontier of this type
   (`d < N^{0.292}`); a new relation that let `d` be as large as
   `N^{1/2−ε}` and still leaked would shrink honest `d`, and
   therefore honest `N`.
4. **A new Type-D collision.** A generation process whose outputs
   are not independent as elements of `(ℤ/Nℤ)*` even when the
   primes themselves are distinct — e.g. a shared algebraic factor
   of `p−1` and `p'−1` large enough to give a common annihilator
   without a common prime. Batch GCD does not see this; a batch
   *order* attack would.
5. **A new Type-E small root** that is a function of the *key* rather
   than the message: a generation-side polynomial of small degree
   with a small root derived from `p` or `d`, not from `m`.
   Coppersmith-on-leaked-bits is the known case. A keygen that
   implicitly satisfies such a polynomial (a “hidden” ROCA) is the
   thing to look for.

What will *not* count, and should not be spent formalizing as a
“new attack”: a correctly generated 2048-bit key with `e = 65537`,
safe-ish primes, full-size `d`, and independent entropy. That is
the baseline. Extra bits of `N` above the GNFS cost of that
baseline are insurance against an unclassified leak; the point of
this development is to make that insurance *accountable*.

## 7. Honest scope of the key-generation development

Machine-checked, and CAS-pinned:

- Fermat identity, recovery at `(p+q)/2`, far-apart lower bound on
  `|p−q|/2` (`FermatFactor`; `cas/08`).
- `gcd(pq₁, pq₂) = p` (`SharedPrime`; `cas/09`).
- One-sided annihilator `p−1 | M` splits `N` when the `q`-side
  disagrees; smoothness is the generation choice that makes such an
  `M` public (`PollardP1`; `cas/10`).
- Safe primes refuse that `M` (`StrongPrimes.safe_prime_resists_p1`;
  `cas/10`).
- Wiener identities, `d < φ ⇒ k < e`, integer basin
  (`Wiener`; `cas/11`, including continued-fraction recovery of `k/d`).
- Hastad: CRT lift of three cube-ciphertexts *is* `m³` when it fits
  (`SmallExponent.hastad_cube_if_small`; `cas/12`).
- CRT-RSA: `e d_p ≡ 1 (mod p−1)`, so `e d_p − 1` annihilates the
  `p`-side (`CRTRSA`; `cas/10`).
- Keygen intent-spec and the refusal lemmas (`KeyGen`).
- Bit-leak / ROCA *shape* (`BitLeak`).
- Cyclotomic product identities `p^k−1 = ∏ Φ_d(p)` for `k ∈ {2,3,4,6}`
  (`Cyclotomic`; `cas/14`).
- Batch order: one public `M` splits two coprime moduli
  (`BatchOrder.batch_p1_splits_pair`; `cas/15`).
- Classical Wiener sufficient criterion `36 d⁴ < N` plus `k ≤ d`
  (`Wiener.wiener_classical_sufficient`; `cas/16`).
- Shared-high-bits / increment-window / adjacent-odd geometries
  (`KeyGenGeom`; `cas/17`).
- Named distributions fail the matching ruler (`KeyGenSampler`;
  `cas/13`).

Not proved, and not claimed:

- Williams’ Lucas recurrence (definition only: `williams_handle`,
  `pp1_resistant`).
- Boneh–Durfee / Coppersmith / LLL / Howgrave–Graham (interface in
  `Lattice`, `BitLeak`).
- Franklin–Reiter gcd in `(ℤ/Nℤ)[X]` actually having degree 1.
- A general density statement that a random `p−1` is not `B`-smooth
  (only the implication “large prime factor ⇒ not `B`-smooth”).
- Any hardness of RSA, and any claim that discharging
  `satisfies_keygen` makes a particular bit length “enough”.

φ vs λ is still distinguished: Wiener is proved in the φ-form
(`ed ≡ 1 (mod φ)`); CRT-RSA and the RSA instance itself use λ.

## 8. What the five avenues actually showed

The catalog in §6 is a list of *known* handles. The work in this
section is the first pass at using those handles as rulers on
generation distributions that honest-looking code still uses, and
at filling the four gaps named in §6.11.

### 8.1 Sampler — distributions vs rulers

`cas/13` draws 16-bit primes from several procedures and scores
them against `kg_far`, `kg_balanced`, smoothness, and batch GCD.

| Distribution | Far-gap `n−4` | Balanced | What failed |
|---|---|---|---|
| Independent random 16-bit | 29/40 pass | 40/40 | — (the baseline) |
| `q = nextprime(p+1)` | 0/20 | yes | Type A: twins |
| Shared top half | 0/20 | — | Type A: prefix |
| Increment window `2^{n/2}` | 0/20 | — | Type A: short walk |
| Tiny 3-prime pool | — | — | Type D: `gcd = p` |
| Independent 16-bit moduli | — | — | 0/20 gcd hits |

Bit-balanced independent sampling *does* pass the geometric
rulers at this size. The failures are all procedures that look
like “pick a random prime” and are not: nextprime-adjacent,
shared prefix, a common increment start, a recycled prime pool.
`KeyGenSampler.v` names each distribution and proves the ruler
it fails. Frequencies are CAS, not theorems.

### 8.2 Type B beyond `p±1`

`Φ_1(p) = p−1`, `Φ_2(p) = p+1`, `Φ_3(p) = p²+p+1`,
`Φ_4(p) = p²+1`, `Φ_6(p) = p²−p+1`, with the product identities
`p^k − 1 = ∏_{d\|k} Φ_d(p)` for `k ∈ {2,3,4,6}`.

Two concrete misses of “safe / strong”:

- `p = 47` is safe (`Φ_1 = 46 = 2·23`) and `Φ_2 = 48` is
  3-smooth. Safe primes refuse Pollard and *invite* Williams.
- `p = 653`: `Φ_1` has prime factor 163, `Φ_2` has 109, and
  `Φ_3 = 427063 = 7 · 13² · 19²` is 19-smooth. A generator that
  checks “strong at `B = 20`” still leaks the cubic handle.

`cyc_strong` is the generation obligation that closes this gap.
Lucas / extension-field evaluation is still not formalized; the
handle is the period, which is.

### 8.3 Type D without a shared prime

Two moduli `N₁ = p q`, `N₂ = p' q'` with four distinct primes
have `gcd(N₁, N₂) = 1`. If `p−1 | M` and `p'−1 | M` for a public
`M` (both `B`-smooth), the same `M` splits both. Batch GCD
returns 1; batch Pollard returns `{p, p'}`.

A shared prime factor `r | gcd(p−1, p'−1)` that is itself large
is a different handle: both primes sit on the AP `X ≡ 1 (mod r)`.
Once `r` is known this is Type A, not Type D. `cas/15` pins both
stories (`r = 101`).

### 8.4 Type C past Wiener

Proved: if `e < φ` then `k < d`; if also the primes are balanced
and `36 d⁴ < N`, the pair is in the integer CF basin
(`wiener_classical_sufficient`). That is a sufficient criterion,
not the slogan `d < ⅓ N^{1/4}`.

CAS on `N = 587·823`, exact continued fractions (no `t_REAL`
rounding): the marker `18 d³ < N` recovered 5/9 instances (it is
*not* sufficient); `d = 7` satisfies `36 d⁴ < N` and is in the
basin; past-Wiener (`18 d³ ≥ N` but `d³ < N`) recovered 0/16 by
CF. Boneh–Durfee’s `0.292` remains an LLL claim, recorded as
`bd_past_wiener` / `boneh_durfee_delta_milli = 292`, not a
theorem.

### 8.5 Type A geometries modern keygens commit

Three generation-side bounds, each implying `~ kg_far`:

- Shared high bits: `|p − q| < 2^s`.
- Increment window `[x, x+W)`: `|p − q| < W`.
- Adjacent odds: `|fermat_diff| = 1`.

On 20-bit constructed pairs (`cas/17`): shared-prefix Fermat
steps `= 0`, independent pair `= 2687`. The geometry is not
“Fermat is clever”; it is that a shared prefix or a short
increment walk places `p+q` next to `⌈√N⌉`.

### 8.6 What this changes about smaller honest `N`

A generator that already discharges `satisfies_keygen` should
also refuse `cyc_strong` (Φ₃, Φ₄, Φ₆) and the three Type-A
geometries above. Those are not new *types*. They are listed
leaks that common code still commits. Extra bits of `N` spent
as margin against them can be returned once the generator
refuses them by construction.

A genuinely new weakness is still one of the five shapes in
§6.11 that is *not* a row of this list. The sampler is the
place to look for one: any distribution that passes every
named ruler and still has a cheap handle is the object.

## 9. Hardness claims

The rest of this document is about *algebra*: annihilators, leaks,
and the winning conditions of named problems. A hardness claim is a
different kind of object. This section says what one is, which
named claims exist in this domain, which arrows between them are
theorems, which are open, and which are false on a given KeyGen.
Nothing here is an axiom that “RSA is hard.”

Companion: [`notes/hardness.md`](notes/hardness.md). Relation-level
arrows are in `rocq/Hardness.v`, pinned by `cas/18_hardness.gp`.

### 9.1 A search problem is not an assumption

`Problem_RSA N e y x` is the proposition `x^e ≡ y (mod N)`. It is a
*winning condition*. For `gcd(e, λ(N)) = 1` and `y` a unit, a
witness `x` *exists*: the `e`-power map is a permutation of
`(ℤ/Nℤ)*`, and `x ≡ y^d (mod N)` is one (`rsa_units_are_eth_powers`).
Existence is Euler/Carmichael, not cryptography.

The same is true, more sharply, of strong RSA. The pair `(x, e) = (1, 2)`
wins on the challenge `y = 1` for every `N > 1`
(`strong_RSA_trivial_at_one`). The bare relation is inhabited at
trivial points.

A **hardness assumption** is a statement about *algorithms* and a
*distribution*:

```
Pr[ A wins on (N, e, y)  |  (N, e) ← KG(1^n),  y ← D_{N,e} ]  ≤  negl(n)
```

for every algorithm `A` in a named class (PPT, circuits of size
`T(n)`, …). Until `KG`, `D`, the class, and the winning condition
are in the sentence, “RSA is hard” is a slogan.

`UnknownOrder.v` writes down winning conditions. It does not
assume they are hard. That is deliberate (rule 5). An axiom
`RSA_hard : Prop` that is never discharged is how a development
starts proving things about the wrong object.

### 9.2 Four ingredients of a claim

1. **The KeyGen distribution `KG`.** Samples `(N, e)` and discards
   `{p, q, d}`. “RSA is hard” is a claim about *one* `KG`. It is
   false for nextprime twins, a shared prime pool, `d < N^{1/4}`,
   a `B`-smooth `p−1`, or `p = 653` against a cubic method at
   `B = 20`. Section 6 is the catalog of `KG` on which the claim
   is *refuted*, not merely unproven. `satisfies_keygen` (plus
   `cyc_strong` and the Type-A geometries of §8.5) is the closest
   thing in this repo to a description of a `KG` that the catalog
   does not immediately kill.

2. **The algorithm class.** Polynomial time in `n = |N|`, or
   “cheaper than GNFS on `N`”, or a concrete circuit bound. This
   repo has no complexity theory and does not introduce one by
   axiom.

3. **The winning condition.** Search (output a root / a factor /
   an order) versus decision (distinguish two distributions).
   For RSA with `gcd(e, λ) = 1` the decision problem on units is
   vacuous — see §9.3. Search is the content.

4. **The challenge distribution `D`.** Uniform in `(ℤ/Nℤ)*` is
   the usual RSA challenge. Uniform in `{0, …, N−1}` is
   different: a non-unit leaks a factor by `gcd`. Textbook
   encryption of a small or stereotyped `m` is a *different*
   `D` (Type E). A claim that underwrites OAEP is not a claim
   that underwrites raw RSA of ASCII.

Omit any one of the four and the sentence no longer has a truth
value that this project can use.

### 9.3 The `e`-power map is a one-way permutation, not a predicate

Let `G = (ℤ/Nℤ)*` and `gcd(e, λ(N)) = 1`. Then

```
x ↦ x^e   :  G → G
```

is a group automorphism. Every unit is an `e`-th power of a
unique unit. Consequently:

- “Is `y ∈ G` an `e`-th residue?” is always yes. There is no
  decisional RSA problem on units analogous to quadratic
  residuosity.
- If `x` is uniform in `G` then `x^e` is uniform in `G`. The
  pair `(N, e, x^e)` is distributed identically to `(N, e, y)`
  for uniform `y ∈ G`. Distinguishing them is impossible
  information-theoretically.
- The assumption, when it is made, is **one-wayness of a
  trapdoor permutation**: given `y`, find the unique `x ∈ G`
  with `x^e = y`.

Decision becomes a real problem only when the map is *not* a
permutation, i.e. when `gcd(e, λ) > 1`:

- **Quadratic residuosity (QR).** `e = 2` always divides `φ(N)`
  for odd `N`. Squaring is 4-to-1 on `(ℤ/Nℤ)*` for distinct odd
  primes. “Is `y` a square?” is a predicate, and the Goldwasser–
  Micali assumption is that it is hard to evaluate without the
  factors.
- **Φ-hiding.** A prime `e` is chosen to *divide* `φ(N)` (or
  not). The hiding assumption is that these two cases are
  indistinguishable given `(N, e)`. The `e`-power map is then
  `e`-to-1, and `e`-th residuosity is a predicate. This is
  incompatible with a standard RSA instance, which *requires*
  `gcd(e, λ) = 1`.
- **DCR (Paillier).** Decisional composite residuosity in
  `(ℤ/N²ℤ)*`: `e = N`, a different group. Not an RSA-in-`G`
  assumption.

These decision assumptions are neighbouring, not instances of
`Problem_RSA`. They are recorded so that “decisional RSA” is
not silently introduced later as if it were the search problem
with a bit of output.

### 9.4 The named search problems

All are relations. A solver is given the input and must produce
the output. Hardness, if claimed, is over `KG` and a challenge
as in §9.2.

| Problem | Input | Output | Winning condition |
|---|---|---|---|
| **Factoring** | `N` | `f` | `1 < f < N` and `f \| N` |
| **RSA** | `(N, e, y)` | `x` | `x^e ≡ y (mod N)` |
| **Strong RSA** | `(N, y)` | `(x, e)` | `e > 1` and `x^e ≡ y (mod N)` |
| **Adaptive root** | `(N, y)` | `(x, e)` | same relation as strong RSA |
| **Order** | `(N, a)` | `k` | `k = ord_G(a)` |
| **Low-order** | `(N, B)` | `(a, k)` | `ord_G(a) = k ≤ B` and `a ≠ 1` |
| **One-sided low-order** | `(N, B)` | `(a, k)` | `a^k ≡ 1 (mod p)` and not `(mod q)`, `k ≤ B` |

The last row is not a standard *named* assumption; it is the
winning condition of Type B / Pollard, and it is the one that
*factors* `N`. Low-order *in `G`* does not: `a^k ≡ 1 (mod N)`
is two-sided (`Hardness.one_sided_low_order_factors`).

Adaptive root and strong RSA are the same relation
(`adaptive_root_is_strong_RSA`). The name changes with the
*group*. On `(ℤ/Nℤ)*` there is a trapdoor `λ`. In a class group
there is no known `λ`, and the same relation is an assumption
about a group with no setup. Wesolowski VDFs, unknown-order
accumulators, and Pietrzak-style proofs use that second
reading. Writing `Problem_AdaptiveRoot` as an alias is honest
about the relation and silent about the group; a later class-
group file must not inherit a trapdoor that is not there.

### 9.5 Arrows that are theorems (relations)

No running times. These are implications between winning
conditions, in `Hardness.v`.

```
{p, q}
  │
  │  construct λ = lcm(p−1, q−1), d ≡ e⁻¹ (mod λ)
  ▼
λ  or  d  or  φ
  │
  ├──────────────────────────────────────────────┐
  │  y ↦ y^d                                     │  (y, λ+1)
  ▼                                              ▼
RSA roots on units                    strong RSA on every unit
  │
  │  rsa_solution_is_strong_RSA
  ▼
strong RSA for that fixed e


order k of a unit
  │
  │  order_divides_lambda
  ▼
k | λ


one-sided a^k ≡ 1 (mod p), not (mod q)
  │
  │  one_sided_low_order_factors
  ▼
Problem_Factor N p
```

Commentary, so the diagram is not over-read:

- **RSA ≤ Factoring**, in the usual reduction language: an
  algorithm that factors (or that is given `λ` or `d`) solves
  RSA on units. We have the algebra
  (`trapdoor_inverts_RSA`, `rsa_dec_enc_units`). We do not have
  a cost bound, because we do not have a cost model.
- **Strong RSA is trivial given `λ`:** `(y, λ+1)` wins for every
  unit `y` (`lambda_solves_strong_RSA`). That is why adaptive
  root is only an assumption in a group whose order is hidden
  *and* has no trapdoor construction of `λ`.
- **An RSA root is a strong-RSA witness** for the prescribed
  `e`. Solvability of RSA implies solvability of strong RSA *at
  that `e`*. Hardness runs backwards: if no algorithm solves
  strong RSA, then no algorithm solves RSA (same `KG`, same
  `y`). The converse hardness implication is false, and is the
  reason strong RSA is called *stronger* (harder to believe,
  easier to use in proofs).
- **Order of a unit divides `λ`.** Sampling orders and taking
  lcms is the usual way to *learn* `λ` from an order oracle.
  Completeness of that procedure (enough random `a` generate
  the 2-primary and odd parts of `λ`) is a density statement
  and is not proved.
- **One-sided small exponent factors; two-sided small order
  does not.** Confusing `Problem_LowOrder` with Pollard is how
  a “low-order assumption” gets stated as if it were Type B.
  Low-order in `G` leaks a divisor of `λ`. One-sided low-order
  leaks a factor of `N`.

### 9.6 Arrows that are not theorems

```
RSA inverter (random y, no d)
        ─ ─ ─ ─ ? ─ ─ ─ ─ ►     Factoring

straight-line reduction, small e
        ─ ─ ─ ─ unlikely ─ ►     Factoring
        (Boneh–Venkatesan)

knowing (e, d)
        ────── yes ────── ►     Factoring
        (Miller / Coron–May; algebra in this repo)
```

- **Factoring ≤ RSA is open.** An oracle that inverts `x ↦ x^e`
  on random challenges is not known to yield `{p, q}`. Boneh–
  Venkatesan indicate that a *straight-line* reduction from
  factoring to low-exponent RSA would collapse in ways we do
  not expect. This repo will not treat “RSA-hard ⇒ Factoring-
  hard” as a design target.
- **Coron–May is not that converse.** Given the *secret* `(e, d)`,
  not an inversion oracle, one factors. That is the annihilator
  of §3, and it is already formalized. Mixing the two is the
  most common way to overclaim the trapdoor theorems.
- **RSA ≤ Strong RSA as hardness** is the informal reading of
  `rsa_solution_is_strong_RSA` and is *not* a reduction in the
  other direction. A strong-RSA solver may return an `e` other
  than the prescribed one and so need not invert the RSA map.
- **Order ≈ Factoring on `N = pq`.** A multiple of `λ` is a
  Miller annihilator, so an algorithm that outputs `λ` (or a
  small multiple) factors. An algorithm that outputs
  `ord(a)` for enough `a` *should* give `λ` by lcm; that
  “enough” is unproved here. In a class group the same order
  problem is not known to yield a public factorization, which
  is the point of moving the assumption.
- **GNFS is not an assumption and not a reduction.** It is the
  best general *attack* on Factoring, with heuristic complexity
  `L_N[1/3, (64/9)^{1/3}]`. The sentence “the remaining attack
  is GNFS on `N`” (§6.10, §8.6) is a report on the state of
  cryptanalysis for a `KG` that refuses the catalog. It is not
  a theorem, and discharging `satisfies_keygen` does not make a
  bit length “enough”.

### 9.7 Neighbouring assumptions, kept out of the RSA file

Recorded so they are not later smuggled in as corollaries of
`Problem_RSA`.

| Assumption | Object | Why it is not RSA |
|---|---|---|
| QR / Rabin | squares in `(ℤ/Nℤ)*` | `e = 2` is not coprime to `λ`; see §10 |
| Φ-hiding | `e \| φ(N)` vs not, given `(N, e)` | standard RSA *forbids* `e \| λ` |
| DCR | `N`-th powers in `(ℤ/N²ℤ)*` | different group |
| Partial-domain RSA | invert on a small interval | different `D`, Coppersmith-adjacent |
| RSA-FDH / RSA-PSS / OAEP | inversion in a hash wrapper | a *scheme* assumption; the game includes the hash |

Textbook RSA encryption of a message from a low-entropy set is
not the RSA assumption of §9.2. It is Type E. Hastad, Coppersmith
stereotyped messages, and Franklin–Reiter live there. A hardness
claim that samples `y` uniformly in `G` is silent about them; a
hardness claim that is supposed to underwrite raw RSA of a PIN
is already false at `e = 3`.

### 9.8 Hardness is relative to KeyGen: leaks are refutations

Fix a winning condition, say `Problem_RSA` or `Problem_Factor`.
A **refutation** of the corresponding assumption on `KG` is an
algorithm that wins with non-negligible probability on samples
from that `KG`. Every row of the §6 catalog is such a
refutation, with an explicit algorithm:

| `KG` does this | Algorithm | What it refutes |
|---|---|---|
| close / shared-prefix / increment-window primes | Fermat | Factoring, RSA, Order |
| shared prime pool | `gcd` | Factoring, RSA, Order |
| smooth `p−1` / `Φ_n(p)` | Pollard / cyclotomic | Factoring, RSA, Low-order (one-sided), Order |
| short `d` | Wiener (CF); BD if one grants LLL | Factoring, RSA |
| tiny `e`, stereotyped `m` | Hastad / Coppersmith | RSA on *that* `D`; not Factoring |
| unbalanced `p` | ECM / trial | Factoring, RSA |
| thin AP / leaked bits of `p` | Coppersmith | Factoring, RSA |

Type E is the only row that can kill RSA-the-search-problem on
a restricted `D` without factoring `N`. That is why it does not
sit on the same arrow as the others, and why `e` is a generation
choice even though it does not, by itself, produce an annihilator
of `G`.

The residual claim, written so it has a truth value:

> If `KG` refuses every named leak, then every attack formalized
> in this repo fails on samples from `KG`, and the cheapest
> *published* attack on the resulting `(N, e)` is general-purpose
> factoring of `N`.

That is not “RSA is hard”. It is “we have not refuted RSA on
this `KG` with the rulers we have.” Extra bits of `N` above the
GNFS cost of that baseline are insurance against an unclassified
leak. The point of the catalog is to make that insurance
accountable (§6.10, §8.6).

### 9.9 What “stronger keys with smaller parameters” is allowed to mean

A smaller `N` is a claim that the *min cost* of the cheapest
applicable attack has not dropped. That min is taken over:

- general Factoring (GNFS, ECM on the smaller prime, …),
- every Type A–E algorithm that `KG` does not refuse,
- scheme-level attacks if `D` is not uniform in `G`.

If `KG` leaks, extra bits of `N` do not raise that min. If `KG`
refuses the catalog, the min is the Factoring cost of `N`, and
bits of `N` are the right parameter. Returning bits that were
being spent as margin against a *refused* leak is then honest.
Returning bits against an *unrefused* leak, or against an
unclassified one, is not a hardness theorem — it is a bet that
§6.11 is empty.

No bit-length recommendation in this repo is a theorem.

### 9.10 What must not be axiomatized

- `RSA_hard`, `Factoring_hard`, `sRSA_hard` as global `Prop`s.
  A later protocol file that needs an assumption should take
  `KG` as a parameter and hypothesize that `KG` does not leak
  the catalog (and, if it wishes, that Factoring is hard on the
  induced `N`-distribution). The hypothesis is then *about a
  named `KG`*, and a leak in that `KG` is a broken hypothesis,
  not a mysterious axiom failure.
- “Decisional RSA” on units with `gcd(e, λ) = 1`.
- “Low-order is Pollard” (two-sided vs one-sided, §9.5).
- “RSA-hard ⇒ Factoring-hard.”
- “Discharging `satisfies_keygen` makes `n`-bit `N` enough.”
- ERH, LLL, GNFS cost, Miller density ≥ 1/2 as ingredients of a
  hardness claim. They may appear as *named skips* in an attack
  cost, not as axioms that close a proof of security.

### 9.11 Honest scope of the hardness development

Machine-checked, and CAS-pinned (`Hardness.v`, `cas/18`):

- Every unit is an `e`-th power under an RSA instance
  (`rsa_units_are_eth_powers`); `enc ∘ dec = id` on units.
- Trapdoor inverts RSA on units (`trapdoor_inverts_RSA`).
- An RSA solution is a strong-RSA solution for that `e`.
- `λ` yields the trivial strong-RSA witness `(y, λ+1)` on units.
- Strong RSA / RSA relations are inhabited at `y = 1`.
- The order of a unit divides `λ`.
- One-sided `a^k ≡ 1 (mod p)` splits `N`; this is
  `Problem_Factor`.
- Adaptive root and strong RSA are the same relation.

Not proved, and not claimed:

- Any PPT bound, any negligible function, any advantage.
- Factoring ≤ RSA; completeness of lcm-of-orders → `λ`.
- Hardness of RSA, strong RSA, adaptive root, order, QR, DCR,
  Φ-hiding, or Factoring, on any `KG`.
- GNFS complexity; that a leak-free `KG` leaves only GNFS.
- Decision problems (QR, Φ-hiding, DCR) as formal objects.
- A probability-space formalization of §9.2.

φ vs λ remains distinguished: trapdoor inversion uses the
`λ`-inverse that the instance already carries. Strong RSA via
`λ+1` uses Carmichael, also `λ`. Wiener (Type C) remains the
`φ`-form, and is an attack, not an assumption.

## 10. Rabin–Williams: the same group, a different map

RSA at a unit exponent and Rabin–Williams (Rabin signatures with
Williams’ 1980 tweak) are the two standard *trapdoor* problems
in `(ℤ/Nℤ)*`. They share the group and the modulus; they do not
share the map, the KeyGen congruences, or the reduction to
Factoring. This section is the overlap, and the reason `p` and
`q` are chosen the way they are. Companion:
[`notes/rabin-williams.md`](notes/rabin-williams.md). Formal
objects: `QuadResidue.v`, `RabinWilliams.v`, `cas/19`.

### 10.1 The same group, a forbidden exponent

Both problems take `N = p q` and work in `G = (ℤ/Nℤ)*`, whose
order `φ(N)` and exponent `λ(N)` are hidden. Rabin is the map

```
x  ↦  x²   (mod N).
```

That is RSA at `e = 2`, except `e = 2` is *excluded* from an
`RSAInstance`: `λ` is even for odd primes, so
`gcd(2, λ) = 2 ≠ 1` (`two_not_rsa_exponent`). The `e`-power
map of §9.3 is a permutation only when `gcd(e, λ) = 1`.
Squaring is 4-to-1 on units of a distinct-odd-prime product
(CRT: two square roots mod `p`, two mod `q`). The kernel of
squaring is exactly the 2-torsion `{±1} × {±1}` — four square
roots of 1, of which two are the non-trivial ones that split
`N` (`nontrivial_sqrt1_splits`).

So Rabin is not “RSA with a small `e`.” It is the neighbouring
problem that §9.3 said becomes a *predicate* (quadratic
residuosity) the moment `e` shares a factor with `λ`. Search
Rabin is: given a square `y`, find a preimage. Decision Rabin
is QR, which RSA-with-coprime-`e` does not have.

### 10.2 Why inversion is equivalent to Factoring here

Pick a random unit `r`, publish `y = r²`, ask an inversion
oracle for a square root `s` of `y`. The four roots are
`±r, ±w` with `w ≢ ±r`. With probability 1/2 the oracle
returns a representative of `±w`, and then

```
x² ≡ y² (mod N),   x ≢ ± y (mod N)
  ⇒  1 < gcd(x − y, N) < N
```

(`rabin_roots_split`). This is a *random-self-reduction* of
Factoring to Rabin inversion, tight up to a factor of two.
RSA has no such theorem: an oracle that inverts `x ↦ x^e` on
random challenges is not known to yield `{p, q}` (§9.6).
Possession of `d` factors (Miller / Coron–May); possession of
an inversion oracle does not, so far as anyone has proved.

That is the hardness-theoretic overlap, stated so it cannot be
blurred: both problems are easy given `{p, q}`; only Rabin is
known to be *as hard as* Factoring.

### 10.3 Williams primes: `p ≡ 3 (mod 8)`, `q ≡ 7 (mod 8)`

A square root mod `p` is cheap when `p ≡ 3 (mod 4)`: if
`a^{(p−1)/2} ≡ 1` then `a^{(p+1)/4}` squares to `a`
(`sqrt_mod4_3_correct`). Integers with both primes
`≡ 3 (mod 4)` are *Blum integers*. Williams (1980) refines
Blum by a further condition mod 8, so that a *public* choice
among four obvious associates of the message is a square:

```
p ≡ 3 (mod 8)     (hence p ≡ 3 (mod 4);  (−1/p) = −1,  (2/p) = −1)
q ≡ 7 (mod 8)     (hence q ≡ 3 (mod 4);  (−1/q) = −1,  (2/q) = +1)
```

(or the two primes swapped). The symbols for `−1` are Euler
and are proved (`neg1_euler_mod4_3`). The symbols for `2` are
the classical `(2/p) = (−1)^{(p²−1)/8}`; they are the reason
for the mod-8 split, and they are not proved here (Gauss’s
lemma). CAS pins them on the working pair `11, 23`.

Let `(a/p) = α`, `(a/q) = β` with `α, β ∈ {±1}`. The four
tweaks have Legendre pairs

```
 a    :  ( α,  β)
−a    :  (−α, −β)      because (−1/p)=(−1/q)=−1
 2a   :  (−α,  β)      because (2/p)=−1, (2/q)=+1
−2a   :  ( α, −β)
```

These four pairs are a permutation of `{±1}²`. Exactly one of
them is `(+1, +1)` (`williams_tweak_exists`,
`williams_tweak_unique`). That unique representative is a
square mod `p` *and* mod `q`, hence a square in `G`. The
signer computes the two prime-side roots by the
`(p+1)/4` formula and combines them by CRT. The verifier
checks that `s²` is one of `{±H, ±2H}` (`rw_verify`).

Without the mod-8 split the four pairs are not a permutation
of `{±1}²` and uniqueness fails. The textbook RSA primes
`p = 11`, `q = 17` are not a Williams pair: `17 ≡ 1 (mod 8)`
and `17 ≡ 1 (mod 4)`, so `−1` is a residue mod `q` and the
sign-tweak does not flip both Legendres. RW KeyGen is *not*
“RSA KeyGen with `e = 2`.”

### 10.4 What the congruences force on `p−1` and `q−1`

`p ≡ 3 (mod 4)` means `p − 1 = 2 · (odd)` (`blum_prime_pminus1_form`).
The 2-adic valuation `v₂(p−1)` is exactly 1; same for `q`.
Thus `v₂(λ) = 1`. The 2-Sylow of `(ℤ/pℤ)*` is just `{1, −1}` —
the simplest possible 2-structure. Miller-from-`λ` then has
`s = 1`: a single squaring, and a non-trivial square root of 1
is already a factor. Pratt’s unique-order-2 check on a prime
(`duality_unique_order_2_on_prime`) is the same fact.

Safe primes are compatible. A safe prime is `p = 2r + 1` with
`r` odd, hence automatically `p ≡ 3 (mod 4)`. It is a Williams
`p` iff `r ≡ 1 (mod 4)` (so `p ≡ 3 (mod 8)`), and a Williams
`q` iff `r ≡ 3 (mod 4)` (so `p ≡ 7 (mod 8)`). The Type-B
obligation on the *odd* part of `p−1` is unchanged: `r` itself
must be a large prime, or at least not `B`-smooth.

`p+1` is complementary: `p ≡ 3 (mod 8)` gives `p+1 ≡ 4 (mod 8)`,
so `v₂(p+1) = 2`; `q ≡ 7 (mod 8)` gives `q+1 ≡ 0 (mod 8)`, so
`v₂(q+1) ≥ 3`. Williams `p+1` (Lucas) still applies if the
odd part of `p+1` is smooth. `cyc_strong` is not implied by
the mod-8 condition.

### 10.5 KeyGen: the RSA rulers plus a congruence

Every Type A–D leak of §6 still applies. Close Williams primes
are Fermat-food; a shared Williams prime is a batch-GCD;
smooth odd part of `p−1` is Pollard; short CRT exponents are
still one-sided annihilators. The extra obligation is

```
kg_rw p q  :=  p ≡ 3 (mod 8)  and  q ≡ 7 (mod 8)
```

(`rw_pair`). There is no public `e` to choose, so
`kg_e_not_tiny` is meaningless; the map *is* tiny (`e = 2`).
Type E is therefore *more* dangerous, not less: Coppersmith /
stereotyped messages see a degree-2 polynomial. Rabin
*encryption* of a raw message is the cautionary tale; RW as
used for *signatures* hashes first, so the challenge is a
digest, not a PIN. A hardness claim for RW signatures is a
claim about inversion on hash outputs, not about QR of ASCII.

### 10.6 Scheme shape, honestly scoped

Signing, reduced to the algebra we have:

1. Hash to a unit `H`.
2. Select the unique tweak `t ∈ {1, −1, 2, −2}` for which
   `t H` is a square mod `p` and mod `q` (the Legendre test;
   uniqueness is the combinatorics of §10.3).
3. Extract roots by `x ↦ x^{(p+1)/4}` and CRT.
4. Publish one of the four roots (a “principal” convention —
   e.g. even and in `(0, N/2)` — is a scheme choice, not
   proved here).

Verification: `s² mod N` is one of `{±H, ±2H}`. Completeness
follows from the sqrt formula plus CRT; uniqueness of the
tweak is the Williams lemma. We do not formalize a principal-
root convention, a hash wrapper, or a signature game.

### 10.7 Honest scope of the RW development

Machine-checked, and CAS-pinned (`QuadResidue`, `RabinWilliams`,
`cas/19` on `N = 11 · 23`):

- Blum form `p ≡ 3 (mod 4)` ⇒ `v₂(p−1) = 1`; mod-8 implies Blum.
- `λ` even; `e = 2` is not an RSA exponent.
- Euler QR direction; `p ≡ 3 (mod 4)` square-root formula.
- Euler for `−1` (mod-4).
- Williams combinatorics: exactly one of the four Legendre
  pairs is `(+1,+1)`.
- Two non-associated square roots split `N`.
- `rw_verify`: `s²` is a tweak of `H`.
- Exhaustive uniqueness of the QR tweak on every unit of 253;
  four roots; Rabin reduction recovers a factor.

Not proved, and not claimed:

- `(2/p)` as a theorem (Gauss); taken as the generation-side
  value that the mod-8 condition is there to force.
- Euler QNR direction (`a^{(p−1)/2} ≡ −1`).
- A principal-root convention; a hash; a signature game.
- PPT tightness of the 1/2 in the Rabin reduction (the
  splitting lemma is proved; the probability is not).
- That RW KeyGen without the §6 rulers is safe. It is not.

The residual comparison with RSA, in one sentence: same hidden-
order group, same catalog of KeyGen leaks, a map that is a
4-to-1 predicate rather than a permutation, a reduction to
Factoring that RSA does not have, and a mod-8 condition on
`{p, q}` whose only job is to make one of `{±H, ±2H}` a square.

## 11. The 2-primary part of `(ℤ/Nℤ)*`

The pieces in §§3–4, 9–10 — four square roots of 1, Pratt’s unique
order-2 element on a prime, Miller’s square-chain, Blum
`v₂(p−1) = 1`, Williams’ mod-8 split — are one object: the
2-Sylow of the unit group, read off the pair

```
(s, r)  :=  (v₂(p−1), v₂(q−1)).
```

This section is that object. Formal: `TwoPrimary.v`. CAS:
`cas/20_two_primary.gp`. Cyclicity of `(ℤ/pℤ)*` is used in the
*counting* model (CAS) and is not a Rocq hypothesis.

### 11.1 Valuations

An odd prime has `v₂(p−1) ≥ 1`. The residue of `p` mod 4 and 8
fixes the first few values:

| `p mod 8` | `v₂(p−1)` | Name |
|---|---|---|
| 3 | `= 1` | Blum / Williams `p` |
| 7 | `= 1` | Blum / Williams `q` |
| 5 | `= 2` | |
| 1 | `≥ 3` | |

Proved: `odd_prime_val2_ge1`, `blum_val2_is_1`, `mod4_1_val2_ge2`,
and `rw_pair_val2_11` (Williams ⇒ `(1,1)`). CAS: `v₂(10)=1`,
`v₂(12)=2`, `v₂(16)=4`, `v₂(40)=3`, `v₂(λ(11·17)) = max(1,4) = 4`.

`v₂(λ) = max(v₂(p−1), v₂(q−1))` is the form of `lcm` on
`2^{s}·odd` and `2^{r}·odd`. Proved: `val2_lcm_max`,
`val2_lambda_semiprime`, `lambda_val2_is_max`. The residue
table mod 8 is `mod8_3_val2_is_1`, `mod8_7_val2_is_1`,
`mod8_5_val2_is_2`, `mod8_1_val2_ge3`.

### 11.2 Four square roots of 1

On a prime, `x² ≡ 1` iff `x ≡ ±1` (`duality_unique_order_2_on_prime`).
On `N = pq` the CRT product is four combinations. They are
constructed (`sqrt1_pp = 1`, `sqrt1_mm = −1`, `sqrt1_pm` ≡ `(1,−1)`,
`sqrt1_mp` ≡ `(−1,1)`) and each squares to 1 (`four_sqrt1`). The
mixed ones are not `±1` (once `p, q ≠ 2`) and so split `N`
(`mixed_sqrt1_splits`).

This is Rabin inversion in miniature: a random square root of 1
that is not `±1` *is* a factor. Blum / Williams make the 2-torsion
*exactly* these four elements — there is no element of order 4 —
so Miller-from-`λ` has `s = 1`.

### 11.3 2-height and Miller mismatch

Write an odd `t` (the odd part of `p−1`, or of `λ`). The
**2-height** of a unit `a` at `p` is the least `k` with
`a^{t · 2^k} ≡ 1 (mod p)`. That `k` is `v₂(ord_p(a))`, and it
is at most `v₂(p−1)`.

If the heights at `p` and at `q` (same `t`) differ, some prefix
of the Miller chain is `1` on one CRT component and not the
other (`height_mismatch_splits`, via
`one_sided_low_order_factors`). Miller-from-`d` is the
corollary: `miller_t` is an odd multiple of `odd_part(λ)`
(`miller_t_multiple_of_lambda_odd`, because `v₂` is a
valuation), heights exist from `a^M ≡ 1`
(`miller_height_exists`), and a mismatch splits `N`
(`miller_from_d`).

The same-`t` discipline matters: `t` should be a common multiple
of the two odd parts (e.g. `odd_part(λ)`). Multiplying an odd
order by an odd integer does not change the 2-height. Using
`odd_part(p−1)` on one side and `odd_part(q−1)` on the other
is a different pair of heights; the theorem requires one `t`.

### 11.4 Counting, under cyclicity (formula in Rocq, realization CAS)

If `(ℤ/pℤ)*` is cyclic of order `2^{s} t` with `t` odd, then

```
P(v₂(ord) = 0)     = 2^{-s}
P(v₂(ord) = i)     = 2^{i−1−s}    (1 ≤ i ≤ s)
```

Independence across `p` and `q` gives

```
P(match)     = Σ_i P_p(i) P_q(i)
P(mismatch)  = 1 − P(match)
```

The frequencies and the three mismatch rates are theorems about
the *model* (`CyclicCount.v`: `cyclic_mismatch_11_17`,
`miller_150_of_158`, `blum_mismatch_is_half`,
`cyclic_mismatch_33_is_21_32`). Realization that `(ℤ/pℤ)*`
attains those counts is the named hypothesis `cyclic_units`
plus CAS exhaustion. Cyclicity of `(ℤ/pℤ)*` is not proved.

Checked exhaustively:

| Pair | `(s,r)` | Units | Mismatch | Formula |
|---|---|---|---|---|
| `11 × 17` | `(1,4)` | 160 | 150 | `15/16` |
| `11 × 19` | `(1,1)` Blum | 180 | 90 | `1/2` |
| `41 × 73` | `(3,3)` matched | 2880 | 1890 | `21/32` |

`±1` are always matches (`ord=1` and `ord=2`). The 150/158 figure
from `cas/04` is the 150 mismatches among the 158 units in
`{2,…,N−2}`: the same 150, excluding `±1`.

Blum / Williams `(1,1)` is the *minimum* mismatch among equal
valuations: `1/2`. Matching at depth 3 already drops to `21/32`.
Matching at depth `s` gives `P(mismatch) = 1 − (2^{-2s} + Σ_{i=1}^{s} 2^{2i−2−2s})`
which tends to `2/3` from below as `s → ∞` — never as high as
an unbalanced pair such as `(1,4)` at `15/16`.

### 11.5 A KeyGen obligation that was not in the catalog

Type A–E leaks give a *public* handle on `λ` or on a CRT
component. Matching deep 2-valuations does not. It *thins* the
set of Miller bases: more of the unit group has the same
2-height on both sides, so more bases are Miller liars. That is
a generation choice that shapes `λ`’s 2-part so that a public
map (the Miller square-chain, or Rabin squaring) is less likely
to land in a CRT disagreement.

Rulers:

```
kg_blum_2adic p q          :=  v₂(p−1) = v₂(q−1) = 1     (RW)
kg_2adic_unbalanced p q    :=  v₂(p−1) ≠ v₂(q−1)         (Miller-friendly)
kg_2adic_matched_deep d    :=  v₂(p−1) = v₂(q−1) ≥ d     (Miller-hostile)
```

Williams *chooses* Blum `(1,1)` on purpose: cheap roots, a
tight Factoring reduction, and a 2-torsion that is exactly four
elements. Ordinary RSA KeyGen does not mention `(s, r)` at all.
A generator that samples both primes `≡ 1 (mod 2^d)` for large
`d` is making the opposite choice, and `satisfies_keygen` does
not refuse it.

This is the first catalog row that is not a short or one-sided
annihilator. It is a *shape* of `λ`. The novel-weakness bet of
§6.11 item 2 (a Type-B module that is not a cyclotomic period
of `p`) now has a concrete neighbour: a generation choice that
does not produce a new annihilator, but that *starves* the
annihilator you already have (`ed−1`) of disagreeing 2-heights.

### 11.6 Honest scope

Machine-checked: `v₂(lcm) = max` and `v₂` is a valuation;
`v₂(λ) = max`; the mod-8 table; 2-height existence from
`a^{t 2^s} ≡ 1` and from Fermat; same-`t` under the named
hypothesis `cyclic_units`; Miller-from-`d` as height mismatch
on `odd_part(M)`; the cyclic-model counts including 150/158;
forced `p ≡ q ≡ 1 (mod 2^d)` is `both_deep`.

CAS-pinned: four roots on 187; exhaustive mismatch counts
against the formula; independent / nextprime / forced /
safe-prime frequencies (`cas/21`).

Not proved: cyclicity of `(ℤ/pℤ)*`; `height_stable_under`
without that hypothesis; a general density theorem for Miller
bases beyond the cyclic *model*.

## 12. Is matched-deep a live generation defect?

`kg_2adic_matched_deep` is a *shape* of `λ`, not an annihilator.
`cas/21_matched_deep.gp` measures three honest-looking samplers
against it.

- Independent 24-bit primes sit on the heuristic
  `P(v₂ ≥ d) ≈ 2^{1−d}`: both-deep-3 about 1/16, matched-deep-3
  about 1/48. Not a live defect.
- `nextprime` twins do **not** inflate deep matching. Consecutive
  odd integers have opposite residues mod 4, so one is often
  Blum. The opposite of a defect.
- Sampling both primes from the progression `1 (mod 2^d)`
  *is* the defect: every pair is `both_deep d`
  (`dist_forced_2adic_both_deep`). `nextprime` of a random
  start **leaves** that progression — the walk has to stay in
  it. Safe primes are the opposite choice: `v₂ = 1` always.

Ordinary RSA KeyGen (independent primes, nextprime-adjacent,
safe/strong) does not commit this. A generator that wants
NTT-friendly `p−1`, or that takes both primes `≡ 1 (mod 2^d)`
for some other reason, does. `satisfies_keygen` still does not
refuse it.

## 13. Type B is a presentation, adaptive root is a relation

Adaptive root and strong RSA are the same winning condition
(`adaptive_root_is_strong_RSA`). On `(ℤ/Nℤ)*` the condition is
trivial given `λ` (`lambda_solves_strong_RSA`,
`adaptive_root_trivial_from_lambda`). Type B is how a *period*
(`p−1`, `p+1`, `Φ_n(p)`) becomes a public `M`.

Williams `p+1` is Type B at `n = 2`, evaluated with a Lucas
`V` sequence so the arithmetic stays in `ℤ/Nℤ`. `Lucas.v`
proves the addition formula `V_{m+n} = V_m V_n − Q^n V_{m−n}`
and doubling as a corollary. CAS: when `P²−4` is a QNR
mod `p`, `V_{p+1} ≡ 2 (mod p)` and `V_{p−1} ≢ 2` — the period
is `+1`, not `−1`. A safe prime (`p = 23 = 2·11+1`) refuses a
smooth `p−1` and still has `p+1 = 24` 3-smooth.

A class group of an imaginary quadratic order is given by a
discriminant, not by `N = pq`. There is no
`discriminant_to_lambda`. Type B and adaptive root therefore
stop being aliases: same relation, different presentation.
Not an axiom that class groups are hard. Formal:
`ClassGroupWall.v`. CAS: `cas/22_lucas.gp`. The second
incarnation is written out in §14–16.

## 14. Presentations

A **presentation** (`Presentation.v`) is a carrier, a
multiplication, an identity, an exponentiation, a named
constructible-torsion predicate, and an optional *public*
annihilator.

| | `(ℤ/Nℤ)*` public | `(ℤ/Nℤ)*` trapdoor | `Cl(Δ)` |
|---|---|---|---|
| Carrier | units of `ℤ/Nℤ` | same | primitive forms of `Δ` |
| Constructible torsion | `{±1}` | `{±1}` | ambiguous forms (`Cl[2]`) |
| Public annihilator | `None` | `Some λ` | `Some 2` |

RSA's public view has no annihilator. The trapdoor view
carries `λ`, and `λ+1` is an adaptive-root witness
(`rsa_lambda_solves_adaptive_root`). `Cl(Δ)` carries `2`:
every ambiguous form is SL2-equivalent to its inverse
(`ambiguous_equiv_inv`). There is no odd public period.
`cl_has_no_lambda_plus_one`: the public option is not `D+1`.

The named problems — `Root e y`, `AdaptiveRoot y`, `Order a`,
`LowOrder B`, `LowOrderOutside B` — are the same winning
conditions on either carrier.

## 15. Constructible torsion, and which arrows die

Unrestricted `Problem_LowOrder` for `B = 2` is a *public
construction* on `Cl(Δ)`. From a divisor of `Δ` one writes
down an ambiguous form (`amb_from_div`). On the catalog
`Δ ∈ {−87, −403, −455}` those forms are reduced (or reduce
to a form with `a = c`), have `a > 1`, and are therefore not
principal (`reduced_a_gt_1_not_principal`). They win
`Problem_LowOrder_Cl` (`catalog_wins_LowOrder_B2`).

Prime discriminants (`−23`, `−47`) have 2-rank 0: the only
order-dividing-2 class is the identity. The 2-rank on a
fundamental `Δ ≡ 1 (mod 4)` is `t−1` with `t = ω(|Δ|)`.
CAS `23_class_group.gp`.

The restricted problem `Problem_LowOrderOutside H` excludes
the constructible set. On RSA, `H = {±1}`. On `Cl`,
`H = Cl[2]`. A Pietrzak forgery that lands in `Cl[2]` is
then *not* a break of the restricted assumption
(`pietrzak_restricted_ignores_Cl2`).

Arrows that die when the presentation is a discriminant:

- `lambda_solves_strong_RSA` — no `discriminant_to_lambda`.
- One-sided low-order / CRT splitting — there is no pair of
  rings whose idempotents are factors of a public `N`
  (`no_crt_split_from_disc`: `Δ < 0` is not a modulus).
- Adaptive root from public data — `Cl` publishes `2`, not
  an odd `e`.

`D+1` annihilates `Cl(−403)` in CAS, but only because
`h(−403) = 2` and `D+1` is even: it is the public
2-annihilator, not a `λ+1` analogue. Odd `D` does not
annihilate any catalog class group. `|D| = 87` does not
annihilate an order-6 class of `Cl(−87)`.

## 16. Proof of exponentiation, and the incarnation table

Wesolowski, algebra only (`ExpProof.v`, `cas/24_exp_proof.gp`):
a correct `π = x^q` for `y = x^{q·ℓ+r}` is an `ℓ`-th root of
`x^{q·ℓ}` (`wesolowski_correct_is_root`). On `(ℤ/Nℤ)*` with
known `λ`, the same `y` has the trivial adaptive-root witness
`(y, λ+1)`.

Pietrzak at `T = 2`: a midpoint `μ` with `μ² = x⁴` is a square
root of `y`. The quotient by the true midpoint squares to 1.
On `(ℤ/Nℤ)*` that element is `±1` or a mixed CRT root (the
Rabin split). On `Cl(Δ)` it may be constructible 2-torsion,
which unrestricted `LowOrder` already counts as a win and
the restricted problem excludes.

An accumulator (`Accumulator.v`) is the map `A ↦ A^x`. A
membership witness is a root. A forged witness for a random
base is adaptive root. Instantiated on `rsa_presentation`;
stated on `cl_presentation`, which has no trapdoor to update
with `λ`. Hash-to-prime is a named skip.

`Print Assumptions` on the headline theorems of this wave
(`compose_id_left`, `compose_inv_of_disc`, `compose_inv_equiv_id`,
`ambiguous_equiv_inv`,
`reduced_a_gt_1_not_principal`, `form_a_one_equiv_id`,
`catalog_wins_LowOrder_B2`, `unrestricted_LowOrder_won_by_Cl2`,
`restricted_LowOrder_excludes_Cl2`, `wesolowski_correct_is_root`,
`pietrzak_restricted_ignores_Cl2`, `membership_witness_is_root`,
`forged_mem_is_adaptive_root`, `cl_has_no_lambda_plus_one`,
`rsa_lambda_solves_adaptive_root`) is **Closed under the global
context**. Remaining named hypotheses, not used by those
theorems: cyclicity of `(ℤ/pℤ)*` (counts only), QNR evaluation
of Lucas `V_{p+1}` (CAS-pinned), and
`compose_preserves_disc` for the two-form Dirichlet branch
when neither leading coefficient is a unit. Identity
composition is a theorem (`compose_id_left`). Inverse
composition lands back on `Δ` (`compose_inv_of_disc`) and is
equivalent to the identity (`compose_inv_equiv_id`) — no extra
hypothesis.

### 16.1 Incarnations × winning conditions

| Sentence | `(ℤ/Nℤ)*` | `Cl(Δ)` |
|---|---|---|
| Units have an order, which divides every annihilator | `order_divides_lambda` | constructible torsion has order ∣ 2 |
| Low-order for `B = 2` is a public construction | no (needs factors, except `−1`) | yes — ambiguous forms from `factor(Δ)` |
| Adaptive root is trivial from public data | yes (`λ+1`), if `λ` is public | no (`Some 2`, not an odd `e`) |
| A Wesolowski proof is an `ℓ`-th root | `wesolowski_correct_is_root` | same relation, `Pexp` = composition |
| A Pietrzak forgery is low-order | may be `±1` | may be *constructible* 2-torsion |

The last row is the edge that was not dry: Pietrzak stated on
`Cl(Δ)` without excluding `Cl[2]` is a break of unrestricted
`Problem_LowOrder` using only the discriminant. The restricted
problem is the one the protocol actually needs.

## 17. The consumer on both carriers

Wesolowski verification is now a presentation predicate
(`wesolowski_verify`). A correct `π` is `P_Root`
(`wesolowski_pi_is_ell_th_root`). A verifying `π` for a value
`z` is adaptive root (`verifying_pi_is_adaptive_root`). On
`Cl(−87)`, CAS `26` runs the protocol on the order-3 class
`(4,3,6)`: `x^3` is the identity and `π^ℓ · x^r` reduces to
`y`.

The Pietrzak quotient is an object: `μ · w` when `mid · w ≡ 1`.
If `μ² ≡ mid²` then `(μ w)² ≡ 1`
(`pietrzak_quotient_squares_to_one_rsa`). On `Cl` the quotient
may be an ambiguous form; `P_LowOrderOutside` still excludes it.

The accumulator is an instance: RSA forges from `λ+1`
(`rsa_acc_forge_from_lambda`). `Cl` publishes `Some 2`, which
cannot be an odd trapdoor (`cl_no_trapdoor_from_two`).

`N = pqr` has eight sign patterns for `x² = 1`, not four
(`MultiPrime.three_prime_sqrt1_is_pm1_each`). `TwoSylow` is
two-prime; the arity is recorded, not rewritten.

Self-composition of a construction-side ambiguous form is the
identity on classes (`compose_self_ambiguous_equiv_id`,
`bqf_exp_2_ambiguous_div`).

## 18. The Williams torus

Public data: `N = pq` and a Lucas parameter `P`. When `P²−4` is
a QNR mod `p` and mod `q`, the hidden order is
`lcm(p+1, q+1)` (`torus_order`). That is not `λ(N)`: on
`11×19` the torus order is 60 and `λ` is 90.

`(p+1)(q+1) = N + (p+q) + 1`. So `N+1` misses `p+q` and does
not annihilate (`lucas_eval_annihilator_is_not_N_plus_one`;
CAS: `V_{N+1} ≢ 2 (mod N)`). If Fermat leaks `p+q`, the torus
period is public (`fermat_leak_is_torus_period`) — Type A on
this presentation, already in the catalog.

Type B at `n = 2` is native: `williams_eval` (`V_{p+1} ≡ 2`)
lifts to every multiple (`williams_eval_on_multiples`).
One-sided `V_M ≡ 2 (mod p)` and not `(mod q)` means `p` divides
`V_M−2` and `N` does not (`williams_onesided_gcd`,
`williams_onesided_not_full_N`). The CRT-split arrow exists
here and not on `Cl`.

`lucas_eval_presentation` has `Pannihilator = None`. The group
law on `V`-values is not pretended: multiplication is on
exponents / `(V,U)` pairs (`lucas_pt`, `lp_inv`).

## 19. Incarnation table, three columns

| Sentence | `(ℤ/Nℤ)*` | `Cl(Δ)` | Williams torus |
|---|---|---|---|
| Group law on the generators we use | `powm` | id, inv, self-compose of ambiguous | Lucas addition; `V_{k(p+1)}` |
| Wesolowski `π` is an `ℓ`-th root on the presentation | `wesolowski_pi_is_ell_th_root` | CAS `26` on `(4,3,6)` | `Pexp` is multiply-exponent |
| Pietrzak quotient has order ∣ 2 | `pietrzak_quotient_squares_to_one_rsa` | may be `Cl[2]` | constructible set is `V_n ≡ 2` |
| Type B is LowOrder on a named presentation | `p−1` on units | no | `p+1` on the torus |
| A public integer like `N+1` annihilates | `λ+1` if `λ` is known | no | **no** — misses `p+q` |

`Print Assumptions` on the new headlines
(`compose_self_ambiguous_equiv_id`, `williams_eval_on_multiples`,
`unit_inverse_exists`, `rsa_trapdoor_inv_is_root`,
`verifying_pi_is_adaptive_root`,
`pietrzak_quotient_squares_to_one_rsa`,
`three_prime_sqrt1_is_pm1_each`,
`lucas_eval_annihilator_is_not_N_plus_one`,
`williams_onesided_gcd`, `fermat_leak_is_torus_period`)
should be closed or list only the named QNR hyp inside
`williams_eval`. Remaining named: Dirichlet associativity of two
non-unit non-inverse forms; Gauss `(2/p)`; cyclicity of
`(ℤ/pℤ)*`.

## 20. A constructor, not a filter

`satisfies_keygen` says whether a pair is allowed. `KeyGenCtor.v`
emits primes that are already allowed. A slot is a residue
`a (mod 4 r s u v w)` with

- `a ≡ 1 (mod r)`, `a ≡ −1 (mod s)`, `a ≡ 3 (mod 4)`
- `a² + a + 1 ≡ 0 (mod u)` so `u | Φ₃(a)`
- `a² + 1 ≡ 0 (mod v)` so `v | Φ₄(a)`
- `a² − a + 1 ≡ 0 (mod w)` so `w | Φ₆(a)`

Then `p = a + k·M` with `M = 4 r s u v w`. By construction
`r | p−1`, `s | p+1`, `p` is Blum, and the same auxiliaries
divide `Φ₃(p)`, `Φ₄(p)`, `Φ₆(p)`. If each auxiliary exceeds
`B` and `p` is prime, `p` is `cyc_strong` at `B`. The walk
is in `k`. Smoothness is not tested after drawing a random
prime.

A raw `CtorPair` is only the CRT walk. A `PlacedCtorPair`
adds balanced / far / bit-length, and `B <` each auxiliary,
as record fields — not a post-hoc filter on a random draw.
The CRT walk does not force placement: two hits in the same
slot can be far and unbalanced. `CtorKey` adds `(e, d)` with
coprimality and `d ≡ e⁻¹ (mod λ)`. `ctor_to_rsa` is an
`RSAInstance`. `ctor_key_satisfies` discharges
`satisfies_keygen_full` (the original filter, plus tiny-`e`
/ tiny-`d_p` / `kg_cyc_strong` including `Φ₄`).

Two discriminators:

- Secret auxiliaries: `r | p−1`, `s | p+1`, and the three
  cyclotomic tests. Needs `p` or `(r,s,u,v,w)`.
- Public `M`: `p ≡ a (mod M)` is `roca_form`. That is a
  Type-A handle. Anyone who knows the slot can enumerate `k`.

Bits against public-AP enumeration, not NFS: if `2^κ ≤ M` then
a `b`-bit interval holds at most `2^{b−κ}+1` candidates
(`public_ap_search_bits`). A 1024-bit `N` is two ≥512-bit
primes (`regime_1024`). Catalog attacks contribute 0 bits of
handle. The remaining generic cost is factoring `N`, minus this
AP discount when `M` is public. If `M` is per-key secret, that
discount is not free. NFS is not proved.

There is no running sampler. Existence of a residue is CRT;
existence of a prime in the progression is not proved here.

CAS `28`: slot `(r,s,u,v,w) = (3,5,7,13,19)`, `M = 103740`,
`a = 13099`. `k = 0,2` give 13099 and 220579, both Blum and
strong at `B = 2` on `p±1` and `Φ₃,Φ₄,Φ₆`. Same-slot pair
is not balanced. Cross-slot `21611` (auxiliaries `5,3,7,13,19`)
is balanced with 13099 and far at gap 13.

## 21. Two encodings, one primality test

Hash-to-prime is not one object. There are two maps. Neither is
a cryptographic hash. Sequentiality and the random oracle stay
named.

**Map A, the slot encoding** (`HashSlot.v`). A seed is an
integer. `slot_encode S seed = ctor_prime S seed`. Every output
is in the constructor AP. Generation accept is `Z.prime`. If
the output is prime and the auxiliaries exceed `B`, it is
`cyc_strong` and Blum (`slot_encode_rulers`). If an encoding
output fails the rulers, it is composite (`slot_reject_is_composite`).
A prime *off* the AP can fail a ruler without being composite:
primality is the accept test, not a membership test. CAS `29`.

If the encoding is public, the image is `roca_form`
(`public_slot_encode_is_roca`). Membership is Type A. There is
no public `slot_encode` free of that handle
(`public_encode_admits_ap_test`). AP-search bits are still
`b − κ` (`public_slot_encode_ap_budget`). NFS is not proved.

Placement is not the encoding. Seeds `0` and `2` on the CAS 28
slot are prime and not `kg_balanced` (`slot_encode_does_not_place`).
A pair encoding still needs `PlacedCtorPair` fields.
Try-and-increment is a spec (`slot_try`): sound if a prime is
returned; complete relative to a window; existence of a prime
in the window is not proved. Dirichlet on APs stays named.
CAS `30`.

**Map B, the challenge / member encoding** (`ChallengePrime.v`).
`ch_encode seed = 2·seed+1` is odd. Accept is primality. There
is no `p±1` / `Φn` / Blum obligation. The image is not the
constructor residue (`ch_encode_not_slot_residue`). CAS `31`.

Wesolowski / Pietrzak verification uses `0 < ℓ`, not
`Z.prime ℓ` (`wesolowski_root_does_not_need_prime_ell`). An
honest `π` still verifies at composite `ℓ`. Soundness against
a cooked composite challenge is ROM / extraction and stays
named.

A membership witness for a composite `x = ab` is a membership
witness for each factor (`rsa_composite_member_splits_witness`).
That is why the *member* map wants primes. It is not the keygen
map. Instantiated on `rsa_presentation`. No hash appears.

CAS `29`–`31`. Headline theorems close under the global context.

## 22. Secure derivation

A seed is CSPRNG output. Unpredictability of the seed is a named
hypothesis, not a theorem. The derivation turns the seed into a
candidate already in a bit range *and* in the constructor class.
Gordon (1985) is this shape. ROCA is Gordon with a public shared
`M`. `HashSlot` (`k = seed`) is the walk, not the derivation.

`S_b` is the finite set `{ n : 2^{b−1} ≤ n < 2^b, n ≡ a (mod M) }`.
It is in bijection with the index interval `[k_min, k_max]`
(`k_in_slice_of_S_b`). `|S_b| = k_max − k_min + 1` when nonempty.
`M ≥ 2^{b−1}` can empty the slice (`empty_slice_example`).

`index_of_seed` on a domain of size `|S_b|` is a bijection onto
that interval (`index_of_seed_in_interval`,
`index_of_seed_surjective`). That is unbiased: uniform seed, uniform
candidate on `S_b`. The usual shortcuts are biased:
`seed mod L` when `L` does not divide the domain (`mod_hits_differ`);
force-residue after sampling `b` bits can leave the range
(`force_residue_leaves_range_example`).

Try-and-increment on the AP is not that bijection. It returns the
*first* prime at or after `k0` (`increment_hits_first`). Resample
can return any prime in the slice (`resample_includes_every_slice_prime`).
Dirichlet and existence of a prime in `S_b` stay named.

CAS `32`–`34`.

## 23. Public class, seeded class, the key

Two outputs of a public map into one AP differ by a multiple of
`M` (`public_map_difference_divides`). The gcd of differences is
a multiple of `M`. There is no public deterministic derivation
whose image lies in one AP and whose class is hidden
(`no_public_hidden_class`). Reuse of `(a, M)` across keys is
publication (`dist_reused_slot_leaks_M`). Per-key auxiliaries
are required for unpredictability of the *set*.

Auxiliaries themselves may be sample-then-test: they are `B`-bit,
not `b`-bit. `aux_split_ready` (`u ≡ 1 (mod 3)`, `v ≡ 1 (mod 4)`,
`w ≡ 1 (mod 6)`) is the named splitting shape. Existence of a
cyclotomic CRT residue in general needs Gauss and stays named;
CAS 28 is a witness that a residue exists for `(3,5,7,13,19)`.
Domain separation is a tag (`domain_tag`), not a PRF.

Placement is an interval on the second index, or empty. Far
`2^{gap} > p/2` can empty it (`far_can_empty_placement`). Same-slot
`13099` and `220579` are not balanced. Cross-slot `21611` is.
`derive_key_success` is the relation: both prime, `k_p` in `S_b`,
`k_q` in the placement interval, `e = 65537`, `d ≡ e⁻¹ (mod λ)`,
balanced, far, bits. Success is an `RSAInstance` meeting the
numeric spec (CAS `38` on the toy pair).

Catalog rows (`Derive.v`): `dist_public_slot` is `roca_form`;
`dist_reused_slot` leaks `M`; `dist_increment_slot` is first-prime,
not unbiased; `dist_force_residue` can leave the range;
`dist_seeded_slot` is `derive_key_success`.

Entropy. A long seed (domain size `|S_b|`) is the bijection
regime (`long_seed_hits_every_index`). A short seed plus stretch
is a named PRF skip; image-in-class remains a theorem. A 256-bit
seed is not uniform on a 352-bit index space. `regime_1024`:
catalog handle bits 0; public `M` of `κ` bits leaves `512−κ` AP
bits; seeded non-reused `M` does not give that discount; NFS is
not proved.

Pocklington needs a factored part of `p−1` larger than `√p`.
`r ≤ 2^{160}` is not enough for a 512-bit prime
(`aux_at_B_not_pocklington_size`). Accept stays `Z.prime`.
Williams adds `a ≡ 3 (mod 8)` on `p` (`rw_p_is_blum`).

CAS `32`–`38`.

