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
completeness of Pratt certificates; any hardness of RSA / strong RSA / order.

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
