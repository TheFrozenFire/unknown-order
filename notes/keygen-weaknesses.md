# RSA key-generation weaknesses — catalog

Companion to `KeyGen.v` / `KeyGenCtor.v`. Each row is a *generation choice* that leaks a
handle on `λ(N)` or on one CRT component. Formal objects are in `rocq/`.
CAS pins the algebra on numbers. Types A–E are the algebraic classification
in this catalog: a novel weakness has to be one of these, or it is not
a weakness of this problem.

| # | Generation choice | Type | Why it leaks | Attack | Rocq | CAS |
|---|-------------------|------|--------------|--------|------|-----|
| 1 | `p ≈ q` (even if same bit length) | A | `N` is near a square; `p+q` is nearly public | Fermat | `FermatFactor` | `08` |
| 2 | Two moduli share a prime | D | `gcd` *is* the shared CRT component | batch GCD | `SharedPrime` | `09` |
| 3 | `p−1` is `B`-smooth | B | cheap public `M` with `p−1 \| M` (one-sided annihilator) | Pollard `p−1` | `PollardP1` | `10` |
| 4 | `q−1` is `B`-smooth | B | same, other component | Pollard `p−1` | `PollardP1` | `10` |
| 5 | `p+1` or `q+1` is `B`-smooth | B | Lucas analogue of Fermat | Williams `p+1` | `StrongPrimes` (def) | — |
| 6 | short `d` (`d < N^{1/4}`) | C | `k/d` is a convergent of `e/N` | Wiener | `Wiener` | `11` |
| 7 | somewhat short `d` (`d < N^{0.292}`) | C | same bilinear relation, Coppersmith | Boneh–Durfee | `Lattice` interface | — |
| 8 | tiny `e` plus stereotyped/related `m` | E | low-degree polynomial with a small root | Hastad / Franklin–Reiter | `SmallExponent` | `12` |
| 9 | `p ≪ q` | A | smallest prime factor is the whole secret | ECM / trial | `KeyGen.small_prime_le_sqrt` | `08` |
| 10 | leaked MSBs/LSBs of `p` or `d` | A/E | small unknown in a modular polynomial | Coppersmith | `BitLeak` (shape) | — |
| 11 | `p` in a thin AP (ROCA form) | A/E | same, with a public progression | ROCA | `BitLeak.roca_form` | — |
| 12 | small CRT exponents `d_p`, `d_q` | B+C | short one-sided annihilator | May / BDF | `CRTRSA.crt_dp_annihilates` | `10` |
| 13 | shared RNG / tiny prime pool | D | collision on `p` ⇒ row 2 | Debian RNG, etc. | `SharedPrime` | `09` |
| 14 | matched deep `v₂(p−1)=v₂(q−1)≥d` | shape of `λ` | thins Miller bases; not a public annihilator | — | `TwoPrimary.kg_2adic_matched_deep` | `20` |

**Not listed as keygen defects:** a correctly generated 2048-bit key with
`e = 65537`, safe-ish primes, and full-size `d`. That is the baseline the
rows above deviate from.

**Intent-spec for a generator** (see `KeyGen.v`): balanced, far-apart primes;
`p−1`, `q−1`, `p+1`, `q+1` each have a large prime factor; `d` large; `e`
not tiny unless messages are padded; independent entropy per prime;
CRT exponents not tiny.

**Why, in one paragraph.** The group law and Fermat's little theorem are
public. The only secret is the integer `p−1` (and `q−1`). Every classical
attack is a procedure for reading a handle on that integer — or on `p`
itself — out of the public pair `(N, e)`. Generation that refuses every
row above leaves only GNFS on `N`; extra bits of `N` spent as margin
against a listed leak are then wasted, and can be returned.

**Where a novel weakness has to sit** (`Refuse_undirected_611_hunt`): a new Type-A
geometry (a public `f(N,e)` close to `p`, `p+q`, or `p−q`); a new Type-B
module (a cheap recurrence whose period is a smooth function of `p` other
than `p±1`); a new Type-C relation (a low-degree identity with a short
unknown other than `(k,d)`); a new Type-D collision (shared algebraic
structure without a shared prime); or a new Type-E key-side small root
(a hidden polynomial the keygen implicitly satisfies).

A **directed** attempt to break that partition — named public
functions of `N`, chance model, collapse tests — is
[`sixth-type-plan.md`](sixth-type-plan.md). That plan is not an
undirected KeyGen pass.

**Avenues already closed this wave.**

| Avenue | What it added | Headline witness |
|---|---|---|
| Sampler | `KeyGenSampler` + `cas/13` | nextprime twins / shared prefix / increment window all fail `kg_far`; independent 16-bit mostly pass |
| Type B beyond `p±1` | `Cyclotomic` + `cas/14` | `p=653` is strong at `B=20` and `Φ_3` is 19-smooth |
| Type D, no shared prime | `BatchOrder` + `cas/15` | one `M` splits two coprime moduli; `r=101` is a shared AP |
| Type C past Wiener | `wiener_classical_sufficient` + `cas/16` | `36 d⁴ < N` is sufficient; `18 d³ < N` recovered only 5/9 |
| Type A geometries | `KeyGenGeom` + `cas/17` | shared-prefix Fermat steps 0 vs 2687 independent |
