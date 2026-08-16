# Rabin–Williams — overlap with RSA

Companion to `THEORY.md` §10. Formal objects: `rocq/QuadResidue.v`,
`rocq/RabinWilliams.v`. CAS: `cas/19_rabin_williams.gp` (`N = 11·23`).

## Same, and not the same

| | RSA | Rabin–Williams |
|---|---|---|
| Group | `(ℤ/Nℤ)*`, `N = pq` | same |
| Hidden | `λ = lcm(p−1, q−1)` | same |
| Map | `x ↦ x^e`, `gcd(e, λ) = 1` | `x ↦ x²` (`e = 2` *forbidden* as RSA `e`) |
| Fibre | 1-to-1 on units | 4-to-1 on units |
| Decision problem on units | vacuous (permutation) | QR (a predicate) |
| Inversion vs Factoring | RSA ≤ Factoring; converse open | equivalent (random-self-reduction, 1/2) |
| Prime shape | no mod-8 condition | `p ≡ 3 (mod 8)`, `q ≡ 7 (mod 8)` (Blum + split) |
| `v₂(p−1)` | unconstrained (odd primes: ≥1) | exactly 1 |
| Type A–D leaks | apply | apply unchanged |
| Type E | degree `e` (3 or 65537) | degree 2 — *worse* for raw messages |

The textbook RSA pair `(11, 17)` is not a Williams pair: `17 ≡ 1 (mod 8)`
and `17 ≡ 1 (mod 4)`. RW KeyGen is not “RSA KeyGen with `e = 2`.”

## Why those congruences

```
p ≡ 3 (mod 8)  ⇒  p ≡ 3 (mod 4),  (−1/p) = −1,  (2/p) = −1
q ≡ 7 (mod 8)  ⇒  q ≡ 3 (mod 4),  (−1/q) = −1,  (2/q) = +1
```

`(−1/·)` is proved (Euler). `(2/·)` is the reason for mod 8 and is
CAS-pinned, not proved (Gauss). Among `{±a, ±2a}` the four Legendre
pairs are a permutation of `{±1}²`, so exactly one is a square mod
both primes (`williams_tweak_exists` / `_unique`).

`p ≡ 3 (mod 4)` also gives the root formula `a^{(p+1)/4}`
(`sqrt_mod4_3_correct`) and `v₂(p−1) = 1`. Safe primes fit: a
Sophie-Germain `r ≡ 1 (mod 4)` yields a Williams `p`; `r ≡ 3 (mod 4)`
yields a Williams `q`. The odd part of `p−1` still needs a large
prime factor (Pollard).

## Rabin reduction

`x² ≡ y²` and `x ≢ ±y (mod N)` ⇒ `gcd(x−y, N)` is a proper factor
(`rabin_roots_split`). An inversion oracle, fed a random square
`r²`, returns a non-associated root with probability 1/2 and so
factors. RSA has no analogous theorem for an inversion *oracle*
(Coron–May / Miller need the secret `d`, not roots of random `y`).

## Scheme (algebra only)

Sign: hash to a unit `H`; pick the unique QR tweak `t ∈ {±1, ±2}`;
root by `(p+1)/4` + CRT. Verify: `s² ∈ {±H, ±2H}` (`rw_verify`).
Principal-root convention, hash, and the signature game are not
formalized. Raw Rabin *encryption* is Type E at degree 2 and is
not what the signature scheme does.
