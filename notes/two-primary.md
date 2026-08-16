# 2-primary structure of `(ℤ/Nℤ)*`

Companion to `THEORY.md` §11. Formal: `rocq/TwoPrimary.v`. CAS:
`cas/20_two_primary.gp`.

RSA, Miller-from-`λ`, Pratt, Blum integers and Rabin–Williams are
the same algebra: the 2-Sylow, read off `(v₂(p−1), v₂(q−1))`.

## Valuations

| `p mod 8` | `v₂(p−1)` |
|---|---|
| 3 or 7 | 1 (Blum / Williams) |
| 5 | 2 |
| 1 | ≥ 3 |

Williams ⇒ `(1,1)`. `v₂(λ) = max(v₂(p−1), v₂(q−1))` (`val2_lcm_max`).

## Four square roots of 1

CRT of `±1` on each prime. Mixed ones (`(1,−1)`, `(−1,1)`) split `N`.
Blum makes the 2-torsion *exactly* these four (no order-4 element).

## Heights and Miller

2-height of `a` at `p`, relative to an odd `t`: least `k` with
`a^{t 2^k} ≡ 1 (mod p)`. Mismatched heights (same `t`) split `N`
(`height_mismatch_splits`). That is Miller’s success condition.

## Counts (cyclic model, CAS)

`P(v=0)=2^{-s}`, `P(v=i)=2^{i-1-s}`. Mismatch `= 1 − Σ P_p(i)P_q(i)`.

| Pair | `(s,r)` | Mismatch |
|---|---|---|
| `11×17` | `(1,4)` | `150/160 = 15/16` |
| `11×19` | `(1,1)` | `90/180 = 1/2` |
| `41×73` | `(3,3)` | `1890/2880 = 21/32` |

Blum is the *least* mismatch among equal valuations. Unbalanced
pairs (e.g. `(1,4)`) are Miller-friendly. Matching deep 2-valuations
is a KeyGen choice that `satisfies_keygen` does not refuse.

## Rulers

- `kg_blum_2adic` — Williams
- `kg_2adic_unbalanced` — Miller-friendly
- `kg_2adic_matched_deep d` — equal and ≥ `d` (Miller-hostile, not an annihilator)
- `kg_2adic_both_deep d` — both ≥ `d`; forced `1 (mod 2^d)` lands here

`cas/21`: independent / nextprime sit on the heuristic; the live
defect is sampling *both* primes from `1 (mod 2^d)`. Safe primes
are Blum.

## Miller-from-`d`

`miller_t` is an odd multiple of `odd_part(λ)`. Heights exist
from `a^M ≡ 1`. A mismatch splits `N` (`MillerHeight.v`).

## 150/158

Cyclic-model theorem (`CyclicCount.miller_150_of_158`): 150
mismatches among 160 units, ±1 always match so 158 in `{2,…,N−2}`.
Cyclicity is named (`cyclic_units`), not proved.
