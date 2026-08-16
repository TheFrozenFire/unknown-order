# Seed conversation — RSA key generation and decryption explained

Source: https://grok.com/share/bGVnYWN5LWNvcHk_50720cb1-f620-400a-b3c9-ee69981b5b0d  
Fetched via `GET https://grok.com/rest/app-chat/share_links/{shareLinkId}`  
`conversationId`: `ca367af3-85a5-429d-9ad3-e4041788747a`

This is the prior grok.com conversation used to seed the first analysis pass. It is **not** a theorem. Claims below are restated in `THEORY.md` and will be machine-checked (or corrected) in `rocq/RSA.v`.

## What the conversation settled

1. **`d` is not “a cube root.”** For public `e` (e.g. 3), exponentiation by `d` *is* the `e`-th-root map on `(ℤ/Nℤ)*`. `d ≡ e⁻¹ (mod λ(N))` (or `φ(N)`).
2. **Possession of `(N, e, d)` is computationally equivalent to factoring `N = pq`.** The integer `M = ed − 1` is a multiple of `λ(N)` and annihilates the unit group.
3. **Four algorithm families** extract a factor from that annihilator; they differ only in the auxiliary parameter that distinguishes the two CRT components of `ℤ/Nℤ`.
4. **Miller-from-`d` is Miller–Rabin run the other way.** Same successive-squaring engine; primality asks whether `n−1` misbehaves, factoring asks whether a known annihilator produces a non-trivial square root of 1.
5. **Pratt certificates are the dual.** Pratt certifies “the group is cyclic of known order”; Miller-from-`λ` exhibits “the 2-torsion is larger than a field’s.”
6. **RSA is the defining example** of a problem in a group of unknown order: `G = (ℤ/Nℤ)*`, order `φ(N)` / exponent `λ(N)` hidden, RSA problem = compute `e`-th roots in `G`.

## Algorithm parameters (to formalize)

| Family | Determinism | Succeeding parameter |
|--------|-------------|----------------------|
| Multiplier enumeration | deterministic | cofactor `k` with `1 ≤ k < e` such that `(ed−1)/k = φ(N)` (or `λ(N)`), then the quadratic `x² − (N−φ+1)x + N = 0` |
| Miller successive-squaring | randomized | base `a` whose orders mod `p` and mod `q` have mismatched 2-adic valuations (≥ 1/2 of units) |
| Sequential-base Miller | deterministic (poly-time under ERH) | first small prime base that splits |
| Coron–May / May lattice | deterministic | lattice dimension + bound `X` so Coppersmith recovers the small root (`k` or `p+q`) |

Common core: `M = ed−1` annihilates `(ℤ/Nℤ)*`; a witness that `ℤ/Nℤ` is not a field is a non-trivial factor.

## Honest caveats inherited from the seed (must survive formalization)

- `φ(N)` vs `λ(N)`: the conversation uses both; every theorem must say which inverse `d` is, and which multiple `M` is.
- Multiplier enumeration is `O(e · polylog N)` — practical for small `e`, not a claim about arbitrary `e`.
- Sequential Miller is deterministic always; polynomial runtime is ERH-conditional.
- Lattice methods: conversation claims poly-time when `ed ≤ N²` (balanced RSA) and `O(log² N)` when `ed ≤ N^{3/2}`. Formalize the exact bound, do not inherit the slogan.
- Success probability “at least 1/2” is a counting statement over `(ℤ/Nℤ)*`, not a cryptographic-advantage game (until we put it in `ProvableSecurity.v`).
