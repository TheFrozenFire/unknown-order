# Hardness claims — catalog

Companion to `THEORY.md` §9. Winning conditions live in `UnknownOrder.v`
and `Hardness.v`. None of these rows is an axiom. A claim is a sentence
about a `KG`, an algorithm class, a winning condition, and a challenge
distribution; omit one and the sentence has no truth value this project
will use.

## Named search relations

| Problem | Input | Output | Relation | Rocq |
|---|---|---|---|---|
| Factoring | `N` | `f` | `1 < f < N`, `f \| N` | `Problem_Factor` |
| RSA | `(N,e,y)` | `x` | `x^e ≡ y (mod N)` | `Problem_RSA` |
| Strong RSA | `(N,y)` | `(x,e)` | `e > 1`, `x^e ≡ y` | `Problem_StrongRSA` |
| Adaptive root | `(N,y)` | `(x,e)` | same as strong RSA | `Problem_AdaptiveRoot` |
| Order | `(N,a)` | `k` | `k = ord(a)` in `(ℤ/Nℤ)*` | `is_order` / `Problem_Order` |
| Low-order (in `G`) | `(N,B)` | `(a,k)` | `ord_G(a) = k ≤ B` | `Problem_LowOrder` |
| One-sided low-order | `(N,B)` | `(a,k)` | `a^k ≡ 1 (mod p)`, not `(mod q)` | `one_sided_low_order` |

Adaptive root *is* strong RSA as a relation. The name changes with the
group (class group: no `λ` to discard).

## Relation arrows that are theorems

| From | To | Theorem | Not a claim of |
|---|---|---|---|
| `{p,q}` / `λ` / `d` | RSA roots on units | `trapdoor_inverts_RSA` | Factoring ≤ RSA |
| RSA solution at `e` | strong RSA at that `e` | `rsa_solution_is_strong_RSA` | a strong-RSA solver inverts RSA |
| `λ` | strong RSA on every unit | `lambda_solves_strong_RSA` `(y, λ+1)` | anything in a class group |
| `y = 1` | RSA / sRSA inhabited | `rsa_trivial_at_one`, `strong_RSA_trivial_at_one` | hardness (it refutes *existence*-hardness) |
| `ord(a) = k` | `k \| λ` | `order_divides_lambda` | lcm of enough orders *is* `λ` |
| one-sided `a^k ≡ 1 (mod p)` | `Problem_Factor` | `one_sided_low_order_factors` | two-sided `Problem_LowOrder` splits `N` |
| every unit | an `e`-th power | `rsa_units_are_eth_powers` | a decision problem on units |

CAS pin: `cas/18_hardness.gp`.

## Decision neighbours (not RSA, not formalized)

| Assumption | Why it is not search-RSA |
|---|---|
| QR | `e = 2` divides `λ`; squaring is not a permutation |
| Φ-hiding | `e \| φ(N)` is *forbidden* in a standard instance |
| DCR | `(ℤ/N²ℤ)*`, not `(ℤ/Nℤ)*` |

Decisional RSA on units with `gcd(e, λ) = 1` is vacuous: the `e`-power
map is a permutation, so `(N,e,x^e)` and `(N,e,y)` are identical.

## Open / refused as slogans

- Factoring ≤ RSA (oracle inversion ⇒ factors). Boneh–Venkatesan:
  a straight-line reduction for small `e` is unlikely.
- Coron–May / Miller-from-`(e,d)` is *not* that converse.
- GNFS cost; “leak-free `KG` ⇒ this bit length is enough.”
- Global axioms `RSA_hard`, `Factoring_hard`.

## Leaks are refutations of a claim about that `KG`

See `notes/keygen-weaknesses.md`. A hardness claim that does not name
`KG` is already false on every row of that table. Type E (Hastad) can
refute RSA on a restricted challenge distribution without factoring.
