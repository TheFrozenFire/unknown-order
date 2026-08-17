# unknown-order

Computational problems in **groups of unknown order**: the group law is public, the
order is not. RSA, strong RSA, adaptive root, order, and low-order are the same
winning conditions on different carriers. This repo writes those conditions once,
instantiates them, and records which arrows exist.

Every claim that matters is checked twice. Rocq (Coq 9.1) proves it for the model.
PARI/GP pins it on numbers. Agreement is evidence because the tools fail differently:
a wrong premise still proves cleanly in Rocq; a wrong model still computes in CAS.

The mathematics is in [`THEORY.md`](THEORY.md). The schedule and named skips are in
[`ROADMAP.md`](ROADMAP.md). Working rules are in [`CLAUDE.md`](CLAUDE.md).

## Three presentations

| | `(ℤ/Nℤ)*` | `Cl(Δ)` | Williams torus |
|---|---|---|---|
| Public data | `N = pq` | discriminant `Δ < 0` | `N` and a Lucas parameter `P` |
| Hidden order | `λ = lcm(p−1, q−1)` | class number (not computed) | `lcm(p+1, q+1)` |
| Constructible torsion | `{±1}` | ambiguous forms (`Cl[2]`) | `V_n ≡ 2` written without factors |
| Public annihilator | `None` (trapdoor: `Some λ`) | `Some 2` | `None` — not `N+1` |
| Type B (a period becomes public `M`) | `p−1` on units | no | `p+1` on the torus |
| CRT-split | yes (one-sided order) | no | yes (one-sided `V_M ≡ 2`) |
| `N+1` / `λ+1` annihilates | `λ+1` does, if `λ` is known | no | **no** — order is `N+(p+q)+1` |

RSA is the worked example, not the only object. Rabin–Williams is the same unit
group at a forbidden exponent `e = 2`.

A Pietrzak forgery is low-order. On `Cl(Δ)` that element may be an ambiguous
form built from `factor(Δ)`, so unrestricted `LowOrder` at `B = 2` is a public
construction. The restricted problem (`LowOrderOutside H`, `H = Cl[2]`) is the
one a protocol needs.

Reusable algebra (`powm`, Carmichael, CRT, `√1` splitting, `v₂`) lives in the
sibling [`rocq-proofs`](https://github.com/TheFrozenFire/rocq-proofs). Clone it
beside this repo. Methodology comes from
[`formal-verification`](https://github.com/TheFrozenFire/formal-verification)
and the last pure-theory run in
[`ciphering`](https://github.com/TheFrozenFire/ciphering). There is no EVM
track: there is no bytecode.

## What is proved

Headline theorems close under the global context unless a skip is named.
Skips that stay named: cyclicity of `(ℤ/pℤ)*` (used only for counts), Gauss
`(2/p)` and the QNR direction of Euler, LLL / Coppersmith, Pratt completeness,
Dirichlet associativity of two non-unit non-inverse forms, hash-to-prime,
sequentiality.

### RSA and the annihilator

`d ≡ e⁻¹ (mod λ)`. `M = ed − 1` annihilates the units. Multiplier enumeration
recovers `{p, q}` from `φ` or `p+q`. Miller successive-squaring turns a height
mismatch into a factor (`MillerHeight`: heights are `v₂(ord)`). Miller–Rabin is
the same engine on a different exponent.

`rocq/RSA.v`, `FactorEnum.v`, `Miller.v`, `Order.v`, `TwoSylow.v`. CAS `01`–`07`, `25`.

### Key generation is a leaked annihilator

Each catalog row is a generation choice that makes a *partial* or *short*
period public (Type A–E in `THEORY.md` §6). Fermat, shared primes, Pollard
`p−1`, Wiener, small `e`, CRT-RSA `d_p`, unbalanced primes, cyclotomic
`Φ_n(p)`, batch order, and close-prime geometries have refusal lemmas in
`KeyGen`. Matched-deep `v₂` is a shape of `λ`, not an annihilator; the live
defect is sampling both primes `≡ 1 (mod 2^d)`, not ordinary `nextprime`.

`notes/keygen-weaknesses.md`. CAS `08`–`17`, `21`. LLL-shaped rows (Boneh–Durfee,
ROCA, Coron–May) are interfaces only.

### The same group, a different map

`e = 2` is not an RSA exponent. Squaring is 4-to-1. Four `√1` via CRT; mixed
roots split `N`. Williams primes give a unique QR among `{±a, ±2a}`. Three
primes give eight roots of 1, not four (`MultiPrime`).

`QuadResidue.v`, `RabinWilliams.v`, `TwoPrimary.v`. CAS `19`–`20`.

### Second incarnation: `Cl(Δ)`

Primitive forms, Gauss reduction, identity, inverse. `id ∘ f = f`. `f ∘ f⁻¹`
lands back on `Δ` and is principal. Construction-side ambiguous forms
(`b = 0` or `a = ±b`) satisfy `[f]² = 1` and win unrestricted low-order at
`B = 2` when they are not principal.

`BinForms.v`, `ClassGroupWall.v`, `Presentation.v`. CAS `23`.

### Consumer: proof of exponentiation, then an accumulator

A correct Wesolowski `π` is an `ℓ`-th root. A Pietrzak midpoint that is not
the true one yields an element of order dividing 2. Membership in an
accumulator is a root; a forged witness for a random base is adaptive root.
Run on `(ℤ/Nℤ)*` (Wesolowski is trivial given `λ`; Pietrzak hits `{±1}` or a
mixed CRT root) and on toy `Cl(Δ)` (Pietrzak must not count `Cl[2]` as a
restricted break). CAS `24`, `26`.

`ExpProof.v`, `Accumulator.v`. Sequentiality and hash-to-prime stay named.

### Third incarnation: the Williams torus

Lucas `V` addition is a theorem. `V_{p+1} ≡ 2 (mod p)` is a named QNR
hypothesis; multiples of the period are a theorem. One-sided `V_M ≡ 2`
splits `N`. `N+1` does not annihilate. If Fermat leaks `p+q`, the torus
order is public — Type A, already in the catalog.

`Lucas.v`, `Torus.v`. CAS `22`, `27`.

## Hardness is a relation, not an axiom

`Hardness.v` records arrows: trapdoor inverts RSA; an RSA solution is strong
RSA at that `e`; `λ+1` solves adaptive root on units; order divides `λ`;
one-sided low-order factors. There is no global `RSA_hard`. A hardness
*claim* needs a named KeyGen distribution (`THEORY.md` §9). Factoring ≤ RSA
and PPT / advantage are out of scope.

## Run it

```sh
git clone https://github.com/TheFrozenFire/rocq-proofs   # sibling of this repo
bash run-check.sh   # CAS (gp) + Rocq (rocq compile); each SKIPs if its tool is absent
```

Needs PARI/GP (`gp`) and Rocq 9.1. The Rocq track builds `../rocq-proofs` first.
CAS is 27 witnesses, `cas/01`–`27`.

## What is left

[`ROADMAP.md`](ROADMAP.md) §5 is done. The remaining cryptanalysis hunt is
`THEORY.md` §6.11: a *named* modern sampler that leaks a Type A–E handle not
already in the catalog. Not another incarnation, and not an undirected
KeyGen pass.
