# When a design overlaps a known break

Lookup for checking another paper against this corpus. A row
fires if the paper's *group*, *challenge space*, *member map*,
or *hardness slogan* matches the trigger. The Rocq column is
the theorem that makes the overlap a fact, not a comment.
Rows without a theorem are still a refuse: do not treat the
paper's claim as discharged here.

Companion to `notes/hardness.md` (relations) and `THEORY.md`
§9 (what a hardness claim is) and §16–17 (PoE / accumulator).

## How to use

1. Name the carrier (`(ℤ/Nℤ)*`, `QR_N`, `ℤ_N^*/{±1}`, `Cl(Δ)`,
   signed QR, torus).
2. Name the winning condition (RSA, Strong RSA, adaptive root,
   low-order, PoE, accumulator membership / non-membership).
3. Name the challenge space `C` and whether `λ` / `|G|` is public.
4. Name the family / `GGen` and its constructible set `H`
   (ordinary `Cl` → ambiguous forms; Mersenne `Cl` → those plus
   the Shanks form; units → `{±1}`; torus → `{V_n ≡ 2}`).
5. Walk the table. A hit is a documented weakness, not an
   open question.

Adaptive root the *game* is `Problem_AdaptiveRoot_C` /
`P_AdaptiveRoot_C`. Strong RSA is the *search* (`e` chosen by
the attacker). `λ+1` wins the search and wins the game only if
`C (λ+1)`. On `Cl`, `2 ∈ C` lets A1 publish `g²` and return `g`
(`cl_AR_C_broken_when_two_in_C`).

## Overlap table

| # | If the paper / design does this | It overlaps | Rocq | Consequence |
|---|---|---|---|---|
| 1 | Accumulator members are composite, or “same bit length” is offered as soundness | Benaloh–de Mare informal soundness | `rsa_composite_member_splits_witness`; `bdm_coprime_gives_product_witness`; `bdm_same_bits_still_splits`; `shamir_trick` | A witness for `x=x₁x₂` is a witness for each factor. Two coprime members give a witness for `x₁y₁`, which can have the same bit length. Prime (or large-prime-factor) members are load-bearing. |
| 2 | Wesolowski / SimPoE on raw `(ℤ/Nℤ)*` with an odd challenge | `−1` soundness break | `wesolowski_soundness_fails_on_units_odd_challenge` | `π ↦ −π` turns a true `y` into an accepting transcript for the false `−y`. Prime challenges `> 2` and Odds-challenges are both odd. Prefer `QR_N` (start from a known square) or the quotient by `{±1}`. |
| 3 | Adaptive root / Wesolowski challenge space `C` is polynomial-size, or every `c ∈ C` is `B`-smooth with only polynomially many primes `≤ B` | 2024/505 Remark 9 / BBF24 | `adaptive_root_known_product_breaks`; `adaptive_root_smooth_power_breaks` | A1 publishes `h^{c·rest}`; A2 returns `h^{rest}`. Prime-challenge AR is not this. Odds-AR is only plausible if a random odd integer is not smooth. |
| 4 | Pietrzak / low-order on `Cl(Δ)` without excluding `Cl[2]` | Unrestricted `LowOrder` is a public construction | `catalog_wins_LowOrder_B2`; `unrestricted_LowOrder_won_by_Cl2`; `pietrzak_restricted_ignores_Cl2`; `pietrzak_quotient_squares_to_one_rsa` | An ambiguous form from `factor(Δ)` has order dividing 2. The protocol needs `LowOrderOutside H` with `H = Cl[2]`. A `Cl[2]` Pietrzak quotient is not a restricted break. |
| 5 | Low-order “in every imaginary-quadratic class group”, or “excluding `Cl[2]` is enough” | Belabas–Kleinjung–Sanso–Wesolowski 2020/1310 | `mersenne31_wins_restricted_LowOrder`; `mersenne31_wins_P_LowOrderOutside` | On the Mersenne discriminant `Δ = 1−2^5 = −31`, the Shanks form `(2,1,4)` has order 3 and is not ambiguous. That wins restricted low-order (`LowOrderOutside Cl[2]`) at `B = 3`. The general 2020/1310 / Mollin / cubic-field construction stays named. CAS `40`. |
| 6 | Treats BP97 Strong RSA (prime `e`, ordinary primes) as the modern game (any `e>1`, safe primes), or says one is “clearly” harder | Incomparable assumptions | *named* | Prime `e` hardens the relation; ordinary primes soften the group (`p−1` may be smooth). 2024/505 Remark 1 is not a theorem. |
| 7 | Strong RSA or adaptive root on a group whose order (or `λ`) is public | The relation is inhabited | `lambda_solves_strong_RSA`; `adaptive_root_is_strong_RSA`; `rsa_acc_forge_from_lambda`; `strong_RSA_trivial_at_one` | `(y, λ+1)` wins on every unit. Adaptive root *is* Strong RSA as a winning condition. The name is only a different *assumption* when there is no public odd annihilator. Also inhabited at `y=1`. |
| 8 | “RSA ≡ factoring” in the standard model, or cites Aggarwal–Maurer / generic ring as discharging that | Model mismatch | *named*; `THEORY.md` §9.6 | AM09 is generic-ring. Boneh–Venkatesan: a straight-line reduction from factoring to low-`e` RSA is unlikely. Coron–May / Miller-from-`(e,d)` is *not* the converse. This repo will not treat Factoring ≤ RSA as a design target. |
| 9 | LLX-style non-membership, and `μ = ∏_{s∈S} s (mod φ(N))` (or `λ`) is given to the adversary | Peng–Bao 2010 | *named, not formalized* | The LLX non-membership algebra uses that product. 2024/505 is out of scope of the attack only if `μ` is never published. |

## Triggers that look like #7 or #4 but are not

| Looks like | But | Why |
|---|---|---|
| Pietrzak on signed QR of a safeprime modulus | #4 | That group has odd order `p'q'`; the only element of order dividing 2 is `1`. Pietrzak's statistical-soundness claim is for *that* group. |
| Adaptive root with `C = PRIMES(2λ)` | #3 | The product-of-`C` attack is not efficient. Still an assumption, not a theorem. |
| Wesolowski on `QR_N` starting from a known square | #2 | The `−1` transcript leaves the subgroup. Membership testing in `QR_N` is not free (equivalent to factoring) unless the protocol never leaves the squares. |
| Low-order on a *random* class in `Cl(Δ)` | #4 | Def. of a hidden-order sampler usually gives a random `g`; a random class is rarely 2-torsion when `h(Δ)` is large. Unrestricted *search* for some low-order element is what `Cl[2]` wins. |

## What a paper-check should write down

For each overlap that fires:

- the trigger (quote the paper's group / `C` / member map / slogan);
- the row number;
- the Rocq name, or `named` if the row is a refuse without a theorem;
- whether the paper already excludes the bad case (then the row does *not* fire).

Do not record “Strong RSA is hard” as a theorem of this corpus.
Do not record AM09 as standard-model RSA ≡ factoring.
Do not record a `Cl[2]` element as a break of `LowOrderOutside Cl[2]`.
