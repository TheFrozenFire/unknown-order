# Hardness claims — catalog

Companion to `Hardness.v` / `Refuse_PPT_advantage`. Winning conditions live in `UnknownOrder.v`
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
| Adaptive root (search) | `(N,y)` | `(x,e)` | same as strong RSA | `Problem_AdaptiveRoot` |
| Adaptive root (game) | `(N,y)` then `c ∈ C` | `x` | `C c` and `x^c ≡ y` | `Problem_AdaptiveRoot_C` |
| Annihilator (order assump.) | `(N,g)` | `e ≠ 0` | `g^e ≡ 1` | `Problem_Annihilator` |
| Fractional root | `(N,y)` | `(x,a,b)` | `a>0`, `x^a ≡ y^b` | `Problem_FractionalRoot` |
| Order | `(N,a)` | `k` | `k = ord(a)` in `(ℤ/Nℤ)*` | `is_order` / `Problem_Order` |
| Low-order (in `G`) | `(N,B)` | `(a,k)` | `ord_G(a) = k ≤ B` | `Problem_LowOrder` |
| One-sided low-order | `(N,B)` | `(a,k)` | `a^k ≡ 1 (mod p)`, not `(mod q)` | `one_sided_low_order` |

Adaptive root *as a search* is strong RSA (`e` chosen by the
attacker). The *game* is `Problem_AdaptiveRoot_C`: `y` first, then
`c ∈ C`. `λ+1` wins the search and wins the game only if `C (λ+1)`.
Constructible torsion `H` is a family parameter
(`cl_presentation_H`, `UOFamily`).

## Relation arrows that are theorems

| From | To | Theorem | Not a claim of |
|---|---|---|---|
| `{p,q}` / `λ` / `d` | RSA roots on units | `trapdoor_inverts_RSA` | Factoring ≤ RSA |
| RSA solution at `e` | strong RSA at that `e` | `rsa_solution_is_strong_RSA` | a strong-RSA solver inverts RSA |
| `λ` | strong RSA on every unit | `lambda_solves_strong_RSA` `(y, λ+1)` | anything in a class group |
| Strong RSA witness at `e` | AR game at that `e` | `strong_RSA_is_ar_C_iff` | the game unless `C e` |
| `λ+1` on `11×17` | prime-challenge AR | `search_lambda_plus_one_misses_prime_AR` | `81` is not prime |
| `2 ∈ C` on ordinary `Cl(−31)` | AR game | `cl_AR_C_broken_when_two_in_C` | A1 publishes `g²` |
| annihilator `M` of `y` | Strong RSA / AR search | `annihilator_plus_one_is_strong_RSA` `(y, M+1)` | class number on `Cl` |
| `h(−31)=3` | AR search on every written class | `class_number_solves_AR_neg31` | `D+1` is not `h` |
| RSA / sRSA | fractional root `b=1` | `rsa_is_fractional_root` | DARK `r`-powers |
| SRS `s₁ = g^{d*}`, `s₁^e ≡ g` | RSA / sRSA at **this** `g` | `srs_first_is_rsa`, `srs_first_is_strong_rsa` | a general sRSA solver; the root is already published |
| `λ*+1` on the same `g` | a **different** sRSA pair `(g, λ*+1)` | `lambda_plus_one_is_other_strong_rsa` | that pair is not `d*` |
| `d*` | RSA / sRSA on **every** unit | `dstar_inverts_every_unit` | extracting `d*` from the SRS |
| DL of `s₁` base `g` | `k ≡ d* (mod ord(g))` | `dlog_of_srs_agrees_mod_order` | DL ≡ sRSA |
| that DL when `ord(g)=λ*` | inverse of `e` mod `λ*` | `dlog_at_full_order_inverts_e` | PPT hardness |
| sampled `τ`; `P_i = g^{τ^i}` | `P_{i+1} = P_i^τ`; DL of `P_1` is `τ` | `pot_succ_is_tau_power`, `pot_first_is_dlog` | a pairing check |
| contribute `ρ` at slot `i` | `P_i^{ρ^i} = g^{(τρ)^i}` | `pot_contribute_multiplies_tau` | HVZK of the update |
| backward walker `e` on `g^{τ^i}` | `e ≡ τ⁻¹ (mod ord(g))` | `backward_walker_is_tau_inv` | that a public KeyGen `e` walks this string |
| two eq-DL transcripts | `ord \| (z−z′) − τ(c−c′)` | `eqdl_extracts_tau` | a simulator (`Refuse_HVZK_simulation`) |
| `i` same-`ρ` equal-DLs on base `P_i` | `P'_i = P_i^{ρ^i} = g^{(τρ)^i}` | `ladder_realizes_update`, `contribution_ladder_step` | a pairing check of the CRS |
| committed `f,h` at `τ` | `g^{f(τ)h(τ)} = C_f^{h(τ)} = C_{f·h}` | `pot_poly_conv_raise`, `poly_eval_conv` | a public check without the integer `h(τ)` |
| monomials `X^i, X^j` | `g^{τ^i · τ^j} = P_{i+j}` | `monomial_eval_product`, `monomial_conv_is_later_slot` | `P_i · P_j` (that is the sum) |
| self-bilinear `e` with `e(g,g)=g` | `e(C_f, C_h) = C_{f·h}` | `self_bil_committed_product` | existence of `e` |
| QAP identity at `τ` | `C_{A·B} = C_C · C_{H·Z}` | `qap_complete_at_tau`, `qap_witness_complete` | a public check without coefficients |
| remainder encoding `= 1` | `τ` is a root, or `ord(g)` divides the remainder | `qap_point_sound`, `qap_sound_at_tau` | the identity as polynomials |
| Schnorr on base `P_i` | `ord(P_i) \| (z−z′) − a_i(c−c′)` | `coeff_slot_extracts` | a hash / NIZK |
| `w0·w1=w2` | QAP identity at every `x` | `mul_gate_sat` | a circuit compiler |
| same `w`, public `r` | `C_A · C_B^r = C_{A+rB}` | `same_w_check` | extractable `w` on both families |
| Jacobi of `g^k` | depends on `k` only mod 2 | `jacobi_sees_only_parity` | a pairing check of the `τ`-string |
| self-bilinear `e` | `e(P_i,P_1)=e(P_{i+1},P_0)`; evaluates if `e(g,g)=g` | `self_bil_checks_pot`, `self_bil_evaluates_pot` | existence of `e` |
| power endo `x ↦ x^k` as next CRS power | `ord \| τ^i (k − τ)` | `power_endo_next_forces_k` | a pairing of two hidden dlogs |
| GII search (unit with no inverse) | empty on `(ℤ/Nℤ)*` | `rsa_gii_search_empty` | computational GII; inversion is Bézout |
| aux self-bilinear with `e(aux,g,g)=g` | publishes `P_{i+1}` | `aux_eval_publishes_next` | existence; iO deferred |
| DARK `C = g^{f(s)}`, `π = g^{q(s)}` | `C = π^{s−z} · g^{f(z)}` | `dark_deg1_open`, `dark_deg2_open` | a pairing/PoE check without `s` |
| Jacobi of `g^a` and `g^b` | product is Jacobi of `g^{a+b}` | `jacobi_additive_pairing` | a large-target pairing |
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
  An `rsa_inverter` recovers `m` (`rsa_inverter_recovers_message`)
  and does not construct a factor
  (`rsa_inverter_constructs_factor_named`). Rabin inversion of a
  planted square does (`rabin_oracle_nonassociate_factors`).
- Aggarwal–Maurer (generic ring) is not that converse in the
  standard model. Citing it as “RSA ≡ factoring” is a model mismatch
  (`notes/paper-overlaps.md` row 8).
- Coron–May / Miller-from-`(e,d)` is *not* that converse.
- GNFS cost; “leak-free `KG` ⇒ this bit length is enough.”
- Global axioms `RSA_hard`, `Factoring_hard`.
- BP97 Strong RSA (prime `e`, ordinary primes) is not the modern
  game (any `e>1`, safe primes); they are incomparable (row 6).

## Leaks are refutations of a claim about that `KG`

See `notes/keygen-weaknesses.md`. A hardness claim that does not name
`KG` is already false on every row of that table. Type E (Hastad) can
refute RSA on a restricted challenge distribution without factoring.
Predicate oracles that recover `m` (LSB, interval, padding) are
the same kind of restricted inversion; they are catalogued in
`notes/transcript-oracle-plan.md`, not as Factoring ≤ RSA.

## Design overlaps (paper-check)

A later paper that re-uses these problems can hit a *known* break
without naming a bad `KG`. The lookup is `notes/paper-overlaps.md`.

| Row | Trigger | Theorem / status |
|---|---|---|
| 1 | composite / same-bit-length accumulator members | `bdm_same_bits_still_splits` |
| 2 | Wesolowski on raw units, odd challenge | `wesolowski_soundness_fails_on_units_odd_challenge` |
| 3 | adaptive-root `C` poly-size or smooth | `adaptive_root_known_product_breaks` |
| 4 | Pietrzak / LowOrder on `Cl(Δ)` without excluding `Cl[2]` | `catalog_wins_LowOrder_B2` |
| 5 | low-order in every class group / “excluding `Cl[2]` is enough” | `mersenne31_wins_restricted_LowOrder` |
| 6 | BP97-sRSA ≡ modern sRSA | `Refuse_BP97_vs_modern_sRSA` |
| 7 | sRSA / AR given public `λ` | `lambda_solves_strong_RSA` |
| 8 | standard-model RSA ≡ factoring | `Refuse_RSA_eq_factoring_standard_model` |
| 9 | LLX non-membership with `∏S mod φ(N)` public | `llx_lambda_forges_nonmem`; `peng_bao_member_still_forges` |
