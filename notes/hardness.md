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
| committed `f,h` at `τ` | `g^{f(τ)h(τ)} = C_f^{h(τ)} = C_{f·h}` | `pot_poly_conv_raise`, `poly_eval_conv` | a hiding pairing (this check recovers bounded coeffs) |
| public product of encodings | `∏ P_{i+j}^{a_i b_j} = C_{a·b}` from slots vs CRS | `public_quad_complete`, `quad_combine_is_product` | a hiding map; NIZK |
| succinct product fold | posted proof `13 log2 n + 2` words | `succ_proof_len_is_log`, `succ_pin_n2_accepts` | ROM / PPT SNARK |
| monomials `X^i, X^j` | `g^{τ^i · τ^j} = P_{i+j}` | `monomial_eval_product`, `monomial_conv_is_later_slot` | `P_i · P_j` (that is the sum) |
| self-bilinear `e` with `e(g,g)=g` | `e(C_f, C_h) = C_{f·h}` | `self_bil_committed_product` | existence of `e` |
| QAP identity at `τ` | `C_{A·B} = C_C · C_{H·Z}` | `qap_complete_at_tau`, `qap_witness_complete`, `public_quad_qap` | a hiding check of the same identity |
| remainder encoding `= 1` | `τ` is a root, or `ord(g)` divides the remainder | `qap_point_sound`, `qap_sound_at_tau` | the identity as polynomials |
| Schnorr on base `P_i` | `ord(P_i) \| (z−z′) − a_i(c−c′)` | `coeff_slot_extracts` | ROM / forking (`Refuse_NIZK_Fiat_Shamir`) |
| Fiat–Shamir of eqdl: `c = fs_challenge(stmt, t)` | NI transcript verifies iff Sigma does at that `c` | `fs_eqdl_complete`, `fs_pin_challenge_depends_on_commit` | collision-resistance / ROM |
| `w0·w1=w2` | QAP identity at every `x` | `mul_gate_sat` | a circuit compiler |
| same `w`, public `r` | `C_A · C_B^r = C_{A+rB}` | `same_w_check` | extractable `w` on both families |
| Schnorr on `U_j = g^{A_j(τ)}` | `ord(U_j) \| (z−z′) − w_j(c−c′)` | `wire_slot_extracts` | a hash / NIZK |
| `w0+w1=w2` | QAP identity; `g^{w0+w1}=g^{w0}g^{w1}` | `add_gate_sat`, `add_is_public_sum` | a circuit compiler |
| `w∈{0,1}` | `w·w=w` as a mul gate | `bit_sat` | range beyond a bit |
| `z = x·y + t` | both gate QAPs at every `u` | `prod_add_sat` | a general compiler |
| bits `b0,b1` | `g^{b0+2b1} = g^{b0}(g^{b1})²` | `range2_encoding` | larger ranges (same shape) |
| bit `s` | `mux s a b` is `a` or `b` | `mux_select` | a hidden product for `s·a` |
| `w0=w1` | add-with-zero QAP | `wire_eq_sat` | |
| Jacobi of `g^k` | depends on `k` only mod 2 | `jacobi_sees_only_parity` | a pairing check of the `τ`-string |
| self-bilinear `e` | `e(P_i,P_1)=e(P_{i+1},P_0)`; evaluates if `e(g,g)=g` | `self_bil_checks_pot`, `self_bil_evaluates_pot` | existence of `e` |
| power endo `x ↦ x^k` as next CRS power | `ord \| τ^i (k − τ)` | `power_endo_next_forces_k` | a pairing of two hidden dlogs |
| GII search (unit with no inverse) | empty on `(ℤ/Nℤ)*` | `rsa_gii_search_empty` | computational GII; inversion is Bézout |
| aux self-bilinear with `e(aux,g,g)=g` | publishes `P_{i+1}` | `aux_eval_publishes_next` | existence; iO deferred |
| DARK `C = g^{f(s)}`, `π = g^{q(s)}` | `C = π^{s−z} · g^{f(z)}` | `dark_deg1_open`, `dark_deg2_open` | a pairing/PoE check without `s` |
| Jacobi of `g^a` and `g^b` | product is Jacobi of `g^{a+b}` | `jacobi_additive_pairing` | a large-target pairing |
| GGM product eq-test `2^{10}−1` | Factor | `ggm_eq_leak_factors` | query-complexity lower bound |
| JNT affine root `(x+c)^{1/e}` | integer cube of `x+c` | `jnt_roots_affine` | SNFS cost; general `GRoot` |
| prep advice `N/17` | Factor before looking at `y` | `prep_then_gra_factors` | RSA easier than factoring |
| SAGM product of handles | sum of exponents | `sagm_product_adds_exponents` | standard-model hardness |
| one queried RSA root + extra unqueried | `Problem_OneMore` | `one_more_pin` | PPT one-more game |
| prime public `e` | `Problem_GHR` | `ghr_pin`; `ghr_prime_e_shamir_gcd` | a new scheme |
| `e \| λ` | φ-hiding relation | `phi_hiding_pin_e5` | PPT φ-hiding game |
| GQ at public `e` | `Problem_RSA` at that `e` | `cpp17_extract_is_fixed_e` | NIZK / HVZK; chosen-`e` sRSA |
| GRA eq-test lift `gcd` proper | Factor | `gra_eq_leak_factors` | every GRA factors `N` |
| `P^e − X` at 2, `e ≥ 2` | not the zero polynomial over `Z` | `Pe_minus_X_eval_2_nonzero` | vanishing as a function on `(Z/NZ)*` |
| no-div GRA identity `X^3 − X` | linear coeff `−1`, `N` cannot divide all coeffs | `gra_nodiv_identical_root_impossible_X3` | a solver for one `y` (const 42) |
| `GInv` of a non-unit | Factor | `gra_inv_nonunit_factors` | `rsa_inverter` (not a GRA) |
| `e > 1` | `e·deg P ≠ 1 + e·deg Q` | `rational_Pe_minus_XQe_leading` | randomized GRAs; huge binary `e` |
| `GConst (λ+1)` | Strong RSA on every unit, no factor | `gra_const_lambda_plus_one_solves_sRSA_without_factoring` | AMS KeyGen-density |
| 1-query integer-cube `GRoot` | drop the gate, still a factor | `bv_few_query_low_e_drops_oracle` | RSA ≢ factoring |
| SLP `X^d` on units | functional cube-root map | `slp_carmichael_is_functional` | polynomial identity in `F_p[X]` |
| Jacobi on residues | two values; not a constant polynomial | `jacobi_two_values` | GRA-hard ⇒ standard-hard |
| multiply-only ops | no `GAdd`; RSA solution is sRSA | `gadd_is_not_a_ggm_op`, `generic_group_does_not_separate_rsa_from_srsa` | query-complexity lower bound |
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

## Strong-RSA witness peel (standard model)

A witness `(x,e)` of unit `y` on `N=pq` is classified; only the last leaf is open.

| Leaf | Identity | Rocq | Residual? |
|---|---|---|---|
| non-unit `x` | `gcd(x,N)` proper | `srsa_nonunit_x_pin` | no |
| Jacobi `(y/N)=−1` | `e` odd | `srsa_jacobi_minus1_forces_odd_e` | no |
| even `e` | `x^{e/2}` is a square root | `srsa_even_e_is_square_root` | no |
| associate `±r` | gcd is `N`, no split | `srsa_associate_neg6_does_not_split` | no |
| mixed square root | `rabin_oracle_nonassociate_factors` | `srsa_mixed_root_of_36_factors` | no |
| `x=y` | `y^{e−1}≡1` | `srsa_x_eq_y_annihilates` | no |
| `λ \| e−1` | Miller `gcd(g−1,N)` | `srsa_lambda_type_miller_factors` | no |
| safeprime `λ=2p'q'` | same Miller on `N=77` | `srsa_safeprime_miller_factors` | no |
| odd `e`, `gcd(e,λ)=1`, `λ` ndiv `e−1` | named `srsa_residual_leaf` | `srsa_residual_pin` (42³≡36) | **yes — Jacobian sentence** |

Self-randomization preserves a *fixed* `e` (`srsa_fixed_e_rerand`) and does not preserve polynomial `e=X` (`srsa_poly_e_not_rerand_invariant`). Related `y,y²` is `x1^{2 e1}=x2^{e2}` (`srsa_related_y_square`). A SAGM handle still peels (`srsa_sagm_lambda_type_peel`).

Do not record Strong RSA ≡ factoring as a theorem. The residual leaf *is* standard-model RSA with a `y`-dependent exponent coprime to `λ`.

### Cuts of the solver (taxonomy)

Rocq IDs are semantic (`residual_*`, `period_*`, `xmap_*`, …). The map
by *question* is [`notes/srsa-cuts.md`](srsa-cuts.md):

1. Peel a witness you already have.
2. What leftover `(x,e)` is allowed to be (`⟨y⟩`, `C₈×C₅`, 16 generators).
3. Gcd-Pohlig **splits**; equality-only order-finding **inverts**.
4. Public maps of `x`. 5. Public maps of `e`.
6. Extra tapes and related `y`. 7. Engines that ignore `y`.
8. Different group or modulus. 9. GRA / GGM / SAGM / SLP.

CAS probe classes 1–500 are a crosswalk in `notes/hundred.md` …
`hundred5.md`, not theorem IDs. Joined first-hundred CAS: `134`.
Residual cube is still not `Problem_Factor`.

## Open / refused as slogans

- Standard-model Factoring ≤ RSA (an `rsa_inverter` constructs a
  factor). The inverter recovers `m`
  (`rsa_inverter_recovers_message`); the converse stays unused
  (`rsa_inverter_constructs_factor_named`). In the generic *ring*,
  a GRA that identically computes low-`e` roots leaks a factor or
  is forbidden by degree (`gra_eq_leak_factors`,
  `gra_inv_nonunit_factors`, `gra_nodiv_identical_root_impossible_X3`).
  That is not the standard-model slogan
  (`Refuse_RSA_eq_factoring_standard_model`,
  `Refuse_AM09_generic_ring_as_standard_model`).
- Boneh–Venkatesan: a few-query low-`e` algebraic reduction that
  outputs a factor can drop `GRoot` (`bv_few_query_low_e_drops_oracle`).
  Not a theorem that RSA is easier than factoring.
- Brown: an SLP that *is* a low-`e` solver is a different object
  (`slp_carmichael_is_functional`, identity forbidden by coeff `−1`).
- Jacobi is standard-easy and not a constant GRA polynomial
  (`jacobi_two_values`) — GRA-hard does not imply standard-hard.
- Coron–May / Miller-from-`(e,d)` is *not* Factoring ≤ RSA.
- GNFS cost; “leak-free `KG` ⇒ this bit length is enough.”
- Global axioms `RSA_hard`, `Factoring_hard`.
- BP97 Strong RSA (prime `e`, ordinary primes) is not the modern
  game (any `e>1`, safe primes); they are incomparable (row 6).
- UO-GGM query lower bounds (`Refuse_UO_GGM`). The stolen DK
  remark is the op signature (`gadd_is_not_a_ggm_op`) plus
  `generic_group_does_not_separate_rsa_from_srsa`.

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
