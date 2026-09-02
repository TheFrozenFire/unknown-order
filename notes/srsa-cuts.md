# Strong RSA cuts — by question, not by batch

Rocq IDs are semantic: `residual_*`, `primary_*`, `dict_*`, `period_*`,
`xmap_*`, `emap_*`, `extra_*`, `engine_*`, `modulus_*`, plus already-
named `srsa_*` / `dozen_*` / `shape_*` / `filter_*` / `arith_*`. Files
are the same cuts. CAS numbered `01`–`138` stay as witnesses; probe
classes 1–500 are a crosswalk in `notes/hundred.md` … `hundred5.md`,
not theorem IDs.

Pin unless noted: `N=11·17=187`, `λ=80`, `(y,x,e)=(36,42,3)`,
`ord(y)=40`, `⟨y⟩≅C₈×C₅`. Residual means
`srsa_residual_leaf` — odd `e`, `gcd(e,λ)=1`, `λ∤ e−1`, units,
`x^e≡y`. None of these cuts inhabits that leaf as `Problem_Factor`.

A **fate** is one of: splits `N`; peels (already-named easy witness);
does not inhabit; leftover (inverts, does not factor); other sentence
(different group or modulus).

## 0. The open leaf

`srsa_residual_pin`: `42³≡36`. That is standard-model RSA with a
`y`-dependent exponent coprime to `λ`. The rest of this file is
restrictions on the TM that is allowed to write `(x,e)`, or
identities the leftover pair must satisfy.

Joined CAS of the *first* hundred fates: `cas/134_whole_identity.gp`
(`whole()`). Numbered CAS `01`–`138` stay.

## 1. Already have a witness — peel it

Restrict **the pair `(x,e)`**, not the algorithm that produced it.
`StrongRSAPeel.v`, CAS `127`.

| If | Then | Rocq |
|---|---|---|
| `gcd(x,N)` proper | splits | `srsa_nonunit_x_pin` |
| `(y/N)=−1` | `e` odd | `srsa_jacobi_minus1_forces_odd_e` |
| `e` even | `x` is a square root | `srsa_even_e_is_square_root` |
| associate `±r` | no split | `srsa_associate_neg6_does_not_split` |
| mixed `√` | splits | `srsa_mixed_root_of_36_factors` |
| `x=y` | `y^{e−1}≡1` | `srsa_x_eq_y_annihilates` |
| `λ \| e−1` | Miller splits | `srsa_lambda_type_miller_factors` |
| otherwise | residual leaf | `srsa_residual_pin` |

Four `√1`: `{1,−1,67,120}` (`srsa_four_sqrt1`). Mixed `67` and `120` split
(`srsa_sqrt1_120_splits`, `srsa_miller_66`). `−1` does not (`srsa_minus1_no_split`).

## 2. What leftover `(x,e)` is allowed to be

Output language of the residual pair on this pin. A solver that
writes outside this set is not residual.

**Subgroup.** `x ∈ ⟨y⟩` and **generates** it (`ord=40`). There are
`φ(40)=16` such elements. Residual `x` is not an order-16 2-Sylow
generator (`v₂(ord x)=3 < v₂(λ)=4`). Index `[units:⟨y⟩]=4`: three
cosets are forbidden. All 16 generators are Jacobi `+1`.

| Claim | IDs |
|---|---|
| `x^{40}≡1`, generates | `residual_x_in_cyc_y`, `residual_x_generates`, `residual_x_order_40_not_20`, `residual_x_order_40` |
| `x=y^{27}`, `gcd(27,40)=1` | `residual_x_is_y_to_27`, `residual_y_to_e_inv` |
| 16 generators | `residual_sixteen_generators`, `dict_phi40` |
| unique unit cube of `36` is `42` | `shape_unique_unit_cube_root_of_36`, `residual_unique_unit_cube` |
| unique unit cube of `1` is `{1}` among `{±1}`-adjacent | `residual_cube_root_of_1` |
| `e` invertible mod `16` and mod `5` | `residual_e_inv_mod_16`, `residual_e_inv_mod_5`, `residual_e_coprime_10_16`, `residual_five_ndiv_e` |
| CRT of `e^{-1}` is `27` | `residual_crt_e_inverse` |
| `5 \| e` shares `λ` | `residual_five_divides_lambda` |
| local CRT `42≡9 (mod 11)≡8 (mod 17)` | `residual_local_cube_mod_p`–`residual_crt_locals`, `residual_crt_is_residual_x`, `shape_crt_*` |
| Jacobi / QR both sides | `residual_local_squares`, `residual_qr_both_sides`, `residual_jacobi_x_vs_2`, `residual_x_local_qr` |
| not in `⟨2⟩`, not order 16 or 10 | `residual_not_in_ltwo`, `residual_x_not_in_lten`, `residual_x_not_ord16`, `residual_x_not_ord10` |
| generates the 5-Sylow | `primary_69_generates_C5`, `residual_x_generates_5_sylow` |

**Public tests of leftover `x`.** Jacobi `+1` is public; leftover `x=42`
satisfies it, but so does `10` (order 16, QNR both sides, not a cube
root): `filter_jacobi_x_plus`, `filter_jacobi_10_plus_not_leftover`.
`2` has Jacobi `−1` and is rejected (`filter_jacobi_2_minus`). Jacobi
`+1` leaves `80` units vs `16` generators (slack `5`):
`residual_jacobi_plus_count`. Checking `x^3≡y` is RSA uniqueness at
fixed `e=3` (`filter_x_cube_check_is_rsa_e3`). Coset reps `2`,`10` of
`⟨y⟩` do not split via `gcd(x−a,N)` (`residual_coset_*_no_split`).
CAS `143`.

**`⟨y⟩ ≅ C₈ × C₅`.** `y^5=100` generates `C₈`; `y^8=137` generates
`C₅`. Cubing is bijective on both. `y` reconstructs as `155·69`.
The order-2 of `C₈` is Miller `67`.

`SrsaPrimary.v` (`primary_*`).

**Dictionary.** Each generator is leftover `x` for **two** residual
`e` (`e` and `e+40`). `φ(80)/φ(40)=2`. Cubing is an automorphism of
`⟨y⟩` of order 4 in `(ℤ/40ℤ)*`, hence **four 4-cycles** on the 16
generators. Residual `x` sits on the cycle `70→42→36→93→70`.

`SrsaDict.v` (`dict_*`).

**SAGM on the challenge.** Residual cube is `(a,e)=(27,3)` on base
`y`: `ae−1=λ`. Knowing `ord(y)` substitutes for knowing `λ` *for
this inversion*. Trapdoor `d=27` inverts **every** unit; `k=27` on
a public base inverts only in that cyclic.

`dict_e_eq_d`, `dict_y_to_d`, `dict_sagm_on_y`, `dict_sagm_ae_minus_1`,
`dict_inv_mod_lam`, `dict_sagm_of_3`, `residual_y_to_27`,
`dict_cbrt_2_in_ltwo`, `dict_three_x_for_k27` — `SrsaDict.v`.

## 3. Two programs on one pin — gcd vs multiply

The same exponents, two TMs.

| TM | Identity | Fate |
|---|---|---|
| `gcd(y^k−1,N)` for `k ∈ {5,8,10}` | `period_y5_minus_1_splits`–`period_y10_minus_1_splits`, `period_gcd_path_splits`, `period_gcd_y5_splits`–`period_gcd_y8_splits` | **splits** |
| `y^k ≡ 1` equality, no gcd | `period_eq_order_40`–`period_eq_not_5`, `period_eq_y40`–`period_eq_y5` | finds `ord=40`, **no split** |
| then `x=y^{27}` | `period_exp_path_leftover`, `period_after_ord_invert`, `residual_y_to_27` | **leftover invert** |
| `gcd(y^{40}−1,N)` | `period_full_period_no_split`, `period_gcd_full_period` | `=N`, no proper factor |
| `gcd(x^k−1,N)` on leftover `x` | `period_x5_minus_1_splits`–`period_x16_minus_1_splits`, `period_same_oracle` | **same split** — leftover `x` is a Pohlig oracle |

On the default pin `gcd(p−1,q−1)=2`, so matching local orders exist
only at `{1,2}`. Any unit of order `>2` is a period leak (order 16
via `g^8−1`, order 4 via `g^2−1`, max-order via `g^5−1` and
`g^{16}−1`). Same mismatch on `N=77` (`period_77_leftover_pohlig`,
`period_77_two_pow3`). Extra pin `N=13·19=247` has
`gcd(p−1,q−1)=6`; leftover `x=179` of `y=69` at `e=5` has matching
local orders `6`, and `gcd(x^5−1,N)=1`, `gcd(x^8−1,N)=1`
(`period_247_*`). Residual leaf named, not `Problem_Factor`.
`SrsaPeriod.v` (`period_*`). CAS `140`.

**Named arrows on the same fork.** Invert from `ord(y)` always:
`order_inverts_in_cyclic` / `order_yields_residual_sRSA` (pin
`42³≡36`). Leftover or order factors `N` only under KeyGen mismatch:
the public quantity is `gcd(x^k−1,N)` (`leftover_mismatch_factors`;
pins `187` leftover `x=42` and `y=36` at `k=5`, `77` leftover `2`
at `k=3`). Matching orders on `247` are not one-sided at `k=5` and
the gcd is `1` or `N` (`matching_247_*`). Residual leaf is not
`Problem_Factor` without that mismatch hyp. Not RSA ≡ or ≢
factoring. `Hardness.v`, `SrsaOrderArrows.v`. CAS `145`.

**Public exponent lattice vs trapdoor period.** `N−1=186=2·3·31` and
`N+1=188=4·47` are public. Pohlig `k∈{5,8,10,16}` that split leftover
`x` do not divide `N−1` (`period_pohlig_ndiv_Nminus1`). No divisor of
`N−1` or `N+1` annihilates `y` or splits (`period_Nminus1_divisors_no_split`,
`period_y_Nminus1_no_annihilator`, `period_Nplus1_*`). Leftover `x^{N−1}≢1`,
so `N−1` does not certify `x∈⟨y⟩` (`period_x_Nminus1_no_membership`).
CAS `141`.

**Annihilator quality short of `λ`.** A scale of `M` on `gcd(y^M−1,N)`:
`M=2` and `M=4` no split; odd part `5` and `2`-powers `8`,`16` split;
`ord(y)=40` leftover-inverts with `gcd=N`; `λ=80` still Miller-splits
on `67` (`period_M2_no_split`, `period_M4_no_split`,
`period_advice_odd_part_splits`, `period_advice_v2_8_splits`,
`period_advice_v2_16_splits`, `period_advice_ord_invert_no_proper`,
`period_advice_lam_miller`). CAS `144`.

One `k=27` in three subgroups: cube roots of `2`, `3`, `36`.
`gcd(161−42,N)=17`, `gcd(75−42,N)=11`. IDs: `period_two_subgroups_split`, `period_cbrt2_cbrt36_split`–`period_cbrt3_cbrt2`.

Safeprime `N=77` is the same dichotomy with `{3,5}` instead of `{5,8}`:
`period_77_pminus1`–`period_77_ord2_is_lam`, `period_77_51_is_2_pow7`–`period_77_two_pow5`.

## 4. How the TM writes `x`

Public `X(N,y)`. Fate is inhabit / one-sided split / leftover by pin
accident.

**Does not invert** (and does not split): associate, midpoint, half,
`y±1` as `x`, Gray, popcount, Lucas, `⌊y/3⌋`, `⌊N/y⌋`, pad, Newton,
CF, `x=φ`, bitlength, `x=N−1`, `x=⌊√N⌋`, `x=2y` (`arith_double_y`).
IDs include `xmap_associate`, `xmap_midpoint`, `xmap_half_y`, `xmap_nextprime_as_x`, `xmap_floor_y_div_3`–`xmap_gray_code`,
`xmap_lucas_L8`–`xmap_eightbit_palindrome`, `xmap_y_inv_sq`–`xmap_x_bitlength_N`, `xmap_nextprime_mod_N`, `xmap_pkcs_pad`,
`filter_neg_y`, `arith_newton_*`, `arith_cf_*`.

**One-sided cube / non-unit `x` splits:** the map is not a global root,
but `gcd(x^3−y,N)` or `gcd(x,N)` is proper. IDs: `xmap_odd_monomial`, `xmap_bitrev_36_is_9`,
`xmap_fibonacci_y`, `xmap_exp_base2`, `xmap_inv_then_cube`, `xmap_cube_then_inv`, `xmap_y7_onesided`, `xmap_y11_onesided`, `xmap_three_y_onesided`,
`xmap_nibble_swap_nonunit`, `xmap_shift_left_2_onesided`, `residual_even_k_not_generator`, `period_y32_splits`, `xmap_y35_onesided`, `filter_onesided_*`,
`xmap_mismatched_crt_splits` (mismatched CRT).

**Leftover by a public formula that lands in `⟨y⟩`:** `x=y^N` (`N≡d
(mod 40)`), Catalan `C_5`, `p(10)`, integer `√y` then `n(n+1)`,
`x=y^{e^{-1} mod 40}`. IDs: `xmap_y_to_the_N`, `xmap_catalan_C5`, `xmap_partition_p10`, `residual_y_to_e_inv`,
`xmap_sqrt_then_n_nplus1`, `dict_binary_product`. Pin geometry, not a general solver.

**Monomial / inverse / affine as *algorithm class* (how `x` is
written, including leftover-shaped inverses):** `shape_monomial_*`,
`shape_inverse_*`, `shape_affine_*`, `xmap_odd_monomial_y5`, `xmap_y_to_the_y`, `xmap_y_to_Nminus1`,
`xmap_y_to_Nplus1`, `residual_y_inv_generator`, `xmap_inv_lam_minus_1`.

**Joint pair / gcd-free X machines** (not another `f(y)` formula).
Public addition chain for `e=3` (Hamming 2: `y^2·y≡93`) is not leftover
`x`; trapdoor `d=27` (Hamming 4) is (`shape_public_chain_e3`,
`shape_trapdoor_chain_d27`). Polynomial `X=1+Y^2` is `175`, not a cube
root and no one-sided split (`shape_poly_x_quadratic`). Short public
bases `{2,3}` with public exponents: `2·3≡6`, `6^3≢36`; `2^3≢42`; SAGM
`2^{27}≡161` is another instance (`shape_public_bases_2_3`). Gcd-free
multiply from `y` of length `≤3` stays at `y`, `y^2`, `y^3`, none leftover
(`shape_gcdfree_bounded_from_y`). Public `x^{N−1}` does not test
membership in `⟨y⟩` (`shape_public_exp_not_membership`). CAS `142`.

## 5. How the TM writes `e`

Public `E(N,y)`.

**Even `e` peels** (square-root case): `φ(y)`, Hamming, `λ(y)`,
bitlength, rad, `ω`, `Ω`, smooth `30`, `ψ(y)`, `ord(y)`, `φ(N)`,
`N±1`, primorial. IDs: `emap_phi_y_even`, `emap_hamming_even`, `emap_lambda_y_even`–`emap_Omega_even`,
`emap_smooth_even`, `emap_dedekind_psi_even`–`emap_phi_N_even`, `emap_e_N_plus_1_even`, `emap_e_N_minus_1_even`, `emap_primorial_even`.

**Shares `λ` (not residual):** `e=25`, `e=5`, `e=y−1=35`, aliquot
`55`, `e=N−2`. IDs: `emap_e25_shares_lambda`, `emap_odd_hamming_shares`, `emap_v2_yminus1`, `emap_e_eq_Nminus2`, `emap_e_y_minus_1_shares`,
`emap_aliquot_shares`, `emap_fermat_5_shares`, `arith_composite_e15`.

**Leftover-shaped odd `e` coprime to `λ`:** inverts in `⟨y⟩` for a
named `x`. IDs: `emap_tau_leftover_e9`–`emap_sigma_leftover`, `emap_mersenne_leftover`–`emap_fermatish_leftover`, `emap_e_two_y_plus_1`–`emap_prevprime_e31`,
`emap_e17_leftover`, `emap_e_lam_minus_1`–`emap_repunit_111`, `emap_collatz_e21`, `dict_e43_same_x_leaf`–`emap_e_eq_x`,
`emap_e_N_minus_lam`, `emap_prime_e7`, `dict_x93_e67`–`dict_x185_e53`, `filter_lowbit_e9`,
`arith_nextprime_e37`, `arith_e7_residual`.

**Public tests of `e` vs residual tests that mention `λ`.** Residual:
odd, `gcd(e,λ)=1`, `λ∤ e−1` (`filter_residual_tests_on_cube`; `e=5`
and `e=15` share `λ`; `e=7` is residual-shaped). Public tests see
`(N,y)` only:

| Public test | Fate | Rocq |
|---|---|---|
| `gcd(e,N−1)=1` | rejects the cube (`gcd(3,186)=3`); accepts non-residual `e=5` and residual `e=7` | `filter_cube_fails_public_e`, `filter_e5_passes_public_e`, `filter_e7_passes_public_e` |
| `gcd(e,N)=1` invertibility mod `N` | does not certify residual (`e=5`, `e=15` pass) | `filter_e_coprime_N_does_not_certify` |
| `gcd(e,φ(y))=1` | `(N,y)`-only; rejects the cube (`φ(36)=12`) | `filter_e_coprime_phi_y_rejects_cube` |

Wrong-Euler inverse mod `N−1`: `shape_wrong_euler_inv`. CAS `139`.

**`E(N,y)` algorithm classes** (not another named `f(y)`). Constant `e`
is RSA at that `e` (`poly_e_constant_is_fixed_e`). `e=X` is not
rerand-invariant (`poly_e_X_not_rerand`). Degree 2: `e=y²` even peels
(`poly_e_square_even_peel`); `e=y²+1=1297` is residual-shaped, leftover
`x=y^{33}≡104` only with a period oracle, and write-`e`-then-`x=y^e`
is `53≠104` (`poly_e_quadratic_*`). Rejection-sampling odd primes
against `gcd(e,N−1)=1` emits `e=5`, which shares `λ`
(`reject_sample_public_e_emits_5`). CAS `139`.

## 6. Extra tapes and related challenges

The TM may emit more than `(x,e)`, or see several `y`.

| Extra / query | Fate | IDs |
|---|---|---|
| `φ` or `p+q` | factors | `filter_phi_*`, `extra_fermat_difference`, `extra_p_plus_q` |
| `d` with `ed≡1 (mod λ)` | Miller | `shape_ed_*`, `extra_crt_dp`, `extra_dp`–`extra_edq_minus_1` |
| local `d_p`, `d_q` | one-sided annihilator | `extra_crt_dp`, `dozen_e11_minus1_shares_lambda` |
| `ord(g)=λ` | trapdoor | `extra_order_is_lambda` |
| factor `e−1` / `N−1` | Miller / public | `extra_factor_e_minus_1`, `extra_factor_N_minus_1` |
| two leftovers `gcd(x_i−x_j,N)` | `42,60` no split; `42,25` splits | `extra_batch_gcd_of_roots`, `extra_leftover_pair_splits`, `extra_gen_pair_42_9`–`extra_gen_pair_42_93` |
| Shamir coprime `e` | product, not a factor | `extra_shamir_two_leftovers`, `extra_twin_exponents`, `extra_shamir_3_7`, `dozen_related_*` |
| `y` and `y^{-1}` | inverse of root | `extra_inverse_challenge` |
| fixed-`e` rerand | leftover for a different `y` | `srsa_fixed_e_rerand`, `extra_rerand_fixed_e`, `shape_chaum_*` |
| CRT of local roots | needs `{p,q}` | `shape_crt_moduli_are_factors`, `residual_crt_is_residual_x` |
| two coprime moduli | no split | `extra_same_y_two_moduli`, `arith_two_moduli_*` |
| advice `N/17` | splits | `dozen_advice_div_splits`, `prep_then_gra_factors` |

## 7. Engines that do not look at `y`

Named factoring algorithms as “solvers.” They split this pin because
`N` is tiny or `p−1` is smooth, not because they inverted `y`.

Pollard `p−1` (`engine_pollard_p1`, `engine_pminus1_B8`), rho (`engine_rho_walk`, `engine_rho_x2_minus_1`), Fermat /
Hart (`engine_fermat_splits`, `engine_hart_square`–`engine_fermat_recovers`), trial (`engine_trial_division`, `engine_trial_13_then_11`),
Williams `p+1` (`engine_williams_pplus1`; `P=3` does not, `engine_williams_P3_no_split`), Fibonacci gcd
(`engine_F9_splits`, `engine_fibonacci_gcd_engine`), Mersenne `2^8−1` (`engine_mersenne_255`, `engine_mersenne_engine`),
index-as-prime `N−1` does not (`engine_index_calculus_Nminus1`). BSGS treating `N` as prime
is the wrong order (`engine_bsgs_wrong_order`, `engine_shor_period_of_2`, `engine_lam_ne_Nminus1`).

## 8. The sentence is a different group or modulus

Paillier `N²` (`modulus_paillier_carrier`), DJ `N³` (`modulus_dj_carrier`), OU/Takagi `p²q`
(`modulus_ou_carrier`, `arith_takagi_*`), prime `N` (`modulus_prime_field`), prime-power
(`modulus_prime_power_field`, `modulus_prime_cube`), triprime (`modulus_triprime_cube_not_residual`, `arith_mixed_pqr_*`),
two safeprimes (`modulus_two_safeprimes`), `N=55,119,209,221,323` (`modulus_N55_cube_residual_shaped`–`modulus_N323_cube_shares`),
Williams torus `V_e` (`modulus_williams_Ve`), Cocks Jacobi (`modulus_cocks_jacobi`). Not the
semiprime cube.

## 9. Restricted algebraic machines

Not standard-model hardness. GRA / SLP / Jacobi: `GenericRing.v`,
`BrownSLP.v`, CAS `115`–`120`. GGM: `GenericGroup.v`, CAS `121`–`122`.
SAGM as the *only* writing of `x`: `SolverRestrict.v`, CAS `128`.
JNT affine integer cubes: `JouxNaccacheThome.v`. Prep-GRA with
advice `N/17`: `PreprocessGRA.v`.

## 10. Proof files (by cut)

| Cut | Prefix | Rocq | CAS |
|---|---|---|---|
| peel a witness | `srsa_*` | `StrongRSAPeel.v` | `127` |
| SAGM / safeprime / poly `e` | `sagm_*` / `safeprime_*` / `poly_e_*` / `reject_sample_*` | `SolverRestrict.v` | `128`, `139` |
| first dozen inroads | `dozen_*` | `DozenInroads.v` | `129` |
| solver shapes | `shape_*` | `SolverShape.v` | `130`, `142` |
| public filters | `filter_*` | `FilterShape.v` | `131`, `139`, `143` |
| arithmetic maps | `arith_*` | `ArithShape.v` | `132` |
| leftover language of `(x,e)` | `residual_*` | `SrsaResidual.v` | `143` |
| `⟨y⟩ ≅ C₈×C₅` | `primary_*` | `SrsaPrimary.v` | |
| dictionary / cubing cycles / SAGM-on-`y` | `dict_*` | `SrsaDict.v` | |
| gcd vs multiply | `period_*` | `SrsaPeriod.v` | `140`, `141`, `144` |
| Order / residual sRSA / Factor arrows | `order_yields_*` / `leftover_*_mismatch_*` / `matching_247_*` | `Hardness.v`, `SrsaOrderArrows.v` | `145` |
| public `X(N,y)` | `xmap_*` | `SrsaWriteX.v` | |
| public `E(N,y)` | `emap_*` | `SrsaWriteE.v` | |
| extra tapes | `extra_*` | `SrsaExtra.v` | |
| named factoring engines | `engine_*` | `SrsaEngines.v` | |
| different group / modulus | `modulus_*` | `SrsaModulus.v` | |

CAS `133`–`138` are the probe classes 1–500; they do not name Rocq
identifiers. Verbose residues: `cas/verbose_dump.gp` (not globbed).
