# One hundred Strong-RSA algorithm-class inroads

CAS probe classes 1–100 in [`cas/133_hundred.gp`](../cas/133_hundred.gp).
Grouping by *question* is [`srsa-cuts.md`](srsa-cuts.md). Rocq names are
semantic (`xmap_*`, `emap_*`, `extra_*`, `engine_*`, `modulus_*`); this
table is the CAS↔Rocq crosswalk, not an index of theorem IDs.

Cuts of the writer, not a verdict on residual-solver ⇒ factor
(`residual_solver_constructs_factor_open_named`). Pin `N=187`
unless noted.

| # | Class | Rocq | Fate |
|---:|---|---|---|
| 1 | Odd monomial `x=y³` | `xmap_odd_monomial` | does not invert; one-sided cube splits (`gcd=17`) |
| 2 | Associate `N−x` | `xmap_associate` | does not inhabit |
| 3 | Midpoint `\|y−⌊N/2⌋\|` | `xmap_midpoint` | does not inhabit |
| 4 | `e=φ(y)` | `emap_phi_y_even` | peels (even `e`) |
| 5 | `e=` Hamming(`y`) | `emap_hamming_even` | peels (even `e`) |
| 6 | Shamir two leftovers | `extra_shamir_two_leftovers` | product, not a factor |
| 7 | Paillier `(ℤ/N²ℤ)*` | `modulus_paillier_carrier` | different group |
| 8 | Williams `V_e` output | `modulus_williams_Ve` | torus, not the cube |
| 9 | LSB(`y`) then constant `e` | `emap_lsb_y_even` | discrete `e`, even branch |
| 10 | `x=y^e` encrypt-as-decrypt | `xmap_encrypt_as_decrypt` | does not invert (`93≠42`); same monomial as 1 |
| 11 | `e=25=5²` | `emap_e25_shares_lambda` | not residual |
| 12 | Coppersmith-small `x` | `xmap_not_coppersmith_small` | residual `x` outside bound |
| 13 | Odd monomial `x=y⁵` | `xmap_odd_monomial_y5` | does not inhabit |
| 14 | `x=y^y` | `xmap_y_to_the_y` | does not inhabit |
| 15 | `x=y^N` | `xmap_y_to_the_N` | leftover cube on this pin (`N≡d mod ord y`) |
| 16 | `x=y^{N−1}` | `xmap_y_to_Nminus1` | does not inhabit |
| 17 | `x=y^{N+1}` | `xmap_y_to_Nplus1` | does not inhabit |
| 18 | `x=⌊√y⌋` | `xmap_floor_sqrt_y` | square, even-`e` peel |
| 19 | `x=⌊y/2⌋` | `xmap_half_y` | does not inhabit |
| 20 | 6-bit reverse of `y` | `xmap_bitrev_36_is_9` | reverse of `36` is `9`; one-sided cube splits (`gcd=11`) |
| 21 | Triangular `y(y−1)/2` | `xmap_triangular` | `69` is a 5th root of `1` |
| 22 | `nextprime(y)` as `x` | `xmap_nextprime_as_x` | does not inhabit |
| 23 | `x=F_y` Fibonacci | `xmap_fibonacci_y` | splits (`gcd(85,N)=17`, non-unit `x`) |
| 24 | `x=2^y` | `xmap_exp_base2` | does not invert; one-sided cube splits (`gcd=11`) |
| 25 | `x=3^y` | `xmap_exp_base3` | does not inhabit |
| 26 | `x=Φ_3(y)` | `xmap_phi3_of_y` | does not inhabit |
| 27 | `x=(y^{-1})³` | `xmap_inv_then_cube` | does not invert; one-sided cube splits (`gcd=11`) |
| 28 | `x=(y³)^{-1}` | `xmap_cube_then_inv` | same residue as 27; one-sided cube splits |
| 29 | Hybrid CRT`(1, y mod q)` | `xmap_hybrid_crt` | unit, not a root |
| 30 | Mismatched CRT`(x_p,1)` | `xmap_mismatched_crt_splits` | splits |
| 31 | Integer JNT `y+c` cube | `xmap_integer_jnt` | only when `y+c` is a cube |
| 32 | `x=y²+1` | `xmap_y2_plus_1` | does not inhabit |
| 33 | `e=λ(y)` | `emap_lambda_y_even` | peels (even) |
| 34 | `e=` bitlength(`y`) | `emap_bitlength_even` | peels (even) |
| 35 | `e=τ(y)` | `emap_tau_leftover_e9` | leftover-shaped `e=9` |
| 36 | `e=σ(y)` | `emap_sigma_leftover` | leftover `25^{91}≡36` |
| 37 | `e=rad(y)` | `emap_rad_even` | peels (even) |
| 38 | `e=ω(y)` | `emap_omega_even` | peels (even) |
| 39 | `e=Ω(y)` | `emap_Omega_even` | peels (even) |
| 40 | `e=` largest prime factor of `y` | `emap_lpf_hits_cube` | leftover cube |
| 41 | `e=y+1` | `emap_y_plus_1_is_nextprime` | coincides with `nextprime` here |
| 42 | `e=` odd part of `y` | `emap_odd_part_e9` | leftover-shaped `e=9` |
| 43 | `e=2·Hamming(y)+1` | `emap_odd_hamming_shares` | shares `λ` |
| 44 | `e=gcd(y−1,N−1)` | `emap_gcd_yminus1_Nminus1` | `=1`, fallback |
| 45 | `e=Φ_3(y)` | `emap_phi3_y_leftover_shaped` | leftover-shaped |
| 46 | `e` from `v₂(y−1)` / `2v₂(y)+1` | `emap_v2_yminus1` | shares `λ` |
| 47 | next Mersenne `e=63` | `emap_mersenne_leftover` | leftover `9^{63}≡36` |
| 48 | `e=N mod y` | `emap_N_mod_y_hits_e7` | leftover `e=7` |
| 49 | `e=2^{⌊log₂ y⌋}+1` | `emap_fermatish_leftover` | leftover `53^{33}≡36` |
| 50 | smooth `e=30` | `emap_smooth_even` | peels (even) |
| 51 | extra CRT `d_p` | `extra_crt_dp` | one-sided annihilator |
| 52 | extra Fermat `p−q` | `extra_fermat_difference` | with `N` factors |
| 53 | extra square root of `y` | `extra_sqrt_splits` | mixed √ splits |
| 54 | extra `ord(g)` | `extra_order_is_lambda` | trapdoor `λ` |
| 55 | extra factorisation of `e−1` | `extra_factor_e_minus_1` | Miller-on-`e−1` splits |
| 56 | extra factorisation of `N−1` | `extra_factor_N_minus_1` | public `186=2·3·31` |
| 57 | extra Wiener `(k,d)` | `extra_wiener_d_not_small` | `d` not small here |
| 58 | extra sequential-square tape | `extra_sequential_square_period` | `2^{λ}≡1` |
| 59 | extra 2-adic heights | `extra_height_mismatch` | mismatch `(1,3)` |
| 60 | extra primitive root mod `p` | `extra_primitive_root_mod_p` | `2` generates `𝔽₁₁*` |
| 61 | extra half-bits of `x` | `extra_half_bits` | `42 = (5,2)` in 3+3 bits |
| 62 | extra cubic/Jacobi symbol | `extra_cubic_symbol_vacuous` | permutation, vacuous |
| 63 | challenges `y` and `y^{-1}` | `extra_inverse_challenge` | cube root of inverse is inverse of root |
| 64 | challenges `y` and `−y` | `extra_neg_y` | `−y≡151` |
| 65 | challenges `y` and `2y` | `extra_two_y` | known multiplier |
| 66 | `y,y²,y³` exponent gcd | `extra_three_powers_gcd` | `gcd(3,5)=1` |
| 67 | units `y` and `y+1` | `extra_y_plus_1_root` | `126³≡37` |
| 68 | batch `gcd(x_i−x_j,N)` | `extra_batch_gcd_of_roots` | `gcd(42−60,N)=1` |
| 69 | adaptive `λ+1` | `extra_adaptive_lambda_plus_one` | search extra, not residual |
| 70 | same `y`, two coprime moduli | `extra_same_y_two_moduli` | `gcd(187,247)=1` |
| 71 | twin exponents `e,e+2` | `extra_twin_exponents` | Shamir coprime |
| 72 | product of two leftover roots | `extra_product_of_leftovers` | `89` is not a cube root |
| 73 | rerand-invariant solver | `extra_rerand_forces_fixed_e` | forces fixed `e=3` |
| 74 | coins independent of `y` | `extra_coins_independent_fixed_e` | fixed-`e` leftover cube |
| 75 | Pollard `p−1` as solver | `engine_pollard_p1` | splits (`M=60`) |
| 76 | Pollard rho | `engine_rho_walk` | splits (Monte-Carlo walk) |
| 77 | BSGS treating `N` as prime | `engine_bsgs_wrong_order` | `λ≠N−1` |
| 78 | Fermat factoring, ignore `y` | `engine_fermat_splits` | splits this pin |
| 79 | trial division | `engine_trial_division` | splits |
| 80 | Williams `p+1` Lucas | `engine_williams_pplus1` | `V₁₂(P=5)` splits |
| 81 | index calculus as if prime | `engine_index_calculus_Nminus1` | `N−1` period does not split |
| 82 | squaring-only chain | `extra_squaring_only` | `2^{8}` |
| 83 | bounded advice on `y` | `extra_advice_on_y_lsb` | 1-bit LSB |
| 84 | streaming bits of `y` | `extra_streaming_first_bit` | first bit `0` |
| 85 | Okamoto–Uchiyama `p²q` | `modulus_ou_carrier` | different map on `p²` |
| 86 | Damgård–Jurik `N³` | `modulus_dj_carrier` | different group |
| 87 | Cocks identity | `modulus_cocks_jacobi` | Jacobi, not an `e`-th root |
| 88 | prime-power `N=p²` / field | `modulus_prime_power_field` | AMM in `𝔽₁₇` |
| 89 | two safeprimes | `modulus_two_safeprimes` | cube shares `λ` on `161` |
| 90 | RW-shaped primes, odd `e` | `modulus_rw_shape_odd_e` | Williams shape `11,23` |
| 91 | twin primes | `modulus_twins` | Fermat centre public |
| 92 | unbalanced `p≪√N` | `modulus_unbalanced` | trial splits `1111` |
| 93 | triprime residual cube | `modulus_triprime_cube_not_residual` | `gcd(3,12)=3`, cube not residual |
| 94 | prime `N` | `modulus_prime_field` | field cube roots |
| 95 | `e=N` | `emap_e_eq_N` | coprime to `λ`, not `λ`-type |
| 96 | `e=N−2` | `emap_e_eq_Nminus2` | shares `λ` |
| 97 | `x=N−1` | `xmap_x_eq_Nminus1` | `(−1)³≢36` |
| 98 | `x=⌊√N⌋` | `xmap_floor_sqrt_N` | does not inhabit |
| 99 | `e=Φ₃(N)` | `xmap_phi3_of_N` | leftover-shaped public `e` |
| 100 | DL of `y` base `3` | `extra_dl_base3` | `y=3^{46}`, `x=3^{42}`, `ae≡c (mod λ)` |

Count: 100. CAS `133`. Jacobian leftover stays unnamed as factoring.
A second hundred is `notes/hundred2.md` / CAS `135`.

Verbose residue dump (not globbed): `cas/verbose_dump.gp`. On this pin `y=6²=(q−p)²` and `x=y+√y`, so several public maps collide; `y^N≡x` is `N≡d (mod ord y)`, not a general solver. Classes 1, 20, 23, 24, 27, 28 leak a prime without being residual cubes.

## Joined identity (CAS `134`)

`cas/134_whole_identity.gp` loads `cas/lib/pin.gp` and `cas/lib/classes.gp`
and checks `whole()` on the default pin: residual ∧ ¬factor_from_x ∧
peel_all ∧ classes_all. That is a conjunction of recorded fates on
`(N,y,x,e)=(187,36,42,3)`, not a disjunction of solvers, not CRT of
theorems, and not a proof that the residual cube factors. Numbered
witnesses `01`–`133` stay. Second moduli `77`, `253`, `45`, `105`,
`247`, `N²` are named extra pins, not a replacement of `N=187`.
