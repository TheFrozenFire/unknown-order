# One hundred Strong-RSA algorithm-class inroads

Roster of items 1–100. Each class has a Rocq headline `hun_NN_*` and a
PARI probe in `cas/133_hundred.gp`. None inhabits `srsa_residual_leaf`
as `Problem_Factor`. Pin `N=187` unless noted.

Files: `HundredA.v` (1–12), `HundredB.v` (13–32), `HundredC.v` (33–50),
`HundredDE.v` (51–74), `HundredFH.v` (75–100).

| # | Class | Rocq | Fate |
|---:|---|---|---|
| 1 | Odd monomial `x=y³` | `hun_01_odd_monomial` | does not invert; one-sided cube splits (`gcd=17`) |
| 2 | Associate `N−x` | `hun_02_associate` | does not inhabit |
| 3 | Midpoint `\|y−⌊N/2⌋\|` | `hun_03_midpoint` | does not inhabit |
| 4 | `e=φ(y)` | `hun_04_phi_y_even` | peels (even `e`) |
| 5 | `e=` Hamming(`y`) | `hun_05_hamming_even` | peels (even `e`) |
| 6 | Shamir two leftovers | `hun_06_shamir_two_leftovers` | product, not a factor |
| 7 | Paillier `(ℤ/N²ℤ)*` | `hun_07_paillier_carrier` | different group |
| 8 | Williams `V_e` output | `hun_08_williams_Ve` | torus, not the cube |
| 9 | LSB(`y`) then constant `e` | `hun_09_lsb_y_even` | discrete `e`, even branch |
| 10 | `x=y^e` encrypt-as-decrypt | `hun_10_encrypt_as_decrypt` | does not invert (`93≠42`); same monomial as 1 |
| 11 | `e=25=5²` | `hun_11_e25_shares_lambda` | not residual |
| 12 | Coppersmith-small `x` | `hun_12_not_coppersmith_small` | residual `x` outside bound |
| 13 | Odd monomial `x=y⁵` | `hun_13_odd_monomial_y5` | does not inhabit |
| 14 | `x=y^y` | `hun_14_y_to_the_y` | does not inhabit |
| 15 | `x=y^N` | `hun_15_y_to_the_N` | leftover cube on this pin (`N≡d mod ord y`) |
| 16 | `x=y^{N−1}` | `hun_16_y_to_Nminus1` | does not inhabit |
| 17 | `x=y^{N+1}` | `hun_17_y_to_Nplus1` | does not inhabit |
| 18 | `x=⌊√y⌋` | `hun_18_floor_sqrt_y` | square, even-`e` peel |
| 19 | `x=⌊y/2⌋` | `hun_19_half_y` | does not inhabit |
| 20 | 6-bit reverse of `y` | `hun_20_bitrev_36_is_9` | reverse of `36` is `9`; one-sided cube splits (`gcd=11`) |
| 21 | Triangular `y(y−1)/2` | `hun_21_triangular` | `69` is a 5th root of `1` |
| 22 | `nextprime(y)` as `x` | `hun_22_nextprime_as_x` | does not inhabit |
| 23 | `x=F_y` Fibonacci | `hun_23_fibonacci_y` | splits (`gcd(85,N)=17`, non-unit `x`) |
| 24 | `x=2^y` | `hun_24_exp_base2` | does not invert; one-sided cube splits (`gcd=11`) |
| 25 | `x=3^y` | `hun_25_exp_base3` | does not inhabit |
| 26 | `x=Φ_3(y)` | `hun_26_phi3_of_y` | does not inhabit |
| 27 | `x=(y^{-1})³` | `hun_27_inv_then_cube` | does not invert; one-sided cube splits (`gcd=11`) |
| 28 | `x=(y³)^{-1}` | `hun_28_cube_then_inv` | same residue as 27; one-sided cube splits |
| 29 | Hybrid CRT`(1, y mod q)` | `hun_29_hybrid_crt` | unit, not a root |
| 30 | Mismatched CRT`(x_p,1)` | `hun_30_mismatched_crt_splits` | splits |
| 31 | Integer JNT `y+c` cube | `hun_31_integer_jnt` | only when `y+c` is a cube |
| 32 | `x=y²+1` | `hun_32_y2_plus_1` | does not inhabit |
| 33 | `e=λ(y)` | `hun_33_lambda_y_even` | peels (even) |
| 34 | `e=` bitlength(`y`) | `hun_34_bitlength_even` | peels (even) |
| 35 | `e=τ(y)` | `hun_35_tau_leftover_e9` | leftover-shaped `e=9` |
| 36 | `e=σ(y)` | `hun_36_sigma_leftover` | leftover `25^{91}≡36` |
| 37 | `e=rad(y)` | `hun_37_rad_even` | peels (even) |
| 38 | `e=ω(y)` | `hun_38_omega_even` | peels (even) |
| 39 | `e=Ω(y)` | `hun_39_Omega_even` | peels (even) |
| 40 | `e=` largest prime factor of `y` | `hun_40_lpf_hits_cube` | leftover cube |
| 41 | `e=y+1` | `hun_41_y_plus_1_is_nextprime` | coincides with `nextprime` here |
| 42 | `e=` odd part of `y` | `hun_42_odd_part_e9` | leftover-shaped `e=9` |
| 43 | `e=2·Hamming(y)+1` | `hun_43_odd_hamming_shares` | shares `λ` |
| 44 | `e=gcd(y−1,N−1)` | `hun_44_gcd_yminus1_Nminus1` | `=1`, fallback |
| 45 | `e=Φ_3(y)` | `hun_45_phi3_y_leftover_shaped` | leftover-shaped |
| 46 | `e` from `v₂(y−1)` / `2v₂(y)+1` | `hun_46_v2_yminus1` | shares `λ` |
| 47 | next Mersenne `e=63` | `hun_47_mersenne_leftover` | leftover `9^{63}≡36` |
| 48 | `e=N mod y` | `hun_48_N_mod_y_hits_e7` | leftover `e=7` |
| 49 | `e=2^{⌊log₂ y⌋}+1` | `hun_49_fermatish_leftover` | leftover `53^{33}≡36` |
| 50 | smooth `e=30` | `hun_50_smooth_even` | peels (even) |
| 51 | extra CRT `d_p` | `hun_51_extra_dp` | one-sided annihilator |
| 52 | extra Fermat `p−q` | `hun_52_fermat_difference` | with `N` factors |
| 53 | extra square root of `y` | `hun_53_extra_sqrt_splits` | mixed √ splits |
| 54 | extra `ord(g)` | `hun_54_extra_order_is_lambda` | trapdoor `λ` |
| 55 | extra factorisation of `e−1` | `hun_55_factor_e_minus_1` | Miller-on-`e−1` splits |
| 56 | extra factorisation of `N−1` | `hun_56_factor_N_minus_1` | public `186=2·3·31` |
| 57 | extra Wiener `(k,d)` | `hun_57_wiener_d_not_small` | `d` not small here |
| 58 | extra sequential-square tape | `hun_58_sequential_square_period` | `2^{λ}≡1` |
| 59 | extra 2-adic heights | `hun_59_height_mismatch` | mismatch `(1,3)` |
| 60 | extra primitive root mod `p` | `hun_60_primitive_root_mod_p` | `2` generates `𝔽₁₁*` |
| 61 | extra half-bits of `x` | `hun_61_half_bits` | `42 = (5,2)` in 3+3 bits |
| 62 | extra cubic/Jacobi symbol | `hun_62_cubic_symbol_vacuous` | permutation, vacuous |
| 63 | challenges `y` and `y^{-1}` | `hun_63_inverse_challenge` | cube root of inverse is inverse of root |
| 64 | challenges `y` and `−y` | `hun_64_neg_y` | `−y≡151` |
| 65 | challenges `y` and `2y` | `hun_65_two_y` | known multiplier |
| 66 | `y,y²,y³` exponent gcd | `hun_66_three_powers_gcd` | `gcd(3,5)=1` |
| 67 | units `y` and `y+1` | `hun_67_y_plus_1_root` | `126³≡37` |
| 68 | batch `gcd(x_i−x_j,N)` | `hun_68_batch_gcd_of_roots` | `gcd(42−60,N)=1` |
| 69 | adaptive `λ+1` | `hun_69_adaptive_lambda_plus_one` | search extra, not residual |
| 70 | same `y`, two coprime moduli | `hun_70_same_y_two_moduli` | `gcd(187,247)=1` |
| 71 | twin exponents `e,e+2` | `hun_71_twin_exponents` | Shamir coprime |
| 72 | product of two leftover roots | `hun_72_product_of_leftovers` | `89` is not a cube root |
| 73 | rerand-invariant solver | `hun_73_rerand_forces_fixed_e` | forces fixed `e=3` |
| 74 | coins independent of `y` | `hun_74_coins_independent_fixed_e` | fixed-`e` leftover cube |
| 75 | Pollard `p−1` as solver | `hun_75_pollard_p1` | splits (`M=60`) |
| 76 | Pollard rho | `hun_76_rho_walk` | splits (Monte-Carlo walk) |
| 77 | BSGS treating `N` as prime | `hun_77_bsgs_wrong_order` | `λ≠N−1` |
| 78 | Fermat factoring, ignore `y` | `hun_78_fermat_splits` | splits this pin |
| 79 | trial division | `hun_79_trial_division` | splits |
| 80 | Williams `p+1` Lucas | `hun_80_williams_pplus1` | `V₁₂(P=5)` splits |
| 81 | index calculus as if prime | `hun_81_index_calculus_Nminus1` | `N−1` period does not split |
| 82 | squaring-only chain | `hun_82_squaring_only` | `2^{8}` |
| 83 | bounded advice on `y` | `hun_83_advice_on_y_lsb` | 1-bit LSB |
| 84 | streaming bits of `y` | `hun_84_streaming_first_bit` | first bit `0` |
| 85 | Okamoto–Uchiyama `p²q` | `hun_85_ou_carrier` | different map on `p²` |
| 86 | Damgård–Jurik `N³` | `hun_86_dj_carrier` | different group |
| 87 | Cocks identity | `hun_87_cocks_jacobi` | Jacobi, not an `e`-th root |
| 88 | prime-power `N=p²` / field | `hun_88_prime_power_field` | AMM in `𝔽₁₇` |
| 89 | two safeprimes | `hun_89_two_safeprimes` | cube shares `λ` on `161` |
| 90 | RW-shaped primes, odd `e` | `hun_90_rw_shape_odd_e` | Williams shape `11,23` |
| 91 | twin primes | `hun_91_twins` | Fermat centre public |
| 92 | unbalanced `p≪√N` | `hun_92_unbalanced` | trial splits `1111` |
| 93 | triprime residual cube | `hun_93_triprime_cube_not_residual` | `gcd(3,12)=3`, cube not residual |
| 94 | prime `N` | `hun_94_prime_field` | field cube roots |
| 95 | `e=N` | `hun_95_e_eq_N` | coprime to `λ`, not `λ`-type |
| 96 | `e=N−2` | `hun_96_e_eq_Nminus2` | shares `λ` |
| 97 | `x=N−1` | `hun_97_x_eq_Nminus1` | `(−1)³≢36` |
| 98 | `x=⌊√N⌋` | `hun_98_floor_sqrt_N` | does not inhabit |
| 99 | `e=Φ₃(N)` | `hun_99_phi3_of_N` | leftover-shaped public `e` |
| 100 | DL of `y` base `3` | `hun_100_dl_base3` | `y=3^{46}`, `x=3^{42}`, `ae≡c (mod λ)` |

Count: 100. CAS `133`. Jacobian leftover stays unnamed as factoring.

Verbose residue dump (not globbed): `cas/verbose_dump.gp`. On this pin `y=6²=(q−p)²` and `x=y+√y`, so several public maps collide; `y^N≡x` is `N≡d (mod ord y)`, not a general solver. Classes 1, 20, 23, 24, 27, 28 leak a prime without being residual cubes.

## Joined identity (CAS `134`)

`cas/134_whole_identity.gp` loads `cas/lib/pin.gp` and `cas/lib/classes.gp`
and checks `whole()` on the default pin: residual ∧ ¬factor_from_x ∧
peel_all ∧ classes_all. That is a conjunction of recorded fates on
`(N,y,x,e)=(187,36,42,3)`, not a disjunction of solvers, not CRT of
theorems, and not a proof that the residual cube factors. Numbered
witnesses `01`–`133` stay. Second moduli `77`, `253`, `45`, `105`,
`247`, `N²` are named extra pins, not a replacement of `N=187`.
