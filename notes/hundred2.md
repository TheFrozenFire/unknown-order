# Second hundred Strong-RSA algorithm-class inroads

CAS probe classes 101–200 in [`cas/135_hundred2.gp`](../cas/135_hundred2.gp).
Grouping by *question*: [`srsa-cuts.md`](srsa-cuts.md). Rocq names are
semantic; this table is the CAS↔Rocq crosswalk.

None inhabits `srsa_residual_leaf` as `Problem_Factor`. Pin `N=187`
unless noted.

| # | Class | Rocq | Fate |
|---:|---|---|---|
| 101 | Odd monomial `x=y⁷` | `xmap_y7_onesided` | one-sided cube splits (`gcd=11`) |
| 102 | Odd monomial `x=y⁹` | `xmap_y9_cubes_to_root` | `70³≡42`, not `36` |
| 103 | Odd monomial `x=y¹¹` | `xmap_y11_onesided` | one-sided cube splits (`gcd=17`) |
| 104 | `x=⌊y/3⌋` | `xmap_floor_y_div_3` | does not inhabit |
| 105 | `x=⌊N/y⌋` | `xmap_floor_N_div_y` | does not inhabit |
| 106 | `x=3y` | `xmap_three_y_onesided` | one-sided cube splits (`gcd=11`) |
| 107 | `x=y−1` | `xmap_y_minus_1` | does not inhabit |
| 108 | `x=y+1` | `xmap_y_plus_1_as_x` | coincides with nextprime-as-`x`; not a root |
| 109 | `x=2y+1` | `xmap_two_y_plus_1` | does not inhabit |
| 110 | `x=y²−1` | `xmap_y2_minus_1` | does not inhabit |
| 111 | Gray code of `y` | `xmap_gray_code` | `54³≡10` |
| 112 | nibble-swap of `y` | `xmap_nibble_swap_nonunit` | splits (`gcd(66,N)=11`) |
| 113 | `x=` popcount(`y`) | `xmap_popcount_as_x` | does not inhabit |
| 114 | `x=C_5` Catalan | `xmap_catalan_C5` | leftover cube on this pin |
| 115 | `x=L_8` Lucas | `xmap_lucas_L8` | does not inhabit |
| 116 | `x=⌊y^{3/2}⌋` | `xmap_floor_y_three_halves` | does not inhabit |
| 117 | `x=y≪2` | `xmap_shift_left_2_onesided` | one-sided cube splits (`gcd=17`) |
| 118 | `x=y mod 16` | `xmap_y_mod_16` | does not inhabit |
| 119 | 8-bit reverse of `y` | `xmap_eightbit_palindrome` | palindrome `x=y`, cubes to `93` |
| 120 | `x=p(10)` partition | `xmap_partition_p10` | leftover cube on this pin |
| 121 | `e=y−1` | `emap_e_y_minus_1_shares` | shares `λ` |
| 122 | `e=2y+1` | `emap_e_two_y_plus_1` | leftover `53^{73}≡36` |
| 123 | `e=2y−1` | `emap_e_two_y_minus_1` | leftover `179^{71}≡36` |
| 124 | `e=` prevprime(`y`) | `emap_prevprime_e31` | leftover `179^{31}≡36` |
| 125 | `e=ψ(y)` Dedekind | `emap_dedekind_psi_even` | peels (even) |
| 126 | `e=ord(y)` | `emap_ord_y_even` | peels (even) |
| 127 | `e=φ(N)` | `emap_phi_N_even` | peels (even) |
| 128 | `e=d` trapdoor as exponent | `dict_e_eq_d` | leftover `93^{27}≡36` |
| 129 | `e=s(y)` aliquot | `emap_aliquot_shares` | shares `λ` |
| 130 | `e=17` Fermat | `emap_e17_leftover` | leftover `104^{17}≡36` |
| 131 | `e=N+1` | `emap_e_N_plus_1_even` | peels (even) |
| 132 | `e=N−1` | `emap_e_N_minus_1_even` | peels (even) |
| 133 | `e=λ−1` | `emap_e_lam_minus_1` | leftover `26^{79}≡36` |
| 134 | `e=φ(y)+1` | `emap_phi_y_plus_1` | leftover `185^{13}≡36` |
| 135 | `e=` digit-sum(`y`) | `emap_digit_sum_e9` | leftover-shaped `e=9` |
| 136 | `e=111` repunit | `emap_repunit_111` | leftover `179^{111}≡36` |
| 137 | `e=7#` primorial | `emap_primorial_even` | peels (even) |
| 138 | `e=5` Fermat | `emap_fermat_5_shares` | shares `λ` |
| 139 | `e=` Collatz steps of `y` | `emap_collatz_e21` | leftover `168^{21}≡36` |
| 140 | `e=` squarefree core of `y` | `emap_squarefree_core_e9` | leftover-shaped `e=9` |
| 141 | extra `p+q` | `extra_p_plus_q` | Fermat centre `28` |
| 142 | extra torus order | `extra_torus_order_is_y` | `lcm(p+1,q+1)=y` on this pin |
| 143 | extra `φ/λ` | `residual_phi_over_lambda` | index `2` |
| 144 | extra `N mod 8` | `residual_N_mod_8` | `N≡3 (mod 8)` |
| 145 | extra bitlength(`N`) | `residual_bitlength_N` | 8 bits |
| 146 | extra `v₂(N−1)` | `residual_v2_N_minus_1` | `=1` |
| 147 | extra cyclicity | `residual_units_not_cyclic` | `λ≠φ`, not cyclic |
| 148 | extra Hamming(`N`) | `extra_hamming_N` | weight `6` |
| 149 | extra digit-reverse(`N`) | `extra_digit_reverse_splits` | splits (`gcd(781,N)=11`) |
| 150 | extra `p,q mod 4` | `residual_mod4_shape` | `p≡3`, `q≡1` |
| 151 | extra 2-Sylow shape | `residual_N_mod_8_two_sylow` | `N≡3 (mod 8)` |
| 152 | extra decimal digits of `N` | `extra_digits_of_N` | `1,8,7` |
| 153 | extra `N mod 100` | `extra_N_mod_100` | `87` |
| 154 | extra nextprime(`N`) | `extra_nextprime_N` | `191` |
| 155 | extra prevprime(`N`) | `extra_prevprime_associate` | `181` even-associate of `−6` |
| 156 | extra `y^λ` | `residual_y_to_lambda` | `≡1` |
| 157 | extra `y^φ` | `residual_y_to_phi` | Euler |
| 158 | extra base-`3` periods | `period_base3_period` | `3^{10}−1` splits; `3^8−1` does not |
| 159 | extra `ord(2)` | `residual_ord2_is_40` | period `40` |
| 160 | extra `φ=(p−1)(q−1)` | `residual_phi_is_product` | definitional |
| 161 | XOR of two leftovers | `extra_xor_leftovers` | `22` is not a cube root |
| 162 | related `y` and `y³` | `extra_related_y_cube` | ciphertext `93` |
| 163 | `e=43` same leftover `x` | `dict_e43_same_x_leaf` | leftover `42^{43}≡36` |
| 164 | `e=47` second leftover | `emap_e47_second_leftover` | leftover `60^{47}≡36` |
| 165 | `e=23` | `emap_e23_ninth` | leftover `9^{23}≡36` |
| 166 | `e=19` | `emap_e19_leftover` | leftover `59^{19}≡36` |
| 167 | `x=e=59` | `emap_e_eq_x` | leftover `59^{59}≡36` |
| 168 | `gcd(F_9,N)` | `engine_F9_splits` | splits |
| 169 | `gcd(F_10,N)` | `engine_F10_splits` | splits |
| 170 | Mersenne `2^8−1` | `engine_mersenne_255` | splits |
| 171 | Catalan `C_6` as `x` | `xmap_catalan_C6_nonunit` | splits (`gcd(132,N)=11`) |
| 172 | `x=y^{-2}` | `xmap_y_inv_sq` | does not inhabit |
| 173 | `x=y^λ` | `residual_y_to_lam_identity` | identity, not a root of `36` |
| 174 | `x=φ(N)` | `xmap_x_eq_phi` | does not inhabit |
| 175 | `x=` bitlength(`N`) | `xmap_x_bitlength_N` | does not inhabit |
| 176 | batch `gcd` of leftovers `42,25` | `extra_leftover_pair_splits` | splits (`gcd=17`); `42,60` does not |
| 177 | `e=N−λ` | `emap_e_N_minus_lam` | leftover `93^{107}≡36` |
| 178 | first nibble of `y` | `extra_first_nibble` | `4` |
| 179 | two-bit advice on `y` | `extra_two_bit_advice` | `y≡0 (mod 4)` |
| 180 | nextprime(`N`) as `x` | `xmap_nextprime_mod_N` | `4³≡64` |
| 181 | Pollard `p−1` `B=8` | `engine_pminus1_B8` | annihilates both sides, no proper factor |
| 182 | rho `f=x²−1` | `engine_rho_x2_minus_1` | splits |
| 183 | Williams `P=3` | `engine_williams_P3_no_split` | `V₁₂` does not split |
| 184 | factorial trial `10!` | `engine_factorial_trial` | no split |
| 185 | Hart one-line | `engine_hart_square` | `14²−N=9` |
| 186 | Fermat/Lehman recover | `engine_fermat_recovers` | splits this pin |
| 187 | trial `13` then `11` | `engine_trial_13_then_11` | `13` misses, `11` hits |
| 188 | Fibonacci gcd engine | `engine_fibonacci_gcd_engine` | `F_9` splits |
| 189 | Mersenne engine | `engine_mersenne_engine` | `2^8−1` splits |
| 190 | Shor period of `2` | `engine_shor_period_of_2` | `40≠λ` |
| 191 | `N=55=5·11` | `modulus_N55_cube_residual_shaped` | cube residual-shaped |
| 192 | `N=119=7·17` | `modulus_N119_cube_shares` | cube shares `λ` |
| 193 | `N=209=11·19` | `modulus_N209_cube_shares` | cube shares `λ` |
| 194 | `N=221=13·17` | `modulus_N221_cube_shares` | cube shares `λ` |
| 195 | `N=323=17·19` | `modulus_N323_cube_shares` | cube shares `λ` |
| 196 | `N=p³=1331` | `modulus_prime_cube` | prime power |
| 197 | DL base `5` | `extra_dl_base5` | `y=5^{22}`, `x=5^{34}`, `ae≡c (mod λ)` |
| 198 | DL base `9` | `extra_dl_base9` | `y=9^{23}`, `x=9^{21}` |
| 199 | `e=` nextprime(`N`) | `emap_e_nextprime_N` | leftover-shaped `e=191` |
| 200 | `x=` prevprime(`N`) | `emap_prevprime_even_peel` | even-`e` peel `181²≡36` |

Count: 100. CAS `135`. Jacobian leftover stays unnamed as factoring.
The first hundred (`notes/hundred.md`, CAS `133`) is unchanged.
A third hundred is `notes/hundred3.md` / CAS `136`.
`whole()` still conjoins classes 1–100 only.
