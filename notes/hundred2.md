# Second hundred Strong-RSA algorithm-class inroads

Stable IDs 101–200. Grouping by *question*: [`srsa-cuts.md`](srsa-cuts.md).

Roster of items 101–200. Each class has a Rocq headline `hun_NN_*`
and a PARI probe in `cas/135_hundred2.gp`. None inhabits
`srsa_residual_leaf` as `Problem_Factor`. Pin `N=187` unless noted.

Files: `HundredI.v` (101–120), `HundredJ.v` (121–140),
`HundredK.v` (141–160), `HundredL.v` (161–180), `HundredM.v` (181–200).

| # | Class | Rocq | Fate |
|---:|---|---|---|
| 101 | Odd monomial `x=y⁷` | `hun_101_y7_onesided` | one-sided cube splits (`gcd=11`) |
| 102 | Odd monomial `x=y⁹` | `hun_102_y9_cubes_to_root` | `70³≡42`, not `36` |
| 103 | Odd monomial `x=y¹¹` | `hun_103_y11_onesided` | one-sided cube splits (`gcd=17`) |
| 104 | `x=⌊y/3⌋` | `hun_104_floor_y_div_3` | does not inhabit |
| 105 | `x=⌊N/y⌋` | `hun_105_floor_N_div_y` | does not inhabit |
| 106 | `x=3y` | `hun_106_three_y_onesided` | one-sided cube splits (`gcd=11`) |
| 107 | `x=y−1` | `hun_107_y_minus_1` | does not inhabit |
| 108 | `x=y+1` | `hun_108_y_plus_1_as_x` | coincides with nextprime-as-`x`; not a root |
| 109 | `x=2y+1` | `hun_109_two_y_plus_1` | does not inhabit |
| 110 | `x=y²−1` | `hun_110_y2_minus_1` | does not inhabit |
| 111 | Gray code of `y` | `hun_111_gray_code` | `54³≡10` |
| 112 | nibble-swap of `y` | `hun_112_nibble_swap_nonunit` | splits (`gcd(66,N)=11`) |
| 113 | `x=` popcount(`y`) | `hun_113_popcount_as_x` | does not inhabit |
| 114 | `x=C_5` Catalan | `hun_114_catalan_C5` | leftover cube on this pin |
| 115 | `x=L_8` Lucas | `hun_115_lucas_L8` | does not inhabit |
| 116 | `x=⌊y^{3/2}⌋` | `hun_116_floor_y_three_halves` | does not inhabit |
| 117 | `x=y≪2` | `hun_117_shift_left_2_onesided` | one-sided cube splits (`gcd=17`) |
| 118 | `x=y mod 16` | `hun_118_y_mod_16` | does not inhabit |
| 119 | 8-bit reverse of `y` | `hun_119_eightbit_palindrome` | palindrome `x=y`, cubes to `93` |
| 120 | `x=p(10)` partition | `hun_120_partition_p10` | leftover cube on this pin |
| 121 | `e=y−1` | `hun_121_e_y_minus_1_shares` | shares `λ` |
| 122 | `e=2y+1` | `hun_122_e_two_y_plus_1` | leftover `53^{73}≡36` |
| 123 | `e=2y−1` | `hun_123_e_two_y_minus_1` | leftover `179^{71}≡36` |
| 124 | `e=` prevprime(`y`) | `hun_124_prevprime_e31` | leftover `179^{31}≡36` |
| 125 | `e=ψ(y)` Dedekind | `hun_125_dedekind_psi_even` | peels (even) |
| 126 | `e=ord(y)` | `hun_126_ord_y_even` | peels (even) |
| 127 | `e=φ(N)` | `hun_127_phi_N_even` | peels (even) |
| 128 | `e=d` trapdoor as exponent | `hun_128_e_eq_d` | leftover `93^{27}≡36` |
| 129 | `e=s(y)` aliquot | `hun_129_aliquot_shares` | shares `λ` |
| 130 | `e=17` Fermat | `hun_130_e17_leftover` | leftover `104^{17}≡36` |
| 131 | `e=N+1` | `hun_131_e_N_plus_1_even` | peels (even) |
| 132 | `e=N−1` | `hun_132_e_N_minus_1_even` | peels (even) |
| 133 | `e=λ−1` | `hun_133_e_lam_minus_1` | leftover `26^{79}≡36` |
| 134 | `e=φ(y)+1` | `hun_134_phi_y_plus_1` | leftover `185^{13}≡36` |
| 135 | `e=` digit-sum(`y`) | `hun_135_digit_sum_e9` | leftover-shaped `e=9` |
| 136 | `e=111` repunit | `hun_136_repunit_111` | leftover `179^{111}≡36` |
| 137 | `e=7#` primorial | `hun_137_primorial_even` | peels (even) |
| 138 | `e=5` Fermat | `hun_138_fermat_5_shares` | shares `λ` |
| 139 | `e=` Collatz steps of `y` | `hun_139_collatz_e21` | leftover `168^{21}≡36` |
| 140 | `e=` squarefree core of `y` | `hun_140_squarefree_core_e9` | leftover-shaped `e=9` |
| 141 | extra `p+q` | `hun_141_p_plus_q` | Fermat centre `28` |
| 142 | extra torus order | `hun_142_torus_order_is_y` | `lcm(p+1,q+1)=y` on this pin |
| 143 | extra `φ/λ` | `hun_143_phi_over_lambda` | index `2` |
| 144 | extra `N mod 8` | `hun_144_N_mod_8` | `N≡3 (mod 8)` |
| 145 | extra bitlength(`N`) | `hun_145_bitlength_N` | 8 bits |
| 146 | extra `v₂(N−1)` | `hun_146_v2_N_minus_1` | `=1` |
| 147 | extra cyclicity | `hun_147_units_not_cyclic` | `λ≠φ`, not cyclic |
| 148 | extra Hamming(`N`) | `hun_148_hamming_N` | weight `6` |
| 149 | extra digit-reverse(`N`) | `hun_149_digit_reverse_splits` | splits (`gcd(781,N)=11`) |
| 150 | extra `p,q mod 4` | `hun_150_mod4_shape` | `p≡3`, `q≡1` |
| 151 | extra 2-Sylow shape | `hun_151_N_mod_8_two_sylow` | `N≡3 (mod 8)` |
| 152 | extra decimal digits of `N` | `hun_152_digits_of_N` | `1,8,7` |
| 153 | extra `N mod 100` | `hun_153_N_mod_100` | `87` |
| 154 | extra nextprime(`N`) | `hun_154_nextprime_N` | `191` |
| 155 | extra prevprime(`N`) | `hun_155_prevprime_associate` | `181` even-associate of `−6` |
| 156 | extra `y^λ` | `hun_156_y_to_lambda` | `≡1` |
| 157 | extra `y^φ` | `hun_157_y_to_phi` | Euler |
| 158 | extra base-`3` periods | `hun_158_base3_period` | `3^{10}−1` splits; `3^8−1` does not |
| 159 | extra `ord(2)` | `hun_159_ord2_is_40` | period `40` |
| 160 | extra `φ=(p−1)(q−1)` | `hun_160_phi_is_product` | definitional |
| 161 | XOR of two leftovers | `hun_161_xor_leftovers` | `22` is not a cube root |
| 162 | related `y` and `y³` | `hun_162_related_y_cube` | ciphertext `93` |
| 163 | `e=43` same leftover `x` | `hun_163_e43_same_x` | leftover `42^{43}≡36` |
| 164 | `e=47` second leftover | `hun_164_e47_second_leftover` | leftover `60^{47}≡36` |
| 165 | `e=23` | `hun_165_e23_ninth` | leftover `9^{23}≡36` |
| 166 | `e=19` | `hun_166_e19_leftover` | leftover `59^{19}≡36` |
| 167 | `x=e=59` | `hun_167_e_eq_x` | leftover `59^{59}≡36` |
| 168 | `gcd(F_9,N)` | `hun_168_F9_splits` | splits |
| 169 | `gcd(F_10,N)` | `hun_169_F10_splits` | splits |
| 170 | Mersenne `2^8−1` | `hun_170_mersenne_255` | splits |
| 171 | Catalan `C_6` as `x` | `hun_171_catalan_C6_nonunit` | splits (`gcd(132,N)=11`) |
| 172 | `x=y^{-2}` | `hun_172_y_inv_sq` | does not inhabit |
| 173 | `x=y^λ` | `hun_173_y_to_lam_identity` | identity, not a root of `36` |
| 174 | `x=φ(N)` | `hun_174_x_eq_phi` | does not inhabit |
| 175 | `x=` bitlength(`N`) | `hun_175_x_bitlength_N` | does not inhabit |
| 176 | batch `gcd` of leftovers `42,25` | `hun_176_leftover_pair_splits` | splits (`gcd=17`); `42,60` does not |
| 177 | `e=N−λ` | `hun_177_e_N_minus_lam` | leftover `93^{107}≡36` |
| 178 | first nibble of `y` | `hun_178_first_nibble` | `4` |
| 179 | two-bit advice on `y` | `hun_179_two_bit_advice` | `y≡0 (mod 4)` |
| 180 | nextprime(`N`) as `x` | `hun_180_nextprime_mod_N` | `4³≡64` |
| 181 | Pollard `p−1` `B=8` | `hun_181_pminus1_B8` | annihilates both sides, no proper factor |
| 182 | rho `f=x²−1` | `hun_182_rho_x2_minus_1` | splits |
| 183 | Williams `P=3` | `hun_183_williams_P3_no_split` | `V₁₂` does not split |
| 184 | factorial trial `10!` | `hun_184_factorial_trial` | no split |
| 185 | Hart one-line | `hun_185_hart_square` | `14²−N=9` |
| 186 | Fermat/Lehman recover | `hun_186_fermat_recovers` | splits this pin |
| 187 | trial `13` then `11` | `hun_187_trial_13_then_11` | `13` misses, `11` hits |
| 188 | Fibonacci gcd engine | `hun_188_fibonacci_gcd_engine` | `F_9` splits |
| 189 | Mersenne engine | `hun_189_mersenne_engine` | `2^8−1` splits |
| 190 | Shor period of `2` | `hun_190_shor_period_of_2` | `40≠λ` |
| 191 | `N=55=5·11` | `hun_191_N55_cube_residual_shaped` | cube residual-shaped |
| 192 | `N=119=7·17` | `hun_192_N119_cube_shares` | cube shares `λ` |
| 193 | `N=209=11·19` | `hun_193_N209_cube_shares` | cube shares `λ` |
| 194 | `N=221=13·17` | `hun_194_N221_cube_shares` | cube shares `λ` |
| 195 | `N=323=17·19` | `hun_195_N323_cube_shares` | cube shares `λ` |
| 196 | `N=p³=1331` | `hun_196_prime_cube` | prime power |
| 197 | DL base `5` | `hun_197_dl_base5` | `y=5^{22}`, `x=5^{34}`, `ae≡c (mod λ)` |
| 198 | DL base `9` | `hun_198_dl_base9` | `y=9^{23}`, `x=9^{21}` |
| 199 | `e=` nextprime(`N`) | `hun_199_e_nextprime_N` | leftover-shaped `e=191` |
| 200 | `x=` prevprime(`N`) | `hun_200_prevprime_even_peel` | even-`e` peel `181²≡36` |

Count: 100. CAS `135`. Jacobian leftover stays unnamed as factoring.
The first hundred (`notes/hundred.md`, CAS `133`) is unchanged.
A third hundred is `notes/hundred3.md` / CAS `136`.
`whole()` still conjoins classes 1–100 only.
