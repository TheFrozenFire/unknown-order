# Third hundred Strong-RSA algorithm-class inroads

Roster of items 201–300. Selective cuts of the **residual leaf**, not
more public maps that miss. Residual `(x,e)` on this pin lives in the
16-element generator set of `⟨y⟩` (`ord(y)=40`). Local orders of `y`
are `5` and `8`, so Pohlig/Miller on the challenge splits `N`.

None inhabits `srsa_residual_leaf` as `Problem_Factor`. Pin `N=187`.

Files: `HundredN.v` (201–220), `HundredO.v` (221–240),
`HundredP.v` (241–260), `HundredQ.v` (261–280), `HundredR.v` (281–300).
CAS `136`.

| # | Class | Rocq | Fate |
|---:|---|---|---|
| 201 | residual `x ∈ ⟨y⟩` | `hun_201_x_in_cyc_y` | `42^{40}≡1` |
| 202 | residual `x` generates `⟨y⟩` | `hun_202_x_generates` | `ord(42)=40` |
| 203 | `x=y^{e^{-1} mod 40}` | `hun_203_x_is_y_to_27` | `k=27`, `gcd(27,40)=1` |
| 204 | unit cube roots of `1` | `hun_204_cube_root_of_1` | only `{1}` among `{1,67}` |
| 205 | unique unit cube root of `y` | `hun_205_unique_unit_cube` | `x≡42` |
| 206 | `e` invertible mod `16` | `hun_206_e_inv_mod_16` | `gcd(3,16)=1` |
| 207 | `e` invertible mod `5` | `hun_207_e_inv_mod_5` | `gcd(3,5)=1` |
| 208 | CRT of `e^{-1}` | `hun_208_crt_e_inverse` | `(11,2) ↦ 27` |
| 209 | `5 \| λ` forbids `e=5` | `hun_209_five_divides_lambda` | not residual |
| 210 | local squares | `hun_210_local_squares` | `42≡3² (mod 11)≡5² (mod 17)` |
| 211 | QR both sides | `hun_211_qr_both_sides` | pin: `y` square ⇒ `x` square |
| 212 | residual `x ∉ ⟨2⟩` | `hun_212_not_in_ltwo` | different cyclic |
| 213 | residual `x ∈ ⟨3⟩,⟨5⟩` | `hun_213_in_lthree_and_lfive` | `3^{42}`, `5^{34}` |
| 214 | local cube root mod `p` | `hun_214_local_cube_mod_p` | `42≡9 (mod 11)` |
| 215 | local `x` mod `q` | `hun_215_local_x_mod_q` | `42≡8 (mod 17)` |
| 216 | CRT of locals | `hun_216_crt_locals` | combining moduli are factors |
| 217 | bits of residual `x` | `hun_217_bits_of_x` | `101010₂` |
| 218 | `x mod 8` | `hun_218_x_mod_8` | `2` |
| 219 | `x−1` | `hun_219_x_minus_1_prime` | `41` prime, no split |
| 220 | `x+1` | `hun_220_x_plus_1_prime` | `43` prime, no split |
| 221 | `φ(40)=16` generators | `hun_221_sixteen_generators` | residual `x`'s for varying `e` |
| 222 | even `k`: `y²` | `hun_222_even_k_not_generator` | not a generator; `174³` splits |
| 223 | `y^{20}` | `hun_223_y20_miller` | order-2 Miller witness `67` |
| 224 | `y^{16}` | `hun_224_y16_five_torsion` | `69⁵≡1` |
| 225 | `y^8` | `hun_225_y8_five_torsion` | `137⁵≡1` |
| 226 | `y^{32}` | `hun_226_y32_splits` | `86` one-sided cube splits |
| 227 | `y^5` | `hun_227_y5_order8` | order `8`, not a generator |
| 228 | `y^{10}` | `hun_228_y10_order4` | `89` order `4` |
| 229 | `x=1` | `hun_229_identity_not_root` | identity is not a root of `36` |
| 230 | `y^{35}` | `hun_230_y35_onesided` | one-sided cube splits (`17`) |
| 231 | `y^4` | `hun_231_y4_order10` | order `10`, not a generator |
| 232 | generator pair `42,9` | `hun_232_gen_pair_42_9` | splits |
| 233 | generator pair `42,53` | `hun_233_gen_pair_42_53` | splits |
| 234 | generator pair `42,93` | `hun_234_gen_pair_42_93` | splits |
| 235 | `gcd(y−x,N)` | `hun_235_y_minus_x` | `=1` |
| 236 | `y^{-1}` is a generator | `hun_236_y_inv_generator` | `k=39` |
| 237 | `x^{-1}` is a generator | `hun_237_x_inv_generator` | `k=13` |
| 238 | `y^{29}` | `hun_238_y29` | generator `15` |
| 239 | `y^3` | `hun_239_y3_generator` | generator `93` |
| 240 | `y^9` | `hun_240_y9_generator` | generator `70` |
| 241 | `gcd(y^5−1,N)` | `hun_241_y5_minus_1_splits` | splits (`ord_p=5`) |
| 242 | `gcd(y^8−1,N)` | `hun_242_y8_minus_1_splits` | splits (`ord_q=8`) |
| 243 | `gcd(y^{10}−1,N)` | `hun_243_y10_minus_1_splits` | splits |
| 244 | `gcd(y^4+1,N)` | `hun_244_phi8_y_splits` | splits |
| 245 | `gcd(y^2+1,N)` | `hun_245_y2_plus_1` | no split |
| 246 | `Φ_5(y)` | `hun_246_phi5_y_splits` | splits |
| 247 | `gcd(x^2−1,N)` | `hun_247_x2_minus_1` | residual `x` does not split this way |
| 248 | `gcd(y^{40}−1,N)` | `hun_248_full_period_no_split` | `=N`, no proper factor |
| 249 | Miller on `y^{20}` | `hun_249_miller_on_period2` | splits |
| 250 | local orders of `y` | `hun_250_local_orders` | `(5,8)` |
| 251 | `5 \| ord(y)` | `hun_251_five_divides_ord` | 5-primary exists |
| 252 | `8 \| ord(y)` | `hun_252_eight_divides_ord` | 2-primary of `⟨y⟩` |
| 253 | `[⟨3⟩:⟨y⟩]=2` | `hun_253_index_two` | `y` in the index-2 subgroup |
| 254 | `dl_3(y)` even | `hun_254_dl_even` | `46` |
| 255 | `y=3^{46}` | `hun_255_y_in_square_subgroup` | `⟨3²⟩` |
| 256 | advice `5 \| λ` | `hun_256_advice_five_div_lam` | names the 5-part |
| 257 | advice `v₂(λ)=4` | `hun_257_v2_lambda` | matched-deep 2-part |
| 258 | advice `ord(y) \| λ` | `hun_258_ord_divides_lam` | `40 \| 80` |
| 259 | `y^{ord}≡1` | `hun_259_y_to_ord` | definitional |
| 260 | advice `φ/λ=2` | `hun_260_phi_over_lam` | not cyclic |
| 261 | advice `λ ≠ N−1` | `hun_261_lam_ne_Nminus1` | BSGS-as-prime is the wrong order |
| 262 | `40 \| 80` | `hun_262_ord_div_lam` | same as 258 |
| 263 | `e` coprime to `10` and `16` | `hun_263_e_coprime_10_16` | both Sylows |
| 264 | `5 ∤ e` | `hun_264_five_ndiv_e` | else shares `λ` |
| 265 | `y` QR both sides | `hun_265_y_local_qr` | integer square |
| 266 | advice local root `9` | `hun_266_advice_local_9` | one-sided integer splits |
| 267 | `N ≡ d (mod 40)` | `hun_267_N_mod_40_is_d` | public `k` hits `e^{-1}` |
| 268 | bitlength of `λ` | `hun_268_bitlength_lam` | 7 bits |
| 269 | `gcd(p−1,q−1)=2` | `hun_269_gcd_pminus1_qminus1` | not cyclic |
| 270 | `λ=lcm(p−1,q−1)` | `hun_270_lambda_lcm` | definitional |
| 271 | program `x=y^{e^{-1}}` | `hun_271_y_to_e_inv` | leftover inhabited |
| 272 | public `k=N mod 40` | `hun_272_public_N_mod_40` | hits `27` on this pin |
| 273 | public `k=d` | `hun_273_y_to_d` | decrypt |
| 274 | public `k=1` | `hun_274_k1_is_y` | not the cube root |
| 275 | public `k=3` | `hun_275_k3_is_y_cube` | encrypt, not invert |
| 276 | public `d=5 \| 40` | `hun_276_public_d5_pohlig` | Pohlig splits |
| 277 | Euclid `(x−y,N)` | `hun_277_euclid_x_minus_y` | no split |
| 278 | 2-bit advice on `y` | `hun_278_low_bits_y` | `00` |
| 279 | even `k` cannot generate | `hun_279_even_k_shares_ord` | not residual `x` |
| 280 | `x=y^{-1}`, `e=λ−1` | `hun_280_inv_lam_minus_1` | leftover |
| 281 | CRT of locals as solver | `hun_281_crt_is_residual_x` | needs `{p,q}` |
| 282 | Hensel at `p²` | `hun_282_hensel_p2` | `42³≡36 (mod 121)` |
| 283 | PKCS-like pad `2^8+y` | `hun_283_pkcs_pad` | does not invert |
| 284 | integer `√y` then `n(n+1)` | `hun_284_sqrt_then_n_nplus1` | leftover cube on this pin |
| 285 | integer sqrt is a unit | `hun_285_integer_sqrt_unit` | even peel, no split |
| 286 | extra `d_p` | `hun_286_dp` | `7` |
| 287 | `e d_p−1` | `hun_287_edp_minus_1` | one-sided `p−1` |
| 288 | extra `d_q` | `hun_288_dq` | `11` |
| 289 | `e d_q−1` | `hun_289_edq_minus_1` | one-sided `q−1` |
| 290 | residual `e` prime | `hun_290_e_prime` | BP97-shaped `e=3` still residual |
| 291 | binary exp of encrypt | `hun_291_binary_encrypt` | `y³` is not invert |
| 292 | Montgomery form of `y` | `hun_292_mont_form` | `y R ≡ 53` |
| 293 | next prime `e=7` | `hun_293_prime_e7` | leftover `60⁷≡36` |
| 294 | Shamir `3,7` | `hun_294_shamir_3_7` | product, not a factor |
| 295 | ratio of leftover gens | `hun_295_ratio_five_torsion` | `42·25^{-1}≡69`, order `5` |
| 296 | ratio `42·60^{-1}` | `hun_296_ratio_y4` | `≡ y^4` |
| 297 | fixed-`e` rerand | `hun_297_rerand_fixed_e` | residual for a different `y` |
| 298 | `x^8` is 5-torsion | `hun_298_x_to_8_is_five_torsion` | `69` |
| 299 | mismatched local orders | `hun_299_mismatched_local_orders` | `(5,8)` |
| 300 | `lcm(ord_p y, ord_q y)` | `hun_300_lcm_local_orders` | `=40=ord_N y` |

Count: 100. CAS `136`. A fourth hundred is `notes/hundred4.md` / CAS `137`.
The residual cube is still not factoring:
enumerating `⟨y⟩` or writing `x=y^{e^{-1}}` inverts without a factor.
Pohlig on the mismatched local orders of `y` *does* factor — that uses
the challenge as a period oracle, not as an `e`-th root.
