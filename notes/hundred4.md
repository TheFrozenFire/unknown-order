# Fourth hundred Strong-RSA algorithm-class inroads

Roster of items 301–400. Residual dictionary, `⟨y⟩ ≅ C₈ × C₅`, the
2-to-1 map of residual `e`, and the dichotomy **gcd-Pohlig splits** vs
**equality-only order-finding leftover-inhabits**.

None inhabits `srsa_residual_leaf` as `Problem_Factor`. Pin `N=187`.

Files: `HundredS.v` (301–320), `HundredT.v` (321–340),
`HundredU.v` (341–360), `HundredV.v` (361–380), `HundredW.v` (381–400).
CAS `137`.

| # | Class | Rocq | Fate |
|---:|---|---|---|
| 301 | generator `93`, `e=67` | `hun_301_x93_e67` | leftover |
| 302 | `k=e=11`, `x=25` | `hun_302_x25_e11` | leftover self-inverse |
| 303 | `e=11+40=51` | `hun_303_x25_e51` | same `x`, second `e` |
| 304 | `k=e=29`, `x=15` | `hun_304_x15_e29` | leftover self-inverse |
| 305 | `e=29+40=69` | `hun_305_x15_e69` | same `x` |
| 306 | `x=168`, `e=61` | `hun_306_x168_e61` | leftover |
| 307 | `x=104`, `e=57` | `hun_307_x104_e57` | leftover |
| 308 | `x=185`, `e=53` | `hun_308_x185_e53` | leftover |
| 309 | `k=1`, `e=41` | `hun_309_xy_e41` | peel-gap residual-shaped `x=y` |
| 310 | `e=81=λ+1` on `y` | `hun_310_y_lambda_type` | λ-type peel |
| 311 | `e=3+80=83` | `hun_311_e_plus_80` | same cube root |
| 312 | `φ(80)=32` | `hun_312_phi80` | residual `e`-classes |
| 313 | `φ(40)=16` | `hun_313_phi40` | residual `x`-classes |
| 314 | `32/16=2` | `hun_314_two_e_per_x` | two `e` per `x` |
| 315 | `e ≡ 3 (mod 40)` | `hun_315_e_mod_40` | `3` and `43` same `x` |
| 316 | kernel `{1,41}` | `hun_316_kernel_1_41` | reduce to `1 (mod 40)` |
| 317 | cubing bijective on `⟨y⟩` | `hun_317_cube_bij_on_cyc` | `gcd(3,40)=1` |
| 318 | 27th power inverse auto | `hun_318_27th_is_inverse_auto` | `3·27≡1 (mod 40)` |
| 319 | compose autos | `hun_319_compose_autos` | `y^{27}` then cube |
| 320 | `ae=λ+1` | `hun_320_ae_is_lambda_plus_1` | SAGM identity |
| 321 | `y^5` generates `C₈` | `hun_321_C8_generator` | `100`, order `8` |
| 322 | powers of `100` | `hun_322_C8_squares` | `89,67,1` |
| 323 | `y^8` generates `C₅` | `hun_323_C5_generator` | `137`, order `5` |
| 324 | `C₅` elements | `hun_324_C5_elements` | `69,103,86` |
| 325 | cubing on `C₅` | `hun_325_cube_bij_C5` | bijective |
| 326 | cubing on `C₈` | `hun_326_cube_bij_C8` | bijective |
| 327 | reconstruct `y` | `hun_327_reconstruct_y` | `155·69≡36` |
| 328 | Bézout `5,8` | `hun_328_bezout_5_8` | `25−24=1` |
| 329 | `C₈[2]` is Miller | `hun_329_C8_order2_is_miller` | `67` |
| 330 | `v₂` of local orders | `hun_330_v2_local_orders` | `(0,3)` mismatch |
| 331 | `8 \| 40` | `hun_331_eight_div_ord` | 2-primary exists |
| 332 | `5 \| 40` | `hun_332_five_div_ord` | 5-primary exists |
| 333 | `C₈ = ⟨y^5⟩` | `hun_333_C8_is_y5` | |
| 334 | order-4 in `C₈` | `hun_334_order4_in_C8` | `89` |
| 335 | `100^6` | `hun_335_C8_pow6` | `166` |
| 336 | `100^3` | `hun_336_C8_pow3` | `111` |
| 337 | `100^5` | `hun_337_C8_pow5` | `155` |
| 338 | `100^7` | `hun_338_C8_pow7` | `144` |
| 339 | `137^3` | `hun_339_C5_pow3` | `103=y^{24}` |
| 340 | ker(square) on `C₈` | `hun_340_ker_squaring_C8` | `{1,67}` |
| 341 | bits of `k=27` | `hun_341_bits_of_27` | `16+8+2+1` |
| 342 | binary product | `hun_342_binary_product` | `y^{16}y^8 y^2 y ≡ 42` |
| 343 | add-chain `y^6` | `hun_343_add_chain_y6` | `47` |
| 344 | add-chain `y^{12}` | `hun_344_add_chain_y12` | `152` |
| 345 | add-chain `y^{24}` | `hun_345_add_chain_y24` | `103` |
| 346 | `k` odd | `hun_346_k_odd` | squaring-only cannot hit |
| 347 | Hamming(`27`)=4 | `hun_347_hamming_27` | four 1-bits |
| 348 | NAF-ish `32−4−1` | `hun_348_naf_shape` | |
| 349 | `y^{25}` | `hun_349_y25` | `C₈` part of Bézout |
| 350 | `y^{16}=g₅²` | `hun_350_y16_is_g5sq` | `C₅` part |
| 351 | gcd-path `y^5−1` | `hun_351_gcd_path_splits` | splits |
| 352 | exp-path `y^{27}` | `hun_352_exp_path_leftover` | leftover cube |
| 353 | equality `y^{40}≡1` | `hun_353_eq_order_40` | finds ord without gcd |
| 354 | equality `y^8≢1` | `hun_354_eq_not_8` | |
| 355 | equality `y^5≢1` | `hun_355_eq_not_5` | |
| 356 | SAGM on `y` | `hun_356_sagm_on_y` | `ae−1=λ` |
| 357 | `y^{81}≡y` | `hun_357_y81` | λ-type on the challenge |
| 358 | `ae=λ+1` | `hun_358_ae_lambda_plus_1` | |
| 359 | `e=43` same `x` | `hun_359_e43_same_x` | |
| 360 | `e=83` same `x` | `hun_360_e83_same_x` | |
| 361 | `43−3` multiple of `40` | `hun_361_e43_minus_3` | |
| 362 | `83−3` multiple of `λ` | `hun_362_e83_minus_3` | |
| 363 | `e=67` coprime | `hun_363_e67_coprime` | leftover-shaped |
| 364 | `e=51` coprime | `hun_364_e51_coprime` | leftover-shaped |
| 365 | `e=61` coprime | `hun_365_e61_coprime` | leftover-shaped |
| 366 | `e=57` coprime | `hun_366_e57_coprime` | leftover-shaped |
| 367 | `e=29` coprime | `hun_367_e29_coprime` | leftover-shaped |
| 368 | `e=39` coprime | `hun_368_e39_coprime` | leftover-shaped |
| 369 | `k=e=39` | `hun_369_x26_e39` | leftover `26^{39}` |
| 370 | `11²≡1 (mod 40)` | `hun_370_self_inverse_11` | self-inverse `k` |
| 371 | `40=8·5` 5-smooth | `hun_371_ord_5_smooth` | PH applies |
| 372 | `ord(y) \| λ` | `hun_372_ord_div_lam` | |
| 373 | `[λ:ord(y)]=2` | `hun_373_index_two` | |
| 374 | `y^{40}≡1` | `hun_374_eq_y40` | equality-only |
| 375 | `y^{20}≢1` | `hun_375_eq_y20` | |
| 376 | `y^8≢1` | `hun_376_eq_y8` | |
| 377 | `y^5≢1` | `hun_377_eq_y5` | |
| 378 | gcd `y^5−1` | `hun_378_gcd_y5_splits` | splits |
| 379 | gcd `y^8−1` | `hun_379_gcd_y8_splits` | splits |
| 380 | gcd `y^{40}−1` | `hun_380_gcd_full_period` | `=N`, no proper factor |
| 381 | then `x=y^{27}` | `hun_381_after_ord_invert` | leftover inhabited |
| 382 | SAGM `(27,3)` on `y` | `hun_382_sagm_ae_minus_1` | residual cube is this pair |
| 383 | `3^{-1} (mod 40)` | `hun_383_inv_mod_40` | `27` |
| 384 | `3^{-1} (mod λ)` | `hun_384_inv_mod_lam` | same `27` on this pin |
| 385 | leftover `x` generates | `hun_385_x_generates` | |
| 386 | `\|C₈\|=8` | `hun_386_C8_order` | |
| 387 | `\|C₅\|=5` | `hun_387_C5_order` | |
| 388 | `lcm(8,5)=40` | `hun_388_lcm_primaries` | |
| 389 | `gcd(8,5)=1` | `hun_389_coprime_primaries` | `C₈ ∩ C₅ = {1}` |
| 390 | `v₂(ord_p y)=0` | `hun_390_v2_ord_p` | |
| 391 | `v₂(ord_q y)=3` | `hun_391_v2_ord_q` | |
| 392 | `v₂(ord_N y)=3` | `hun_392_v2_ord_N` | max of locals |
| 393 | `v₂(λ)=4` | `hun_393_v2_lam_bigger` | missing `C₂` in `⟨y⟩` |
| 394 | `3^{40}≢1` | `hun_394_three_not_in_cyc_y` | `⟨3⟩` properly larger |
| 395 | `3^{80}≡1` | `hun_395_three_full_lambda` | |
| 396 | `dl₃(y)` even | `hun_396_y_even_power_of_3` | |
| 397 | primary product | `hun_397_product_primaries` | reconstructs `y` |
| 398 | cube leftover `x` | `hun_398_cube_of_x` | inverse auto |
| 399 | `y^{27}` | `hun_399_y_to_27` | leftover `x` |
| 400 | cubing on both primaries | `hun_400_cube_bij_primaries` | bijective |

Count: 100. CAS `137`. A fifth hundred is `notes/hundred5.md` / CAS `138`.

The residual cube is SAGM `(a,e)=(27,3)` on the challenge. Equality-only
tests `y^k ≡ 1` find `ord=40` and invert without a factor. The same
exponents as `gcd(y^k−1,N)` split. That is two programs on one pin, not
RSA ≡ factoring.
