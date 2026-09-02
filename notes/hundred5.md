# Fifth hundred Strong-RSA algorithm-class inroads

CAS probe classes 401–500 in [`cas/138_hundred5.gp`](../cas/138_hundred5.gp).
Grouping by *question*: [`srsa-cuts.md`](srsa-cuts.md). The leftover
cube root **is a Pohlig oracle** for the same mismatched local orders
as `y`. Cubing permutes the 16 generators in four 4-cycles.
`gcd(p−1,q−1)=2` so matching local orders exist only at `{1,2}`. One
`k=27` gives three leftover roots in `⟨2⟩`, `⟨3⟩`, `⟨y⟩`; two of those
pairs split `N`.

Cuts of the writer, not a verdict on residual-solver ⇒ factor. Pin `N=187`
unless noted (`77`).

| # | Class | Rocq | Fate |
|---:|---|---|---|
| 401 | Pohlig on leftover `x`, `k=5` | `period_x5_minus_1_splits` | splits |
| 402 | Pohlig on `x`, `k=8` | `period_x8_minus_1_splits` | splits |
| 403 | Pohlig on `x`, `k=10` | `period_x10_minus_1_splits` | splits |
| 404 | Pohlig on `x`, `k=16` | `period_x16_minus_1_splits` | splits |
| 405 | `gcd(x^4−1,N)` | `period_x4_minus_1` | no split |
| 406 | `gcd(x^2−1,N)` | `period_x2_minus_1` | no split |
| 407 | `x^5` generates `C₈` | `primary_x5_generates_C8` | `111` |
| 408 | `x^8` in `C₅` | `primary_x8_in_C5` | `69` |
| 409 | reconstruct `x` | `primary_reconstruct_x` | `111^5·69^2≡42` |
| 410 | `y` and `x` same oracle | `period_same_oracle` | both `gcd(·^5−1)=11` |
| 411 | `70^3≡42` | `dict_cycle_70_cube` | cubing 4-cycle |
| 412 | `42^3≡36` | `dict_cycle_42_cube` | |
| 413 | `36^3≡93` | `dict_cycle_36_cube` | |
| 414 | `93^3≡70` | `dict_cycle_93_cube` | closes cycle 1 |
| 415 | `3^4≡1 (mod 40)` | `dict_three_order_4_mod_40` | cubing has order 4 |
| 416 | `27^4≡1 (mod 40)` | `dict_27_order_4_mod_40` | inverse same order |
| 417 | `9^3≡168` | `dict_cycle2_9` | cycle 2 |
| 418 | `168^3≡60` | `dict_cycle2_168` | |
| 419 | `15^3≡9` | `dict_cycle2_15` | closes cycle 2 |
| 420 | Jacobi `x` vs `2` | `residual_jacobi_x_vs_2` | `N≡3 (mod 8)`, `x` QR mod `p` |
| 421 | order-16 unit `10` | `period_ten_order_16` | |
| 422 | `10^8≡67` | `period_ten_pow8_miller` | Miller witness |
| 423 | `gcd(10^8−1,N)` | `period_ten_pow8_splits` | splits |
| 424 | `10^{16}≡1` | `period_ten_pow16` | |
| 425 | `42 ∉ ⟨10⟩` | `residual_x_not_in_lten` | not 2-Sylow |
| 426 | order-4 unit `21` | `period_21_order_4` | `21^2≡67` |
| 427 | `gcd(21^2−1,N)` | `period_21_sq_splits` | splits |
| 428 | `89=y^{10}` order 4 | `period_89_order_4` | in `⟨y⟩` |
| 429 | mixed `√1` `120` | `srsa_sqrt1_120_splits` | splits both ways |
| 430 | `−1` | `srsa_minus1_no_split` | no Miller split |
| 431 | `p−1,q−1` | `residual_pminus1_qminus1` | `10,16` |
| 432 | `λ=lcm(10,16)` | `residual_lambda_lcm` | |
| 433 | `φ=160` | `residual_phi_product` | |
| 434 | index of `⟨y⟩` | `residual_index_four` | `4` cosets |
| 435 | leftover `x` order 40 | `residual_x_order_40` | not 16 |
| 436 | `v₂(ord x)=3` | `residual_v2_ord_x` | |
| 437 | `v₂(λ)=4` | `residual_v2_lam` | missing `C₂` |
| 438 | `69` generates `C₅` | `primary_69_generates_C5` | full 5-Sylow |
| 439 | `111` generates `C₈` | `primary_111_generates_C8` | |
| 440 | leftover `x` generates 5-Sylow | `residual_x_generates_5_sylow` | |
| 441 | `N=77`, `2^6−1` | `period_77_pminus1` | splits `7` |
| 442 | `2^{10}−1` on `77` | `period_77_qminus1` | splits `11` |
| 443 | leftover `51` Pohlig | `period_77_leftover_pohlig` | splits `7` |
| 444 | `ord(2)=λ` on `77` | `period_77_ord2_is_lam` | `30` |
| 445 | `k=27` coords | `dict_k27_coords` | `(3,2) (mod 8,5)` |
| 446 | `e=3` coords | `dict_e3_coords` | `(3,3)` |
| 447 | `3` has order 4 in `(ℤ/40ℤ)*` | `dict_3_order_4_mod_40` | not cyclic |
| 448 | `N≡3 (mod 8)` | `residual_N_mod_8_for_2` | `(2/N)=−1` |
| 449 | cube root of `2` | `dict_cube_root_of_2` | `161∈⟨2⟩` |
| 450 | SAGM of `3` | `dict_sagm_of_3` | `75^3≡3` |
| 451 | `75≠42` | `dict_75_not_42` | different instance |
| 452 | `36^{27}≡42` | `residual_y_to_27` | this instance |
| 453 | `10 mod 8` | `residual_ten_jacobi_plus` | |
| 454 | `10` not order 40 | `residual_ten_not_ord40` | |
| 455 | `21 mod 8` | `residual_21_mod_8` | |
| 456 | `⟨2⟩` order 40 | `residual_ltwo_ord40` | |
| 457 | `2≠36` | `residual_two_ne_y` | different subgroup |
| 458 | `gcd(161−42,N)` | `period_two_subgroups_split` | splits |
| 459 | four cosets | `residual_four_cosets` | residual only in `⟨y⟩` |
| 460 | `60^3≡15` | `dict_cycle2_60` | cycle 2 |
| 461 | `168^3≡60` | `dict_cycle2_168` | |
| 462 | `25^3≡104` | `dict_cycle3_25` | cycle 3 |
| 463 | `104^3≡59` | `dict_cycle3_104` | |
| 464 | `59^3≡53` | `dict_cycle3_59` | |
| 465 | `53^3≡25` | `dict_cycle3_53` | closes cycle 3 |
| 466 | `49^3≡26` | `dict_cycle4_49` | cycle 4 |
| 467 | `26^3≡185` | `dict_cycle4_26` | |
| 468 | `185^3≡179` | `dict_cycle4_185` | |
| 469 | `179^3≡49` | `dict_cycle4_179` | closes cycle 4 |
| 470 | `gcd(p−1,q−1)=2` | `period_gcd_pminus1_qminus1` | match only at `{1,2}` |
| 471 | `5 \| ord(y)` | `primary_five_div_ord` | |
| 472 | `8 \| ord(y)` | `primary_eight_div_ord` | |
| 473 | max-order `3`, `k=5` | `period_three_pohlig_5` | splits |
| 474 | `3^{16}−1` | `period_three_pohlig_16` | splits |
| 475 | `3^8−1` | `period_three_pow8_no_split` | no split |
| 476 | `120+1=p^2` | `srsa_120_plus_1` | |
| 477 | `67−1=66` | `srsa_miller_66` | |
| 478 | four `√1` | `srsa_four_sqrt1` | `{1,−1,67,120}` |
| 479 | `x^{16}≢1` | `residual_x16_not_1` | not order 16 |
| 480 | `x^8≢1` | `residual_x8_not_1` | not order 8 |
| 481 | cbrt `2` in `⟨2⟩` | `dict_cbrt_2_in_ltwo` | leftover other `y` |
| 482 | cbrt `3` in `⟨3⟩` | `dict_cbrt_3_in_lthree` | SAGM |
| 483 | cbrt `36` in `⟨y⟩` | `dict_cbrt_36_in_ly` | this leftover |
| 484 | three `x` for one `k` | `dict_three_x_for_k27` | |
| 485 | `gcd(161−42,N)` | `period_cbrt2_cbrt36_split` | splits |
| 486 | `gcd(75−42,N)` | `period_cbrt3_cbrt36_split` | splits |
| 487 | `gcd(75−161,N)` | `period_cbrt3_cbrt2` | `=1` |
| 488 | `5` has order 80 | `period_five_max_order` | |
| 489 | `5^5−1` | `period_five_pohlig_5` | splits |
| 490 | `5^{16}−1` | `period_five_pohlig_16` | splits |
| 491 | bitlength `λ` | `residual_lam_bitlength` | 7 bits |
| 492 | leftover `x` QR both sides | `residual_x_local_qr` | |
| 493 | `161 mod 8` | `residual_161_mod_8` | |
| 494 | order-16 → Miller | `period_ord16_to_miller` | |
| 495 | leftover `x` not order 16 | `residual_x_not_ord16` | |
| 496 | leftover `x` not order 10 | `residual_x_not_ord10` | |
| 497 | `77`: `2^7≡51` | `period_77_51_is_2_pow7` | |
| 498 | `77` `λ=30` | `period_77_lambda` | |
| 499 | `77`: `2^3−1` | `period_77_two_pow3` | splits `7` |
| 500 | `77`: `2^5−1` | `period_77_two_pow5` | no split |

Count: 100. CAS `138`.

A TM that gcds `x^5−1` after writing the leftover cube **factors**.
A TM that does not gcd **inverts**. Same pin, two programs. Writing
`c^{27}` for public `c∈{2,3,36}` is leftover in three subgroups;
`gcd` of two of those roots factors. Still not `srsa_residual_leaf`
as `Problem_Factor`.
