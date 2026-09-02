# Strong RSA cuts — by question, not by batch

The numbered IDs (`hun_01`…`hun_500`, `dozen_*`, `shape_*`, `filter_*`,
`arith_*`, peel lemmas) stay. Those files are the **roster**. This
file is the **map**: the same identities grouped by *what is
restricted* and *what fate that restriction has*.

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
(`whole()`). Numbered `01`–`138` stay. Sequential rosters:
`notes/hundred.md` … `notes/hundred5.md`.

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

Four `√1`: `{1,−1,67,120}` (`hun_478`). Mixed `67` and `120` split
(`hun_429`, `hun_477`). `−1` does not (`hun_430`).

## 2. What leftover `(x,e)` is allowed to be

Output language of the residual pair on this pin. A solver that
writes outside this set is not residual.

**Subgroup.** `x ∈ ⟨y⟩` and **generates** it (`ord=40`). There are
`φ(40)=16` such elements. Residual `x` is not an order-16 2-Sylow
generator (`v₂(ord x)=3 < v₂(λ)=4`). Index `[units:⟨y⟩]=4`: three
cosets are forbidden. All 16 generators are Jacobi `+1`.

| Claim | IDs |
|---|---|
| `x^{40}≡1`, generates | `hun_201`, `hun_202`, `hun_385`, `hun_435` |
| `x=y^{27}`, `gcd(27,40)=1` | `hun_203`, `hun_271` |
| 16 generators | `hun_221`, `hun_313` |
| unique unit cube of `36` is `42` | `shape_unique_unit_cube_root_of_36`, `hun_205` |
| unique unit cube of `1` is `{1}` among `{±1}`-adjacent | `hun_204` |
| `e` invertible mod `16` and mod `5` | `hun_206`, `hun_207`, `hun_263`, `hun_264` |
| CRT of `e^{-1}` is `27` | `hun_208` |
| `5 \| e` shares `λ` | `hun_209` |
| local CRT `42≡9 (mod 11)≡8 (mod 17)` | `hun_214`–`hun_216`, `hun_281`, `shape_crt_*` |
| Jacobi / QR both sides | `hun_210`, `hun_211`, `hun_420`, `hun_492` |
| not in `⟨2⟩`, not order 16 or 10 | `hun_212`, `hun_425`, `hun_495`, `hun_496` |
| generates the 5-Sylow | `hun_438`, `hun_440` |

**`⟨y⟩ ≅ C₈ × C₅`.** `y^5=100` generates `C₈`; `y^8=137` generates
`C₅`. Cubing is bijective on both. `y` reconstructs as `155·69`.
The order-2 of `C₈` is Miller `67`.

IDs: `hun_223`–`hun_228`, `hun_321`–`hun_340`, `hun_386`–`hun_389`,
`hun_407`–`hun_409`.

**Dictionary.** Each generator is leftover `x` for **two** residual
`e` (`e` and `e+40`). `φ(80)/φ(40)=2`. Cubing is an automorphism of
`⟨y⟩` of order 4 in `(ℤ/40ℤ)*`, hence **four 4-cycles** on the 16
generators. Residual `x` sits on the cycle `70→42→36→93→70`.

IDs: `hun_301`–`hun_320`, `hun_361`–`hun_370`, `hun_411`–`hun_419`,
`hun_460`–`hun_469`.

**SAGM on the challenge.** Residual cube is `(a,e)=(27,3)` on base
`y`: `ae−1=λ`. Knowing `ord(y)` substitutes for knowing `λ` *for
this inversion*. Trapdoor `d=27` inverts **every** unit; `k=27` on
a public base inverts only in that cyclic.

IDs: `hun_128`, `hun_273`, `hun_354`/`hun_356`/`hun_382`–`hun_384`,
`hun_450`–`hun_452`, `hun_481`–`hun_484`.

## 3. Two programs on one pin — gcd vs multiply

The same exponents, two TMs.

| TM | Identity | Fate |
|---|---|---|
| `gcd(y^k−1,N)` for `k ∈ {5,8,10}` | `hun_241`–`hun_243`, `hun_351`, `hun_378`–`hun_379` | **splits** |
| `y^k ≡ 1` equality, no gcd | `hun_353`–`hun_355`, `hun_374`–`hun_377` | finds `ord=40`, **no split** |
| then `x=y^{27}` | `hun_352`, `hun_381`, `hun_399` | **leftover invert** |
| `gcd(y^{40}−1,N)` | `hun_248`, `hun_380` | `=N`, no proper factor |
| `gcd(x^k−1,N)` on leftover `x` | `hun_401`–`hun_404`, `hun_410` | **same split** — leftover `x` is a Pohlig oracle |

`gcd(p−1,q−1)=2`, so matching local orders exist only at `{1,2}`.
Any unit of order `>2` is a period leak (order 16 via `g^8−1`,
order 4 via `g^2−1`, max-order via `g^5−1` and `g^{16}−1`).
IDs: `hun_250`, `hun_299`–`hun_300`, `hun_330`, `hun_390`–`hun_393`,
`hun_421`–`hun_427`, `hun_470`–`hun_475`, `hun_488`–`hun_490`.

One `k=27` in three subgroups: cube roots of `2`, `3`, `36`.
`gcd(161−42,N)=17`, `gcd(75−42,N)=11`. IDs: `hun_458`, `hun_485`–`hun_487`.

Safeprime `N=77` is the same dichotomy with `{3,5}` instead of `{5,8}`:
`hun_441`–`hun_444`, `hun_497`–`hun_500`.

## 4. How the TM writes `x`

Public `X(N,y)`. Fate is inhabit / one-sided split / leftover by pin
accident.

**Does not invert** (and does not split): associate, midpoint, half,
`y±1` as `x`, Gray, popcount, Lucas, `⌊y/3⌋`, `⌊N/y⌋`, pad, Newton,
CF, `x=φ`, bitlength, `x=N−1`, `x=⌊√N⌋`, `x=2y` (`arith_double_y`).
IDs include `hun_02`, `hun_03`, `hun_19`, `hun_22`, `hun_104`–`hun_111`,
`hun_115`–`hun_119`, `hun_172`–`hun_175`, `hun_180`, `hun_283`,
`filter_neg_y`, `arith_newton_*`, `arith_cf_*`.

**One-sided cube / non-unit `x` splits:** the map is not a global root,
but `gcd(x^3−y,N)` or `gcd(x,N)` is proper. IDs: `hun_01`, `hun_20`,
`hun_23`, `hun_24`, `hun_27`, `hun_28`, `hun_101`, `hun_103`, `hun_106`,
`hun_112`, `hun_117`, `hun_222`, `hun_226`, `hun_230`, `filter_onesided_*`,
`hun_30` (mismatched CRT).

**Leftover by a public formula that lands in `⟨y⟩`:** `x=y^N` (`N≡d
(mod 40)`), Catalan `C_5`, `p(10)`, integer `√y` then `n(n+1)`,
`x=y^{e^{-1} mod 40}`. IDs: `hun_15`, `hun_114`, `hun_120`, `hun_271`,
`hun_284`, `hun_342`. Pin geometry, not a general solver.

**Monomial / inverse / affine as *algorithm class* (how `x` is
written, including leftover-shaped inverses):** `shape_monomial_*`,
`shape_inverse_*`, `shape_affine_*`, `hun_13`, `hun_14`, `hun_16`,
`hun_17`, `hun_236`, `hun_280`.

## 5. How the TM writes `e`

Public `E(N,y)`.

**Even `e` peels** (square-root case): `φ(y)`, Hamming, `λ(y)`,
bitlength, rad, `ω`, `Ω`, smooth `30`, `ψ(y)`, `ord(y)`, `φ(N)`,
`N±1`, primorial. IDs: `hun_04`, `hun_05`, `hun_33`–`hun_39`,
`hun_50`, `hun_125`–`hun_127`, `hun_131`, `hun_132`, `hun_137`.

**Shares `λ` (not residual):** `e=25`, `e=5`, `e=y−1=35`, aliquot
`55`, `e=N−2`. IDs: `hun_11`, `hun_43`, `hun_46`, `hun_96`, `hun_121`,
`hun_129`, `hun_138`, `arith_composite_e15`.

**Leftover-shaped odd `e` coprime to `λ`:** inverts in `⟨y⟩` for a
named `x`. IDs: `hun_35`–`hun_36`, `hun_47`–`hun_49`, `hun_122`–`hun_124`,
`hun_130`, `hun_133`–`hun_136`, `hun_139`, `hun_163`–`hun_167`,
`hun_177`, `hun_293`, `hun_301`–`hun_308`, `filter_lowbit_e9`,
`arith_nextprime_e37`, `arith_e7_residual`.

**Public filter `gcd(e,N−1)=1` rejects the cube** (`gcd(3,186)=3`):
`filter_cube_fails_public_e`. Wrong-Euler inverse mod `N−1`:
`shape_wrong_euler_inv`.

## 6. Extra tapes and related challenges

The TM may emit more than `(x,e)`, or see several `y`.

| Extra / query | Fate | IDs |
|---|---|---|
| `φ` or `p+q` | factors | `filter_phi_*`, `hun_52`, `hun_141` |
| `d` with `ed≡1 (mod λ)` | Miller | `shape_ed_*`, `hun_51`, `hun_286`–`hun_289` |
| local `d_p`, `d_q` | one-sided annihilator | `hun_51`, `dozen_e11_minus1_shares_lambda` |
| `ord(g)=λ` | trapdoor | `hun_54` |
| factor `e−1` / `N−1` | Miller / public | `hun_55`, `hun_56` |
| two leftovers `gcd(x_i−x_j,N)` | `42,60` no split; `42,25` splits | `hun_68`, `hun_176`, `hun_232`–`hun_234` |
| Shamir coprime `e` | product, not a factor | `hun_06`, `hun_71`, `hun_294`, `dozen_related_*` |
| `y` and `y^{-1}` | inverse of root | `hun_63` |
| fixed-`e` rerand | leftover for a different `y` | `srsa_fixed_e_rerand`, `hun_297`, `shape_chaum_*` |
| CRT of local roots | needs `{p,q}` | `shape_crt_moduli_are_factors`, `hun_281` |
| two coprime moduli | no split | `hun_70`, `arith_two_moduli_*` |
| advice `N/17` | splits | `dozen_advice_div_splits`, `prep_then_gra_factors` |

## 7. Engines that do not look at `y`

Named factoring algorithms as “solvers.” They split this pin because
`N` is tiny or `p−1` is smooth, not because they inverted `y`.

Pollard `p−1` (`hun_75`, `hun_181`), rho (`hun_76`, `hun_182`), Fermat /
Hart (`hun_78`, `hun_185`–`hun_186`), trial (`hun_79`, `hun_187`),
Williams `p+1` (`hun_80`; `P=3` does not, `hun_183`), Fibonacci gcd
(`hun_168`, `hun_188`), Mersenne `2^8−1` (`hun_170`, `hun_189`),
index-as-prime `N−1` does not (`hun_81`). BSGS treating `N` as prime
is the wrong order (`hun_77`, `hun_190`, `hun_261`).

## 8. The sentence is a different group or modulus

Paillier `N²` (`hun_07`), DJ `N³` (`hun_86`), OU/Takagi `p²q`
(`hun_85`, `arith_takagi_*`), prime `N` (`hun_94`), prime-power
(`hun_88`, `hun_196`), triprime (`hun_93`, `arith_mixed_pqr_*`),
two safeprimes (`hun_89`), `N=55,119,209,221,323` (`hun_191`–`hun_195`),
Williams torus `V_e` (`hun_08`), Cocks Jacobi (`hun_87`). Not the
semiprime cube.

## 9. Restricted algebraic machines

Not standard-model hardness. GRA / SLP / Jacobi: `GenericRing.v`,
`BrownSLP.v`, CAS `115`–`120`. GGM: `GenericGroup.v`, CAS `121`–`122`.
SAGM as the *only* writing of `x`: `SolverRestrict.v`, CAS `128`.
JNT affine integer cubes: `JouxNaccacheThome.v`. Prep-GRA with
advice `N/17`: `PreprocessGRA.v`.

## 10. Stable IDs (roster → file → CAS)

| IDs | Rocq | CAS | Notes roster |
|---|---|---|---|
| peel | `StrongRSAPeel.v` | `127` | hardness peel table |
| SAGM / safeprime / poly `e` | `SolverRestrict.v` | `128` | |
| dozen 1–12 | `DozenInroads.v` | `129` | |
| solver shapes 1–12 | `SolverShape.v` | `130` | |
| filter 1–12 | `FilterShape.v` | `131` | |
| arith 1–12 | `ArithShape.v` | `132` | |
| `hun_01`–`hun_100` | `HundredA`–`HundredFH` | `133` | `hundred.md` |
| `whole()` | — | `134` | first hundred ∧ peel ∧ residual |
| `hun_101`–`hun_200` | `HundredI`–`HundredM` | `135` | `hundred2.md` |
| `hun_201`–`hun_300` | `HundredN`–`HundredR` | `136` | `hundred3.md` |
| `hun_301`–`hun_400` | `HundredS`–`HundredW` | `137` | `hundred4.md` |
| `hun_401`–`hun_500` | `HundredX`–`HundredAB` | `138` | `hundred5.md` |

Verbose residues: `cas/verbose_dump.gp` (not globbed).
