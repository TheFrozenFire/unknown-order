# RSA-land — what exists, what this tree owns

The project proves **algebra that people have already found**
in RSA and its close relatives (Rabin, Williams, hidden-order
groups built from an RSA modulus). A construction is in scope
when it has a winning condition, a homomorphism, a CRT identity,
or a named refuse. Protocol, ROM, PPT, and “the hash is random”
stay named.

Companion to `notes/paper-overlaps.md`, `notes/hardness.md`,
`notes/accumulators-zk.md`, `notes/transcript-oracle-plan.md`.

## How to read a row

- **Have** — Rocq name + CAS.
- **Algebra next** — a Closed lemma is missing; the identity is
  classical.
- **Named** — refuse (ROM / PPT / LLL / MPC / hash).
- **Neighbour** — not `(ℤ/Nℤ)*` (Paillier, QR decision, …).

Do not treat “RSA-FDH is EUF-CMA” as a theorem of this corpus.

## 1. Textbook map and trapdoor

| Object | Status |
|---|---|
| `m ↦ m^e`, `c ↦ c^d`, `ed ≡ 1 (mod λ)` | **Have** `RSA.v` |
| `M = ed−1` annihilates units | **Have** |
| `φ = λ · gcd(p−1, q−1)` | **Have** `phi_eq_lambda_times_gcd`; CAS 75 |
| Miller / enum from `(e,d)` | **Have** |
| `(N,e,d)` ⇒ factor | **Have** (not the converse) |
| RSA inverter recovers `m` | **Have** `rsa_inverter_recovers_message` |
| RSA inverter constructs a factor | **Open** `rsa_inverter_constructs_factor_open_named` |
| Decisional RSA on units | vacuous (`rsa_units_are_eth_powers`) |

## 2. Blinding and homomorphism

Chaum 1983. The signer sees `m·r^e`, returns `(m·r^e)^d = m^d·r`.
The user multiplies by `r⁻¹`. No hash in the identity.

| Object | Status |
|---|---|
| Decrypt/sign homomorphism | **Have** `sign_homomorphism`, `decrypt_blinding` |
| Chaum: unblind ∘ sign ∘ blind = raw sign | **Have** `chaum_unblind_is_raw_sign` |
| Product of raw signatures | **Have** T7 |
| Partial-blind / Abe–Fujisaki common info | Named (`Refuse_hash_as_oracle`) |
| RSA-FDH / PSS / PKCS#1 v1.5 *as a scheme* | `Refuse_OAEP_PSS` |

## 3. Threshold and mediated RSA

Additive shares of `d` are the homomorphism again.
Shoup 2000 clears Lagrange denominators by `Δ = ℓ!` and extracts
with Bézout `4Δ²·a + e·b = 1`.

| Object | Status |
|---|---|
| `d = d₁+d₂` ⇒ `m^d = m^{d₁} m^{d₂}` | **Have** `additive_share_combines` |
| Mediated RSA / SEM (`d_u + d_s`) | **Have** (same lemma, two parties) |
| Shoup extract: `y = x^{k d}`, `k a = 1+e t` ⇒ `y^a x^{-t} = x^d` | **Have** `shoup_extract_from_kd` |
| Shamir 2-of-3 in the exponent | **Have** `shamir_two_of_three`; CAS 67 |
| Feldman / Pedersen VSS, complaints, robustness | `Refuse_threshold_robustness` |
| Proactive refresh (add shares of 0) | **Have** `share_refresh_by_zero` |
| Desmedt–Frankel / Gennaro–Jarecki–Krawczyk–Rabin | Same algebra; protocol named |

## 4. Distributed key generation

Boneh–Franklin 1997: parties hold additive shares of candidate
primes; they publish `N = (∑pᵢ)(∑qᵢ)` and run a *biprimality*
test without revealing `p+q` (publishing `p+q` *is* factoring).

| Object | Status |
|---|---|
| `N = (p₁+p₂)(q₁+q₂)` | **Have** `dkg_N_is_product` |
| Published `(N, p+q)` factors | **Have** `FactorEnum` / `sum_from_phi` |
| `#{x : x²≡1 (mod N)} = 2^{ω(N)}` for odd squarefree `N` | **Have** k=2,3 constructed; mixed split; k=3 ≠ k=2 |
| Product of two KeyGen keys, CRT of local `d` | **Have** `carmichael_shared`, `d_star_inverts`, `shared_dec_eq_powm`; CAS 78–80 |
| Arity 3 (triplet of coprime cofactors) | **Have** `carmichael_shared3` |
| Assembled `d*` is toxic (`e d*−1` annihilates `N*`) | **Have** `d_star_annihilates_shared`; CAS 81 |
| Iterated `shared_dec` is `g^{d*^k}` in `(ℤ/N*ℤ)*` | **Have** `dstar_power_crs_is_powm`; not a pairing CRS |
| Public check: next`^e` = previous | **Have** `shared_dec_is_eth_root`, `srs_first_checks`, `srs_step_checks` |
| SRS root of `g` is RSA/sRSA at that `g`; DL of `s₁` is not sRSA | **Have** `srs_first_is_rsa`, `lambda_plus_one_is_other_strong_rsa`, `dlog_of_srs_agrees_mod_order` |
| “`d*` is ZK / like τ in powers-of-tau” | Named (`dstar_is_zk_like_tau_named`, `pot_bilinear_crs_named`; HVZK / ECC refused) |
| Sampled-`τ` string `g^{τ^i}`; contribute multiplies `τ` | **Have** `pot_succ_is_tau_power`, `pot_contribute_multiplies_tau`, `three_contributors_product`; CAS 82 |
| Only `τ⁻¹` walks the new string backward | **Have** `tau_inv_walks_backward`, `backward_walker_is_tau_inv` |
| Honest contribution moves `P_1` | **Have** `honest_contribution_moves_string`, `honest_tau_one_if_coprime` |
| Equal-DL completeness / extract `τ` | **Have** `eqdl_complete`, `eqdl_extracts_tau`; sim named (`pot_hvzk_eqdl_named`) |
| Pairing check of a hidden relation | Named (`pot_bilinear_verify_named`; ECC / pairings refused) |
| Jacobi `(g^k/N)` sees `k` only mod 2 | **Have** `jacobi_sees_only_parity`, `pot_jacobi_tail_constant`; CAS 83 |
| Blum: Jacobi `+1` ⇒ exactly one of `{a,−a}` is QR mod `N` | **Have** `blum_jacobi_one_exactly_one_pm`; this is Cocks's carefully chosen `a` |
| Williams `both_qr` ⇔ `is_qr_N` | **Have** `williams_both_qr_is_qr_N` |
| Shamir at `(2,3)`: square root + cube root ⇒ 6th root | **Have** `sixth_root_from_square_and_cube` |
| Cubic decision vacuous when `e=3` is RSA | **Have** `cubic_decision_vacuous` |
| Cocks decrypt: Jacobi`(c+2s)` = Jacobi`(t)` | **Have** `cocks_decrypt_jacobi`, `cocks_carefully_chosen`; CAS 84 |
| Self-bilinear `e(g^a,g^b)=e(g,g)^{ab}` checks / evaluates the `τ`-string | **Have** `self_bil_checks_pot`, `self_bil_evaluates_pot` (existence is a hyp; iO deferred) |
| Equal-DL / PoK of a contribution `ρ` | **Have** `update_pok_complete`, `extracted_contributor_agrees`; CAS 85 |
| Equal-DL ladder: slot `i` is `i` same-`ρ` steps, `P'_i = P_i^{ρ^i}` | **Have** `ladder_realizes_update`, `contribution_ladder_step`, `slot2_leg1_complete`, `slot2_leg2_complete`; CAS 94 |
| Product of committed evaluations: `g^{f(τ)h(τ)} = C_f^{h(τ)}`; group law adds | **Have** `poly_eval_conv`, `pot_poly_conv_raise`, `monomial_conv_is_later_slot`, `self_bil_committed_product`, `two_wire_commit`; CAS 95 |
| Public quadratic check on encodings + CRS slots (bounded slot search + bilinear combine); not group-mul | **Have** `public_quad_complete`, `public_quad_pin_rejects_group_mul`, `quad_combine_is_product`; CAS 112 |
| Succinct product check: posted proof `13 log2 n + 2` words, not one slot per coefficient | **Have** `succ_proof_len_is_log`, `succ_pin_n2_accepts`, `succ_pin_n2_rejects_group_mul`; CAS 114 |
| QAP: honest witness encodings satisfy `C_{AB}=C_C C_{HZ}`; remainder `1` is a root or annihilator | **Have** `qap_complete_at_tau`, `qap_point_sound`, `pot_wires_is_lincomb`, `pot_wires_app`, `public_quad_qap`; CAS 96, 112 |
| Per-slot coeff PoK: assemble `∏ P_i^{a_i}`; extract `a_i` | **Have** `slots_assemble`, `coeff_slot_eqdl`, `coeff_slot_extracts`; CAS 97 |
| Fiat–Shamir compilation of eqdl / slot Sigma: `c = H(statement, t)`; NI verifier recomputes `c` | **Have** `fs_eqdl_complete`, `fs_slot_complete`, `fs_pin_rejects_wrong_challenge`; CAS 113. ROM/PPT NIZK stays named (`Refuse_NIZK_Fiat_Shamir`) |
| Mul gate `w0·w1=w2` as QAP | **Have** `mul_gate_sat`, `mul_gate_complete`; CAS 98 |
| Same `w` on two CRSs: `C_A · C_B^r = wires(A_j + r B_j)` | **Have** `same_w_check`; CAS 99 |
| Wire PoK: assemble `U_j^{w_j}`; extract `w_j` | **Have** `wire_slots_assemble`, `wire_slot_extracts`; CAS 100 |
| Add gate `w0+w1=w2`; public sum of encodings | **Have** `add_gate_sat`, `add_is_public_sum`; CAS 101 |
| Bit `w∈{0,1}` is `w·w=w` | **Have** `bit_sat`, `bit_complete` |
| Circuit `z = x·y + t` (shared mul wire) | **Have** `prod_add_sat`, `prod_add_complete`, `mul_public_first`; CAS 102 |
| Bit AND/OR/XOR tables and closure | **Have** `bit_and_is_mul`, `bit_or_closed`, `bit_xor_table`; CAS 103 |
| Two-bit `v = b0 + 2 b1`; encoding is public | **Have** `range2_bit_qap`, `range2_encoding`; CAS 104 |
| Mux `s·a+(1−s)·b` on a bit `s` | **Have** `mux_select`, `mux_gates`; CAS 105 |
| Wire equality `w0=w1` as `w0+0=w1` | **Have** `wire_eq_sat`; CAS 106 |
| Bit-sum `b0+2 v_rest`; recursive encoding | **Have** `bit_value_cons_encoding`; CAS 107 |
| Inner product of two pairs | **Have** `inner2_sat`, `inner2_public_sum`; CAS 108 |
| Bit less-than `(1−x)·y` | **Have** `bit_lt_table`, `bit_lt_is_and`; CAS 109 |
| Conditional swap from two muxes | **Have** `cswap_select`, `cswap_involution`; CAS 110 |
| All-bits + 3-bit encoding unfold | **Have** `all_bits_qap`, `three_bit_encoding`; CAS 111 |
| Cubic residue when `3 \| p−1`; `e=3` forbidden iff `3 \| λ` | **Have** `cube_euler_one_direction`, `cube_euler_converse`, `three_divides_lambda_forbids_e3`; CAS 86, 154 |
| Cube mod `N=pq` is CRT of local cubes; `a^{λ/3}≡1` necessary, not sufficient | **Have** `cube_N_iff_both`, `cube_euler_lambda_necessary`, `cube_euler_lambda_not_sufficient_247`, `pin_units_are_cubes`; CAS 155 |
| Cubic character in `μ₃`; kernel `{1,ω,ω²}` locally, CRT on `N`; pin kernel trivial | **Have** `cube_kernel_three`, `mu3_N_iff_locals`, `pin_cube_kernel_trivial`, `mixed_kernel_91`; CAS 156 |
| Eval pairing on `μ_n`, `n=2,3,6` | **Have** `eval_pair_reduce_mod_n`, `omega_cube_is_one`; CAS 87 |
| Alternating bilinear map on cyclic `μ₃` is constant 1 | **Have** `alternating_bilinear_mu3_trivial`, `eval_pair_omega_13_not_alternating`; CAS 157. Non-degenerate pairing of two hidden `μ₃` elements stays `Refuse_elliptic_curve_branch` |
| 2-of-2 root oracle is raise-to-`d*`, not sampled `τ` | **Have** `two_party_next_forces_dstar`; CAS 88 |
| Inversion is public on units and on `Cl`; `x ↦ x^k` is not a pairing | **Have** `rsa_gii_search_empty`, `power_endo_next_forces_k`; CAS 89 |
| Aux self-bilinear evaluates the string if `e(aux,g,g)=g` | **Have** `aux_eval_publishes_next`; CAS 90 (existence a hyp; iO deferred) |
| DARK deg 1–2: `C = π^{s−z} · g^{f(z)}` | **Have** `dark_deg1_open`, `dark_deg2_open`; CAS 91; PoE/VDF named |
| Same `τ`-string on `cl_presentation`; no `λ` trapdoor | **Have** `potP_rsa_is_pot`, `pot_cl_no_lambda`; CAS 92 |
| Jacobi additive pairing; Cocks pair covers Blum | **Have** `jacobi_additive_pairing`, `cocks_pair_covers_blum`; CAS 93 |
| Boneh–Franklin biprimality *protocol* (OT, proofs) | `Refuse_DKG_MPC` |
| Damgård–Mikkelsen / Miller–Rabin DKG | Same refuse; MR engine **Have** |
| Shared `φ` or `λ` from shares of `p+q` | Publishing it factors (above) |

Biprimality as *algebra* is the structure of `(ℤ/Nℤ)*`:
four `√1` for two odd primes, eight for three. A candidate `N`
that admits a mixed triple-root is not an RSA modulus.

## 5. CRT-RSA and implementation maps

| Object | Status |
|---|---|
| `d_p`, `d_q` are one-sided annihilators | **Have** |
| Garner / CRT decrypt equals `c^d` | **Have** `crt_decrypt_eq_rsa_dec` |
| Bellcore CRT-fault | **Have** |
| Quisquater–Couvreur | CRT decrypt (same) |
| Extra Montgomery reduction (Schindler) | Interval/comparison; T18 still open as a predicate |
| Safe-error / Yen faults | Implementation; algebra is Bellcore-shaped |

## 6. Variants of the modulus

| Object | Status |
|---|---|
| Multi-prime `N=pqr`, eight `√1` | **Have** |
| Multi-power / Takagi `N=p²q` | **Have** `carmichael_takagi`, `sqrt1_mod_p2_is_pm1`, `takagi_mixed_sqrt1_splits`, `takagi_ed_is_id_p2`; CAS 72 |
| Safe primes ⇒ `λ=2p'q'` | **Have** `safe_pair_lambda` |
| Rebalanced RSA (short `d_p`, `d_q`) | **Have** CRTRSA |
| Multi-prime RSA (PKCS#1) | Same as multi-prime `√1` + CRT |

## 7. Attacks that are identities (not PPT)

Owned or shaped in `KeyGen`, `SmallExponent`, `TranscriptOracle`.
Franklin–Reiter for `e=3` is the cube-gap identity
`(m+δ)³−m³ = 3δ m(m+δ)+δ³`, not a `Z/NZ[x]` gcd engine.

| Object | Status |
|---|---|
| Fermat, shared prime, Pollard `p−1`, Wiener | **Have** |
| Håstad broadcast, `e=3` small cube | **Have** |
| Franklin–Reiter cube gap | **Have** `fr_cube_gap` |
| Common modulus, Bézout | **Have** |
| Bleichenbacher/Manger interval | T11 engine **Have**; T10 wrap **Have** `bleiche_wrap_interval`; PKCS#1 type-2 is `[2B,3B)` |
| Boneh–Durfee / Coppersmith / ROCA lattice | named |
| NFS | named |

## 8. Signatures and ID from the same map

| Object | Status |
|---|---|
| GQ / FS factoring ID | **Have** |
| Cramer–Shoup 2000 Strong RSA signatures | **Have** `cs_verify_is_rsa`, `cs_same_e_ratio`; hash-to-prime / EUF named |
| Gennaro–Halevi–Rabin | hash-to-prime named; `ChallengePrime` is the other map |
| CL signatures / anonymous credentials | `Refuse_Camenisch_Michels_protocol` |
| Undeniable / designated confirmer / proxy | scheme |

## 9. Time-lock and sequentiality

Rivest–Shamir–Wagner: `x^{2^T}`. The trapdoor is
`2^T mod λ`. Sequentiality is `Refuse_this_is_a_VDF`.

| Object | Status |
|---|---|
| Trapdoor evaluation `a^{2^T} = a^{2^T mod λ}` | **Have** `timelock_trapdoor_reduces_exp` |
| Sequentiality / VDF | named |

## 10. Neighbours (not this carrier)

| Object | Why not here |
|---|---|
| Goldwasser–Micali / QR decision | `e=2` is not a permutation |
| Paillier homomorphism on `(ℤ/N²ℤ)*` | **Have** `one_plus_N_pow`, `paillier_add`; CAS 73. DCR named |
| Damgård–Jurik `s=2` on `N³` | **Have** `one_plus_N_pow_N3`, `dj_add`; CAS 77. Higher `s` is the same binomial |
| Damgård–Jurik `s>2` | Algebra next (one more binomial term per `s`) |
| Okamoto–Uchiyama `L` on `p²` | **Have** `ou_L_of_scaled`, `ou_rand_vanishes`; CAS 76 |
| Naccache–Stern / Benaloh | high residuosity |
| OAEP / RSA-KEM tightness | ROM + PPT |
| Quantum / Shor | out of corpus |

## What “everything in RSA-land” means here

A paper that introduces a new *group*, *share*, *blinding*,
*CRT recombination*, or *winning condition* on an RSA modulus
gets a theorem or a named refuse. A paper that only assumes
Strong RSA / AR and then does ROM games is already covered by
`notes/paper-overlaps.md` and does not get a new file.
