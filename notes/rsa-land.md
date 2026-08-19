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
| RSA inverter recovers `m`, does not factor | **Have** `rsa_inverter_recovers_message`; refuse converse |
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
| “`d*` is ZK / like τ in powers-of-tau” | Named (`dstar_is_zk_like_tau_named`, `pot_bilinear_crs_named`; HVZK / ECC refused) |
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
