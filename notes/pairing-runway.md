# Pairing runway — exploration areas

Companion to the sampled-`τ` SRS (`PowersOfTau.v`, CAS 82) and
QR / Cocks / Jacobi (`QRModN.v`, `Cocks.v`, CAS 83–84).

Goal: a check of consecutive CRS powers that does not publish `τ`.
A pairing that multiplies two hidden exponents and lands in a
*large* group would do that. Jacobi does the first and fails the
second. This file is the retained map of what to try next.

Constraints unchanged: no SHA/ROM/PPT as theorems, no ECC pairing
branch, no CLT/GGH development, iO deferred not refused, PARI the
gated CAS.

## Already closed (do not redo)

| Fact | Rocq |
|---|---|
| Sampled `τ`; contribute multiplies; walker is `τ⁻¹` | `pot_succ_is_tau_power`, `pot_contribute_multiplies_tau`, `backward_walker_is_tau_inv` |
| Equal-DL completeness / extract | `eqdl_complete`, `eqdl_extracts_tau` |
| Jacobi sees only parity; `τ`-tail constant | `jacobi_sees_only_parity`, `pot_jacobi_tail_constant` |
| Blum Jacobi `+1` ⇒ exactly one of `{a,−a}` is QR | `blum_jacobi_one_exactly_one_pm`, `cocks_carefully_chosen` |
| Williams `both_qr` ⇔ `is_qr_N` | `williams_both_qr_is_qr_N` |
| Cocks `t + a t⁻¹` decrypts a Jacobi bit | `cocks_decrypt_jacobi` |
| Self-bilinear spec: checks / evaluates the string | `self_bil_checks_pot`, `self_bil_evaluates_pot` |
| Square + cube root ⇒ 6th root | `sixth_root_from_square_and_cube` |
| Cubic *decision* vacuous when `e=3` is RSA | `cubic_decision_vacuous` |

## Areas (keep this roster)

Order inside a band is the recommended attack order. Skip a row
only with a written death in this file.

### Public pairing (grow the target)

1. **Higher residue symbols, especially when `3 | λ`.** *(this sitting)*
   Jacobi is `n=2`. The cubic character is vacuous when cubing
   is a permutation. It is 3-to-1 when `3` divides `λ`. **Have**
   `cube_euler_one_direction`, `cubing_invertible_on_units`,
   `three_divides_lambda_forbids_e3`; CAS 86. Converse
   (Euler `=1` ⇒ cube) still open; needs a primitive root or
   a Blum-style extractor.

2. **Evaluation pairing on `μ_n` for `n=2,3,4,6`.** *(this sitting)*
   **Have** `eval_pair_reduce_mod_n`, `eval_pair_mu2_on_mixed`,
   `omega_cube_is_one`, `eval_pair_mu3`, `mu2_is_mu6`,
   `eval_pair_mu6`; CAS 87. Target order divides `n` (at most 6).
   One argument is an integer in the clear.

3. **Endomorphisms / infeasible inversion.** *(this sitting)*
   **Have** `rsa_gii_search_empty`, `power_endo_hom`,
   `power_endo_next_forces_k`; CAS 89. Inversion is Bézout /
   `bqf_inv`. Using `x ↦ x^k` as “next CRS power” forces
   `k ≡ τ`. Isogenies stay `Refuse_elliptic_curve_branch`.

4. **Self-bilinear with auxiliary information, algebra only.** *(this sitting)*
   **Have** `aux_self_bil_checks_pot`, `aux_eval_publishes_next`;
   CAS 90. Freezing `aux` recovers `self_bilinear`. If
   `e(aux,g,g) = g`, the map computes `P_{i+1}` — too strong
   to publish. iO stays deferred. Committed evaluations:
   `g^{f(τ)h(τ)} = C_f^{h(τ)} = C_{f·h}`; group law adds.
   Monomials already sit in the CRS (`P_{i+j} = g^{τ^i τ^j}`).
   **Have** `poly_eval_conv`, `pot_poly_conv_raise`,
   `monomial_conv_is_later_slot`, `self_bil_committed_product`,
   `two_wire_commit`; CAS 95. QAP completeness:
   honest `A_w B_w − C_w = H Z` gives `C_{AB} = C_C · C_{HZ}`;
   remainder encoding `1` means `τ` is a root or the order
   divides. **Have** `qap_complete_at_tau`, `qap_point_sound`,
   `pot_wires_is_lincomb`, `pot_wires_app`; CAS 96.
   Coefficient PoK (`slots_assemble`, `coeff_slot_extracts`; CAS 97),
   one mul gate (`mul_gate_complete`; CAS 98), same-`w` check
   (`same_w_check`; CAS 99).
   Wire PoK (`wire_slot_extracts`; CAS 100), addition
   (`add_gate_complete`; CAS 101), bits (`bit_complete`).

### Checkable SRS, pairing optional

5. **Equal-DL transcript as the public check.** *(this sitting)*
   Completeness and extraction are theorems. A ceremony is:
   each contributor publishes updated powers plus an extractable
   equal-DL proof of the contribution `ρ`. **Have**
   `update_first_is_old_first_to_rho`, `update_pok_complete`,
   `extracted_contributor_agrees`; CAS 85. Extra slots: an
   `i`-step same-`ρ` ladder on base `P_i` gives `P'_i = P_i^{ρ^i}`.
   **Have** `ladder_realizes_update`, `contribution_ladder_step`,
   `slot2_leg1_complete`, `slot2_leg2_complete`; CAS 94.

6. **2-of-2 pairing oracle from the old shared trapdoor.** *(this sitting)*
   **Have** `two_party_root_is_eth`, `two_party_root_hom`,
   `two_party_next_forces_dstar`; CAS 88. The oracle raises to
   `d*`. Using it as “next CRS power” forces `τ ≡ d*` — the old
   public-`e` string. It is not a pairing of two group elements.

7. **DARK-style commitments in unknown order.** *(this sitting)*
   **Have** `dark_deg1_open`, `dark_deg2_open`; CAS 91.
   `C = π^{s−z} · g^{f(z)}` is an exponent identity.
   Checking it without the integer `s` is a pairing or a
   PoE (`Refuse_this_is_a_VDF`). Sequentiality is not a theorem.

8. **The same `τ`-string in `Cl(Δ)`.** *(this sitting)*
   **Have** `potP_rsa_is_pot`, `potP_cl_at_zero`,
   `pot_cl_no_lambda`, `pot_cl_contribute_slot0`; CAS 92.
   Toxic waste is only `τ`. Public annihilator is `Some 2`.
   General Cl contribute needs `compose_assoc_named` (not taken).

### Finish what QR/Cocks opened

9. **Cubic residuosity as a decision problem only when it is
   not a permutation.** Companion to QR-mod-`N`. Folded into
   area 1.

10. **Obstruction theorem.** *(this sitting)*
    `jacobi_sees_only_parity` / `pot_jacobi_tail_constant` are
    the theorem: Jacobi of any CRS word is a function of
    exponent parities. Target `{±1}`. **Have**
    `jacobi_additive_pairing`; CAS 93.

11. **Cocks / Boneh–Gentry–Hamburg identities only.** *(this sitting)*
    **Have** `jacobi_additive_pairing`, `jacobi_neg1_on_blum`,
    `cocks_pair_covers_blum`; CAS 93. 1-bit pairing catalog,
    not a CRS check.

## Attack order this sitting

5, then 1+9, then 10. After those three: 2 if torsion is cheap,
else 6 if we want an interactive substitute.
