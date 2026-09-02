# Named skips

A `Definition foo_named` is first-class Rocq.  **Unused** means
refuse (nothing depends on it).  **Used** means a consumer is
weaker by exactly that hypothesis.  `Definition foo_open_named`
is a live algebraic target: unused means *unproved*, not banned.
`NamedRefuse` constructors are out of model (ROM, PPT, NFS) —
not a ban on proving a nearby Gallina reduction.

Generated.  Do not edit by hand.

## `*_named` propositions

| Name | File | Line | Status | Used at |
|---|---|---:|---|---|
| `strong_rsa_solver_constructs_factor_open_named` | `Hardness.v` | 78 | open | — |
| `residual_solver_constructs_factor_open_named` | `StrongRSAPeel.v` | 273 | open | — |
| `rsa_inverter_constructs_factor_open_named` | `TranscriptOracle.v` | 587 | open | — |
| `compose_preserves_disc_named` | `BinForms.v` | 677 | refuse | — |
| `compose_assoc_named` | `BinForms.v` | 803 | refuse | — |
| `compose_left_compat_named` | `BinForms.v` | 812 | refuse | — |
| `cocks_hash_named` | `Cocks.v` | 30 | refuse | — |
| `cocks_ind_id_cpa_named` | `Cocks.v` | 33 | refuse | — |
| `eval_pair_needs_integer_named` | `EvalPairing.v` | 211 | refuse | — |
| `coppersmith_named` | `Lattice.v` | 67 | refuse | — |
| `dirichlet_ap_prime_named` | `NamedSkips.v` | 73 | refuse | — |
| `orders_generate_lambda_named` | `Order.v` | 241 | refuse | — |
| `pot_bilinear_verify_named` | `PowersOfTau.v` | 36 | refuse | — |
| `pot_hvzk_eqdl_named` | `PowersOfTau.v` | 41 | refuse | — |
| `pratt_complete_named` | `Pratt.v` | 110 | refuse | — |
| `dstar_is_zk_like_tau_named` | `SharedKey.v` | 638 | refuse | — |
| `pot_bilinear_crs_named` | `SharedKey.v` | 643 | refuse | — |
| `boneh_durfee_named` | `Wiener.v` | 158 | refuse | — |

## `NamedRefuse` constructors

| Constructor | File | Line |
|---|---|---:|
| `Refuse_ROM` | `NamedSkips.v` | 41 |
| `Refuse_SHA_in_Rocq` | `NamedSkips.v` | 42 |
| `Refuse_PPT_advantage` | `NamedSkips.v` | 43 |
| `Refuse_NFS_cost` | `NamedSkips.v` | 44 |
| `Refuse_RSA_eq_factoring_standard_model` | `NamedSkips.v` | 45 |
| `Refuse_AM09_generic_ring_as_standard_model` | `NamedSkips.v` | 46 |
| `Refuse_BP97_vs_modern_sRSA` | `NamedSkips.v` | 47 |
| `Refuse_undirected_611_hunt` | `NamedSkips.v` | 48 |
| `Refuse_elliptic_curve_branch` | `NamedSkips.v` | 49 |
| `Refuse_lattice_lll_development` | `NamedSkips.v` | 50 |
| `Refuse_FO_DF_simulation` | `NamedSkips.v` | 51 |
| `Refuse_pairing_accumulators` | `NamedSkips.v` | 52 |
| `Refuse_this_is_a_VDF` | `NamedSkips.v` | 53 |
| `Refuse_HVZK_simulation` | `NamedSkips.v` | 54 |
| `Refuse_PRF_stretch` | `NamedSkips.v` | 55 |
| `Refuse_hash_as_oracle` | `NamedSkips.v` | 56 |
| `Refuse_NIZK_Fiat_Shamir` | `NamedSkips.v` | 57 |
| `Refuse_Camenisch_Michels_protocol` | `NamedSkips.v` | 58 |
| `Refuse_Mollin_general_2020_1310` | `NamedSkips.v` | 59 |
| `Refuse_r_power_hardness` | `NamedSkips.v` | 60 |
| `Refuse_polynomial_gcd_over_ZN` | `NamedSkips.v` | 61 |
| `Refuse_RW_signature_scheme` | `NamedSkips.v` | 62 |
| `Refuse_EN_card_from_N` | `NamedSkips.v` | 63 |
| `Refuse_Redei_4rank_fund_minus4N` | `NamedSkips.v` | 64 |
| `Refuse_UO_GGM` | `NamedSkips.v` | 65 |
| `Refuse_DKG_MPC` | `NamedSkips.v` | 66 |
| `Refuse_threshold_robustness` | `NamedSkips.v` | 67 |
| `Refuse_OAEP_PSS` | `NamedSkips.v` | 68 |

_43 refuses, 3 open targets, 0 used-as-hypothesis weaknesses._
