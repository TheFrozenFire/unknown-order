# Named skips

A `Definition foo_named` is first-class Rocq.  **Unused** means
refuse (nothing depends on it).  **Used** means a consumer is
weaker by exactly that hypothesis.  `NamedRefuse` constructors
are refuses that are not even propositions (ROM, PPT, NFS).

Generated.  Do not edit by hand.

## `*_named` propositions

| Name | File | Line | Status | Used at |
|---|---|---:|---|---|
| `compose_preserves_disc_named` | `BinForms.v` | 677 | refuse | — |
| `compose_assoc_named` | `BinForms.v` | 803 | refuse | — |
| `compose_left_compat_named` | `BinForms.v` | 812 | refuse | — |
| `coppersmith_named` | `Lattice.v` | 67 | refuse | — |
| `dirichlet_ap_prime_named` | `NamedSkips.v` | 55 | refuse | — |
| `orders_generate_lambda_named` | `Order.v` | 241 | refuse | — |
| `pratt_complete_named` | `Pratt.v` | 110 | refuse | — |
| `boneh_durfee_named` | `Wiener.v` | 158 | refuse | — |

## `NamedRefuse` constructors

| Constructor | File | Line |
|---|---|---:|
| `Refuse_ROM` | `NamedSkips.v` | 29 |
| `Refuse_SHA_in_Rocq` | `NamedSkips.v` | 30 |
| `Refuse_PPT_advantage` | `NamedSkips.v` | 31 |
| `Refuse_NFS_cost` | `NamedSkips.v` | 32 |
| `Refuse_RSA_eq_factoring_standard_model` | `NamedSkips.v` | 33 |
| `Refuse_AM09_generic_ring_as_standard_model` | `NamedSkips.v` | 34 |
| `Refuse_BP97_vs_modern_sRSA` | `NamedSkips.v` | 35 |
| `Refuse_undirected_611_hunt` | `NamedSkips.v` | 36 |
| `Refuse_elliptic_curve_branch` | `NamedSkips.v` | 37 |
| `Refuse_lattice_lll_development` | `NamedSkips.v` | 38 |
| `Refuse_FO_DF_simulation` | `NamedSkips.v` | 39 |
| `Refuse_pairing_accumulators` | `NamedSkips.v` | 40 |
| `Refuse_this_is_a_VDF` | `NamedSkips.v` | 41 |
| `Refuse_HVZK_simulation` | `NamedSkips.v` | 42 |
| `Refuse_PRF_stretch` | `NamedSkips.v` | 43 |
| `Refuse_hash_as_oracle` | `NamedSkips.v` | 44 |
| `Refuse_NIZK_Fiat_Shamir` | `NamedSkips.v` | 45 |
| `Refuse_Camenisch_Michels_protocol` | `NamedSkips.v` | 46 |
| `Refuse_Mollin_general_2020_1310` | `NamedSkips.v` | 47 |
| `Refuse_r_power_hardness` | `NamedSkips.v` | 48 |
| `Refuse_polynomial_gcd_over_ZN` | `NamedSkips.v` | 49 |
| `Refuse_RW_signature_scheme` | `NamedSkips.v` | 50 |

_30 refuses, 0 used-as-hypothesis weaknesses._
