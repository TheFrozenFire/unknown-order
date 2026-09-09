# Transcripts and oracles — bit leakage after the key is used

Companion to `rocq/TranscriptOracle.v`. CAS `57`. Types A–E in
[`keygen-weaknesses.md`](keygen-weaknesses.md) partition handles
from public `(N, e)` alone. This catalog is extra inputs:
ciphertext, signature, decrypt/sign oracle, fault. They do not
add a sixth letter to A–E.

An oracle is a named Gallina function, not a PPT game. Recovering
`m` is restricted inversion, not a key handle, unless the same
answers determine `p` without determining `m`.

## Interfaces

| # | Interface | Adversary is given |
|---|---|---|
| I0 | Transcript only | `(N, e)` and `c = m^e` or `σ = m^d`, no queries |
| I1 | Predicate | adaptive `P(c) ∈ {0,1}` |
| I2 | Partial value | bits of `m` or `d`, or interval membership |
| I3 | Full inverse | adaptive `c ↦ m` or `m ↦ σ` on a named domain |
| I4 | Fault | incorrect CRT signature / skipped multiply |
| I5 | Related algebraic | several transcripts with a known polynomial or multiplicative relation |

I3 on raw units *is* the RSA problem. I1 is the interesting default:
one bit per query, multiplicativity `P(c · α^e) = P(α · m)`.

## Owned algebra

| Row | Type | Rocq / status |
|---|---|---|
| T1 | stereotyped / small `m` | Type E shape (`SmallExponent`) |
| T2 | Håstad broadcast | `hastad_cube_if_small` |
| T3 | Franklin–Reiter related `m` | `related_message_common_root`; poly gcd over `ℤ/Nℤ` named |
| T4 | common modulus, coprime `e₁, e₂` | Bézout on ciphertexts; message recovery, not a key handle |
| T5 | Jacobi of ciphertext | `(c/N)=(m/N)` for odd `e`; public, no query |
| T7 | product of raw signatures | `sign_hom_3`, `sign_weighted_product` |
| T8 | PKCS#1 v1.5 / `e=3` signature forgery | Type E on the padded integer; hash named |
| T10–T13 | padding / MSB / LSB predicates | recover `m` by interval / doubling; not `p` |
| T12 | LSB of `m` | ACGS-shaped; hardness slogan refused |
| T16 | QR-mod-`p` bit given `(m/N)` | is `(m/q)`; RW-adjacent relation |
| T18 | extra Montgomery reduction | comparison predicate; timer out |
| T21 | bits of `d` or `p` | `BitLeak` shape; Coppersmith named |
| T24 | textbook sign homomorphism | forge any `m` from raw signatures |
| T25 | Chaum blinding | CCA on raw RSA; companion to T24 |
| T27 | Rabin invert of a random square | `rabin_oracle_nonassociate_factors` |
| T29 | Bellcore CRT-faulty signature | `bellcore_factors`; one-sided mixed root |
| K1 | predicate on one CRT side | `one_sided_congruence_factors`; not a function of recombined `m` |

Coron–May / Miller-from-`(e,d)` is knowledge of `(e,d)`, not
I3 ⇒ factor for RSA. That converse is
`rsa_inverter_extracts_factor_open_named`.

Implementation bugs (OpenSSL padding, microarch) are listed only
so their algebraic core can be named. Do not model a TLS stack.
