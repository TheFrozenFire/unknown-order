# Convert — invert-all-units-folds

## 1. Rendering status

SOURCE-MAPPED

This status concerns source mapping only; it is not a validity verdict.

## 2. Frozen source contract

- Headline: an invert-all-units polynomial has Fermat folds
  `X^{d_p}` (mod `p`) and `X^{d_q}` (mod `q`); CRT of those degrees
  recovers `d` (mod `λ`). Writing the invert poly writes the local
  inverse maps, hence `d`. Not
  `residual_solver_constructs_factor_open_named`.
- Pin: `N=11·17=187`, `λ=80`, `e=3`, `p<q`.
- Accepted primitives named in the source: campaign pin, Fermat fold
  / class_sum, `p+q` as the missing `𝔽_q*` sample, geometric kernel
  `K` only as context for leftover (not required for this headline).
- Source: `notes/srsa-cuts.md` (campaign-pin / Fermat-fold paragraph,
  CAS `176`–`186`).
- Conservative transcription: “invert-all-units” means
  `powm (poly_eval P y) e N = y mod N` for every unit `y`.

## 3. Source inventory

| Source ID | Source segment | Role | Placement |
|---|---|---|---|
| SRC-001 | Campaign pins have `p<q`, so every residue of `𝔽_p*` is a unit of `N`. | hypothesis | ⟨1⟩1 |
| SRC-002 | An all-units invert poly matches `X^{d_p}` on that complete sample set, any degree (`invert_all_units_local_p`, CAS `176`). | assertion | ⟨1⟩2 |
| SRC-003 | Fermat fold on `𝔽_p*` is exactly `X^{d_p}` as a polynomial (`invert_all_units_fold_p`, CAS `177`): `p−1` samples, fold degree `< p−1`, no leftover. | assertion | ⟨1⟩3 |
| SRC-004 | Fermat fold on `𝔽_q*` agrees with `X^{d_q}` on the `q−2` samples (`invert_all_units_fold_q_eval`, CAS `179`); functional, not a polynomial identity. | assertion | ⟨2⟩1 |
| SRC-005 | The missing `𝔽_q*` sample is the unit `p+q` (`p+q ≡ p (mod q)`). | witness existence | ⟨2⟩2 |
| SRC-006 | Invert-all-units at that lift fills the missing sample, so `fold_q ≡ X^{d_q}` as polynomials with no extra top-zero hypothesis (`invert_all_units_fold_q`, `invert_all_units_fold_q_classes`, CAS `184`, `185`). | assertion | ⟨2⟩3 |
| SRC-007 | Both Fermat folds are the local inverse monomials, and CRT of those degrees is `d` mod `λ` (`invert_all_units_both_folds_are_local_monomials`, CAS `186`). | conclusion | ⟨1⟩4 |
| SRC-008 | Writing the invert poly wrote the local inverse maps, hence wrote `d`. Not `residual_solver_constructs_factor_open_named`. | honest-closure | ⟨1⟩5 |

## 4. Lamport-style rendering

⟨1⟩1. ASSUME campaign pin (`p<q`) PROVE every residue of `𝔽_p*` is a unit of `N`.
⟨1⟩2. An invert-all-units poly matches `X^{d_p}` on all of `𝔽_p*`.
⟨1⟩3. SUFFICES fold_p ≡ `X^{d_p}` as polynomials mod `p`.
        Proof: `p−1` samples, deg(fold) `< p−1`.
⟨2⟩1. fold_q agrees with `X^{d_q}` on the `q−2` listed samples
        (`𝔽_q* \ {p}`).
⟨2⟩2. PICK `y = p+q` : `y` is a unit of `N` and `y ≡ p (mod q)`.
        Existence: `pin_p_plus_q_coprime` (source supplies the witness).
⟨2⟩3. Invert-all-units at `y` plus ⟨2⟩1 ⇒ fold_q ≡ `X^{d_q}` as
        polynomials (no top-zero hyp).
⟨1⟩4. ⟨1⟩3 and ⟨2⟩3: both folds are the local inverse monomials;
        CRT of the degrees is `d` mod `λ`.
⟨1⟩5. Q.E.D. of the headline. Not the residual-solver open named.

## 5. Source-to-step mapping ledger

| Rendered step / item | Source ID(s) | Mapping kind | Source support | Issue ID | Notes |
|---|---|---|---|---|---|
| ⟨1⟩1 | SRC-001 | DIRECT | EXPLICIT | — | |
| ⟨1⟩2 | SRC-002 | DIRECT | EXPLICIT | — | |
| ⟨1⟩3 | SRC-003 | STRUCTURAL | EXPLICIT | — | SUFFICES from “as a polynomial” |
| ⟨2⟩1 | SRC-004 | DIRECT | EXPLICIT | — | |
| ⟨2⟩2 | SRC-005 | STRUCTURAL | EXPLICIT | — | PICK; existence named |
| ⟨2⟩3 | SRC-006 | DIRECT | EXPLICIT | — | |
| ⟨1⟩4 | SRC-007 | DIRECT | EXPLICIT | — | |
| ⟨1⟩5 | SRC-008 | DIRECT | EXPLICIT | — | |

## 6. Gap and ambiguity register

None that this route depends on. Leftover-kernel span (`K`, CAS
`192`) is a *different* headline, grandfathered.

A `PICK` of the missing `𝔽_q*` sample *without* `p+q` would be
GAP-001. The source supplies the witness; do not re-open it.

## 7. Frozen audit handoff

Forward and reverse inspect this rendering. Do not audit
`SrsaRootPoly.v` as a Lamport proof. Kernel trust of the named
theorem is Print Assumptions Closed.
