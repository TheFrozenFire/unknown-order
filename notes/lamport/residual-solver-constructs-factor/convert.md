# Convert — residual-solver-constructs-factor

## 1. Rendering status

SOURCE-MAPPED

This status concerns source mapping only; it is not a validity verdict.

The notes state the headline as a live unproved target and postpone
it. That postponement is mapped, not repaired.

## 2. Frozen source contract

- Headline: a residual solver (every unit `y`) constructs a factor of `N`.
- Theorem as the source would have it:

  ```
  forall (R : RSAInstance) (Solve : residual_solver (rsa_N R) (rsa_lambda R)),
    exists f, Problem_Factor (rsa_N R) f.
  ```

  That is exactly `residual_solver_constructs_factor_open_named`
  (`StrongRSAPeel.v`).
- Hypotheses / definitions in scope: `RSAInstance`, `srsa_residual_leaf`
  (odd `e`, `gcd(e,λ)=1`, `λ ∤ e−1`, units, `x^e ≡ y`),
  `residual_solver` (a leftover pair for every unit `y`).
- Accepted primitives: those definitions. Not accepted: PPT, ROM,
  NFS, GRA/GGM/SAGM as standard-model hardness, cyclicity as a hyp.
- Source text: `notes/srsa-cuts.md` §0 (“The residual leaf (live
  target)”) and the closing sentence of the fold paragraph
  (“Writing the invert poly wrote the local inverse maps, hence
  wrote `d`. Not `residual_solver_constructs_factor_open_named`.”).
- Conservative transcription: none.

## 3. Source inventory

| Source ID | Source segment | Role | Placement |
|---|---|---|---|
| SRC-001 | Residual means `srsa_residual_leaf` — odd `e`, `gcd(e,λ)=1`, `λ∤ e−1`, units, `x^e≡y`. | definition | ⟨1⟩1 |
| SRC-002 | Cuts of the writer classify which TMs inhabit that leaf, split, peel, or miss. They do not settle whether a residual *solver* constructs a factor. | admission | ⟨1⟩2, ADM-001 |
| SRC-003 | Whether a residual *solver* (every unit `y`) constructs a factor is `residual_solver_constructs_factor_open_named` — unproved, on-goal. | admission of the headline | ⟨1⟩3, ADM-001 |
| SRC-004 | Invert from `ord(y)` always inhabits the leaf. A leftover pair factors `N` only under KeyGen mismatch. | nearby classification, not the headline | ⟨1⟩4 |
| SRC-005 | Writing the invert poly wrote the local inverse maps, hence wrote `d`. Not the open named. | explicit non-discharge | ⟨1⟩5 |

## 4. Lamport-style rendering

⟨1⟩1. DEFINE residual leaf ≜ `srsa_residual_leaf`
        (odd `e`, `gcd(e,λ)=1`, `λ ∤ e−1`, units, `x^e ≡ y`).
⟨1⟩2. DEFINE residual solver ≜ a leftover pair for every unit `y`.
⟨1⟩3. A residual solver constructs a factor of `N`.
        Proof: ADMITTED — ADM-001; source names
        `residual_solver_constructs_factor_open_named` and says
        unproved, on-goal. No route is supplied.
⟨1⟩4. A leftover pair for one `y` is not a factor
        (KeyGen mismatch / `matching_247_*`).
⟨1⟩5. An invert-all-units polynomial writes local inverse maps
        (hence `d`). That is a different sentence.
        Q.E.D. of ⟨1⟩3 is not claimed.

## 5. Source-to-step mapping ledger

| Rendered step / item | Source ID(s) | Mapping kind | Source support | Issue ID | Notes |
|---|---|---|---|---|---|
| ⟨1⟩1 | SRC-001 | DIRECT | EXPLICIT | — | |
| ⟨1⟩2 | SRC-003 | NORMALIZED | EXPLICIT | — | `residual_solver` type |
| ⟨1⟩3 | SRC-002, SRC-003 | OBLIGATION | ADMITTED | ADM-001 | headline |
| ⟨1⟩4 | SRC-004 | DIRECT | EXPLICIT | — | does not discharge ⟨1⟩3 |
| ⟨1⟩5 | SRC-005 | DIRECT | EXPLICIT | — | too-strong warning for the fold route |
| ADM-001 | SRC-002, SRC-003 | OBLIGATION | ADMITTED | ADM-001 | |

## 6. Gap and ambiguity register

- **ADM-001** — exact missing proposition: a Gallina function from
  `residual_solver N λ` to `Problem_Factor N`. Occurs at ⟨1⟩3.
  Source: `notes/srsa-cuts.md` §0. Later fold lemmas depend on *not*
  inhabiting this name. Closing it would be a new proof, not a
  citation of `invert_all_units_both_folds_are_local_monomials`.

## 7. Frozen audit handoff

Forward and reverse inspect this rendering. Mapping annotations are
not premises. Do not treat `SrsaRootPoly.v` as a Lamport proof of
⟨1⟩3.
