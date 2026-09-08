# Reverse — invert-all-units-folds

## 1. Audit boundary

- Headline / conclusion: invert-all-units ⇒ Fermat folds are
  `X^{d_p}` and `X^{d_q}`; CRT recovers `d` (mod `λ`); this writes
  the local inverse maps, hence `d`; not
  `residual_solver_constructs_factor_open_named`.
- Hypotheses: campaign pin (`p<q`); `P` inverts every unit.
- Accepted primitives: `invert_all_units_local_p`,
  `invert_all_units_fold_p_is_local_monomial`,
  `pin_p_plus_q_coprime`, `invert_all_units_fold_q` /
  `invert_all_units_fold_q_classes`,
  `invert_all_units_fold_degrees_crt_d`.
- Source: `notes/srsa-cuts.md` Fermat-fold paragraph (CAS `176`–`186`).

## 2. Obligation graph

```
C0 <- R0 (AND: C1, C2, O-crt, O-honest)
C1 <- R1 (AND: O-p-units, O-match-p, O-deg-p)
C2 <- R2 (AND: O-samples-q, O-lift, O-eval-lift)
```

- C0: both folds are local inverse monomials; CRT recovers `d`.
- C1: fold_p ≡ `X^{d_p}` as a polynomial.
- C2: fold_q ≡ `X^{d_q}` as a polynomial (no top-zero hyp).
- O-p-units: `p<q` ⇒ `𝔽_p*` residues are units of `N`.
- O-match-p: invert-all-units ⇒ match `X^{d_p}` on `𝔽_p*`.
- O-deg-p: `p−1` samples and deg(fold)`< p−1`.
- O-samples-q: fold_q agrees with `X^{d_q}` on `𝔽_q* \ {p}`.
- O-lift: `p+q` is a unit, `p+q ≡ p (mod q)`.
- O-eval-lift: invert-all-units at the lift.
- O-crt: local inverse degrees CRT to `d` mod `λ`.
- O-honest: C0 does not inhabit the residual-solver open named.

No supplied alternative route. Diagnostic (not used): leftover
kernel span is a different claim.

## 3. Critical findings

None on R0. A `PICK` of residue `p` without the lift would fail
O-lift (`missing`); the source supplies `p+q`.

`too strong` relative to C0 would be “therefore a residual solver
constructs a factor.” That is C0 of
`residual-solver-constructs-factor`, not an obligation of R0.
Recorded as O-honest (`discharged` by explicit non-claim).

## 4. Dependency table

| ID | Exact claim or obligation | Needed by | Route / edge | Classification | Support | Status |
|---|---|---|---|---|---|---|
| C0 | both folds local monomials; CRT `d` | root | R0 | major claim | | discharged |
| C1 | fold_p ≡ `X^{d_p}` | C0 | R0 | major claim | | discharged |
| C2 | fold_q ≡ `X^{d_q}` | C0 | R0 | major claim | | discharged |
| O-p-units | `p<q` ⇒ `𝔽_p*` units of `N` | C1 | R1 | hypothesis | pin | discharged |
| O-match-p | match `X^{d_p}` on `𝔽_p*` | C1 | R1 | named theorem | `invert_all_units_local_p` | discharged |
| O-deg-p | samples vs fold degree | C1 | R1 | algebraic/logical step | Fermat fold | discharged |
| O-samples-q | fold_q on `q−2` samples | C2 | R2 | named theorem | `invert_all_units_fold_q_eval` | discharged |
| O-lift | `p+q` unit, `≡ p (mod q)` | C2 | R2 | named theorem | `pin_p_plus_q_coprime` | discharged |
| O-eval-lift | invert at the lift | C2 | R2 | named theorem | `invert_all_units_fold_q` | discharged |
| O-crt | CRT of `d_p`, `d_q` is `d` | C0 | R0 | named theorem | `invert_all_units_fold_degrees_crt_d` | discharged |
| O-honest | not residual-solver ⇒ factor | C0 | R0 | too strong (refused) | split_from | discharged |

## 5. Verdict

FOLLOWS

Decisive nodes: C1, C2, O-lift, O-crt. Reverse-closed sentence is
the STATUS `headline` / theorem
`invert_all_units_both_folds_are_local_monomials` (CAS
`186_both_folds_crt.gp`). The stronger name stays
`residual_solver_constructs_factor_open_named`
(`split_from: residual-solver-constructs-factor`).
