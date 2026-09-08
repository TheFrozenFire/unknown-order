# Forward — invert-all-units-folds

## 1. Verdict

PASS. No critical or major issue. The `PICK` at ⟨2⟩2 names an
existence proof (`p+q` unit) before the witness is used.

## 2. Theorem contract

Let `P` invert every unit of pin `N` under `e`. Then the Fermat
fold of `P` on `𝔽_p*` is `X^{d_p}` as a polynomial and the Fermat
fold on `𝔽_q*` is `X^{d_q}` as a polynomial. CRT of those local
inverse degrees is `d` mod `λ`.

Not claimed: a residual solver constructs a factor.

## 3. Proof-structure summary

Two levels. Pattern: local `p`-side (complete `𝔽_p*` sample because
`p<q`), then `q`-side with an explicit lift of the missing residue,
then CRT. Scope well formed. ⟨1⟩5 exports the honest-closure
restriction, not a private child of ⟨2⟩.

## 4. Findings

None at MAJOR or CRITICAL.

```
[LMP-001] NOTE — Step ⟨1⟩5 — Honest-closure marker
Claim: this Q.E.D. is not residual_solver_constructs_factor_open_named.
Available facts: ⟨1⟩4.
Problem: none; the marker is the catalog discipline.
Why it matters: vantage 7 / vapor 10.
Required repair: none.
```

## 5. Step ledger

| Step | Current goal | Legal dependencies | Justification checked | Status |
|---|---|---|---|---|
| ⟨1⟩1 | `𝔽_p*` residues are units | pin `p<q` | definition / pin | OK |
| ⟨1⟩2 | match `X^{d_p}` on `𝔽_p*` | invert-all-units, ⟨1⟩1 | named lemma | OK |
| ⟨1⟩3 | fold_p as polynomial | ⟨1⟩2, deg `< p−1`, `p−1` samples | SUFFICES reduction first | OK |
| ⟨2⟩1 | fold_q on `q−2` samples | invert-all-units | named lemma | OK |
| ⟨2⟩2 | PICK `p+q` | `pin_p_plus_q_coprime` | existence before use | OK |
| ⟨2⟩3 | fold_q as polynomial | ⟨2⟩1, ⟨2⟩2 | named lemmas | OK |
| ⟨1⟩4 | both folds; CRT `d` | ⟨1⟩3, ⟨2⟩3 | named theorem | OK |
| ⟨1⟩5 | Q.E.D. of this headline | ⟨1⟩4 | exact current goal | OK |

## 6. Unresolved obligations

None on this route. The residual-solver name remains a different
claim (`residual-solver-constructs-factor`).

## 7. Minimal repair plan

None. Kernel-check the reverse-closed sentence
(`invert_all_units_both_folds_are_local_monomials`, CAS `186`).
