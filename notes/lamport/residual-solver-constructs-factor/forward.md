# Forward — residual-solver-constructs-factor

## 1. Verdict

INCOMPLETE. Highest-severity issue: ADM-001 (the headline is
explicitly postponed; no internal silent `PICK`).

## 2. Theorem contract

```
forall (R : RSAInstance) (Solve : residual_solver (rsa_N R) (rsa_lambda R)),
  exists f, Problem_Factor (rsa_N R) f.
```

Domains: RSA instance with odd distinct primes; solver returns a
residual leaf at every unit. Conclusion: some factor of `rsa_N R`.

## 3. Proof-structure summary

Five top-level steps, one level. Pattern: define the leaf and the
solver, then admit the headline. Scope is well formed. No illegal
citation of a sibling’s private substep. ⟨1⟩4 and ⟨1⟩5 are nearby
classifications, not a discharge of ⟨1⟩3.

## 4. Findings

```
[LMP-001] NOTE — Step ⟨1⟩3 — Admitted headline
Claim: residual solver constructs a factor.
Available facts: definitions ⟨1⟩1, ⟨1⟩2.
Problem: source postpones the support (ADM-001).
Why it matters: this is the live target; it is not a closed route.
Required repair: a new proof, or keep the name unused.
```

No MAJOR/CRITICAL: the source does not pretend ⟨1⟩3 is proved.

## 5. Step ledger

| Step | Current goal | Legal dependencies | Justification checked | Status |
|---|---|---|---|---|
| ⟨1⟩1 | define residual leaf | source definition | definition | OK |
| ⟨1⟩2 | define residual solver | source definition | definition | OK |
| ⟨1⟩3 | solver ⇒ factor | ⟨1⟩1, ⟨1⟩2 | admitted | CONDITIONAL |
| ⟨1⟩4 | leftover pair ⇏ factor | named mismatch facts | not used to close ⟨1⟩3 | OK |
| ⟨1⟩5 | invert poly writes `d` | fold route (other claim) | explicit non-discharge | OK |

## 6. Unresolved obligations

ADM-001: inhabit `residual_solver_constructs_factor_open_named`
without projecting `rsa_p` / writing `{p,q}` into coefficients /
writing `d` into a degree. Downstream: any catalog sentence that
cites this name as proved.

## 7. Minimal repair plan

Do not inhabit the name from the fold classification. Freeze the
weaker sentence as a separate claim (`invert-all-units-folds`).
Keep this name unused.
