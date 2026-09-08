# Reverse — residual-solver-constructs-factor

## 1. Audit boundary

- Headline / conclusion: a residual solver (every unit `y`)
  constructs a factor of `N`.
- Hypotheses: `RSAInstance`; `residual_solver` as defined.
- Accepted primitives: `srsa_residual_leaf`, `residual_solver`,
  `Problem_Factor`. Not accepted: PPT, GRA-as-hardness, cyclicity.
- Source in scope: `notes/srsa-cuts.md` §0 and the fold-paragraph
  non-discharge sentence. Not in scope as a proof of this headline:
  `invert_all_units_both_folds_are_local_monomials`.

## 2. Obligation graph

```
C0 <- R0 (AND: O1)
C0 <- R1 (OR alternative; diagnostic only — fold classification)
```

- C0: residual solver constructs a factor.
- R0 (primary, the notes’ actual treatment of C0): postpone.
  O1 = ADM-001 (produce a factor from any residual solver).
- R1 (diagnostic): invert-all-units poly has Fermat folds
  `X^{d_p}` and `X^{d_q}`, CRT recovers `d`. This is a *different
  sentence*. Using it as C0 would be `too strong` / `route switch`.

## 3. Critical findings

- **O1 / ADM-001** — `unavailable support` on R0; the source
  identifies the obligation and does not discharge it.
- **R1** — `too strong` if offered as C0: writing local inverse maps
  writes `d`; it does not construct a factor from an arbitrary
  residual solver. Recorded weaker sentence: invert-all-units Fermat
  folds are the local inverse monomials
  (`invert-all-units-folds`).

No counterexample that C0 is false. A leftover pair for one `y`
need not split (`matching_247_*`); that does not decide the
*solver* question.

## 4. Dependency table

| ID | Exact claim or obligation | Needed by | Route / edge | Classification | Support | Status |
|---|---|---|---|---|---|---|
| C0 | residual solver constructs a factor | root | R0 | major claim | | failing |
| O1 | Gallina map `residual_solver → Problem_Factor` | C0 | R0 | unavailable support | ADM-001 | open |
| R1 | invert-all-units folds are local monomials | C0 | diagnostic | too strong | weaker claim | diagnostic only |

## 5. Verdict

NOT ESTABLISHED BY THIS PROOF

Decisive nodes: O1 (ADM-001), R1 (`too strong` as a route to C0).
This does not show the conclusion is false and does not rule out a
different proof. The weaker reverse-closed sentence lives in
`invert-all-units-folds`.
