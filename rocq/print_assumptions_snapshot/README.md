# Print Assumptions baseline

Seeded by `bash rocq/print-assumptions.sh --refresh-baseline`.

Commit `baseline/summary.csv` and `baseline/summary.md` only. Per-result
`.txt` dumps are gitignored. Headline: every named result Closed under
the global context (0 load-bearing axioms). Diff the summary on later
runs; refresh only when the roster or a trust count is meant to change.
