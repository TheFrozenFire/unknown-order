# Lamport review is not the map

Do not check convert/forward/reverse/STATUS into this directory.
Notes are working scratch.

The residual-solver split is load-bearing in Rocq:

- live target: `residual_solver_constructs_factor_open_named`
  (unused `*_open_named`)
- reverse-closed sentence:
  `invert_all_units_both_folds_are_local_monomials`
- join: subsection comments `Not [residual_solver_constructs_factor_open_named]`,
  harvested into `generated/NAMED_SKIPS.md`
- compile-time names: `rocq/Routes.v`

A new paper/plan/cut still runs `lamport-audit` (harness skill) as a
review. After the theorem lands, write `Not [foo_open_named]` on the
`(** **` comment and leave the open named unused.
