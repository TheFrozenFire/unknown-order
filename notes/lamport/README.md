# Lamport route freeze

New paper/plan/cut headlines freeze a **route** here before CAS or
Rocq. Procedure: harness skill `lamport-audit`
(`formal-verification/.agents/skills/lamport-audit/`). Schema:
`reference/artifact.md`. Gate (from the repo root): `bash ../formal-verification/tooling/lamport-gate --root .`
(also via `run-check.sh`).

Existing theorems are **grandfathered**. Do not backfill one
directory per lemma.

`confirming_tools` is still Rocq + CAS. Do not list `lamport`.

If reverse only supports a weaker sentence than `notes/hardness.md`
or `notes/srsa-cuts.md`, prove the weaker sentence and leave the
strong name `*_open_named` unused.
