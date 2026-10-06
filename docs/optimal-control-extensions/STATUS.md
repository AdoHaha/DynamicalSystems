# Optimal-control extensions — live checkpoint

Date: 2026-10-06.
Baseline: `dev` = `7b9037fb57f826650e8f7b372102b1decb2be1ea`.
Work branch: `codex/optimal-control-extensions`.

This checkpoint is deliberately committed before proof work so an interrupted session does not lose its starting point. It does **not** claim any new theorem or compilation result.

## Requested scope

- K2: optimal-control existence, with feasibility/closure and ordinary-control recovery justified rather than assumed under another name.
- K6: state constraints; distinguish a verification theorem from a necessary principle with measure multipliers and a BV costate.
- K7: per-input nondegeneracy and a precise finite-switch conclusion.
- K8: relaxed controls, dynamics closure, disintegration and ordinary-control selection.
- Measurable PMP: integral/AE dynamics, Lebesgue-point needles, AE Hamiltonian minimization.
- Endpoint constraints and abnormal multipliers: do not silently normalize a multiplier that can vanish.

## Rules for this branch

Preserve the concept-organized library on current dev. Public files and declarations should use mathematical concepts, not campaign numbers. Do not regress the integrated K3/K4 proofs. No `sorry`, added axiom, or renamed target assumption counts as completion. Separate mathematical proof, Lean source, compiler validation, and semantic scope in the final record.

## Environment observed at checkpoint

The connected GitHub API can read and commit repository files. This session's local container currently has neither Lean nor Lake on PATH, and an attempted GitHub clone failed DNS resolution. Existing repository CI and any available execution capability will be inspected; until a real build result is obtained, newly authored Lean must be labelled unvalidated.

## Status

Repository inspection and proof development in progress in the current interactive session. No background job or future delivery is implied. Final scope, theorem names, and validation evidence will replace this section as work is committed.
