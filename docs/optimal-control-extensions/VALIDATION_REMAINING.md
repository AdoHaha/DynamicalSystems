# Validation of the remaining-control checkpoint

Date: 2026-10-06. Local work branch: `codex/remaining-optimal-control-proofs`.
Baseline: `69eb63fa294ff2af591bd004f5509b626a18157c`.
Compiler: repository-pinned `leanprover/lean4:v4.35.0-rc2`.

## Checks

- `lake build DynamicalSystems`: PASS, including new umbrella imports.
- `bash scripts/check_optimal_control_extensions.sh`: PASS for the integrated
  finite-switching, relaxed-control and bounded-existence regressions.
- `bash scripts/check_remaining_optimal_control.sh`: PASS, including the final
  actual-optimality forced interior atom regression and all axiom audits.
- Principal new declarations have `#print axioms` audits. The combined script
  rejects dependencies outside `propext`, `Classical.choice`, and `Quot.sound`.
- New sources are scanned for proof placeholders, added axioms and `native_decide`.
- `git diff --check`: PASS.

The umbrella build replays existing warnings in unrelated baseline modules.
Targeted new production-module builds pass without new warnings.

## Regression meaning

`LinearGrowthExistence.lean` proves an actual feasible pair for `x′ = x + u` on
horizon 2 and invokes ordinary minimizer existence. It separately disproves a
uniform global velocity bound, so the new growth theorem is needed.

`EndpointMultipliers.lean` includes actual measurable endpoint-constrained
optimality for the square-root objective and proves that every eligible cost
multiplier vanishes. It also proves terminal-cost optimality for a scalar integrator
before applying the finite-switch bridge.

`MeasureAdjoint.lean` checks interior Dirac jumps and terminal atom traces.
`Mathlib/Analysis/Calculus/IntegralAffineVariation.lean` tests integral
differentiation under a Dirac measure using a measurable single-point spike.

`StateConstraintNecessity.lean` audits actual-optimality multiplier extraction,
constructed replacement trajectories and the assembled scoped state PMP.
`StateConstraintAtoms.lean` proves the actual obstacle-constrained integrator optimum
against every measurable admissible competitor, derives its singleton contact set,
and invokes the necessity theorem. Complementarity and the common-AE control minimum
force a positive Dirac multiplier and a nonzero interior costate jump. Its independent
review and all three principal axiom audits pass. Terminal atoms are tested separately
at the measure-tail level, not as a second actual-optimality regression.

## Review boundary

Independent agent reviews found no semantic blockers within the documented scopes.
The external agy reviewer was unavailable because of its account quota. Local
compilation and agent reviews do not close general nonlinear PMP, general K6,
minimum-time K7 or nonconvex K2/K8 selection.

## Affine-convex K6 continuation

The updated `scripts/check_remaining_optimal_control.sh` passed after adding all
nine new production modules to the umbrella build and checking all four new
regression files. No new production warnings were emitted. The new principal
`exists_stateConstrainedPMP_of_affine_convex_minimum` and strict-initial-fiber
corollary have standard-axiom audits. The script's strict whitelist passes.

The actual nonzero-A optimum regression invokes the full theorem. Separate
singular nonlinear variation/pairing tests agree; nonzero-A additive-adjoint
regressions retain interior and terminal atoms and prove failure of AC. The
actual-optimality forced interior-atom regression remains passing.

Independent reviews cover first variation, indexed pairing, the final necessity
assembly and its regression. Review reports under the parent workspace distinguish
reviewer-owned files from independently reviewed files. The prior external agy
quota failure is still not a completed external review.

Precise inputs, outputs and remaining nonlinear boundaries are in
[K6_AFFINE_NECESSITY.md](K6_AFFINE_NECESSITY.md).

Affine K6 proof checkpoint: local commit `259894b` on
`codex/remaining-optimal-control-proofs`; no push or dev merge.
