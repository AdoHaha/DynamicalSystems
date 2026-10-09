# R4c continuation: concrete finite relaxed realization

Worktree: `/home/igor/zabawy/auto_automatyk/.worktrees/r4c-worker`.
Branch: `remaining-optimal-control-r4c-worker`. Starting commit: `5af40ac`.

## Current result

`exists_limit_finiteRelaxedControl_of_unifIntegrable` now joins the moving
endpoint compactness and load-bearing Cesari/Fatou argument to **actual measurable
finite relaxed controls**. Its conclusions include simplex normalization,
admissibility of every atom almost everywhere, the actual weighted integral
trajectory law on the limiting interval, integrable weighted velocity and cost,
and the terminal-plus-running objective upper bound.

The finite-control realization gap is closed for the concrete graph formulation
with nonnegative source costs. The source paths, velocities, costs and constant
extensions remain analytic inputs; they are not yet constructed from the book's
admissible minimizing pairs. The full headline
`exists_relaxedMinimizer_of_weakCesariProperty` is still not declared.

Book anchors: BM *Nonlinear Optimal Control Theory* (2012), Definition 5.4.2
(cached lines 6318 onward), Theorem 5.4.4 (6352), Step 4 (6971–7005), Step 5
(7006–7046), and the lower-bound reduction in the proof before Step 1. The number
of atoms is an explicit natural `N`; BM uses state dimension + 2. No assertion
identifying arbitrary fixed `N` with the whole convex hull is made.

## New declarations

### `FiniteRelaxedEpigraph.lean`

Definitions:

- `FiniteRelaxedControl`: real weight tuple and finite atom tuple.
- `finiteRelaxedControlGraph`: weights nonnegative, sum exactly one, every atom
  in the **original** time/state/control graph.
- `finiteRelaxedVelocity`: actual finite weighted original dynamics.
- `finiteRelaxedRunningCost`: actual finite weighted original cost.

Proofs:

- `lowerSemicontinuousOn_mul_continuous_nonneg`: continuous nonnegative weights
  times real lower semicontinuous costs are lower semicontinuous, including at
  zero weights. No nonnegative cost assumption is needed for this fact.
- `isClosed_controlGraph_of_upperHemicontinuous`: upper hemicontinuity and closed
  original values derive a closed original graph.
- `isClosed_finiteRelaxedControlGraph`: closed original graph derives the closed
  concrete simplex/atom graph. Controls are not assumed compact.
- `continuous_finiteRelaxedVelocity`: derived from original continuous dynamics.
- `lowerSemicontinuousOn_finiteRelaxedRunningCost`: derived from original cost
  lower semicontinuity **on the original graph**, not an assumed property of the
  relaxed cost.
- `finiteRelaxedRunningCost_nonneg` and
  `finiteRelaxedRunningCost_ge_of_lowerBound`: transfer original cost lower
  bounds using actual simplex normalization.
- `exists_measurable_finiteRelaxedControl_of_epigraph`: instantiates the existing
  sigma-compact epigraph selector. Produces measurable weights and atoms and
  their actual weighted identities; no recovery certificate is assumed.
- `aestronglyMeasurable_cost_of_ae_mem_closed_graph`: handles cost measurable
  only on the graph by a measurable extension and almost everywhere equality.
- `exists_integrable_finiteRelaxedControl_of_integrable_lowerBound`: a merely
  integrable lower bound and integrable epigraph domination yield integrability
  of the realized actual cost and its integral bound. The bounding function is
  `‖costLimit‖ + ‖β‖`. No continuity of `β` is required.
- `exists_integrable_finiteRelaxedControl_of_epigraph`: nonnegative specialization
  of the preceding result, with its original signature retained.

### `FiniteRelaxedExistence.lean`

- `exists_limit_finiteRelaxedControl_of_unifIntegrable`: applies the moving
  objective-epigraph result to the concrete relaxed graph, restricts the actual
  L1 velocity to the limiting interval, realizes a finite relaxed control, and
  transfers the integral law and complete objective bound. Property (Q) is
  load-bearing through the existing Cesari/Mazur/Fatou proof chain.

### `CesariCostShift.lean`

- `hasWeakCesariProperty_image_affineIsometryEquiv`: transports tubes, closed
  convex hulls and the core through an actual invertible continuous affine map.
- `shiftedVelocityCostSet`: subtracts a time-dependent lower bound from cost.
- `hasWeakCesariProperty_shiftedVelocityCostSet`: proves preservation of weak
  property (Q) for **arbitrary** time-dependent shifts. Weak property (Q)
  compares state fibers at a fixed time, so no time continuity is needed.

## Load-bearing inputs and reuse

| Input | Actual use |
| --- | --- |
| Original closed graph | Closed finite graph and sigma-compact epigraph domain. |
| Original continuous dynamics | Continuous weighted velocity and selection map. |
| Original graph cost lower semicontinuity | Derived weighted lower semicontinuity; closed epigraph and realized cost measurability. |
| Sigma-compact ambient control space | Concrete finite tuples remain sigma-compact; existing selector applies without compact controls. |
| Simplex conditions | Nonnegative multipliers in lower semicontinuity and cost bounds; normalization transfers the lower bound unchanged. |
| Nonnegative original graph cost | Integrability of the realized cost in the nonnegative moving-interval result. |
| Integrable lower bound (general realization) | Norm domination gives integrability despite negative costs. |
| `hcesari`, compact time-state range, original laws and uniform integrability | Reused moving endpoint extraction and genuine lower closure. |
| Closed strict-duration boundary | Endpoint feasibility and nonzero limiting interval measure for selection. |
| Source cost sign and integrability | Fatou and running-cost subsequence. Their ambient sign is separate from the limiting graph cost sign. |
| Lower semicontinuous terminal cost and total objective convergence | Running-cost extraction and terminal objective comparison. |

No supplied weak limit, feasible recovery, relaxed-cost regularity certificate,
or optimality assumption appears in the new extraction theorem. Reused results
include `exists_measurable_control_of_constrained_epigraph`,
`exists_limit_endpoints_objective_epigraph_of_unifIntegrable`, and the existing
weak-L1/Mazur/Fatou machinery.

## Exact remaining work

1. **Classical equi-AC bridge:** derive uniform integrability of derivative norm
   integrals from the book's finite-disjoint-interval condition. The converse
   interval-integral-to-AC result in mathlib does not supply this uniform bridge.
2. **Source pair API and extensions:** define the faithful variable-endpoint
   finite relaxed problem; construct constant path and zero velocity/cost
   extensions from its admissible pairs and derive the analytic input laws,
   integrability, source epigraph membership, and objective identification.
3. **Complete integrable cost shift:** property (Q) preservation and realized-cost
   integrability are now proved. Still connect the shift to source extensions,
   the continuous primitive and endpoint-dependent terminal compensation, and
   undo it in the moving-interval objective bound. Do not assume lower
   semicontinuity of `c - β(t)` when `β` is merely integrable.
4. **Minimizer assembly:** relate objective convergence to the actual feasible
   cost infimum, produce the realized admissible pair and compare with every
   competitor. No full relaxed minimizer theorem has yet been claimed.
5. **Ordinary conclusion / occupation interface:** prove the dimension-dependent
   convex-hull identification needed for the book's ordinary-convexity conclusion.
   If exposing occupation measures, construct the finite-atomic kernel/marginal
   and integral identities. The current representation is explicit measurable
   weights and atoms.

These are unproved tasks, not external blockers or hidden certificates. Previous
reports describing finite-atomic realization as entirely missing are historical;
this continuation closes the concrete selector and moving-limit realization.

## Verification

The umbrella and check script include all three new modules; the script's direct
Lean gate checks zero warnings. `DynamicalSystemsTest/R4CFiniteRelaxed.lean`
audits all 19 declarations (including definitions). Final validation passed:

- `lake build DynamicalSystems`: exit 0, 4256 jobs.
- `scripts/check_remaining_optimal_control.sh`: exit 0, including zero-warning
  direct Lean checks of all three new modules and forbidden-token checks.
- All 19 new declarations were audited; the full script produced 189 dependency
  records, all within `{propext, Classical.choice, Quot.sound}`.
- `git diff --check`: clean. Logs: `.lake/r4c-finite-check.log` and
  `.lake/r4c-finite-umbrella.log` (ignored). Full builds replay older warnings;
  the new modules have no warnings.

No proof escapes, linter suppressions, or lines beyond 100 columns were added.

Preexisting worktree deletions of `HARD_REPORT.md` and `R4C_REPORT.md` remain
untouched and excluded from the commit. This report is the committed snapshot;
the required canonical main-workspace `R4C_REPORT.md` is updated separately.
