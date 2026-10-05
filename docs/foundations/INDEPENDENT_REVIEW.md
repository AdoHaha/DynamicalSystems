# Review of the foundational repairs

Reviewed on 2026-10-05 using Lean `4.35.0-rc2` and the pinned Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Review ownership and scope

The reviewers were separate agents in this implementation session.

The Duhamel implementer independently reviewed the H1, H2, H3, H6, and H7
changes, including the complete-flow application of H3. The H6/H7 implementer
separately reviewed H5. H4 verification below was performed by its author and
is explicitly distinguished from those independent reviews.

The review checks mathematical scope, the substance of the derivations,
regression examples, and transitive axiom dependencies. It concerns the
repaired declarations and their proof dependencies; it does not certify every
declaration in the repository or claim that all unrelated admissions are gone.

## Independent semantic review: H1, H2, H3, H6/H7

No blocking issue was found in the reviewed implementations.

| Target | Findings and limits |
| --- | --- |
| **[H1: comparison functions](../../DynamicalSystems/Basic/ComparisonFunctions.lean)** | The replacement proves class-K-infinity bounds for continuous positive-definite functions on compact sets. Closed-ball bounds assume a proper state space; global bounds additionally assume radial unboundedness. The comparison functions are constructed from an attained, monotone, Lipschitz infimum envelope and an inverse class-K-infinity function. Their existence is derived, not assumed. The compact-set theorem itself does not assume finite dimensionality. |
| **[H2: flow congruence](../../DynamicalSystems/Mathlib/Dynamics/Basic.lean)** | The repaired theorem adds local Lipschitz continuity of the common generator. Orbit differentiability gives actual integral curves, and uniqueness at time zero identifies the two flows. This is a sufficient uniqueness hypothesis; the review does not claim it is logically necessary for every possible pair of flows. |
| **[H3: continuous dependence](../../DynamicalSystems/Mathlib/Analysis/ODE/ContinuousDependence.lean)** | Compactness of the time interval produces a common spatial Lipschitz bound near the reference trajectory. A differential barrier proves that nearby trajectories remain in the required region, and a two-sided Gronwall estimate proves joint continuity. The proof does not assume the desired confinement or continuous dependence. Its more general endpoint treats an arbitrary continuously parameterized initial slice of supplied global integral curves. No completeness or finite-dimensionality assumption is needed for that dependence result. |
| **[H3 application: complete flows](../../DynamicalSystems/Mathlib/Analysis/ODE/CompleteFlow.lean)** | `IsCompleteVectorField.flow` obtains joint continuity from H3 and the group law from integral-curve uniqueness. The assumption supplies global trajectories; this construction itself does not require completeness of the ambient normed space. The derivative and chain-rule corollaries refer to the constructed flow. |
| **[H6/H7: feedback causality](../../DynamicalSystems/InputOutput/ClosedLoop.lean)** | Locally Lp solvability and uniqueness of the truncated feedback state equations are explicit, separate assumptions. Component causality first proves that truncating a full solution satisfies the truncated equations. Uniqueness then identifies equal input prefixes with equal state prefixes. The output theorem follows from the state/output equations. Truncated uniqueness is an algebraic well-posedness condition, not the causal conclusion restated as a premise. |

The regression evidence exercises the repaired scope:

- H1 formally proves that `x² * exp(-x)` has no global class-K lower bound,
  while obtaining local bounds for this same function and global bounds for
  the quadratic function.
- H2 identifies a flow with zero generator as the identity. The H3 application
  identifies the flow of an arbitrary constant vector field, including a
  negative-time example.
- H6/H7 prove the hypotheses for a scalar memoryless loop whose coefficient
  product is `6`; the repair does not impose a small-gain condition. A separate
  two-sample integer example constructs causal components with globally unique,
  locally Lp feedback solutions whose inverse dependence is noncausal. This
  formally demonstrates the missing condition in the original statements.

The relevant production modules and their new imports compiled successfully.
The reviewer also rebuilt the complete-flow and both feedback regression
modules, and inspected the successful H1/H2 regression evidence. No import
cycle or unresolved assumption was found on these paths.

## Independent semantic review: H5

The H5 reviewer found no semantic defect or hidden extension assumption in
the final [continuation theorem](../../DynamicalSystems/Mathlib/Analysis/ODE/GlobalExistenceContinuation.lean).
Its public hypotheses are a complete real normed space, uniformly locally
Lipschitz `f`, time continuity `Continuous f`, and
`LocallyUniformLinearGrowth f`: on each compact time interval, constants
`C, C'` bound `‖f t x‖` by `C * ‖x‖ + C'` for all states. There is no
properness, finite-dimensionality, or global spatial Lipschitz hypothesis.

The proof uses interval uniqueness to glue compatible solutions. Two-sided
Gronwall bounds give a speed bound, hence a Cauchy limit at each finite
endpoint. Completeness supplies the limit; local existence restarts the
solution, and uniqueness justifies the joins. Time reversal supplies the
left extension. Extension contradicts a finite supremum of existence radii.
The reviewer checked the endpoint seams, signs under time reversal, and the
explicit discharge of the extension premise in the final theorem. The
argument uses compactness of time intervals, without compactness of state
balls.

The [pointwise-growth counterexample](../../DynamicalSystemsTest/Mathlib/Analysis/ODE/PointwiseGrowthObstruction.lean)
formally rules out the original hypothesis even on complete `ℝ`: its jointly
C¹ field is bounded in the state variable at each fixed time, but the solution
`(1 - t)⁻¹` cannot extend continuously through `t = 1`. Thus H5 required a
statement repair as well as a proof. The established sufficient condition is
local uniformity of the linear-growth constants; arbitrary locally integrable
growth coefficients are outside this theorem's scope.

## H4: author verification

The repaired [Duhamel theorem](../../DynamicalSystems/Mathlib/Analysis/ODE/Duhamel.lean)
assumes a real Banach space, continuous operator
coefficient `L`, continuous forcing `g`, normalization `X s s = id`, and the
operator-valued `HasDerivAt` equation for `X`. It does not assume a cocycle,
backward differentiability, or the derivative of the integral being proved.

The proof derives the cocycle from integral-curve uniqueness, obtains the
backward derivative by differentiating the inverse operator, and constructs
the existing `IsStateTransition` interface. It factors the Duhamel integral
through a fixed transition operator and applies the interval-integral
fundamental theorem of calculus and the product rule. The public endpoints
provide `HasDerivAt`, a genuine `IsIntegralCurve`, the raw `deriv` identity,
and an `IsFundamentalSolution` result.

Author-compiled regressions cover an arbitrary Banach-space primitive, the
nonautonomous equation `x' = t*x + 1`, negative times, and a formal example
showing that the unnormalized derivative equation alone is insufficient.

## Exact dependency evidence

In a fresh independent Lean process, `#print axioms` succeeded for the
following 19 declarations. Every report contained exactly
`[propext, Classical.choice, Quot.sound]`; none contained `sorryAx` or another
nonstandard axiom.

| Reviewed area | Independently printed declarations |
| --- | --- |
| H1 | `MemKI.symm`; `ComparisonFunction.exists_memKI_le_of_coercive`; `ComparisonFunction.exists_memKI_bounds_of_isCompact`; `ComparisonFunction.exists_memKI_bounds_on_closedBall`; `ComparisonFunction.exists_memKI_bounds_of_radiallyUnbounded` |
| H2 | `flow_congr` |
| H3 | `UniformlyLocallyLipschitz.exists_lipschitzOnWith_closedBall_along`; `norm_le_mul_exp_of_norm_deriv_le_on_closedBall`; `continuous_uncurry_of_isIntegralCurve`; `IsFundamentalSolution.continuous_of_uniformlyLocallyLipschitz`; `IsFundamentalSolution.continuous` |
| Complete flow | `IsCompleteVectorField.flow`; `IsCompleteVectorField.isIntegralCurve_flow`; `IsCompleteVectorField.deriv_comp_flow`; `CompleteFlowRegression.constant_flow_apply` |
| H6/H7 | `SetRel.closedLoop.mem_inputState_truncate`; `SetRel.closedLoop.isCausal_inputState`; `SetRel.closedLoop.isCausal_inputOutput_of_inputState`; `SetRel.closedLoop.isCausal_inputOutput` |

The H5 reviewer separately imported the final continuation and counterexample
modules in a fresh Lean process, printed the public theorem type, and compiled
generic applications of both completeness interfaces using their displayed
hypotheses. That process exited successfully. The reviewer's axiom checks
reported only the same three standard axioms for these seven declarations:

```text
UniformlyLocallyLipschitz.isCompleteVectorField
UniformlyLocallyLipschitz.continuous_uncurry
PointwiseGrowthObstruction.not_complete
ODE.exists_extension_Ioo_right
ODE.exists_extension_Ioo
ODE.isCompleteVectorField_of_extension
IsIntegralCurveOn.eqOn_Ioo_of_uniformlyLocallyLipschitz
```

The reviewer also inspected successful final builder metadata for the
continuation module and the positive and negative H5 regression evidence.

The H4 author's successful test compilation printed the exact standard-axiom
set for these seven declarations:

```text
IsFundamentalSolution.linear_cocycle
IsFundamentalSolution.isStateTransition
IsStateTransition.hasDerivAt_duhamelOperator
IsFundamentalSolution.duhamelOperator_isIntegralCurve
IsFundamentalSolution.duhamelOperator_isFundamentalSolution
DuhamelTests.normalization_is_necessary
DuhamelTests.scalar_forced_fundamentalSolution
```

The checked-in [aggregate audit](../../DynamicalSystemsTest/Foundations/Axioms.lean)
enforces the three-standard-axiom allowlist transitively and fails on missing
target names. The [validation script](../../scripts/check_foundations.sh)
builds the library and regression modules before running that audit. Those
integration checks are maintained separately from this review's evidence;
successful compilation of unrelated modules alone is not an axiom audit.
