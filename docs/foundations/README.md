# Foundational ODE and feedback repairs

This branch completes the seven `proof_wanted` declarations identified after the
Kirk–Medhin campaign. The replacements have kernel-checked proofs, explicit
mathematical contracts, regression applications, and counterexamples to the
overstated original claims. The main global-existence theorem covers arbitrary
real Banach spaces with locally Lipschitz vector fields.

Base: `dev` at `b4e6a3663bc3ed6a65742d3b1461e83f2e04e33f`.
Branch: `proof/ode-causality-repair`.
The Lean toolchain and dependency manifest are unchanged: Lean `v4.35.0-rc2`,
mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Completed targets and contracts

| Target | Public result | Contract and scope |
| --- | --- | --- |
| H1 `foo` | `ComparisonFunction.exists_memKI_bounds_of_isCompact`, `exists_memKI_bounds_on_closedBall`, `exists_memKI_bounds_of_radiallyUnbounded` | Local bounds on compact sets; global bounds with radial unboundedness in a proper normed space. Both comparison functions are class K∞. |
| H2 `flow_congr` | `flow_congr` | Differentiable flow orbits, identical generators, and a locally Lipschitz common generator imply equality of flows. |
| H3 `continuous` | `IsFundamentalSolution.continuous`; stronger `continuous_uncurry_of_isIntegralCurve` | Uniform local Lipschitz continuity in the state gives joint continuity of supplied trajectories from continuous initial data. |
| H4 Duhamel | `IsFundamentalSolution.duhamelOperator_isIntegralCurve`, `duhamelOperator_isFundamentalSolution` | Continuous coefficients and forcing, a normalized operator solution, and actual derivative hypotheses on a real Banach space. |
| H5 completeness | `UniformlyLocallyLipschitz.isCompleteVectorField` | A complete state space, continuous time dependence, and linear growth uniform on each compact time interval. |
| H6 state causality | `SetRel.closedLoop.isCausal_inputState` | Causal components and a global graph, measurable prefixes, locally Lp solvability, and uniqueness of the actual truncated feedback equations. |
| H7 output causality | `SetRel.closedLoop.isCausal_inputOutput` | The corresponding output graph and the same substantive hypotheses; derived through the input-state equations. |

The statements were repaired where needed. In particular, H5's original
pointwise-in-time growth hypothesis was false even for a continuously
differentiable scalar vector field. H1's original global conclusion also cannot
be repaired by adding only continuity and finite dimensionality.

## H5: Banach-space continuation

The growth condition is deliberately local in time:

```lean
def LocallyUniformLinearGrowth (f : ℝ → E → E) : Prop :=
  ∀ a b : ℝ, ∃ C C' : ℝ≥0, ∀ t ∈ Set.Icc a b, ∀ x : E,
    ‖f t x‖ ≤ (C : ℝ) * ‖x‖ + C'
```

For `[CompleteSpace E]`, the main theorem takes
`hf : UniformlyLocallyLipschitz f`, `htime : Continuous f`, and
`hgrowth : LocallyUniformLinearGrowth f`, and returns `IsCompleteVectorField f`.
Here `Continuous f` uses the function-space topology: continuity in time at each
fixed state. Joint continuity is derived from this and `hf`.

The proof constructs a global curve. Existing local existence produces a
nonempty set of admissible symmetric time intervals; interval uniqueness glues
their solutions. If the supremum of their radii were finite, the existing
Grönwall estimate would bound the state and hence the speed throughout that
interval. The resulting Lipschitz curve has finite endpoint limits by
completeness. Local existence at those limits and uniqueness across the seams
extend the curve past both endpoints, contradicting maximality. The admissible
radii are therefore unbounded, and the glued curve solves the equation for all
real times.

The reusable continuation criterion `ODE.isCompleteVectorField_of_extension`
has an extension premise. The main theorem **discharges** that premise with the
growth estimate and the proved endpoint-extension lemmas. It does not assume
global existence or an unproved continuation assertion.

There is no finite-dimensionality, compactness of state-space balls, global
spatial Lipschitz constant, or single growth constant valid for all time.
`locallyUniformLinearGrowth_of_continuous_bound` accepts continuous growth
coefficients that may be unbounded over the full real line. The regressions
include `x' = sin(x²)` and `x' = t x`.

The source is divided by mathematical role:

- [UniformlyLocallyLipschitzUniqueness.lean](../../DynamicalSystems/Mathlib/Analysis/ODE/UniformlyLocallyLipschitzUniqueness.lean): uniqueness on an arbitrary open interval.
- [GlobalExistenceGrowth.lean](../../DynamicalSystems/Mathlib/Analysis/ODE/GlobalExistenceGrowth.lean): growth conditions, Grönwall estimates, endpoint limits, and extension.
- [GlobalExistenceContinuation.lean](../../DynamicalSystems/Mathlib/Analysis/ODE/GlobalExistenceContinuation.lean): gluing, the maximal-radius argument, and the final completeness theorem.

The existing `norm_le_gronwallBound_of_linear_growth` in
`GlobalExistenceLinear.lean` is made public so it can be reused; its proof is
unchanged. The old global uniqueness theorem also reuses the new interval
uniqueness lemma.

### Why the original H5 hypothesis fails

The formal regression uses

\[
 f(t,x)=\frac{2(1-t)^2x^4}{1+(1-t)^4x^4}.
\]

Its denominator is strictly positive. The test proves `ContDiff ℝ 1`, uniform
local Lipschitz continuity, time continuity, and boundedness in the state at
each fixed time. For `t ≠ 1`, a bound is `2/(1-t)²`; at `t = 1` the field is
identically zero. Thus it satisfies the original `∀ t, ∃ a b, ...` linear-growth
premise. Nevertheless, the solution through `(0, 1)` is `1/(1-t)` for `t < 1`,
and it has no continuous extension through time 1. The theorem
`PointwiseGrowthObstruction.not_complete` formally proves the failure of
completeness.

Compact-time uniform bounds are the sufficient condition proved here. More
general completeness results with locally integrable growth coefficients would
require a separate theorem; this branch does not claim that extension.

## H3 and the flow API

[ContinuousDependence.lean](../../DynamicalSystems/Mathlib/Analysis/ODE/ContinuousDependence.lean)
proves a stronger result than the original placeholder. The parameter space
may be any topological space. Once the trajectories are supplied, continuity
of the vector field in time is unnecessary: differentiability gives continuity
of each trajectory, and uniform local Lipschitz estimates control differences
between trajectories. Completeness of the state space is also unnecessary for
this theorem.

Compactness of a reference trajectory's time interval supplies one tube radius
and one spatial Lipschitz constant. A differential barrier proves confinement
and the separation estimate. Confinement is derived, rather than appearing as
an extra hypothesis. This avoids requiring the spatial differentiability used
by the library's higher-order geometric flow regularity results.

The compatibility theorem `IsFundamentalSolution.continuous` retains the original
time-continuity argument; the stronger wrapper is named
`continuous_of_uniformlyLocallyLipschitz`.

[CompleteFlow.lean](../../DynamicalSystems/Mathlib/Analysis/ODE/CompleteFlow.lean)
then constructs a bundled continuous `Flow ℝ E` from a complete autonomous
locally Lipschitz vector field. Uniqueness proves the group law, and H3 proves
joint continuity. The API includes the integral-curve equation,
`hasDerivAt_flow`, `deriv_flow`, and `deriv_comp_flow`. The corresponding
`IsLinearlyBddVectorField` flow wrappers are restored in `Mathlib/Dynamics/Basic`.
The nonzero translation regression checks the formula at negative as well as
positive time.

H2 uses the same uniqueness infrastructure: `Flow.isIntegralCurve` derives each
orbit's equation from the generator, and `flow_congr` applies uniqueness to the
two orbits. Local Lipschitz continuity is the sufficient uniqueness hypothesis
used by this proof.

## H1: local and global comparison bounds

[ComparisonFunctions.lean](../../DynamicalSystems/Basic/ComparisonFunctions.lean)
constructs the comparison functions, including the class-K∞ inverse used for
the upper bound. A shared infimum-envelope construction proves continuity,
monotonicity, positivity, strict increase, and unboundedness.

On an arbitrary compact set, continuity and positive definiteness suffice;
the ambient normed additive group may be infinite-dimensional. The closed-ball
wrapper explicitly assumes `ProperSpace`. For global bounds in a proper space,
the radial-unboundedness hypothesis is `Tendsto V (cocompact E) atTop`.

The test `ComparisonFunctionTests.no_global_classK_lower_bound` proves that
`V(x) = x² exp(-x)` has no global class-K lower bound, even though it is continuous
and positive definite on the real line. Its local bounds are proved with the
new compact theorem. A quadratic example exercises the global theorem.

## H4: Duhamel's formula

[Duhamel.lean](../../DynamicalSystems/Mathlib/Analysis/ODE/Duhamel.lean) accepts
continuous `L : ℝ → E →L[ℝ] E` and `g : ℝ → E`, together with
`X s s = ContinuousLinearMap.id ℝ E` and
`HasDerivAt (X s ·) ((L t).comp (X s t)) t` for all `s, t`.

Uniqueness derives the cocycle law; inverse differentiation derives the backward
equation. These facts connect the original initial-time-first convention for
`X` to the existing `IsStateTransition` API. Factoring the integral through the
initial time reduces differentiation to the ordinary interval-integral FTC and
the product rule. The result holds for all real times, including times before
the initial time.

`duhamelOperator_isIntegralCurve` now returns an actual `IsIntegralCurve` proof.
`duhamelOperator_deriv` provides the pointwise derivative form, and
`duhamelOperator_isFundamentalSolution` includes the initial condition. The
tests refute the original unnormalized statement using `X = 0`, `L = 0`,
`g = 1`, and verify `x' = t x + 1` using its exponential transition operator.

## H6/H7: feedback causality

[ClosedLoop.lean](../../DynamicalSystems/InputOutput/ClosedLoop.lean) defines
`loop.truncate S` by truncating each component's input and output before closing
the feedback loop. `HasUniqueTruncatedStates` requires uniqueness for those
actual algebraic feedback equations on admissible prefixes. Existence for every
possible truncated input is unnecessary. Full graph well-posedness of each
truncated loop is available as a stronger sufficient condition.

`LocallyLpSolvable` separately ensures that locally Lp external inputs admit
locally Lp internal states. Component causality proves that restricting a full
state produces a state of the truncated loop. Prefix uniqueness then proves
input-state causality. `isCausal_inputOutput_of_inputState` transfers this to
outputs through the existing algebraic correspondence.

The scalar gains 2 and 3 satisfy the repaired theorem; their gain product is 6,
so the result is useful beyond small-gain hypotheses. The separate two-sample
integer-signal counterexample proves both original causality conclusions false:
a causal bijection encodes one bit of the first sample into the second output,
making its inverse depend on the future. The formal example satisfies the
original component graph/causality and full-loop graph assumptions, and even
local Lp solvability. This isolates the missing prefix-uniqueness requirement.

## Imports and compatibility

`import DynamicalSystems` exports all new APIs. For focused imports, use the
source module named above: H3 is in `ContinuousDependence`, H4 in `Duhamel`, H5
in `GlobalExistenceContinuation`, and the bundled flow construction in
`CompleteFlow`. `GlobalExistence` remains the lower-level home of global
uniqueness and the Duhamel operator definition; importing it alone does not
import the new higher-level results.

The false `foo` placeholder is replaced by descriptive comparison theorem names.
The repaired H2, H4, H5, H6, and H7 statements require the assumptions shown in
the table. Existing public definitions are retained. None of the seven original
`proof_wanted` declarations was a public proof of its displayed proposition.

## Verification and rerunning

The recorded run passed the full `DynamicalSystems` umbrella and its 261 project
modules, all eight regression modules, and the enforced 58-declaration axiom
audit. Changed Lean source and regression files compiled without warnings;
unchanged downstream files emitted existing style and deprecation warnings.

Run in a normal checkout with the pinned Lean toolchain and dependencies:

```sh
bash scripts/check_foundations.sh
```

The script builds `DynamicalSystems`, compiles eight regression modules and the
aggregate audit, and screens production source for active placeholders. It is
also called by the existing GitHub Actions build workflow.

[Axioms.lean](../../DynamicalSystemsTest/Foundations/Axioms.lean) explicitly names
58 declarations spanning all seven targets, analytic bridges, flow constructors,
counterexamples, and applications. It computes their transitive axiom dependencies
and raises an error for a missing declaration or any axiom other than `propext`,
`Classical.choice`, or `Quot.sound`. This is an enforced check, not merely printed
diagnostics.

The source screen ignores nested comments and strings. At the base revision it
finds 7 active `proof_wanted` declarations in 263 production files and no active
`sorry`, `admit`, or custom `axiom`. In the repaired 269-file production tree all
four counts are zero. Pinned Batteries represents `proof_wanted` by a private
`ProofWanted` wrapper carrying no proof of the requested statement; the original
holes therefore did not themselves inject `sorryAx` into the library. Commented
drafts in unrelated files are preserved.

See [VALIDATION.json](VALIDATION.json) and [VALIDATION.txt](VALIDATION.txt) for the
recorded build scope, exact options, source fingerprints, and audit output.
The implementation session used the stock pinned Lean compiler with recursively
verified dependency fingerprints and the pinned Mathlib cache. It ran Lean
directly rather than claiming a Lake build or a Verso documentation build.
The canonical Lake script above provides the ordinary-checkout reproduction path.

[INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md) records the separate semantic
reviews and their scope. Kernel acceptance, transitive axiom auditing, and
semantic review are distinct checks. No claim is made that every unrelated
declaration's intended mathematical specification has been independently reviewed.
