# Variational integration and G10–G12 review

## Reviewed snapshot

This review concerns `geometric-ralph` at
`451db05eff60098a4074dd50af51e06f3f283314`, compared with the earlier variational
contribution at `3615165ef0abc8aca244b3a8f82774e6b4472396`. The Krener task supplied
by the orchestrator is the document added in
[`auto_automatyk` commit `a24af233`](https://github.com/LiderMyHand/auto_automatyk/commit/a24af23362101d31bf55e703292272251aee65ff).
Findings describe that input snapshot. The separate “Resolved by the current
contribution” section records the follow-up changes, preserving the review's
original scope.

**Assessment:** the contribution was integrated intact, and G12 supplies a real
uniform extension of the variational theory. The principal difficulty for the
next worker is a mismatch between the task's abbreviated statements and the
actual exported contracts. The checked proofs do not contain the corresponding
mathematical shortcuts.

## What integrated well

The merge commit `7bc7525f2c4129b65b6fe20a54448ff0e3a35b6b` has exactly the same
tree as the contributed `3615165` commit: `git diff 3615165 7bc7525` is empty.
The subsequent comparison through `451db05` changes only
`FlowCommutator.lean` and `FlowTransport.lean`. The underlying Taylor, Gronwall,
tangent-solution, spatial-variation, and first-order variational proofs remain
unchanged. Existing broad-box reduction interfaces were preserved while the
common integration argument was extracted into `flowsCommute_of_key`.

The following mathematical improvements are substantive:

| Exported result | What it actually establishes |
| --- | --- |
| `uniformFlowInvariance` | One positive time radius and one positive initial-state radius work simultaneously for both chosen flows to remain in the prescribed spatial box. |
| `uniformTangentSolution_onBox` | One time interval and one smaller spatial ball are chosen before the initial point. At each point there is a tangent operator solution, identified with the actual spatial derivative of the same chosen flow. |
| `uniformDifferentiability_onBox` | Spatial differentiability of that chosen flow at every initial point in the smaller ball, on one common time interval. |
| `uniformInvertibility_onBox` | Invertibility of those spatial derivatives on another common interval and smaller ball. |
| `uniformTransport_onBox` | The transported Lie-derivative identity, with one time interval and one smaller ball valid for all initial points. |
| `flowsCommute_unconditional_onBox` | The two chosen flows commute at the distinguished initial point `x₀` for sufficiently small pairs of times, using only the common regularity box and vanishing bracket. |

The uniform tangent proof fixes the compact coefficient bound, trajectory
window, spatial ball, and linear-ODE existence time before introducing the
Taylor tolerance. Only the perturbation radius then depends on that tolerance.
It estimates the nonlinear-flow error against the candidate tangent solution
and obtains `HasFDerivAt`; it does not merely assign a value to `fderiv`.
The same flow `localFlow D.hf0` is used throughout the different initial-state
fibers. These are the critical quantifier and flow-identity requirements from
the previous review. See
[`uniformTangentSolution_onBox`](https://github.com/AdoHaha/DynamicalSystems/blob/451db05eff60098a4074dd50af51e06f3f283314/DynamicalSystems/Control/Geometric/FlowTransport.lean#L220-L576).

The invertibility proof also has a concrete quantitative basis: a uniform
Gronwall estimate makes the derivative sufficiently close to the identity for
the geometric-series unit criterion. The transport proof differentiates this
inverse and the field evaluated on the trajectory, using the identified
tangent solution. No second derivative of the field is required. See
[`uniformInvertibility_onBox` and `uniformTransport_onBox`](https://github.com/AdoHaha/DynamicalSystems/blob/451db05eff60098a4074dd50af51e06f3f283314/DynamicalSystems/Control/Geometric/FlowTransport.lean#L591-L810).

## Findings that affect the Krener task

### 1. The task displays a stronger commutation statement than the library exports

**Priority: high for the next proof; this is a task-contract defect, not a
defect in the checked theorem.**

The task writes the conclusion as commutation at `y`. The actual conclusion of
`flowsCommute_unconditional_onBox` has `x₀` in both compositions and no
quantifier over nearby initial points. Its integration core
`flowsCommute_of_key` has the same limitation. The output is

```text
∃ δ > 0, ∀ |t| < δ, ∀ |s| < δ,
  Φ t (Ψ s x₀) = Ψ s (Φ t x₀).
```

The composition-chart argument uses intermediate points depending on the
transverse coordinate and the other flow times. Applying the theorem again
at such a point also changes the chosen `localFlow` and potentially its time
window. It does not by itself provide commutation for the fixed family of
flows defining the chart.

Two valid ways forward are available. Extend the integration core with one
shared neighborhood of initial points, retaining the same chosen flows; or
export the already established uniform identity
`DΦ t y (g y) = g (Φ t y)` and use the chain rule to differentiate finite
compositions directly. The latter avoids unnecessary flow reordering in the
Krener proof. Sources:
[`flowsCommute_of_key`](https://github.com/AdoHaha/DynamicalSystems/blob/451db05eff60098a4074dd50af51e06f3f283314/DynamicalSystems/Control/Geometric/FlowCommutator.lean#L422-L429),
[`flowsCommute_unconditional_onBox`](https://github.com/AdoHaha/DynamicalSystems/blob/451db05eff60098a4074dd50af51e06f3f283314/DynamicalSystems/Control/Geometric/FlowTransport.lean#L821-L826),
and the existing
[`key` proof](https://github.com/AdoHaha/DynamicalSystems/blob/451db05eff60098a4074dd50af51e06f3f283314/DynamicalSystems/Control/Geometric/FlowCommutator.lean#L719-L744).

### 2. The target's regularity contract is weaker than its “local diffeomorphism” description

**Priority: high when deciding what a completed Krener result means.**

`SimultaneouslyRectifiable` records an `OpenPartialHomeomorph`, its base value
and source membership, and the values of `fderiv` on the distinguished
coordinate vectors. It does not explicitly record differentiability or
continuous differentiability of the map and inverse throughout their domains.
An inverse-function theorem applied to a strict derivative at the origin
establishes a local homeomorphism, but that alone is not a proof of `C¹`
regularity throughout its source. In particular, when `k = 0`, the coordinate
derivative clause is empty.

The existing target can remain as a compatibility interface. A reusable
construction should additionally expose the regularity actually established,
for example differentiability of both directions, and separately `C¹`
regularity when it has been proved. The task should say which of these is
required. It should also distinguish the present spatial differentiability
results from joint differentiability in time and initial state, which is
needed when evaluating `fderiv` of the entire chart. Source:
[`SimultaneouslyRectifiable`](https://github.com/AdoHaha/DynamicalSystems/blob/451db05eff60098a4074dd50af51e06f3f283314/DynamicalSystems/Control/Geometric/Frobenius.lean#L93-L107).

### 3. The chart construction still needs two explicit adapters

**Priority: medium; these are normal remaining proof obligations.**

`flowComplement` and `flowEquiv` split off a single nonzero vector. They do not
yet provide the splitting of the span of an arbitrary independent finite
family used in the task's formula. A family version should expose the
continuous linear equivalence and its action on coordinate vectors, so the
inverse-function argument can use a precise derivative rather than repeat
linear algebra inside its proof. See
[`flowComplement` and `flowEquiv`](https://github.com/AdoHaha/DynamicalSystems/blob/451db05eff60098a4074dd50af51e06f3f283314/DynamicalSystems/Control/Geometric/Rectification.lean#L265-L288).

The inverse-function chart must also be restricted so its whole source lies
inside all necessary time and initial-state domains. The one-field theorem
`rectifyingChart_rectifies` still asks for separate time and initial-state
membership; source membership alone is explicitly unused in that proof.
A full simultaneous result needs to discharge these conditions through the
construction's source, including all intermediate composition points. See
[`rectifyingChart_rectifies`](https://github.com/AdoHaha/DynamicalSystems/blob/451db05eff60098a4074dd50af51e06f3f283314/DynamicalSystems/Control/Geometric/Rectification.lean#L551-L574).

### 4. `CommonFlowDomain` currently represents a spatial regularity box

**Priority: low for correctness, medium for API clarity.**

The bundle contains positive numbers `T` and `r` and `C¹` regularity of the two
fields at every point of `closedBall x₀ r`. Its `T` and `hT` fields are not used
by the G10–G12 proofs, nor do they certify a flow interval. All usable flow
times are constructed later from the chosen local-flow data. There is no
hidden transport, differentiability, or invertibility premise in this bundle.
See
[`CommonFlowDomain`](https://github.com/AdoHaha/DynamicalSystems/blob/451db05eff60098a4074dd50af51e06f3f283314/DynamicalSystems/Control/Geometric/FlowCommutator.lean#L646-L664).

For the next API iteration, either describe this as a common spatial `C¹`
box, or add genuine interval properties if the time field is needed. Provide
a constructor from local `C¹` and bracket-vanishing neighborhoods, which makes
the connection to `FlowsCommuteLocally` direct and avoids hand-assembling the
same finite intersections in downstream proofs.

### 5. The ported Frobenius target accidentally requested analytic regularity

**Priority: high for the target's meaning; this affected a definition, not a
completed theorem. Corrected in the current contribution.**

The reviewed `frobeniusTheorem` replaced the upstream `SmoothFunction` and
`SmoothFunctionOn` wrappers with `ContDiff ℝ ⊤` and `ContDiffOn ℝ ⊤`. The upstream
wrappers use the order `∞`. In the pinned Mathlib, the differentiability order
has two distinct infinite levels: `∞` denotes smoothness and the top element
`⊤`, also written `ω`, denotes analyticity. The theorem
`contDiff_omega_iff_analyticOnNhd` confirms the latter interpretation for the
present real normed-space setting. Thus the target port changed the regularity
of both the input and the requested solution.

The correction is exactly two order replacements: `ContDiff ℝ ∞ g` and
`ContDiffOn ℝ ∞ w (interior s)`, with the `ContDiff` notation scope opened.
This restores the upstream smooth target. It does not prove the target or
reduce a premise of the new Krener theorem, which uses only local `C¹` data.
Sources: upstream
[`SmoothFunction` and `SmoothFunctionOn`](https://github.com/igorkhavkine/lean-dg-frobenius/blob/d762d3d53ad36d5a5f91a8c3280f0a1a279dee06/Frobenius/Basic.lean#L33-L37),
the upstream
[`exists_sol_of_fderiv_compat` statement](https://github.com/igorkhavkine/lean-dg-frobenius/blob/d762d3d53ad36d5a5f91a8c3280f0a1a279dee06/Frobenius/Basic.lean#L266-L270),
Mathlib's
[order notation](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/ContDiff/Defs.lean#L91-L93),
and its
[analyticity equivalence](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/ContDiff/Defs.lean#L1196).

## Documentation and maintainability

Some earlier sections still describe the uniform window as an outstanding
step even though the later G12 section proves it. Examples are
`FlowTransport.lean` lines 110–121 and `FlowCommutator.lean` lines 687–691 and
837–842 at the reviewed snapshot. Their original stage-specific meaning is
understandable, but present-tense “remains open” text is misleading to a worker
reading an isolated section. Label these sections historical or replace the
status sentence with a link to the later theorem. The original
`docs/variational-equation.md` is also a historical handoff and should be dated
or linked to the current status.

The G12 master proof is about 350 lines and repeats much of the bounded
linear-ODE construction and Gronwall identification already present in the
per-point modules. This is sound integration, but future edits would be
easier if the following interfaces were extracted after the present theorem
is complete:

1. A bounded continuous linear-ODE existence theorem with an explicit time
   interval controlled by the coefficient bound.
2. A single-flow theorem bundling a common time interval, common spatial
   neighborhood, spatial derivative identification, and its time equation.
   The tangent theory does not mathematically require a second field `g`.
3. A uniform field-preservation corollary for vanishing brackets, exposing the
   intermediate identity currently private to the commutation proof.

These interfaces would benefit both the control library and a later port to
`lean-dg-frobenius`. They are maintenance suggestions, not prerequisites for
trusting the checked result.

## Resolved by the current contribution

The implementation now supplies both the general finite-family theorem
`krenerLemma` in
[`SimultaneousRectification.lean`](../DynamicalSystems/Control/Geometric/SimultaneousRectification.lean)
and the smooth compatible-PDE theorem in
[`FrobeniusIntegrability.lean`](../DynamicalSystems/Control/Geometric/FrobeniusIntegrability.lean).
The Krener hypotheses are the original local `C¹` assumptions, linear independence
at `x₀`, and pairwise `FlowsCommuteLocally`. There are no additional transport,
flow-domain, derivative, or chart assumptions. The existing
`SimultaneouslyRectifiable` definition is retained for compatibility.

The repairs address the review findings as follows:

| Finding | Resolution |
| --- | --- |
| The commutation theorem concerns only `x₀` | The existing theorem keeps its precise scope. `uniform_fderiv_localFlow_apply_onBox` and `eventually_fderiv_localFlow_apply` expose preservation of a commuting field by the derivative of the fixed flow, uniformly near `(0, x₀)`. The composition proof uses that identity directly. |
| Missing joint regularity | `contDiffAt_localFlow_joint` proves that the chosen local flow is `C¹` jointly in time and initial state near `(0, x₀)`. The proof includes continuity of the spatial derivative through a continuous family of linear variational equations. |
| The target omits chart regularity | `simultaneousRectifyingChart_contDiffOn` and `simultaneousRectifyingChart_symm_contDiffOn` prove `C¹` regularity of the constructed chart on its source and its inverse on its target. The specification also records invertible derivatives and the inverse derivative. |
| Missing finite-family splitting | `frameComplement`, `frameEquiv`, and `frameCoordinates` supply the complement, the continuous linear splitting, and its conversion to the target's canonical `Fin n → ℝ` coordinates. |
| Unrestricted inverse-function source | `exists_simultaneousRectifyingChart` restricts the chart to a neighborhood where all composition derivative identities hold. `simultaneousRectifyingChart_rectifies` requires only source membership for the coordinate-line statement. |
| The common box requires manual construction | `CommonFlowDomain.exists_of_contDiffAt_of_eventually` constructs a closed regularity ball carrying any supplied local property, including bracket vanishing. The arbitrary positive `T` parameter is documented accurately. |
| The Frobenius port used the analytic order | Both regularity orders in the `frobeniusTheorem` interface are restored to `∞`, matching the upstream smooth statement. |
| The smooth compatible-PDE statement had no proof | `frobeniusTheorem_holds : frobeniusTheorem` now proves the full recorded proposition. `exists_sol_of_fderiv_compat` gives the stronger open-domain and `HasFDerivAt` formulation. |

The supporting proofs are organized in
[`FlowBox.lean`](../DynamicalSystems/Control/Geometric/FlowBox.lean),
[`JointFlow.lean`](../DynamicalSystems/Control/Geometric/JointFlow.lean),
[`FlowRegularity.lean`](../DynamicalSystems/Control/Geometric/FlowRegularity.lean),
[`FrameComplement.lean`](../DynamicalSystems/Control/Geometric/FrameComplement.lean),
[`MultiFlow.lean`](../DynamicalSystems/Control/Geometric/MultiFlow.lean), and
[`LocalDiffeomorph.lean`](../DynamicalSystems/Control/Geometric/LocalDiffeomorph.lean).
The source headers and historical status passages in `Frobenius.lean`,
`FlowCommutator.lean`, and `FlowTransport.lean` now direct readers to these
results. They preserve the older reduction theorems' explicit premises and
distinguish the smaller working balls from the original full-box premises.

### Completion of the smooth compatible-PDE theorem

`frobeniusTheorem` remains a `Prop`-valued interface, and
`frobeniusTheorem_holds` supplies its proof. The construction is split into
three mathematical steps and a final interface theorem:

1. [`FrobeniusGraph.lean`](../DynamicalSystems/Control/Geometric/FrobeniusGraph.lean)
   composes the graph fields' local flows to produce an integral
   parametrization. Its horizontal derivative is the identity. The mean-value
   theorem therefore makes its horizontal projection exactly `x₀ + t` on one
   small ball. Translating the parameters and taking the vertical projection
   yields a solution with `Dw(x) = g(x, w(x))` throughout an open neighborhood.
2. [`FrobeniusCoordinates.lean`](../DynamicalSystems/Control/Geometric/FrobeniusCoordinates.lean)
   proves the linear-coordinate transformation of the coefficient and
   curvature and transfers the solution to any finite-dimensional real base
   space. The result is not restricted to a particular `Fin k → ℝ` model.
3. [`FrobeniusRegularity.lean`](../DynamicalSystems/Control/Geometric/FrobeniusRegularity.lean)
   proves smoothness from the differential equation. The function and open
   domain are fixed before induction on the derivative order. If `w` is
   `Cⁿ`, composition with smooth `g` makes its prescribed derivative `Cⁿ`,
   yielding `Cⁿ⁺¹`. Every finite order holds on the same domain, so `w` is
   `C∞` there. Smooth dependence of the flow to every order is unnecessary.
4. `FrobeniusIntegrability.lean` combines these results. The useful endpoint
   `exists_sol_of_fderiv_compat` provides an open set `U` containing `x₀`,
   a smooth function on `U`, its specified initial value, and an actual
   `HasFDerivAt` proof at every `x ∈ U`. Choosing `s = U` makes
   `interior s = s`; the within-derivative statement of `frobeniusTheorem`
   follows at every point requested by its existing interface.

The theorem has exactly the graph-compatibility scope of the ported statement:
the coefficient is globally smooth, its curvature vanishes everywhere, and
the solution is local through each prescribed point. It does not yet turn an
arbitrary involutive frame into a graph connection. That normalization is the
separate preamble identified in `commutingBasis_of_involutive`; the new linear
base-coordinate transformation starts with a graph connection already given.
The iterated-bracket realization and reachability hypotheses of the Chow
development also remain separate. Uniform flow commutation over nearby
initial states is not claimed: field preservation suffices for the completed
Krener and compatible-PDE constructions.

## Baseline validation performed

The reviewed `FlowTransport` dependency chain built successfully with the
pinned Lean `4.35.0-rc2` and the repository's Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Lake reported successful completion
of 2792 jobs. Existing warnings in `Rectification.lean` do not come from the
G10–G12 additions.

An independent dependency inspection covered 16 declarations: the preserved
first-order variational theorem, the full local time-variational theorem, the
per-point transport theorem, and the 13 principal G10–G12 helper and endpoint
theorems. Every declaration depended only on Lean's usual foundations
`propext`, `Classical.choice`, and `Quot.sound`. The inspected signatures
confirm the uniform quantifier order in the four G12 variational theorems and
the distinguished-point scope of the final commuting theorem.

This validation concerns the geometric proof chain and the stated comparison
commits. It does not establish unrelated parts of the entire repository or
the still absent simultaneous-rectification theorem at that snapshot.

## Final Frobenius interface audit

An independent compiler check imported the built `FrobeniusIntegrability`
module and checked the three endpoint declarations. The two existence
theorems require finite-dimensional `X` and `Y` and completeness of `Y`; they
do not require an additional explicit `CompleteSpace X` parameter. The
coordinate construction uses the complete finite real-coordinate model, and
the solution transfer uses its continuous linear equivalence with `X`.

`frobeniusTheorem_holds` has only the real normed-space structures as outer
parameters. Completeness and finite-dimensionality remain universally
quantified inside the existing proposition, exactly as specified by
`frobeniusTheorem`. A separately written example expanded the entire target
statement, including these internal instance binders, and was discharged by
`frobeniusTheorem_holds` with no additional outer instances. Another example
checked the useful smooth existence theorem without an explicit
`CompleteSpace X` hypothesis. Both compiled successfully.

The proof of the within-derivative conclusion uses the openness of `U` at
each `x ∈ U`, rewrites `interior U = U`, and applies the actual full derivative
of `w`. Thus there is no unhandled boundary or differentiability convention
in the final target. Independent dependency inspection of
`exists_local_solution_of_totalFderivCompat`, `exists_sol_of_fderiv_compat`,
and `frobeniusTheorem_holds` reported only `propext`, `Classical.choice`, and
`Quot.sound` for all three.

### Complete contribution verification

The final tree passes `lake build DynamicalSystems` (3993 jobs), both exact
consumer files, and `lake lint -- DynamicalSystems`. The standard project
`axiom-audit` checks 5069 declarations and reports zero violations, with only
`propext`, `Classical.choice`, and `Quot.sound` used. Individual dependency
records also cover all 78 new declarations. The build replays existing
compiler warnings in older files; all eleven new proof modules compile
without warnings. The recorded commands and outputs are in
[frobenius-validation.txt](frobenius-validation.txt) and
[krener-validation.txt](krener-validation.txt).
