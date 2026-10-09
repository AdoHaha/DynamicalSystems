# GPT Pro handoff: finish Berkovitz–Medhin Theorem 5.4.4 in Lean

## Task to continue

Complete the genuine relaxed-existence theorem
`exists_relaxedMinimizer_of_weakCesariProperty`, matching Berkovitz–Medhin,
*Nonlinear Optimal Control Theory* (2012), Theorem **5.4.4**. The earlier reference
“5.4.4.4” meant this theorem. Reuse the proved weak-L1, moving-interval,
Cesari/Mazur/Fatou, and concrete finite-atomic realization results below.

**Status: partial. The full headline is neither proved nor declared.** The latest
result constructs a limiting finite relaxed control with actual integral dynamics
and an objective bound from supplied extended analytic sequence data. It does
not yet instantiate those data from the book's admissible minimizing sequence,
handle the whole integrable cost shift, or prove global minimality.

This document is self-contained as a research/proof handoff. If you have no
repository access, request the Lean modules listed below and the relevant book
sections, or provide detailed mathematical bridge proofs and Lean-ready lemma
statements. Do not present uncompiled suggested code as a verified proof.

## Checkout and history

- Repository: `https://github.com/AdoHaha/DynamicalSystems`.
- Branch: `remaining-optimal-control-r4c-worker`.
- Local worktree: `/home/igor/zabawy/auto_automatyk/.worktrees/r4c-worker`.
- Lean toolchain: `leanprover/lean4:v4.35.0-rc2`.
- Proof checkpoint before this documentation commit:
  `c89f5b334aabb3e29546d7c48879e8744d7b5bb4`.
- Validated proof commits:
  - `4ead5e0`: weak L1 compactness, integral-law convergence, noncompact selection,
    and the fixed-interval integral minimizer.
  - `5af40ac`: moving endpoints, eventual feasibility, terminal objective bound.
  - `c89f5b3`: concrete measurable finite relaxed realization and cost-shift helpers.
- `5069820` is an earlier preserved WIP; start at the latest branch tip.
- Main `dev` has advanced separately and contains integration of some earlier
  work. Do not treat it as interchangeable with this branch or cherry-pick
  duplicate proofs blindly. No merge/rebase of current `dev` was done here.
- Local deletions of `notes/.../HARD_REPORT.md` and `notes/.../R4C_REPORT.md`
  predate this handoff and were deliberately excluded from the commits.

The cached book is local, outside this worktree:
`/home/igor/zabawy/auto_automatyk/papers/text/berkovitz_medhin_nonlinear_optimal_control.txt`.
Read §§5.3–5.4 and the admissibility/relaxation definitions in §§3.5 and 4.4.
Useful cached-text anchors:

| Topic | Approximate text line |
| --- | ---: |
| Definitions 5.3.1–5.3.2: uniform integral AC and trajectory equi-AC | 6006–6042 |
| Theorem 5.3.5: weak L1 convergence via primitives | 6078 |
| Assumption 5.4.1 | 6299 |
| Definition 5.4.2: ordinary and relaxed cost epigraphs | 6318 |
| Theorem 5.4.4 | 6352 |
| Remark 5.4.13: integrable lower-bound reduction | 6679 |
| Proof Step 1: common-interval extensions and endpoints | 6750–6832 |
| Step 2: running-cost subsequence | 6833–6845 |
| Step 3: property (Q), Mazur/Fatou, (5.4.28)–(5.4.32) | 6847–6969 |
| Step 4: measurable finite relaxed realization | 6971–7005 |
| Step 5: objective comparison, (5.4.33) | 7006–7046 |

## Mathematical target

The book's data include a compact time interval `I`, a closed state domain
`X ⊆ ℝ^d`, and an open control domain `U ⊆ ℝ^m`. The dynamics `f` are continuous
on `I × X × U`; the running cost `c` is lower semicontinuous there and satisfies
`c(t,x,u) ≥ β(t)` for an integrable time function `β`. Controls belong to the
state-dependent constraint `Ω(t,x)`. The terminal set `B` is closed and imposes
`t0 < t1`; the terminal cost `g` is lower semicontinuous on `B`.

A finite relaxed control has `d+2` atoms `u_i(t) ∈ Ω(t,x(t))` and measurable
weights `π_i(t) ≥ 0`, `Σ_i π_i(t) = 1`. Its dynamics and objective are

```text
x'(t) = Σ_i π_i(t) f(t,x(t),u_i(t)),
J = g(t0,x(t0),t1,x(t1)) + ∫_[t0,t1] Σ_i π_i(t)c(t,x(t),u_i(t)) dt.
```

Assume admissible relaxed pairs are nonempty, and an actual minimizing sequence
has trajectories in a compact time-state set `R0 ⊆ I × X` and satisfies the
classical equi-absolutely-continuous trajectory condition. Assume the relaxed
velocity–cost epigraph has weak Cesari property (Q) at every point of `R0`.
Construct an admissible relaxed minimizer and prove its objective is no larger
than **every** admissible competitor's. Under convexity of the ordinary
constrained epigraph, also prove the book's ordinary-and-relaxed optimality
conclusion.

Our epigraph coordinate order is `(velocity, cost)`, the reverse of the book's
written `(cost, velocity)` order. Weak property (Q) means

```text
⋂_(δ>0) closure(convexHull(⋃_(dist(x',x)<δ) Q(t,x'))) ⊆ Q(t,x).
```

The time is fixed in this definition. This matters for merely measurable cost
shifts. Property (Q) must participate in proving limiting feasibility.

## What is already proved; reuse it

All paths below are relative to the Lean repository/worktree root.

### Weak L1 and trajectory extraction

`DynamicalSystems/Mathlib/MeasureTheory/WeakL1Compactness.lean`:

- `DynamicalSystems.WeakL1.exists_weak_L1_clusterPoint_of_uniformIntegrable`.
  Truncation plus weak compactness of bounded L2 approximants constructs weak
  L1 cluster points. There is no L2 bound on the original velocities.

`DynamicalSystems/Mathlib/MeasureTheory/EquiIntegrableTrajectories.lean`:

- `uniformIntegrable_of_unifIntegrable_on_interval`: derives the global L1
  bound on a finite interval, without an extra supplied norm bound.
- `exists_uniform_limit_weak_L1_tendsto_integral_law`: given actual source
  integral laws, compact state range and `UnifIntegrable` L1 velocities,
  extracts uniform path convergence, weak L1 convergence and the limit law.
- Primitive uniqueness uses Lebesgue differentiation. Weak sequential
  convergence is proved from this law; do not replace it by assumed convergence.

Here `UnifIntegrable` controls integrals of velocity **norms** on small measurable
sets. It is not yet derived from the classical disjoint-interval trajectory
condition. Be precise about the distinction from bounds on the norm of a signed
or vector integral, where cancellation is possible.

### Eventual Cesari lower closure and moving intervals

`DynamicalSystems/OptimalControl/ContinuousTime/CesariExistenceArgument.lean`:

- `exists_weights_ae_tendsto_of_weak_Lp_tendsto`: actual Mazur tail weights.
- `exists_integrable_cost_epigraph_of_weak_Lp_tendsto`: original Fatou engine.
- `exists_integrable_cost_epigraph_of_weak_Lp_tendsto_of_eventually_mem`: the
  needed strengthened engine. Membership may hold only eventually for each
  time, almost everywhere; the finite exceptional prefix may depend on time.
- Other eventual-tail helper lemmas are in the same file. The original four
  public theorem signatures/docstrings were preserved as corollaries.

`DynamicalSystems/Mathlib/MeasureTheory/MovingIntervalCompactness.lean`:

- `eventually_mem_Ioo_of_endpoint_tendsto`.
- `const_on_outer_intervals_of_uniform_tendsto_endpoints`.
- `integral_difference_law_on_subinterval`.
- `exists_uniform_limit_endpoints_weak_L1_integral_law`.

`DynamicalSystems/OptimalControl/ContinuousTime/CesariMovingInterval.lean`:

- `exists_limit_endpoints_cost_epigraph_of_unifIntegrable`.
- `exists_runningCost_tendsto_subseq_of_tendsto_totalCost`.
- `terminalCost_add_le_of_tendsto_totalCost`.
- `exists_limit_endpoints_objective_epigraph_of_unifIntegrable`.

These derive endpoint convergence, actual boundary membership and strictly
positive limiting duration; preserve constant extensions; derive the limiting
interval law; apply eventual Cesari/Fatou closure; extract a running-cost
subsequence and pass lower semicontinuous `g` to the limit. Property (Q) is needed
only on the actual compact time-state set, not on the whole interval times its
state projection. Global compactness of the admissible-pair space is not assumed.

### Concrete finite relaxed selection

`DynamicalSystems/Mathlib/MeasureTheory/MeasurableEpigraphLift.lean` and
`MeasurableSigmaCompactLift.lean` supply the sigma-compact measurable selector.

`DynamicalSystems/OptimalControl/ContinuousTime/FiniteRelaxedEpigraph.lean`
defines and proves:

```lean
FiniteRelaxedControl N U := (Fin N → ℝ) × (Fin N → U)
```

For `p = (t,x,(weights,atoms))`, `finiteRelaxedControlGraph N C` requires
nonnegative weights, sum one, and `(t,x,atoms i) ∈ C` for every atom.
`finiteRelaxedVelocity N f` and `finiteRelaxedRunningCost N c` are the actual
weighted sums, not abstract recovery maps.

Important lemmas:

- `isClosed_controlGraph_of_upperHemicontinuous`: upper hemicontinuity plus
  closed values derives the original closed graph.
- `isClosed_finiteRelaxedControlGraph`.
- `continuous_finiteRelaxedVelocity`.
- `lowerSemicontinuousOn_finiteRelaxedRunningCost`: derives weighted lower
  semicontinuity from original graph cost lower semicontinuity, including at
  zero weights. No weighted-cost regularity certificate is supplied.
- `exists_measurable_finiteRelaxedControl_of_epigraph`.
- `exists_integrable_finiteRelaxedControl_of_integrable_lowerBound`: realizes
  actual dynamics and cost; integrability follows from integrable domination
  and an integrable lower bound. No continuity of the lower bound is required.
- `exists_integrable_finiteRelaxedControl_of_epigraph`: nonnegative specialization.

### Strongest current assembled theorem

`DynamicalSystems/OptimalControl/ContinuousTime/FiniteRelaxedExistence.lean`:

`OptimalControl.exists_limit_finiteRelaxedControl_of_unifIntegrable`.

Its analytic inputs are:

- `x : ℕ → Icc a b →ᵇ E`, ambient L1 velocities `w`, moving endpoint sequences
  `l,r : ℕ → Icc a b`, ambient running costs `cost`.
- Original integral law for `x,w`, constant extension identities outside each
  source interval, source membership in compact time-state `R`, and uniform
  integrability of `w`.
- Interior source epigraph membership in the **concrete finite relaxed graph**,
  ambient nonnegative integrable source costs, and total objectives tending to
  a real `m`.
- Closed strict-duration boundary `B`, original boundary membership, lower
  semicontinuous terminal `g`, continuous original `f`, lower semicontinuous
  original graph cost `c`, nonnegative graph costs, and load-bearing property (Q).

It constructs a uniform limiting path, limiting endpoints in `B`, a measurable
finite relaxed control `u`, its actual weighted integral dynamics on the limiting
interval, integrable actual weighted velocity and cost, and `J_limit ≤ m`.

**Limits of this theorem:** it assumes the analytic source data rather than
constructing them from admissible pairs; `m` is a supplied objective limit rather
than the proved feasible infimum; it handles nonnegative running costs; it has
arbitrary explicit `N` and asserts no dimension-dependent convex-hull equality.
The output states compact state-projection membership, not a standalone proof of
all-time limiting time-state membership in the original state domain. Check and
supply that admissibility condition when assembling the problem API.

The older `exists_integralMinimizer_of_weakCesariProperty` in
`CesariCompactnessArgument.lean` proves only a fixed-interval integral minimizer,
without variable endpoint constraints or terminal cost. Use its infimum-comparison
pattern; do not rename it as the full book theorem.

### Cost shift helpers

`DynamicalSystems/OptimalControl/ContinuousTime/CesariCostShift.lean`:

- `shiftedVelocityCostSet` subtracts `β(t)` from the cost coordinate.
- `hasWeakCesariProperty_image_affineIsometryEquiv` transports the Cesari core.
- `hasWeakCesariProperty_shiftedVelocityCostSet` preserves weak property (Q)
  for arbitrary time-dependent shifts, with no time continuity hypothesis.

## All remaining work, in recommended order

### 1. Classical equi-AC → derivative uniform integrability

Define/use the real disjoint-interval trajectory condition: for each `ε>0` there
is one `δ>0` working for every sequence index and every finite disjoint family
inside the interval, with total interval length below `δ` implying
`Σ ‖x_n(b_i)-x_n(a_i)‖ < ε`.

Prove it implies `UnifIntegrable` for the actual L1 derivatives represented by
the integral laws. This is the missing uniform implication, not the easy
converse bound `‖∫v‖ ≤ ∫‖v‖`. In finite-dimensional states a coordinatewise
argument may be enough; make dimension constants explicit. A route using
variation of primitives and approximation of measurable sets by finite unions
of intervals needs both the integral/variation identity and the required
uniform estimate. Do not simply define “equi-AC” to mean `UnifIntegrable`.

Useful mathlib source to inspect:
`Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`,
`Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`,
bounded variation, differentiation, and measure regularity modules.
The existing interval-integral-to-AC result is a converse and does not close this.

### 2. Faithful admissible-pair API and source extensions

Represent original variable-endpoint admissible finite relaxed pairs, including
trajectory state-domain constraints, endpoint membership, measurable weights
and atoms, simplex normalization, actual integral dynamics, integrable costs,
and the full terminal objective. Define competitors and their actual objective
set. Use `N = d+2` for the book interpretation.

From an admissible minimizing sequence derive **all** inputs of the current
limit theorem:

- common compact time interval;
- constant trajectory extensions and zero derivative/cost extensions;
- ambient L1 integrability and correct original extended integral laws;
- equi-AC preservation by extension and then Step 1's uniform integrability;
- source compact-range membership and source endpoint constraints;
- actual interior epigraph membership and equality of source objectives.

Recover limiting all-time membership in the original closed time-state domain,
including endpoints. An interior eventual-membership proof plus continuity and
closedness, or clamped evaluation along source times, can supply it. Do not
replace the actual time-state compact set by an unrelated compactness certificate.

**Relative-domain regularity requires attention:** the current selector assumes
`Continuous f` on its whole ambient `T × E × U`. The book assumes continuity only
on `I × X × U`. Do not add global extendability as a new book hypothesis, or use
a closed state subtype as though it were a Hilbert vector space. Add a selector
variant using continuity on the original graph/domain (then the lift map is
continuous on its epigraph subtype), or prove an applicable extension theorem.
Similarly model the original open control domain as a sigma-compact subtype and
check the constraint graph is closed **relative to that domain**. Verify the
book's definition of upper semicontinuity supplies the required closed values;
our existing graph lemma takes both inputs explicitly.

### 3. Complete the general integrable lower-cost shift

Let `F(t)=∫_a^t β(s)ds`. Derive continuity of this primitive from integrability.
For each actual source interval define

```text
c_shift = c - β(t),
g_shift(t0,x0,t1,x1) = g(t0,x0,t1,x1) + F(t1)-F(t0).
```

Then the complete objective is unchanged. Prove source integral identities,
measurability and nonnegativity after the shift; transfer property (Q) using the
proved shift helper; pass the endpoint compensation continuously; undo the shift
in the limiting objective and actual admissible cost.

Crucial: `c - β(t)` need not be lower semicontinuous when `β` is merely integrable.
Do not feed an unjustified shifted lower semicontinuity hypothesis to the
selector. Recover an epigraph point for the original lower semicontinuous cost
and use the general integrable-lower-bound realization lemma already proved.
Also track artificial costs outside the moving source intervals: subtracting
`β` on the whole common interval changes those extensions. An ambient constant
shift without the outside contribution/endpoint correction can yield the wrong
bound. Keep the exact objective equality in the proof.

### 4. Infimum and final relaxed minimizer assembly

Define minimizing sequences against the actual feasible objective set. Establish
nonemptiness and a legitimate lower bound, or derive finiteness from the actual
compact-range minimizing sequence before using real `sInf`. Boundary `B` is
closed but is not assumed globally compact; terminal `g` can be unbounded below
away from the compact endpoint range. Do not silently assume global boundedness
of `g` or boundedness below of all costs without proving what is needed.

Instantiate the extraction/realization theorem, verify every admissibility
condition of the realized pair, and prove its objective ≤ every competitor's.
State `exists_relaxedMinimizer_of_weakCesariProperty` only at this point, with
`hcesari` indispensable to the limiting lower-closure/feasibility proof.

### 5. Ordinary-convexity conclusion and representation identities

Prove the needed finite-dimensional equality of the finite relaxed epigraph
(using `d+2` atoms) with the convex hull of the ordinary constrained epigraph,
handling cost slack and empty constraint fibers correctly. Reuse existing
Carathéodory/convexity lemmas where applicable. Under ordinary epigraph convexity,
realize the same limiting velocity/cost by an ordinary measurable control and
prove simultaneous optimality for both objective sets, as in Corollary 4.4.3.

The concrete finite-atomic weights-and-atoms representation is already available.
If the public theorem exposes the existing occupation-measure `RelaxedControl`
API, additionally construct the measurable finite-atomic kernel and occupation
measure, prove the fixed marginal and weighted integral identities, and account
for the probability normalization of restricted Lebesgue measure. Existing
`RelaxedControls.lean` is a probability-marginal API; the moving interval proof
uses unnormalized Lebesgue integrals. Do not identify those without the factor.

## Proof contract and completion gates

- No `sorry`, `admit`, new axioms, `native_decide`, or `proof_wanted`.
- Dependencies only in `{propext, Classical.choice, Quot.sound}`.
- No `@[nolint]` or linter-disabling options.
- All headline assumptions must have an actual mathematical role. In particular,
  no supplied weak convergence, feasible recovery, admissible-space compactness,
  or optimality certificate replacing the missing argument.
- Concept-named declarations; book provenance belongs in docstrings.
- Reuse existing results, preserve established signatures/docstrings, and use
  Lean lines at most 100 characters.
- Keep umbrella imports and `scripts/check_remaining_optimal_control.sh` wired.
- Run `lake env lean <new-or-modified-module>` with zero warnings.
- Run `lake build DynamicalSystems` and the check script successfully.
- Add `#print axioms` coverage for the new headlines and bridges.
- Record exact remaining gaps if a full bridge is still unproved; never report
  the full theorem as complete just because the analytic limit exists.

Latest proof checkpoint validation (before this docs-only handoff): full build
passed with 4256 jobs; check script passed; all 19 newest declarations were
audited, 189 dependency records overall, standard axioms only. New modules had
zero direct warnings; full builds replay older warnings. Audit files are
`DynamicalSystemsTest/R4CCompactness.lean`, `R4CMovingInterval.lean`, and
`R4CFiniteRelaxed.lean`.

## Suggested response/deliverables from GPT Pro

1. A faithful final Lean statement and admissible-pair/minimizing-sequence API.
2. Complete proofs of the missing bridges above, starting with classical equi-AC.
3. The assembled relaxed existence headline with load-bearing `hcesari`.
4. The ordinary-convexity corollary, or an exact residual gap if unfinished.
5. Build/axiom evidence if working in the repo; otherwise clearly label Lean
   snippets as proposals and give enough mathematical detail to implement them.

Earlier campaign tasks H2 (BM 6.3.22 horizontal-variation/free-terminal-time
transversality), H3 (BM 6.3.9 unbounded-control growth), and H4 (time-dependent
`G` primitive mismatch in the necessity-to-sufficiency bridge) were not worked on
in this R4c continuation. They are secondary to the requested BM 5.4.4 handoff;
inspect current main/dev before treating their historical gap reports as current.
