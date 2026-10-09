# R4c proof report

## Status and provenance

Worktree: `/home/igor/zabawy/auto_automatyk/.worktrees/r4c-worker`.
Branch: `remaining-optimal-control-r4c-worker`, base `eedefe0`, preserved WIP
`5069820`. This report describes the subsequent validated completion commit.

**Partial completion.** The weak L1 compactness crux, actual limiting integral law,
noncompact epigraph selection, and a genuine fixed-interval integral minimizer
are proved. The full variable-endpoint, finite-atomic relaxed BM 5.4.4 headline
`exists_relaxedMinimizer_of_weakCesariProperty` is **not proved or declared**.
The fixed-interval minimizer has its own accurate name and admissibility predicate.

Source read: Berkovitz–Medhin, *Nonlinear Optimal Control Theory* (2012), complete
§§5.3–5.4, cached `papers/text/berkovitz_medhin_nonlinear_optimal_control.txt`.
Exact anchors: Definition 5.3.1 at line 6006; Theorem 5.3.5 at 6078;
Assumption 5.4.1 at 6299; Theorem 5.4.4 at 6352; its proof at 6750;
(5.4.27) at 6777, Step 3 and (5.4.28)–(5.4.32) at 6847–6969;
Steps 4–5 at 6971–7046. The cached page headers place the existence proof on
printed pp. 132–137. No assertion from the erroneous uniform-convergence claim
in Remark 5.3.4 is used.

## New proof chain

### `Mathlib/MeasureTheory/WeakL1Compactness.lean`

Namespace `DynamicalSystems.WeakL1`:

- `exists_weak_clusterPoint_of_uniform_norm_approximation`: in a complete real
  normed space, weakly compact approximations with uniformly vanishing norm
  errors yield an actual weak cluster point. A common ultrafilter selects the
  approximating weak limits; norm bounds make those limits Cauchy.
- `l2ToL1`, `l2ToL1_coeFn`, `isCompact_weak_l2ToL1_closedBall`: continuous linear
  inclusion on a finite measure space and weak compactness of its ball images.
- `exists_weak_L1_clusterPoint_of_uniformIntegrable`: uniformly integrable L1
  sequences with values in a complete real Hilbert space have weak L1 cluster
  points. Bounded truncations provide the L2 approximations. **No L2 bound on the
  original velocities is an input.**
- Helpers: `norm_le_of_weak_tendsto`,
  `dual_apply_eq_of_weak_clusterPoint_of_tendsto`.

This supplies the missing compactness mechanism for BM 5.4.4 Step 1. It reuses
merged `WeakL2.isCompact_toWeakSpace_image_closedBall` only for the truncations.
The general theorem concludes a cluster point; sequential weak convergence is
proved next using the actual primitive trajectories.

### `Mathlib/MeasureTheory/EquiIntegrableTrajectories.lean`

Namespace `DynamicalSystems.EquiIntegrableTrajectories`:

- `uniformIntegrable_of_unifIntegrable_on_interval`: derives the global L1 bound
  by a finite cover of the interval. This is equation (5.3.1); no extra global
  norm-bound hypothesis is required.
- `equicontinuous_of_unifIntegrable_integral_law` and
  `exists_uniform_tendsto_subseq_of_unifIntegrable_integral_law`: derive
  equicontinuity from small derivative integrals, then uniform subsequential
  convergence by mathlib Arzelà–Ascoli.
- `setIntegralCLM`, `setIntegralCLM_apply`,
  `setIntegral_eq_of_weak_clusterPoint_of_tendsto`: continuous linear L1
  integration transfers the original dynamics to the limit.
- `eq_of_setIntegral_Ioc_eq`: Lebesgue differentiation proves uniqueness of L1
  velocities from their indefinite integrals.
- `weak_L1_tendsto_of_unifIntegrable_of_integral_law_limit`: proves the
  sufficiency direction of BM 5.3.5 in the derivative-integral formulation.
  Every subsequence has a weak cluster point with the same primitive; uniqueness
  gives convergence against every continuous linear functional on L1.
- `exists_uniform_limit_weak_L1_clusterPoint_integral_law` and the stronger
  `exists_uniform_limit_weak_L1_tendsto_integral_law`: jointly construct a uniform
  trajectory subsequence, weak L1 velocity convergence, and the limiting law.

These are genuine fixed-interval Step 1 results. `UnifIntegrable` is the mathlib
formulation of uniformly absolutely continuous **norm integrals** of velocities,
not a supplied weak-limit certificate. The finite-disjoint-interval definition
of equi-AC trajectories has not yet been bridged to this hypothesis.

### `Mathlib/MeasureTheory/MeasurableEpigraphLift.lean`

Namespace `DynamicalSystems.MeasurableLift`:

- `exists_measurable_ae_lift_of_continuous_sigmaCompact`: extends the merged
  measurable lift to a.e. range membership. The good source set is measurable
  because the continuous image is a countable union of compact sets.
- `constrainedVelocityCostSet`: uses the actual time/state/control graph.
- `exists_measurable_control_of_constrained_epigraph`: derives closedness of
  the cost epigraph from a closed constraint graph and lower semicontinuous
  cost; derives sigma-compactness of its subtype; applies the merged lift and
  obtains measurable controls, actual velocity equality, and cost domination.

This proves the generic noncompact selection mechanism in Step 4. The control
space is sigma-compact, not assumed compact. It has not yet been identified
with BM's simplex and finite control tuples.

### `OptimalControl/ContinuousTime/CesariCompactnessArgument.lean`

Namespace `OptimalControl`:

- `intervalPathValue`, `intervalPathValue_of_mem`,
  `measurable_intervalPathValue`: ambient real-line trajectory representatives.
- `exists_limit_trajectory_cost_epigraph_of_unifIntegrable`: constructs the
  trajectory, velocity, limiting law, integrable feasible cost epigraph, and
  integral bound. The derived weak convergence feeds the **merged**
  `exists_integrable_cost_epigraph_of_weak_Lp_tendsto` directly.
- `exists_limit_control_of_unifIntegrable_constrained_epigraph`: joins this
  extraction to noncompact selection. It constructs a measurable control,
  graph admissibility, actual integral dynamics, integrable velocity and cost,
  and the limiting cost bound. Nonnegativity of the sequence costs is derived
  from the primitive graph cost bound.
- `IsConstrainedIntegralPair`, `constrainedIntegralCostValues`: actual measurable
  control/trajectory admissibility and the costs of **all** such competitors.
- `exists_integralMinimizer_of_weakCesariProperty`: from an admissible minimizing
  sequence with compact range and equi-integrable velocities, constructs an
  admissible pair and proves its cost no greater than that of every competitor.
  The infimum is taken over the actual predicate, not an abstract optimum
  certificate. Nonnegative graph costs prove boundedness below by zero.

The last theorem is a genuine minimizer theorem, but is for a fixed interval,
nonnegative running cost, no terminal cost or prescribed endpoint set, and a
specified sigma-compact control space. It does not assert BM relaxed existence.

## Load-bearing hypotheses and reuse

| Input | Actual use |
| --- | --- |
| Complete real Hilbert velocity space; finite measure | Truncation L2 weak compactness, Banach completeness, and L2→L1 inclusion. |
| `UnifIntegrable` | Finite-cover global bound, small-interval equicontinuity, weak cluster extraction on every reindexed sequence. |
| Compact state set and values in it | Arzelà–Ascoli and preservation of limiting state range. Compactness of an admissible-pair space is not assumed. |
| Original integral dynamics | Derived limiting primitive, uniqueness of velocity, and weak convergence. |
| `hcesari` | Limiting-state property (Q) enters the merged Mazur/Fatou lower-closure proof, where Cesari-core membership becomes actual epigraph feasibility. This is required by selection and admissibility, not a by-product. |
| Original epigraph membership | Common-tail combinations and Fatou feasible lower closure. |
| Integrable sequence costs and convergence | Fatou integral bound; the minimizer theorem uses convergence to the actual feasible-cost infimum. |
| Closed control graph, continuous dynamics, lower semicontinuous cost | Closed sigma-compact epigraph domain, continuous realization map, measurable realized cost. |
| Sigma-compact control/state spaces | Compact-exhaustion measurable selection. No inverse/recovery certificate is supplied. |
| Positive interval length | Nonzero restricted Lebesgue measure supplies a nonempty epigraph domain for selection. |
| Nonnegative graph cost | Fatou's sign hypothesis, integrability of realized cost, and a proved lower bound for the feasible-cost infimum. |
| Admissible minimizing sequence | Provides the original integral laws and integrability, and the comparison with the actual infimum. |

Reused merged declarations: weak Hilbert ball compactness; all common Mazur tail
weights, a.e. extraction, Cesari membership, liminf/Fatou, and integrable epigraph
machinery in `CesariExistenceArgument`; and
`exists_measurable_lift_of_continuous_sigmaCompact`. No merged theorem was
re-proved or renamed to imply completion of the full headline.

## Exactly what remains for the full BM 5.4.4 headline

1. **Book equi-AC input.** Prove that the finite-disjoint-interval definition
   (Definition 5.3.2) for the admissible trajectories gives `UnifIntegrable` of
   their L1 derivatives (Definition 5.3.1), and instantiate the integral-law
   representation. The present theorems start with derivative norm integrals.
2. **Faithful relaxed problem API.** Define variable `t0 < t1`, closed boundary
   set `B`, lower semicontinuous terminal cost `g`, graph constraints from the
   upper semicontinuous `Ω`, and finite relaxed controls with simplex weights
   and `n+2` atoms in `Ω(t,x)`. The existing `LinearGrowthProblem` still assumes
   compact controls and a fixed horizon; it cannot directly instantiate this.
3. **Moving intervals and endpoints (Step 1).** Prove extraction of endpoint
   times, constant extension of paths, zero extension of velocities and costs,
   preservation of equi-integrability, the original extended integral law,
   limiting constancy outside the limiting interval, and limiting membership
   in `B` using joint endpoint evaluation. Only the fixed interval law is done.
4. **Eventual feasibility (Step 3).** On the interior of the limiting interval,
   original epigraph membership holds only eventually for each time. The
   merged cost theorem currently requires membership for every sequence index
   a.e. Generalize the tail-membership lower-closure step to this eventual
   input and prove the interval-restriction/zero-extension cost bound.
5. **Finite-atomic realization (Step 4).** Prove equality of the constrained
   relaxed epigraph with the image of the concrete simplex/atom/cost-slack
   domain, its closedness and sigma-compactness from BM's data, continuity of
   its velocity map, and lower semicontinuity of weighted cost. Instantiate
   the new measurable epigraph selector to obtain measurable weights and atoms
   and their actual weighted dynamics/cost identities. If exposing occupation
   measures, build the finite-atomic kernel/measure and prove its marginal and
   integral identities; this construction is not present yet.
6. **General lower bound and terminal objective (Steps 2/5).** Handle
   `f0 ≥ β(t)` with merely integrable `β`, prove the measurable shift of
   property (Q), the endpoint-dependent compensation via the continuous
   primitive of `β`, and the required bounded cost subsequence. Then pass `g`
   to the limiting endpoints by lower semicontinuity and compare the complete
   relaxed objective with its minimizing infimum. The current minimizer
   theorem covers only unshifted nonnegative running cost on a fixed interval.
7. **Ordinary conclusion.** Under convexity of the ordinary constrained
   epigraph, instantiate measurable ordinary realization and show simultaneous
   optimality for the ordinary and relaxed objectives.

These are unproved bridges, not hypotheses hidden in the new headlines. The
requested full declaration has not been replaced with compactness, recovery, or
optimality assumptions. H2(a), H3, and H4+ were not attempted; the primary full
R4c task remains open.

## Verification

The four new modules are wired alphabetically into `DynamicalSystems.lean` and
included in `scripts/check_remaining_optimal_control.sh`, including its direct
zero-warning gate. `DynamicalSystemsTest/R4CCompactness.lean` prints dependencies
for all 28 new declarations, including the minimizer headline.

Final verification passed:

- `lake build DynamicalSystems`: exit 0, 4251 jobs.
- `scripts/check_remaining_optimal_control.sh`: exit 0, including the umbrella
  build, all extension targets, direct zero-warning checks of all four new
  modules, forbidden-token/linter-suppression checks, and dependency audits.
- Separate forbidden-token and linter-suppression searches in all four new
  modules and the new audit file: no matches. All new Lean lines are at most
  100 characters. `git diff --check`: clean.
- All 28 new declarations were checked by `#print axioms`. The script audited
  154 declarations overall; every dependency set is a subset of
  `{propext, Classical.choice, Quot.sound}`.

Full builds replay existing warnings in older modules. The direct Lean checks
of the four new modules emitted zero warnings; no linter suppression was used.
Build/check logs are in the worktree's ignored `.lake/r4c-build.log` and
`.lake/r4c-check.log`.
