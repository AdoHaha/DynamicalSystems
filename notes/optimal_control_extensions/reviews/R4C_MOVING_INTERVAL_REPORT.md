# R4c continuation: moving intervals and the terminal objective

Worktree: `/home/igor/zabawy/auto_automatyk/.worktrees/r4c-worker`.
Branch: `remaining-optimal-control-r4c-worker`. Starting commit: `4ead5e0`.

## Status

The strongest new result is
`OptimalControl.exists_limit_endpoints_objective_epigraph_of_unifIntegrable`.
It extracts a uniform trajectory limit, weak L1 velocity convergence, limiting
endpoint times satisfying the actual closed boundary constraint, the integral
law on the limiting interval, and an integrable feasible cost epigraph whose
**terminal plus running objective** is at most the limiting sequence objective.
Property (Q) is assumed only on the actual compact time-state set `R` and is used
in the Mazur/Fatou lower-closure proof.

This is a proved analytic step toward BM Theorem 5.4.4. It is not yet a relaxed
minimizer: the source sequence is supplied as constant-extended paths, L1
velocities, and running costs with their actual laws. A concrete finite-atomic
relaxed problem and the realization/infimum assembly remain to be constructed.
`exists_relaxedMinimizer_of_weakCesariProperty` is not declared.

## Book anchors

Berkovitz–Medhin, *Nonlinear Optimal Control Theory* (2012), cached
`papers/text/berkovitz_medhin_nonlinear_optimal_control.txt`:

- Theorem 5.4.4, line 6352; Assumption 5.4.1, line 6299.
- Step 1, lines 6750–6832, equations (5.4.26)–(5.4.27): common interval,
  endpoint extraction, constant trajectory extensions and limiting law.
- Step 2, lines 6833–6845: terminal-cost lower bound and running-cost subsequence.
- Step 3, lines 6847–6969, equations (5.4.28)–(5.4.32): eventual interior
  feasibility, property (Q), Mazur/Fatou lower closure.
- Step 5, lines 7006–7046, equation (5.4.33): terminal objective comparison.

## Declarations and reuse

### `CesariExistenceArgument.lean`

Five new eventual-membership variants:

- `mem_of_weakCesariProperty_of_eventually_mem_of_tail_convexHull`
- `velocityCost_liminf_mem_of_weakCesariProperty_of_eventually_mem`
- `ae_velocityCost_liminf_mem_and_lintegral_le_of_eventually_mem`
- `exists_integrable_cost_epigraph_of_cesari_combinations_of_eventually_mem`
- `exists_integrable_cost_epigraph_of_weak_Lp_tendsto_of_eventually_mem`

The finite infeasible prefix may depend on time. The pointwise proof discards
that prefix and reuses the original Cesari tail lemma. The existing Fatou/Mazur
engine is generalized once; the four original theorem signatures and docstrings
are preserved as corollaries of the generalized engine.

### `MovingIntervalCompactness.lean`

Namespace `DynamicalSystems.EquiIntegrableTrajectories`:

- `eventually_mem_Ioo_of_endpoint_tendsto`
- `const_on_outer_intervals_of_uniform_tendsto_endpoints`
- `integral_difference_law_on_subinterval`
- `exists_uniform_limit_endpoints_weak_L1_integral_law`

These reuse `exists_uniform_limit_weak_L1_tendsto_integral_law` rather than
re-proving weak compactness. Compact endpoint pairs yield a further subsequence;
joint endpoint evaluation and closedness preserve the real boundary set. Its
strict-time condition proves positive limiting duration. The ambient primitive
is restricted to obtain the actual limiting interval law.

### `CesariMovingInterval.lean`

Namespace `OptimalControl`:

- `hasWeakCesariProperty_congr_at_time`
- `hasWeakCesariProperty_const_of_isClosed_of_convex`
- `mem_state_projection_of_constant_extension`
- `exists_limit_endpoints_cost_epigraph_of_unifIntegrable`
- `exists_runningCost_tendsto_subseq_of_tendsto_totalCost`
- `terminalCost_add_le_of_tendsto_totalCost`
- `exists_limit_endpoints_objective_epigraph_of_unifIntegrable`

Compactness of the actual time-state set supplies its compact state projection.
Source membership is required only on each source interval. Constant extensions
supply the global state range. Closedness then puts the limiting time-state pair
in `R` at each interior limiting time. Endpoint convergence gives eventual
source epigraph feasibility there. Outside the limiting interval, an auxiliary
constant closed convex halfspace supplies nonnegative cost lower closure.
The generalized weak-Lp epigraph theorem gives the limiting cost; nonnegativity
outside permits restriction without increasing its integral.

For the objective theorem, compact endpoint data and lower semicontinuity of
`g` give a lower bound for terminal costs. Convergence of total objectives and
nonnegative running costs produce a convergent running-cost subsequence.
Closed epigraph membership of `g` gives the final terminal comparison.

## Load-bearing inputs

| Input | Proof use |
| --- | --- |
| Compact time-state `R`, original membership | Compact state projection for Ascoli; closedness gives actual limiting membership. |
| Constant source extensions | Global compact state range and limiting constancy outside the interval. |
| Original integral law and `UnifIntegrable` velocities | Uniform extraction, weak L1 convergence, and the actual limiting integral law. |
| Closed boundary `B`, positive duration on `B` | Joint endpoint limit remains admissible and has positive duration. |
| `hcesari` on `R` | Converts Cesari-core membership into actual interior cost-epigraph feasibility. |
| Original interior epigraph membership | Eventual membership for the tail lower-closure argument. |
| Nonnegative integrable source costs | Fatou, running-cost subsequence, and restriction of the limiting cost bound. |
| Lower semicontinuous terminal `g` | Compact lower bound and closed-epigraph terminal comparison. |
| Convergent total objective | Produces running-cost subsequence and final objective upper bound. |

No weak-limit, feasible-recovery, or optimality certificate is assumed.

## Exactly what remains for full relaxed existence

1. Prove that the book's finite-disjoint-interval **equi-AC** trajectory condition
   gives `UnifIntegrable` of the L1 derivatives. The current input is uniform
   absolute continuity of derivative norm integrals.
2. Define a faithful noncompact, state-dependent, variable-endpoint relaxed
   problem. From its actual admissible pairs construct the constant trajectory
   and zero velocity/cost extensions, proving their original integral laws,
   integrability, equi-integrability, and objective identification. The analytic
   endpoint extraction and terminal comparison themselves are now proved.
3. Construct the finite simplex/atom domain and identify its image with the
   constrained relaxed epigraph. Derive its closedness and sigma-compactness
   from the constraint data, continuity of weighted velocity, and lower
   semicontinuity of weighted cost. Instantiate the existing measurable selector
   to obtain weights and atoms satisfying the actual dynamics/cost identities.
   An occupation-measure interface additionally needs the finite-atomic kernel,
   marginal, and integral identities.
4. Handle the general integrable lower bound `f0 ≥ β(t)`: epigraph translation,
   preservation of property (Q), undoing the measurable cost shift, and the
   continuous primitive's endpoint compensation. The unshifted nonnegative
   running-cost and lower semicontinuous terminal comparison is now proved.
5. Produce the minimizing sequence from the actual feasible relaxed-cost set,
   realize the limit as an admissible relaxed pair, and compare against every
   competitor. Under ordinary epigraph convexity, also prove the ordinary
   conclusion. The full relaxed headline remains open.

H2/H3/H4 were not attempted in this continuation.

## Verification and repository handling

- `lake build DynamicalSystems`: exit 0, 4253 jobs.
- `scripts/check_remaining_optimal_control.sh`: exit 0; includes direct
  `lake env lean` zero-warning checks of both new modules and the modified
  Cesari engine, forbidden-token checks, and the new audit file.
- All 16 new declarations audited. The complete script has 170 axiom records;
  every dependency set is contained in `{propext, Classical.choice, Quot.sound}`.
- Umbrella imports and check-script targets are wired. No proof escapes or
  linter suppressions were added. `git diff --check` passed.
- Logs: `.lake/r4c-moving-build.log` and `.lake/r4c-moving-check.log` (ignored).
  Full builds replay warnings from older modules; the direct checks above are clean.

Preexisting worktree deletions of `HARD_REPORT.md` and `R4C_REPORT.md` are
preserved and excluded from this commit. The required canonical `R4C_REPORT.md`
in the main workspace is updated; this new report is the committed snapshot.
