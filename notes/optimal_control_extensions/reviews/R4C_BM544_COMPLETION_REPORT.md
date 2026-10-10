# R4c — BM Theorem 5.4.4 assembled from actual admissible pairs

## Result

`OptimalControl.exists_relaxedMinimizer_of_weakCesariProperty` proves existence
of an actual `FiniteRelaxedAdmissiblePair N P` whose original terminal-plus-running
objective is no larger than that of **every** admissible competitor. Its source
is an actual classical equi-absolutely-continuous minimizing sequence, with
trajectories in a compact original time-state set. No supplied weak limit,
uniform-integrability certificate, limiting feasibility, objective limit, or
optimality certificate occurs in the headline.

`exists_ordinaryMinimizer_of_weakCesariProperty_of_convex` proves the convexity
conclusion: the returned pair uses a measurable ordinary control repeated in
all atom slots; its velocity and running cost are exactly the original ordinary
dynamics and cost, and it minimizes over all admissible relaxed competitors.
Ordinary controls are included as repeated-atom relaxed controls.

These statements use the book's finite-atomic relaxed representation, not a
separate occupation-measure representation. For BM's finite-dimensional state
space set `N = Module.finrank ℝ E + 2`. The imported
`finiteRelaxedVelocityCostSet_eq_convexHull` identifies precisely this epigraph
with the convex hull of the ordinary epigraph. No dimension condition is needed
for existence in an explicitly fixed finite-atom problem.

## Book anchors and assumptions

Berkovitz–Medhin, *Nonlinear Optimal Control Theory* (2012): Assumption 5.4.1,
Definition 5.4.2, Theorem 5.4.4, Remark 5.4.13, and proof Steps 1–5,
particularly (5.4.29)–(5.4.33). Cached text lines approximately 6299, 6318,
6352, 6679, and 6750–7046. The cached edition labels the theorem page 124;
use the theorem number rather than an offset from another edition.

The problem is stated over the original closed control graph, with dynamics
continuous and running cost lower semicontinuous **on that graph**. Controls
need only be sigma-compact, not compact. An open Euclidean control domain can
be modeled as the ambient control type. The existing
`isClosed_controlGraph_of_upperHemicontinuous` supplies graph closedness from
upper hemicontinuity and closed fibers. The terminal boundary is closed and
has positive duration; its terminal cost is lower semicontinuous there. The
running cost has a merely integrable time-dependent lower bound.

The headline generalizes the state space to a complete Hilbert space with the
Borel, sigma-compact, and second-countability structures needed by the existing
analytic and measurable-selection APIs. Euclidean spaces satisfy these inputs.

## New declarations and actual proof chain

File: `OptimalControl/ContinuousTime/CesariRelaxedMinimizer.lean`.

1. `exists_admissibleRelaxedPair_objective_le`: given actual equi-AC admissible
   pairs and a convergent objective sequence, constructs an actual admissible
   pair with objective at most the limiting value.
2. `IsRelaxedMinimizingSequence`: eventual comparison with every actual
   competitor, up to each positive tolerance. This is the usual minimizing
   sequence condition without assuming a finite infimum beforehand.
3. `exists_relaxedMinimizer_of_weakCesariProperty`: derives a finite objective
   cluster point from compact source endpoint data and the minimizing condition;
   applies the limiting-pair theorem to a subsequence; compares its objective
   with every admissible competitor.
4. `exists_ordinaryRelaxedPair_objective_le`: pointwise ordinary epigraph
   convexity and relative-domain selection produce a measurable ordinary
   control along the same trajectory with no larger objective.
5. `exists_ordinaryMinimizer_of_weakCesariProperty_of_convex`: applies ordinary
   recovery to the relaxed minimizer and preserves global minimality.

Actual source paths, L1 velocities, shifted costs, extension laws, integrability,
and objective identities come from `FiniteRelaxedSourceSequence`. Classical
finite-disjoint-interval equi-AC yields uniform integrability through
`unifIntegrable_extendedVelocityLp_of_equiAC`; weak-L1 extraction, primitive-law
passing, moving endpoints, Mazur/Fatou and lower closure reuse
`CesariCompactnessArgument`, `CesariExistenceArgument` and `CesariMovingInterval`.

The merely integrable lower bound is subtracted before zero extension. Its
continuous primitive compensates the terminal objective. Weak property (Q) is
transported by the fixed-time affine cost translation and used in the actual
lower-closure theorem. Original cost epigraph membership is then restored;
selection uses the original lower semicontinuous cost, never an unsupported
continuity assumption on the shifted cost. Integration restores the original
objective exactly.

The supplied draft `mem_closed_timeStateSet_of_uniform_tendsto_endpoints` is now
kernel-checked and reused in source state feasibility. It preserves the original
time-state set at every limiting active time, including both endpoints. The
new admissible pair has the actual integral dynamics, original state constraint,
original control graph, integrable velocity/cost, and original boundary data.

## Load-bearing hypotheses

| Input | Proof use |
| --- | --- |
| Actual admissible source pairs | Derive extensions, velocities, source feasibility, integrability, laws, boundary and objective identities. |
| Classical equi-AC | Derive uniform integrability needed by weak-L1 compactness. |
| Compact original time-state range | Ascoli/state compactness, all-time limiting state membership and compact endpoint lower bound. |
| Range inclusion in original state domain | Establish limiting pair's original state feasibility; enables ordinary convexity along its path. |
| `hcesari` | Recover actual limiting relaxed epigraph from Mazur/Fatou Cesari-core membership. |
| Closed original graph | Closed finite graph and sigma-compact measurable epigraph realization. |
| Relative continuous dynamics | Continuous realization map; actual selected velocity identity. |
| Relative lower semicontinuous cost | Closed original epigraph, selected cost measurability and integrability. |
| Integrable lower bound | Nonnegative shifted source costs; original selected cost integrability; exact objective restoration. |
| Closed positive-duration boundary | Endpoint feasibility and nonzero limiting interval measure. |
| Lower semicontinuous terminal cost | Compact lower bound and limit objective comparison after primitive compensation. |
| Minimizing sequence condition | Eventual upper objective bound, finite cluster point and comparison with every competitor. |
| Ordinary epigraph convexity | Conversion of relaxed membership to ordinary membership before measurable ordinary recovery. |

## Integration and repairs

- Wired the new theorem and all newer source/equi-AC/relative-selection helper
  modules into the umbrella and check script, with alphabetical umbrella blocks.
- The script directly checks the new modules with zero warnings and audits the
  new headlines in `DynamicalSystemsTest/R4CMinimizer.lean`.
- Repaired source shifted-epigraph indicator unfolding, removed a deprecated
  continuity API and an unused section instance, preserving explicit theorem
  statements and existing docstrings.
- The proof-escape scan now excludes nested Lean block comments and line
  comments: the ordinary English word “admit” in a selector docstring is not
  the Lean tactic. It still rejects proof escapes in code.

## Verification

- `lake build DynamicalSystems`: exit 0, 4285 jobs, including a final rebuild
  after alphabetical umbrella wiring.
- `scripts/check_remaining_optimal_control.sh`: exit 0. Direct Lean checks of
  new/modified hard modules and newly wired source/equi-AC/selection helpers
  completed with zero warnings.
- The complete log contains 200 axiom dependency records, all contained in
  `{propext, Classical.choice, Quot.sound}`. Six additional direct audit records
  cover the five new declarations and the dimension-dependent convex-hull identity.
- No proof escapes or linter suppressions were added; the code scan passed.
  `git diff --check` passed, and all new Lean lines satisfy the 100-column limit.
- Ignored logs: `.lake/r4c-full-minimizer-check.log`,
  `.lake/r4c-headline-axioms.log`, `.lake/r4c-bm544-umbrella.log`.
  Full builds replay warnings from older modules; the direct hard gates are clean.

## Exact remaining scope

No BM 5.4.4 assembly or ordinary-convexity proof obligation remains in this
finite-atomic formulation. A separate public occupation-measure adapter
(kernel/marginal/integration identities) has not been added; BM's theorem and
this proof use finite measurable weights and atoms directly.

H2 (BM 6.3.22 horizontal time variation/transversality), H3 (BM 6.3.9 unbounded
controls), and H4's R1-to-R6b bridge remain separate campaign tasks. This
continuation makes no claim to close them or merge the worker branch into `dev`.
Preexisting deletions of the worktree's `HARD_REPORT.md` and `R4C_REPORT.md`
remain unstaged; the required canonical main-workspace `R4C_REPORT.md` is updated
separately, and this file is the committed completion snapshot.
