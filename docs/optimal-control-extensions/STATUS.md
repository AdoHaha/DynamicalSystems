# Optimal-control extensions — current local checkpoint

Date: 2026-10-06. Baseline: `dev` at `69eb63f` (integrated bounded existence,
relaxation/recovery and structural finite switching). Current local branch:
`codex/remaining-optimal-control-proofs`. Nothing from this checkpoint is pushed
or merged into dev.

## Scope and proof inventory

The old checkpoint described an unavailable compiler and an earlier baseline.
This session uses the repository-pinned Lean 4.35.0-rc2 and actual local builds.
The previously integrated K2/K7/K8 results remain valid in their documented scope.

| Obligation | New local proof | Remaining boundary |
| --- | --- | --- |
| K2/K8 existence | `LinearGrowthProblem.exists_relaxed_minimizer_global` and `exists_ordinary_minimizer_global`: arbitrary finite horizon, primitive linear growth, derived Gronwall bound, radial localization, equivalence with original dynamics and all original competitors | Ordinary recovery still requires compact convex controls, control-affine dynamics and convex running cost; arbitrary nonconvex velocity-cost selection remains open |
| Endpoint/abnormal necessity | `exists_endpoint_multipliers` and `exists_ae_hamiltonian_endpoint_multipliers`: actual convex endpoint-integral optimality, nontrivial cost/endpoint pair, one common AE Hamiltonian minimum | General nonlinear trajectory PMP is not proved |
| K7 optimality connection | `hasAEFiniteSwitchesOn_of_linear_terminal_cost_minimizing`: actual measurable box-control minimum of the LTI terminal-response objective, nonzero linear terminal cost and per-input Krylov condition | Fixed horizon/free terminal; minimum-time reachable-boundary argument remains open |
| K6 multiplier extraction | `ConvexStateControlProblem.exists_measure_of_isMinimum`: actual affine-convex integral trajectories, finite positive constraint measures, complementarity, active-set support and unconstrained-dynamics penalized minimum; actual Slater pair proves normality | Hard terminal equalities are not included |
| K6 scoped necessity | `ConvexStateControlProblem.exists_integrator_state_pmp`: constructed BV costate, exact measure increments, terminal value and common AE Hamiltonian minimum from actual constrained optimality | Integrator dynamics, linear terminal cost, state-independent convex running cost and one affine state constraint |
| K6 general foundations | Constructed measure tails, BV, traces/atoms and propagated-costate mild balances; differentiation of actual integrals along bounded measurable affine variations under finite measures | Full affine-dynamics, spatially nonlinear convex-data PMP assembly and arbitrary nonlinear PMP remain open |

## Validation and semantic review

New production modules and regression files are checked locally with the pinned
compiler. `scripts/check_remaining_optimal_control.sh` records the combined build,
regressions, forbidden-proof-token scan and axiom checks. The umbrella imports
include these new modules on this work branch. Exact final build results are
recorded in `VALIDATION_REMAINING.md` after the combined check finishes.

Independent agents reviewed the growth extension, endpoint/switching scope and
K6 foundations. Reports and responses are under the parent workspace's
`notes/optimal_control_extensions/reviews/`. The requested external agy review
could not run because its account quota was exhausted; a submitted request is
not a completed review. Local compiler validation and agent reviews do not
constitute acceptance of the broader remaining campaign.
