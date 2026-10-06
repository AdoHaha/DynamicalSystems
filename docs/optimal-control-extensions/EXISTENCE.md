# End-to-end relaxed and ordinary optimal-control existence

Date: 2026-10-06. Namespace: `OptimalControl.BoundedContinuousProblem`.

## Proven final theorems

- `exists_relaxed_minimizer`: an optimal relaxed trajectory/control pair exists.
- `exists_ordinary_minimizer`: an optimal measurable ordinary trajectory/control pair exists in the compact-convex-control, control-affine-dynamics, convex-running-cost regime.

Both conclusions compare the constructed minimizer against **every admissible competitor**. The required nonemptiness is one actual feasible pair, which is necessary because an arbitrary endpoint constraint need not be reachable.

## Primitive hypotheses and exact scope

The horizon is any strictly positive finite real `T`. State space is finite-dimensional and real; controls form a compact metric space for the relaxed theorem. Dynamics and running cost are jointly continuous in time, state and control; terminal cost is continuous. Dynamics have an explicit **global uniform velocity bound**. Endpoint target and each time's state-constraint set are closed. No convexity is required of the target, state constraints, terminal cost, or state dependence.

For ordinary recovery, controls are a nonempty compact convex subset of a finite-dimensional real vector space. Dynamics are affine in control and running cost is convex in control. The algebraic `AffineConvexData` records the actual affine formula and a convex extension of the running cost; it does not contain a selector, realization, closure, or optimality premise.

The global velocity bound is an explicit restriction. This milestone does not claim the full linear-growth/local-coercivity Filippov theorem or arbitrary nonconvex velocity-cost epigraph selection. A general LTI field `A x + B u` with nonzero `A` is not globally bounded in state, so applying this theorem to it requires a separately justified bounded extension/localization, not silently dropping the bound.

## Complete proof chain

1. `ControlHorizon` constructs normalized Lebesgue probability on `[0,T]`, proves its total mass, exact interval masses, rescaling to subtype Lebesgue volume, and pushforward to ordinary restricted real Lebesgue measure. Dynamics undo the normalization by multiplying the occupation integral by `T`.
2. `IsRelaxedTrajectory` is the actual Volterra equation at **every time**, not a terminal or moment constraint. It implies the initial condition.
3. `IsRelaxedTrajectory.lipschitzWith` derives a uniform Lipschitz bound from bounded velocities and the exact time marginal.
4. Generic `BoundedContinuousFunction.isCompact_lipschitzPaths` proves Arzelà–Ascoli compactness of the fixed-initial-value path tube.
5. `isClosed_relaxedTrajectoryGraph` uses the previously proved joint time-restricted occupation integral continuity. Therefore the actual dynamics graph is closed under uniform trajectory and weak control convergence.
6. `isCompact_relaxedTrajectoryGraph` and `isCompact_relaxedAdmissible` derive compactness of the full feasible set, including closed endpoint/state constraints.
7. The objective is jointly continuous, so the genuine feasible pair and the extreme-value theorem give a relaxed minimizer.
8. Disintegration/barycentric recovery constructs a measurable ordinary control, preserves the whole trajectory and all constraints, and does not increase cost by Jensen. All ordinary and relaxed integrability obligations are derived from primitive compact continuous data.
9. Every ordinary competitor embeds as its graph measure with the same dynamics and exactly the same objective. This yields ordinary global optimality.

## Validation and campaign status

All production modules compile with pinned Lean 4.35.0-rc2/Mathlib. `DynamicalSystemsTest/ControlExistence.lean` builds a concrete box-constrained scalar integrator with quadratic effort cost, supplies an actual feasible control/path, and applies the ordinary existence theorem. Its five central axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`.

This completes K2 existence and K8 closure/disintegration/recovery **for the stated bounded continuous and convex-affine regime**, with no target-shaped analytic assumption left over. It does not mark a broader campaign requirement automatically satisfied. K6 necessity, nonlinear measurable PMP, and abnormal-multiplier existence are separate from existence of optimizers.

Reproduce: `bash scripts/check_optimal_control_extensions.sh`.
