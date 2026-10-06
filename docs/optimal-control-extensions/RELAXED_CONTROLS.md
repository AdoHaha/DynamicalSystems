# Relaxed-control compactness, integration and ordinary-control recovery

Date: 2026-10-06. This is a compiled intermediate milestone for K8/K2, not yet an optimal-control existence theorem.

## Actual results

`OptimalControl.RelaxedControl` is the space of probability occupation measures on time × control with a prescribed time marginal. Its weak compactness is derived for compact metric time/control spaces, by proving the marginal constraint closed and applying probability-measure compactness. No compact feasible trajectory space is assumed.

Every measurable ordinary control embeds as its actual graph measure. Conversely, `kernel` constructs a Markov disintegration and `disintegrate`, `integral_kernel`, and `setIntegral_kernel` prove reconstruction and full/restricted-time Bochner integral identities.

`continuous_setIntegral_param` proves joint continuity of actual time-restricted occupation integrals when a continuous parameter-dependent vector field and the weak occupation measure both vary. The proof does not apply weak convergence directly to a discontinuous indicator. Instead, continuous time weights approximate any integrable weight in L1 of the **fixed time marginal**, with an error estimate uniform over all occupation measures. Finite-dimensional vector coordinates then give the Bochner-valued result. This supplies the analytic closure step for Volterra dynamics.

For a compact convex control set in a finite-dimensional real vector space, `recoveredControl` is the conditional barycentre. Its measurability and membership in the original control set are proved. `setIntegral_affine_eq_recovered` preserves every restricted-time control-affine dynamics integral, and `integral_convex_cost_recovered_le` proves that continuous convex running costs do not increase. No measurable selector or recovery conclusion is supplied as input.

## Scope boundaries

Ordinary recovery is for **convex controls, control-affine dynamics, and convex running costs**. It is not arbitrary nonconvex purification or a general Filippov velocity-cost epigraph selection theorem. The integrated cost comparison currently retains ordinary integrability premises on the actual functions; an OCP-level existence theorem must discharge them from its primitive data.

This milestone supplies weak compactness, disintegration, the restricted-time closure tool, and a proved recovery mechanism. Compactness of bounded solution paths, the closed feasible trajectory graph, and final minimizer extraction are still distinct steps. It does not mark all K2/K8 completed.

## Validation

The three production modules and `DynamicalSystemsTest/RelaxedControls.lean` compile locally under pinned Lean 4.35.0-rc2 and Mathlib. The test file checks a compact interval control space, membership of its recovered barycentre, measurable subtype-valued recovery, and prints axioms for six principal results. All use only `propext`, `Classical.choice`, and `Quot.sound`.

Run `bash scripts/check_optimal_control_extensions.sh` for explicit module builds and regression tests, in addition to the branch CI's library build and axiom audit. No placeholder or new axiom was introduced.
