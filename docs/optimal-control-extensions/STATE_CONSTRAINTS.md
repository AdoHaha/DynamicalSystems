# State-constraint necessity — recovery checkpoint

Date: 2026-10-06. Starting library commit: `a6c03366e650afb3911b34bb2453ec11a0d87ef8`.

This continuation targets K6, particularly the necessary measure multiplier and BV adjoint rather than only a verification certificate. It preserves the existing K2/K7/K8 work and the integrated baseline.

## First compiled milestone

`OptimalControl.exists_path_measure_multipliers` derives a finite nonnegative measure and a nonnegative normal-or-abnormal cost multiplier from an actual constrained optimum of a convex problem with continuous pointwise-convex path constraints. The constraint index is an arbitrary compact Hausdorff space; it can represent a continuous horizon and finitely many constraint channels.

The proof constructs the achievable path/cost upper image, derives its convexity and a genuine interior point using strict slack, excludes strict feasible improvement, applies infinite-dimensional Hahn--Banach separation, proves positivity and nontriviality, and constructs the measure using Mathlib's Riesz--Markov theorem. It derives both integral complementarity and concentration on the active constraint set. No separator, measure, costate, constraint qualification, or Lagrangian optimality conclusion is supplied as input.

`path_costMultiplier_pos_of_slater` separately proves normality from actual strict feasibility. It does not divide by an unproved positive multiplier.

The regression theorem `PathConstraintTest.exists_interior_atom_multiplier` uses an infinite family of constraints `v ≤ (t-1/2)^2` with objective `-v`. It derives a strictly positive cost multiplier and a nonzero measure concentrated at the unique interior active point. This rules out replacing all state multipliers by ordinary Lebesgue densities.

Both production modules and the regression file compile under the pinned Lean 4.35.0-rc2/Mathlib environment. The four printed axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`. Run `bash scripts/check_state_constraint_pmp.sh`; the existing branch CI now invokes this script as well.

## Remaining within this continuation

The abstract path-constraint multiplier theorem is not by itself the full K6 PMP. The next step is to connect actual controlled integral trajectories to these hypotheses, construct a BV costate from the measure, and prove the adjoint and common-AE Hamiltonian conditions. General nonlinear nonconvex state-constraint PMP is not claimed at this checkpoint. No background job or future delivery is implied.
