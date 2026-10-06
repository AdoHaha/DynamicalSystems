# State-constraint necessity and BV costates — live proof checkpoint

Date: 2026-10-06. Starting branch commit: `a6c03366e650afb3911b34bb2453ec11a0d87ef8`.

The next task is K6's state-constraint multiplier/BV-costate problem. Existing endpoint, relaxed-existence and finite-switch results are not being relabelled as its solution.

## Planned first necessary-condition scope

For a genuine constrained minimum with a convex attainable cost/state-residual upper image in `R × C(time,R)`, derive a nontrivial nonnegative cost multiplier and positive continuous functional by geometric Hahn–Banach. Construct the finite positive Borel measure using Riesz–Markov; prove complementary slackness and that the measure vanishes off the active constraint set. Keep abnormal multipliers unless an actual constraint qualification proves positivity. Then construct and check the BV costate contribution, with endpoint and atom conventions explicit.

The desired input is primitive convexity and actual optimality, not a supplied separator, positive functional, measure, Lagrangian minimum, or BV certificate. A scoped convex necessary theorem is distinct from the full nonlinear measurable needle-variation PMP; the final status must state which is proved.

## Reuse found

- Existing library `NeedleSeparation` and `Mathlib/Analysis/LocallyConvex/Separation`: geometric Hahn–Banach.
- Pinned Mathlib `MeasureTheory/Integral/RieszMarkovKakutani/Real`: constructs representing measures of positive real linear functionals.
- Pinned Mathlib `MeasureTheory/VectorMeasure/BoundedVariation` and `IntegrationByParts`: vector-valued Stieltjes measures, one-sided jump conventions, and integration by parts.
- Existing `ControlHorizon`, `RelaxedTrajectories`, `OrdinaryControlExistence`: actual finite-horizon time/dynamics models. Their existence results are not multiplier-necessity proofs.

## Validation

This initial checkpoint claims no new completed theorem. The local execution tools are currently returning runtime errors, so validation will use the branch's actual GitHub Actions Lean compiler rather than an unverified claim of local compilation. Final declarations and observed check results will replace this checkpoint as milestones are committed.
