# Optimal control — concept guide

This guide maps a mathematical question to the module to import, the principal
declaration, its decisive assumptions, the scope of its conclusion, and a checked
example or counterexample.  It follows the concept organization described in
`auto_automatyk:notes/reviews/optimal_control_concept_organization.md`; the full
declaration map is `optimal_control_declaration_map.json` there.

Import paths below are complete Lean module names.  The prefix
`DynamicalSystems.OptimalControl.ContinuousTime.` is abbreviated `CT.` in prose
only; code must use the full name.  Tests live under `DynamicalSystemsTest.` and
are not imported by the library.

The library states **normal** PMP clauses: a costate with the stated terminal
transversality condition, not an abnormal multiplier.  The assembly predicates in
`MinimumPrinciple` are *pointwise on the horizon*.  Euler–Lagrange conclusions come
in two strengths: a **within-horizon** `HasDerivWithinAt` momentum statement, and a
stronger classical endpoint `eulerLagrange` predicate that additionally needs
two-sided momentum differentiability at the endpoints.

## 1. Hamiltonian and PMP clauses

- **Question.** How do I state the Hamiltonian and the PMP clauses?
- **Import.** `DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple`
- **Principal declarations.** root `hamiltonianOf`, `costateEquation`,
  `transversalityCondition`, `HamiltonianMinimizing`.
- **Assumptions.** `[NormedAddCommGroup E] [InnerProductSpace ℝ E]`; `costateEquation`
  and `transversalityCondition` additionally use `[CompleteSpace E]`.
  These are definitions/predicates plus the assembly bridges `pmpAssembly` and
  `pmpAssembly_minimizing`.
- **Scope.** The definitions are unconditional; the assembly theorems take
  admissibility and a supplied costate.  They do **not** assume optimality.  The
  optimality-to-costate derivations are in §2 and §3 below.
- **Examples.** `PMPExamples.QuadraticCost.pmp_from_general_theorem` and
  `PMPExamples.QuadraticCost.explicit_costate` exhibit a normal PMP triple.
  Distinguish stationarity from minimization: the counterexample
  `PMPExamples.PointwiseRepresentative.optimal_without_pointwise_pmp` shows an
  optimal control can fail an all-times pointwise Hamiltonian condition after a
  null-set change (the usual a.e. formulation is not refuted).

## 2. Normal PMP from integral optimality on a finite horizon

- **Question.** How do I derive normal PMP from an optimal integral trajectory on a
  finite horizon?
- **Import.** `DynamicalSystems.OptimalControl.ContinuousTime.NeedlePMPOnHorizon`
- **Principal declaration.** `needleCostate_of_integralOptimality_onHorizon`
- **Assumptions.** `SmoothNeedleDataOnHorizon prob x u` (primitive analytic data:
  horizon positivity, local Lipschitz and continuity of the nominal and admissible
  test branches, and the actual spatial Fréchet derivative data) together with
  `NeedleIntegralModel.IsIntegralOptimalPair prob x₀ x u`.
  `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`.
- **Scope.** Produces a normal costate satisfying `costateEquation`,
  `transversalityCondition`, and `HamiltonianMinimizing` under the *actual*
  regularity hypotheses, with a free terminal state.
- **Examples.** The positive example `PMPExamples.QuadraticCost.pmp_from_general_theorem`
  (with `explicit_costate`) constructs a normal costate through the global smooth
  endpoint `needleCostate_of_integralOptimality_smooth`, of which this theorem is the
  clamped finite-horizon specialization; `PMPExamples.HorizonLocality.no_global_nominal_zero_bound`
  records the scope boundary: the clamping step needs a nominal zero bound, so the
  horizon-local hypothesis is not vacuous.

## 3. Geometric / separation route to PMP

- **Question.** How does the geometric/separation route derive PMP?
- **Import.** `DynamicalSystems.OptimalControl.ContinuousTime.GeometricMinimumPrinciple`
- **Principal declaration.**
  `integralOptimal_implies_PMP_via_hahnBanach_of_integral_reference`
- **Assumptions.** `[FiniteDimensional ℝ X]`, integral optimality
  (`NeedleIntegralModel.IsIntegralOptimalPair`), the stronger global branch regularity
  `BolzaBranchRegularity prob u` and `BolzaBranchRegularity prob (fun _ => v)` for
  each admissible test `v`, plus spatial Fréchet data `DL`, `Df` with their
  continuity and `HasFDerivAt prob.K DK (x prob.T)`.
- **Scope.** A normal free-terminal-state Bolza PMP result obtained by separating the
  needle endpoint generators in a finite-dimensional space.
- **Counterexample.** `PMPExamples.ClassicalAdmissibility.ContinuousOCPAdapter.optimality_does_not_imply_pmp`
  (with `reference_no_costate`) shows that a differentiable competitor class whose
  controls cannot switch is too small for the needle/separation step: optimality there
  does not yield a normal costate.

## 4. Full linear state transition

- **Question.** Where is a full linear state transition constructed?
- **Import.** `DynamicalSystems.Mathlib.Analysis.ODE.StateTransitionExistence`
- **Principal declaration.** `exists_stateTransitionOn_Icc`
- **Assumptions.** `[NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [FiniteDimensional ℝ X]`, `hab : a ≤ b`, and `ContinuousOn A (Icc a b)`.
- **Scope.** Returns an operator-valued `Phi` on the stated interval with the diagonal
  property, the forward equation `HasDerivAt (fun r => Phi r s) (A t ∘SL Phi t s) t`,
  the backward equation `HasDerivAt (fun r => Phi t r) (-Phi t s ∘SL A s) s`, and the
  cocycle law `Phi t r ∘SL Phi r s = Phi t s`.
- **Examples.** `NonautonomousFlowOrder.cocycle`, `bundled_reverse`, and
  `reversed_composition_fails` exercise the diagonal, restart/cocycle, and reversed
  composition properties (the last shows that reversing an unrestricted composition
  is not generally valid).  The richer `IsStateTransition` predicate and its API live
  in `DynamicalSystems.Mathlib.Analysis.ODE.StateTransition`.

## 5. Actual cost differentiation

- **Question.** Where is actual cost differentiation proved?
- **Import.** `DynamicalSystems.OptimalControl.ContinuousTime.FirstVariationDifferentiation`
- **Principal declarations.** `hasDerivAt_cvFunctional_affine`;
  `hasStrictFDerivAt_cvFunctional_perturbed`.
- **Assumptions.** `ContDiff ℝ 1 (uncurryLagrangian L)`, 
  `ContDiff ℝ 1 x` and the perturbation directions, and `0 ≤ T`.  The interval
  integral is differentiated under the integral sign (Mathlib `ParametricIntegral`).
- **Scope.** Identifies `firstVariation` with the actual one- or two-parameter cost
  derivative: `HasDerivAt (fun ε => cvFunctional L K T (x + ε • η)) (firstVariation L K T x η) 0`,
  and the strict derivative of the two-parameter family
  `p ↦ cvFunctional L K T (perturbedCurve x η ξ p)`.  No endpoint restriction on the
  one-parameter direction.
- **Examples.** `IsoperimetricVariation.Examples.NonzeroMultiplier.constrained_augmentedEulerLagrange`
  (with `multiplier_eq_neg_one`) uses this differentiation in a constrained minimum.
  `DuBoisReymond.Examples.NondifferentiableVelocity` records the low-regularity
  positive example.

## 6. Fixed-endpoint minimum implies weak Euler–Lagrange

- **Question.** How does a fixed-endpoint minimum imply weak Euler–Lagrange?
- **Import.** `DynamicalSystems.OptimalControl.ContinuousTime.WeakEulerLagrangeMinimum`
- **Principal declaration.**
  `WeakEulerLagrange.eulerLagrange_hasDerivWithinAt_of_fixedEndpoint_min`
- **Assumptions.** C¹ data: `ContDiff ℝ 1 (uncurryLagrangian L)`, 
  `ContDiff ℝ 1 x`, `0 < T`, and `IsMinOn (cvFunctional L K T) {y | ContDiff ℝ 1 y ∧
  y 0 = x 0 ∧ y T = x T} x`.
- **Scope.** Concludes the momentum `HasDerivWithinAt` at every `t ∈ Icc 0 T`; the
  momentum differentiability is *derived*, not assumed, and the endpoint derivatives
  are **within the horizon**.  The stronger classical endpoint requires two-sided
  derivatives.
- **Counterexample.** `WeakEulerLagrange.Counterexamples.TwoSidedEndpointDerivative.not_eulerLagrange`
  (with `curve_isMinOn` and `curve_hasVanishingFirstVariation`) shows a C¹ minimizer
  that satisfies the within-horizon momentum statement but not the two-sided endpoint
  derivative of the classical `eulerLagrange` predicate.  Keep the two endpoint
  notions distinct.

## 7. One common isoperimetric multiplier

- **Question.** Where is one common isoperimetric multiplier obtained?
- **Import.** `DynamicalSystems.OptimalControl.ContinuousTime.IsoperimetricEulerLagrange`
- **Principal declaration.**
  `IsoperimetricVariation.exists_common_isoperimetricMultiplier`
- **Assumptions.** A single scalar constraint `G`, a fixed-endpoint minimum of the
  actual `cvFunctional` over `fixedEndpointC1Curves T (x 0) (x T)` subject to the
  constraint, C¹ data, and a supplying direction `ξ` with
  `firstVariation G (fun _ ↦ 0) T x ξ ≠ 0`.
- **Scope.** One multiplier `lam` valid for **every** endpoint-zero C¹ variation `η`:
  `firstVariation L K T x η + lam * firstVariation G (fun _ ↦ 0) T x η = 0`.  This is the full
  scalar-constraint theorem; it does not turn into a theorem for arbitrarily many
  constraints (that is the abstract `IsoperimetricVariation.exists_normal_multipliers`).
- **Examples.** `IsoperimetricVariation.Examples.NonzeroMultiplier.multiplier_eq_neg_one`
  and `constrained_augmentedEulerLagrange` exhibit a nonzero common multiplier.

## 8. Constrained Euler–Lagrange endpoints

- **Question.** Where are the constrained Euler–Lagrange endpoints?
- **Import.** `DynamicalSystems.OptimalControl.ContinuousTime.IsoperimetricEulerLagrange`
- **Principal declarations.**
  `IsoperimetricVariation.augmentedEulerLagrangeWithin_of_isoperimetric`;
  `IsoperimetricVariation.augmentedEulerLagrange_of_isoperimetric`.
- **Assumptions.** Same constrained-minimum hypotheses as §7, with C¹ data for the
  within-horizon endpoint and C² data (`ContDiff ℝ 2` for `L`, `G`, `x`) for the
  classical endpoint.
- **Scope.** The first statement gives the C¹ endpoint-within result
  (`HasVanishingFirstVariation` plus the `HasDerivWithinAt` momentum statement); the
  second uses C² data to conclude the existing stronger classical `eulerLagrange`
  predicate.  Single scalar constraint only.
- **Examples.** `IsoperimetricVariation.Examples.NonzeroMultiplier.constrained_augmentedEulerLagrange`.

## 9. Energy laws without assuming acceleration

- **Question.** What energy law follows without assuming acceleration?
- **Imports.** `DynamicalSystems.OptimalControl.ContinuousTime.DuBoisReymond`;
  `DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousDuBoisReymond`.
- **Principal declarations.** `DuBoisReymond.energy_eq_of_cvFunctional_min`;
  `NonautonomousDuBoisReymond.weak_duBoisReymond_of_cvFunctional_min`.
- **Assumptions.** Actual minima in the endpoint-preserving
  `fixedEndpointPiecewiseC1Curves` competitor class, a `C¹` Lagrangian, a
  `HasDerivAt x (v t) t` flow with **continuous velocity** `v`, `0 < T`.  Acceleration
  is not assumed.
- **Scope.** The autonomous law conserves `energyCurve L x v` on the horizon; the
  nonautonomous compensated law conserves
  `energyCurve L x v t + ∫ s in 0..t, timePartialCurve L x v s` and gives the derivative
  `E' = -∂ₜL` off the endpoints.  Both energy conventions use `E = p · v - L`; the
  autonomous and nonautonomous namespaces stay separate.
- **Examples.** `DuBoisReymond.Examples.NondifferentiableVelocity.energy_conserved`
  (continuous velocity with an interior cusp) and
  `NonautonomousDuBoisReymond.Examples.NondifferentiableVelocity.compensated_energy_eq_zero`
  (genuinely time-dependent Lagrangian).  These are positive demonstrations of the
  theorem's low-regularity scope, not counterexamples.

## 10. Weierstrass–Erdmann corner conditions from a minimum

- **Question.** Where are Weierstrass–Erdmann corner conditions derived from a
  minimum?
- **Import.** `DynamicalSystems.OptimalControl.ContinuousTime.PiecewiseC1WeierstrassErdmann`
- **Principal declaration.** `FinitePiecewise.weierstrassErdmann_of_piecewiseC1On_min`
- **Assumptions.** `ContDiff ℝ 1 (uncurryLagrangian L)`,  the
  original one-corner predicate `IsPiecewiseC₁On x vL vR T τ`, continuous one-sided
  velocities `vL`, `vR`, and a minimum over
  `FinitePiecewise.fixedEndpointFinitePiecewiseC1CurvesOn T (x 0) (x T)`.
- **Scope.** Both momentum and energy match at the corner:
  `fderiv ℝ (L τ (x τ)) (vL τ) = fderiv ℝ (L τ (x τ)) (vR τ)` and the corresponding
  energy equality.  The corner is selected by the supplied predicate.
- **Examples.** No checked example exercises the corner theorem directly; its
  endpoint-preserving finite-piecewise competitor class is illustrated by
  `DuBoisReymond.Examples.NondifferentiableVelocity`.

## 11. Every represented finite corner

- **Question.** What is proved for every represented finite corner?
- **Imports.** `DynamicalSystems.OptimalControl.ContinuousTime.FiniteWeierstrassErdmann`;
  `DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteWeierstrassErdmann`.
- **Principal declarations.**
  `FinitePiecewise.weierstrassErdmann_at_every_represented_corner`;
  `FinitePiecewise.nonautonomous_weierstrassErdmann_at_every_represented_corner`.
- **Assumptions.** A minimum over `fixedEndpointFinitePiecewiseC1Curves T A B`,
  `ContDiff ℝ 1` data, two adjacent pieces with `HasDerivAt` and continuous velocities,
  and a *supplied* finite-context representation `SpliceContext` / `TimeSpliceContext`
  of the selected adjacent pair.
- **Scope.** The corner condition is concluded at the junction of the represented
  pair.  There is **no** automatic extraction of an arbitrary partition from `x`; the
  representation is part of the hypothesis, and the `represented_corner` /
  `piecewiseC1On` distinction is preserved in the names.
- **Examples.** No checked example exercises the represented-corner theorem directly;
  the closest is `DuBoisReymond.Examples.NondifferentiableVelocity`, which uses the
  same endpoint-preserving finite-piecewise competitor class.

## Cross-cutting scope distinctions

These distinctions survive the organization and should not be collapsed:

- **Integral vs classical admissibility.** `NeedleIntegralModel.IsIntegralOptimalPair`
  and the classical `IsOptimalPair` are different contracts.  `NeedleIntegralModel` is
  a coherent concept namespace; the two predicates are not silently identified (see
  `PMPExamples.ClassicalAdmissibility.ContinuousOCPAdapter`).
- **Two state-transition specifications.** Root `stateTransition` in
  `DynamicalSystems.OptimalControl.ContinuousTime.NeedleVariation` is weaker than the
  promoted `IsStateTransition`; `variationOfConstants` there assumes a cancellation
  formula that the richer method derives.  Both statements are kept; any equivalence
  needs an explicit bridge.
- **Within-horizon vs classical Euler–Lagrange.** See §6 and §8.
- **One scalar constraint.** See §7; `exists_normal_multipliers` is an abstract
  finite-family result, not an extension of the scalar Euler–Lagrange theorem.
- **Differentiable-test converse.** `EulerLagrangeStationarity` proves the exact
  `HasVanishingFirstVariation` predicate; because its quantifier includes tests whose
  variation density need not be integrable, it is not an actual-cost differentiability
  theorem for every differentiable test.  It is kept separate from §5.

## Executable audits

The active API, axiom, and proof-dependency audits live with the concept tests:

- `DynamicalSystemsTest.OptimalControl.ContinuousTime.Audits.PublicAPI` — `#check`
  probes of the principal public endpoints and assembly bridges.
- `DynamicalSystemsTest.OptimalControl.ContinuousTime.Audits.Axioms` — `#print axioms`
  of the public declarations, examples, and generic support; every result must use a
  subset of `{propext, Classical.choice, Quot.sound}`.
- `DynamicalSystemsTest.OptimalControl.ContinuousTime.Audits.Dependencies` —
  proof-term reference probes along the Hahn–Banach, constructed-family, and
  terminal-sensitivity chains.

Compile a single audit with, for example:

```bash
lake env lean --root=. \
  DynamicalSystemsTest/OptimalControl/ContinuousTime/Audits/PublicAPI.lean
```

The library build (`lake build DynamicalSystems`) covers
`DynamicalSystems.OptimalControl.ContinuousTime.*`; the tests and audits under
`DynamicalSystemsTest` are compiled explicitly.
