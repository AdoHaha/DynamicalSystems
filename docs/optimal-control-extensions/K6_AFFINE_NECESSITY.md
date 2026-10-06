# Affine-convex state-constraint necessity

Date: 2026-10-06. This is a locally compiled continuation beyond the previous
integrator-only checkpoint. The result is a necessity theorem from actual
optimality, rather than a verification theorem accepting multiplier certificates.

## Public theorem

`OptimalControl.ConvexStateControlProblem.exists_stateConstrainedPMP_of_affine_convex_minimum`
in `StateConstrainedMinimumPrinciple.lean`.

Primitive inputs are a positive finite horizon, finite-dimensional real state and
control spaces, compact convex controls, continuous coefficients in
`f(t,x,u) = A(t)x + B(t)u + a(t)`, convex C¹ terminal cost, jointly convex C¹
running cost in state/control, and finitely many convex spatial C¹ state
constraints. The primitive costs, constraints and derivative maps are jointly
continuous. State constraints need no time derivative. Controls are measurable;
trajectories satisfy the actual Volterra equation at every time.

The minimum premise compares every actual admissible measurable trajectory/control
pair satisfying all state inequalities. No transition, comparison-trajectory
existence, measure, first-variation inequality, adjoint identity, BV certificate
or Hamiltonian minimum is a public input.

## Outputs and conventions

The theorem constructs a scalar `α ≥ 0` and a finite positive measure `μ` on
`[0,T] × Fin n`, with `α ≠ 0 ∨ μ ≠ 0`, complementarity and concentration on
actual contacts. This single indexed measure retains all finitely many constraints.

It constructs the actual state transition and a real-time costate from the terminal
covector, the running spatial derivative and the indexed constraint-normal tails.
The measure tails are open at their lower limit. Its conclusions include:

- Bounded variation on the horizon and a right-continuous representative.
- The exact additive adjoint increment, with the ordinary `p ∘ A` term,
  running spatial derivative and singular indexed constraint integral.
- The full negative constraint-normal integral on each atomic time fiber as its jump.
- `p(T) = α Dφ(x(T))`, while the left terminal trace additionally contains
  every terminal constraint-normal atom.
- One common almost-everywhere set on which the actual Hamiltonian is minimized
  against **every** control value.

Time integrals in the problem use the repository's normalized horizon measure `ν`.
The explicit factor `T` undoes its normalization: `T ν` is Lebesgue time.
The increment theorem preserves this factor rather than silently changing measures.
No division by the possibly zero cost multiplier occurs.

Fixed initial state can make an initial constraint multiplier redundant.
`stateMeasure_initial_fiber_eq_zero` separately proves that strict initial
feasibility eliminates the entire initial-time fiber. The theorem does not
silently discard initial atoms when that hypothesis is absent. Uniform Slater
normality is already derived from an actual strictly feasible pair at the measure
extraction level; this final theorem retains the abnormal alternative.

## Proof chain

1. Convexity of actual affine integral trajectories and objective/constraints
   yields positive measure multipliers by infinite-dimensional separation and RMK.
2. `AffineIntegralResponse` constructs actual L¹-forced trajectories, proves
   Volterra dynamics and uniqueness, and derives exact response differences.
3. `AffineControlPath` constructs every measurable compact-valued comparison
   trajectory and the actual affine response in the original time convention.
4. `StateControlFirstVariation` differentiates the actual penalized functional;
   domination and integrability follow from compact control/state tubes.
5. Indexed Fubini turns terminal/running/constraint variations into pairing with
   the constructed adjoint. The original constrained minimum is not used for
   arbitrary replacements; the derived penalized minimum is used first.
6. Measurable localization gives a common-AE linear control inequality. Convex
   supporting derivatives yield the actual Hamiltonian minimum.
7. Measure-tail and transition calculus derive BV, exact increments and traces.

## Regression coverage

`AffineStateNecessity.lean` proves actual global optimality for `x′ = x + u`,
`u ∈ [-1,1]`, quadratic terminal/running costs and nonlinear state constraint
`x² − 1 ≤ 0`, then invokes the **full** theorem and retains its entire conclusion.

`StateControlFirstVariation.lean` differentiates nonlinear costs and a nonlinear
state constraint under a terminal Dirac measure, with merely measurable controls.
The independently derived objective derivative and adjoint-control pairing agree.

`MeasureAdjointBalance.lean` proves the transition for `A = id`, checks interior
and terminal atoms in the additive equation, and proves the resulting BV costate
is not absolutely continuous. This is a foundation regression with an explicit
measure. The separate `StateConstraintAtoms.lean` regression proves actual
constrained optimality and **forces** a positive interior Dirac and nonzero jump.

## Source and representation boundary

The local Berkovitz–Medhin text, §11.6 (PDF pages 335–336, printed pages 322–323),
was checked against the endpoint and state-constraint scope. Its general nonlinear
statement uses a shifted absolutely continuous adjoint and a monotone constraint
multiplier. This proof uses the BV measure-tail representative directly and is not
a claimed formalization of that broader nonlinear theorem. The previous session's
affine-convex measure argument supplies the roadmap; each construction and identity
above is now checked in Lean, rather than retained as an informal certificate.

## Remaining K6 boundary

This closes the affine-convex C¹ necessity slice. It does not prove unrestricted
nonlinear dynamics PMP, nonconvex control/state geometry, hard terminal equality
assembly, or time-measurable coefficient generality. Those require additional
linearization/needle-variation and endpoint machinery. No whole-campaign
acceptance or external publication is claimed.
