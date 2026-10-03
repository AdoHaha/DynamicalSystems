/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.Extr

/-! # Continuous-time optimal control problem substrate

This file sets up the basic data of a continuous-time deterministic optimal
control problem and its trajectory/cost bookkeeping.  The state space `X` is a
normed `ℝ`-vector space, the control space `U` is arbitrary, the dynamics is
`f : ℝ → X → U → X`, the running cost is `L : ℝ → X → U → ℝ`, the terminal cost
is `K : X → ℝ`, the horizon is `T : ℝ` and the controls are constrained to a set
`controlSet : Set U`.  Costs are genuine Lebesgue/Bochner integrals over the
interval `[0, T]`.

The definitions follow Sontag, *Mathematical Control Theory: Deterministic Finite
Dimensional Systems*, 2nd ed., 1998, Ch. 8 §8.1 (printed pp. 349–363): the
instantaneous (running) cost, the total cost as the running integral plus the
terminal cost, the admissible trajectory/control pairs of the optimal control
problem, the associated cost set and the dynamic-programming value function
(the infimum of the cost set).

Admissibility is purely *relational*: rather than postulating a global solution
map `(ℝ → U) → (ℝ → X)` (which stalls on the question of global existence), a
pair `(x, u)` is admissible from `x₀` when `x 0 = x₀`, the control respects the
constraint set on `[0, T]`, the trajectory satisfies the ODE `x' = f t x u`
pointwise on `[0, T]` in the relational sense of `HasDerivAt`, and the running
cost is interval-integrable.  Bundling the last clause into admissibility avoids
the Bochner convention that non-integrable functions integrate to junk (`0`).

## Main definitions

* `ContinuousOCP`: horizon, dynamics, running cost, terminal cost and control
  constraint set of a continuous-time optimal control problem.
* `IsAdmissiblePair`: the relational admissibility predicate for a trajectory and
  a control.
* `continuousTotalCost`: the running-cost integral over `[0, T]` plus the terminal
  cost `K (x T)`.
* `continuousCostSet`: the set of total costs of admissible pairs from `x₀`.
* `continuousValueFunction`: the infimum of the cost set, i.e. the optimal
  cost-to-go.
* `IsOptimalPair`: an admissible pair whose total cost is minimal.

## Main results

* `continuousValueFunction_le`: the value function is a lower bound of the cost of
  every admissible pair.
* `le_continuousValueFunction`: a lower bound of every admissible cost bounds the
  value function.
* `continuousValueFunction_eq_continuousTotalCost`: the value function equals the
  cost of an optimal pair, when one exists.
* `bddBelow_continuousCostSet`: with a nonnegative horizon, nonnegative running
  cost and nonnegative terminal cost, the cost set is bounded below.

## Implementation notes

The value function is a genuine `sInf` into `ℝ`, which is only conditionally
complete.  On `ℝ` the convention is `sInf ∅ = 0` and `sInf s = 0` when `s` is
unbounded below, so `continuousValueFunction` is only the honest optimal
cost-to-go under hypotheses excluding those degenerate cases; for instance
`bddBelow_continuousCostSet` supplies a lower bound when `0 ≤ T`, `0 ≤ L` and
`0 ≤ K`.  The minimisation is relational (`IsMinOn`), never a single-valued
`argmin`: optimal controls need not exist, and when they do this file only
records the minimising property.
-/

@[expose] public section

open scoped Interval

open MeasureTheory

variable {X U : Type*}

/-- A continuous-time deterministic optimal control problem.

The horizon is `T`, the dynamics is `ẋ = f t x u`, the running (instantaneous)
cost is `L t x u`, the terminal cost is `K x`, and admissible controls take
values in `controlSet` (Sontag, *Mathematical Control Theory*, 2nd ed., 1998,
Ch. 8 §8.1, printed pp. 349–363). -/
structure ContinuousOCP (X U : Type*) where
  /-- The horizon `T` (the cost is integrated over `[0, T]`). -/
  (T : ℝ)
  /-- The dynamics `ẋ = f t x u`. -/
  (f : ℝ → X → U → X)
  /-- The running (instantaneous) cost `L t x u`. -/
  (L : ℝ → X → U → ℝ)
  /-- The terminal cost `K x`. -/
  (K : X → ℝ)
  /-- The set of admissible control values. -/
  (controlSet : Set U)

/-- The total cost of the trajectory/control pair `(x, u)`: the running cost
integrated over the horizon plus the terminal cost at the final state
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.1, printed
pp. 349–363).

The initial state `x₀` does not enter the formula; it is kept as a parameter so
that the cost can be written uniformly with `IsAdmissiblePair`, which already
records `x 0 = x₀`. -/
noncomputable def continuousTotalCost (prob : ContinuousOCP X U) (_x₀ : X)
    (x : ℝ → X) (u : ℝ → U) : ℝ :=
  (∫ t in 0..prob.T, prob.L t (x t) (u t)) + prob.K (x prob.T)

section Normed

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Admissibility of a trajectory/control pair `(x, u)` from `x₀` for the problem
`prob`: the trajectory starts at `x₀`, the control respects `controlSet` on the
horizon `[0, T]`, the trajectory solves the ODE `ẋ = f t x u` pointwise on
`[0, T]` (relational `HasDerivAt`, *not* a global solution map), and the running
cost is interval-integrable over `[0, T]` (Sontag, *Mathematical Control Theory*,
2nd ed., 1998, Ch. 8 §8.1, printed pp. 349–363).

The relational condition avoids postulating a global solver, and the bundled
`IntervalIntegrable` clause rules out the Bochner convention that a
non-integrable running cost contributes `0`. -/
def IsAdmissiblePair (prob : ContinuousOCP X U) (x₀ : X) (x : ℝ → X) (u : ℝ → U) : Prop :=
  x 0 = x₀ ∧
    (∀ t ∈ Set.Icc 0 prob.T, u t ∈ prob.controlSet) ∧
    (∀ t ∈ Set.Icc 0 prob.T, HasDerivAt x (prob.f t (x t) (u t)) t) ∧
    IntervalIntegrable (fun t ↦ prob.L t (x t) (u t)) volume 0 prob.T

/-- The set of total costs of admissible trajectory/control pairs from `x₀`. -/
def continuousCostSet (prob : ContinuousOCP X U) (x₀ : X) : Set ℝ :=
  {c | ∃ x u, IsAdmissiblePair prob x₀ x u ∧ c = continuousTotalCost prob x₀ x u}

/-- The dynamic-programming value function: the infimum of the total cost over the
admissible trajectory/control pairs from `x₀`, i.e. the optimal cost-to-go
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.1, printed
pp. 349–363).

This is an `sInf` into `ℝ`; see the implementation notes for the conditional
completeness caveat. -/
noncomputable def continuousValueFunction (prob : ContinuousOCP X U) (x₀ : X) : ℝ :=
  sInf (continuousCostSet prob x₀)

/-- An admissible trajectory/control pair whose total cost is minimal over all
admissible pairs from `x₀` (Sontag, *Mathematical Control Theory*, 2nd ed., 1998,
Ch. 8 §8.1, printed pp. 349–363).  Optimality is relational (`IsMinOn` over the
admissible pairs); the problem need not have a unique or even an existing
minimiser. -/
def IsOptimalPair (prob : ContinuousOCP X U) (x₀ : X) (x : ℝ → X) (u : ℝ → U) : Prop :=
  IsAdmissiblePair prob x₀ x u ∧
    IsMinOn (fun p : (ℝ → X) × (ℝ → U) ↦ continuousTotalCost prob x₀ p.1 p.2)
      {p : (ℝ → X) × (ℝ → U) | IsAdmissiblePair prob x₀ p.1 p.2} (x, u)

/-- The value function is a lower bound of the cost of every admissible pair.  The
boundedness hypothesis is needed because `ℝ` is only conditionally complete. -/
theorem continuousValueFunction_le (prob : ContinuousOCP X U) (x₀ : X)
    (x : ℝ → X) (u : ℝ → U) (hu : IsAdmissiblePair prob x₀ x u)
    (hbd : BddBelow (continuousCostSet prob x₀)) :
    continuousValueFunction prob x₀ ≤ continuousTotalCost prob x₀ x u :=
  csInf_le hbd ⟨x, u, hu, rfl⟩

/-- A lower bound of every admissible cost bounds the value function. -/
theorem le_continuousValueFunction (prob : ContinuousOCP X U) (x₀ : X) {a : ℝ}
    (hne : (continuousCostSet prob x₀).Nonempty)
    (ha : ∀ r ∈ continuousCostSet prob x₀, a ≤ r) :
    a ≤ continuousValueFunction prob x₀ :=
  le_csInf hne ha

/-- When a minimising admissible pair exists, the value function equals its total
cost.  If no minimiser exists this fails in general and one should use the
`continuousValueFunction_le` / `le_continuousValueFunction` sandwich instead. -/
theorem continuousValueFunction_eq_continuousTotalCost (prob : ContinuousOCP X U) (x₀ : X)
    (x : ℝ → X) (u : ℝ → U) (hu : IsOptimalPair prob x₀ x u) :
    continuousValueFunction prob x₀ = continuousTotalCost prob x₀ x u := by
  have hmem : continuousTotalCost prob x₀ x u ∈ continuousCostSet prob x₀ :=
    ⟨x, u, hu.1, rfl⟩
  have hbd : BddBelow (continuousCostSet prob x₀) :=
    ⟨continuousTotalCost prob x₀ x u, by
      rintro r ⟨v, w, hv, rfl⟩
      exact (isMinOn_iff.mp hu.2) (v, w) hv⟩
  refine le_antisymm (csInf_le hbd hmem) ?_
  refine le_csInf ⟨continuousTotalCost prob x₀ x u, hmem⟩ ?_
  rintro r ⟨v, w, hv, rfl⟩
  exact (isMinOn_iff.mp hu.2) (v, w) hv

/-- With a nonnegative horizon, a nonnegative running cost and a nonnegative
terminal cost, the cost set is bounded below by `0`.  This is the honestness
guard for the `sInf` definition of the value function: it excludes the
`¬ BddBelow` case in which `sInf` on `ℝ` silently returns `0`. -/
theorem bddBelow_continuousCostSet (prob : ContinuousOCP X U) (x₀ : X)
    (hT : 0 ≤ prob.T) (hL : ∀ t x u, 0 ≤ prob.L t x u) (hK : ∀ x, 0 ≤ prob.K x) :
    BddBelow (continuousCostSet prob x₀) := by
  refine ⟨0, ?_⟩
  rintro c ⟨x, u, _, rfl⟩
  unfold continuousTotalCost
  exact add_nonneg (intervalIntegral.integral_nonneg hT fun t _ ↦ hL t (x t) (u t)) (hK _)

end Normed
