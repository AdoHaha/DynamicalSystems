/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Basic.NonAutonomous
public import DynamicalSystems.Stability.Floquet
public import Mathlib.Topology.Bornology.Basic

/-! # Equilibria, limit cycles and boundedness

This file records the Chapter 1 vocabulary of Kabziński and Mosiołek,
*Projektowanie nieliniowych układów sterowania*, for autonomous and non-autonomous
flows.

## Main definitions

* `IsEquilibrium`: a state at which an autonomous vector field vanishes.
* `IsEquilibriumAt`: a state at which a non-autonomous vector field vanishes for all times.
* `IsIsolatedEquilibrium`: an equilibrium with a neighbourhood containing no other equilibrium.
* `IsLimitCycle`: an orbit that is periodic with some positive period.
* `IsBoundedTrajectory`: the forward trajectory is bounded.
* `IsUniformlyBoundedAt`: trajectories starting in a bounded ball remain in a bounded ball,
  with a bound that is uniform in the initial time.
* `IsUltimatelyUniformlyBoundedAt`: trajectories eventually enter a fixed bounded ball,
  after a time that is uniform in the initial time.
-/

open scoped Topology

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `x` is an equilibrium of the autonomous vector field `f`, i.e. `f x = 0`. -/
def IsEquilibrium (f : E → E) (x : E) : Prop := f x = 0

/-- `x` is an equilibrium of the non-autonomous vector field `f`, i.e. `f t x = 0` for every
time `t`. -/
def IsEquilibriumAt (f : ℝ → E → E) (x : E) : Prop := ∀ t, f t x = 0

/-- `x` is an isolated equilibrium of `f`: it is an equilibrium and some neighbourhood of `x`
contains no other equilibrium. -/
def IsIsolatedEquilibrium (f : E → E) (x : E) : Prop :=
  IsEquilibrium f x ∧ ∃ U ∈ 𝓝 x, ∀ y ∈ U, IsEquilibrium f y → y = x

/-- A limit cycle of `f`: a periodic orbit of `f` with some positive period. Following the
book's Definition 1.3 we do not require the orbit to be isolated.

Note that `IsPeriodicOrbit` is an *autonomous* notion: it is stated for a fixed vector field `f`
and a trajectory `φ` of `f`, and it does not ask that `φ` be non-constant. In particular every
equilibrium `φ ≡ xₑ` is periodic with every period `T > 0`, so it satisfies this predicate. The
book's Definition 1.3 instead demands a genuinely time-varying solution, so this predicate is a
convenient superset of the book's limit cycles; no non-constancy conjunct is imposed here. -/
def IsLimitCycle (f : E → E) (φ : ℝ → E) : Prop := ∃ T, IsPeriodicOrbit f φ T

/-- The forward trajectory of the flow `Φ` starting at `x₀`, i.e. the image of `[0, ∞)`, is
bounded. Restricting to `t ≥ 0` matters: the book's Definition 1.12 bounds `x(t; t₀, x₀)` only
for `t ≥ t₀`, so a stable but backwards-unbounded flow such as `Φ t x = exp (-t) * x` still has
bounded forward trajectories. -/
def IsBoundedTrajectory (Φ : ℝ → E → E) (x₀ : E) : Prop :=
  Bornology.IsBounded (Set.image (fun t ↦ Φ t x₀) (Set.Ici 0))

/-- The non-autonomous flow `Φ` is uniformly bounded: for every bounded set of initial states
there is a bound that is valid for all initial times. -/
def IsUniformlyBoundedAt (Φ : NonautonomousFlow ℝ E) : Prop :=
  ∀ α > 0, ∃ β > 0, ∀ t₀ ≥ 0, ∀ x, ‖x‖ < α → ∀ t ≥ t₀, ‖Φ t₀ x t‖ < β

/-- The non-autonomous flow `Φ` is ultimately uniformly bounded with ultimate bound `B`: every
bounded set of initial states eventually enters the ball of radius `B`, after a time that is
uniform in the initial time. -/
def IsUltimatelyUniformlyBoundedAt (Φ : NonautonomousFlow ℝ E) (B : ℝ) : Prop :=
  ∀ α > 0, ∃ τ > 0, ∀ t₀ ≥ 0, ∀ x, ‖x‖ < α → ∀ t ≥ t₀ + τ, ‖Φ t₀ x t‖ < B
