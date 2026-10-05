/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.NeedleDisplacement
public import DynamicalSystems.OptimalControl.ContinuousTime.NeedleVariation

/-!
# Integration with the existing frozen-impulse theorem

The existing `needleImpulseFirstOrder` supplies only the first-order expansion
of the frozen-reference dynamics integral. `needleTrajectoryFirstOrder` upgrades
this to the true trajectory displacement by the short-interval absorption and
quadratic-remainder estimates in `NeedleDisplacement`.

The remaining primitive ODE obligation is the existence of the integral-solution
family with uniform local Lipschitz and forcing bounds. No trajectory sensitivity
or Hamiltonian inequality is assumed.

For repository integration, place the core file under the desired
`DynamicalSystems` module path and adjust its import above. This adapter imports
the current `NeedleVariation` to reuse the already-proved impulse theorem.
-/

@[expose] public section

open Filter
open scoped Topology

variable {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- First-order displacement at the end of a needle, derived from primitive
integral-solution data and continuity of the frozen dynamics branches. -/
theorem needleTrajectoryFirstOrder
    (f : ℝ → X → U → X) (x₀ : ℝ → X) (u₀ : ℝ → U)
    (xε : ℝ → ℝ → X) (τ : ℝ) (v : U) {L M : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hfamily : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      NeedleIntervalData (xε ε) x₀ (fun t z => f t z v)
        (fun t => f t (x₀ t) (u₀ t)) (τ - ε) τ L M)
    (hfv : Continuous (fun t => f t (x₀ t) v))
    (hfu : Continuous (fun t => f t (x₀ t) (u₀ t))) :
    Tendsto (fun ε : ℝ => ε⁻¹ •
        (xε ε τ - x₀ τ - ε • (f τ (x₀ τ) v - f τ (x₀ τ) (u₀ τ))))
      (𝓝[>] 0) (𝓝 0) :=
  needle_displacement_firstOrder_of_integral_solutions
    (x := xε) (y := x₀) (F := fun t z => f t z v)
    (f₀ := fun t => f t (x₀ t) (u₀ t)) (τ := τ) (L := L) (M := M)
    hL hM hfamily
    (needleImpulseFirstOrder f x₀ u₀ τ v hfv hfu)

end
