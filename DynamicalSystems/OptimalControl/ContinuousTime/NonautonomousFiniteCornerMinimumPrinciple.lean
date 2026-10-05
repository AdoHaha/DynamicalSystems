/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.FiniteCornerMinimumPrinciple
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteCornerConditions

/-!
# Nonautonomous corner conditions at every represented finite corner

A minimum of the original time-dependent functional implies both corner laws
at every finite-context representation of an adjacent C1 pair. The actual
reference and its representation only need to coincide on the horizon.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace KirkMedhin.FinitePiecewise

open TimeReparametrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original nonautonomous minimum implies both Weierstrass–Erdmann conditions
at every represented finite corner, under C1 Lagrangian and continuous velocities. -/
theorem nonautonomous_weierstrassErdmann_at_every_represented_corner
    (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L))
    {T : ℝ} {A B : E} {x : ℝ → E}
    (hmin : IsMinOn (cvFunctional L K T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) x) :
    ∀ (x₁ v₁ x₂ v₂ : ℝ → E),
      (∀ t, HasDerivAt x₁ (v₁ t) t) → Continuous v₁ →
      (∀ t, HasDerivAt x₂ (v₂ t) t) → Continuous v₂ →
      ∀ (start d₁ d₂ : ℝ), 0 < d₁ → 0 < d₂ → x₁ d₁ = x₂ 0 →
      ∀ (F : (ℝ → E) → ℝ → E),
      TimeSpliceContext start (d₁ + d₂) (x₁ 0) (x₂ d₂) 0 T A B F →
      EqOn x (F (concatenate d₁ x₁ x₂)) (Icc 0 T) →
      fderiv ℝ (L (start + d₁) (x₁ d₁)) (v₁ d₁) =
          fderiv ℝ (L (start + d₁) (x₂ 0)) (v₂ 0) ∧
        fderiv ℝ (L (start + d₁) (x₁ d₁)) (v₁ d₁) (v₁ d₁) -
            L (start + d₁) (x₁ d₁) (v₁ d₁) =
          fderiv ℝ (L (start + d₁) (x₂ 0)) (v₂ 0) (v₂ 0) -
            L (start + d₁) (x₂ 0) (v₂ 0) := by
  intro x₁ v₁ x₂ v₂ hx₁ hv₁ hx₂ hv₂ start d₁ d₂ hd₁ hd₂ hjoin F ctx hrep
  have href := concatenate_mem_fixedEndpointFinitePiecewiseC1Curves
    (.smooth hd₁ hx₁ hv₁) (.smooth hd₂ hx₂ hv₂) hjoin
  have hT := (ctx.feasible href).2.2.duration_pos
  have hcost := cvFunctional_eq_of_eqOn L K hT hrep
  have hm : IsMinOn (cvFunctional (fun t ↦ L (0 + t)) K T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) (F (concatenate d₁ x₁ x₂)) := by
    intro y hy
    change cvFunctional (fun t ↦ L (0 + t)) K T (F (concatenate d₁ x₁ x₂)) ≤
      cvFunctional (fun t ↦ L (0 + t)) K T y
    simp only [zero_add]
    rw [← hcost]
    exact hmin hy
  exact weierstrassErdmann_in_timeSpliceContext L K hL hx₁ hv₁ hx₂ hv₂
    hd₁ hd₂ hjoin ctx hm

end KirkMedhin.FinitePiecewise
