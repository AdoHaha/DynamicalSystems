/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.FiniteSpatialVariations

/-!
# Weierstrass–Erdmann at every represented finite corner

The reference may be given independently of its piecewise representation and
may differ outside the horizon. Every representation of a selected adjacent
pair by a finite surrounding context inherits both corner conditions.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace FinitePiecewise

open TimeReparametrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A single actual minimum implies both corner conditions at every finite-context
representation of every adjacent pair of C1 arcs. Representation is required only
on the physical horizon; no claim of automatic partition extraction is hidden. -/
theorem weierstrassErdmann_at_every_represented_corner
    (L : E → E → ℝ) (K : E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {T : ℝ} {A B : E} {x : ℝ → E}
    (hmin : IsMinOn (cvFunctional (fun _ ↦ L) K T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) x) :
    ∀ (x₁ v₁ x₂ v₂ : ℝ → E),
      (∀ t, HasDerivAt x₁ (v₁ t) t) → Continuous v₁ →
      (∀ t, HasDerivAt x₂ (v₂ t) t) → Continuous v₂ →
      ∀ (d₁ d₂ : ℝ), 0 < d₁ → 0 < d₂ → x₁ d₁ = x₂ 0 →
      ∀ (F : (ℝ → E) → ℝ → E),
      SpliceContext (d₁ + d₂) (x₁ 0) (x₂ d₂) T A B F →
      EqOn x (F (concatenate d₁ x₁ x₂)) (Icc 0 T) →
      fderiv ℝ (L (x₁ d₁)) (v₁ d₁) = fderiv ℝ (L (x₂ 0)) (v₂ 0) ∧
        energyCurve L x₁ v₁ d₁ = energyCurve L x₂ v₂ 0 := by
  intro x₁ v₁ x₂ v₂ hx₁ hv₁ hx₂ hv₂ d₁ d₂ hd₁ hd₂ hjoin F ctx hrep
  have href := concatenate_mem_fixedEndpointFinitePiecewiseC1Curves
    (.smooth hd₁ hx₁ hv₁) (.smooth hd₂ hx₂ hv₂) hjoin
  have hT := (ctx.feasible href).2.2.duration_pos
  have hcost := _root_.cvFunctional_eq_of_eqOn (fun _ ↦ L) K hT hrep
  apply weierstrassErdmann_of_cvFunctional_min_weak L K hL hx₁ hv₁ hx₂ hv₂
    hd₁ hd₂ hjoin ctx
  intro y hy
  change cvFunctional (fun _ ↦ L) K T (F (concatenate d₁ x₁ x₂)) ≤
    cvFunctional (fun _ ↦ L) K T y
  rw [← hcost]
  exact hmin hy

end FinitePiecewise
