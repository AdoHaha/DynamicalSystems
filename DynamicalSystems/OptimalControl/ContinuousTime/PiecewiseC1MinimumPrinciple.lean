/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteCornerMinimumPrinciple
import DynamicalSystems.OptimalControl.ContinuousTime.PiecewiseC1Extensions

/-!
# Weierstrass–Erdmann from the original piecewise-C1 predicate

The original one-corner reference supplies its own global branch extensions by
integration of the continuous one-sided velocities. Thus neither a supplied
branch decomposition nor any variational or differential necessary condition
is needed. The ambient class permits finitely many additional corners.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace FinitePiecewise

open TimeReparametrization PiecewiseC1Extensions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fixed-endpoint finite-piecewise C1 curves on the physical horizon; values
outside the horizon are unrestricted and carry no cost or derivative conditions. -/
def fixedEndpointFinitePiecewiseC1CurvesOn (T : ℝ) (a b : E) : Set (ℝ → E) :=
  {x | x 0 = a ∧ x T = b ∧ ∃ y, IsFinitePiecewiseC1 T y ∧ EqOn x y (Icc 0 T)}

/-- Every constructed finite-piecewise competitor is admissible on the horizon. -/
theorem mem_finitePiecewiseC1CurvesOn_of_mem {T : ℝ} {a b : E} {x : ℝ → E}
    (hx : x ∈ fixedEndpointFinitePiecewiseC1Curves T a b) :
    x ∈ fixedEndpointFinitePiecewiseC1CurvesOn T a b :=
  ⟨hx.1, hx.2.1, x, hx.2.2, fun _ _ ↦ rfl⟩

variable [CompleteSpace E]

/-- The original project's single-corner predicate gives actual membership in the
finite-piecewise horizon class; the global C1 extensions are constructed by FTC. -/
theorem mem_finitePiecewiseC1CurvesOn_of_isPiecewiseC1On
    {x vL vR : ℝ → E} {T τ : ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ)
    (hvL : Continuous vL) (hvR : Continuous vR) :
    x ∈ fixedEndpointFinitePiecewiseC1CurvesOn T (x 0) (x T) := by
  have hd : 0 < T - τ := sub_pos.mpr hcorner.2.1
  have hj := arcs_join hcorner hvL
  have hfinite := IsFinitePiecewiseC1.join
    (.smooth hcorner.1 (hasDerivAt_leftArc x hvL) hvL)
    (.smooth hd (hasDerivAt_rightArc x hvR τ)
      (hvR.comp (continuous_const.add continuous_id))) hj
  have hsum : τ + (T - τ) = T := by ring
  rw [hsum] at hfinite
  exact ⟨rfl, rfl, _, hfinite, eqOn_concatenate hcorner hvL hvR⟩

/-- Both nonautonomous corner conditions follow from the original piecewise-C1
reference and its actual functional minimum. Its global branches are derived,
with no acceleration, Euler–Lagrange, energy, or stationarity assumption. -/
theorem weierstrassErdmann_of_original_piecewiseC1_min
    (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    {x vL vR : ℝ → E} {T τ : ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ)
    (hvL : Continuous vL) (hvR : Continuous vR)
    (hmin : IsMinOn (cvFunctional L K T)
      (fixedEndpointFinitePiecewiseC1Curves T (x 0) (x T)) x) :
    fderiv ℝ (L τ (x τ)) (vL τ) = fderiv ℝ (L τ (x τ)) (vR τ) ∧
      fderiv ℝ (L τ (x τ)) (vL τ) (vL τ) - L τ (x τ) (vL τ) =
        fderiv ℝ (L τ (x τ)) (vR τ) (vR τ) - L τ (x τ) (vR τ) := by
  obtain ⟨xL, xR, hxL, hxR, hL0, hLτ, hR0, hRT, hjoin, hrep⟩ :=
    exists_global_arcs hcorner hvL hvR
  have hd : 0 < T - τ := sub_pos.mpr hcorner.2.1
  have hsum : τ + (T - τ) = T := by ring
  have hctx : TimeSpliceContext 0 (τ + (T - τ)) (xL 0) (xR (T - τ))
      0 T (x 0) (x T) id := by
    simpa only [hsum, hL0, hRT] using
      (TimeSpliceContext.hole (start := 0) (d := τ + (T - τ))
        (a := xL 0) (b := xR (T - τ)))
  have h := nonautonomous_weierstrassErdmann_at_every_represented_corner L K hL hmin
    xL vL xR (fun s ↦ vR (τ + s)) hxL hvL hxR
    (hvR.comp (continuous_const.add continuous_id)) 0 τ (T - τ) hcorner.1 hd hjoin
    id hctx hrep
  simpa only [zero_add, add_zero, hLτ, hR0] using h

/-- The final original-predicate theorem uses the natural horizon-only ambient
class and proves both momentum and energy continuity at the actual corner. -/
theorem weierstrassErdmann_of_piecewiseC1On_min
    (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    {x vL vR : ℝ → E} {T τ : ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ)
    (hvL : Continuous vL) (hvR : Continuous vR)
    (hmin : IsMinOn (cvFunctional L K T)
      (fixedEndpointFinitePiecewiseC1CurvesOn T (x 0) (x T)) x) :
    fderiv ℝ (L τ (x τ)) (vL τ) = fderiv ℝ (L τ (x τ)) (vR τ) ∧
      fderiv ℝ (L τ (x τ)) (vL τ) (vL τ) - L τ (x τ) (vL τ) =
        fderiv ℝ (L τ (x τ)) (vR τ) (vR τ) - L τ (x τ) (vR τ) := by
  apply weierstrassErdmann_of_original_piecewiseC1_min L K hL hcorner hvL hvR
  intro y hy
  exact hmin (mem_finitePiecewiseC1CurvesOn_of_mem hy)

/-- Autonomous specialization of the original-predicate theorem, retaining only
continuous one-sided velocities and actual ambient functional optimality. -/
theorem autonomous_weierstrassErdmann_of_piecewiseC1On_min
    (L : E → E → ℝ) (K : E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x vL vR : ℝ → E} {T τ : ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ)
    (hvL : Continuous vL) (hvR : Continuous vR)
    (hmin : IsMinOn (cvFunctional (fun _ ↦ L) K T)
      (fixedEndpointFinitePiecewiseC1CurvesOn T (x 0) (x T)) x) :
    fderiv ℝ (L (x τ)) (vL τ) = fderiv ℝ (L (x τ)) (vR τ) ∧
      energyCurve L x vL τ = energyCurve L x vR τ :=
  weierstrassErdmann_of_piecewiseC1On_min (fun _ ↦ L) K
    (contDiff_autonomous_lagrangian L hL) hcorner hvL hvR hmin

end FinitePiecewise
