/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.DuBoisReymond
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# A weak du Bois–Reymond minimizer with nondifferentiable velocity

The Lagrangian penalizes the square of the first velocity component. The
reference remains stationary in that component while its second velocity is
`|t - 1/2|`. Its cost is minimal, its velocity is continuous, and its velocity
is not differentiable at the interior time `1/2`. The weak theorem applies to
this actual minimizer without an Euler–Lagrange or acceleration hypothesis.
-/

open MeasureTheory Set
open scoped Interval

namespace KirkMedhin.WeakDuBoisReymondRegression

open KirkMedhin.TimeReparametrization KirkMedhin.DuBoisReymond

/-- A nonconstant, nonnegative quadratic Lagrangian on a two-dimensional state. -/
def lagrangian (_ : ℝ × ℝ) (v : ℝ × ℝ) : ℝ := v.1 ^ 2

/-- A continuous velocity with an interior cusp in its unpenalized component. -/
noncomputable def velocity (t : ℝ) : ℝ × ℝ := (0, |t - 1 / 2|)

/-- The actual state curve obtained by integrating the cusp velocity. -/
noncomputable def reference (t : ℝ) : ℝ × ℝ :=
  (0, ∫ s in 0..t, |s - 1 / 2|)

theorem velocity_continuous : Continuous velocity :=
  continuous_const.prodMk ((continuous_id.sub continuous_const).abs)

theorem reference_hasDerivAt (t : ℝ) : HasDerivAt reference (velocity t) t := by
  have hc : Continuous (fun s : ℝ => |s - 1 / 2|) :=
    (continuous_id.sub continuous_const).abs
  exact (hasDerivAt_const t (0 : ℝ)).prodMk
    (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt)

theorem lagrangian_contDiff : ContDiff ℝ 1 lagrangian.uncurry :=
  contDiff_snd.fst.pow 2

theorem lagrangian_nonconstant : lagrangian (0, 0) (1, 0) ≠ lagrangian (0, 0) (0, 0) := by
  norm_num [lagrangian]

theorem reference_feasible : reference ∈
    fixedEndpointPiecewiseC1Curves 1 (reference 0) (reference 1) := by
  refine ⟨rfl, rfl, (1 / 2 : ℝ), velocity, velocity, ?_,
    velocity_continuous, velocity_continuous⟩
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · exact (continuous_iff_continuousAt.mpr
      fun t => (reference_hasDerivAt t).continuousAt).continuousOn
  · intro t _
    exact (reference_hasDerivAt t).hasDerivWithinAt
  · intro t _
    exact (reference_hasDerivAt t).hasDerivWithinAt

/-- The genuine `cvFunctional` is minimized among all ambient fixed-endpoint
piecewise-C1 competitors; the minimum is derived directly from nonnegativity. -/
theorem reference_optimal : IsMinOn
    (cvFunctional (fun _ => lagrangian) (fun _ => 0) 1)
    (fixedEndpointPiecewiseC1Curves 1 (reference 0) (reference 1)) reference := by
  have hcost : cvFunctional (fun _ => lagrangian) (fun _ => 0) 1 reference = 0 := by
    simp only [cvFunctional, (reference_hasDerivAt _).deriv, lagrangian, velocity,
      zero_pow (by decide : (2 : ℕ) ≠ 0), intervalIntegral.integral_zero, add_zero]
  intro y _
  rw [hcost]
  change 0 ≤ (∫ t in 0..1, (deriv y t).1 ^ 2) + 0
  simpa only [add_zero] using
    intervalIntegral.integral_nonneg (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (fun t _ => sq_nonneg ((deriv y t).1))

/-- The new theorem yields energy conservation for this actual minimizer. -/
theorem energy_conserved : ∀ t ∈ Icc 0 (1 : ℝ),
    energyCurve lagrangian reference velocity t = energyCurve lagrangian reference velocity 0 :=
  energy_eq_of_cvFunctional_min lagrangian (fun _ => 0) lagrangian_contDiff
    reference_hasDerivAt velocity_continuous (by norm_num) reference_optimal

/-- The removed acceleration assumption really fails at an interior time. -/
theorem velocity_not_differentiable : ¬ DifferentiableAt ℝ velocity (1 / 2) := by
  intro h
  have hcusp : DifferentiableAt ℝ (fun t : ℝ => |t - 1 / 2|) (1 / 2) := h.snd
  have hshift : DifferentiableAt ℝ (fun t : ℝ => |t - 1 / 2|) (0 + 1 / 2) := by
    simpa only [zero_add] using hcusp
  have habs := hshift.comp 0 ((differentiableAt_id (𝕜 := ℝ)).add_const (1 / 2))
  apply not_differentiableAt_abs_zero
  simpa only [Function.comp_def, add_sub_cancel_right, id_eq] using habs

end KirkMedhin.WeakDuBoisReymondRegression

#print axioms KirkMedhin.WeakDuBoisReymondRegression.reference_optimal
#print axioms KirkMedhin.WeakDuBoisReymondRegression.energy_conserved
#print axioms KirkMedhin.WeakDuBoisReymondRegression.velocity_not_differentiable
