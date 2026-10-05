/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.DuBoisReymondLowRegularity
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousDuBoisReymond
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A genuinely time-dependent weak du Bois–Reymond regression

For `L(t,x,v) = v.1² - t`, the reference integrates the continuous velocity
`(0, |t - 1/2|)`. Its velocity is not differentiable at the interior time `1/2`.
The actual minimum is `-1/2`, its time partial is `-1`, and its energy is `t`.
The nonautonomous minimum theorem supplies the compensated conservation law
and the interior derivative, checking the time-partial sign without an
acceleration assumption.
-/

open MeasureTheory Set
open scoped Interval

namespace NonautonomousDuBoisReymond.Examples.NondifferentiableVelocity

open DuBoisReymond.Examples.NondifferentiableVelocity TimeReparametrization

/-- A quadratic velocity penalty with an explicit, nonzero time partial. -/
def lagrangian (t : ℝ) (_x v : ℝ × ℝ) : ℝ := v.1 ^ 2 - t

/-- The time-dependent density is jointly continuously differentiable. -/
theorem lagrangian_contDiff : ContDiff ℝ 1 (uncurryLagrangian lagrangian) :=
  (contDiff_snd.snd.fst.pow 2).sub contDiff_fst

/-- The explicit time term contributes negative one half to the actual action. -/
theorem integral_time_term : (∫ t in (0 : ℝ)..1, -t) = -(1 / 2 : ℝ) := by
  rw [intervalIntegral.integral_neg, integral_id]
  norm_num

/-- The actual action of the reference, including the time-dependent contribution. -/
theorem reference_cost : cvFunctional lagrangian (fun _ => 0) 1 reference = -(1 / 2 : ℝ) := by
  simpa [cvFunctional, (reference_hasDerivAt _).deriv, lagrangian, velocity]
    using integral_time_term

/-- Every actual competitor has cost at least the reference cost. The undefined
Bochner integral is zero, which also respects this lower bound. -/
theorem cost_lower_bound (y : ℝ → ℝ × ℝ) :
    -(1 / 2 : ℝ) ≤ cvFunctional lagrangian (fun _ => 0) 1 y := by
  change -(1 / 2 : ℝ) ≤ (∫ t in (0 : ℝ)..1, (deriv y t).1 ^ 2 - t) + 0
  simp only [add_zero]
  by_cases hi : IntervalIntegrable (fun t : ℝ => (deriv y t).1 ^ 2 - t) volume 0 1
  · have hn : Continuous (fun t : ℝ => -t) := continuous_id.neg
    have hb := intervalIntegral.integral_mono (by norm_num : (0 : ℝ) ≤ 1)
      (hn.intervalIntegrable 0 1) hi
      (fun t => by linarith [sq_nonneg ((deriv y t).1)])
    simpa only [integral_time_term] using hb
  · rw [intervalIntegral.integral_undef hi]
    norm_num

/-- The same genuine reference is feasible in the theorem's ambient variational class. -/
theorem reference_is_feasible : reference ∈
    fixedEndpointPiecewiseC1Curves 1 (reference 0) (reference 1) :=
  reference_feasible

/-- Genuine fixed-endpoint piecewise-C1 optimality follows from the cost comparison. -/
theorem reference_optimal : IsMinOn (cvFunctional lagrangian (fun _ => 0) 1)
    (fixedEndpointPiecewiseC1Curves 1 (reference 0) (reference 1)) reference := by
  intro y _
  rw [reference_cost]
  exact cost_lower_bound y

/-- The acceleration hypothesis fails at an interior point of this actual minimizer. -/
theorem reference_velocity_not_differentiable :
    ¬ DifferentiableAt ℝ velocity (1 / 2) := velocity_not_differentiable

/-- The genuine partial time derivative has the nonzero value minus one. -/
theorem timePartial_eq_neg_one (t : ℝ) :
    NonautonomousDuBoisReymond.timePartialCurve lagrangian reference velocity t = -1 := by
  unfold NonautonomousDuBoisReymond.timePartialCurve lagrangian
  exact ((hasDerivAt_id t).const_sub ((velocity t).1 ^ 2)).deriv

/-- The actual momentum vanishes along the reference in both components. -/
theorem momentum_eq_zero (t : ℝ) :
    fderiv ℝ (lagrangian t (reference t)) (velocity t) = 0 := by
  change fderiv ℝ (fun v : ℝ × ℝ => v.1 ^ 2 - t) (velocity t) = 0
  have h := ((hasFDerivAt_fst (𝕜 := ℝ) (p := velocity t)).pow 2).sub_const t
  simpa [velocity] using h.fderiv

/-- The energy is genuinely time dependent, equal to physical time. -/
theorem energy_eq_time (t : ℝ) :
    NonautonomousDuBoisReymond.energyCurve lagrangian reference velocity t = t := by
  change (fderiv ℝ (lagrangian t (reference t)) (velocity t)) (velocity t) -
    lagrangian t (reference t) (velocity t) = t
  rw [momentum_eq_zero]
  simp [lagrangian, velocity]

/-- The new nonautonomous theorem applies to this actual minimizer and returns
both compensated conservation and the interior energy derivative. -/
theorem reference_weak_duBoisReymond :
    (∀ t ∈ Icc 0 (1 : ℝ),
      NonautonomousDuBoisReymond.energyCurve lagrangian reference velocity t +
        (∫ s in 0..t,
          NonautonomousDuBoisReymond.timePartialCurve lagrangian reference velocity s) =
      NonautonomousDuBoisReymond.energyCurve lagrangian reference velocity 0) ∧
    (∀ t ∈ Ioo 0 (1 : ℝ),
      HasDerivAt (NonautonomousDuBoisReymond.energyCurve lagrangian reference velocity)
        (-NonautonomousDuBoisReymond.timePartialCurve lagrangian reference velocity t) t) :=
  NonautonomousDuBoisReymond.weak_duBoisReymond_of_cvFunctional_min lagrangian
    (fun _ => 0) lagrangian_contDiff reference_hasDerivAt velocity_continuous
    (by norm_num) reference_optimal

/-- Compensating by the actual time partial makes the energy constant, as derived
from the variational theorem rather than a supplied energy equation. -/
theorem compensated_energy_eq_zero (t : ℝ) (ht : t ∈ Icc 0 1) :
    NonautonomousDuBoisReymond.energyCurve lagrangian reference velocity t +
      (∫ s in 0..t,
        NonautonomousDuBoisReymond.timePartialCurve lagrangian reference velocity s) = 0 := by
  simpa only [energy_eq_time] using reference_weak_duBoisReymond.1 t ht

/-- The weak theorem derives positive unit energy slope even though the velocity
fails to be differentiable at `1/2`. -/
theorem energy_hasDerivAt_one (t : ℝ) (ht : t ∈ Ioo 0 1) :
    HasDerivAt (NonautonomousDuBoisReymond.energyCurve lagrangian reference velocity) 1 t := by
  simpa only [timePartial_eq_neg_one, neg_neg] using reference_weak_duBoisReymond.2 t ht

end NonautonomousDuBoisReymond.Examples.NondifferentiableVelocity
