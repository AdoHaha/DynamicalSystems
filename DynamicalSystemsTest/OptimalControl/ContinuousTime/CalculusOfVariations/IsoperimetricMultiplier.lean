/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.IsoperimetricEulerLagrange
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A scalar isoperimetric problem with a nonzero normal multiplier

On the unit horizon, minimize `∫ (y'² + y)` among C1 curves with both endpoints
zero and integral constraint `∫ y = 0`. The zero curve is an actual constrained
minimum. The direction `t ↦ t * (1 - t)` makes the constraint derivative `1 / 6`,
so the normal-multiplier theorem applies to concrete regular data.
-/

@[expose] public section

open MeasureTheory Set
open scoped Interval

namespace IsoperimetricVariation.Examples.NonzeroMultiplier



/-- The running cost penalizes squared velocity and rewards signed state. -/
def runningCost (_t y v : ℝ) : ℝ := v ^ 2 + y

/-- The isoperimetric integrand is the state itself. -/
def constraintCost (_t y _v : ℝ) : ℝ := y

/-- No terminal penalty is present. -/
def terminalCost (_y : ℝ) : ℝ := 0

/-- The candidate minimizing curve is identically zero. -/
def reference (_t : ℝ) : ℝ := 0

/-- A smooth endpoint-zero direction with nonzero constraint variation. -/
def regularDirection (t : ℝ) : ℝ := t * (1 - t)

/-- The running cost satisfies the joint C2 hypothesis. -/
theorem runningCost_contDiff : ContDiff ℝ 2 (uncurryLagrangian runningCost) := by
  exact (contDiff_snd.snd.pow 2).add contDiff_snd.fst

/-- The constraint integrand satisfies the joint C2 hypothesis. -/
theorem constraintCost_contDiff : ContDiff ℝ 2 (uncurryLagrangian constraintCost) := by
  exact contDiff_snd.fst

/-- The terminal penalty satisfies the C1 hypothesis. -/
theorem terminalCost_contDiff : ContDiff ℝ 1 terminalCost := contDiff_const

/-- The reference curve satisfies the C2 hypothesis. -/
theorem reference_contDiff : ContDiff ℝ 2 reference := contDiff_const

/-- The regular direction is continuously differentiable. -/
theorem regularDirection_contDiff : ContDiff ℝ 1 regularDirection :=
  contDiff_id.mul (contDiff_const.sub contDiff_id)

/-- The zero curve belongs to the actual fixed-endpoint admissible class. -/
theorem reference_admissible : reference ∈ fixedEndpointC1Curves 1 0 0 := by
  exact ⟨reference_contDiff.of_le (by norm_num), rfl, rfl⟩

/-- The candidate's actual cost is zero. -/
theorem reference_cost : cvFunctional runningCost terminalCost 1 reference = 0 := by
  change (∫ t in (0 : ℝ)..1, deriv (fun _ : ℝ ↦ (0 : ℝ)) t ^ 2 + 0) + 0 = 0
  simp

/-- The candidate's actual isoperimetric constraint value is zero. -/
theorem reference_constraint :
    cvFunctional constraintCost (fun _ ↦ 0) 1 reference = 0 := by
  simp [cvFunctional, constraintCost, reference]

/-- The zero curve minimizes the actual cost on the actual constrained class:
the constraint cancels the state term and the remaining squared-velocity
integral is nonnegative. -/
theorem reference_isMinOn : IsMinOn (cvFunctional runningCost terminalCost 1)
    {y | y ∈ fixedEndpointC1Curves 1 0 0 ∧
      cvFunctional constraintCost (fun _ ↦ 0) 1 y =
        cvFunctional constraintCost (fun _ ↦ 0) 1 reference} reference := by
  intro y hy
  have hsq : IntervalIntegrable (fun t ↦ deriv y t ^ 2) volume 0 1 :=
    (hy.1.1.continuous_deriv_one.pow 2).intervalIntegrable 0 1
  have hyi : IntervalIntegrable y volume 0 1 :=
    hy.1.1.continuous.intervalIntegrable 0 1
  have hconstraint : (∫ t in 0..1, y t) = 0 := by
    simpa only [cvFunctional, constraintCost, reference, intervalIntegral.integral_zero,
      add_zero] using hy.2
  rw [reference_cost]
  change 0 ≤ (∫ t in 0..1, deriv y t ^ 2 + y t) + 0
  rw [intervalIntegral.integral_add hsq hyi, hconstraint, add_zero, add_zero]
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun t ↦ sq_nonneg _)

/-- The regular direction has nonzero integral. -/
theorem regularDirection_integral :
    (∫ t in (0 : ℝ)..1, regularDirection t) = 1 / 6 := by
  have hfun : regularDirection = fun t : ℝ ↦ t - t ^ 2 := by
    funext t
    simp only [regularDirection]
    ring
  have hlin : Continuous (fun t : ℝ ↦ t) := continuous_id
  have hsq : Continuous (fun t : ℝ ↦ t ^ 2) := by fun_prop
  rw [hfun, intervalIntegral.integral_sub (hlin.intervalIntegrable 0 1)
    (hsq.intervalIntegrable 0 1), integral_id, integral_pow]
  norm_num

/-- The actual constraint first variation is exactly one sixth. -/
theorem constraint_firstVariation :
    firstVariation constraintCost (fun _ ↦ 0) 1 reference regularDirection = 1 / 6 := by
  simp [firstVariation, constraintCost, regularDirection_integral]

/-- The actual running-cost first variation is also one sixth. -/
theorem running_firstVariation :
    firstVariation runningCost terminalCost 1 reference regularDirection = 1 / 6 := by
  change firstVariation runningCost (fun _ ↦ 0) 1 (fun _ ↦ 0) regularDirection = 1 / 6
  have hstate : fderiv ℝ (fun y : ℝ ↦ (0 : ℝ) ^ 2 + y) 0 =
      ContinuousLinearMap.id ℝ ℝ := by
    simp
  have hvelocity : fderiv ℝ (fun v : ℝ ↦ v ^ 2 + 0) 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    rw [fderiv_eq_deriv_mul]
    simp
  simp only [firstVariation, runningCost, deriv_const, hstate, hvelocity]
  simp [regularDirection_integral]

/-- The data satisfy the genuine normality hypothesis with an explicit
endpoint-zero constraint direction. -/
theorem constraint_regular : ∃ ξ : ℝ → ℝ, ContDiff ℝ 1 ξ ∧ ξ 0 = 0 ∧ ξ 1 = 0 ∧
    firstVariation constraintCost (fun _ ↦ 0) 1 reference ξ ≠ 0 := by
  refine ⟨regularDirection, regularDirection_contDiff, ?_, ?_, ?_⟩
  · simp [regularDirection]
  · simp [regularDirection]
  · rw [constraint_firstVariation]
    norm_num

/-- On the regular direction, augmented stationarity determines the multiplier. -/
theorem augmented_firstVariation (lam : ℝ) :
    firstVariation (fun t y v ↦ runningCost t y v + lam * constraintCost t y v)
      terminalCost 1 reference regularDirection = (1 + lam) / 6 := by
  rw [_root_.firstVariation_add_smul runningCost constraintCost terminalCost lam 1
    reference regularDirection (runningCost_contDiff.of_le (by norm_num))
    (constraintCost_contDiff.of_le (by norm_num))
    (reference_contDiff.of_le (by norm_num)) regularDirection_contDiff,
    running_firstVariation, constraint_firstVariation]
  ring

/-- The multiplier for the concrete stationary augmented problem must be minus one. -/
theorem multiplier_eq_neg_one (lam : ℝ)
    (hvan : HasVanishingFirstVariation
      (fun t y v ↦ runningCost t y v + lam * constraintCost t y v)
      terminalCost 1 reference) : lam = -1 := by
  have hdir : ∀ t, HasDerivAt regularDirection (deriv regularDirection t) t :=
    fun t ↦ (regularDirection_contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have h := hvan regularDirection hdir (by simp [regularDirection]) (by simp [regularDirection])
  rw [augmented_firstVariation] at h
  linarith

/-- The general isoperimetric theorem applies to the concrete constrained
minimum and produces augmented stationarity on every differentiable
endpoint-zero direction together with the exact Euler–Lagrange equation.
Its normal multiplier is necessarily minus one. -/
theorem constrained_augmentedEulerLagrange :
    ∃ lam : ℝ, lam = -1 ∧
      HasVanishingFirstVariation
        (fun t y v ↦ runningCost t y v + lam * constraintCost t y v)
        terminalCost 1 reference ∧
      eulerLagrange (fun t y v ↦ runningCost t y v + lam * constraintCost t y v)
        1 reference := by
  obtain ⟨lam, hvan, hEL⟩ := _root_.IsoperimetricVariation.augmentedEulerLagrange_of_isoperimetric
    runningCost constraintCost terminalCost 1 reference runningCost_contDiff
    constraintCost_contDiff terminalCost_contDiff reference_contDiff (by norm_num)
    reference_isMinOn constraint_regular
  exact ⟨lam, multiplier_eq_neg_one lam hvan, hvan, hEL⟩

end IsoperimetricVariation.Examples.NonzeroMultiplier
