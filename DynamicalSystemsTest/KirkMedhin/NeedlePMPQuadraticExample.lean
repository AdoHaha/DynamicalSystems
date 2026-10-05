/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.NeedlePMP

/-!
# A nonzero-costate example with a quadratic state cost

For `x' = u`, `U = [-1,1]`, and `T = 1`, minimize

  integral ((x(t) + t)^2 + u(t)^2) dt + 2 x(1).

The reference `x(t) = -t`, `u(t) = -1` is an actual integral optimum with
value `-1`. Its costate is `p(t) = 2`. The lower bound is proved against
every integral competitor by completing the square, independently of PMP.
The running cost is quadratic in the state and is not globally Lipschitz.
-/

open Set MeasureTheory
open scoped Interval NNReal

namespace K1QuadraticExample

/-- Scalar integrator with a quadratic tracking cost and a linear terminal penalty. -/
def problem : ContinuousOCP ℝ ℝ where
  T := 1
  f := fun _ _ u => u
  L := fun t x u => (x + t) ^ 2 + u ^ 2
  K := fun x => 2 * x
  controlSet := Icc (-1) 1

/-- The optimal trajectory, moving at the lowest admissible velocity. -/
def referenceState (t : ℝ) : ℝ := -t
/-- The constant boundary control generating the reference trajectory. -/
def referenceControl (_ : ℝ) : ℝ := -1
/-- The explicit nonzero costate, matching the terminal-cost gradient. -/
def referenceCostate (_ : ℝ) : ℝ := 2

theorem reference_admissible :
    NeedleIntegralModel.IsIntegralAdmissiblePair problem 0 referenceState referenceControl := by
  apply NeedleIntegralModel.of_classical problem 0 referenceState referenceControl
    (by norm_num [problem])
  · refine ⟨by simp [referenceState], ?_, ?_, ?_⟩
    · intro t _
      norm_num [problem, referenceControl]
    · intro t _
      change HasDerivAt (fun s : ℝ => -s) (-1) t
      exact (hasDerivAt_id t).neg
    · simp [problem, referenceState, referenceControl]
  · exact intervalIntegrable_const

theorem reference_cost : continuousTotalCost problem referenceState referenceControl = -1 := by
  norm_num [continuousTotalCost, problem, referenceState, referenceControl]

/-- A lower bound for every actual integral competitor. The endpoint relation
is used to replace the terminal cost by the integral of `2u`. -/
theorem cost_lower_bound (y v : ℝ → ℝ)
    (h : NeedleIntegralModel.IsIntegralAdmissiblePair problem 0 y v) :
    -1 ≤ continuousTotalCost problem y v := by
  have hvi : IntervalIntegrable v volume 0 1 := h.2.2.1
  have hLi : IntervalIntegrable (fun t => (y t + t) ^ 2 + (v t) ^ 2) volume 0 1 :=
    h.2.2.2.2
  have hyT : y 1 = ∫ t in (0 : ℝ)..1, v t := by
    simpa only [problem, zero_add] using h.2.2.2.1 1 (by norm_num [problem])
  have hbasei : IntervalIntegrable (fun t => (-2) * v t - 1) volume 0 1 :=
    (hvi.const_mul (-2)).sub intervalIntegrable_const
  have hpoint (t : ℝ) : (-2) * v t - 1 ≤ (y t + t) ^ 2 + (v t) ^ 2 := by
    nlinarith [sq_nonneg (y t + t), sq_nonneg (v t + 1)]
  have hineq := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    hbasei hLi (fun t _ => hpoint t)
  have hbase : (∫ t in (0 : ℝ)..1, (-2) * v t - 1) =
      (-2) * (∫ t in (0 : ℝ)..1, v t) - 1 := by
    rw [intervalIntegral.integral_sub (hvi.const_mul (-2)) intervalIntegrable_const,
      intervalIntegral.integral_const_mul]
    norm_num
  rw [hbase] at hineq
  change -1 ≤ (∫ t in (0 : ℝ)..1, (y t + t) ^ 2 + (v t) ^ 2) + 2 * y 1
  rw [hyT]
  linarith

theorem reference_optimal :
    NeedleIntegralModel.IsIntegralOptimalPair problem 0 referenceState referenceControl := by
  refine ⟨reference_admissible, ?_⟩
  intro y v h
  rw [reference_cost]
  exact cost_lower_bound y v h

/-- Directly checking the unique expected costate is an independent check of
the sign and terminal convention used by the general theorem. -/
theorem explicit_costate :
    costateEquation problem.L problem.f problem.T referenceState referenceControl referenceCostate ∧
      transversalityCondition problem.K problem.T referenceState referenceCostate ∧
      HamiltonianMinimizing problem.L problem.f problem.controlSet problem.T
        referenceState referenceControl referenceCostate := by
  refine ⟨?_, ?_, ?_⟩
  · intro t _
    have hH : HasDerivAt
        (fun y => hamiltonianOf problem.L problem.f t y (referenceControl t) (referenceCostate t))
        0 (referenceState t) := by
      have h := (((hasDerivAt_id (-t)).add_const t).pow 2).add_const (1 - 2)
      convert h using 1
      · simp only [hamiltonianOf, problem, referenceControl, even_two, Even.neg_pow,
          one_pow, referenceCostate, RCLike.inner_apply, conj_trivial, neg_mul, one_mul,
          id_eq, Pi.pow_apply]
        funext y
        ring
      · simp only [Nat.cast_ofNat, id_eq, neg_add_cancel, Nat.add_one_sub_one, pow_one,
          mul_zero, mul_one]
      · rfl
    rw [hH.hasGradientAt'.gradient]
    rw [neg_zero]
    change HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 t
    exact hasDerivAt_const t (2 : ℝ)
  · have hK : HasDerivAt problem.K 2 (referenceState problem.T) := by
      simpa [problem] using (hasDerivAt_id (referenceState problem.T)).const_mul 2
    change (2 : ℝ) = gradient problem.K (referenceState problem.T)
    rw [hK.hasGradientAt'.gradient]
  · intro t _ v _
    simp only [problem, hamiltonianOf, referenceState, referenceControl, referenceCostate,
      Real.inner_apply, neg_add_cancel, zero_pow (by decide : 2 ≠ 0), zero_add]
    nlinarith [sq_nonneg (v + 1)]

theorem costate_nonzero : referenceCostate 1 ≠ 0 := by norm_num [referenceCostate]


/-- The genuine spatial derivative of the quadratic running cost. -/
noncomputable def runningDerivative (t y : ℝ) : ℝ →L[ℝ] ℝ :=
  (2 * (y + t)) • ContinuousLinearMap.id ℝ ℝ

theorem has_running_derivative (t y : ℝ) :
    HasFDerivAt (fun z => problem.L t z (referenceControl t)) (runningDerivative t y) y := by
  rw [hasFDerivAt_iff_hasDerivAt]
  have h := (((hasDerivAt_id y).add_const t).pow 2).add_const ((-1 : ℝ) ^ 2)
  convert h using 1 <;> simp [problem, referenceControl, runningDerivative]


theorem runningDerivative_continuous :
    Continuous (fun q : ℝ × ℝ => runningDerivative q.1 q.2) := by
  change Continuous (fun q : ℝ × ℝ => (2 * (q.2 + q.1)) • ContinuousLinearMap.id ℝ ℝ)
  fun_prop

theorem nominal_dynamics_continuous :
    Continuous (fun q : ℝ × ℝ => problem.f q.1 q.2 (referenceControl q.1)) :=
  continuous_const

theorem test_dynamics_continuous (v : ℝ) :
    Continuous (fun q : ℝ × ℝ => problem.f q.1 q.2 v) := continuous_const

theorem nominal_running_continuous :
    Continuous (fun q : ℝ × ℝ => problem.L q.1 q.2 (referenceControl q.1)) := by
  change Continuous (fun q : ℝ × ℝ => (q.2 + q.1) ^ 2 + (-1 : ℝ) ^ 2)
  fun_prop

theorem test_running_continuous (v : ℝ) :
    Continuous (fun q : ℝ × ℝ => problem.L q.1 q.2 v) := by
  change Continuous (fun q : ℝ × ℝ => (q.2 + q.1) ^ 2 + v ^ 2)
  fun_prop


/-- This example really lies outside a globally Lipschitz running-cost
assumption, so the continuous-branch remainder argument is essential. -/
theorem running_not_globally_lipschitz :
    ¬ ∃ M : ℝ≥0, LipschitzWith M (fun z : ℝ => problem.L 0 z 0) := by
  rintro ⟨M, hM⟩
  have h := hM.dist_le_mul ((M : ℝ) + 1) 0
  have hpos : 0 < (M : ℝ) + 1 := by positivity
  simp only [problem, add_zero, zero_pow (by decide : 2 ≠ 0),
    Real.dist_eq, sub_zero] at h
  rw [abs_of_nonneg (sq_nonneg _), abs_of_pos hpos] at h
  nlinarith [M.property]


/-- Every primitive analytic hypothesis of the general theorem is discharged
for the concrete problem. No PMP conclusion occurs in this certificate. -/
noncomputable def regularity :
    K1NeedlePMP.SmoothNeedleData problem referenceState referenceControl where
  horizon_pos := by norm_num [problem]
  nominal_lipschitz := by
    refine ⟨0, 1, fun _ => LipschitzWith.const (-1), ?_⟩
    intro t
    norm_num [problem, referenceControl]
  test_lipschitz := by
    intro v _
    exact ⟨0, ‖v‖, fun _ => LipschitzWith.const v, fun _ => le_rfl⟩
  nominal_dynamics_continuous := nominal_dynamics_continuous
  test_dynamics_continuous := fun v _ => test_dynamics_continuous v
  nominal_running_continuous := nominal_running_continuous
  test_running_continuous := fun v _ => test_running_continuous v
  dynamicsDerivative := fun _ _ => 0
  has_dynamics_derivative := fun _ _ y => hasFDerivAt_const (-1) y
  dynamics_derivative_continuous := fun _ _ => continuousAt_const
  runningDerivative := runningDerivative
  has_running_derivative := fun t _ y => has_running_derivative t y
  running_derivative_continuous := fun _ _ => runningDerivative_continuous.continuousAt
  terminal_differentiable := by
    change DifferentiableAt ℝ (fun z : ℝ => 2 * z) _
    fun_prop

/-- The new theorem applies to a independently proved optimum and constructs
an actual minimizing costate. Its terminal value is nonzero. -/
theorem pmp_from_general_theorem :
    ∃ p : ℝ → ℝ,
      costateEquation problem.L problem.f problem.T referenceState referenceControl p ∧
      transversalityCondition problem.K problem.T referenceState p ∧
      HamiltonianMinimizing problem.L problem.f problem.controlSet problem.T
        referenceState referenceControl p ∧ p 1 ≠ 0 := by
  obtain ⟨p, hcostate, hterminal, hminimum⟩ :=
    K1NeedlePMP.needleCostate_of_integralOptimality_smooth
      problem 0 referenceState referenceControl regularity reference_optimal
  refine ⟨p, hcostate, hterminal, hminimum, ?_⟩
  have hK : HasDerivAt problem.K 2 (referenceState problem.T) := by
    simpa [problem] using (hasDerivAt_id (referenceState problem.T)).const_mul 2
  change p 1 = gradient problem.K (referenceState problem.T) at hterminal
  rw [hK.hasGradientAt'.gradient] at hterminal
  rw [hterminal]
  norm_num

end K1QuadraticExample
