import DynamicalSystems.OptimalControl.ContinuousTime.LinearGrowthControlExistence
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Set MeasureTheory OptimalControl
open scoped BoundedContinuousFunction NNReal

local instance : Nonempty (Icc (-1 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩

-- Unlike the bounded-velocity theorem, this example has nonzero state drift.
noncomputable def linearGrowthProblem : LinearGrowthProblem ℝ (Icc (-1 : ℝ) 1) where
  horizon := 2
  horizon_pos := by norm_num
  initial := 0
  dynamics := fun _ x u ↦ x + (u : ℝ)
  dynamics_continuous := continuous_fst.snd.add (continuous_subtype_val.comp continuous_snd)
  growthConstant := 1
  growthRate := 1
  dynamics_growth := fun _ x u ↦ by
    have hu : ‖(u : ℝ)‖ ≤ 1 := by simpa [Real.norm_eq_abs] using abs_le.mpr u.2
    simpa only [NNReal.coe_one, one_mul, add_comm] using
      (norm_add_le x (u : ℝ)).trans (add_le_add_right hu ‖x‖)
  runningCost := fun _ _ u ↦ (u : ℝ) ^ 2
  runningCost_continuous := (continuous_subtype_val.comp continuous_snd).pow 2
  terminalCost := fun _ ↦ 0
  terminalCost_continuous := continuous_const
  target := {0}
  target_closed := isClosed_singleton
  stateConstraint := fun _ ↦ univ
  stateConstraint_closed := fun _ ↦ isClosed_univ

noncomputable def linearGrowthAffine : linearGrowthProblem.AffineConvexData where
  drift := fun _ x ↦ x
  inputMap := fun _ _ ↦ ContinuousLinearMap.id ℝ ℝ
  dynamics_eq := fun _ _ _ ↦ rfl
  costExtension := fun _ _ u ↦ u ^ 2
  cost_eq := fun _ _ _ ↦ rfl
  cost_convex := fun _ _ ↦ ((show Even (2 : ℕ) by decide).convexOn_pow (𝕜 := ℝ)).subset
    (subset_univ _) (convex_Icc _ _)

theorem linearGrowth_feasible : ∃ x u, linearGrowthProblem.OrdinaryAdmissible x u := by
  refine ⟨BoundedContinuousFunction.const _ 0, fun _ ↦ ⟨0, by norm_num⟩,
    measurable_const, ?_, ?_, ?_⟩
  · intro t
    change (0 : ℝ) = 0 + (2 : ℝ) • ∫ _ in Ioc (timeZero (2) _) t,
      (0 + 0 : ℝ) ∂horizonProbability (2) _
    simp
  · change (0 : ℝ) ∈ ({0} : Set ℝ)
    simp
  · intro t
    trivial

-- The original field is genuinely outside the previous global bounded-velocity scope.
theorem linearGrowth_dynamics_not_bounded :
    ¬ ∃ M : ℝ, ∀ t x u, ‖linearGrowthProblem.dynamics t x u‖ ≤ M := by
  rintro ⟨M, hM⟩
  have h := hM (timeZero (2) (by norm_num)) (|M| + 1) ⟨0, by norm_num⟩
  change ‖|M| + 1 + 0‖ ≤ M at h
  rw [add_zero, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  linarith [le_abs_self M]

example : ∃ x u, linearGrowthProblem.OrdinaryAdmissible x u ∧
    ∀ y v, linearGrowthProblem.OrdinaryAdmissible y v →
      linearGrowthProblem.ordinaryCost x u ≤ linearGrowthProblem.ordinaryCost y v :=
  linearGrowthProblem.exists_ordinary_minimizer_global linearGrowthAffine (convex_Icc _ _)
    linearGrowth_feasible

#print axioms OptimalControl.IsRelaxedTrajectory.norm_le_of_linear_growth
#print axioms OptimalControl.LinearGrowthProblem.exists_relaxed_minimizer_global
#print axioms OptimalControl.LinearGrowthProblem.exists_ordinary_minimizer_global

#print axioms OptimalControl.IsRelaxedTrajectory.norm_le_gronwall_of_linear_growth
