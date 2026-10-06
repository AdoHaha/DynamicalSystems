import DynamicalSystems.OptimalControl.ContinuousTime.OrdinaryControlExistence
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Set MeasureTheory OptimalControl
open scoped BoundedContinuousFunction NNReal

local instance : Nonempty (Icc (-1 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩

-- A concrete integrator with a quadratic effort cost and an endpoint constraint.
noncomputable def integratorProblem : BoundedContinuousProblem ℝ (Icc (-1 : ℝ) 1) where
  horizon := 1
  horizon_pos := by norm_num
  initial := 0
  dynamics := fun _ _ u => (u : ℝ)
  dynamics_continuous := continuous_subtype_val.comp continuous_snd
  velocityBound := 1
  dynamics_bound := fun _ _ u => by simpa only [Real.norm_eq_abs, NNReal.coe_one] using abs_le.mpr u.2
  runningCost := fun _ _ u => (u : ℝ) ^ 2
  runningCost_continuous := (continuous_subtype_val.comp continuous_snd).pow 2
  terminalCost := fun _ => 0
  terminalCost_continuous := continuous_const
  target := {0}
  target_closed := isClosed_singleton
  stateConstraint := fun _ => univ
  stateConstraint_closed := fun _ => isClosed_univ

noncomputable def integratorAffine : integratorProblem.AffineConvexData where
  drift := fun _ _ => 0
  inputMap := fun _ _ => ContinuousLinearMap.id ℝ ℝ
  dynamics_eq := fun _ _ _ => by simp [integratorProblem]
  costExtension := fun _ _ u => u ^ 2
  cost_eq := fun _ _ _ => rfl
  cost_convex := fun _ _ => ((show Even (2 : ℕ) by decide).convexOn_pow (𝕜 := ℝ)).subset (subset_univ _) (convex_Icc _ _)

theorem integrator_feasible :
    ∃ x u, integratorProblem.OrdinaryAdmissible x u := by
  refine ⟨BoundedContinuousFunction.const _ 0, fun _ => ⟨0, by norm_num⟩,
    measurable_const, ?_, ?_, ?_⟩
  · intro t
    change (0 : ℝ) = 0 + (1 : ℝ) • ∫ _ in Ioc (timeZero 1 _) t, (0 : ℝ) ∂horizonProbability 1 _
    simp
  · change (0 : ℝ) ∈ ({0} : Set ℝ)
    simp
  · intro t
    trivial

example : ∃ x u, integratorProblem.OrdinaryAdmissible x u ∧
    ∀ y v, integratorProblem.OrdinaryAdmissible y v →
      integratorProblem.ordinaryCost x u ≤ integratorProblem.ordinaryCost y v :=
  integratorProblem.exists_ordinary_minimizer integratorAffine (convex_Icc _ _) integrator_feasible

#print axioms BoundedContinuousFunction.isCompact_lipschitzPaths
#print axioms OptimalControl.isClosed_relaxedTrajectoryGraph
#print axioms OptimalControl.isCompact_relaxedTrajectoryGraph
#print axioms OptimalControl.BoundedContinuousProblem.exists_relaxed_minimizer
#print axioms OptimalControl.BoundedContinuousProblem.exists_ordinary_minimizer
