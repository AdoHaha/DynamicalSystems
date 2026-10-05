/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceContinuation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Regression examples for local-Lipschitz global existence

The nonlinear sine example exercises a bounded smooth vector field with
unbounded spatial derivative. The time-linear example exercises a growth
constant which is uniform on compact time intervals but not on the whole line.
-/

open Set
open scoped NNReal

namespace GlobalExistenceGrowthRegression

/-- A bounded nonlinear smooth field is complete by the local-Lipschitz theorem. -/
theorem sin_square_complete :
    IsCompleteVectorField (fun (_ : ℝ) (x : ℝ) => Real.sin (x ^ 2)) := by
  apply UniformlyLocallyLipschitz.isCompleteVectorField_of_bound
    (C := 0) (C' := 1)
  · exact ContDiff.uniformlyLocallyLipschitz (by fun_prop)
  · fun_prop
  · intro t x
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (x ^ 2)

/-- The coefficient `t` has a uniform bound on each compact time interval. -/
theorem time_linear_growth : LocallyUniformLinearGrowth (fun (t x : ℝ) => t * x) := by
  intro a b
  refine ⟨⟨|a| + |b|, by positivity⟩, 0, fun t ht x => ?_⟩
  have htime : |t| ≤ |a| + |b| := abs_le.mpr
    ⟨by linarith [ht.1, neg_abs_le a, abs_nonneg b],
      by linarith [ht.2, le_abs_self b, abs_nonneg a]⟩
  change |t * x| ≤ (|a| + |b|) * |x| + 0
  rw [abs_mul, add_zero]
  exact mul_le_mul_of_nonneg_right htime (abs_nonneg x)

/-- Time-dependent growth constants do not prevent global existence. -/
theorem time_linear_complete : IsCompleteVectorField (fun (t x : ℝ) => t * x) := by
  apply UniformlyLocallyLipschitz.isCompleteVectorField
  · exact ContDiff.uniformlyLocallyLipschitz (by fun_prop)
  · fun_prop
  · exact time_linear_growth

#print axioms UniformlyLocallyLipschitz.isCompleteVectorField
#print axioms sin_square_complete
#print axioms time_linear_complete

end GlobalExistenceGrowthRegression
