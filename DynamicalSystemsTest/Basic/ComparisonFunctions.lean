/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Basic.ComparisonFunctions
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Positive-definite comparison regression examples

A smooth positive-definite function can decay to zero at infinity along a ray. Thus
continuity and finite dimensionality do not repair the former unrestricted global
statement. The same function does have comparison bounds on every closed ball.
A radially unbounded quadratic function exercises the global theorem.
-/

@[expose] public noncomputable section

open NNReal Filter Topology

namespace ComparisonFunctionTests

/-- Smooth and positive definite, but decays to zero along the positive half-line. -/
def decayingPositiveDefinite (x : ℝ) : ℝ := x ^ 2 * Real.exp (-x)

theorem decaying_continuous : Continuous decayingPositiveDefinite := by
  unfold decayingPositiveDefinite
  fun_prop

theorem decaying_nonneg (x : ℝ) : 0 ≤ decayingPositiveDefinite x :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem decaying_zero_iff (x : ℝ) : decayingPositiveDefinite x = 0 ↔ x = 0 := by
  simp [decayingPositiveDefinite]

/-- Even smooth positive definiteness on `ℝ` does not give a global class-`K` lower bound. -/
theorem no_global_classK_lower_bound :
    ¬ ∃ α : ℝ≥0 → ℝ≥0, MemK α ∧
      ∀ x : ℝ, (α ‖x‖₊ : ℝ) ≤ decayingPositiveDefinite x := by
  rintro ⟨α, hα, hbound⟩
  have hpos : (0 : ℝ) < α 1 := by exact_mod_cast hα.pos (by norm_num)
  have hlim : Tendsto decayingPositiveDefinite atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have hle : (α 1 : ℝ) ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hnorm : (1 : ℝ≥0) ≤ ‖x‖₊ := by
      change (1 : ℝ) ≤ ‖x‖
      simpa only [Real.norm_eq_abs] using hx.trans (le_abs_self x)
    exact (show (α 1 : ℝ) ≤ α ‖x‖₊ from hα.strictMono.monotone hnorm).trans (hbound x)
  exact (not_le_of_gt hpos) hle

/-- The local theorem applies even when every global class-`K` lower bound fails. -/
theorem decaying_local_bounds (r : ℝ) :
    ∃ α₁ α₂ : ℝ≥0 → ℝ≥0, MemKI α₁ ∧ MemKI α₂ ∧
      ∀ x ∈ Metric.closedBall (0 : ℝ) r,
        (α₁ ‖x‖₊ : ℝ) ≤ decayingPositiveDefinite x ∧
          decayingPositiveDefinite x ≤ α₂ ‖x‖₊ :=
  ComparisonFunction.exists_memKI_bounds_on_closedBall decayingPositiveDefinite r
    decaying_continuous.continuousOn (fun x _ ↦ decaying_nonneg x)
    (fun x _ ↦ decaying_zero_iff x)

/-- The global theorem applies to a radially unbounded quadratic Lyapunov function. -/
theorem quadratic_global_bounds :
    ∃ α₁ α₂ : ℝ≥0 → ℝ≥0, MemKI α₁ ∧ MemKI α₂ ∧
      ∀ x : ℝ, (α₁ ‖x‖₊ : ℝ) ≤ x ^ 2 ∧ x ^ 2 ≤ α₂ ‖x‖₊ := by
  apply ComparisonFunction.exists_memKI_bounds_of_radiallyUnbounded (fun x : ℝ ↦ x ^ 2)
    (by fun_prop) (fun x ↦ sq_nonneg x) (fun x ↦ sq_eq_zero_iff)
  have hlim : Tendsto (fun x : ℝ ↦ ‖x‖ ^ 2) (cocompact ℝ) atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_norm_cocompact_atTop
  simpa only [Real.norm_eq_abs, sq_abs] using hlim

end ComparisonFunctionTests

#print axioms MemKI.surjective
#print axioms MemKI.symm
#print axioms ComparisonFunction.exists_memKI_le_of_coercive
#print axioms ComparisonFunction.exists_memKI_sandwich_of_coercive
#print axioms ComparisonFunction.exists_memKI_sandwich_on_isCompact
#print axioms ComparisonFunction.exists_memKI_bounds_on_closedBall
#print axioms ComparisonFunction.exists_memKI_bounds_of_radiallyUnbounded
#print axioms ComparisonFunctionTests.no_global_classK_lower_bound
#print axioms ComparisonFunctionTests.decaying_local_bounds
#print axioms ComparisonFunctionTests.quadratic_global_bounds
