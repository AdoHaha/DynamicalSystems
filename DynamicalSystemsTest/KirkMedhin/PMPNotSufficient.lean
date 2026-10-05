/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple

/-!
# The existing PMP predicates do not imply optimality

Consider `x' = u`, `T = 1`, `x(0) = 0`, `u ∈ [-1, 1]`, zero running cost,
and terminal cost `K(x) = (x² - 1)²`. The smooth reference `x = u = p = 0`
is admissible and satisfies all three existing PMP predicates, but its cost is
one. The smooth admissible competitor `u = 1`, `x(t) = t` has cost zero.

This is an exact-project regression against an unrestricted PMP-to-optimality
converse. The admissibility and PMP definitions are imported unchanged. Extra
convexity or verification hypotheses are needed for a sufficiency theorem.
-/

@[expose] public section

namespace PMPExamples.NotSufficient

open Set MeasureTheory
open scoped Interval ContDiff

/-- Smooth scalar control problem with a nonconvex terminal penalty. -/
def problem : ContinuousOCP ℝ ℝ where
  T := 1
  f := fun _ _ u ↦ u
  L := fun _ _ _ ↦ 0
  K := fun x ↦ (x ^ 2 - 1) ^ 2
  controlSet := Icc (-1) 1

theorem horizon_pos : 0 < problem.T := by norm_num [problem]

theorem problem_data_smooth :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ × ℝ ↦ problem.f z.1 z.2.1 z.2.2) ∧
    ContDiff ℝ ∞ (fun z : ℝ × ℝ × ℝ ↦ problem.L z.1 z.2.1 z.2.2) ∧
    ContDiff ℝ ∞ problem.K := by
  dsimp [problem]
  exact ⟨by fun_prop, by fun_prop, by fun_prop⟩

theorem reference_admissible :
    IsAdmissiblePair problem 0 (fun _ ↦ 0) (fun _ ↦ 0) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro t _
    norm_num [problem]
  · intro t _
    exact hasDerivAt_const t 0
  · exact intervalIntegrable_const

theorem competitor_admissible :
    IsAdmissiblePair problem 0 (fun t ↦ t) (fun _ ↦ 1) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro t _
    norm_num [problem]
  · intro t _
    exact hasDerivAt_id t
  · exact intervalIntegrable_const

theorem reference_cost :
    continuousTotalCost problem (fun _ ↦ 0) (fun _ ↦ 0) = 1 := by
  norm_num [continuousTotalCost, problem]

theorem competitor_cost :
    continuousTotalCost problem (fun t ↦ t) (fun _ ↦ 1) = 0 := by
  norm_num [continuousTotalCost, problem]

theorem terminal_gradient_zero : gradient problem.K 0 = 0 := by
  change gradient (fun x : ℝ ↦ (x ^ 2 - 1) ^ 2) 0 = 0
  rw [gradient_eq_deriv']
  have hK : HasDerivAt (fun x : ℝ ↦ (x ^ 2 - 1) ^ 2) 0 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).pow 2).sub_const 1).pow 2 using 1 <;> norm_num
    rfl
  exact hK.deriv

theorem reference_costateEquation :
    costateEquation problem.L problem.f problem.T
      (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) := by
  intro t _
  simpa [problem, hamiltonianOf, gradient_fun_const] using hasDerivAt_const t (0 : ℝ)

theorem reference_hamiltonianMinimizing :
    HamiltonianMinimizing problem.L problem.f problem.controlSet problem.T
      (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) := by
  intro t _ v _
  simp [problem, hamiltonianOf]

theorem reference_transversality :
    transversalityCondition problem.K problem.T (fun _ ↦ 0) (fun _ ↦ 0) := by
  exact terminal_gradient_zero.symm

/-- The reference satisfies admissibility and every existing PMP conclusion. -/
theorem reference_satisfies_pmp :
    IsAdmissiblePair problem 0 (fun _ ↦ 0) (fun _ ↦ 0) ∧
    costateEquation problem.L problem.f problem.T
      (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) ∧
    HamiltonianMinimizing problem.L problem.f problem.controlSet problem.T
      (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) ∧
    transversalityCondition problem.K problem.T (fun _ ↦ 0) (fun _ ↦ 0) :=
  ⟨reference_admissible, reference_costateEquation,
    reference_hamiltonianMinimizing, reference_transversality⟩

/-- An actual admissible competitor strictly improves the actual total cost. -/
theorem reference_not_optimal :
    ¬ IsOptimalPair problem 0 (fun _ ↦ 0) (fun _ ↦ 0) := by
  intro hopt
  have hle := ((isOptimalPair_iff problem 0 (fun _ ↦ 0) (fun _ ↦ 0)).mp hopt).2
    (fun t ↦ t) (fun _ ↦ 1) competitor_admissible
  rw [reference_cost, competitor_cost] at hle
  norm_num at hle

/-- Exact-project counterexample to the unrestricted PMP-to-optimality converse. -/
theorem pmp_does_not_imply_optimality :
    IsAdmissiblePair problem 0 (fun _ ↦ 0) (fun _ ↦ 0) ∧
    (∃ p : ℝ → ℝ,
      costateEquation problem.L problem.f problem.T (fun _ ↦ 0) (fun _ ↦ 0) p ∧
      HamiltonianMinimizing problem.L problem.f problem.controlSet problem.T
        (fun _ ↦ 0) (fun _ ↦ 0) p ∧
      transversalityCondition problem.K problem.T (fun _ ↦ 0) p) ∧
    ¬ IsOptimalPair problem 0 (fun _ ↦ 0) (fun _ ↦ 0) := by
  refine ⟨reference_admissible, ?_, reference_not_optimal⟩
  exact ⟨fun _ ↦ 0, reference_costateEquation,
    reference_hamiltonianMinimizing, reference_transversality⟩

end PMPExamples.NotSufficient
