import DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple
import DynamicalSystemsTest.OptimalControl.ContinuousTime.MinimumPrinciple.ClassicalAdmissibility
/-!
# The same obstruction against the exact project predicates

The imported scalar proof is connected here to `ContinuousOCP`, `IsOptimalPair`,
`costateEquation`, `HamiltonianMinimizing`, and `transversalityCondition` without
changing any of those definitions.
-/

namespace PMPExamples.ClassicalAdmissibility.ContinuousOCPAdapter

open Set
open scoped ContDiff

/-- Smooth scalar problem with a disconnected control set and no admissible switches. -/
noncomputable def problem : ContinuousOCP ℝ ℝ where
  T := 1
  f := fun _ _ u => u
  L := fun t _ u => (t - 1 / 2) * u
  K := fun _ => 0
  controlSet := {-1, 1}

theorem horizon_pos : 0 < problem.T := by norm_num [problem]

theorem problem_data_smooth :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ × ℝ => problem.f z.1 z.2.1 z.2.2) ∧
    ContDiff ℝ ∞ (fun z : ℝ × ℝ × ℝ => problem.L z.1 z.2.1 z.2.2) ∧
    ContDiff ℝ ∞ problem.K := by
  dsimp [problem]
  exact ⟨by fun_prop, by fun_prop, by fun_prop⟩

theorem reference_smooth :
    ContDiff ℝ ∞ (fun t : ℝ => t) ∧ ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)) := by
  exact ⟨by fun_prop, by fun_prop⟩

theorem admissible_iff (x u : ℝ → ℝ) :
    IsAdmissiblePair problem 0 x u ↔ PMPExamples.ClassicalAdmissibility.ScalarModel.IsAdmissible x u := by
  simp only [IsAdmissiblePair, problem, PMPExamples.ClassicalAdmissibility.ScalarModel.IsAdmissible,
    Set.mem_insert_iff, Set.mem_singleton_iff]

theorem totalCost_eq (x u : ℝ → ℝ) :
    continuousTotalCost problem x u = PMPExamples.ClassicalAdmissibility.ScalarModel.totalCost u := by
  simp [continuousTotalCost, problem, PMPExamples.ClassicalAdmissibility.ScalarModel.totalCost]

/-- A smooth reference is optimal in the project's actual admissible class. -/
theorem reference_isOptimalPair :
    IsOptimalPair problem 0 (fun t => t) (fun _ => 1) := by
  apply (isOptimalPair_iff problem 0 (fun t => t) (fun _ => 1)).mpr
  refine ⟨(admissible_iff _ _).mpr PMPExamples.ClassicalAdmissibility.ScalarModel.reference_admissible, ?_⟩
  intro y v h
  rw [totalCost_eq, totalCost_eq]
  exact PMPExamples.ClassicalAdmissibility.ScalarModel.reference_optimal.2 y v ((admissible_iff y v).mp h)

/-- The target PMP conclusion fails for that reference using exactly the existing
adjoint, Hamiltonian minimum, and terminal predicates. -/
theorem reference_no_costate :
    ¬ ∃ p : ℝ → ℝ,
      costateEquation problem.L problem.f problem.T (fun t => t) (fun _ => 1) p ∧
      HamiltonianMinimizing problem.L problem.f problem.controlSet problem.T
        (fun t => t) (fun _ => 1) p ∧
      transversalityCondition problem.K problem.T (fun t => t) p := by
  rintro ⟨p, hp, hmin, hterminal⟩
  apply PMPExamples.ClassicalAdmissibility.ScalarModel.reference_has_no_normal_pmp
  refine ⟨p, ?_, ?_, ?_⟩
  · intro t ht
    have h := hp t ht
    simpa [problem, hamiltonianOf, gradient_fun_const] using h
  · simpa [transversalityCondition, problem, gradient_fun_const] using hterminal
  · intro t ht v hv
    have h := hmin t ht v (by simpa [problem] using hv)
    simpa [problem, hamiltonianOf, Real.inner_apply, mul_comm] using h

/-- An exact, kernel-checkable regression for the originally requested implication. -/
theorem optimality_does_not_imply_pmp :
    IsOptimalPair problem 0 (fun t => t) (fun _ => 1) ∧
    ¬ ∃ p : ℝ → ℝ,
      costateEquation problem.L problem.f problem.T (fun t => t) (fun _ => 1) p ∧
      HamiltonianMinimizing problem.L problem.f problem.controlSet problem.T
        (fun t => t) (fun _ => 1) p ∧
      transversalityCondition problem.K problem.T (fun t => t) p :=
  ⟨reference_isOptimalPair, reference_no_costate⟩

end PMPExamples.ClassicalAdmissibility.ContinuousOCPAdapter
