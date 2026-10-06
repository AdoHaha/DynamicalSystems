import DynamicalSystems.OptimalControl.ContinuousTime.PathConstraintMultipliers

open Set MeasureTheory OptimalControl

namespace PathConstraintTest

abbrev Time := Icc (0 : ℝ) 1

noncomputable def constraintCurve (v : ℝ) : C(Time, ℝ) :=
  ⟨fun t => v - ((t : ℝ) - 1 / 2) ^ 2, by fun_prop⟩

theorem objective_convex : ConvexOn ℝ (univ : Set ℝ) (fun v => -v) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b _ _ _
  change -(a * x + b * y) ≤ a * (-x) + b * (-y)
  ring_nf
  rfl

theorem constraint_convex (t : Time) :
    ConvexOn ℝ (univ : Set ℝ) (fun v => constraintCurve v t) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b _ _ hab
  change a * x + b * y - ((t : ℝ) - 1 / 2) ^ 2 ≤
    a * (x - ((t : ℝ) - 1 / 2) ^ 2) + b * (y - ((t : ℝ) - 1 / 2) ^ 2)
  have he : a * ((t : ℝ) - 1 / 2) ^ 2 + b * ((t : ℝ) - 1 / 2) ^ 2 =
      ((t : ℝ) - 1 / 2) ^ 2 := by rw [← add_mul, hab, one_mul]
  linarith

-- An infinite family of constraints has only one active index, strictly inside
-- the interval. Necessity forces a nonzero measure concentrated there; a zero
-- measure or a mere Lebesgue density cannot replace the measure multiplier.
theorem exists_interior_atom_multiplier :
    ∃ (μ : Measure Time) (α : ℝ), IsFiniteMeasure μ ∧ 0 < α ∧ μ ≠ 0 ∧
      μ {t | (t : ℝ) ≠ 1 / 2} = 0 := by
  have hGu : constraintCurve 0 ≤ 0 := by
    intro t
    change 0 - ((t : ℝ) - 1 / 2) ^ 2 ≤ 0
    nlinarith [sq_nonneg ((t : ℝ) - 1 / 2)]
  have hopt : ∀ v ∈ (univ : Set ℝ), constraintCurve v ≤ 0 → -(0 : ℝ) ≤ -v := by
    intro v _ hv
    have h := hv ⟨1 / 2, by norm_num⟩
    change v - (1 / 2 - 1 / 2) ^ 2 ≤ 0 at h
    norm_num at h ⊢
    exact h
  obtain ⟨μ, α, hμ, hα, hne, hcomp, hnull, hmin⟩ := exists_path_measure_multipliers
    univ constraintCurve (fun v => -v) objective_convex constraint_convex 0 (mem_univ _) hGu hopt
  let := hμ
  have hap : 0 < α := path_costMultiplier_pos_of_slater univ constraintCurve (fun v => -v)
    0 μ α hα hne hmin ⟨-1, mem_univ _, by
      intro t
      change -1 - ((t : ℝ) - 1 / 2) ^ 2 < 0
      nlinarith [sq_nonneg ((t : ℝ) - 1 / 2)]⟩
  have hμne : μ ≠ 0 := by
    intro hz
    have h := hmin 1 (mem_univ _)
    simp [hz] at h
    linarith
  refine ⟨μ, α, hμ, hap, hμne, ?_⟩
  have hs : {t : Time | (t : ℝ) ≠ 1 / 2} = {t | constraintCurve 0 t < 0} := by
    ext t
    change (t : ℝ) ≠ 1 / 2 ↔ 0 - ((t : ℝ) - 1 / 2) ^ 2 < 0
    simp only [zero_sub, neg_lt_zero, sq_pos_iff, sub_ne_zero]
  rw [hs]
  exact hnull

#print axioms ContinuousLinearMap.integral_positiveRepresentingMeasure
#print axioms OptimalControl.exists_path_measure_multipliers
#print axioms OptimalControl.path_costMultiplier_pos_of_slater
#print axioms exists_interior_atom_multiplier

end PathConstraintTest
