import DynamicalSystems.OptimalControl.ContinuousTime.ContinuousOCP
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Abel

/-!
# A candidate integral competitor class for needle variations

This is an explicit proposed model extension, not a redefinition of existing
optimality. Optimality among classical competitors does not imply optimality
among these competitors. The counterexample in this handoff demonstrates why.
All problem data and the total cost reuse ContinuousOCP unchanged.
-/

namespace NeedleIntegralModel

open Set MeasureTheory
open scoped Interval

variable {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Integral dynamics admit continuous trajectories with finitely many corners.
Integrability of both the vector field and running cost excludes junk integrals.
The control type need not carry measurable structure in this relational model. -/
def IsIntegralAdmissiblePair (prob : ContinuousOCP X U) (x₀ : X)
    (x : ℝ → X) (u : ℝ → U) : Prop :=
  x 0 = x₀ ∧
    (∀ t ∈ Icc 0 prob.T, u t ∈ prob.controlSet) ∧
    IntervalIntegrable (fun t => prob.f t (x t) (u t)) volume 0 prob.T ∧
    (∀ t ∈ Icc 0 prob.T,
      x t = x₀ + ∫ s in 0..t, prob.f s (x s) (u s)) ∧
    IntervalIntegrable (fun t => prob.L t (x t) (u t)) volume 0 prob.T

/-- Optimality over the enlarged integral competitor class. It is deliberately
not inferred from the original IsOptimalPair predicate. -/
def IsIntegralOptimalPair (prob : ContinuousOCP X U) (x₀ : X)
    (x : ℝ → X) (u : ℝ → U) : Prop :=
  IsIntegralAdmissiblePair prob x₀ x u ∧
    ∀ y v, IsIntegralAdmissiblePair prob x₀ y v →
      continuousTotalCost prob x u ≤ continuousTotalCost prob y v

/-- A classical trajectory with integrable dynamics satisfies the integral
relation, by the fundamental theorem of calculus. -/
theorem of_classical (prob : ContinuousOCP X U) (x₀ : X)
    (x : ℝ → X) (u : ℝ → U) (hT : 0 ≤ prob.T)
    (hadm : IsAdmissiblePair prob x₀ x u)
    (hfi : IntervalIntegrable (fun t => prob.f t (x t) (u t)) volume 0 prob.T) :
    IsIntegralAdmissiblePair prob x₀ x u := by
  refine ⟨hadm.1, hadm.2.1, hfi, ?_, hadm.2.2.2⟩
  intro t ht
  have hsub : uIcc 0 t ⊆ uIcc 0 prob.T := by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl ht.2
  have hder : ∀ s ∈ uIcc 0 t, HasDerivAt x (prob.f s (x s) (u s)) s := by
    intro s hs
    apply hadm.2.2.1 s
    simpa [uIcc_of_le hT] using hsub hs
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hfi.mono_set hsub)
  rw [hadm.1] at heq
  rw [heq]
  abel

/-- Right-derivative trajectories, including Ico step needles at switches, give
integral admissibility. Only interior right derivatives are needed by the FTC. -/
theorem of_right_derivative (prob : ContinuousOCP X U) (x₀ : X)
    (x : ℝ → X) (u : ℝ → U) (hT : 0 ≤ prob.T)
    (hx₀ : x 0 = x₀)
    (hu : ∀ t ∈ Icc 0 prob.T, u t ∈ prob.controlSet)
    (hx : ContinuousOn x (Icc 0 prob.T))
    (hd : ∀ t ∈ Ioo 0 prob.T,
      HasDerivWithinAt x (prob.f t (x t) (u t)) (Ioi t) t)
    (hfi : IntervalIntegrable (fun t => prob.f t (x t) (u t)) volume 0 prob.T)
    (hLi : IntervalIntegrable (fun t => prob.L t (x t) (u t)) volume 0 prob.T) :
    IsIntegralAdmissiblePair prob x₀ x u := by
  refine ⟨hx₀, hu, hfi, ?_, hLi⟩
  intro t ht
  have hsub : Icc 0 t ⊆ Icc 0 prob.T := Icc_subset_Icc le_rfl ht.2
  have hsubu : uIcc 0 t ⊆ uIcc 0 prob.T := by
    simpa [uIcc_of_le ht.1, uIcc_of_le hT] using hsub
  have heq := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    ht.1 (hx.mono hsub)
    (fun s hs => hd s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩) (hfi.mono_set hsubu)
  rw [hx₀] at heq
  rw [heq]
  abel

end NeedleIntegralModel
