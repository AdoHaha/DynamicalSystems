import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Classical admissibility with disconnected controls

This file specializes the project's classical, everywhere-differentiable
admissibility predicate to the smooth scalar problem

* horizon `1`, initial state `0`, dynamics `x' = u`;
* control set `{-1, 1}`;
* running cost `(t - 1/2) * u`, terminal cost `0`.

Darboux's theorem forces every admissible control to be constant on `[0,1]`.
Both constant controls have cost zero. The smooth reference `x(t)=t`, `u(t)=1`
is therefore globally optimal in this admissible class. Nevertheless there is
no normal PMP arc: the adjoint equation and terminal condition force `p=0`,
whereas Hamiltonian minimization fails at `t=3/4` against `u=-1`.

All analytic data are polynomials; the horizon is strictly positive and the
reference is smooth. The obstruction is closure under needle perturbations,
not differentiability of the problem data or a zero-duration edge case.
-/

namespace PMPExamples.ClassicalAdmissibility.ScalarModel

open Set MeasureTheory
open scoped Interval

/-- Classical admissibility for the scalar derivative-constrained regression. -/
def IsAdmissible (x u : ℝ → ℝ) : Prop :=
  x 0 = 0 ∧
    (∀ t ∈ Icc (0 : ℝ) 1, u t = -1 ∨ u t = 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (u t) t) ∧
    IntervalIntegrable (fun t => (t - 1 / 2) * u t) volume 0 1

/-- Actual integral running cost in the scalar regression problem. -/
noncomputable def totalCost (u : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (t - 1 / 2) * u t

/-- Minimum actual cost among all classically admissible scalar competitors. -/
def IsOptimal (x u : ℝ → ℝ) : Prop :=
  IsAdmissible x u ∧ ∀ y v, IsAdmissible y v → totalCost u ≤ totalCost v

/-- The classical derivative constraint rules out every genuine switch. -/
theorem admissible_control_constant {x u : ℝ → ℝ} (h : IsAdmissible x u) :
    (∀ t ∈ Icc (0 : ℝ) 1, u t = -1) ∨
      (∀ t ∈ Icc (0 : ℝ) 1, u t = 1) := by
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, u t ≠ 0 := by
    intro t ht
    rcases h.2.1 t ht with hm | hp
    · rw [hm]
      norm_num
    · rw [hp]
      norm_num
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne
      (f := x) (f' := u) (m := (0 : ℝ)) (convex_Icc (0 : ℝ) 1)
      (fun t ht => (h.2.2.1 t ht).hasDerivWithinAt) hne with hneg | hpos
  · left
    intro t ht
    rcases h.2.1 t ht with hm | hp
    · exact hm
    · have hn := hneg t ht
      rw [hp] at hn
      norm_num at hn
  · right
    intro t ht
    rcases h.2.1 t ht with hm | hp
    · have hn := hpos t ht
      rw [hm] at hn
      norm_num at hn
    · exact hp

theorem integral_centered_time :
    (∫ t in (0 : ℝ)..1, (t - 1 / 2)) = 0 := by
  have hsub : (∫ t in (0 : ℝ)..1, t - 1 / 2) =
      (∫ t in (0 : ℝ)..1, t) - (∫ _t in (0 : ℝ)..1, (1 / 2 : ℝ)) :=
    intervalIntegral.integral_sub (continuous_id.intervalIntegrable 0 1)
      intervalIntegrable_const
  rw [hsub]
  rw [integral_id, intervalIntegral.integral_const]
  norm_num

/-- Every classically admissible pair has exactly zero cost. -/
theorem admissible_cost_eq_zero {x u : ℝ → ℝ} (h : IsAdmissible x u) :
    totalCost u = 0 := by
  rcases admissible_control_constant h with hneg | hpos
  · unfold totalCost
    have heq : (∫ t in (0 : ℝ)..1, (t - 1 / 2) * u t) =
        ∫ t in (0 : ℝ)..1, -(t - 1 / 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
      change (t - 1 / 2) * u t = -(t - 1 / 2)
      rw [hneg t ht']
      ring
    rw [heq, intervalIntegral.integral_neg, integral_centered_time, neg_zero]
  · unfold totalCost
    have heq : (∫ t in (0 : ℝ)..1, (t - 1 / 2) * u t) =
        ∫ t in (0 : ℝ)..1, (t - 1 / 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
      change (t - 1 / 2) * u t = t - 1 / 2
      rw [hpos t ht', mul_one]
    rw [heq, integral_centered_time]

theorem reference_admissible : IsAdmissible (fun t => t) (fun _ => 1) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro t _
    exact Or.inr rfl
  · intro t _
    exact hasDerivAt_id t
  · exact (by fun_prop : Continuous (fun t : ℝ => (t - 1 / 2) * 1)).intervalIntegrable 0 1

theorem reference_optimal : IsOptimal (fun t => t) (fun _ => 1) := by
  refine ⟨reference_admissible, ?_⟩
  intro y v h
  rw [admissible_cost_eq_zero reference_admissible, admissible_cost_eq_zero h]

/-- The three scalar clauses here are exactly the specialized normal adjoint,
terminal condition, and Hamiltonian minimum clauses of the project predicates. -/
theorem reference_has_no_normal_pmp :
    ¬ ∃ p : ℝ → ℝ,
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt p 0 t) ∧
      p 1 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ v : ℝ, v = -1 ∨ v = 1 →
        (t - 1 / 2) * 1 + p t * 1 ≤ (t - 1 / 2) * v + p t * v) := by
  rintro ⟨p, hp, hterminal, hmin⟩
  have hFTC : (∫ _t in (3 / 4 : ℝ)..1, (0 : ℝ)) = p 1 - p (3 / 4) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      have ht' : t ∈ Icc (3 / 4 : ℝ) 1 := by
        simpa only [Set.uIcc_of_le (by norm_num : (3 / 4 : ℝ) ≤ 1)] using ht
      exact hp t ⟨by linarith [ht'.1], ht'.2⟩
    · exact intervalIntegrable_const
  have hpq : p (3 / 4) = 0 := by
    simp only [intervalIntegral.integral_zero, hterminal, zero_sub] at hFTC
    linarith
  have hbad := hmin (3 / 4) (by norm_num) (-1) (Or.inl rfl)
  norm_num [hpq] at hbad

end PMPExamples.ClassicalAdmissibility.ScalarModel
