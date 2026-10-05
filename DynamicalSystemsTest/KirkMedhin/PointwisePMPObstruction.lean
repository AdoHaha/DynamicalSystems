import DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple
import Mathlib.Tactic.NormNum

/-!
# An obstruction to an unrestricted pointwise PMP theorem

The existing admissibility predicate does not require continuous controls.
Changing the control at one isolated interior time can preserve the state
equation and cost while violating pointwise Hamiltonian minimization.  The
example has smooth data and the compact control set `[0,1]`.

This is not an obstruction to the usual almost-everywhere PMP, nor to a
pointwise theorem with suitable continuity/regular-time hypotheses.  It shows
why a theorem from the present `IsOptimalPair` to the existing all-times
`HamiltonianMinimizing` cannot hold without such extra hypotheses.
-/

namespace KirkMedhin.K1.PointwiseObstruction

open Set MeasureTheory Filter
open scoped Interval

/-- Zero dynamics and a quadratic control cost on the unit control interval. -/
def problem : ContinuousOCP ℝ ℝ where
  T := 1
  f := fun _ _ _ => 0
  L := fun _ _ u => u ^ 2
  K := fun _ => 0
  controlSet := Icc 0 1

/-- A control changed only at the single interior time one half. -/
noncomputable def isolatedControl (t : ℝ) : ℝ :=
  if t = (1 / 2 : ℝ) then 1 else 0

theorem runningCost_ae_zero :
    (fun t : ℝ => isolatedControl t ^ 2) =ᵐ[volume] (fun _ => 0) := by
  filter_upwards [volume.ae_ne (1 / 2 : ℝ)] with t ht
  simp only [isolatedControl, ite_eq_right ht, zero_pow (by decide : 2 ≠ 0)]

theorem isolatedControl_cost_zero :
    continuousTotalCost problem (fun _ => 0) isolatedControl = 0 := by
  change (∫ t in (0 : ℝ)..1, isolatedControl t ^ 2) + 0 = 0
  have hi : (∫ t in (0 : ℝ)..1, isolatedControl t ^ 2) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [runningCost_ae_zero] with t ht
    exact fun _ => ht
  simp [hi]

theorem isolatedControl_admissible :
    IsAdmissiblePair problem 0 (fun _ => 0) isolatedControl := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro t _ht
    change isolatedControl t ∈ Icc (0 : ℝ) 1
    unfold isolatedControl
    split_ifs <;> norm_num
  · intro t _ht
    exact hasDerivAt_const t 0
  · change IntervalIntegrable (fun t : ℝ => isolatedControl t ^ 2) volume 0 1
    exact intervalIntegrable_const.congr_ae (ae_restrict_of_ae runningCost_ae_zero.symm)

theorem isolatedControl_optimal :
    IsOptimalPair problem 0 (fun _ => 0) isolatedControl := by
  apply (isOptimalPair_iff problem 0 (fun _ => 0) isolatedControl).2
  refine ⟨isolatedControl_admissible, ?_⟩
  intro x u _hadmissible
  rw [isolatedControl_cost_zero]
  change 0 ≤ (∫ t in (0 : ℝ)..1, u t ^ 2) + 0
  exact add_nonneg
    (intervalIntegral.integral_nonneg zero_le_one (fun t _ht => sq_nonneg (u t)))
    le_rfl

/-- There is no costate at all making the all-times Hamiltonian condition hold. -/
theorem no_pointwise_hamiltonian_minimizing (p : ℝ → ℝ) :
    ¬ HamiltonianMinimizing problem.L problem.f problem.controlSet problem.T
      (fun _ => 0) isolatedControl p := by
  intro hmin
  have hbad := hmin (1 / 2) (by norm_num [problem]) 0 (by norm_num [problem])
  norm_num [hamiltonianOf, problem, isolatedControl] at hbad

/-- The original admissibility/optimality predicates alone do not imply the
original pointwise Hamiltonian-minimization predicate. -/
theorem optimal_without_pointwise_pmp :
    IsOptimalPair problem 0 (fun _ => 0) isolatedControl ∧
      ¬ ∃ p : ℝ → ℝ,
        HamiltonianMinimizing problem.L problem.f problem.controlSet problem.T
          (fun _ => 0) isolatedControl p := by
  refine ⟨isolatedControl_optimal, ?_⟩
  rintro ⟨p, hp⟩
  exact no_pointwise_hamiltonian_minimizing p hp

end KirkMedhin.K1.PointwiseObstruction
