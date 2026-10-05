/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.Duhamel
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Duhamel regression examples

The first example refutes the former unnormalized statement. The constructive
examples exercise a Banach-valued forcing and a nonconstant, unbounded-in-time
operator coefficient, including times before the initial condition.
-/

@[expose] public noncomputable section

open IsFundamentalSolution

namespace DuhamelTests

/-- The zero family satisfies the bare derivative equation for `L = 0`, but
its Duhamel integral cannot solve `x' = 1`: diagonal normalization is essential. -/
theorem normalization_is_necessary :
    (∀ _s t : ℝ, deriv (fun _ : ℝ => (0 : ℝ →L[ℝ] ℝ)) t =
      (0 : ℝ →L[ℝ] ℝ).comp (0 : ℝ →L[ℝ] ℝ)) ∧
    deriv (duhamelOperator (fun _ _ => (0 : ℝ →L[ℝ] ℝ)) (fun _ => 1) 0 0) 0 ≠ 1 := by
  constructor
  · simp
  · have hzero : duhamelOperator (fun _ _ => (0 : ℝ →L[ℝ] ℝ)) (fun _ => 1) 0 0 =
        fun _ => (0 : ℝ) := by
      funext t
      simp [duhamelOperator]
    rw [hzero]
    norm_num

/-- Continuous Banach-valued forcing gives the usual primitive, without a
finite-dimensionality restriction or any ordering of `s` and `t`. -/
theorem continuous_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℝ → E} (hg : Continuous g) (s : ℝ) (x₀ : E) :
    IsIntegralCurve (fun t => x₀ + ∫ r in s..t, g r) (fun t _ => g t) := by
  have h := duhamelOperator_isIntegralCurve
    (L := fun _ => (0 : E →L[ℝ] E))
    (X := fun _ _ => ContinuousLinearMap.id ℝ E)
    continuous_const hg (fun _ => rfl)
    (fun _ t => by simpa using (hasDerivAt_const t (ContinuousLinearMap.id ℝ E))) s x₀
  have heq : duhamelOperator (fun _ _ => ContinuousLinearMap.id ℝ E) g s x₀ =
      fun t => x₀ + ∫ r in s..t, g r := by
    funext t
    simp [duhamelOperator]
  rw [heq] at h
  simpa using h

/-- Transition for `x' = t x`, whose coefficient is not uniformly bounded on
the real line. -/
def scalarTransition (s t : ℝ) : ℝ →L[ℝ] ℝ :=
  Real.exp ((t ^ 2 - s ^ 2) / 2) • ContinuousLinearMap.id ℝ ℝ

theorem scalarTransition_diag (s : ℝ) :
    scalarTransition s s = ContinuousLinearMap.id ℝ ℝ := by
  simp [scalarTransition]

theorem scalarTransition_forward (s t : ℝ) :
    HasDerivAt (scalarTransition s)
      ((t • ContinuousLinearMap.id ℝ ℝ).comp (scalarTransition s t)) t := by
  have harg : HasDerivAt (fun r : ℝ => (r ^ 2 - s ^ 2) / 2) t t := by
    have hp := (((hasDerivAt_id t).pow 2).sub_const (s ^ 2)).div_const 2
    change HasDerivAt (fun r : ℝ => (r ^ 2 - s ^ 2) / 2) ((2 * t ^ 1 * 1) / 2) t at hp
    convert hp using 1
    ring
  have hd := harg.exp.smul_const (ContinuousLinearMap.id ℝ ℝ)
  change HasDerivAt (fun r => Real.exp ((r ^ 2 - s ^ 2) / 2) • ContinuousLinearMap.id ℝ ℝ) _ t
  simpa [scalarTransition, smul_smul, mul_comm] using hd

/-- The constructor works with a genuinely nonautonomous linear coefficient. -/
theorem scalar_forced_fundamentalSolution :
    IsFundamentalSolution (duhamelOperator scalarTransition (fun _ => (1 : ℝ)))
      (fun t x => t * x + 1) := by
  simpa using duhamelOperator_isFundamentalSolution
    (L := fun t => t • ContinuousLinearMap.id ℝ ℝ)
    (by fun_prop) continuous_const scalarTransition_diag scalarTransition_forward

/-- A concrete check with final time preceding the initial time. -/
example : HasDerivAt (duhamelOperator scalarTransition (fun _ => (1 : ℝ)) 3 7)
    ((-2) * duhamelOperator scalarTransition (fun _ => (1 : ℝ)) 3 7 (-2) + 1) (-2) :=
  scalar_forced_fundamentalSolution.isIntegralCurve 3 7 (-2)

end DuhamelTests

#print axioms IsFundamentalSolution.linear_cocycle
#print axioms IsFundamentalSolution.isStateTransition
#print axioms IsStateTransition.hasDerivAt_duhamelOperator
#print axioms IsFundamentalSolution.duhamelOperator_isIntegralCurve
#print axioms IsFundamentalSolution.duhamelOperator_isFundamentalSolution
#print axioms DuhamelTests.normalization_is_necessary
#print axioms DuhamelTests.scalar_forced_fundamentalSolution
