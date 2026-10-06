import DynamicalSystems.Mathlib.Analysis.ODE.MeasureAdjointBalance
import DynamicalSystems.OptimalControl.ContinuousTime.AffineStateMinimumPrinciple
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Tactic.NormNum

open Set MeasureTheory MeasureAdjoint
open scoped Topology

namespace MeasureAdjointBalanceTests

/-- A genuine scalar nonzero state coefficient. -/
noncomputable def coefficient : ℝ → ℝ →L[ℝ] ℝ := fun _ ↦ ContinuousLinearMap.id ℝ ℝ

/-- The actual transition of `x'=x`. -/
noncomputable def transition (s t : ℝ) : ℝ →L[ℝ] ℝ :=
  Real.exp (s - t) • ContinuousLinearMap.id ℝ ℝ

theorem transition_actual : IsStateTransition coefficient transition := by
  constructor
  · intro s
    simp [transition]
  · intro s t
    have h := (((hasDerivAt_id t).sub_const s).exp).smul_const
      (ContinuousLinearMap.id ℝ ℝ)
    simpa [coefficient, transition] using h
  · intro t s
    have h := (((hasDerivAt_const s t).sub (hasDerivAt_id s)).exp).smul_const
      (ContinuousLinearMap.id ℝ ℝ)
    simpa [coefficient, transition, neg_smul] using h
  · intro t r s
    apply ContinuousLinearMap.ext
    intro x
    simp only [transition, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring

noncomputable def atomMeasure : Measure ℝ := Measure.dirac (1 / 2) + Measure.dirac 1

instance : IsFiniteMeasure atomMeasure := by
  dsimp [atomMeasure]
  infer_instance

noncomputable def transformedNormal (s : ℝ) : ℝ →L[ℝ] ℝ :=
  Real.exp s • ContinuousLinearMap.id ℝ ℝ

noncomputable def terminalReference : ℝ →L[ℝ] ℝ :=
  -Real.exp 1 • ContinuousLinearMap.id ℝ ℝ

noncomputable def p : ℝ → ℝ →L[ℝ] ℝ :=
  propagatedCostate transition atomMeasure transformedNormal terminalReference

theorem normal_integrable : Integrable transformedNormal atomMeasure := by
  exact (integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))

/-- The constructed costate has the exact additive balance for the nonzero coefficient.
This is a foundation regression with explicit data, rather than an optimality theorem. -/
theorem actual_additive_balance {a b : ℝ} (hab : a ≤ b) :
    p b - p a = -(∫ t in a..b, (p t).comp (coefficient t)) -
      ∫ s in Ioc a b, (transformedNormal s).comp (transition 0 s) ∂atomMeasure := by
  exact propagated_increment normal_integrable terminalReference transition_actual
    continuous_const hab

theorem physical_normal (s : ℝ) : (transformedNormal s).comp (transition 0 s) =
    ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [transformedNormal, transition, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, zero_sub]
  rw [← mul_assoc, ← Real.exp_add]
  simp

/-- The full interval balance counts both atoms, each with its untransformed normal. -/
theorem both_atoms_additive_balance : p 1 - p 0 =
    -(∫ t in (0 : ℝ)..1, p t) - (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
  have h := actual_additive_balance (a := 0) (b := 1) (by norm_num)
  simpa only [physical_normal, coefficient, ContinuousLinearMap.comp_id, setIntegral_const,
    show atomMeasure.real (Ioc 0 1) = 2 by norm_num [Measure.real, atomMeasure]] using h

/-- Both atoms survive the propagated jump law; the nonzero coefficient changes the
smooth propagation but does not remove the atom. -/
theorem interior_jump : p (1 / 2) - Function.leftLim p (1 / 2) =
    -ContinuousLinearMap.id ℝ ℝ := by
  change propagatedCostate transition atomMeasure transformedNormal terminalReference (1 / 2) -
    Function.leftLim (propagatedCostate transition atomMeasure transformedNormal terminalReference)
      (1 / 2) = _
  rw [propagated_jump terminalReference transition_actual normal_integrable]
  have hm : atomMeasure.real {1 / 2} = 1 := by norm_num [Measure.real, atomMeasure]
  rw [hm, one_smul]
  apply ContinuousLinearMap.ext
  intro x
  simp only [transformedNormal, transition, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, neg_apply, smul_eq_mul]
  rw [← mul_assoc, ← Real.exp_add]
  norm_num

theorem terminal_jump : p 1 - Function.leftLim p 1 = -ContinuousLinearMap.id ℝ ℝ := by
  change propagatedCostate transition atomMeasure transformedNormal terminalReference 1 -
    Function.leftLim (propagatedCostate transition atomMeasure transformedNormal terminalReference)
      1 = _
  rw [propagated_jump terminalReference transition_actual normal_integrable]
  have hm : atomMeasure.real {1} = 1 := by norm_num [Measure.real, atomMeasure]
  rw [hm, one_smul]
  apply ContinuousLinearMap.ext
  intro x
  simp only [transformedNormal, transition, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, neg_apply, smul_eq_mul]
  rw [← mul_assoc, ← Real.exp_add]
  norm_num

theorem terminal_value : p 1 = -ContinuousLinearMap.id ℝ ℝ := by
  have hz : atomMeasure.restrict (Ioi 1) = 0 := by
    norm_num [atomMeasure, Measure.restrict_add, restrict_dirac]
  apply ContinuousLinearMap.ext
  intro x
  simp only [p, propagatedCostate, costate, openIntegralTail, hz, integral_zero_measure,
    add_zero, terminalReference, transition, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, neg_apply]
  simp only [zero_sub]
  rw [← mul_assoc, neg_mul, ← Real.exp_add]
  norm_num

/-- The terminal left trace differs from the actual terminal value because of the atom. -/
theorem terminal_left_trace : Function.leftLim p 1 = 0 := by
  have h := terminal_jump
  rw [terminal_value] at h
  exact sub_eq_self.mp h

/-- The singular costate is BV, derived from its construction. -/
theorem p_boundedVariation : BoundedVariationOn p (Icc 0 1) :=
  propagated_boundedVariation terminalReference transition_actual continuous_const
    normal_integrable 0 1

/-- An interior nonzero jump rules out absolute continuity on the horizon. -/
theorem p_not_absolutelyContinuous : ¬ AbsolutelyContinuousOnInterval p 0 1 := by
  intro h
  have hc : ContinuousAt p (1 / 2) := h.continuousOn.continuousAt (by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_mem_nhds (by norm_num) (by norm_num))
  have hl : Function.leftLim p (1 / 2) = p (1 / 2) :=
    leftLim_eq_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have hj := interior_jump
  rw [hl, sub_self] at hj
  have hx := congrArg (fun f : ℝ →L[ℝ] ℝ ↦ f 1) hj
  norm_num at hx

#print axioms MeasureAdjoint.propagated_increment
#print axioms MeasureAdjoint.propagated_normal_increment
#print axioms MeasureAdjoint.fullPropagatedCostate_increment
#print axioms MeasureAdjoint.indexed_propagated_increment
#print axioms actual_additive_balance
#print axioms interior_jump
#print axioms terminal_left_trace
#print axioms p_not_absolutelyContinuous

end MeasureAdjointBalanceTests

#print axioms OptimalControl.ConvexStateControlProblem.affineCostateReal_increment
#print axioms OptimalControl.ConvexStateControlProblem.affineCostateReal_jump
#print axioms OptimalControl.ConvexStateControlProblem.affineCostateReal_terminal_left_trace
#print axioms OptimalControl.ConvexStateControlProblem.affineCostateReal_boundedVariation
