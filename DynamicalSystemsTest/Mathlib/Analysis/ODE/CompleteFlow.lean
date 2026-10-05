import DynamicalSystems.Mathlib.Analysis.ODE.CompleteFlow
import Mathlib.Tactic.NormNum

/-!
# Regression: constructing the translation flow from supplied integral curves

This example identifies the choice-based flow constructor with an explicit
nonzero constant-velocity trajectory, including negative times. It exercises
the completeness input, uniqueness, joint continuity, and orbit derivative API.
-/

noncomputable section

namespace CompleteFlowRegression

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Constant vector fields are complete even without a complete state space. -/
theorem constant_complete (c : E) : IsCompleteVectorField (fun _ _ ↦ c) := by
  intro t₀ x₀
  refine ⟨fun t ↦ x₀ + (t - t₀) • c, by simp, ?_⟩
  intro t
  simpa using (((hasDerivAt_id t).sub_const t₀).smul_const c).const_add x₀

/-- The constructor recovers the explicit translation flow at every real time. -/
theorem constant_flow_apply (c x : E) (t : ℝ) :
    (constant_complete c).flow (LipschitzWith.const c).locallyLipschitz t x = x + t • c := by
  have hexplicit : IsIntegralCurve (fun s : ℝ ↦ x + s • c) (fun _ _ ↦ c) := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const c).const_add x
  have heq := ((constant_complete c).isIntegralCurve_flow
    (LipschitzWith.const c).locallyLipschitz x).eq_of_uniformlyLocallyLipschitz
    (t₀ := 0) (LipschitzWith.const c).locallyLipschitz.uniformlyLocallyLipschitz
    hexplicit (by simp)
  exact congrFun heq t

example : (constant_complete (3 : ℝ)).flow
    (LipschitzWith.const (3 : ℝ)).locallyLipschitz (-2) 5 = -1 := by
  rw [constant_flow_apply]
  norm_num

example (x : E) (c : E) :
    deriv ((constant_complete c).flow (LipschitzWith.const c).locallyLipschitz · x) 0 = c := by
  simp

end CompleteFlowRegression
