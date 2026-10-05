import DynamicalSystems.Mathlib.Dynamics.Basic

/-! # Flows with a zero generator are the identity flow -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem flow_eq_id_of_generator_zero (Φ : Flow ℝ E)
    (hΦ : ∀ x, Differentiable ℝ (Φ · x))
    (hzero : ∀ x, deriv (Φ · x) 0 = 0) : Φ = Flow.id ℝ E := by
  apply flow_congr hΦ
  · intro x
    change Differentiable ℝ (fun _ : ℝ ↦ x)
    fun_prop
  · intro x
    change deriv (Φ · x) 0 = deriv (fun _ : ℝ ↦ x) 0
    simpa using hzero x
  · simpa only [hzero] using (LocallyLipschitz.const (0 : E) :
      LocallyLipschitz (fun _ : E ↦ (0 : E)))

#print axioms Flow.isIntegralCurve
#print axioms flow_congr
#print axioms flow_eq_id_of_generator_zero
