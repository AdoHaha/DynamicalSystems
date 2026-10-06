import DynamicalSystems.OptimalControl.ContinuousTime.FiniteSwitching

open Set OptimalControl

-- A genuinely controllable pair may have a completely ineffective input column.
example : LinearMap.IsControllable (0 : ℝ →ₗ[ℝ] ℝ) (LinearMap.snd ℝ ℝ ℝ) := by
  apply top_unique
  intro x _
  exact LinearMap.mem_reachableSubspace_of_mem_range ⟨(0, x), rfl⟩

example : ¬ CyclicInput (0 : ℝ →L[ℝ] ℝ) (0 : ℝ) := by
  intro h
  have hz : Submodule.span ℝ (range (fun k : Fin (Module.finrank ℝ ℝ) =>
      (((0 : ℝ →L[ℝ] ℝ).toLinearMap) ^ (k : ℕ)) (0 : ℝ))) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro x ⟨k, rfl⟩
    simp
  rw [h] at hz
  have : (1 : ℝ) ∈ (⊥ : Submodule ℝ ℝ) := hz Submodule.mem_top
  simp at this

example (T t : ℝ) :
    linearSwitchingFunction (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ) 0 T t = 0 := by
  simp [linearSwitchingFunction]

-- The one-dimensional nonzero channel is cyclic.
example : CyclicInput (0 : ℝ →L[ℝ] ℝ) (1 : ℝ) := by
  unfold CyclicInput
  apply top_unique
  intro x _
  have hone : (1 : ℝ) ∈ Submodule.span ℝ (range (fun k : Fin (Module.finrank ℝ ℝ) =>
      (((0 : ℝ →L[ℝ] ℝ).toLinearMap) ^ (k : ℕ)) (1 : ℝ))) := by
    apply Submodule.subset_span
    exact ⟨⟨0, by simp⟩, by simp⟩
  simpa using Submodule.smul_mem _ x hone

-- The standard double integrator: (position, velocity)' = (velocity, input).
noncomputable def doubleIntegrator : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.inl ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem doubleIntegrator_cyclic : CyclicInput doubleIntegrator (0, 1) := by
  unfold CyclicInput
  apply top_unique
  intro x _
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hb : (0, 1) ∈ Submodule.span ℝ (range (fun k : Fin (Module.finrank ℝ (ℝ × ℝ)) =>
      (doubleIntegrator.toLinearMap ^ (k : ℕ)) (0, 1))) := by
    apply Submodule.subset_span
    refine ⟨⟨0, by simp [hdim]⟩, ?_⟩
    simp
  have hAb : (1, 0) ∈ Submodule.span ℝ (range (fun k : Fin (Module.finrank ℝ (ℝ × ℝ)) =>
      (doubleIntegrator.toLinearMap ^ (k : ℕ)) (0, 1))) := by
    apply Submodule.subset_span
    refine ⟨⟨1, by simp [hdim]⟩, ?_⟩
    simp [doubleIntegrator]
  have hx := Submodule.add_mem _ (Submodule.smul_mem _ x.1 hAb)
    (Submodule.smul_mem _ x.2 hb)
  simpa using hx

example (q : (ℝ × ℝ) →L[ℝ] ℝ) (hq : q ≠ 0) (T a b : ℝ) :
    {t | t ∈ Icc a b ∧ linearSwitchingFunction doubleIntegrator q (0, 1) T t = 0}.Finite :=
  finite_zeroSet_linearSwitchingFunction _ q _ T a b doubleIntegrator_cyclic hq

#print axioms OptimalControl.hasDerivAt_terminalAdjointCovector
#print axioms OptimalControl.exists_ne_zero_linearSwitchingFunction
#print axioms OptimalControl.finite_all_switching_zeros
#print axioms OptimalControl.hasFiniteSwitchesOn_of_linear_box_minimizing
#print axioms OptimalControl.hasAEFiniteSwitchesOn_of_linear_box_minimizing
