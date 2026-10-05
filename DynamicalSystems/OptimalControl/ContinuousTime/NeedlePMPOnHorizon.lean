import DynamicalSystems.OptimalControl.ContinuousTime.NeedlePMP

/-!
# Normal PMP from analytic data on the finite horizon

Time clamping constructs all global extensions required by the existing IVP
theorems. The problem and every integral competitor keep exactly their original
meaning on the horizon. No extension, global bound at zero, or off-horizon
regularity is supplied by the caller.
-/


open Set MeasureTheory
open scoped Interval NNReal

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Project time onto the closed control horizon. -/
noncomputable def _root_.horizonTimeClamp (T : ℝ) (hT : 0 ≤ T) (t : ℝ) : ℝ := projIcc 0 T hT t

theorem _root_.horizonTimeClamp_mem (T : ℝ) (hT : 0 ≤ T) (t : ℝ) : _root_.horizonTimeClamp T hT t ∈ Icc 0 T :=
  (projIcc 0 T hT t).property

theorem _root_.horizonTimeClamp_eq {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) : _root_.horizonTimeClamp T hT t = t := by
  simp only [_root_.horizonTimeClamp, projIcc_of_mem hT ht]

theorem _root_.continuous_horizonTimeClamp (T : ℝ) (hT : 0 ≤ T) : Continuous (_root_.horizonTimeClamp T hT) :=
  continuous_subtype_val.comp continuous_projIcc

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem _root_.continuous_horizonTimeClamp_comp {G : Type*} [TopologicalSpace G]
    {F : ℝ → E → G} {T : ℝ} (hT : 0 ≤ T)
    (hF : ContinuousOn (fun q : ℝ × E => F q.1 q.2) (Icc 0 T ×ˢ univ)) :
    Continuous (fun q : ℝ × E => F (_root_.horizonTimeClamp T hT q.1) q.2) := by
  exact hF.comp_continuous
    (((_root_.continuous_horizonTimeClamp T hT).comp continuous_fst).prodMk continuous_snd)
    (fun q => ⟨_root_.horizonTimeClamp_mem T hT q.1, mem_univ q.2⟩)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem _root_.exists_norm_bound_at_zero_on_Icc {F : ℝ → E → E} {T : ℝ}
    (hF : ContinuousOn (fun q : ℝ × E => F q.1 q.2) (Icc 0 T ×ˢ univ)) :
    ∃ B : ℝ, ∀ t ∈ Icc 0 T, ‖F t 0‖ ≤ B := by
  have h0 : ContinuousOn (fun t => F t 0) (Icc 0 T) :=
    hF.comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨ht, mem_univ (0 : E)⟩)
  exact isCompact_Icc.exists_bound_of_continuousOn h0

/-- Extend the dynamics and running cost constantly beyond the horizon endpoints. -/
noncomputable def _root_.ContinuousOCP.clampTime (prob : ContinuousOCP E U) (hT : 0 ≤ prob.T) :
    ContinuousOCP E U where
  T := prob.T
  f := fun t y v => prob.f (_root_.horizonTimeClamp prob.T hT t) y v
  L := fun t y v => prob.L (_root_.horizonTimeClamp prob.T hT t) y v
  K := prob.K
  controlSet := prob.controlSet

/-- Extend the nominal control by its endpoint values outside the horizon. -/
noncomputable def _root_.horizonClampedControl (prob : ContinuousOCP E U) (hT : 0 ≤ prob.T)
    (u : ℝ → U) (t : ℝ) : U := u (_root_.horizonTimeClamp prob.T hT t)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem _root_.horizonClampedControl_eqOn (prob : ContinuousOCP E U) (hT : 0 ≤ prob.T) (u : ℝ → U) :
    EqOn (_root_.horizonClampedControl prob hT u) u (Icc 0 prob.T) := by
  intro t ht
  simp only [_root_.horizonClampedControl, _root_.horizonTimeClamp_eq hT ht]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem _root_.continuousTotalCost_clampTime (prob : ContinuousOCP E U) (hT : 0 ≤ prob.T)
    (x : ℝ → E) {u w : ℝ → U} (hwu : EqOn w u (Icc 0 prob.T)) :
    continuousTotalCost (_root_.ContinuousOCP.clampTime prob hT) x w = continuousTotalCost prob x u := by
  unfold continuousTotalCost
  change (∫ t in 0..prob.T, prob.L (_root_.horizonTimeClamp prob.T hT t) (x t) (w t)) + prob.K (x prob.T) = _
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  simp only [_root_.horizonTimeClamp_eq hT ht, hwu ht]

omit [CompleteSpace E] in
theorem _root_.NeedleIntegralModel.isIntegralAdmissiblePair_clampTime_iff (prob : ContinuousOCP E U) (hT : 0 ≤ prob.T)
    (x₀ : E) (x : ℝ → E) {u w : ℝ → U} (hwu : EqOn w u (Icc 0 prob.T)) :
    NeedleIntegralModel.IsIntegralAdmissiblePair (_root_.ContinuousOCP.clampTime prob hT) x₀ x w ↔
      NeedleIntegralModel.IsIntegralAdmissiblePair prob x₀ x u := by
  have hf : EqOn (fun t => prob.f (_root_.horizonTimeClamp prob.T hT t) (x t) (w t))
      (fun t => prob.f t (x t) (u t)) (Icc 0 prob.T) := by
    intro t ht
    simp only [_root_.horizonTimeClamp_eq hT ht, hwu ht]
  have hL : EqOn (fun t => prob.L (_root_.horizonTimeClamp prob.T hT t) (x t) (w t))
      (fun t => prob.L t (x t) (u t)) (Icc 0 prob.T) := by
    intro t ht
    simp only [_root_.horizonTimeClamp_eq hT ht, hwu ht]
  have hfi : IntervalIntegrable (fun t => prob.f (_root_.horizonTimeClamp prob.T hT t) (x t) (w t))
      volume 0 prob.T ↔ IntervalIntegrable (fun t => prob.f t (x t) (u t)) volume 0 prob.T := by
    apply intervalIntegrable_congr
    intro t ht
    rw [uIoc_of_le hT] at ht
    exact hf ⟨ht.1.le, ht.2⟩
  have hLi : IntervalIntegrable (fun t => prob.L (_root_.horizonTimeClamp prob.T hT t) (x t) (w t))
      volume 0 prob.T ↔ IntervalIntegrable (fun t => prob.L t (x t) (u t)) volume 0 prob.T := by
    apply intervalIntegrable_congr
    intro t ht
    rw [uIoc_of_le hT] at ht
    exact hL ⟨ht.1.le, ht.2⟩
  have hint (t : ℝ) (ht : t ∈ Icc 0 prob.T) :
      (∫ s in 0..t, prob.f (_root_.horizonTimeClamp prob.T hT s) (x s) (w s)) =
        ∫ s in 0..t, prob.f s (x s) (u s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact hf ⟨hs.1, hs.2.trans ht.2⟩
  constructor
  · rintro ⟨h0, hc, hif, heq, hiL⟩
    refine ⟨h0, ?_, hfi.mp hif, ?_, hLi.mp hiL⟩
    · intro t ht
      rw [← hwu ht]
      exact hc t ht
    · intro t ht
      simpa only [_root_.ContinuousOCP.clampTime, hint t ht] using heq t ht
  · rintro ⟨h0, hc, hif, heq, hiL⟩
    refine ⟨h0, ?_, hfi.mpr hif, ?_, hLi.mpr hiL⟩
    · intro t ht
      change w t ∈ prob.controlSet
      rw [hwu ht]
      exact hc t ht
    · intro t ht
      change x t = x₀ + ∫ s in 0..t, prob.f (_root_.horizonTimeClamp prob.T hT s) (x s) (w s)
      rw [hint t ht]
      exact heq t ht

omit [CompleteSpace E] in
theorem _root_.NeedleIntegralModel.isIntegralOptimalPair_clampTime (prob : ContinuousOCP E U) (hT : 0 ≤ prob.T)
    (x₀ : E) (x : ℝ → E) (u : ℝ → U)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x₀ x u) :
    NeedleIntegralModel.IsIntegralOptimalPair (_root_.ContinuousOCP.clampTime prob hT) x₀ x
      (_root_.horizonClampedControl prob hT u) := by
  have hu := _root_.horizonClampedControl_eqOn prob hT u
  refine ⟨(_root_.NeedleIntegralModel.isIntegralAdmissiblePair_clampTime_iff prob hT x₀ x hu).mpr hopt.1, ?_⟩
  intro y v hy
  rw [_root_.continuousTotalCost_clampTime prob hT x hu, _root_.continuousTotalCost_clampTime prob hT y (fun _ _ => rfl)]
  exact hopt.2 y v ((_root_.NeedleIntegralModel.isIntegralAdmissiblePair_clampTime_iff prob hT x₀ y (fun _ _ => rfl)).mp hy)

/-- Primitive finite-horizon regularity. Spatial Lipschitz constants are
uniform in time on the horizon and may depend on the fixed test control.
There are no global temporal assumptions or bound-at-zero hypotheses. -/
structure SmoothNeedleDataOnHorizon
    (prob : ContinuousOCP E U) (x : ℝ → E) (u : ℝ → U) where
  horizon_pos : 0 < prob.T
  nominal_lipschitz : ∃ K : ℝ≥0,
    ∀ t ∈ Icc 0 prob.T, LipschitzWith K (fun y => prob.f t y (u t))
  test_lipschitz : ∀ v ∈ prob.controlSet, ∃ K : ℝ≥0,
    ∀ t ∈ Icc 0 prob.T, LipschitzWith K (fun y => prob.f t y v)
  nominal_dynamics_continuous :
    ContinuousOn (fun q : ℝ × E => prob.f q.1 q.2 (u q.1)) (Icc 0 prob.T ×ˢ univ)
  test_dynamics_continuous : ∀ v ∈ prob.controlSet,
    ContinuousOn (fun q : ℝ × E => prob.f q.1 q.2 v) (Icc 0 prob.T ×ˢ univ)
  nominal_running_continuous :
    ContinuousOn (fun q : ℝ × E => prob.L q.1 q.2 (u q.1)) (Icc 0 prob.T ×ˢ univ)
  test_running_continuous : ∀ v ∈ prob.controlSet,
    ContinuousOn (fun q : ℝ × E => prob.L q.1 q.2 v) (Icc 0 prob.T ×ˢ univ)
  /-- The actual nominal spatial derivative of the dynamics. -/
  dynamicsDerivative : ℝ → E → E →L[ℝ] E
  has_dynamics_derivative : ∀ t ∈ Icc 0 prob.T, ∀ y,
    HasFDerivAt (fun z => prob.f t z (u t)) (dynamicsDerivative t y) y
  dynamics_derivative_continuous :
    ContinuousOn (fun q : ℝ × E => dynamicsDerivative q.1 q.2) (Icc 0 prob.T ×ˢ univ)
  /-- The actual nominal spatial derivative of the running cost. -/
  runningDerivative : ℝ → E → E →L[ℝ] ℝ
  has_running_derivative : ∀ t ∈ Icc 0 prob.T, ∀ y,
    HasFDerivAt (fun z => prob.L t z (u t)) (runningDerivative t y) y
  running_derivative_continuous :
    ContinuousOn (fun q : ℝ × E => runningDerivative q.1 q.2) (Icc 0 prob.T ×ˢ univ)
  terminal_differentiable : DifferentiableAt ℝ prob.K (x prob.T)

/-- Construct the global analytic data required by the IVP-based PMP theorem. -/
noncomputable def SmoothNeedleDataOnHorizon.clamped
    {prob : ContinuousOCP E U} {x : ℝ → E} {u : ℝ → U}
    (r : SmoothNeedleDataOnHorizon prob x u) :
    SmoothNeedleData (_root_.ContinuousOCP.clampTime prob r.horizon_pos.le) x
      (_root_.horizonClampedControl prob r.horizon_pos.le u) where
  horizon_pos := r.horizon_pos
  nominal_lipschitz := by
    obtain ⟨K, hK⟩ := r.nominal_lipschitz
    obtain ⟨B, hB⟩ := _root_.exists_norm_bound_at_zero_on_Icc (F := fun t y => prob.f t y (u t))
      r.nominal_dynamics_continuous
    exact ⟨K, B, fun t => hK _ (_root_.horizonTimeClamp_mem _ _ t), fun t => hB _ (_root_.horizonTimeClamp_mem _ _ t)⟩
  test_lipschitz := by
    intro v hv
    obtain ⟨K, hK⟩ := r.test_lipschitz v hv
    obtain ⟨B, hB⟩ := _root_.exists_norm_bound_at_zero_on_Icc (F := fun t y => prob.f t y v)
      (r.test_dynamics_continuous v hv)
    exact ⟨K, B, fun t => hK _ (_root_.horizonTimeClamp_mem _ _ t), fun t => hB _ (_root_.horizonTimeClamp_mem _ _ t)⟩
  nominal_dynamics_continuous :=
    _root_.continuous_horizonTimeClamp_comp (F := fun t y => prob.f t y (u t)) _ r.nominal_dynamics_continuous
  test_dynamics_continuous := fun v hv =>
    _root_.continuous_horizonTimeClamp_comp (F := fun t y => prob.f t y v) _ (r.test_dynamics_continuous v hv)
  nominal_running_continuous :=
    _root_.continuous_horizonTimeClamp_comp (F := fun t y => prob.L t y (u t)) _ r.nominal_running_continuous
  test_running_continuous := fun v hv =>
    _root_.continuous_horizonTimeClamp_comp (F := fun t y => prob.L t y v) _ (r.test_running_continuous v hv)
  dynamicsDerivative := fun t y => r.dynamicsDerivative (_root_.horizonTimeClamp prob.T r.horizon_pos.le t) y
  has_dynamics_derivative := fun t _ y =>
    r.has_dynamics_derivative _ (_root_.horizonTimeClamp_mem _ _ t) y
  dynamics_derivative_continuous := fun _ _ =>
    (_root_.continuous_horizonTimeClamp_comp _ r.dynamics_derivative_continuous).continuousAt
  runningDerivative := fun t y => r.runningDerivative (_root_.horizonTimeClamp prob.T r.horizon_pos.le t) y
  has_running_derivative := fun t _ y => r.has_running_derivative _ (_root_.horizonTimeClamp_mem _ _ t) y
  running_derivative_continuous := fun _ _ =>
    (_root_.continuous_horizonTimeClamp_comp _ r.running_derivative_continuous).continuousAt
  terminal_differentiable := r.terminal_differentiable

/-- Normal PMP on the original problem from primitive data confined to its
finite horizon. Clamping constructs the global problem/control extensions,
preserves the entire integral competitor class, and transfers all PMP clauses. -/
theorem needleCostate_of_integralOptimality_onHorizon
    (prob : ContinuousOCP E U) (x₀ : E) (x : ℝ → E) (u : ℝ → U)
    (r : SmoothNeedleDataOnHorizon prob x u)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x₀ x u) :
    ∃ p : ℝ → E,
      costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p ∧
      HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u p := by
  obtain ⟨p, hcostate, hterminal, hminimum⟩ :=
    needleCostate_of_integralOptimality_smooth
      (_root_.ContinuousOCP.clampTime prob r.horizon_pos.le) x₀ x
      (_root_.horizonClampedControl prob r.horizon_pos.le u) r.clamped
      (_root_.NeedleIntegralModel.isIntegralOptimalPair_clampTime prob r.horizon_pos.le x₀ x u hopt)
  refine ⟨p, ?_, hterminal, ?_⟩
  · intro t ht
    simpa only [_root_.ContinuousOCP.clampTime, _root_.horizonClampedControl, hamiltonianOf, _root_.horizonTimeClamp_eq r.horizon_pos.le ht]
      using hcostate t ht
  · intro t ht v hv
    simpa only [_root_.ContinuousOCP.clampTime, _root_.horizonClampedControl, hamiltonianOf, _root_.horizonTimeClamp_eq r.horizon_pos.le ht]
      using hminimum t ht v hv

