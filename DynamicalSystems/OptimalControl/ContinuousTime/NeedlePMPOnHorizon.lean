import DynamicalSystems.OptimalControl.ContinuousTime.NeedlePMP
import DynamicalSystems.OptimalControl.ContinuousTime.ReferenceExtension

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

