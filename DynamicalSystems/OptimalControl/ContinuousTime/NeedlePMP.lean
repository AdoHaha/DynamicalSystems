import DynamicalSystems.OptimalControl.ContinuousTime.AdjointExistence
import DynamicalSystems.OptimalControl.ContinuousTime.NeedleFamily
import DynamicalSystems.OptimalControl.ContinuousTime.NeedleCostIdentity
import DynamicalSystems.OptimalControl.ContinuousTime.NeedleVariation
import DynamicalSystems.OptimalControl.ContinuousTime.ActualNeedleCostRemainder
import DynamicalSystems.OptimalControl.ContinuousTime.OptimalityGeometry
import DynamicalSystems.OptimalControl.ContinuousTime.ReferenceExtension

/-!
# Normal Pontryagin minimum principle from integral optimality

The regularity data below contains actual dynamics, derivatives and continuity
conditions. It contains no costate, feasible needle family, sensitivity, cost
variation, Hamiltonian inequality, or separation condition. Those objects and
conclusions are constructed in the proof.
-/


open Set Filter MeasureTheory
open scoped Topology Interval NNReal

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Primitive analytic assumptions for the first normal Bolza PMP theorem.
Optimality is over integral competitors, including genuine switched
trajectories. The global nominal reference is constructed by an extension. The
derivative continuity hypotheses are ambient continuity at reference-graph
points, not merely continuity of the derivative restricted to that graph. -/
structure SmoothNeedleData (prob : ContinuousOCP E U) (x : ℝ → E) (u : ℝ → U) where
  horizon_pos : 0 < prob.T
  nominal_lipschitz : ∃ K : ℝ≥0, ∃ B : ℝ,
    (∀ t, LipschitzWith K (fun y => prob.f t y (u t))) ∧
      ∀ t, ‖prob.f t 0 (u t)‖ ≤ B
  test_lipschitz : ∀ v ∈ prob.controlSet, ∃ K : ℝ≥0, ∃ B : ℝ,
    (∀ t, LipschitzWith K (fun y => prob.f t y v)) ∧
      ∀ t, ‖prob.f t 0 v‖ ≤ B
  nominal_dynamics_continuous : Continuous (fun q : ℝ × E => prob.f q.1 q.2 (u q.1))
  test_dynamics_continuous : ∀ v ∈ prob.controlSet,
    Continuous (fun q : ℝ × E => prob.f q.1 q.2 v)
  nominal_running_continuous : Continuous (fun q : ℝ × E => prob.L q.1 q.2 (u q.1))
  test_running_continuous : ∀ v ∈ prob.controlSet,
    Continuous (fun q : ℝ × E => prob.L q.1 q.2 v)
  /-- Actual spatial derivative of the nominal vector field. -/
  dynamicsDerivative : ℝ → E → E →L[ℝ] E
  has_dynamics_derivative : ∀ t ∈ Icc 0 prob.T, ∀ y,
    HasFDerivAt (fun z => prob.f t z (u t)) (dynamicsDerivative t y) y
  dynamics_derivative_continuous : ∀ t ∈ Icc 0 prob.T,
    ContinuousAt (fun q : ℝ × E => dynamicsDerivative q.1 q.2) (t, x t)
  /-- Actual spatial derivative of the nominal running cost. -/
  runningDerivative : ℝ → E → E →L[ℝ] ℝ
  has_running_derivative : ∀ t ∈ Icc 0 prob.T, ∀ y,
    HasFDerivAt (fun z => prob.L t z (u t)) (runningDerivative t y) y
  running_derivative_continuous : ∀ t ∈ Icc 0 prob.T,
    ContinuousAt (fun q : ℝ × E => runningDerivative q.1 q.2) (t, x t)
  terminal_differentiable : DifferentiableAt ℝ prob.K (x prob.T)

/-- Internal data after the actual integral reference has been extended by
the global nominal IVP. The outer theorem constructs this extension. -/
structure GlobalSmoothNeedleData (prob : ContinuousOCP E U) (x : ℝ → E) (u : ℝ → U)
    extends SmoothNeedleData prob x u where
  reference_equation : IsIntegralCurve x (fun t y => prob.f t y (u t))

namespace GlobalSmoothNeedleData

variable {prob : ContinuousOCP E U} {x : ℝ → E} {u : ℝ → U}

/-- Nominal dynamics derivative evaluated on the reference trajectory. -/
def stateCoefficient (r : GlobalSmoothNeedleData prob x u) (t : ℝ) : E →L[ℝ] E :=
  r.dynamicsDerivative t (x t)

/-- Nominal running-cost derivative evaluated on the reference trajectory. -/
def costCovector (r : GlobalSmoothNeedleData prob x u) (t : ℝ) : E →L[ℝ] ℝ :=
  r.runningDerivative t (x t)

/-- Riesz representative of the nominal running-cost derivative. -/
noncomputable def costGradient (r : GlobalSmoothNeedleData prob x u) (t : ℝ) : E :=
  (InnerProductSpace.toDual ℝ E).symm (r.costCovector t)

omit [CompleteSpace E] in
theorem stateCoefficient_continuousOn (r : GlobalSmoothNeedleData prob x u) :
    ContinuousOn r.stateCoefficient (Icc 0 prob.T) := by
  intro t ht
  have hg : ContinuousAt (fun s : ℝ => (s, x s)) t :=
    (continuous_id.prodMk r.reference_equation.continuous).continuousAt
  have hc : ContinuousAt (fun s => r.dynamicsDerivative s (x s)) t :=
    (r.dynamics_derivative_continuous t ht).comp (f := fun s : ℝ => (s, x s)) hg
  exact hc.continuousWithinAt

omit [CompleteSpace E] in
theorem costCovector_continuousOn (r : GlobalSmoothNeedleData prob x u) :
    ContinuousOn r.costCovector (Icc 0 prob.T) := by
  intro t ht
  have hg : ContinuousAt (fun s : ℝ => (s, x s)) t :=
    (continuous_id.prodMk r.reference_equation.continuous).continuousAt
  have hc : ContinuousAt (fun s => r.runningDerivative s (x s)) t :=
    (r.running_derivative_continuous t ht).comp (f := fun s : ℝ => (s, x s)) hg
  exact hc.continuousWithinAt

theorem costGradient_continuousOn (r : GlobalSmoothNeedleData prob x u) :
    ContinuousOn r.costGradient (Icc 0 prob.T) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
    r.costCovector_continuousOn

@[simp] theorem toDual_costGradient (r : GlobalSmoothNeedleData prob x u) (t : ℝ) :
    InnerProductSpace.toDual ℝ E (r.costGradient t) = r.costCovector t := by
  exact (InnerProductSpace.toDual ℝ E).apply_symm_apply _

theorem has_running_gradient (r : GlobalSmoothNeedleData prob x u)
    (t : ℝ) (ht : t ∈ Icc 0 prob.T) :
    HasGradientAt (fun y => prob.L t y (u t)) (r.costGradient t) (x t) := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  rw [r.toDual_costGradient]
  exact r.has_running_derivative t ht (x t)

/-- Construct the costate from actual nominal spatial derivatives. -/
theorem exists_costate (r : GlobalSmoothNeedleData prob x u) :
    ∃ p : ℝ → E, Continuous p ∧
      (∀ t ∈ Icc 0 prob.T,
        HasDerivAt p (-(r.stateCoefficient t).adjoint (p t) - r.costGradient t) t) ∧
      costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p := by
  exact exists_costate_of_spatial_derivatives
    prob x u r.stateCoefficient r.costGradient r.horizon_pos.le
    r.stateCoefficient_continuousOn r.costGradient_continuousOn
    (fun t ht => r.has_dynamics_derivative t ht (x t)) r.has_running_gradient

end GlobalSmoothNeedleData

omit [CompleteSpace E] in
/-- Continuity extends the needle inequality from positive times to the left
endpoint. A positive horizon is essential for this extension. -/
theorem hamiltonianMinimizing_of_positive_time_jumps
    (prob : ContinuousOCP E U) (x p : ℝ → E) (u : ℝ → U)
    (hT : 0 < prob.T)
    (hcont : ∀ v ∈ prob.controlSet, Continuous (fun t =>
      hamiltonianOf prob.L prob.f t (x t) v (p t) -
        hamiltonianOf prob.L prob.f t (x t) (u t) (p t)))
    (hpos : ∀ t, 0 < t → t ≤ prob.T → ∀ v ∈ prob.controlSet,
      0 ≤ hamiltonianOf prob.L prob.f t (x t) v (p t) -
        hamiltonianOf prob.L prob.f t (x t) (u t) (p t)) :
    HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u p := by
  intro t ht v hv
  apply sub_nonneg.mp
  rcases eq_or_lt_of_le ht.1 with heq | hgt
  · subst t
    apply ge_of_tendsto ((hcont v hv).continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun t => hamiltonianOf prob.L prob.f t (x t) v (p t) -
        hamiltonianOf prob.L prob.f t (x t) (u t) (p t))
        (𝓝[>] (0 : ℝ)) (𝓝 _))
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with s hs hsT
    exact hpos s hs hsT.le v hv
  · exact hpos t hgt ht.2 v hv

/-- The cost derivative is derived from the exact nonlinear cost identity.
The error limit here refers to the explicitly defined Taylor/control errors;
the final theorem discharges it using actual spatial derivatives. -/
theorem costSlope_of_constructedNeedles
    (prob : ContinuousOCP E U) (x_init : E) (x : ℝ → E) (u : ℝ → U)
    (r : GlobalSmoothNeedleData prob x u) (p : ℝ → E)
    (hpc : Continuous p)
    (hpd : ∀ t ∈ Icc 0 prob.T,
      HasDerivAt p (-(r.stateCoefficient t).adjoint (p t) - r.costGradient t) t)
    (hpT : transversalityCondition prob.K prob.T x p)
    (τ : ℝ) (hτ₀ : 0 < τ) (hτ : τ ≤ prob.T) (v : U) (hv : v ∈ prob.controlSet)
    (y : ℝ → ℝ → E) (Kv M C : ℝ)
    (hfamily : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      NeedleIntegralModel.ConstructedNeedle prob x_init x u τ v ε (y ε) Kv M C)
    (hR : Tendsto (fun ε : ℝ => ε⁻¹ * actualNeedleCostRemainder
      (fun t z => prob.f t z (u t)) (fun t z => prob.f t z v)
      (fun t z => prob.L t z (u t)) (fun t z => prob.L t z v) prob.K
      r.stateCoefficient r.costGradient (gradient prob.K (x prob.T))
      x (y ε) p prob.T τ ε) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ε⁻¹ *
      (continuousTotalCost prob (y ε) (needleControl u τ v ε) - continuousTotalCost prob x u))
      (𝓝[>] 0) (𝓝 (hamiltonianOf prob.L prob.f τ (x τ) v (p τ) -
        hamiltonianOf prob.L prob.f τ (x τ) (u τ) (p τ))) := by
  let j : ℝ → ℝ := fun t => prob.L t (x t) v - prob.L t (x t) (u t) +
    inner ℝ (p t) (prob.f t (x t) v - prob.f t (x t) (u t))
  have hxc := r.reference_equation.continuous
  have hj : Continuous j :=
    (((r.test_running_continuous v hv).comp (continuous_id.prodMk hxc)).sub
      (r.nominal_running_continuous.comp (continuous_id.prodMk hxc))).add
    (hpc.inner
      (((r.test_dynamics_continuous v hv).comp (continuous_id.prodMk hxc)).sub
        (r.nominal_dynamics_continuous.comp (continuous_id.prodMk hxc))))
  have hεshort : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < τ :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hτ₀)
  have hidentity : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      continuousTotalCost prob (y ε) (needleControl u τ v ε) - continuousTotalCost prob x u =
        (∫ t in (τ - ε)..τ, j t) + actualNeedleCostRemainder
          (fun t z => prob.f t z (u t)) (fun t z => prob.f t z v)
          (fun t z => prob.L t z (u t)) (fun t z => prob.L t z v) prob.K
          r.stateCoefficient r.costGradient (gradient prob.K (x prob.T))
          x (y ε) p prob.T τ ε := by
    filter_upwards [hfamily, hεshort, self_mem_nhdsWithin] with ε hf hετ hpos
    have hε : 0 < ε := hpos
    have hactual := cost_difference_eq_impulse_add_actualNeedleCostRemainder
      (fun t z => prob.f t z (u t)) (fun t z => prob.f t z v)
      (fun t z => prob.L t z (u t)) (fun t z => prob.L t z v) prob.K
      r.stateCoefficient r.costGradient (gradient prob.K (x prob.T))
      x (y ε) p prob.T τ ε hε.le (sub_nonneg.mpr hετ.le) hτ
      r.nominal_dynamics_continuous (r.test_dynamics_continuous v hv)
      r.nominal_running_continuous (r.test_running_continuous v hv)
      hxc hf.continuous hpc r.stateCoefficient_continuousOn r.costGradient_continuousOn
      (hf.before 0 (sub_nonneg.mpr hετ.le)) hpT
      (fun t _ => (r.reference_equation t).hasDerivWithinAt)
      (fun t _ => by
        simpa only [needleControl, apply_ite] using
          (hf.right_derivative t).mono Ioi_subset_Ici_self)
      (fun t ht => (hpd t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt)
    simpa only [continuousTotalCost, needleControl, apply_ite, j] using hactual
  have hsum := (tendsto_needleAverage j τ hj).add hR
  have hJ : Tendsto (fun ε : ℝ => ε⁻¹ *
      (continuousTotalCost prob (y ε) (needleControl u τ v ε) - continuousTotalCost prob x u))
      (𝓝[>] 0) (𝓝 (j τ)) := by
    apply (show Tendsto _ _ (𝓝 (j τ)) from (by simpa only [add_zero] using hsum)).congr'
    filter_upwards [hidentity] with ε hε
    rw [hε, mul_add]
  have hjτ : j τ = hamiltonianOf prob.L prob.f τ (x τ) v (p τ) -
      hamiltonianOf prob.L prob.f τ (x τ) (u τ) (p τ) := by
    simp only [j, hamiltonianOf, inner_sub_right]
    ring
  simpa only [hjτ] using hJ

/-- Normal PMP from actual integral optimality, with a global nominal reference.
Every feasible needle, its displacement estimate, the nonlinear cost expansion,
and the minimizing costate are constructed from primitive analytic data. -/
theorem needleCostate_of_globalIntegralOptimality
    (prob : ContinuousOCP E U) (x_init : E) (x : ℝ → E) (u : ℝ → U)
    (r : GlobalSmoothNeedleData prob x u)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x_init x u) :
    ∃ p : ℝ → E,
      costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p ∧
      HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u p := by
  obtain ⟨p, hpc, hpd, hcostate, hterminal⟩ := r.exists_costate
  obtain ⟨K₀, B₀, hLip₀, hB₀⟩ := r.nominal_lipschitz
  obtain ⟨P₀, hP₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) prob.T) hpc.continuousOn
  let P := max P₀ 0
  have hP : 0 ≤ P := le_max_right _ _
  have hpbound : ∀ t ∈ Icc 0 prob.T, ‖p t‖ ≤ P :=
    fun t ht => (hP₀ t ht).trans (le_max_left _ _)
  refine ⟨p, hcostate, hterminal, ?_⟩
  apply hamiltonianMinimizing_of_positive_time_jumps prob x p u r.horizon_pos
  · intro v hv
    have hxc := r.reference_equation.continuous
    exact
      (((r.test_running_continuous v hv).comp (continuous_id.prodMk hxc)).add
        (hpc.inner ((r.test_dynamics_continuous v hv).comp (continuous_id.prodMk hxc)))).sub
      ((r.nominal_running_continuous.comp (continuous_id.prodMk hxc)).add
        (hpc.inner (r.nominal_dynamics_continuous.comp (continuous_id.prodMk hxc))))
  · intro τ hτ₀ hτ v hv
    obtain ⟨Kv, Bv, hLipv, hBv⟩ := r.test_lipschitz v hv
    obtain ⟨M, hM, hforcing⟩ := NeedleIntegralModel.exists_frozen_forcing_bound
      prob x u v r.reference_equation.continuous
      r.nominal_dynamics_continuous (r.test_dynamics_continuous v hv)
    let C := 2 * M * Real.exp ((K₀ : ℝ) * prob.T)
    have hC : 0 ≤ C := by positivity
    obtain ⟨y, hfamily, _⟩ := NeedleIntegralModel.exists_feasible_needle_family
      prob x_init x u τ v hLip₀ hLipv hB₀ hBv
      r.nominal_dynamics_continuous (r.test_dynamics_continuous v hv)
      r.nominal_running_continuous (r.test_running_continuous v hv)
      r.reference_equation hopt.1.1 hopt.1.2.1 hv hτ₀ hτ hM hforcing
    have hybound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc 0 prob.T,
        ‖y ε t - x t‖ ≤ C * ε :=
      hfamily.mono (fun _ h => h.displacement_bound)
    have hK : HasFDerivAt prob.K
        (InnerProductSpace.toDual ℝ E (gradient prob.K (x prob.T))) (x prob.T) :=
      r.terminal_differentiable.hasGradientAt.hasFDerivAt
    have hRbase := tendsto_scaled_actualNeedleCostFamilyRemainder_of_continuous
      (F₀ := fun t z => prob.f t z (u t)) (Fv := fun t z => prob.f t z v)
      (L₀ := fun t z => prob.L t z (u t)) (Lv := fun t z => prob.L t z v)
      (DF := r.dynamicsDerivative) (DL := r.runningDerivative)
      (x := x) (y := y) (p := p)
      hτ₀ hτ hC hP r.reference_equation.continuous.continuousOn
      r.has_dynamics_derivative r.dynamics_derivative_continuous
      r.has_running_derivative r.running_derivative_continuous hK
      (fun _ _ => r.nominal_dynamics_continuous.continuousAt)
      (fun _ _ => (r.test_dynamics_continuous v hv).continuousAt)
      (fun _ _ => r.nominal_running_continuous.continuousAt)
      (fun _ _ => (r.test_running_continuous v hv).continuousAt)
      hpbound hybound
    have hR : Tendsto (fun ε : ℝ => ε⁻¹ * actualNeedleCostRemainder
        (fun t z => prob.f t z (u t)) (fun t z => prob.f t z v)
        (fun t z => prob.L t z (u t)) (fun t z => prob.L t z v) prob.K
        r.stateCoefficient r.costGradient (gradient prob.K (x prob.T))
        x (y ε) p prob.T τ ε) (𝓝[>] 0) (𝓝 0) := by
      simpa only [actualNeedleCostRemainder, actualNeedleCostFamilyRemainder,
        needleCostRemainder, r.toDual_costGradient,
        GlobalSmoothNeedleData.stateCoefficient, GlobalSmoothNeedleData.costCovector]
        using hRbase
    have hslope := costSlope_of_constructedNeedles prob x_init x u r p hpc hpd
      hterminal τ hτ₀ hτ v hv y Kv M C hfamily hR
    exact integralOptimal_costSlope_nonneg prob x_init x u hopt
      y (fun ε => needleControl u τ v ε) (hfamily.mono (fun _ h => h.admissible))
      _ hslope

/-- The normal Pontryagin minimum principle from actual integral optimality.

The supplied state need only satisfy the integral admissibility contained in
optimality. Its global nominal representative, all feasible needles, the state
estimates, the cost expansion and the single minimizing costate are constructed.
No derivative or regularity of the state outside the horizon is required.

The global hypotheses concern the nominal and fixed-control vector fields.
Running costs need joint continuity and genuine nominal spatial derivatives;
they are not required to be globally Lipschitz in the state. -/
theorem needleCostate_of_integralOptimality_smooth
    (prob : ContinuousOCP E U) (x_init : E) (x : ℝ → E) (u : ℝ → U)
    (r : SmoothNeedleData prob x u)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x_init x u) :
    ∃ p : ℝ → E,
      costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p ∧
      HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u p := by
  obtain ⟨K₀, B₀, hLip₀, hB₀⟩ := r.nominal_lipschitz
  obtain ⟨y, hy, heq, hyopt⟩ := NeedleIntegralModel.exists_global_optimal_reference_of_integral
    prob x_init x u r.horizon_pos.le hLip₀ hB₀ r.nominal_dynamics_continuous hopt
  let ry : GlobalSmoothNeedleData prob y u := {
    horizon_pos := r.horizon_pos
    nominal_lipschitz := r.nominal_lipschitz
    test_lipschitz := r.test_lipschitz
    nominal_dynamics_continuous := r.nominal_dynamics_continuous
    test_dynamics_continuous := r.test_dynamics_continuous
    nominal_running_continuous := r.nominal_running_continuous
    test_running_continuous := r.test_running_continuous
    dynamicsDerivative := r.dynamicsDerivative
    has_dynamics_derivative := r.has_dynamics_derivative
    dynamics_derivative_continuous := fun t ht => by
      simpa only [heq ht] using r.dynamics_derivative_continuous t ht
    runningDerivative := r.runningDerivative
    has_running_derivative := r.has_running_derivative
    running_derivative_continuous := fun t ht => by
      simpa only [heq ht] using r.running_derivative_continuous t ht
    terminal_differentiable := by
      simpa only [heq (right_mem_Icc.mpr r.horizon_pos.le)] using r.terminal_differentiable
    reference_equation := hy }
  obtain ⟨p, hcostate, hterminal, hminimum⟩ :=
    needleCostate_of_globalIntegralOptimality prob x_init y u ry hyopt
  exact ⟨p,
    (NeedleIntegralModel.costateEquation_congr_state prob u p heq).mp hcostate,
    (NeedleIntegralModel.transversalityCondition_congr_state
      prob p r.horizon_pos.le heq).mp hterminal,
    (NeedleIntegralModel.HamiltonianMinimizing_congr_state prob u p heq).mp hminimum⟩

