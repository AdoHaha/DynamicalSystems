/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module
public import DynamicalSystems.OptimalControl.ContinuousTime.StateConstraintMultipliers
public import DynamicalSystems.Mathlib.Analysis.ODE.MeasureAdjoint
public import DynamicalSystems.OptimalControl.ContinuousTime.MeasurableHamiltonian
/-! # Integral Hamiltonian assembly for state-constrained integrators -/
@[expose] public section
open Set MeasureTheory Filter
open scoped Topology
namespace OptimalControl.ConvexStateControlProblem
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (P : OptimalControl.ConvexStateControlProblem E E 1)
omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The actual integrator trajectory is the constructed integral control path. -/
theorem integrator_trajectory_eq (hf : ∀ t x u, P.dynamics t x u = u)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z) (t : P.Time) :
    z.1 t = integralControlPath P.horizon_pos P.initial z.2 t := by
  simpa only [hf, integralControlPath] using hz.2.2 t

/-- The Bolza cost for a linear terminal cost and a state-independent running cost. -/
theorem integrator_cost_eq (hf : ∀ t x u, P.dynamics t x u = u)
    (lambda : E →L[ℝ] ℝ) (hterm : P.terminalCost = lambda)
    (hL : ∀ t x u, P.runningCost t x u = P.runningCost t P.initial u)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z) :
    P.cost z = lambda P.initial + P.horizon *
      ∫ t, P.runningCost t P.initial (z.2 t) + lambda (z.2 t)
        ∂horizonProbability P.horizon P.horizon_pos := by
  have hu := P.integrable_control z.2 hz.1 hz.2.1
  have hli := P.integrable_composition z hz P.runningCost P.runningCost_continuous
  simp_rw [hL] at hli
  unfold cost
  rw [hterm, P.integrator_trajectory_eq hf z hz,
    integralControlPath_terminal P.horizon_pos P.initial z.2 hu]
  simp_rw [hL]
  rw [map_add, map_smul, ← lambda.integral_comp_comm hu, integral_add hli
    (lambda.integrable_comp hu)]
  simp only [smul_eq_mul]
  ring
omit [SecondCountableTopology E] in
/-- Affine state-constraint integrals turn into the actual measure-tail pairing. -/
theorem integrator_constraint_integral_eq (hf : ∀ t x u, P.dynamics t x u = u)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z)
    (μ : Measure P.Time) [IsFiniteMeasure μ]
    (w : P.Time → E →L[ℝ] ℝ) (hw : Continuous w)
    (c : P.Time → ℝ) (hc : Continuous c) :
    (∫ s, w s (z.1 s) + c s ∂μ) = (∫ s, w s P.initial + c s ∂μ) +
      P.horizon * ∫ t, (∫ s in Ioi t, w s ∂μ) (z.2 t)
        ∂horizonProbability P.horizon P.horizon_pos := by
  have hu := P.integrable_control z.2 hz.1 hz.2.1
  have hwi : Integrable w μ :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hci : Integrable (fun s ↦ w s P.initial + c s) μ :=
    ((hw.clm_apply continuous_const).add hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpi := MeasureAdjoint.integrable_order_prefix_apply hwi hu
  have he (s : P.Time) : w s (z.1 s) + c s =
      w s P.initial + c s + P.horizon * w s
        (∫ t in Iio s, z.2 t ∂horizonProbability P.horizon P.horizon_pos) := by
    rw [P.integrator_trajectory_eq hf z hz,
      integralControlPath_prefix P.horizon_pos P.initial z.2 hu]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  simp_rw [he]
  rw [integral_add hci (hpi.const_mul P.horizon), integral_const_mul,
    MeasureAdjoint.integral_order_tail_pairing hwi hu]

/-- Hamiltonian with the costate constructed from the actual constraint measure. -/
noncomputable def integratorHamiltonian (α : ℝ) (μ : Measure P.Time)
    (lambda : E →L[ℝ] ℝ) (w : P.Time → E →L[ℝ] ℝ) (t : P.Time) (u : E) : ℝ :=
  α * P.runningCost t P.initial u +
    (α • lambda + ∫ s in Ioi t, w s ∂μ) u

/-- Exact augmented-cost identity: no derivative or variational certificate is supplied. -/
theorem integrator_augmented_cost_eq (hf : ∀ t x u, P.dynamics t x u = u)
    (lambda : E →L[ℝ] ℝ) (hterm : P.terminalCost = lambda)
    (hL : ∀ t x u, P.runningCost t x u = P.runningCost t P.initial u)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z) (α : ℝ)
    (μ : Measure P.Time) [IsFiniteMeasure μ]
    (w : P.Time → E →L[ℝ] ℝ) (hw : Continuous w)
    (c : P.Time → ℝ) (hc : Continuous c) :
    α * P.cost z + (∫ s, w s (z.1 s) + c s ∂μ) =
      α * lambda P.initial + (∫ s, w s P.initial + c s ∂μ) +
        P.horizon * ∫ t, P.integratorHamiltonian α μ lambda w t (z.2 t)
          ∂horizonProbability P.horizon P.horizon_pos := by
  have hu := P.integrable_control z.2 hz.1 hz.2.1
  have hli := P.integrable_composition z hz P.runningCost P.runningCost_continuous
  simp_rw [hL] at hli
  have hwi : Integrable w μ :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hti := MeasureAdjoint.integrable_order_tail_apply hwi hu
  have hqi := lambda.integrable_comp hu
  rw [P.integrator_cost_eq hf lambda hterm hL z hz,
    P.integrator_constraint_integral_eq hf z hz μ w hw c hc]
  simp only [integratorHamiltonian, add_apply,
    smul_apply, smul_eq_mul]
  have ha := integral_add (hli.const_mul α) ((hqi.const_mul α).add hti)
  have hb := integral_add (hqi.const_mul α) hti
  simp only [Pi.add_apply] at ha hb
  rw [ha, hb, integral_const_mul, integral_const_mul, integral_add hli hqi]
  ring

/-- Restrict the single affine state constraint to the actual compact time type. -/
def singleResidual (z : P.Candidate) : C(P.Time, ℝ) :=
  (P.residual z).comp ⟨fun t ↦ (t, 0), continuous_id.prodMk continuous_const⟩

omit [CompleteSpace E] in
/-- For one state constraint the necessity measure lives directly on time. -/
theorem exists_time_measure_of_isMinimum (z : P.Candidate) (hz : P.IsMinimum z) :
    ∃ (α : ℝ) (μ : Measure P.Time), IsFiniteMeasure μ ∧ 0 ≤ α ∧
      (α ≠ 0 ∨ μ ≠ 0) ∧ (∫ t, P.singleResidual z t ∂μ) = 0 ∧
      μ {t | P.singleResidual z t ≠ 0} = 0 ∧
      ∀ y, P.DynamicsAdmissible y →
        α * P.cost z ≤ α * P.cost y + ∫ t, P.singleResidual y t ∂μ := by
  apply ConvexProgramming.exists_continuousInequality_measure P.convex_dynamicsAdmissible
    P.cost P.singleResidual z P.convexOn_cost
    (fun t ↦ P.convexOn_residual (t, 0)) hz.1
    (fun t ↦ hz.2.1 (t, 0))
  intro y hy hg
  apply hz.2.2 y hy
  intro q
  rcases q with ⟨t, i⟩
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact hg t

omit [CompleteSpace E] in
/-- The constructed Hamiltonian is integrable along every actual admissible control. -/
theorem integrable_integratorHamiltonian (z : P.Candidate) (hz : P.DynamicsAdmissible z)
    (hL : ∀ t x u, P.runningCost t x u = P.runningCost t P.initial u)
    (α : ℝ) (μ : Measure P.Time) [IsFiniteMeasure μ]
    (lambda : E →L[ℝ] ℝ) (w : P.Time → E →L[ℝ] ℝ) (hw : Continuous w) :
    Integrable (fun t ↦ P.integratorHamiltonian α μ lambda w t (z.2 t))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hu := P.integrable_control z.2 hz.1 hz.2.1
  have hli := P.integrable_composition z hz P.runningCost P.runningCost_continuous
  simp_rw [hL] at hli
  have hwi : Integrable w μ :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hti := MeasureAdjoint.integrable_order_tail_apply hwi hu
  apply ((hli.const_mul α).add (((lambda.integrable_comp hu).const_mul α).add hti)).congr
  exact Eventually.of_forall (fun _ ↦ by simp [integratorHamiltonian])

/-- Actual constrained optimality constructs state measures and yields one common
AE Hamiltonian minimum for integrator dynamics and affine state constraints. -/
theorem exists_integrator_state_minimum_principle
    (hf : ∀ t x u, P.dynamics t x u = u)
    (lambda : E →L[ℝ] ℝ) (hterm : P.terminalCost = lambda)
    (hL : ∀ t x u, P.runningCost t x u = P.runningCost t P.initial u)
    (w : P.Time → E →L[ℝ] ℝ) (hw : Continuous w)
    (c : P.Time → ℝ) (hc : Continuous c)
    (hg : ∀ t x, P.constraint (t, 0) x = w t x + c t)
    (z : P.Candidate) (hz : P.IsMinimum z) :
    ∃ (α : ℝ) (μ : Measure P.Time), IsFiniteMeasure μ ∧ 0 ≤ α ∧
      (α ≠ 0 ∨ μ ≠ 0) ∧ (∫ t, P.singleResidual z t ∂μ) = 0 ∧
      μ {t | P.singleResidual z t ≠ 0} = 0 ∧
      ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v ∈ P.controlSet,
        P.integratorHamiltonian α μ lambda w t (z.2 t) ≤
          P.integratorHamiltonian α μ lambda w t v := by
  obtain ⟨α, μ, hfin, hα, hne, hcomp, hsupport, hmin⟩ :=
    P.exists_time_measure_of_isMinimum z hz
  let : IsFiniteMeasure μ := hfin
  let u : P.Time → P.controlSet := fun t ↦ ⟨z.2 t, hz.1.2.1 t⟩
  let H : P.Time → P.controlSet → ℝ := fun t v ↦ P.integratorHamiltonian α μ lambda w t v
  have hu : Measurable u := hz.1.1.subtype_mk
  have hi : Integrable (fun t ↦ H t (u t))
      (horizonProbability P.horizon P.horizon_pos).toMeasure :=
    P.integrable_integratorHamiltonian z hz.1 hL α μ lambda w hw
  have hcompare : ∀ v : P.Time → P.controlSet, Measurable v →
      (∫ t, H t (u t) ∂horizonProbability P.horizon P.horizon_pos) ≤
        ∫ t, H t (v t) ∂horizonProbability P.horizon P.horizon_pos := by
    intro v hv
    obtain ⟨y, hy, hyu, hyx⟩ := P.exists_integrator_candidate hf
      (fun t ↦ (v t : E)) (measurable_subtype_coe.comp hv) (fun t ↦ (v t).2)
    have hm := hmin y hy
    have he (a : P.Candidate) : (∫ t, P.singleResidual a t ∂μ) =
        ∫ t, w t (a.1 t) + c t ∂μ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      exact hg t (a.1 t)
    have hzid := P.integrator_augmented_cost_eq hf lambda hterm hL z hz.1 α μ w hw c hc
    have hyid := P.integrator_augmented_cost_eq hf lambda hterm hL y hy α μ w hw c hc
    rw [he] at hcomp hm
    have hint : P.horizon * (∫ t, H t (u t) ∂horizonProbability P.horizon P.horizon_pos) ≤
        P.horizon * ∫ t, H t (v t) ∂horizonProbability P.horizon P.horizon_pos := by
      change P.horizon * (∫ t, P.integratorHamiltonian α μ lambda w t (z.2 t)
        ∂horizonProbability P.horizon P.horizon_pos) ≤ _
      simp only [hyu] at hyid
      change P.horizon * (∫ t, P.integratorHamiltonian α μ lambda w t (z.2 t)
        ∂horizonProbability P.horizon P.horizon_pos) ≤
          P.horizon * ∫ t, P.integratorHamiltonian α μ lambda w t (v t)
            ∂horizonProbability P.horizon P.horizon_pos
      linarith
    nlinarith [P.horizon_pos]
  have hconst (v : P.controlSet) : Integrable (fun t ↦ H t v)
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
    obtain ⟨y, hy, hyu, _⟩ := P.exists_integrator_candidate hf
      (fun _ ↦ (v : E)) measurable_const (fun _ ↦ v.2)
    have hi := P.integrable_integratorHamiltonian y hy hL α μ lambda w hw
    simpa only [hyu] using hi
  have hcont : ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, Continuous (H t) := by
    apply Eventually.of_forall
    intro t
    have hcost : Continuous (fun v : P.controlSet ↦ P.runningCost t P.initial v) :=
      P.runningCost_continuous.comp ((continuous_const.prodMk continuous_const).prodMk
        continuous_subtype_val)
    exact (continuous_const.mul hcost).add
      ((α • lambda + ∫ s in Ioi t, w s ∂μ).continuous.comp continuous_subtype_val)
  have hae := OptimalControl.ae_hamiltonian_minimizing_of_integral_minimizing
    H u hu hi hconst hcont hcompare
  refine ⟨α, μ, hfin, hα, hne, hcomp, hsupport, ?_⟩
  filter_upwards [hae] with t ht
  intro v hv
  exact ht ⟨v, hv⟩

/-- The BV costate is constructed from the necessary state-constraint measure. -/
noncomputable def integratorCostate (α : ℝ) (μ : Measure P.Time)
    (lambda : E →L[ℝ] ℝ) (w : P.Time → E →L[ℝ] ℝ) (t : P.Time) : E →L[ℝ] ℝ :=
  α • lambda + ∫ s in Ioi t, w s ∂μ

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Integrability derives BV of the actual constructed costate. -/
theorem integratorCostate_boundedVariation (α : ℝ) (μ : Measure P.Time)
    [IsFiniteMeasure μ] (lambda : E →L[ℝ] ℝ) (w : P.Time → E →L[ℝ] ℝ)
    (hw : Continuous w) : BoundedVariationOn (P.integratorCostate α μ lambda w) univ := by
  have hwi : Integrable w μ :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : Isometry (fun q : E →L[ℝ] ℝ ↦ α • lambda + q) :=
    Isometry.of_dist_eq (fun _ _ ↦ dist_add_left _ _ _)
  exact hi.lipschitzWith.comp_boundedVariationOn (MeasureAdjoint.boundedVariation_order_tail hwi)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Exact measure-adjoint increments retain all atoms and singular measure parts. -/
theorem integratorCostate_increment (α : ℝ) (μ : Measure P.Time)
    [IsFiniteMeasure μ] (lambda : E →L[ℝ] ℝ) (w : P.Time → E →L[ℝ] ℝ)
    (hw : Continuous w) {a b : P.Time} (hab : a ≤ b) :
    P.integratorCostate α μ lambda w b - P.integratorCostate α μ lambda w a =
      -∫ s in Ioc a b, w s ∂μ := by
  have hwi : Integrable w μ :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simpa [integratorCostate, neg_sub] using
    congrArg Neg.neg (MeasureAdjoint.order_tail_sub hwi hab)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- At the terminal time the open tail is empty, including for terminal atoms. -/
theorem integratorCostate_terminal (α : ℝ) (μ : Measure P.Time)
    (lambda : E →L[ℝ] ℝ) (w : P.Time → E →L[ℝ] ℝ) :
    P.integratorCostate α μ lambda w (timeEnd P.horizon P.horizon_pos.le) = α • lambda := by
  have hs : Ioi (timeEnd P.horizon P.horizon_pos.le) = (∅ : Set P.Time) := by
    ext t
    simp only [mem_Ioi, mem_empty_iff_false, iff_false]
    exact not_lt.mpr t.2.2
  simp [integratorCostate, hs]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The constructed costate is right-continuous at every horizon time. -/
theorem integratorCostate_right_continuous (α : ℝ) (μ : Measure P.Time)
    [IsFiniteMeasure μ] (lambda : E →L[ℝ] ℝ) (w : P.Time → E →L[ℝ] ℝ)
    (hw : Continuous w) (t : P.Time) :
    ContinuousWithinAt (P.integratorCostate α μ lambda w) (Ici t) t := by
  have hwi : Integrable w μ :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact continuousWithinAt_const.add (MeasureAdjoint.continuousWithinAt_order_tail hwi t)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The terminal left trace retains the actual terminal measure atom. -/
theorem integratorCostate_terminal_left_trace (α : ℝ) (μ : Measure P.Time)
    [IsFiniteMeasure μ] (lambda : E →L[ℝ] ℝ) (w : P.Time → E →L[ℝ] ℝ)
    (hw : Continuous w) :
    Function.leftLim (P.integratorCostate α μ lambda w)
      (timeEnd P.horizon P.horizon_pos.le) =
        α • lambda + μ.real {timeEnd P.horizon P.horizon_pos.le} •
          w (timeEnd P.horizon P.horizon_pos.le) := by
  let b := timeEnd P.horizon P.horizon_pos.le
  have : (𝓝[<] b).NeBot := nhdsLT_neBot_of_exists_lt
    ⟨timeZero P.horizon P.horizon_pos.le, P.horizon_pos⟩
  have hwi : Integrable w μ :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl := (tendsto_const_nhds (x := α • lambda)).add
    (MeasureAdjoint.tendsto_order_tail_left hwi b)
  have hs : Ici b = ({b} : Set P.Time) := by
    ext t
    simp only [mem_Ici, mem_singleton_iff]
    exact ⟨fun ht ↦ le_antisymm t.2.2 ht, fun ht ↦ ht.ge⟩
  have he := leftLim_eq_of_tendsto hl
  rw [hs, integral_singleton] at he
  exact he

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Every positive horizon time has the correct negative measure-atom jump. -/
theorem integratorCostate_jump (α : ℝ) (μ : Measure P.Time)
    [IsFiniteMeasure μ] (lambda : E →L[ℝ] ℝ) (w : P.Time → E →L[ℝ] ℝ)
    (hw : Continuous w) (t : P.Time) (ht : 0 < (t : ℝ)) :
    P.integratorCostate α μ lambda w t - Function.leftLim (P.integratorCostate α μ lambda w) t =
      -(μ.real {t} • w t) := by
  have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt
    ⟨timeZero P.horizon P.horizon_pos.le, ht⟩
  have hwi : Integrable w μ :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl := (tendsto_const_nhds (x := α • lambda)).add
    (MeasureAdjoint.tendsto_order_tail_left hwi t)
  have he := leftLim_eq_of_tendsto hl
  change (α • lambda + ∫ s in Ioi t, w s ∂μ) -
    Function.leftLim (fun x ↦ α • lambda + ∫ s in Ioi x, w s ∂μ) t = _
  rw [he]
  have hj := congrArg Neg.neg (MeasureAdjoint.order_closed_tail_sub_open hwi t)
  simpa [integratorCostate, neg_sub] using hj

/-- Scoped necessity PMP: actual optimality produces measures and the BV costate,
exact measure-adjoint increments, terminal value and a common AE control minimum. -/
theorem exists_integrator_state_pmp
    (hf : ∀ t x u, P.dynamics t x u = u)
    (lambda : E →L[ℝ] ℝ) (hterm : P.terminalCost = lambda)
    (hL : ∀ t x u, P.runningCost t x u = P.runningCost t P.initial u)
    (w : P.Time → E →L[ℝ] ℝ) (hw : Continuous w)
    (c : P.Time → ℝ) (hc : Continuous c)
    (hg : ∀ t x, P.constraint (t, 0) x = w t x + c t)
    (z : P.Candidate) (hz : P.IsMinimum z) :
    ∃ (α : ℝ) (μ : Measure P.Time), IsFiniteMeasure μ ∧ 0 ≤ α ∧
      (α ≠ 0 ∨ μ ≠ 0) ∧ (∫ t, P.singleResidual z t ∂μ) = 0 ∧
      μ {t | P.singleResidual z t ≠ 0} = 0 ∧
      BoundedVariationOn (P.integratorCostate α μ lambda w) univ ∧
      (∀ t, ContinuousWithinAt (P.integratorCostate α μ lambda w) (Ici t) t) ∧
      (∀ t : P.Time, 0 < (t : ℝ) →
        P.integratorCostate α μ lambda w t -
          Function.leftLim (P.integratorCostate α μ lambda w) t = -(μ.real {t} • w t)) ∧
      (∀ a b : P.Time, a ≤ b →
        P.integratorCostate α μ lambda w b - P.integratorCostate α μ lambda w a =
          -∫ s in Ioc a b, w s ∂μ) ∧
      P.integratorCostate α μ lambda w (timeEnd P.horizon P.horizon_pos.le) = α • lambda ∧
      Function.leftLim (P.integratorCostate α μ lambda w)
        (timeEnd P.horizon P.horizon_pos.le) =
          α • lambda + μ.real {timeEnd P.horizon P.horizon_pos.le} •
            w (timeEnd P.horizon P.horizon_pos.le) ∧
      ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v ∈ P.controlSet,
        α * P.runningCost t P.initial (z.2 t) + P.integratorCostate α μ lambda w t (z.2 t) ≤
          α * P.runningCost t P.initial v + P.integratorCostate α μ lambda w t v := by
  obtain ⟨α, μ, hfin, hα, hne, hcomp, hsupp, hmin⟩ :=
    P.exists_integrator_state_minimum_principle hf lambda hterm hL w hw c hc hg z hz
  let : IsFiniteMeasure μ := hfin
  exact ⟨α, μ, hfin, hα, hne, hcomp, hsupp,
    P.integratorCostate_boundedVariation α μ lambda w hw,
    P.integratorCostate_right_continuous α μ lambda w hw,
    P.integratorCostate_jump α μ lambda w hw,
    fun a b hab ↦ P.integratorCostate_increment α μ lambda w hw hab,
    P.integratorCostate_terminal α μ lambda w,
    P.integratorCostate_terminal_left_trace α μ lambda w hw, hmin⟩

end OptimalControl.ConvexStateControlProblem
