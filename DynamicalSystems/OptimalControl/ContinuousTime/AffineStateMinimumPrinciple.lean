/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.StateControlAdjointPairing
public import DynamicalSystems.Mathlib.Analysis.ODE.MeasureAdjointBalance
public import DynamicalSystems.Mathlib.Analysis.BoundedVariation.Add

/-!
# Constructed measure costates for affine state-control problems

Both running spatial derivatives and indexed state normals are transported through the
actual state transition. The open-tail convention retains terminal atoms in left traces.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology

namespace OptimalControl.ConvexStateControlProblem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {n : ℕ} (P : OptimalControl.ConvexStateControlProblem E V n)

/-- Real-time costate, constructed from both indexed constraint measures and running cost. -/
noncomputable def affineCostateReal (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (α : ℝ) (μ : Measure P.ConstraintIndex)
    (Phi : ℝ → ℝ → E →L[ℝ] E) (t : ℝ) : E →L[ℝ] ℝ :=
  MeasureAdjoint.indexedPropagatedCostate (fun q : P.ConstraintIndex ↦ (q.1 : ℝ)) Phi μ
    (fun q ↦ (P.stateConstraintNormal D z q).comp (Phi q.1 0))
    (α • (D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le))).comp
      (Phi P.horizon 0)) t +
  MeasureAdjoint.indexedPropagatedCostate ((↑) : P.Time → ℝ) Phi
    (horizonProbability P.horizon P.horizon_pos).toMeasure
    (fun s ↦ (P.horizon * α) • (P.runningStateCovector D z s).comp (Phi s 0)) 0 t

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- On the actual horizon the real-time construction equals the control-pairing adjoint. -/
theorem affineCostateReal_eq (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (α : ℝ) (μ : Measure P.ConstraintIndex)
    (Phi : ℝ → ℝ → E →L[ℝ] E) (t : P.Time) :
    P.affineCostateReal D z α μ Phi t =
      P.affineMeasureCostate D z α μ (fun s ↦ Phi s 0) (fun s ↦ Phi 0 s) t := by
  have ht : {s : P.Time | (t : ℝ) < (s : ℝ)} = Ioi t := rfl
  have hq : {q : P.ConstraintIndex | (t : ℝ) < (q.1 : ℝ)} = {q | t < q.1} := rfl
  simp only [affineCostateReal, MeasureAdjoint.indexedPropagatedCostate,
    affineMeasureCostate, referenceFrameAdjoint, zero_add, ← ContinuousLinearMap.add_comp,
    integral_smul, mul_smul, timeEnd, ht, hq]
  congr 1
  abel

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Continuous normal data make the transported constraint density integrable. -/
theorem integrable_affineConstraintDensity (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (μ : Measure P.ConstraintIndex) [IsFiniteMeasure μ]
    (Phi : ℝ → ℝ → E →L[ℝ] E) (hPhi : Continuous (Function.uncurry Phi)) :
    Integrable (fun q ↦ (P.stateConstraintNormal D z q).comp (Phi q.1 0)) μ := by
  exact P.integrable_stateConstraintNormal D z μ (fun s ↦ Phi s 0)
    (hPhi.comp (continuous_subtype_val.prodMk continuous_const))

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- Compact controls derive integrability of the transported running density. -/
theorem integrable_affineRunningDensity (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z) (α : ℝ)
    (Phi : ℝ → ℝ → E →L[ℝ] E) (hPhi : Continuous (Function.uncurry Phi)) :
    Integrable (fun s ↦ (P.horizon * α) •
      (P.runningStateCovector D z s).comp (Phi s 0))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  exact P.integrable_runningStateCovector D z hz (fun s ↦ Phi s 0)
    (hPhi.comp (continuous_subtype_val.prodMk continuous_const)) (P.horizon * α)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- BV follows from the two integrable tails and the actual backward transition. -/
theorem affineCostateReal_boundedVariation (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z) (α : ℝ)
    (μ : Measure P.ConstraintIndex) [IsFiniteMeasure μ]
    {A : ℝ → E →L[ℝ] E} {Phi : ℝ → ℝ → E →L[ℝ] E}
    (hPhi : IsStateTransition A Phi) (hA : Continuous A) (a b : ℝ) :
    BoundedVariationOn (P.affineCostateReal D z α μ Phi) (Icc a b) := by
  have hn := P.integrable_affineConstraintDensity D z μ Phi hPhi.continuous
  have hl := P.integrable_affineRunningDensity D z hz α Phi hPhi.continuous
  exact (MeasureAdjoint.indexed_propagated_boundedVariation
    (fun q : P.ConstraintIndex ↦ (q.1 : ℝ)) (continuous_subtype_val.comp continuous_fst)
    hn _ hPhi hA a b).add
      (MeasureAdjoint.indexed_propagated_boundedVariation ((↑) : P.Time → ℝ)
        continuous_subtype_val hl 0 hPhi hA a b)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- Both integrable tails retain a right-continuous real-time costate representative. -/
theorem affineCostateReal_right_continuous (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z) (α : ℝ)
    (μ : Measure P.ConstraintIndex) [IsFiniteMeasure μ]
    {A : ℝ → E →L[ℝ] E} {Phi : ℝ → ℝ → E →L[ℝ] E}
    (hPhi : IsStateTransition A Phi) (t : ℝ) :
    ContinuousWithinAt (P.affineCostateReal D z α μ Phi) (Ici t) t := by
  have hn := P.integrable_affineConstraintDensity D z μ Phi hPhi.continuous
  have hl := P.integrable_affineRunningDensity D z hz α Phi hPhi.continuous
  exact (MeasureAdjoint.indexed_propagated_right_continuous
    (fun q : P.ConstraintIndex ↦ (q.1 : ℝ)) (continuous_subtype_val.comp continuous_fst)
    hn _ hPhi t).add
      (MeasureAdjoint.indexed_propagated_right_continuous ((↑) : P.Time → ℝ)
        continuous_subtype_val hl 0 hPhi t)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- Left limits of the sum are obtained from the actual constructed tail limits. -/
theorem affineCostateReal_leftLim_add (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z) (α : ℝ)
    (μ : Measure P.ConstraintIndex) [IsFiniteMeasure μ]
    {A : ℝ → E →L[ℝ] E} {Phi : ℝ → ℝ → E →L[ℝ] E}
    (hPhi : IsStateTransition A Phi) (t : ℝ) :
    Function.leftLim (P.affineCostateReal D z α μ Phi) t =
      Function.leftLim (MeasureAdjoint.indexedPropagatedCostate
        (fun q : P.ConstraintIndex ↦ (q.1 : ℝ)) Phi μ
        (fun q ↦ (P.stateConstraintNormal D z q).comp (Phi q.1 0))
        (α • (D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le))).comp
          (Phi P.horizon 0))) t +
      Function.leftLim (MeasureAdjoint.indexedPropagatedCostate ((↑) : P.Time → ℝ) Phi
        (horizonProbability P.horizon P.horizon_pos).toMeasure
        (fun s ↦ (P.horizon * α) • (P.runningStateCovector D z s).comp (Phi s 0)) 0) t := by
  have hn := P.integrable_affineConstraintDensity D z μ Phi hPhi.continuous
  have hl := P.integrable_affineRunningDensity D z hz α Phi hPhi.continuous
  rw [MeasureAdjoint.indexed_propagated_left_trace
      (fun q : P.ConstraintIndex ↦ (q.1 : ℝ)) (continuous_subtype_val.comp continuous_fst)
      hn _ hPhi t,
    MeasureAdjoint.indexed_propagated_left_trace ((↑) : P.Time → ℝ)
      continuous_subtype_val hl 0 hPhi t]
  apply leftLim_eq_of_tendsto
  have hp := (hPhi.backward 0 t).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Iio t))
  have hnt := (tendsto_const_nhds (x :=
      α • (D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le))).comp
        (Phi P.horizon 0))).add (MeasureAdjoint.tendsto_indexed_tail_left
      (fun q : P.ConstraintIndex ↦ (q.1 : ℝ))
      (continuous_subtype_val.comp continuous_fst) hn t)
  have hlt := (tendsto_const_nhds (x := (0 : E →L[ℝ] ℝ))).add
    (MeasureAdjoint.tendsto_indexed_tail_left ((↑) : P.Time → ℝ) continuous_subtype_val hl t)
  exact (((continuous_fst.clm_comp continuous_snd).tendsto _).comp
    (hnt.prodMk_nhds hp)).add (((continuous_fst.clm_comp continuous_snd).tendsto _).comp
      (hlt.prodMk_nhds hp))

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- The costate jump is exactly the negative spatial normal on the full multiplier time fiber.
The running-cost measure has no atoms, even at the horizon endpoints. -/
theorem affineCostateReal_jump (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z) (α : ℝ)
    (μ : Measure P.ConstraintIndex) [IsFiniteMeasure μ]
    {A : ℝ → E →L[ℝ] E} {Phi : ℝ → ℝ → E →L[ℝ] E}
    (hPhi : IsStateTransition A Phi) (t : ℝ) :
    P.affineCostateReal D z α μ Phi t -
      Function.leftLim (P.affineCostateReal D z α μ Phi) t =
        -(∫ q in {q : P.ConstraintIndex | (q.1 : ℝ) = t},
          P.stateConstraintNormal D z q ∂μ) := by
  have hn := P.integrable_affineConstraintDensity D z μ Phi hPhi.continuous
  have hl := P.integrable_affineRunningDensity D z hz α Phi hPhi.continuous
  have hsub : ({s : P.Time | (s : ℝ) = t} : Set P.Time).Subsingleton := by
    intro a ha b hb
    exact Subtype.ext (ha.trans hb.symm)
  have hzero := setIntegral_measure_zero
    (fun s ↦ (P.horizon * α) • (P.runningStateCovector D z s).comp (Phi s 0))
    (hsub.measure_zero (μ := (horizonProbability P.horizon P.horizon_pos).toMeasure))
  rw [P.affineCostateReal_leftLim_add D z hz α μ hPhi t]
  unfold affineCostateReal
  have he : ∀ a b c d : E →L[ℝ] ℝ, (a + b) - (c + d) = (a - c) + (b - d) := by
    intros
    abel
  rw [he, MeasureAdjoint.indexed_propagated_jump
      (fun q : P.ConstraintIndex ↦ (q.1 : ℝ)) (continuous_subtype_val.comp continuous_fst)
      hn _ hPhi t,
    MeasureAdjoint.indexed_propagated_jump ((↑) : P.Time → ℝ)
      continuous_subtype_val hl 0 hPhi t, hzero]
  simp only [ContinuousLinearMap.zero_comp, neg_zero, add_zero]
  congr 1
  have hc := ((ContinuousLinearMap.compL ℝ E E ℝ).flip (Phi 0 t)).integral_comp_comm
    (hn.integrableOn (s := {q : P.ConstraintIndex | (q.1 : ℝ) = t}))
  change (∫ q in {q : P.ConstraintIndex | (q.1 : ℝ) = t},
    ((P.stateConstraintNormal D z q).comp (Phi q.1 0)).comp (Phi 0 t) ∂μ) =
      (∫ q in {q : P.ConstraintIndex | (q.1 : ℝ) = t},
        (P.stateConstraintNormal D z q).comp (Phi q.1 0) ∂μ).comp (Phi 0 t) at hc
  rw [← hc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem ((isClosed_eq
    (continuous_subtype_val.comp continuous_fst) continuous_const).measurableSet)] with q hq
  change (q.1 : ℝ) = t at hq
  rw [← hq, ContinuousLinearMap.comp_assoc, hPhi.cocycle, hPhi.diag,
    ContinuousLinearMap.comp_id]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ V] in
/-- Exact additive adjoint balance, derived from the two constructed indexed tails.
Running derivatives use the actual normalized time measure multiplied by the horizon. -/
theorem affineCostateReal_increment (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z) (α : ℝ)
    (μ : Measure P.ConstraintIndex) [IsFiniteMeasure μ]
    {A : ℝ → E →L[ℝ] E} {Phi : ℝ → ℝ → E →L[ℝ] E}
    (hPhi : IsStateTransition A Phi) (hA : Continuous A) {a b : ℝ} (hab : a ≤ b) :
    P.affineCostateReal D z α μ Phi b - P.affineCostateReal D z α μ Phi a =
      -(∫ t in a..b, (P.affineCostateReal D z α μ Phi t).comp (A t)) -
      (P.horizon * α) • (∫ s in {s : P.Time | a < (s : ℝ) ∧ (s : ℝ) ≤ b},
        P.runningStateCovector D z s ∂horizonProbability P.horizon P.horizon_pos) -
      ∫ q in {q : P.ConstraintIndex | a < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ b},
        P.stateConstraintNormal D z q ∂μ := by
  let k := fun q : P.ConstraintIndex ↦ (q.1 : ℝ)
  let w := fun q ↦ (P.stateConstraintNormal D z q).comp (Phi q.1 0)
  let v := fun s ↦ (P.horizon * α) • (P.runningStateCovector D z s).comp (Phi s 0)
  let lambda := α • (D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le))).comp
    (Phi P.horizon 0)
  let q := MeasureAdjoint.indexedPropagatedCostate k Phi μ w lambda
  let r := MeasureAdjoint.indexedPropagatedCostate ((↑) : P.Time → ℝ) Phi
    (horizonProbability P.horizon P.horizon_pos).toMeasure v 0
  have hk : Continuous k := continuous_subtype_val.comp continuous_fst
  have hn := P.integrable_affineConstraintDensity D z μ Phi hPhi.continuous
  have hl := P.integrable_affineRunningDensity D z hz α Phi hPhi.continuous
  have hq := MeasureAdjoint.indexed_propagated_increment k hk hn lambda hPhi hA hab
  have hr := MeasureAdjoint.indexed_propagated_increment ((↑) : P.Time → ℝ)
    continuous_subtype_val hl 0 hPhi hA hab
  have hiq := MeasureAdjoint.indexed_propagated_integrableOn_comp k hk hn lambda
    hPhi hA a b
  have hir := MeasureAdjoint.indexed_propagated_integrableOn_comp ((↑) : P.Time → ℝ)
    continuous_subtype_val hl 0 hPhi hA a b
  dsimp only at hq hr
  have hq' : q b - q a = -(∫ t in a..b, (q t).comp (A t)) -
      ∫ q in {q : P.ConstraintIndex | a < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ b},
        P.stateConstraintNormal D z q ∂μ := by
    simpa only [k, ContinuousLinearMap.comp_assoc, hPhi.cocycle, hPhi.diag,
      ContinuousLinearMap.comp_id] using hq
  have hr' : r b - r a = -(∫ t in a..b, (r t).comp (A t)) -
      (P.horizon * α) • (∫ s in {s : P.Time | a < (s : ℝ) ∧ (s : ℝ) ≤ b},
        P.runningStateCovector D z s ∂horizonProbability P.horizon P.horizon_pos) := by
    simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc,
      hPhi.cocycle, hPhi.diag, ContinuousLinearMap.comp_id, integral_smul] using hr
  change (q b + r b) - (q a + r a) =
    -(∫ t in a..b, (q t + r t).comp (A t)) - _ - _
  simp only [ContinuousLinearMap.add_comp]
  rw [intervalIntegral.integral_add
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hiq)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hir)]
  have he : (q b + r b) - (q a + r a) = (q b - q a) + (r b - r a) := by abel
  rw [he, hq', hr']
  abel

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The value at the horizon excludes the terminal atom, giving the actual terminal gradient. -/
theorem affineCostateReal_terminal (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (α : ℝ) (μ : Measure P.ConstraintIndex)
    {A : ℝ → E →L[ℝ] E} {Phi : ℝ → ℝ → E →L[ℝ] E}
    (hPhi : IsStateTransition A Phi) :
    P.affineCostateReal D z α μ Phi P.horizon =
      α • D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le)) := by
  have hs : {s : P.Time | P.horizon < (s : ℝ)} = ∅ := by
    ext s
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_lt.mpr s.2.2
  have hq : {q : P.ConstraintIndex | P.horizon < (q.1 : ℝ)} = ∅ := by
    ext q
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_lt.mpr q.1.2.2
  simp only [affineCostateReal, MeasureAdjoint.indexedPropagatedCostate, hs, hq,
    setIntegral_empty, add_zero, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc, hPhi.cocycle,
    hPhi.diag, ContinuousLinearMap.comp_id]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- The terminal left trace includes every terminal constraint atom. -/
theorem affineCostateReal_terminal_left_trace (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z) (α : ℝ)
    (μ : Measure P.ConstraintIndex) [IsFiniteMeasure μ]
    {A : ℝ → E →L[ℝ] E} {Phi : ℝ → ℝ → E →L[ℝ] E}
    (hPhi : IsStateTransition A Phi) :
    Function.leftLim (P.affineCostateReal D z α μ Phi) P.horizon =
      α • D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le)) +
        ∫ q in {q : P.ConstraintIndex | (q.1 : ℝ) = P.horizon},
          P.stateConstraintNormal D z q ∂μ := by
  have hj := P.affineCostateReal_jump D z hz α μ hPhi P.horizon
  rw [P.affineCostateReal_terminal D z α μ hPhi] at hj
  have he : Function.leftLim (P.affineCostateReal D z α μ Phi) P.horizon -
      α • D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le)) =
        ∫ q in {q : P.ConstraintIndex | (q.1 : ℝ) = P.horizon},
          P.stateConstraintNormal D z q ∂μ := by
    simpa only [neg_sub, neg_neg] using congrArg Neg.neg hj
  simpa only [add_comm] using sub_eq_iff_eq_add.mp he

end OptimalControl.ConvexStateControlProblem
