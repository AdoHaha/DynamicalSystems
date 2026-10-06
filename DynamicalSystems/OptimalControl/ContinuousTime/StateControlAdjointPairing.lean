/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.StateControlFirstVariation
public import DynamicalSystems.Mathlib.Analysis.ODE.MeasureAdjointPairing
public import DynamicalSystems.OptimalControl.ContinuousTime.MeasurableHamiltonian

/-!
# State-control first variation paired with the constructed measure adjoint

A factorized affine state response turns the actual first variation into a control pairing.
The reference-frame adjoint combines terminal, running and indexed state-constraint tails.
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

/-- The running spatial covector along the actual reference pair. -/
noncomputable def runningStateCovector (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (t : P.Time) : E →L[ℝ] ℝ :=
  (D.runningDerivative t (z.1 t, z.2 t)).comp (ContinuousLinearMap.inl ℝ E V)

/-- The running control covector along the actual reference pair. -/
noncomputable def runningControlCovector (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (t : P.Time) : V →L[ℝ] ℝ :=
  (D.runningDerivative t (z.1 t, z.2 t)).comp (ContinuousLinearMap.inr ℝ E V)

/-- The spatial normal of each indexed constraint along the actual trajectory. -/
noncomputable def stateConstraintNormal (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (q : P.ConstraintIndex) : E →L[ℝ] ℝ :=
  D.constraintDerivative q (z.1 q.1)

/-- Adjoint in a fixed frame, containing the actual running derivative and indexed measures. -/
noncomputable def referenceFrameAdjoint (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (α : ℝ) (μ : Measure P.ConstraintIndex)
    (K : P.Time → E →L[ℝ] E) (t : P.Time) : E →L[ℝ] ℝ :=
  α • (D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le))).comp
      (K (timeEnd P.horizon P.horizon_pos.le)) +
    P.horizon • (∫ s in Ioi t, α • (P.runningStateCovector D z s).comp (K s)
      ∂horizonProbability P.horizon P.horizon_pos) +
    ∫ q in {q | t < q.1}, (P.stateConstraintNormal D z q).comp (K q.1) ∂μ

/-- The costate is transported back from the constructed reference-frame adjoint. -/
noncomputable def affineMeasureCostate (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (α : ℝ) (μ : Measure P.ConstraintIndex)
    (K J : P.Time → E →L[ℝ] E) (t : P.Time) : E →L[ℝ] ℝ :=
  (P.referenceFrameAdjoint D z α μ K t).comp (J t)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- Compactness derives integrability of transported running spatial covectors. -/
theorem integrable_runningStateCovector (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z)
    (K : P.Time → E →L[ℝ] E) (hK : Continuous K) (α : ℝ) :
    Integrable (fun t ↦ α • (P.runningStateCovector D z t).comp (K t))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  apply P.integrable_composition z hz
    (fun t x u ↦ α • (D.runningDerivative t (x, u)).comp
      (ContinuousLinearMap.inl ℝ E V) |>.comp (K t))
  exact ((D.runningDerivative_continuous.comp
    (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))).clm_comp
      continuous_const).const_smul α |>.clm_comp (hK.comp continuous_fst.fst)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The transported nonlinear constraint normal is integrable for every finite multiplier. -/
theorem integrable_stateConstraintNormal (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (μ : Measure P.ConstraintIndex) [IsFiniteMeasure μ]
    (K : P.Time → E →L[ℝ] E) (hK : Continuous K) :
    Integrable (fun q ↦ (P.stateConstraintNormal D z q).comp (K q.1)) μ := by
  have hc : Continuous (fun q ↦ (P.stateConstraintNormal D z q).comp (K q.1)) :=
    (D.constraintDerivative_continuous.comp
      (continuous_id.prodMk (z.1.continuous.comp continuous_fst))).clm_comp
        (hK.comp continuous_fst)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- Continuous transport of admissible controls is integrable, with no extra bound premise. -/
theorem integrable_transformed_control (z : P.Candidate) (hz : P.DynamicsAdmissible z)
    (J : P.Time → E →L[ℝ] E) (B : P.Time → V →L[ℝ] E)
    (hJ : Continuous J) (hB : Continuous B) :
    Integrable (fun t ↦ J t (B t (z.2 t)))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  apply P.integrable_composition z hz (fun t _ u ↦ J t (B t u))
  exact (hJ.comp continuous_fst.fst).clm_apply
    ((hB.comp continuous_fst.fst).clm_apply continuous_snd)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Terminal strict prefixes have full Lebesgue mass. -/
theorem integral_terminal_prefix (v : P.Time → E) :
    (∫ t in Iio (timeEnd P.horizon P.horizon_pos.le), v t
      ∂horizonProbability P.horizon P.horizon_pos) =
      ∫ t, v t ∂horizonProbability P.horizon P.horizon_pos := by
  apply (integral_eq_setIntegral _ _).symm
  have h := Measure.ae_ne (horizonProbability P.horizon P.horizon_pos).toMeasure
    (timeEnd P.horizon P.horizon_pos.le)
  filter_upwards [h] with t ht
  exact lt_of_le_of_ne t.2.2 (fun he ↦ ht (Subtype.ext he))

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ V] in
/-- Fubini turns the actual first variation into the constructed costate-control pairing.
The response identity is an intermediate hypothesis discharged by affine integral dynamics. -/
theorem firstVariation_eq_control_pairing (D : P.ContinuouslyDifferentiableData)
    (α : ℝ) (μ : Measure P.ConstraintIndex) [IsFiniteMeasure μ]
    (z y : P.Candidate) (hz : P.DynamicsAdmissible z) (hy : P.DynamicsAdmissible y)
    (K J : P.Time → E →L[ℝ] E) (B : P.Time → V →L[ℝ] E)
    (hK : Continuous K) (hJ : Continuous J) (hB : Continuous B)
    (hresponse : ∀ t, y.1 t - z.1 t = P.horizon • K t
      (∫ s in Iio t, J s (B s (y.2 s - z.2 s))
        ∂horizonProbability P.horizon P.horizon_pos)) :
    P.stateControlFirstVariation D α μ z y =
      P.horizon * ∫ t, (α • P.runningControlCovector D z t +
        (P.affineMeasureCostate D z α μ K J t).comp (B t)) (y.2 t - z.2 t)
        ∂horizonProbability P.horizon P.horizon_pos := by
  let ν := (horizonProbability P.horizon P.horizon_pos).toMeasure
  let v := fun t ↦ J t (B t (y.2 t - z.2 t))
  have hv : Integrable v ν := by
    have hi := (P.integrable_transformed_control y hy J B hJ hB).sub
      (P.integrable_transformed_control z hz J B hJ hB)
    apply hi.congr
    exact Eventually.of_forall (fun t ↦ by simp [v, map_sub])
  let ell := fun t ↦ P.horizon • (α • (P.runningStateCovector D z t).comp (K t))
  let normal := fun q ↦ (P.stateConstraintNormal D z q).comp (K q.1)
  let lambda := α • (D.terminalDerivative
    (z.1 (timeEnd P.horizon P.horizon_pos.le))).comp
      (K (timeEnd P.horizon P.horizon_pos.le))
  have hell : Integrable ell ν :=
    (P.integrable_runningStateCovector D z hz K hK α).smul P.horizon
  have hn : Integrable normal μ := P.integrable_stateConstraintNormal D z μ K hK
  have hp := MeasureAdjoint.integral_firstVariation_pairing
    (fun q : P.ConstraintIndex ↦ q.1) continuous_fst lambda hell hn hv
  have hdu : Integrable (fun t ↦ P.runningControlCovector D z t) ν := by
    apply P.integrable_composition z hz (fun t x u ↦
      (D.runningDerivative t (x,u)).comp (ContinuousLinearMap.inr ℝ E V))
    exact (D.runningDerivative_continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))).clm_comp
      continuous_const
  have huu (a : P.Candidate) (ha : P.DynamicsAdmissible a) :
      Integrable (fun t ↦ (P.runningControlCovector D z t) (a.2 t)) ν := by
    obtain ⟨R, _, hR⟩ := P.exists_candidate_norm_bound a ha
    apply ((hdu.norm).const_mul (R : ℝ)).mono'
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hdu.aestronglyMeasurable.prodMk ha.1.aestronglyMeasurable))
    exact Eventually.of_forall (fun t ↦ by
      apply ((P.runningControlCovector D z t).le_opNorm (a.2 t)).trans
      nlinarith [hR t, norm_nonneg (P.runningControlCovector D z t)])
  have hu : Integrable (fun t ↦ (P.runningControlCovector D z t) (y.2 t - z.2 t)) ν := by
    apply ((huu y hy).sub (huu z hz)).congr
    exact Eventually.of_forall (fun t ↦ by simp [map_sub])
  have hl := MeasureAdjoint.integrable_order_prefix_apply hell hv
  have hnormalprefix : Integrable
      (fun q ↦ normal q (∫ t in Iio q.1, v t ∂ν)) μ := by
    have hw : Integrable (fun q ↦ normal q (∫ t in Iio q.1, v t ∂ν)) μ := by
      have hp' : Integrable (fun q : P.ConstraintIndex × P.Time ↦
          normal q.1 (v q.2)) (μ.prod ν) := by
        apply hn.op_fst_snd _ _ hv
        · exact continuous_fst.clm_apply continuous_snd
        · exact ⟨1, fun f x ↦ by simpa using f.le_opNorm x⟩
      have hs : MeasurableSet {q : P.ConstraintIndex × P.Time | q.2 < q.1.1} :=
        (isOpen_lt continuous_snd continuous_fst.fst).measurableSet
      apply (hp'.indicator hs).integral_prod_left.congr
      apply Eventually.of_forall
      intro q
      dsimp only
      rw [← (normal q).integral_comp_comm hv.integrableOn,
        ← integral_indicator measurableSet_Iio]
      apply integral_congr_ae
      exact Eventually.of_forall (fun t ↦ by simp [Set.indicator])
    exact hw
  have hr (t : P.Time) :
      α * D.runningDerivative t (z.1 t,z.2 t) (y.1 t-z.1 t,y.2 t-z.2 t) =
        ell t (∫ s in Iio t, v s ∂ν) + α * (P.runningControlCovector D z t) (y.2 t-z.2 t) := by
    rw [hresponse t]
    have he : (P.horizon • K t (∫ s in Iio t, v s ∂ν), y.2 t-z.2 t) =
        (P.horizon • K t (∫ s in Iio t, v s ∂ν),0) + (0,y.2 t-z.2 t) := by simp
    rw [he, map_add]
    have hsp : (P.horizon • K t (∫ s in Iio t, v s ∂ν), (0 : V)) =
        P.horizon • (K t (∫ s in Iio t, v s ∂ν), (0 : V)) := by simp
    rw [hsp, map_smul]
    simp [ell, runningStateCovector, runningControlCovector, smul_eq_mul]
    ring
  have hc (q : P.ConstraintIndex) :
      D.constraintDerivative q (z.1 q.1) (y.1 q.1-z.1 q.1) =
        P.horizon * normal q (∫ s in Iio q.1, v s ∂ν) := by
    rw [hresponse q.1]
    simp [normal, stateConstraintNormal, smul_eq_mul, v, ν]
  have ht : α * D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le))
      (y.1 (timeEnd P.horizon P.horizon_pos.le)-z.1 (timeEnd P.horizon P.horizon_pos.le)) =
      P.horizon * lambda (∫ t, v t ∂ν) := by
    rw [hresponse]
    change α * D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le))
      (P.horizon • K (timeEnd P.horizon P.horizon_pos.le)
        (∫ t in Iio (timeEnd P.horizon P.horizon_pos.le), v t ∂ν)) = _
    rw [P.integral_terminal_prefix v]
    simp [lambda, smul_eq_mul]
    ring
  have hframe (t : P.Time) :
      lambda + (∫ s in Ioi t, ell s ∂ν) +
        ∫ q in {q | t < q.1}, normal q ∂μ = P.referenceFrameAdjoint D z α μ K t := by
    simp [referenceFrameAdjoint, lambda, ell, normal, ν, integral_smul]
  rw [show P.stateControlFirstVariation D α μ z y =
      P.horizon * (lambda (∫ t, v t ∂ν) +
        (∫ s, ell s (∫ t in Iio s, v t ∂ν) ∂ν) +
        (∫ q, normal q (∫ t in Iio q.1, v t ∂ν) ∂μ)) +
        P.horizon * (∫ t, α * (P.runningControlCovector D z t) (y.2 t-z.2 t) ∂ν) by
      unfold stateControlFirstVariation
      rw [mul_add, ht]
      simp_rw [hc]
      rw [integral_const_mul]
      have he := integral_congr_ae (μ := ν) (Eventually.of_forall hr)
      rw [integral_const_mul, integral_add hl (hu.const_mul α)] at he
      change α * _ = _ at he
      change P.horizon * lambda _ + α * (P.horizon * (∫ t,
        D.runningDerivative t (z.1 t,z.2 t) (y.1 t-z.1 t,y.2 t-z.2 t) ∂ν)) + _ = _
      rw [mul_left_comm α P.horizon, he]
      ring, hp]
  have hf : Integrable (fun t ↦ (P.referenceFrameAdjoint D z α μ K t) (v t)) ν := by
    have h := ((lambda.integrable_comp hv).add
      (MeasureAdjoint.integrable_order_tail_apply hell hv)).add
      (MeasureAdjoint.integrable_indexed_tail_apply (fun q : P.ConstraintIndex ↦ q.1)
        continuous_fst hn hv)
    apply h.congr
    exact Eventually.of_forall (fun t ↦ by
      simp only [Pi.add_apply, ← add_apply, hframe])
  simp_rw [hframe]
  rw [← mul_add, ← integral_add hf (hu.const_mul α)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun t ↦ by
    simp [affineMeasureCostate, v, add_apply, smul_eq_mul]
    ring)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- The constructed reference-frame adjoint is integrable, including its indexed measure tail. -/
theorem integrable_referenceFrameAdjoint (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z) (α : ℝ)
    (μ : Measure P.ConstraintIndex) [IsFiniteMeasure μ]
    (K : P.Time → E →L[ℝ] E) (hK : Continuous K) :
    Integrable (P.referenceFrameAdjoint D z α μ K)
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hi := P.integrable_runningStateCovector D z hz K hK α
  have hn := P.integrable_stateConstraintNormal D z μ K hK
  exact ((integrable_const _).add ((MeasureAdjoint.integrable_order_tail hi).smul
    P.horizon)).add (MeasureAdjoint.integrable_indexed_tail
      (fun q : P.ConstraintIndex ↦ q.1) continuous_fst hn)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Continuous bounded transport preserves integrability of the constructed control costate. -/
theorem integrable_affineMeasureCostate_control (D : P.ContinuouslyDifferentiableData)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z) (α : ℝ)
    (μ : Measure P.ConstraintIndex) [IsFiniteMeasure μ]
    (K J : P.Time → E →L[ℝ] E) (B : P.Time → V →L[ℝ] E)
    (hK : Continuous K) (hJ : Continuous J) (hB : Continuous B) :
    Integrable (fun t ↦ (P.affineMeasureCostate D z α μ K J t).comp (B t))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hi := P.integrable_referenceFrameAdjoint D z hz α μ K hK
  have hc : Continuous (fun t ↦ (J t).comp (B t)) := hJ.clm_comp hB
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hm : AEStronglyMeasurable
      (fun t ↦ (P.referenceFrameAdjoint D z α μ K t).comp ((J t).comp (B t)))
      (horizonProbability P.horizon P.horizon_pos).toMeasure :=
    (continuous_fst.clm_comp continuous_snd).comp_aestronglyMeasurable
      (hi.aestronglyMeasurable.prodMk hc.aestronglyMeasurable)
  apply (hi.norm.const_mul (max C 0)).mono' (by
    convert hm using 1
    funext t
    simp [affineMeasureCostate, ContinuousLinearMap.comp_assoc])
  apply Eventually.of_forall
  intro t
  have hn := (P.referenceFrameAdjoint D z α μ K t).opNorm_comp_le ((J t).comp (B t))
  have hb := (hC _ ⟨t,rfl⟩).trans (le_max_left C 0)
  simp only [affineMeasureCostate, ContinuousLinearMap.comp_assoc]
  exact hn.trans (by nlinarith [norm_nonneg (P.referenceFrameAdjoint D z α μ K t)])

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- An integrable covector pairs integrably with every measurable compact-set control. -/
theorem integrable_covector_control (G : P.Time → V →L[ℝ] ℝ)
    (hG : Integrable G (horizonProbability P.horizon P.horizon_pos).toMeasure)
    (u : P.Time → V) (hu : Measurable u) (hU : ∀ t, u t ∈ P.controlSet) :
    Integrable (fun t ↦ G t (u t))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  obtain ⟨R, hR⟩ := P.controlSet_compact.isBounded.exists_norm_le
  apply (hG.norm.const_mul (max R 0)).mono'
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hG.aestronglyMeasurable.prodMk hu.aestronglyMeasurable))
  exact Eventually.of_forall (fun t ↦ by
    apply ((G t).le_opNorm (u t)).trans
    have hb := (hR _ (hU t)).trans (le_max_left R 0)
    nlinarith [norm_nonneg (G t)])

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- Nonnegative integral pairings imply an actual Hamiltonian minimum on one common
full-measure set. Compact controls supply integrability; convex C1 data supplies support. -/
theorem ae_runningHamiltonian_minimizing_of_nonnegative_pairings
    (D : P.ContinuouslyDifferentiableData) (α : ℝ) (hα : 0 ≤ α)
    (z : P.Candidate) (hz : P.DynamicsAdmissible z)
    (Q : P.Time → V →L[ℝ] ℝ)
    (hQ : Integrable Q (horizonProbability P.horizon P.horizon_pos).toMeasure)
    (hpair : ∀ u : P.Time → V, Measurable u → (∀ t, u t ∈ P.controlSet) →
      0 ≤ ∫ t, (α • P.runningControlCovector D z t + Q t) (u t-z.2 t)
        ∂horizonProbability P.horizon P.horizon_pos) :
    ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v ∈ P.controlSet,
      α * P.runningCost t (z.1 t) (z.2 t) + Q t (z.2 t) ≤
        α * P.runningCost t (z.1 t) v + Q t v := by
  let ν := (horizonProbability P.horizon P.horizon_pos).toMeasure
  let G := fun t ↦ α • P.runningControlCovector D z t + Q t
  have hdu : Integrable (fun t ↦ P.runningControlCovector D z t) ν := by
    apply P.integrable_composition z hz (fun t x u ↦
      (D.runningDerivative t (x,u)).comp (ContinuousLinearMap.inr ℝ E V))
    exact (D.runningDerivative_continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))).clm_comp
      continuous_const
  have hG : Integrable G ν := (hdu.smul α).add hQ
  let ustar : P.Time → P.controlSet := fun t ↦ ⟨z.2 t,hz.2.1 t⟩
  have hu : Measurable ustar := hz.1.subtype_mk
  have hi := P.integrable_covector_control G hG z.2 hz.1 hz.2.1
  have hc (v : P.controlSet) : Integrable (fun t ↦ G t v) ν :=
    P.integrable_covector_control G hG (fun _ ↦ v) measurable_const (fun _ ↦ v.2)
  have hmin (u : P.Time → P.controlSet) (hu : Measurable u) :
      (∫ t, G t (ustar t) ∂ν) ≤ ∫ t, G t (u t) ∂ν := by
    have hui := P.integrable_covector_control G hG (fun t ↦ u t)
      (measurable_subtype_coe.comp hu) (fun t ↦ (u t).2)
    have hm := hpair (fun t ↦ u t) (measurable_subtype_coe.comp hu)
      (fun t ↦ (u t).2)
    have he : (∫ t, G t ((u t : V)-z.2 t) ∂ν) =
        (∫ t, G t (u t) ∂ν) - ∫ t, G t (z.2 t) ∂ν := by
      have he := integral_sub hui hi
      rw [← he]
      apply integral_congr_ae
      exact Eventually.of_forall (fun t ↦ by simp [map_sub])
    change 0 ≤ ∫ t, G t ((u t : V)-z.2 t) ∂ν at hm
    rw [he] at hm
    exact sub_nonneg.mp hm
  have hae := OptimalControl.ae_hamiltonian_minimizing_of_integral_minimizing
    (fun t (v : P.controlSet) ↦ G t v) ustar hu hi hc
    (Eventually.of_forall (fun t ↦ (G t).continuous.comp continuous_subtype_val)) hmin
  filter_upwards [hae] with t ht
  intro v hv
  have hm := ht ⟨v,hv⟩
  have hs := P.runningCost_supporting_controlDerivative D t (z.1 t) (z.2 t) v
  have hsm := mul_le_mul_of_nonneg_left hs hα
  change α * (P.runningControlCovector D z t) (z.2 t) + Q t (z.2 t) ≤
    α * (P.runningControlCovector D z t) v + Q t v at hm
  have hd : D.runningDerivative t (z.1 t,z.2 t) (0,v-z.2 t) =
      (P.runningControlCovector D z t) v - (P.runningControlCovector D z t) (z.2 t) := by
    simp [runningControlCovector, ← map_sub]
  rw [hd] at hsm
  nlinarith

end OptimalControl.ConvexStateControlProblem
