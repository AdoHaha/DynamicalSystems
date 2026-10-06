/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedControls
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuity of time-restricted occupation integrals

Weak convergence alone does not allow testing against a discontinuous time
indicator. A fixed time marginal supplies the missing uniform estimate:
continuous time functions approximate any integrable weight in L1 of that
marginal, uniformly over all relaxed controls. This proves continuity of the
actual Volterra-integral terms, without assuming a dynamics-closure theorem.
-/

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology Uniformity BoundedContinuousFunction

namespace OptimalControl.RelaxedControl

variable {τ U : Type*} [MeasurableSpace τ] [MeasurableSpace U]
  {ν : ProbabilityMeasure τ}

/-- Time projection is genuinely measure preserving. -/
theorem measurePreserving_fst (ρ : RelaxedControl τ U ν) :
    MeasurePreserving Prod.fst ρ.measure ν.toMeasure :=
  ⟨measurable_fst, ρ.fst_measure⟩

/-- Integration of a time-only function uses exactly the fixed marginal. -/
theorem integral_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : RelaxedControl τ U ν) {h : τ → E} (hh : AEStronglyMeasurable h ν.toMeasure) :
    (∫ z, h z.1 ∂ρ.measure) = ∫ t, h t ∂ν := by
  have hm : AEStronglyMeasurable h (Measure.map Prod.fst ρ.measure) := by
    rwa [ρ.measurePreserving_fst.map_eq]
  rw [← integral_map measurable_fst.aemeasurable hm, ρ.measurePreserving_fst.map_eq]

variable [MetricSpace τ] [BorelSpace τ] [CompactSpace τ]
  [MetricSpace U] [BorelSpace U] [CompactSpace U]

omit [CompactSpace τ] in
/-- Integrable time weights times bounded continuous integrands are
integrable for every fixed-marginal relaxed control. -/
theorem integrable_weighted (ρ : RelaxedControl τ U ν)
    (f : (τ × U) →ᵇ ℝ) {h : τ → ℝ} (hh : Integrable h ν.toMeasure) :
    Integrable (fun z => h z.1 * f z) ρ.measure :=
  (ρ.measurePreserving_fst.integrable_comp_of_integrable hh).mul_bdd
    f.continuous.aestronglyMeasurable (Eventually.of_forall f.norm_coe_le_norm)

omit [CompactSpace τ] in
/-- The crucial error bound is independent of the occupation measure. -/
theorem norm_weighted_integral_sub_le (ρ : RelaxedControl τ U ν)
    (f : (τ × U) →ᵇ ℝ) {h g : τ → ℝ}
    (hh : Integrable h ν.toMeasure) (hg : Integrable g ν.toMeasure) :
    ‖(∫ z, h z.1 * f z ∂ρ.measure) - (∫ z, g z.1 * f z ∂ρ.measure)‖ ≤
      ‖f‖ * ∫ t, ‖h t - g t‖ ∂ν := by
  rw [← integral_sub (ρ.integrable_weighted f hh) (ρ.integrable_weighted f hg)]
  calc
    ‖∫ z, h z.1 * f z - g z.1 * f z ∂ρ.measure‖ ≤
        ∫ z, ‖f‖ * ‖h z.1 - g z.1‖ ∂ρ.measure := by
      apply norm_integral_le_of_norm_le
        ((ρ.measurePreserving_fst.integrable_comp_of_integrable (hh.sub hg).norm).const_mul ‖f‖)
      filter_upwards with z
      rw [← sub_mul, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm z) (norm_nonneg _)
    _ = ‖f‖ * ∫ t, ‖h t - g t‖ ∂ν := by
      rw [integral_const_mul]
      exact congrArg (fun x : ℝ => ‖f‖ * x)
        (ρ.integral_fst (hh.sub hg).norm.aestronglyMeasurable)

/-- Weak continuity on the fixed-marginal space for every integrable time
weight. The weight need not be continuous and need not vanish at endpoints. -/
theorem continuous_weighted_integral (f : (τ × U) →ᵇ ℝ)
    {h : τ → ℝ} (hh : Integrable h ν.toMeasure) :
    Continuous (fun ρ : RelaxedControl τ U ν => ∫ z, h z.1 * f z ∂ρ.measure) := by
  apply continuous_of_uniform_approx_of_continuous
  intro W hW
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_uniformity_dist.mp hW
  have hd : 0 < ‖f‖ + 1 := by positivity
  obtain ⟨g, happrox, hg⟩ := hh.exists_boundedContinuous_integral_sub_le (div_pos hε hd)
  refine ⟨fun ρ => ∫ z, g z.1 * f z ∂ρ.measure, ?_, ?_⟩
  · let gf : (τ × U) →ᵇ ℝ := (g.compContinuous ⟨Prod.fst, continuous_fst⟩) * f
    exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction gf).comp
      continuous_subtype_val
  · intro ρ
    apply hεW
    rw [dist_eq_norm]
    calc
      ‖(∫ z, h z.1 * f z ∂ρ.measure) - (∫ z, g z.1 * f z ∂ρ.measure)‖ ≤
          ‖f‖ * ∫ t, ‖h t - g t‖ ∂ν := ρ.norm_weighted_integral_sub_le f hh hg
      _ ≤ ‖f‖ * (ε / (‖f‖ + 1)) := mul_le_mul_of_nonneg_left happrox (norm_nonneg _)
      _ < ε := by
        calc
          ‖f‖ * (ε / (‖f‖ + 1)) < (‖f‖ + 1) * (ε / (‖f‖ + 1)) :=
            mul_lt_mul_of_pos_right (by linarith) (div_pos hε hd)
          _ = ε := by field_simp

/-- Consequently every measurable time restriction is continuous on relaxed
controls. The common marginal, rather than an unjustified application of weak
convergence to an indicator, is essential here. -/
theorem continuous_setIntegral (f : (τ × U) →ᵇ ℝ) {s : Set τ} (hs : MeasurableSet s) :
    Continuous (fun ρ : RelaxedControl τ U ν => ∫ z in s ×ˢ univ, f z ∂ρ.measure) := by
  have h := continuous_weighted_integral (ν := ν) f ((integrable_const (1 : ℝ)).indicator hs)
  convert h using 1
  funext ρ
  rw [← integral_indicator (hs.prod MeasurableSet.univ)]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z.1 ∈ s <;> simp [hz]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [CompactSpace τ] in
/-- Vector-valued weighted integrability, derived from the common marginal
and the boundedness of the continuous vector field. -/
theorem integrable_weighted_smul (ρ : RelaxedControl τ U ν)
    (f : (τ × U) →ᵇ E) {h : τ → ℝ} (hh : Integrable h ν.toMeasure) :
    Integrable (fun z => h z.1 • f z) ρ.measure :=
  (ρ.measurePreserving_fst.integrable_comp_of_integrable hh).smul_bdd ‖f‖
    f.continuous.aestronglyMeasurable (Eventually.of_forall f.norm_coe_le_norm)

/-- The vector-valued form of weighted weak continuity in finite-dimensional
state spaces. Scalar coordinates commute with the Bochner integral. -/
theorem continuous_weighted_smul_integral (f : (τ × U) →ᵇ E)
    {h : τ → ℝ} (hh : Integrable h ν.toMeasure) :
    Continuous (fun ρ : RelaxedControl τ U ν => ∫ z, h z.1 • f z ∂ρ.measure) := by
  let e := (Module.finBasis ℝ E).equivFunL
  have hc : Continuous (fun ρ : RelaxedControl τ U ν =>
      e (∫ z, h z.1 • f z ∂ρ.measure)) := by
    apply continuous_pi
    intro i
    let q : E →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
    let g : (τ × U) →ᵇ ℝ := BoundedContinuousFunction.comp q q.lipschitzWith f
    have hg := continuous_weighted_integral (ν := ν) g hh
    convert hg using 1
    funext ρ
    have hi := (q.integral_comp_comm (ρ.integrable_weighted_smul f hh)).symm
    simpa [q, g, map_smul, smul_eq_mul] using hi
  simpa only [Function.comp_def, e.symm_apply_apply] using e.symm.continuous.comp hc

omit [CompactSpace τ] in
/-- Changing the integrand has a uniformly bounded effect, independent of the
relaxed control. This permits the state trajectory and control measure to
vary simultaneously. -/
theorem norm_weighted_smul_integral_sub_le (ρ : RelaxedControl τ U ν)
    (f g : (τ × U) →ᵇ E) {h : τ → ℝ} (hh : Integrable h ν.toMeasure) :
    ‖(∫ z, h z.1 • f z ∂ρ.measure) - (∫ z, h z.1 • g z ∂ρ.measure)‖ ≤
      (∫ t, ‖h t‖ ∂ν) * ‖f - g‖ := by
  rw [← integral_sub (ρ.integrable_weighted_smul f hh) (ρ.integrable_weighted_smul g hh)]
  calc
    ‖∫ z, h z.1 • f z - h z.1 • g z ∂ρ.measure‖ ≤
        ∫ z, ‖h z.1‖ * ‖f - g‖ ∂ρ.measure := by
      apply norm_integral_le_of_norm_le
        ((ρ.measurePreserving_fst.integrable_comp_of_integrable hh.norm).mul_const ‖f - g‖)
      filter_upwards with z
      rw [← smul_sub, norm_smul]
      exact mul_le_mul_of_nonneg_left ((f - g).norm_coe_le_norm z) (norm_nonneg _)
    _ = (∫ t, ‖h t‖ ∂ν) * ‖f - g‖ := by
      rw [integral_mul_const]
      exact congrArg (fun x : ℝ => x * ‖f - g‖) (ρ.integral_fst hh.norm.aestronglyMeasurable)

/-- Joint continuity in the weak occupation measure and the uniformly
converging vector-valued integrand. -/
theorem continuous_weighted_smul_integral_joint {h : τ → ℝ} (hh : Integrable h ν.toMeasure) :
    Continuous (fun p : RelaxedControl τ U ν × ((τ × U) →ᵇ E) =>
      ∫ z, h z.1 • p.2 z ∂p.1.measure) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hn : Tendsto (fun r : RelaxedControl τ U ν × ((τ × U) →ᵇ E) =>
      (∫ t, ‖h t‖ ∂ν) * ‖r.2 - p.2‖) (𝓝 p) (𝓝 0) := by
    have hsub : Tendsto (fun r : RelaxedControl τ U ν × ((τ × U) →ᵇ E) => r.2 - p.2)
        (𝓝 p) (𝓝 (p.2 - p.2)) := (continuous_snd.tendsto p).sub tendsto_const_nhds
    simpa only [sub_self, norm_zero, mul_zero] using hsub.norm.const_mul (∫ t, ‖h t‖ ∂ν)
  have hd : Tendsto (fun r : RelaxedControl τ U ν × ((τ × U) →ᵇ E) =>
      (∫ z, h z.1 • r.2 z ∂r.1.measure) - (∫ z, h z.1 • p.2 z ∂r.1.measure))
      (𝓝 p) (𝓝 0) :=
    squeeze_zero_norm (fun r => r.1.norm_weighted_smul_integral_sub_le r.2 p.2 hh) hn
  have hc := (continuous_weighted_smul_integral p.2 hh).continuousAt.tendsto.comp
    (continuous_fst.tendsto p)
  change Tendsto _ (𝓝 p) (𝓝 _)
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hd.add hc

/-- Joint continuity for a genuine measurable time restriction. -/
theorem continuous_setIntegral_joint {s : Set τ} (hs : MeasurableSet s) :
    Continuous (fun p : RelaxedControl τ U ν × ((τ × U) →ᵇ E) =>
      ∫ z in s ×ˢ univ, p.2 z ∂p.1.measure) := by
  have hc := continuous_weighted_smul_integral_joint (U := U) (E := E) (ν := ν)
    ((integrable_const (1 : ℝ)).indicator hs)
  convert hc using 1
  funext p
  rw [← integral_indicator (hs.prod MeasurableSet.univ)]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z.1 ∈ s <;> simp [hz]

/-- Parameter-dependent continuous fields may be substituted directly into
occupation integrals. This is the closure tool for actual controlled
trajectories, where the parameter is a uniformly converging state path. -/
theorem continuous_setIntegral_param {P : Type*} [TopologicalSpace P]
    (F : P → (τ × U) → E) (hF : Continuous (Function.uncurry F))
    {s : Set τ} (hs : MeasurableSet s) :
    Continuous (fun p : P × RelaxedControl τ U ν =>
      ∫ z in s ×ˢ univ, F p.1 z ∂p.2.measure) := by
  let Fc : P → C(τ × U, E) := fun p => ⟨F p, hF.comp (continuous_const.prodMk continuous_id)⟩
  have hFc : Continuous Fc := ContinuousMap.continuous_of_continuous_uncurry Fc hF
  let Fb : P → ((τ × U) →ᵇ E) := fun p => BoundedContinuousFunction.mkOfCompact (Fc p)
  have hFb : Continuous Fb :=
    (ContinuousMap.isometryEquivBoundedOfCompact (τ × U) E).continuous.comp hFc
  exact (continuous_setIntegral_joint (ν := ν) (E := E) hs).comp
    (continuous_snd.prodMk (hFb.comp continuous_fst))

end OptimalControl.RelaxedControl
