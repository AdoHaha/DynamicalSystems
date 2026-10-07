/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-!
# Differentiating affine variations with measurable reference paths

A jointly continuous spatial derivative is bounded on the compact state tube. This derives
the domination needed to differentiate an actual integral, even for merely measurable
reference paths and finite singular measures. No first-variation or domination certificate
is assumed.
-/

@[expose] public section

open Set MeasureTheory Metric Filter
open scoped Topology NNReal

namespace IntegralAffineVariation

variable {Ω W : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A jointly continuous integrand composed with a uniformly bounded measurable path is
integrable for any finite measure. The uniform scalar bound follows from compactness. -/
theorem integrable_continuous_of_bounded
    (g : Ω → W → ℝ) (hg : Continuous (fun p : Ω × W ↦ g p.1 p.2))
    (z : Ω → W) (hz : Measurable z) (R : ℝ≥0) (hzbound : ∀ s, ‖z s‖ ≤ R) :
    Integrable (fun s ↦ g s (z s)) μ := by
  let K : Set (Ω × W) := univ ×ˢ closedBall (0 : W) (R : ℝ)
  have hK : IsCompact K := isCompact_univ.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hK.bddAbove_image hg.norm.continuousOn
  have hm : Measurable (fun s ↦ g s (z s)) :=
    hg.measurable.comp (measurable_id.prodMk hz)
  apply (integrable_const M).mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro s
  exact hM ⟨(s, z s), ⟨mem_univ _, by simpa using hzbound s⟩, rfl⟩

/-- Actual differentiation under a finite measure of a spatially C¹ integrand along an
affine perturbation of bounded measurable paths. The derivative and its integrability are
conclusions. The dominating constant is derived by compactness of the state tube. -/
theorem hasDerivAt_integral_affine
    (g : Ω → W → ℝ) (D : Ω → W → W →L[ℝ] ℝ)
    (hg : Continuous (fun p : Ω × W ↦ g p.1 p.2))
    (hD : Continuous (fun p : Ω × W ↦ D p.1 p.2))
    (hderiv : ∀ s x, HasFDerivAt (g s) (D s x) x)
    (z d : Ω → W) (hz : Measurable z) (hd : Measurable d)
    (R : ℝ≥0) (hzbound : ∀ s, ‖z s‖ ≤ R) (hdbound : ∀ s, ‖d s‖ ≤ R)
    (hint : Integrable (fun s ↦ g s (z s)) μ) :
    Integrable (fun s ↦ D s (z s) (d s)) μ ∧
      HasDerivAt (fun θ : ℝ ↦ ∫ s, g s (z s + θ • d s) ∂μ)
        (∫ s, D s (z s) (d s) ∂μ) 0 := by
  let K : Set (Ω × W) := univ ×ˢ closedBall (0 : W) (2 * (R : ℝ))
  have hK : IsCompact K := isCompact_univ.prod (isCompact_closedBall _ _)
  obtain ⟨M₀, hM₀⟩ := hK.bddAbove_image hD.norm.continuousOn
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hDbound (s : Ω) (x : W) (hx : ‖x‖ ≤ 2 * (R : ℝ)) : ‖D s x‖ ≤ M :=
    (hM₀ ⟨(s, x), ⟨mem_univ _, by simpa using hx⟩, rfl⟩).trans (le_max_left _ _)
  let F : ℝ → Ω → ℝ := fun θ s ↦ g s (z s + θ • d s)
  let F' : ℝ → Ω → ℝ := fun θ s ↦ D s (z s + θ • d s) (d s)
  have hFmeas (θ : ℝ) : AEStronglyMeasurable (F θ) μ :=
    (hg.measurable.comp (measurable_id.prodMk (hz.add (hd.const_smul θ)))).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (F' 0) μ := by
    have heval : Continuous (fun p : (Ω × W) × W ↦ D p.1.1 p.1.2 p.2) :=
      (hD.comp continuous_fst).clm_apply continuous_snd
    have hm : Measurable (fun s ↦ D s (z s) (d s)) :=
      heval.measurable.comp ((measurable_id.prodMk hz).prodMk hd)
    simpa [F'] using hm.aestronglyMeasurable (μ := μ)
  have hbound : ∀ᵐ s ∂μ, ∀ θ ∈ ball (0 : ℝ) 1, ‖F' θ s‖ ≤ M * R := by
    apply Eventually.of_forall
    intro s θ hθ
    have hθnorm : ‖θ‖ < 1 := by simpa [mem_ball, dist_zero_right] using hθ
    have hstate : ‖z s + θ • d s‖ ≤ 2 * (R : ℝ) := by
      calc
        _ ≤ ‖z s‖ + ‖θ‖ * ‖d s‖ := by simpa [norm_smul] using norm_add_le (z s) (θ • d s)
        _ ≤ R + 1 * (R : ℝ) := add_le_add (hzbound s)
          (mul_le_mul hθnorm.le (hdbound s) (norm_nonneg _) (by positivity))
        _ = _ := by ring
    exact ((D s (z s + θ • d s)).le_opNorm (d s)).trans
      (mul_le_mul (hDbound s _ hstate) (hdbound s) (norm_nonneg _) hM)
  have hdiff : ∀ᵐ s ∂μ, ∀ θ ∈ ball (0 : ℝ) 1, HasDerivAt (fun θ ↦ F θ s) (F' θ s) θ := by
    apply Eventually.of_forall
    intro s θ _
    have ha : HasDerivAt (fun θ : ℝ ↦ z s + θ • d s) (d s) θ := by
      simpa using ((hasDerivAt_id θ).smul_const (d s)).const_add (z s)
    exact (hderiv s (z s + θ • d s)).comp_hasDerivAt θ ha
  have hzero : Integrable (F 0) μ := by simpa [F] using hint
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds (0 : ℝ) zero_lt_one) (Eventually.of_forall hFmeas) hzero hF'meas
    hbound (integrable_const (M * (R : ℝ))) hdiff
  simpa [F, F'] using hres

/-- First-variation differentiation derived entirely from primitive C¹ data and bounded
measurable paths. Nominal integrability is also derived from compactness. -/
theorem hasDerivAt_integral_affine_of_bounded
    (g : Ω → W → ℝ) (D : Ω → W → W →L[ℝ] ℝ)
    (hg : Continuous (fun p : Ω × W ↦ g p.1 p.2))
    (hD : Continuous (fun p : Ω × W ↦ D p.1 p.2))
    (hderiv : ∀ s x, HasFDerivAt (g s) (D s x) x)
    (z d : Ω → W) (hz : Measurable z) (hd : Measurable d)
    (R : ℝ≥0) (hzbound : ∀ s, ‖z s‖ ≤ R) (hdbound : ∀ s, ‖d s‖ ≤ R) :
    Integrable (fun s ↦ D s (z s) (d s)) μ ∧
      HasDerivAt (fun θ : ℝ ↦ ∫ s, g s (z s + θ • d s) ∂μ)
        (∫ s, D s (z s) (d s) ∂μ) 0 :=
  hasDerivAt_integral_affine g D hg hD hderiv z d hz hd R hzbound hdbound
    (integrable_continuous_of_bounded g hg z hz R hzbound)

end IntegralAffineVariation
