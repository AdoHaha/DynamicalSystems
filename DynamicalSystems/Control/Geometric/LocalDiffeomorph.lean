/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! # Differentiable local charts from an invertible strict derivative

Strict differentiability at a point controls all nearby difference quotients. If ordinary
derivatives exist throughout a neighborhood, their values therefore converge to the strict
derivative at that point. An invertible strict derivative consequently gives invertible ordinary
derivatives throughout a smaller neighborhood. The inverse function theorem then supplies a chart
whose forward and inverse maps are differentiable on their respective open domains.

These results do not assert continuity of the derivative away from the distinguished point.
-/

@[expose] public section

open Set Filter
open scoped Topology NNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F} {a : E}

/-- Nearby ordinary derivatives converge to the strict derivative at the base point, provided
that the function is differentiable throughout a neighborhood. -/
theorem HasStrictFDerivAt.tendsto_fderiv_of_eventually_differentiableAt
    {A : E →L[𝕜] F} (hf : HasStrictFDerivAt f A a)
    (hdiff : ∀ᶠ x in 𝓝 a, DifferentiableAt 𝕜 f x) :
    Tendsto (fderiv 𝕜 f) (𝓝 a) (𝓝 A) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  let c : ℝ≥0 := ⟨ε / 2, (half_pos hε).le⟩
  obtain ⟨s, hs, happ⟩ := hf.approximates_deriv_on_nhds
    (c := c) (Or.inr (show 0 < c from half_pos hε))
  filter_upwards [eventually_mem_nhds_iff.mpr hs, hdiff] with x hx hdx
  have hbound := (hdx.hasFDerivAt.sub (A.hasFDerivAt)).le_of_lipschitzOn
    hx happ.lipschitzOnWith
  rw [dist_eq_norm]
  exact hbound.trans_lt (half_lt_self hε)

/-- Under neighborhood differentiability, an invertible strict derivative yields invertible
ordinary derivatives throughout a smaller neighborhood. -/
theorem HasStrictFDerivAt.eventually_isInvertible_fderiv_of_eventually_differentiableAt
    [CompleteSpace E] {A : E ≃L[𝕜] F} (hf : HasStrictFDerivAt f (A : E →L[𝕜] F) a)
    (hdiff : ∀ᶠ x in 𝓝 a, DifferentiableAt 𝕜 f x) :
    ∀ᶠ x in 𝓝 a, (fderiv 𝕜 f x).IsInvertible :=
  (hf.tendsto_fderiv_of_eventually_differentiableAt hdiff)
    ContinuousLinearMap.isInvertible_equiv.eventually_nhds

/-- Restrict the inverse-function chart to any prescribed neighborhood so that both directions
are differentiable everywhere on their open domains. The final clause gives the inverse derivative
explicitly; continuity of derivatives away from the base point is not required. -/
theorem HasStrictFDerivAt.exists_local_differentiable_chart
    [CompleteSpace E] {A : E ≃L[𝕜] F} (hf : HasStrictFDerivAt f (A : E →L[𝕜] F) a)
    (hdiff : ∀ᶠ x in 𝓝 a, DifferentiableAt 𝕜 f x)
    {U : Set E} (hU : U ∈ 𝓝 a) :
    ∃ Φ : OpenPartialHomeomorph E F,
      (Φ : E → F) = f ∧ a ∈ Φ.source ∧ Φ.source ⊆ U ∧
      (∀ x ∈ Φ.source, DifferentiableAt 𝕜 Φ x) ∧
      (∀ x ∈ Φ.source, (fderiv 𝕜 Φ x).IsInvertible) ∧
      ∀ y ∈ Φ.target,
        HasFDerivAt Φ.symm (fderiv 𝕜 Φ (Φ.symm y)).inverse y := by
  have hinv := hf.eventually_isInvertible_fderiv_of_eventually_differentiableAt hdiff
  obtain ⟨V, hVsub, hVopen, haV⟩ := mem_nhds_iff.mp (inter_mem hU (hdiff.and hinv))
  let Φ := (hf.toOpenPartialHomeomorph f).restrOpen V hVopen
  have hcoe : (Φ : E → F) = f := rfl
  have hgood (x : E) (hx : x ∈ Φ.source) :
      x ∈ U ∧ DifferentiableAt 𝕜 f x ∧ (fderiv 𝕜 f x).IsInvertible :=
    hVsub hx.2
  refine ⟨Φ, hcoe, ⟨hf.mem_toOpenPartialHomeomorph_source, haV⟩,
    fun x hx => (hgood x hx).1,
    fun x hx => (hgood x hx).2.1,
    fun x hx => (hgood x hx).2.2, ?_⟩
  intro y hy
  obtain ⟨B, hB⟩ := (hgood (Φ.symm y) (Φ.map_target hy)).2.2
  have hder : HasFDerivAt Φ (B : E →L[𝕜] F) (Φ.symm y) := by
    rw [hB]
    exact (hgood (Φ.symm y) (Φ.map_target hy)).2.1.hasFDerivAt
  have hinverse := Φ.hasFDerivAt_symm hy hder
  simpa only [hcoe, ← hB, ContinuousLinearMap.inverse_equiv] using hinverse

end
