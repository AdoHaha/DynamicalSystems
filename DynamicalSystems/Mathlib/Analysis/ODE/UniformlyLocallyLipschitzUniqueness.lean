/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.UniformlyLocallyLipschitz
public import Mathlib.Topology.Connected.Clopen

/-! # Local Lipschitz uniqueness on intervals -/

@[expose] public noncomputable section

open Set Filter Topology Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E}

/-- Local Lipschitz uniqueness on an open time interval. -/
theorem IsIntegralCurveOn.eqOn_Ioo_of_uniformlyLocallyLipschitz
    (hf : UniformlyLocallyLipschitz f) {α β : ℝ → E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (hα : IsIntegralCurveOn α f (Ioo a b))
    (hβ : IsIntegralCurveOn β f (Ioo a b)) (heq : α t₀ = β t₀) :
    EqOn α β (Ioo a b) := by
  let : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  let S : Set (Ioo a b) := {t | α t = β t}
  have hclosed : IsClosed S :=
    isClosed_eq hα.continuousOn.domRestrict hβ.continuousOn.domRestrict
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t (ht : α t = β t)
    obtain ⟨K, U, hU, hfK⟩ := hf t (α t)
    have hαat : IsIntegralCurveAt α f t := by
      filter_upwards [isOpen_Ioo.mem_nhds t.property] with s hs
      exact (hα s hs).hasDerivAt (isOpen_Ioo.mem_nhds hs)
    have hβat : IsIntegralCurveAt β f t := by
      filter_upwards [isOpen_Ioo.mem_nhds t.property] with s hs
      exact (hβ s hs).hasDerivAt (isOpen_Ioo.mem_nhds hs)
    have hαU : ∀ᶠ s in 𝓝 (t : ℝ), α s ∈ U :=
      ((hα t t.property).hasDerivAt (isOpen_Ioo.mem_nhds t.property)).continuousAt.eventually_mem hU
    have hβU : ∀ᶠ s in 𝓝 (t : ℝ), β s ∈ U := by
      have hU' : U ∈ 𝓝 (β t) := ht ▸ hU
      exact ((hβ t t.property).hasDerivAt
        (isOpen_Ioo.mem_nhds t.property)).continuousAt.eventually_mem hU'
    have hloc := hαat.eventuallyEq hfK hαU hβat hβU ht
    exact continuous_subtype_val.continuousAt.eventually hloc
  have hS : S = univ := (IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨t₀, ht₀⟩, heq⟩)
  intro t ht
  have : (⟨t, ht⟩ : Ioo a b) ∈ S := hS ▸ mem_univ _
  exact this
