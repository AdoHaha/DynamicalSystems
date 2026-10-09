/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Extending a small-set estimate from a generating semiring

Approximate a measurable set in the *sum* of two finite measures. This controls
both the size of the approximating set and the error in the quantity being
estimated. In a family of measures the approximant may depend on the member;
the modulus in the resulting estimate does not acquire such a dependence.
-/

@[expose] public section

open Set MeasurableSpace MeasureTheory
open scoped ENNReal symmDiff

namespace DynamicalSystems.MeasureContinuity

/-- A uniform small-set estimate on finite unions from a generating semiring
extends to measurable sets. The common modulus is halved and the bound doubled;
no uniform choice of approximating sets is required. -/
theorem measure_le_of_small_on_semiring
    {α : Type*} [mα : MeasurableSpace α] {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {C : Set (Set α)}
    (hC : IsSetSemiring C)
    (hcover : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ (μ + ν) (⋃₀ D)ᶜ = 0)
    (hgen : mα = generateFrom C) {ε δ : ℝ≥0∞} (hε : 0 < ε) (hδ : 0 < δ)
    (hbound : ∀ t ∈ supClosure C, μ t < δ → ν t ≤ ε)
    {s : Set α} (hs : MeasurableSet s) (hsmall : μ s < δ / 2) :
    ν s ≤ ε + ε := by
  have hhalf : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨t, htC, ht⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
    (μ := μ + ν) hC hcover hgen hs (lt_min hhalf hε)
  have hμ : μ (t ∆ s) < δ / 2 := by
    have H : μ (t ∆ s) ≤ (μ + ν) (t ∆ s) := by simp [Measure.add_apply]
    exact (H.trans_lt ht).trans_le (min_le_left _ _)
  have hν : ν (t ∆ s) < ε := by
    have H : ν (t ∆ s) ≤ (μ + ν) (t ∆ s) := by simp [Measure.add_apply]
    exact (H.trans_lt ht).trans_le (min_le_right _ _)
  have hμt : μ t < δ := by
    calc
      μ t ≤ μ (s ∪ (t ∆ s)) := measure_mono (by
        intro x hx
        by_cases hxs : x ∈ s
        · exact Or.inl hxs
        · exact Or.inr (Or.inl ⟨hx, hxs⟩))
      _ ≤ μ s + μ (t ∆ s) := measure_union_le _ _
      _ < δ / 2 + δ / 2 := ENNReal.add_lt_add hsmall hμ
      _ = δ := ENNReal.add_halves δ
  calc
    ν s ≤ ν (t ∪ (t ∆ s)) := measure_mono (by
      intro x hx
      by_cases hxt : x ∈ t
      · exact Or.inl hxt
      · exact Or.inr (Or.inr ⟨hx, hxt⟩))
    _ ≤ ν t + ν (t ∆ s) := measure_union_le _ _
    _ ≤ ε + ε := add_le_add (hbound t htC hμt) hν.le

end DynamicalSystems.MeasureContinuity
