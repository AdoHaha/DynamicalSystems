/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.EMetricSpace.BoundedVariation
/-! # Addition of functions of bounded variation -/
@[expose] public section

open Set

/-- The variation of a sum is bounded by the sum of the variations. -/
theorem eVariationOn_add_le {τ F : Type*} [LinearOrder τ] [NormedAddCommGroup F]
    (f g : τ → F) (s : Set τ) :
    eVariationOn (fun t ↦ f t + g t) s ≤ eVariationOn f s + eVariationOn g s := by
  unfold eVariationOn
  apply iSup_le
  intro p
  calc
    _ ≤ ∑ i ∈ Finset.range p.1,
        (edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) +
          edist (g (p.2.1 (i + 1))) (g (p.2.1 i))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))) +
        ∑ i ∈ Finset.range p.1, edist (g (p.2.1 (i + 1))) (g (p.2.1 i)) :=
      Finset.sum_add_distrib
    _ ≤ _ := add_le_add (le_iSup_of_le p le_rfl) (le_iSup_of_le p le_rfl)

/-- Sums of BV functions are BV, with no differentiability or absolute continuity premise. -/
theorem BoundedVariationOn.add {τ F : Type*} [LinearOrder τ] [NormedAddCommGroup F]
    {f g : τ → F} {s : Set τ} (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun t ↦ f t + g t) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (eVariationOn_add_le f g s)
