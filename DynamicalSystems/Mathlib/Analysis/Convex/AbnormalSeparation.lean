/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Supporting covectors without an interior qualification

In finite dimension a convex set containing zero has a nonzero supporting covector at zero
whenever zero is not an interior point. The empty-interior case is handled by an annihilator
of its proper linear span. This case is essential for abnormal endpoint multipliers.
-/

@[expose] public section

open Set

/-- A nonzero continuous supporting covector exists even when the convex set has empty
interior. The sign is chosen to give nonnegative values on the set. -/
theorem exists_nonzero_supporting_covector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hC : Convex ℝ C) (hzero : (0 : E) ∈ C)
    (hboundary : (0 : E) ∉ interior C) :
    ∃ q : E →L[ℝ] ℝ, q ≠ 0 ∧ ∀ x ∈ C, 0 ≤ q x := by
  classical
  by_cases hint : (interior C).Nonempty
  · obtain ⟨q, hq, hs⟩ :=
      geometric_hahn_banach_of_nonempty_interior_point hC hboundary hint
    refine ⟨-q, neg_ne_zero.mpr hq, ?_⟩
    intro x hx
    change 0 ≤ -(q x)
    exact neg_nonneg.mpr (by simpa using hs x hx)
  · have hspan : Submodule.span ℝ C ≠ ⊤ := by
      intro htop
      have haff : affineSpan ℝ C = ⊤ := by
        apply SetLike.coe_injective
        rw [← insert_eq_of_mem hzero, affineSpan_insert_zero, htop]
        rfl
      exact hint (hC.interior_nonempty_iff_affineSpan_eq_top.mpr haff)
    obtain ⟨q, hq, hker⟩ :=
      (Submodule.span ℝ C).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hspan)
    refine ⟨q.toContinuousLinearMap, ?_, ?_⟩
    · intro hz
      apply hq
      exact LinearMap.toContinuousLinearMap.injective hz
    · intro x hx
      have hz : q x = 0 := hker (Submodule.subset_span hx)
      change 0 ≤ q x
      rw [hz]
