/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Tactic.Linarith

/-!
# Separation from a negative halfspace

Abstract separation of a convex set from the strict negative halfspace of a
continuous linear functional: the separating functional is a positive multiple
of that functional, and can be normalized to evaluate to one on a fixed point.
No control-theoretic structure appears in the statements.
-/

@[expose] public section

open Set


section AbstractSeparation

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- A linear functional strictly negative on the entire negative halfspace of `c`
is a positive multiple of `c`, provided `c e = 1`.  This algebraic lemma is the
normality step after geometric separation. -/
theorem positive_multiple_of_negative_halfspace
    (c q : E →L[ℝ] ℝ) (e : E) (he : c e = 1)
    (hnegative : ∀ y, c y < 0 → q y < 0) :
    0 < q e ∧ q = (q e) • c := by
  have hqe : 0 < q e := by
    have hn := hnegative (-e) (by simp [he])
    simp only [map_neg] at hn
    linarith
  have hker : ∀ y, c y = 0 → q y = 0 := by
    intro y hy
    by_contra hqy
    have hd : c (-e + ((q e + 1) / q y) • y) < 0 := by
      simp [map_add, map_smul, he, hy]
    have hn := hnegative (-e + ((q e + 1) / q y) • y) hd
    simp only [map_add, map_neg, map_smul, smul_eq_mul] at hn
    have hcancel : ((q e + 1) / q y) * q y = q e + 1 :=
      div_mul_cancel₀ _ hqy
    linarith
  refine ⟨hqe, ?_⟩
  ext y
  have hk := hker (y - (c y) • e) (by simp [map_sub, map_smul, he])
  simp only [map_sub, map_smul, smul_eq_mul] at hk
  simp only [smul_apply, smul_eq_mul]
  nlinarith

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Genuine geometric Hahn–Banach extraction.  The functional `q` is obtained from
Mathlib's separation theorem.  Its coefficient along `e` is strictly positive, and
it is nonnegative on the variation set.

Only convexity and membership of zero are required; callers may use any cone of
attainable first-order endpoint variations.  The disjointness assumption is the
endpoint-expansion/optimality obligation, stated in a form that does not mention a
Hamiltonian or an already selected multiplier. -/
theorem _root_.exists_positive_multiple_separating_negative_halfspace
    (c : E →L[ℝ] ℝ) (e : E) (he : c e = 1)
    (C : Set E) (hconvex : Convex ℝ C) (hzero : (0 : E) ∈ C)
    (hdisjoint : Disjoint {y | c y < 0} C) :
    ∃ q : E →L[ℝ] ℝ,
      q ≠ 0 ∧ 0 < q e ∧ (∀ y ∈ C, 0 ≤ q y) ∧ q = (q e) • c := by
  have hopen : IsOpen {y : E | c y < 0} :=
    isOpen_lt c.continuous continuous_const
  have hhalfspace : Convex ℝ {y : E | c y < 0} :=
    (convex_Iio (0 : ℝ)).linear_preimage c.toLinearMap
  obtain ⟨q, u, hdescent, hvariation⟩ :=
    geometric_hahn_banach_open hhalfspace hopen hconvex hdisjoint
  have hu : u ≤ 0 := by simpa using hvariation 0 hzero
  have hnegative : ∀ y, c y < 0 → q y < 0 :=
    fun y hy => (hdescent y hy).trans_le hu
  obtain ⟨hqe, hmultiple⟩ :=
    positive_multiple_of_negative_halfspace c q e he hnegative
  have hc : ∀ y ∈ C, 0 ≤ c y := by
    intro y hy
    by_contra h
    exact (Set.disjoint_left.1 hdisjoint) (not_le.1 h) hy
  refine ⟨q, ?_, hqe, ?_, hmultiple⟩
  · intro hqzero
    have : q e = 0 := by simp [hqzero]
    linarith
  · intro y hy
    rw [hmultiple]
    simp only [smul_apply, smul_eq_mul]
    exact mul_nonneg hqe.le (hc y hy)

/-- The multiplier extracted by Hahn–Banach can be normalized to evaluate to one on
`e`.  The normalized multiplier equals the terminal differential. -/
theorem _root_.exists_normalized_positive_multiple_separating_negative_halfspace
    (c : E →L[ℝ] ℝ) (e : E) (he : c e = 1)
    (C : Set E) (hconvex : Convex ℝ C) (hzero : (0 : E) ∈ C)
    (hdisjoint : Disjoint {y | c y < 0} C) :
    ∃ (q : E →L[ℝ] ℝ) (α : ℝ),
      q ≠ 0 ∧ 0 < α ∧ (∀ y ∈ C, 0 ≤ q y) ∧ q e = α ∧ α⁻¹ • q = c := by
  obtain ⟨q, hqzero, hqe, hnonneg, hmultiple⟩ :=
    _root_.exists_positive_multiple_separating_negative_halfspace c e he C hconvex hzero hdisjoint
  refine ⟨q, q e, hqzero, hqe, hnonneg, rfl, ?_⟩
  calc
    (q e)⁻¹ • q = (q e)⁻¹ • ((q e) • c) :=
      congrArg (fun z : E →L[ℝ] ℝ => (q e)⁻¹ • z) hmultiple
    _ = c := inv_smul_smul₀ (ne_of_gt hqe) c

end AbstractSeparation
