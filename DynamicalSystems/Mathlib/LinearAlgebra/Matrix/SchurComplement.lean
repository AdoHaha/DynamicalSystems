/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Strict positive-definite block Schur complement

This file proves the strict positive-definite Schur complement equivalence for 2×2 block matrices
over `ℝ`.

## Main results

* `Matrix.posDef_fromBlocks₂₂_iff`: `[A, B; Bᵀ, D]` is positive definite iff `D` and the Schur
  complement `A - B * ⅟D * Bᵀ` are positive definite, when `D` is invertible.
* `Matrix.posDef_fromBlocks₁₁_iff`: `[A, B; Bᵀ, D]` is positive definite iff `A` and the Schur
  complement `D - Bᵀ * ⅟A * B` are positive definite, when `A` is invertible.
-/

@[expose] public section

namespace Matrix

open scoped Matrix

variable {m n : Type*}

/-- A block-diagonal matrix `[A, 0; 0, D]` is positive definite if both diagonal blocks `A`
and `D` are positive definite. -/
theorem posDef_fromBlocks_zero [Finite m] [Finite n] (A : Matrix m m ℝ) (D : Matrix n n ℝ)
    (hA : A.PosDef) (hD : D.PosDef) :
    (fromBlocks A 0 0 D).PosDef := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx ↦ ?_⟩
  · exact IsHermitian.fromBlocks hA.1 conjTranspose_zero hD.1
  · have hx_split : x = (x ∘ Sum.inl) ⊕ᵥ (x ∘ Sum.inr) := (Sum.elim_comp_inl_inr x).symm
    have hx_ne : x ∘ Sum.inl ≠ 0 ∨ x ∘ Sum.inr ≠ 0 := by
      contrapose! hx
      ext i
      cases i with
      | inl i => exact congr_fun hx.1 i
      | inr i => exact congr_fun hx.2 i
    nth_rw 1 [hx_split]
    rw [fromBlocks_mulVec, zero_mulVec, zero_mulVec, add_zero, zero_add]
    rw [Function.star_sumElim]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    cases hx_ne with
    | inl h1 =>
      have p1 := hA.dotProduct_mulVec_pos h1
      have p2 : 0 ≤ star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) :=
        hD.posSemidef.dotProduct_mulVec_nonneg _
      exact add_pos_of_pos_of_nonneg p1 p2
    | inr h2 =>
      have p2 := hD.dotProduct_mulVec_pos h2
      have p1 : 0 ≤ star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) :=
        hA.posSemidef.dotProduct_mulVec_nonneg _
      exact add_pos_of_nonneg_of_pos p1 p2

/-- A block-diagonal matrix `[A, 0; 0, D]` is positive definite if and only if both diagonal
blocks `A` and `D` are positive definite. -/
theorem posDef_fromBlocks_zero_iff [Finite m] [Finite n] (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    (fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef := by
  refine ⟨fun h ↦ ?_, fun ⟨hA, hD⟩ ↦ posDef_fromBlocks_zero A D hA hD⟩
  have hA_sub : (fromBlocks A 0 0 D).submatrix Sum.inl Sum.inl = A := by
    ext i j; simp [fromBlocks_apply₁₁]
  have hD_sub : (fromBlocks A 0 0 D).submatrix Sum.inr Sum.inr = D := by
    ext i j; simp [fromBlocks_apply₂₂]
  exact ⟨hA_sub ▸ h.submatrix Sum.inl_injective, hD_sub ▸ h.submatrix Sum.inr_injective⟩

/-- The strict positive definiteness of a block matrix `[A, B; Bᵀ, D]` with invertible
bottom-right block `D` is equivalent to that of the block-diagonal matrix
`[A - B * ⅟D * Bᵀ, 0; 0, D]` obtained by the LDU congruence that eliminates the off-diagonal
block. This is the congruence underlying `posDef_fromBlocks₂₂_iff`. -/
private theorem posDef_fromBlocks_congr₂₂ [Finite m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) [Invertible D] (hD : D.PosDef) :
    (fromBlocks A B Bᵀ D).PosDef ↔ (fromBlocks (A - B * ⅟D * Bᵀ) 0 0 D).PosDef := by
  have := Fintype.ofFinite m
  classical
  have hU : IsUnit (fromBlocks 1 (B * ⅟D) 0 1 : Matrix (m ⊕ n) (m ⊕ n) ℝ) := by
    rw [isUnit_fromBlocks_zero₂₁]
    exact ⟨isUnit_one, isUnit_one⟩
  have h_star : star (fromBlocks 1 (B * ⅟D) 0 1 : Matrix (m ⊕ n) (m ⊕ n) ℝ) =
      fromBlocks 1 0 (⅟D * Bᵀ) 1 := by
    rw [star_eq_conjTranspose, fromBlocks_conjTranspose]
    simp only [conjTranspose_one, conjTranspose_zero]
    congr 1
    rw [conjTranspose_mul, invOf_eq_nonsing_inv, conjTranspose_nonsing_inv, hD.isHermitian.eq,
      ← invOf_eq_nonsing_inv, conjTranspose_eq_transpose_of_trivial]
  have h_fac : fromBlocks 1 (B * ⅟D) 0 1 * fromBlocks (A - B * ⅟D * Bᵀ) 0 0 D *
      star (fromBlocks 1 (B * ⅟D) 0 1 : Matrix (m ⊕ n) (m ⊕ n) ℝ) = fromBlocks A B Bᵀ D := by
    rw [h_star, ← fromBlocks_eq_of_invertible₂₂]
  rw [← h_fac]
  exact IsUnit.posDef_star_right_conjugate_iff hU

/-- The strict positive definiteness of a block matrix `[A, B; Bᵀ, D]` with invertible
top-left block `A` is equivalent to that of the block-diagonal matrix
`[A, 0; 0, D - Bᵀ * ⅟A * B]` obtained by the LDU congruence that eliminates the off-diagonal
block. This is the congruence underlying `posDef_fromBlocks₁₁_iff`. -/
private theorem posDef_fromBlocks_congr₁₁ [Fintype m] [DecidableEq m] [Finite n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) [Invertible A] (hA : A.PosDef) :
    (fromBlocks A B Bᵀ D).PosDef ↔ (fromBlocks A 0 0 (D - Bᵀ * ⅟A * B)).PosDef := by
  have := Fintype.ofFinite n
  classical
  have hU : IsUnit (fromBlocks 1 0 (Bᵀ * ⅟A) 1 : Matrix (m ⊕ n) (m ⊕ n) ℝ) := by
    rw [isUnit_fromBlocks_zero₁₂]
    exact ⟨isUnit_one, isUnit_one⟩
  have h_star : star (fromBlocks 1 0 (Bᵀ * ⅟A) 1 : Matrix (m ⊕ n) (m ⊕ n) ℝ) =
      fromBlocks 1 (⅟A * B) 0 1 := by
    rw [star_eq_conjTranspose, fromBlocks_conjTranspose]
    simp only [conjTranspose_one, conjTranspose_zero]
    congr 1
    rw [conjTranspose_mul, invOf_eq_nonsing_inv, conjTranspose_nonsing_inv, hA.isHermitian.eq,
      ← invOf_eq_nonsing_inv, conjTranspose_eq_transpose_of_trivial, transpose_transpose]
  have h_fac : fromBlocks 1 0 (Bᵀ * ⅟A) 1 * fromBlocks A 0 0 (D - Bᵀ * ⅟A * B) *
      star (fromBlocks 1 0 (Bᵀ * ⅟A) 1 : Matrix (m ⊕ n) (m ⊕ n) ℝ) = fromBlocks A B Bᵀ D := by
    rw [h_star, ← fromBlocks_eq_of_invertible₁₁]
  rw [← h_fac]
  exact IsUnit.posDef_star_right_conjugate_iff hU

/-- A 2×2 block matrix `[A, B; Bᵀ, D]` with invertible bottom-right block `D` is positive
definite if and only if `D` is positive definite and the Schur complement `A - B * ⅟D * Bᵀ`
is positive definite. -/
theorem posDef_fromBlocks₂₂_iff [Finite m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) [Invertible D] :
    (fromBlocks A B Bᵀ D).PosDef ↔ D.PosDef ∧ (A - B * ⅟D * Bᵀ).PosDef := by
  have := Fintype.ofFinite m
  classical
  constructor
  · intro h
    have hD_sub : (fromBlocks A B Bᵀ D).submatrix Sum.inr Sum.inr = D := by
      ext i j; simp [fromBlocks_apply₂₂]
    have hD : D.PosDef := hD_sub ▸ h.submatrix Sum.inr_injective
    have h_block : (fromBlocks (A - B * ⅟D * Bᵀ) 0 0 D).PosDef :=
      (posDef_fromBlocks_congr₂₂ A B D hD).mp h
    rw [posDef_fromBlocks_zero_iff] at h_block
    exact ⟨hD, h_block.1⟩
  · rintro ⟨hD, hS⟩
    have h_block : (fromBlocks (A - B * ⅟D * Bᵀ) 0 0 D).PosDef :=
      (posDef_fromBlocks_zero_iff _ _).2 ⟨hS, hD⟩
    exact (posDef_fromBlocks_congr₂₂ A B D hD).mpr h_block

/-- A 2×2 block matrix `[A, B; Bᵀ, D]` with invertible top-left block `A` is positive
definite if and only if `A` is positive definite and the Schur complement `D - Bᵀ * ⅟A * B`
is positive definite. -/
theorem posDef_fromBlocks₁₁_iff [Fintype m] [DecidableEq m] [Finite n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) [Invertible A] :
    (fromBlocks A B Bᵀ D).PosDef ↔ A.PosDef ∧ (D - Bᵀ * ⅟A * B).PosDef := by
  have := Fintype.ofFinite n
  classical
  constructor
  · intro h
    have hA_sub : (fromBlocks A B Bᵀ D).submatrix Sum.inl Sum.inl = A := by
      ext i j; simp [fromBlocks_apply₁₁]
    have hA : A.PosDef := hA_sub ▸ h.submatrix Sum.inl_injective
    have h_block : (fromBlocks A 0 0 (D - Bᵀ * ⅟A * B)).PosDef :=
      (posDef_fromBlocks_congr₁₁ A B D hA).mp h
    rw [posDef_fromBlocks_zero_iff] at h_block
    exact ⟨hA, h_block.2⟩
  · rintro ⟨hA, hS⟩
    have h_block : (fromBlocks A 0 0 (D - Bᵀ * ⅟A * B)).PosDef :=
      (posDef_fromBlocks_zero_iff _ _).2 ⟨hA, hS⟩
    exact (posDef_fromBlocks_congr₁₁ A B D hA).mpr h_block

end Matrix

/-! The campaign gate refers to the two main results by their unqualified names, so expose them at
root level in addition to the `Matrix.`-qualified forms above (matching Mathlib's block API). -/
export Matrix (posDef_fromBlocks₂₂_iff posDef_fromBlocks₁₁_iff)
