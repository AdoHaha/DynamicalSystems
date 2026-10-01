/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Weighted dilations

This file records the weighted dilations used in the homogeneity theory of
A. Levant and L. Alelishvili, *Discontinuous Homogeneous Control*, Chapter 4 of
G. Bartolini, L. Fridman, A. Pisano and E. Usai (eds.), *Modern Sliding Mode Control
Theory: New Perspectives and Applications*, LNCIS 375, Springer 2008 (printed p. 72,
PDF p. 88). Given a weight vector `r : ι → ℝ`, the weighted dilation of exponent
`λ > 0` acts on `x : ι → ℝ` coordinatewise by `x i ↦ λ ^ (r i) * x i`.

These are new root-namespace names for the book's `d_λ`; they are deliberately
*not* Mathlib's `Dilation`, which scales a metric by a constant ratio and is an
unrelated notion.

## Main definitions

* `weightedDilation`: the weighted dilation `d_λ x = fun i ↦ λ ^ (r i) * x i`.

## Main results

* `weightedDilation_one`: `d_1 = id`.
* `weightedDilation_mul`: `d_{λμ} = d_λ ∘ d_μ` for `λ, μ > 0`.
* `weightedDilation_add`: `d_λ` is additive.
* `weightedDilation_smul`: `d_λ` is homogeneous over scalar multiplication.
-/

@[expose] public section

variable {ι : Type*}

/-- The **weighted dilation** of exponent `λ` with weights `r`, acting on
`x : ι → ℝ` coordinatewise by `(d_λ x) i = λ ^ (r i) * x i`. -/
noncomputable def weightedDilation (r : ι → ℝ) (l : ℝ) : (ι → ℝ) → (ι → ℝ) :=
  fun x i ↦ l ^ (r i) * x i

/-- The weighted dilation of exponent `1` is the identity. -/
theorem weightedDilation_one (r : ι → ℝ) : weightedDilation r 1 = id := by
  funext x i
  simp only [weightedDilation]
  rw [Real.one_rpow, one_mul]
  rfl

/-- Weighted dilations compose multiplicatively: `d_{λμ} = d_λ ∘ d_μ` for
`λ, μ > 0`. -/
theorem weightedDilation_mul (r : ι → ℝ) {l μ : ℝ} (hl : 0 < l) (hμ : 0 < μ)
    (x : ι → ℝ) :
    weightedDilation r (l * μ) x = weightedDilation r l (weightedDilation r μ x) := by
  funext i
  simp only [weightedDilation]
  rw [Real.mul_rpow (le_of_lt hl) (le_of_lt hμ)]
  ring

/-- Weighted dilations distribute over addition. -/
theorem weightedDilation_add (r : ι → ℝ) (l : ℝ) (x y : ι → ℝ) :
    weightedDilation r l (x + y) = weightedDilation r l x + weightedDilation r l y := by
  funext i
  simp only [weightedDilation, Pi.add_apply]
  ring

/-- Weighted dilations commute with scalar multiplication. -/
theorem weightedDilation_smul (r : ι → ℝ) (l c : ℝ) (x : ι → ℝ) :
    weightedDilation r l (c • x) = c • weightedDilation r l x := by
  funext i
  simp only [weightedDilation, Pi.smul_apply, smul_eq_mul]
  ring
