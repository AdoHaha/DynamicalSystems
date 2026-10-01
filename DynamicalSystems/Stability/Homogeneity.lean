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
* `IsHomogeneousFunction`: degree-`q` homogeneity of a scalar function.
* `IsHomogeneousVectorField`: degree-`q` homogeneity of a vector field.

## Main results

* `weightedDilation_one`: `d_1 = id`.
* `weightedDilation_mul`: `d_{λμ} = d_λ ∘ d_μ` for `λ, μ > 0`.
* `weightedDilation_add`: `d_λ` is additive.
* `weightedDilation_smul`: `d_λ` is homogeneous over scalar multiplication.
* `IsHomogeneousFunction.add`, `.const_mul`, `.mul`: the homogeneous scalar functions
  of a fixed degree (of degrees adding, for `.mul`) form a graded algebra.
* `IsHomogeneousVectorField.add`, `.const_smul`: homogeneous vector fields of a fixed
  degree form a module.
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

/-- A scalar function `g` is **homogeneous of degree `q`** with respect to the weights
`r` if `g (d_λ x) = λ ^ q * g x` for every `λ > 0`. -/
def IsHomogeneousFunction (g : (ι → ℝ) → ℝ) (r : ι → ℝ) (q : ℝ) : Prop :=
  ∀ l, 0 < l → ∀ x, g (weightedDilation r l x) = l ^ q * g x

/-- A vector field `f` is **homogeneous of degree `q`** with respect to the weights `r`
if `f (d_λ x) = λ ^ q • d_λ (f x)` for every `λ > 0`. -/
def IsHomogeneousVectorField (f : (ι → ℝ) → (ι → ℝ)) (r : ι → ℝ) (q : ℝ) : Prop :=
  ∀ l, 0 < l → ∀ x, f (weightedDilation r l x) = l ^ q • weightedDilation r l (f x)

/-- The sum of two functions homogeneous of the same degree is homogeneous of that
degree. -/
theorem IsHomogeneousFunction.add {g h : (ι → ℝ) → ℝ} {r : ι → ℝ} {q : ℝ}
    (hg : IsHomogeneousFunction g r q) (hh : IsHomogeneousFunction h r q) :
    IsHomogeneousFunction (fun x ↦ g x + h x) r q := by
  intro l hl x
  change g (weightedDilation r l x) + h (weightedDilation r l x) = l ^ q * (g x + h x)
  rw [hg l hl x, hh l hl x]
  ring

/-- A constant multiple of a homogeneous function is homogeneous of the same degree. -/
theorem IsHomogeneousFunction.const_mul (c : ℝ) {g : (ι → ℝ) → ℝ} {r : ι → ℝ} {q : ℝ}
    (hg : IsHomogeneousFunction g r q) :
    IsHomogeneousFunction (fun x ↦ c * g x) r q := by
  intro l hl x
  change c * g (weightedDilation r l x) = l ^ q * (c * g x)
  rw [hg l hl x]
  ring

/-- The pointwise product of homogeneous functions of degrees `p` and `q` is homogeneous
of degree `p + q`. -/
theorem IsHomogeneousFunction.mul {g h : (ι → ℝ) → ℝ} {r : ι → ℝ} {p q : ℝ}
    (hg : IsHomogeneousFunction g r p) (hh : IsHomogeneousFunction h r q) :
    IsHomogeneousFunction (fun x ↦ g x * h x) r (p + q) := by
  intro l hl x
  change g (weightedDilation r l x) * h (weightedDilation r l x) = l ^ (p + q) * (g x * h x)
  rw [hg l hl x, hh l hl x, Real.rpow_add hl]
  ring

/-- The sum of two vector fields homogeneous of the same degree is homogeneous of that
degree. -/
theorem IsHomogeneousVectorField.add {f F : (ι → ℝ) → (ι → ℝ)} {r : ι → ℝ} {q : ℝ}
    (hf : IsHomogeneousVectorField f r q) (hF : IsHomogeneousVectorField F r q) :
    IsHomogeneousVectorField (fun x ↦ f x + F x) r q := by
  intro l hl x
  change f (weightedDilation r l x) + F (weightedDilation r l x)
    = l ^ q • weightedDilation r l (f x + F x)
  rw [hf l hl x, hF l hl x, weightedDilation_add, smul_add]

/-- A constant multiple of a homogeneous vector field is homogeneous of the same degree. -/
theorem IsHomogeneousVectorField.const_smul (c : ℝ) {f : (ι → ℝ) → (ι → ℝ)}
    {r : ι → ℝ} {q : ℝ} (hf : IsHomogeneousVectorField f r q) :
    IsHomogeneousVectorField (fun x ↦ c • f x) r q := by
  intro l hl x
  change c • f (weightedDilation r l x) = l ^ q • weightedDilation r l (c • f x)
  rw [hf l hl x, weightedDilation_smul, smul_comm]
