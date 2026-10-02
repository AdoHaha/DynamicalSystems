/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.Basic

/-! # The convex subdifferential

For a finite-valued function `F : E → ℝ` on a real normed space and a point `x`,
the **convex subdifferential** is the set of continuous linear functionals `x*`
that support `F` from below at `x`:

`subdifferential F x = {x* | ∀ y, F x + x* (y - x) ≤ F y}`.

The subdifferential is a closed convex subset of the dual space `E →L[ℝ] ℝ`
(restricted to supporting functionals, it is the set of slopes of affine
minorants of `F` that are exact at `x`). Its elements are the subgradients of
convex analysis: `0` is a subgradient exactly at global minimizers, and a
Fréchet derivative of a convex function is always a subgradient.

## Main definitions

* `subdifferential F x`: the convex subdifferential of `F` at `x`.

## Main statements

* `subdifferential_isClosed`: the subdifferential is closed.
* `subdifferential_convex`: the subdifferential is convex.
* `zero_mem_subdifferential_iff_isMinOn`: `0 ∈ ∂F x` if and only if `x` is a
  global minimizer of `F`.
* `subdifferential_of_hasFDerivAt`: a Fréchet derivative of a convex `F` at `x`
  is a subgradient of `F` at `x`. Convexity is essential: for a merely
  differentiable function the tangent line need not lie below the graph (e.g.
  `F y = -y²` at `x = 0`), so the statement carries the true minimal hypothesis
  `ConvexOn ℝ Set.univ F`.
-/

@[expose] public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **convex subdifferential** of `F : E → ℝ` at `x : E`, consisting of the
continuous linear functionals `x*` such that the affine function
`y ↦ F x + x* (y - x)` is a minorant of `F`. -/
def subdifferential (F : E → ℝ) (x : E) : Set (E →L[ℝ] ℝ) :=
  {xStar | ∀ y : E, F x + xStar (y - x) ≤ F y}

/-- The subdifferential `∂F x` is closed: it is the intersection over `y` of the
closed half-spaces `{x* | F x + x* (y - x) ≤ F y}` cut out by the continuous
evaluation functionals. -/
theorem subdifferential_isClosed (F : E → ℝ) (x : E) : IsClosed (subdifferential F x) := by
  rw [subdifferential, Set.ofPred_forall]
  apply isClosed_iInter
  intro y
  exact isClosed_le (continuous_const.add (ContinuousLinearMap.apply ℝ ℝ (y - x)).continuous)
    continuous_const

/-- The subdifferential `∂F x` is convex: it is an intersection of half-spaces, and
the supporting inequality is preserved by convex combinations of subgradients. -/
theorem subdifferential_convex (F : E → ℝ) (x : E) : Convex ℝ (subdifferential F x) := by
  intro x₁ h₁ x₂ h₂ a b ha hb hab y
  have hx₁ := h₁ y
  have hx₂ := h₂ y
  have happ : (a • x₁ + b • x₂) (y - x) = a * x₁ (y - x) + b * x₂ (y - x) := by
    simp only [add_apply, smul_apply, smul_eq_mul]
  rw [happ]
  calc F x + (a * x₁ (y - x) + b * x₂ (y - x))
      = (a * F x + b * F x) + (a * x₁ (y - x) + b * x₂ (y - x)) := by
        rw [show a * F x + b * F x = F x by rw [← add_mul, hab, one_mul]]
    _ = a * (F x + x₁ (y - x)) + b * (F x + x₂ (y - x)) := by ring
    _ ≤ a * F y + b * F y :=
        add_le_add (mul_le_mul_of_nonneg_left hx₁ ha) (mul_le_mul_of_nonneg_left hx₂ hb)
    _ = F y := by rw [← add_mul, hab, one_mul]

/-- `0` belongs to the subdifferential of `F` at `x` if and only if `x` is a global
minimizer of `F`. -/
theorem zero_mem_subdifferential_iff_isMinOn (F : E → ℝ) (x : E) :
    (0 : E →L[ℝ] ℝ) ∈ subdifferential F x ↔ IsMinOn F Set.univ x := by
  simp only [subdifferential, Set.mem_ofPred_eq, zero_apply, add_zero, isMinOn_iff,
    Set.mem_univ, true_implies]

/-- A Fréchet derivative of a convex function is a subgradient. Convexity is
required: it is exactly the condition that the tangent affine function lies below
the graph of `F`. -/
theorem subdifferential_of_hasFDerivAt {F : E → ℝ} {x : E} {F' : E →L[ℝ] ℝ}
    (hF : ConvexOn ℝ Set.univ F) (h : HasFDerivAt F F' x) : F' ∈ subdifferential F x := by
  intro y
  let γ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let g : ℝ → ℝ := F ∘ ⇑γ
  have hg : ConvexOn ℝ Set.univ g := by
    simpa [g, Set.preimage_univ] using hF.comp_affineMap γ
  have hlin : HasDerivAt (⇑γ) (y - x) 0 := by
    simpa [γ] using (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
  have hg' : HasDerivAt g (F' (y - x)) 0 := by
    have h0 : x = γ 0 := by
      simp [γ, AffineMap.lineMap_apply_module]
    exact h.comp_hasDerivAt_of_eq (0 : ℝ) hlin h0
  have hslope := hg.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (zero_lt_one : (0 : ℝ) < 1) hg'
  have hg0 : g 0 = F x := by simp [g, γ, AffineMap.lineMap_apply_module]
  have hg1 : g 1 = F y := by simp [g, γ, AffineMap.lineMap_apply_module]
  rw [slope_def_field, hg0, hg1] at hslope
  linarith
