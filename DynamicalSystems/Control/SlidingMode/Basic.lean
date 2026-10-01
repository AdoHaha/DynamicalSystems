/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! # First-order sliding-mode foundations

This file records the first-order sliding-mode vocabulary of G. Bartolini,
L. Fridman, A. Pisano and E. Usai (eds.), *Modern Sliding Mode Control Theory:
New Perspectives and Applications*, LNCIS 375, Springer 2008. The setup is the
single-input affine system `x' = f x + u • g x` with scalar output `σ : E → ℝ`,
and the sliding manifold `{x | σ x = 0}` (Chapter 4, A. Levant and
L. Alelishvili, *Discontinuous Homogeneous Control*, Section 3, printed pp. 75–76:
the output `σ` is to be driven to zero and kept there). The equivalent control
`u_eq = -a / b` and the reduction `σ̇ = a + b u` on the manifold follow the
variable-structure control presentation of Chapter 14, Y. Pan and K. Furuta,
*Second-Order Sliding Sector for Variable Structure Control*, equation (19),
printed p. 103, where `u_eq(t) = -(SB)^{-1} S A x(t)` is the input making
`ṡ(x) = 0`.

The *sliding derivative* of `σ` along a field `F` is the Lie (orbital) derivative
`fderiv ℝ σ x (F x)`, i.e. the directional derivative of the output along `F`
evaluated at `x`. Since `fderiv ℝ σ x` is a continuous linear map unconditionally,
the linearity lemmas below hold with no differentiability hypothesis on `σ`.

## Main definitions

* `slidingManifold σ`: the zero level set `{x | σ x = 0}` of the output.
* `slidingDerivative σ F x`: the Lie derivative `fderiv ℝ σ x (F x)`.
* `equivalentControl σ f g x`: the equivalent control `-a(x) / b(x)`, with
  `a := slidingDerivative σ f x` and `b := slidingDerivative σ g x`.

## Main statements

* `slidingDerivative_add`, `slidingDerivative_smul`: linearity of `slidingDerivative`
  in the vector field.
* `slidingDerivative_affine`: the affine decomposition `σ̇ = a + b u`.
* `equivalentControl_spec`: the equivalent control zeroes the sliding derivative
  where `b ≠ 0`.
* `equivalentControl_unique`: the equivalent control is the unique such value.
* `slidingDerivative_equivalentControl_closedLoop`: the equivalent-control closed
  loop is tangent to the sliding manifold (`σ̇ = 0` where `b ≠ 0`).
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The sliding manifold of a scalar output `σ`: its zero level set. This is the
subset of state space on which the sliding variable vanishes. -/
def slidingManifold (σ : E → ℝ) : Set E := {x | σ x = 0}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Membership in the sliding manifold, in terms of the output (a `simp` lemma). -/
@[simp] theorem mem_slidingManifold {σ : E → ℝ} {x : E} :
    x ∈ slidingManifold σ ↔ σ x = 0 := Iff.rfl

/-- The Lie (orbital) derivative of a scalar output `σ` along the vector field `F`,
`σ̇ = dσ(x) · F(x)`. It is the directional derivative of `σ` along `F` at `x`. -/
noncomputable def slidingDerivative (σ : E → ℝ) (F : E → E) (x : E) : ℝ :=
  fderiv ℝ σ x (F x)

/-- `slidingDerivative` unfolds to the evaluation of `fderiv` on the field (a `simp`
lemma). -/
@[simp] theorem slidingDerivative_def (σ : E → ℝ) (F : E → E) (x : E) :
    slidingDerivative σ F x = fderiv ℝ σ x (F x) := rfl

/-- `slidingDerivative` is additive in the vector field: the Lie derivative along
`F + G` is the sum of the Lie derivatives along `F` and along `G`. -/
theorem slidingDerivative_add (σ : E → ℝ) (F G : E → E) (x : E) :
    slidingDerivative σ (fun y ↦ F y + G y) x =
      slidingDerivative σ F x + slidingDerivative σ G x := by
  simp only [slidingDerivative, map_add]

/-- `slidingDerivative` is homogeneous in the vector field: the Lie derivative along
`u • F` is `u` times the Lie derivative along `F`. -/
theorem slidingDerivative_smul (σ : E → ℝ) (F : E → E) (u : ℝ) (x : E) :
    slidingDerivative σ (fun y ↦ u • F y) x = u * slidingDerivative σ F x := by
  simp only [slidingDerivative, map_smul, smul_eq_mul]

/-- The affine decomposition of the sliding derivative for the single-input affine
system `x' = f x + u • g x`: `σ̇ = a(x) + b(x) u`, where `a = slidingDerivative σ f x`
and `b = slidingDerivative σ g x`. -/
theorem slidingDerivative_affine (σ : E → ℝ) (f g : E → E) (u : ℝ) (x : E) :
    slidingDerivative σ (fun y ↦ f y + u • g y) x =
      slidingDerivative σ f x + u * slidingDerivative σ g x := by
  simp only [slidingDerivative, map_add, map_smul, smul_eq_mul]

/-- The equivalent control `u_eq = -a / b`, where `a = slidingDerivative σ f x` and
`b = slidingDerivative σ g x`. It is the value of the control that makes the sliding
derivative `σ̇ = a + b u` vanish whenever `b ≠ 0` (equation (19) of Pan–Furuta,
printed p. 103, in the specialized scalar form). -/
noncomputable def equivalentControl (σ : E → ℝ) (f g : E → E) (x : E) : ℝ :=
  -slidingDerivative σ f x / slidingDerivative σ g x

/-- `equivalentControl` unfolds to `-a / b` (a `simp` lemma). -/
@[simp] theorem equivalentControl_def (σ : E → ℝ) (f g : E → E) (x : E) :
    equivalentControl σ f g x = -slidingDerivative σ f x / slidingDerivative σ g x :=
  rfl

/-- The defining property of the equivalent control: where `b = slidingDerivative σ g x`
is nonzero, `u_eq` makes the sliding derivative `a + b u` vanish, i.e. `σ̇ = 0`. -/
theorem equivalentControl_spec (σ : E → ℝ) (f g : E → E) (x : E)
    (hb : slidingDerivative σ g x ≠ 0) :
    slidingDerivative σ f x + equivalentControl σ f g x * slidingDerivative σ g x = 0 := by
  rw [equivalentControl_def]
  field_simp
  ring

/-- Uniqueness of the equivalent control: if `b = slidingDerivative σ g x ≠ 0` and a
control value `u` makes the sliding derivative vanish, then `u = equivalentControl`. -/
theorem equivalentControl_unique (σ : E → ℝ) (f g : E → E) (u : ℝ) (x : E)
    (hb : slidingDerivative σ g x ≠ 0)
    (hu : slidingDerivative σ f x + u * slidingDerivative σ g x = 0) :
    u = equivalentControl σ f g x := by
  rw [equivalentControl_def, eq_div_iff hb]
  linarith

/-- The equivalent-control closed loop `f + g · u_eq` is tangent to the sliding
manifold: its sliding derivative vanishes wherever `b = slidingDerivative σ g x ≠ 0`.
This is the algebraic content of the invariance of the sliding manifold under the
equivalent-control dynamics. -/
theorem slidingDerivative_equivalentControl_closedLoop (σ : E → ℝ) (f g : E → E) (x : E)
    (hb : slidingDerivative σ g x ≠ 0) :
    slidingDerivative σ (fun y ↦ f y + equivalentControl σ f g y • g y) x = 0 := by
  rw [slidingDerivative, map_add, map_smul, smul_eq_mul]
  exact equivalentControl_spec σ f g x hb
