/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.ConvexAnalysis.Conjugate
public import DynamicalSystems.ConvexAnalysis.Subdifferential

/-! # Duality between the conjugate and the subdifferential

For a finite-valued function `F : E → ℝ` on a real normed space, a continuous
linear functional `x*` is a subgradient of `F` at `x` if and only if the
Fenchel–Young inequality at the pair `(x, x*)` is an equality. This is
Rindler, *Calculus of Variations*, Theorem 3.32: the subdifferential is exactly
the set of dual points at which the Fenchel–Young inequality is tight.

The statement is unconditional — no convexity or lower semicontinuity of `F` is
required. In one direction the definition of the subdifferential bounds the
counting function `y ↦ x* y - F y` by its value at `x`, which bounds the
conjugate; in the other direction the conjugate is a supremum, so equality
forces `x` itself to realize it and yields the supporting inequality.

## Main statements

* `mem_subdifferential_iff_duality_equality`: `x* ∈ ∂F x` if and only if
  `F x + F* x* = x* x`.
-/

@[expose] public section

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Duality between the subdifferential and the conjugate** (Rindler,
Theorem 3.32). For a finite-valued function `F : E → ℝ`, a continuous linear
functional `x*` is a subgradient of `F` at `x` if and only if the Fenchel–Young
inequality is an equality:
`x* ∈ ∂F x ↔ F x + F* x* = x* x`.

No convexity or lower semicontinuity of `F` is needed: both sides simply say that
the affine function `y ↦ x* y - F y` attains its supremum at `x`. -/
theorem mem_subdifferential_iff_duality_equality (F : E → ℝ) (x : E) (xStar : E →L[ℝ] ℝ) :
    xStar ∈ subdifferential F x ↔
      (F x : EReal) + convexConjugate F xStar = (xStar x : EReal) := by
  constructor
  · intro h
    refine le_antisymm ?_ (fenchel_inequality F x xStar)
    have hle : convexConjugate F xStar ≤ (xStar x : EReal) - (F x : EReal) := by
      rw [convexConjugate_le_iff]
      intro y
      have hy := h y
      rw [map_sub] at hy
      have hy' : xStar y - F y ≤ xStar x - F x := by linarith
      exact_mod_cast hy'
    calc (F x : EReal) + convexConjugate F xStar
        ≤ (F x : EReal) + ((xStar x : EReal) - (F x : EReal)) := add_le_add le_rfl hle
      _ = (xStar x : EReal) := by rw [add_comm, EReal.sub_add_cancel]
  · intro heq y
    have hle := le_iSup (fun z : E ↦ ((xStar z : EReal) - (F z : EReal))) y
    have hbound : (F x : EReal) + ((xStar y : EReal) - (F y : EReal)) ≤ (xStar x : EReal) := by
      calc (F x : EReal) + ((xStar y : EReal) - (F y : EReal))
          ≤ (F x : EReal) + convexConjugate F xStar := add_le_add le_rfl hle
        _ = (xStar x : EReal) := heq
    have hreal : F x + (xStar y - F y) ≤ xStar x := by
      exact_mod_cast hbound
    rw [map_sub]
    linarith
