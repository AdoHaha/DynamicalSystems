/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # The Legendre–Fenchel convex conjugate

For a finite-valued function `F : E → ℝ` on a real normed space and a continuous
linear functional `x* : E →L[ℝ] ℝ` the **convex conjugate** is

`convexConjugate F x* = ⨆ x, ((x* x : EReal) - (F x : EReal))`,

with the supremum taken in the extended reals `EReal = [-∞, +∞]`. Keeping `F`
finite-valued avoids the indeterminate form `∞ - ∞` in the definition. The
construction is the starting point of convex duality: it yields the
Fenchel–Young inequality `x* x ≤ F x + F* x*` (below) and, for a convex lower
semicontinuous `F`, the Fenchel–Moreau biconjugation theorem.

## Main definitions

* `convexConjugate F x*`: the Legendre–Fenchel conjugate of `F` at `x*`.

## Main statements

* `fenchel_inequality`: the Fenchel–Young inequality
  `x* x ≤ F x + convexConjugate F x*`.
* `convexConjugate_le_iff`: `convexConjugate F x* ≤ r` holds if and only if
  `x* x - F x ≤ r` for every `x`.
* `convexConjugate_antitone`: the conjugate is antitone in `F`.
* `convexConjugate_add_apply`: the shift rule `(F + y*)* x* = F* (x* - y*)`.
* `convexConjugate_add_const`: the constant shift rule `(F + c)* x* = F* x* - c`.
* `convexConjugate_const_zero`: `(const c)* 0 = -c`.
* `convexConjugate_lsc`: `x* ↦ convexConjugate F x*` is lower semicontinuous.
-/

@[expose] public section

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Legendre–Fenchel convex conjugate of a finite-valued function
`F : E → ℝ`, evaluated at a continuous linear functional `x*`:
`convexConjugate F x* = ⨆ x, (x* x - F x)`, the supremum being taken in the
extended reals `EReal`. -/
noncomputable def convexConjugate (F : E → ℝ) (xStar : E →L[ℝ] ℝ) : EReal :=
  ⨆ x : E, ((xStar x : EReal) - (F x : EReal))

/-- **Fenchel–Young inequality.** For every `x : E` and every continuous linear
functional `x*`, `x* x ≤ F x + convexConjugate F x*`. -/
theorem fenchel_inequality (F : E → ℝ) (x : E) (xStar : E →L[ℝ] ℝ) :
    (xStar x : EReal) ≤ (F x : EReal) + convexConjugate F xStar := by
  calc (xStar x : EReal)
      = ((xStar x : EReal) - (F x : EReal)) + (F x : EReal) := by rw [EReal.sub_add_cancel]
    _ ≤ convexConjugate F xStar + (F x : EReal) :=
        add_le_add_left (le_iSup (fun y : E ↦ ((xStar y : EReal) - (F y : EReal))) x) _
    _ = (F x : EReal) + convexConjugate F xStar := by rw [add_comm]

/-- The conjugate is characterised by its family of affine minorants: the
inequality `convexConjugate F x* ≤ r` holds if and only if `x* x - F x ≤ r` for
every `x`. -/
theorem convexConjugate_le_iff (F : E → ℝ) (xStar : E →L[ℝ] ℝ) (r : EReal) :
    convexConjugate F xStar ≤ r ↔ ∀ x : E, (xStar x : EReal) - (F x : EReal) ≤ r :=
  iSup_le_iff

/-- The Legendre–Fenchel conjugate is antitone: if `F ≤ G` pointwise, then
`convexConjugate G x* ≤ convexConjugate F x*` for every `x*`. -/
theorem convexConjugate_antitone {F G : E → ℝ} (h : F ≤ G) (xStar : E →L[ℝ] ℝ) :
    convexConjugate G xStar ≤ convexConjugate F xStar := by
  rw [convexConjugate, convexConjugate]
  apply iSup_le
  intro y
  apply le_iSup_of_le y
  exact EReal.sub_le_sub (le_refl (xStar y : EReal)) (by exact_mod_cast h y)

/-- The shift rule for the conjugate: conjugating `F + y*` shifts the argument
of the conjugate by `-y*`, that is `(F + y*)* x* = F* (x* - y*)`. -/
theorem convexConjugate_add_apply (F : E → ℝ) (yStar xStar : E →L[ℝ] ℝ) :
    convexConjugate (fun x ↦ F x + yStar x) xStar = convexConjugate F (xStar - yStar) := by
  rw [convexConjugate, convexConjugate]
  congr 1
  funext x
  rw [sub_apply]
  norm_cast
  ring

/-- The shift rule for a constant: conjugating `F + c` subtracts `c` from the
conjugate, that is `(F + c)* x* = F* x* - c`. -/
theorem convexConjugate_add_const (F : E → ℝ) (c : ℝ) (xStar : E →L[ℝ] ℝ) :
    convexConjugate (fun x ↦ F x + c) xStar = convexConjugate F xStar - (c : EReal) := by
  apply le_antisymm
  · rw [convexConjugate_le_iff]
    intro x
    have hx : ((xStar x : EReal) - (F x : EReal)) ≤ convexConjugate F xStar :=
      le_iSup (fun y : E ↦ ((xStar y : EReal) - (F y : EReal))) x
    have hsub := EReal.sub_le_sub hx (le_refl (c : EReal))
    rw [EReal.coe_add]
    have heq : (xStar x : EReal) - ((F x : EReal) + (c : EReal)) =
        ((xStar x : EReal) - (F x : EReal)) - (c : EReal) := by
      norm_cast
      ring
    rw [heq]
    exact hsub
  · rw [EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c)) (.inl (EReal.coe_ne_top c))]
    rw [convexConjugate_le_iff]
    intro x
    have hx : ((xStar x : EReal) - ((F x : EReal) + (c : EReal))) ≤
        convexConjugate (fun x ↦ F x + c) xStar := by
      rw [← EReal.coe_add]
      exact le_iSup (fun y : E ↦ ((xStar y : EReal) - ((F y + c : ℝ) : EReal))) x
    have h := add_le_add_left hx (c : EReal)
    have heq : ((xStar x : EReal) - ((F x : EReal) + (c : EReal))) + (c : EReal) =
        (xStar x : EReal) - (F x : EReal) := by
      norm_cast
      ring
    rwa [heq] at h

/-- The conjugate of the constant function of value `c`, evaluated at the zero
functional, is the negated constant: `(const c)* 0 = -c`. -/
theorem convexConjugate_const_zero (c : ℝ) :
    convexConjugate (fun _ : E ↦ c) (0 : E →L[ℝ] ℝ) = (-c : EReal) := by
  rw [convexConjugate]
  simp only [zero_apply]
  rw [ciSup_const]
  simp

/-- The conjugate `x* ↦ convexConjugate F x*` is lower semicontinuous, being the
supremum of the continuous affine functions `x* ↦ x* x - F x`. -/
theorem convexConjugate_lsc (F : E → ℝ) :
    LowerSemicontinuous (fun xStar : E →L[ℝ] ℝ ↦ convexConjugate F xStar) := by
  change LowerSemicontinuous (fun xStar : E →L[ℝ] ℝ ↦
    ⨆ x : E, ((xStar x : EReal) - (F x : EReal)))
  apply lowerSemicontinuous_iSup
  intro x
  have h : (fun xStar : E →L[ℝ] ℝ ↦ (xStar x : EReal) - (F x : EReal))
      = fun xStar ↦ ((xStar x - F x : ℝ) : EReal) := by
    funext xStar
    rw [← EReal.coe_sub]
  rw [h]
  exact Continuous.lowerSemicontinuous (continuous_coe_real_ereal.comp (by fun_prop))
