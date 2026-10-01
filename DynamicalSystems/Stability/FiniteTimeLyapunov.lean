/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Finite-time Lyapunov comparison

This file records the scalar comparison estimate behind the finite-time Lyapunov sufficient
condition of A. Levant and L. Alelishvili, *Discontinuous Homogeneous Control*, Chapter 4 of
G. Bartolini, L. Fridman, A. Pisano and E. Usai (eds.), *Modern Sliding Mode Control Theory:
New Perspectives and Applications*, LNCIS 375, Springer 2008 (printed pp. 72–73, PDF pp. 88–89).

The finite-time Lyapunov condition for a positive-definite function `V` is
`V̇ ≤ -c V ^ α` with `0 ≤ α < 1` and `c > 0`; the book's definition 1° (printed p. 72)
is the resulting finite-time stability property. The present file isolates the
one-dimensional comparison step: along such an inequality a non-negative scalar `z` cannot
stay positive past the settling time `z 0 ^ (1 - α) / (c * (1 - α))`.

## Main statements

* `eq_zero_of_hasDerivWithinAt_le_neg_mul_rpow`: a non-negative continuous `z` whose right
  derivative satisfies `z' ≤ -c * z ^ α` (`0 ≤ α < 1`, `c > 0`) reaches zero by time
  `z 0 ^ (1 - α) / (c * (1 - α))`.
-/

open Set

@[expose] public section

set_option linter.unusedVariables false in
/-- Scalar finite-time comparison: a non-negative continuous `z` with right derivative
`z' ≤ -c z ^ α` (`0 ≤ α < 1`, `c > 0`) reaches zero by time
`z 0 ^ (1 - α) / (c * (1 - α))`.

The proof sets `p = 1 - α > 0`. Since `z' ≤ -c z ^ α ≤ 0`, the function `z` is non-increasing
on `[0, ∞)`, so it stays zero once it vanishes. Off the zero set the function
`s ↦ z s ^ p + c * p * s` has right derivative `p * z ^ (p - 1) * z' + c * p ≤ -c * p + c * p = 0`,
because `z ^ (p - 1) * z ^ α = z ^ 0 = 1`; the one-sided fencing theorem
`image_le_of_deriv_right_le_deriv_boundary` therefore gives `z t ^ p + c * p * t ≤ z 0 ^ p`, and
the assumed lower bound on `t` forces `z t ^ p = 0`, hence `z t = 0`.

The hypothesis `0 ≤ α` is part of the stated range `0 ≤ α < 1` of the comparison condition; the
argument only needs `α < 1` (through `p = 1 - α > 0`), so it is kept for compatibility with the
Lyapunov theorem that consumes this estimate. The unused-variable linter is disabled locally
for this binder rather than dropping it from the required statement; both the compiler's
`unusedVariables` warning and the `unusedArguments` linter are disabled locally. -/
@[nolint unusedArguments]
theorem eq_zero_of_hasDerivWithinAt_le_neg_mul_rpow {z : ℝ → ℝ} {c α : ℝ}
    (hc : 0 < c) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hzcont : ContinuousOn z (Set.Ici 0)) (hnonneg : ∀ t, 0 ≤ t → 0 ≤ z t)
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt z (deriv z t) (Set.Ici t) t)
    (hineq : ∀ t, 0 ≤ t → deriv z t ≤ -c * z t ^ α) :
    ∀ t, z 0 ^ (1 - α) / (c * (1 - α)) ≤ t → z t = 0 := by
  have hp : 0 < 1 - α := by linarith
  have hc' : 0 < c * (1 - α) := mul_pos hc hp
  -- `z` is non-increasing on `[0, ∞)` because `z' ≤ -c z ^ α ≤ 0`.
  have hanti : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → z b ≤ z a := by
    intro a b ha hab
    have hcont : ContinuousOn z (Set.Icc a b) := hzcont.mono fun x hx ↦ le_trans ha hx.1
    have hderiv' : ∀ x ∈ Set.Ico a b, HasDerivWithinAt z (deriv z x) (Set.Ici x) x :=
      fun x hx ↦ hderiv x (le_trans ha hx.1)
    have hbound : ∀ x ∈ Set.Ico a b, deriv z x ≤ (0 : ℝ) := by
      intro x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1
      have hzα : 0 ≤ z x ^ α := Real.rpow_nonneg (hnonneg x hx0) α
      have h := hineq x hx0
      nlinarith [hc, hzα]
    have hmain := image_le_of_deriv_right_le_deriv_boundary (f := z) (f' := deriv z)
      (B := fun _ ↦ z a) (B' := fun _ ↦ 0) hcont hderiv' (le_refl (z a)) continuousOn_const
      (fun x _ ↦ hasDerivWithinAt_const x (Set.Ici x) (z a)) hbound
    exact hmain (Set.right_mem_Icc.mpr hab)
  intro t ht
  have ht0 : 0 ≤ t := by
    have h0 : 0 ≤ z 0 ^ (1 - α) / (c * (1 - α)) :=
      div_nonneg (Real.rpow_nonneg (hnonneg 0 le_rfl) _) hc'.le
    linarith
  by_contra hzt
  have hztpos : 0 < z t := lt_of_le_of_ne (hnonneg t ht0) (Ne.symm hzt)
  -- Off the zero set, `s ↦ z s ^ (1 - α) + c * (1 - α) * s` decreases at slope `c * (1 - α)`.
  have hF : z t ^ (1 - α) + c * (1 - α) * t ≤ z 0 ^ (1 - α) := by
    let F : ℝ → ℝ := fun s ↦ z s ^ (1 - α) + c * (1 - α) * s
    have hFcont : ContinuousOn F (Set.Icc 0 t) := by
      have h1 : ContinuousOn (fun s ↦ z s ^ (1 - α)) (Set.Icc 0 t) :=
        (hzcont.mono fun x hx ↦ hx.1).rpow_const fun _ _ ↦ Or.inr hp.le
      have h2 : ContinuousOn (fun s : ℝ ↦ c * (1 - α) * s) (Set.Icc 0 t) :=
        continuousOn_const.mul continuousOn_id
      exact h1.add h2
    have hFderiv : ∀ x ∈ Set.Ico 0 t,
        HasDerivWithinAt F (deriv z x * (1 - α) * z x ^ ((1 - α) - 1) + c * (1 - α))
          (Set.Ici x) x := by
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hxt : x ≤ t := le_of_lt hx.2
      have hzx : 0 < z x := lt_of_lt_of_le hztpos (hanti hx0 hxt)
      have h1 : HasDerivWithinAt (fun s ↦ z s ^ (1 - α))
          (deriv z x * (1 - α) * z x ^ ((1 - α) - 1)) (Set.Ici x) x :=
        (hderiv x hx0).rpow_const (Or.inl (ne_of_gt hzx))
      have h2 : HasDerivWithinAt (fun s : ℝ ↦ c * (1 - α) * s) (c * (1 - α))
          (Set.Ici x) x := by
        simpa using (hasDerivWithinAt_id x (Set.Ici x)).const_mul (c * (1 - α))
      exact h1.add h2
    have hbound : ∀ x ∈ Set.Ico 0 t,
        deriv z x * (1 - α) * z x ^ ((1 - α) - 1) + c * (1 - α) ≤ 0 := by
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hxt : x ≤ t := le_of_lt hx.2
      have hzx : 0 < z x := lt_of_lt_of_le hztpos (hanti hx0 hxt)
      have hP : 0 ≤ z x ^ ((1 - α) - 1) := Real.rpow_nonneg (le_of_lt hzx) _
      have hstep1 : deriv z x * (1 - α) ≤ (-c * z x ^ α) * (1 - α) :=
        mul_le_mul_of_nonneg_right (hineq x hx0) hp.le
      have hstep2 : deriv z x * (1 - α) * z x ^ ((1 - α) - 1)
          ≤ (-c * z x ^ α) * (1 - α) * z x ^ ((1 - α) - 1) :=
        mul_le_mul_of_nonneg_right hstep1 hP
      have haux : z x ^ α * z x ^ ((1 - α) - 1) = 1 := by
        rw [← Real.rpow_add hzx, show α + ((1 - α) - 1) = 0 by ring, Real.rpow_zero]
      have hident : (-c * z x ^ α) * (1 - α) * z x ^ ((1 - α) - 1) = -c * (1 - α) := by
        calc (-c * z x ^ α) * (1 - α) * z x ^ ((1 - α) - 1)
            = -c * (1 - α) * (z x ^ α * z x ^ ((1 - α) - 1)) := by ring
          _ = -c * (1 - α) := by rw [haux, mul_one]
      linarith
    have hmain := image_le_of_deriv_right_le_deriv_boundary (f := F)
      (f' := fun x ↦ deriv z x * (1 - α) * z x ^ ((1 - α) - 1) + c * (1 - α))
      (B := fun _ ↦ F 0) (B' := fun _ ↦ 0) hFcont hFderiv (le_refl (F 0)) continuousOn_const
      (fun x _ ↦ hasDerivWithinAt_const x (Set.Ici x) (F 0)) hbound
    have ht' := hmain (Set.right_mem_Icc.mpr ht0)
    simpa [F] using ht'
  -- The assumed time bound makes the right-hand side of the fence non-positive.
  have ht' : z 0 ^ (1 - α) ≤ c * (1 - α) * t := by
    have h := ht
    rw [div_le_iff₀ hc'] at h
    calc z 0 ^ (1 - α) ≤ t * (c * (1 - α)) := h
      _ = c * (1 - α) * t := by ring
  have hle : z t ^ (1 - α) ≤ 0 := by linarith
  have hpos : 0 < z t ^ (1 - α) := Real.rpow_pos_of_pos hztpos _
  linarith
