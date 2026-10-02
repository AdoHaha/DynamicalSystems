/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.Basic
public import DynamicalSystems.Stability.FiniteTimeLyapunov
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The reaching condition of first-order sliding mode

This file records the *reaching phase* of first-order sliding-mode control of
G. Bartolini, L. Fridman, A. Pisano and E. Usai (eds.), *Modern Sliding Mode
Control Theory: New Perspectives and Applications*, LNCIS 375, Springer 2008
(Chapter 4, A. Levant and L. Alelishvili, *Discontinuous Homogeneous Control*,
Section 3, printed pp. 75–76). The task of the reaching phase is to drive the
scalar output `σ` to the sliding manifold `{σ = 0}` in finite time and to keep
it there.

For a scalar output `s : ℝ → ℝ` the *reaching condition* with rate `η > 0` is

`s t * s' t ≤ -η * |s t|` for all `t ≥ 0`,

i.e. `(1/2) d/dt (s t)^2 ≤ -η |s t|`. It is the scalar form of the Lyapunov
condition `V̇ ≤ -c V ^ α` for `V = s ^ 2`, `α = 1/2` and `c = 2η`, and is
discharged below by the finite-time comparison estimate
`eq_zero_of_hasDerivWithinAt_le_neg_mul_rpow` of
`DynamicalSystems.Stability.FiniteTimeLyapunov`.

## Main definitions

* `ReachingCondition η s`: the reaching condition `s * s' ≤ -η |s|` for `t ≥ 0`.

## Main statements

* `eq_zero_of_reachingCondition`: a continuous output `s` with a right derivative
  on `[0, ∞)` satisfying the reaching condition with rate `η > 0` vanishes for
  all `t ≥ |s 0| / η`.
-/

open Set

@[expose] public section

/-- The reaching condition `s * s' ≤ -η |s|` (`η > 0`) along a scalar output `s`:
the time derivative of `(1/2) s^2` is at most `-η |s|`, so the squared output
decreases at a rate proportional to the output itself. This is the scalar
reaching condition of first-order sliding-mode control (Chapter 4, printed
pp. 75–76), written for the forward time half-line. -/
def ReachingCondition (η : ℝ) (s : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → s t * deriv s t ≤ -η * |s t|

/-- Under the reaching condition a continuous output with a right derivative on
`[0, ∞)` reaches the sliding manifold in finite time: `s t = 0` for every
`t ≥ |s 0| / η`.

The proof applies the finite-time comparison estimate
`eq_zero_of_hasDerivWithinAt_le_neg_mul_rpow` to `z t = (s t)^2` with `α = 1/2`
and `c = 2η`. Indeed `z' = 2 s s' ≤ -2η |s| = -(2η) z ^ (1/2)`, so `z` vanishes by
time `z 0 ^ (1/2) / (2η * (1/2)) = |s 0| / η`, and `z t = 0` is equivalent to
`s t = 0`. The only point needing care is that the right derivative of `z` is
`2 s s'`: where `s' ≠ 0` the output `s` is differentiable (otherwise `deriv s = 0`
by convention) and the two-sided chain rule applies, while where `s' = 0` the
right derivative of `z` vanishes and `deriv z = 0`. -/
theorem eq_zero_of_reachingCondition {η : ℝ} (hη : 0 < η) {s : ℝ → ℝ}
    (hscont : ContinuousOn s (Set.Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt s (deriv s t) (Set.Ici t) t)
    (h : ReachingCondition η s) :
    ∀ t, |s 0| / η ≤ t → s t = 0 := by
  have hc : (0 : ℝ) < 2 * η := by linarith
  have hα1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hzcont : ContinuousOn (fun t : ℝ ↦ (s t) ^ 2) (Set.Ici 0) := by
    have h := hscont.pow 2
    rwa [Pi.pow_def] at h
  have hnonneg : ∀ t, 0 ≤ t → 0 ≤ (s t) ^ 2 := fun t _ ↦ sq_nonneg (s t)
  -- The two-sided derivative of `z t = (s t)^2` is always `2 * s t * deriv s t`.
  have hzderiv : ∀ t, 0 ≤ t → deriv (fun x : ℝ ↦ (s x) ^ 2) t = 2 * s t * deriv s t := by
    intro t ht
    by_cases hd : deriv s t = 0
    · have hchain : HasDerivWithinAt (fun x : ℝ ↦ (s x) ^ 2) (2 * s t * deriv s t)
          (Set.Ici t) t := by
        have h2 : HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * s t) (s t) := by
          simpa using hasDerivAt_pow 2 (s t)
        exact h2.comp_hasDerivWithinAt t (hderiv t ht)
      rw [hd, mul_zero] at hchain
      rw [hchain.deriv_eq_zero (uniqueDiffWithinAt_Ici t), hd]
      ring
    · have hsd : DifferentiableAt ℝ s t := by
        by_contra hnsd
        exact hd (deriv_zero_of_not_differentiableAt hnsd)
      have h2 : HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * s t) (s t) := by
        simpa using hasDerivAt_pow 2 (s t)
      exact (h2.comp t hsd.hasDerivAt).deriv
  have hzwithin : ∀ t, 0 ≤ t → HasDerivWithinAt (fun x : ℝ ↦ (s x) ^ 2)
      (deriv (fun x : ℝ ↦ (s x) ^ 2) t) (Set.Ici t) t := by
    intro t ht
    have hchain : HasDerivWithinAt (fun x : ℝ ↦ (s x) ^ 2) (2 * s t * deriv s t)
        (Set.Ici t) t := by
      have h2 : HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * s t) (s t) := by
        simpa using hasDerivAt_pow 2 (s t)
      exact h2.comp_hasDerivWithinAt t (hderiv t ht)
    rwa [← hzderiv t ht] at hchain
  have hzineq : ∀ t, 0 ≤ t → deriv (fun x : ℝ ↦ (s x) ^ 2) t ≤
      (-(2 * η)) * (fun x : ℝ ↦ (s x) ^ 2) t ^ (1 / 2 : ℝ) := by
    intro t ht
    rw [hzderiv t ht]
    have hzpow : ((s t) ^ 2) ^ (1 / 2 : ℝ) = |s t| := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
    rw [hzpow]
    have hreach := h t ht
    have hmul := mul_le_mul_of_nonneg_left hreach (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [hmul]
  intro t ht
  -- The settling bound of the comparison estimate is exactly `|s 0| / η`.
  have hbound : ((s 0) ^ 2) ^ (1 - (1 / 2 : ℝ)) / ((2 * η) * (1 - 1 / 2)) = |s 0| / η := by
    have h1 : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
    have h2 : (2 * η) * (1 / 2 : ℝ) = η := by ring
    rw [h1, h2, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  have hmain := eq_zero_of_hasDerivWithinAt_le_neg_mul_rpow (z := fun x : ℝ ↦ (s x) ^ 2)
    (c := 2 * η) (α := 1 / 2) hc hα1 hzcont hnonneg hzwithin hzineq t (by rwa [hbound])
  exact sq_eq_zero_iff.mp hmain
