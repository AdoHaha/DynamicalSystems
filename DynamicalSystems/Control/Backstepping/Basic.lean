/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import DynamicalSystems.Stability.Comparison
public import DynamicalSystems.Stability.Barbalat

/-!
# Integrator backstepping for second-order nonlinear systems

This file formalizes the integrator backstepping design for the second-order
strict-feedback nonlinear system of Kabziński and Mosiołek,
*Projektowanie nieliniowych układów sterowania*, Chapter 6, Section 6.2
(equations 6.19–6.38).

The plant is

```
x₁' = x₂ + F₁(x₁, θ)
x₂' = g * u + F₂(x₁, x₂, θ)
```

and the control objective is tracking of a smooth reference trajectory `x₁d`.
The design introduces the tracking errors `e₁ = x₁ - x₁d` and
`e₂ = x₂ - α₁`, where `α₁` is the virtual stabilizing function, and the
composite Lyapunov candidate `V₂ = (1/2) e₁² + (1/2) e₂²`.

## Main definitions

* `backstepping_e1`: tracking error `e₁ = x₁ - x₁d` (equation 6.21).
* `backstepping_alpha1`: stabilizing function `α₁ = -k₁ e₁ - F₁ + x₁d'`
  (equation 6.28).
* `backstepping_e2`: error coordinate `e₂ = x₂ - α₁` (equation 6.24).
* `backstepping_u`: feedback control `u = -k₂ e₂ - e₁ - F₂ + α₁'`
  (equation 6.37).
* `backstepping_V2`: composite Lyapunov function `V₂(e₁, e₂) = (1/2) e₁² + (1/2) e₂²`
  (equation 6.35).

## Main results

* `backstepping_e1_hasDerivAt`: closed-loop dynamics `e₁' = -k₁ e₁ + e₂`
  (equation 6.30).
* `backstepping_e2_hasDerivAt`: closed-loop dynamics `e₂' = -k₂ e₂ - e₁`.
* `backstepping_V2_hasDerivAt`: Lyapunov derivative `V₂' = -k₁ e₁² - k₂ e₂²`
  (equation 6.38).
* `backstepping_V2_deriv_le_neg_mul`: dissipation inequality
  `V₂' ≤ -(2 min k₁ k₂) V₂`.
* `backstepping_V2_le_exp_decay`: exponential decay of `V₂` along closed-loop
  trajectories via the scalar comparison (Grönwall) estimate.
* `backstepping_tracking_tendsto_zero`: asymptotic tracking `e₁ → 0` and `e₂ → 0`.
-/

@[expose] public section

/-- First error coordinate: the tracking error between the plant state `x₁` and the
reference trajectory `x_d` (Kabziński–Mosiołek, equation 6.21). -/
-- The underscore in `backstepping_e1` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def backstepping_e1 (x1 xd : ℝ) : ℝ := x1 - xd

/-- Virtual control (stabilizing function) `α₁` for the second-order system:
`α₁ = -k₁ (x₁ - x_d) - f₁ + x_d'` (Kabziński–Mosiołek, equation 6.28). The value
`f₁_val` is `F₁(x₁, θ)` and `xd'` is the reference velocity `ẋ₁d`. -/
-- The underscore in `backstepping_alpha1` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def backstepping_alpha1 (k1 x1 xd xd' f1_val : ℝ) : ℝ :=
  -k1 * (x1 - xd) - f1_val + xd'

/-- Second error coordinate: the discrepancy between the plant state `x₂` and the
virtual control `α₁` (Kabziński–Mosiołek, equation 6.24). -/
-- The underscore in `backstepping_e2` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def backstepping_e2 (x2 alpha1_val : ℝ) : ℝ := x2 - alpha1_val

/-- Actual feedback control `u` for the second-order system:
`u = -k₂ e₂ - e₁ - f₂ + α₁'` (Kabziński–Mosiołek, equation 6.37). -/
-- The underscore in `backstepping_u` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def backstepping_u (k2 e1 e2 f2_val alpha1' : ℝ) : ℝ :=
  -k2 * e2 - e1 - f2_val + alpha1'

/-- Composite Lyapunov function for the second-order backstepping system:
`V₂(e₁, e₂) = (1/2) e₁² + (1/2) e₂²` (Kabziński–Mosiołek, equation 6.35). -/
-- The underscore in `backstepping_V2` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
noncomputable def backstepping_V2 (e1 e2 : ℝ) : ℝ :=
  (1 / 2 : ℝ) * e1 ^ 2 + (1 / 2 : ℝ) * e2 ^ 2

/-- Algebraic cancellation in the first error coordinate: along the plant
`x₁' = x₂ + F₁` and the reference `x_d' = x_d'`, the error derivative
`(x₂ + F₁) - x_d'` equals `-k₁ e₁ + e₂` for the stabilizing function `α₁`
(Kabziński–Mosiołek, equations 6.25 and 6.30). -/
private theorem backstepping_e1_algebra (k1 x1 x2 xd xd' f1_val : ℝ) :
    (x2 + f1_val) - xd' =
      -k1 * backstepping_e1 x1 xd +
        backstepping_e2 x2 (backstepping_alpha1 k1 x1 xd xd' f1_val) := by
  dsimp [backstepping_e1, backstepping_alpha1, backstepping_e2]
  ring

/-- Algebraic cancellation in the second error coordinate: with
`u = -k₂ e₂ - e₁ - f₂ + α₁'` the error derivative `(u + f₂) - α₁'` equals
`-k₂ e₂ - e₁` (Kabziński–Mosiołek, equation 6.38). -/
private theorem backstepping_e2_algebra (k2 e1 e2 f2_val alpha1' : ℝ) :
    (backstepping_u k2 e1 e2 f2_val alpha1' + f2_val) - alpha1' = -k2 * e2 - e1 := by
  dsimp [backstepping_u]
  ring

/-- The derivative of the tracking error `e₁` along the plant trajectories satisfies
`e₁' = -k₁ e₁ + e₂` (Kabziński–Mosiołek, equations 6.25 and 6.30). -/
theorem backstepping_e1_hasDerivAt
    {x1 x2 xd xd' : ℝ → ℝ} {f1_val : ℝ → ℝ} {k1 : ℝ} {t : ℝ}
    (hx1 : HasDerivAt x1 (x2 t + f1_val t) t)
    (hxd : HasDerivAt xd (xd' t) t) :
    HasDerivAt (fun s ↦ backstepping_e1 (x1 s) (xd s))
      (-k1 * backstepping_e1 (x1 t) (xd t) +
        backstepping_e2 (x2 t) (backstepping_alpha1 k1 (x1 t) (xd t) (xd' t) (f1_val t))) t := by
  have h := hx1.sub hxd
  rw [backstepping_e1_algebra] at h
  exact h

/-- The derivative of the second error coordinate `e₂` along the plant trajectories
satisfies `e₂' = -k₂ e₂ - e₁` when the control equals `backstepping_u` at time `t`
(Kabziński–Mosiołek, equations 6.31 and 6.38). -/
theorem backstepping_e2_hasDerivAt
    {x2 u : ℝ → ℝ} {alpha1 alpha1' f2_val : ℝ → ℝ} {k2 e1 : ℝ} {t : ℝ}
    (hx2 : HasDerivAt x2 (u t + f2_val t) t)
    (halpha1 : HasDerivAt alpha1 (alpha1' t) t)
    (hu : u t = backstepping_u k2 e1 (backstepping_e2 (x2 t) (alpha1 t)) (f2_val t) (alpha1' t)) :
    HasDerivAt (fun s ↦ backstepping_e2 (x2 s) (alpha1 s))
      (-k2 * backstepping_e2 (x2 t) (alpha1 t) - e1) t := by
  have h := hx2.sub halpha1
  rw [hu, backstepping_e2_algebra] at h
  exact h

/-- Derivative of the composite Lyapunov function `V₂` along the closed-loop error
dynamics `e₁' = -k₁ e₁ + e₂`, `e₂' = -k₂ e₂ - e₁`:
`V₂' = -k₁ e₁² - k₂ e₂²` (Kabziński–Mosiołek, equation 6.38). -/
theorem backstepping_V2_hasDerivAt
    {e1 e2 : ℝ → ℝ} {k1 k2 : ℝ} {t : ℝ}
    (he1 : HasDerivAt e1 (-k1 * e1 t + e2 t) t)
    (he2 : HasDerivAt e2 (-k2 * e2 t - e1 t) t) :
    HasDerivAt (fun s ↦ backstepping_V2 (e1 s) (e2 s))
      (-k1 * (e1 t) ^ 2 - k2 * (e2 t) ^ 2) t := by
  dsimp [backstepping_V2]
  have h1 := (he1.pow 2).const_mul (1 / 2 : ℝ)
  have h2 := (he2.pow 2).const_mul (1 / 2 : ℝ)
  have hadd := h1.add h2
  convert hadd using 1
  ring

/-- Dissipation inequality for the composite Lyapunov function: for positive gains
`k₁, k₂` the closed-loop derivative is bounded by `-(2 min k₁ k₂) V₂`
(Kabziński–Mosiołek, equation 6.38). -/
theorem backstepping_V2_deriv_le_neg_mul
    {k1 k2 e1 e2 : ℝ} (hk1 : 0 < k1) (hk2 : 0 < k2) :
    -k1 * e1 ^ 2 - k2 * e2 ^ 2 ≤ -(2 * min k1 k2 * backstepping_V2 e1 e2) := by
  dsimp [backstepping_V2]
  have hmin1 : min k1 k2 ≤ k1 := min_le_left k1 k2
  have hmin2 : min k1 k2 ≤ k2 := min_le_right k1 k2
  have hsq1 : 0 ≤ e1 ^ 2 := sq_nonneg e1
  have hsq2 : 0 ≤ e2 ^ 2 := sq_nonneg e2
  have hminpos : 0 < min k1 k2 := lt_min hk1 hk2
  nlinarith [hmin1, hmin2, hsq1, hsq2]

/-- Exponential decay of the composite Lyapunov function `V₂(t)` along closed-loop
trajectories. If `V₂' = -k₁ e₁² - k₂ e₂²` and `k₁, k₂ > 0`, then for `t ≥ 0`
`V₂(t) ≤ V₂(0) exp (-(2 min k₁ k₂) t)` by the scalar comparison (Grönwall) estimate. -/
theorem backstepping_V2_le_exp_decay
    {e1 e2 : ℝ → ℝ} {k1 k2 : ℝ} (hk1 : 0 < k1) (hk2 : 0 < k2)
    (hderiv : ∀ t ≥ 0, HasDerivAt (fun s ↦ backstepping_V2 (e1 s) (e2 s))
      (-k1 * (e1 t) ^ 2 - k2 * (e2 t) ^ 2) t) :
    ∀ t ≥ 0, backstepping_V2 (e1 t) (e2 t) ≤
      backstepping_V2 (e1 0) (e2 0) * Real.exp (-(2 * min k1 k2) * t) := by
  intro t ht
  have hc : 0 < 2 * min k1 k2 := by
    have hmin : 0 < min k1 k2 := lt_min hk1 hk2
    linarith
  have hderiv' : ∀ s, 0 ≤ s →
      HasDerivAt (fun s ↦ backstepping_V2 (e1 s) (e2 s))
        (deriv (fun s ↦ backstepping_V2 (e1 s) (e2 s)) s) s := by
    intro s hs
    simpa only [(hderiv s hs).deriv] using hderiv s hs
  have hineq : ∀ s, 0 ≤ s →
      deriv (fun s ↦ backstepping_V2 (e1 s) (e2 s)) s ≤
        -(2 * min k1 k2 * backstepping_V2 (e1 s) (e2 s)) + 0 := by
    intro s hs
    rw [(hderiv s hs).deriv, add_zero]
    exact backstepping_V2_deriv_le_neg_mul hk1 hk2
  have hgron := le_gronwallBound_of_hasDerivAt_le_Ici (t₀ := 0) (c := 2 * min k1 k2)
    (d := 0) hc hderiv' hineq t ht
  rw [zero_div, zero_mul, add_zero] at hgron
  simpa only [sub_zero] using hgron

/-- Asymptotic tracking convergence of the second-order backstepping system: if the
composite Lyapunov function satisfies the closed-loop identity
`V₂' = -k₁ e₁² - k₂ e₂²` with `k₁, k₂ > 0`, then both error coordinates converge to
zero (Kabziński–Mosiołek, equation 6.38). -/
theorem backstepping_tracking_tendsto_zero
    {e1 e2 : ℝ → ℝ} {k1 k2 : ℝ} (hk1 : 0 < k1) (hk2 : 0 < k2)
    (hderiv : ∀ t ≥ 0, HasDerivAt (fun s ↦ backstepping_V2 (e1 s) (e2 s))
      (-k1 * (e1 t) ^ 2 - k2 * (e2 t) ^ 2) t) :
    Filter.Tendsto e1 Filter.atTop (nhds 0) ∧ Filter.Tendsto e2 Filter.atTop (nhds 0) := by
  have hdecay := backstepping_V2_le_exp_decay hk1 hk2 hderiv
  have hc : 0 < 2 * min k1 k2 := by
    have hmin : 0 < min k1 k2 := lt_min hk1 hk2
    linarith
  have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-(2 * min k1 k2) * t))
      Filter.atTop (nhds 0) := by
    have hct : Filter.Tendsto (fun t : ℝ => (2 * min k1 k2) * t) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id
    have hexp_neg : Filter.Tendsto
        (fun t : ℝ => Real.exp (-((2 * min k1 k2) * t))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hct
    simpa only [neg_mul] using hexp_neg
  have hw : Filter.Tendsto
      (fun t : ℝ => backstepping_V2 (e1 0) (e2 0) * Real.exp (-(2 * min k1 k2) * t))
      Filter.atTop (nhds 0) := by
    simpa using hexp.const_mul (backstepping_V2 (e1 0) (e2 0))
  constructor
  · refine Barbalat.tendsto_zero_of_tendsto_zero_of_sq_le (c := (1 / 2 : ℝ))
      (by norm_num) hw ?_
    intro t ht
    have hV := hdecay t ht
    have h2 : 0 ≤ (1 / 2 : ℝ) * (e2 t) ^ 2 := by positivity
    dsimp [backstepping_V2] at hV ⊢
    linarith
  · refine Barbalat.tendsto_zero_of_tendsto_zero_of_sq_le (c := (1 / 2 : ℝ))
      (by norm_num) hw ?_
    intro t ht
    have hV := hdecay t ht
    have h2 : 0 ≤ (1 / 2 : ℝ) * (e1 t) ^ 2 := by positivity
    dsimp [backstepping_V2] at hV ⊢
    linarith
