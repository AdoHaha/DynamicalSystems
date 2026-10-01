/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import DynamicalSystems.Control.Calculus
public import DynamicalSystems.Control.Backstepping.Tuning
public import DynamicalSystems.Control.Adaptive.RobustMRAC
public import DynamicalSystems.Stability.Projection
public import DynamicalSystems.Stability.Comparison
public import DynamicalSystems.Stability.UltimateBoundedness

/-!
# Robust adaptive backstepping with tuning functions

This file formalizes the robust modifications of the adaptive backstepping
tuning-functions design for second-order strict-feedback systems, following
Kabziński and Mosiołek, *Projektowanie nieliniowych układów sterowania*,
Komitet Automatyki i Robotyki PAN, Monografie tom 22, Chapter 7, Section 7.4,
pages 135–142, Theorems 7.4 and 7.6, equations (7.128)–(7.174).

## Architecture

The plant is the second-order strict-feedback system with parametric uncertainty
```
x₁' = x₂ + ϕ₁(x₁)ᵀ θ
x₂' = u + ϕ₂(x₁, x₂)ᵀ θ
```
with tracking error `e₁ = x₁ - x_d`, virtual control `α₁ = -k₁ e₁ - θ̂ᵀ ϕ₁ + x_d'`,
second error `e₂ = x₂ - α₁`, and tuning functions `τ₁ = e₁ • ϕ₁`, `τ₂ = τ₁ + e₂ • z₂`.
The composite Lyapunov candidate is the public `tuning_V2` of
`DynamicalSystems.Control.Backstepping.Tuning`:
`V₂(e₁, e₂, θ̃) = (1/2) e₁² + (1/2) e₂² + (1/2) (θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ θ̃))`.

Two robust adaptation mechanisms counter parameter drift:
1. **σ-modification (Section 7.4.1, Theorem 7.4):**
   `θ̂' = Γ *ᵥ (τ₂ - σ • θ̂)`. Along trajectories, completing the square gives
   `V̇₂ ≤ -k₁ e₁² - k₂ e₂² - (σ/2) ‖θ̃‖² + (σ/2) ‖θ‖² ≤ -c V₂ + d` with
   `d = (σ/2) ‖θ‖²`, yielding uniform boundedness `V₂(t) ≤ max (V₂(0)) (d/c)` and
   eventual boundedness `V₂(t) < B` for every `B > d/c`.
2. **Parameter box projection (Section 7.4.3, Theorem 7.6):**
   `θ̂' = Γ *ᵥ Proj θᵐ θᴹ τ₂ θ̂`. Along trajectories with true parameter `θ ∈ [θᵐ, θᴹ]`,
   the fundamental projection inequality `Proj_sum_nonpos` ensures
   `V̇₂ ≤ -k₁ e₁² - k₂ e₂² ≤ 0`, preventing drift without an energy offset.

## Main definitions

* `robust_tuning_sigma_adaptation_law`: σ-modified tuning-function adaptation vector field
  `θ̂' = Γ *ᵥ (τ₂ - σ • θ̂)` (equation 7.136).
* `robust_tuning_proj_adaptation_law`: projected tuning-function adaptation vector field
  `θ̂' = Γ *ᵥ Proj θᵐ θᴹ τ₂ θ̂` (equation 7.166).

## Main results

* `robust_tuning_sigma_lyapunov_hasDerivAt`: closed-loop Lyapunov derivative identity
  `V̇₂ = -k₁ e₁² - k₂ e₂² + σ (θ̃ ⬝ᵥ θ̂)` (equation 7.137).
* `robust_tuning_sigma_deriv_le`: completing-the-square derivative bound
  `V̇₂ ≤ -k₁ e₁² - k₂ e₂² - (σ/2) ‖θ̃‖² + (σ/2) ‖θ‖²` (equation 7.138).
* `robust_tuning_sigma_dissipation_le`: dissipative differential inequality
  `V̇₂ ≤ -c V₂ + d` where `d = (σ/2) (θ ⬝ᵥ θ)` (equation 7.138).
* `robust_tuning_sigma_bound_le_max`: uniform trajectory bound
  `V₂(t) ≤ max (V₂(0)) (d/c)` (Theorem 7.4).
* `robust_tuning_sigma_eventually_bounded`: asymptotic ultimate boundedness
  `V₂(t) < B` for every `B > d/c` (Theorem 7.4).
* `robust_tuning_proj_lyapunov_hasDerivAt`: closed-loop derivative identity under
  projection (equation 7.167).
* `robust_tuning_proj_lyapunov_deriv_le`: non-positive dissipation bound
  `V̇₂ ≤ -k₁ e₁² - k₂ e₂²` via `Proj_sum_nonpos` (equation 7.173, Theorem 7.6).

## References

* J. Kabziński, P. Mosiołek, *Projektowanie nieliniowych układów sterowania*,
  Komitet Automatyki i Robotyki PAN, Monografie tom 22, Chapter 7, Section 7.4.
* P. A. Ioannou, P. V. Kokotović, *Adaptive Systems with Reduced Models*,
  Springer, 1983.
* J.-B. Pomet, L. Praly, *Adaptive nonlinear regulation: Estimation from a
  Lyapunov equation*, IEEE Trans. Automat. Control, 37(6):729–740, 1992.
-/

open scoped Matrix

variable {p : ℕ}

@[expose] public section

/-! ### Definitions -/

/-- Adaptation vector field for robust adaptive backstepping with σ-modification:
`θ̂' = Γ *ᵥ (τ - σ • θ̂)` (Kabziński–Mosiołek, equation 7.136). -/
-- The underscore in `robust_tuning_sigma_adaptation_law` is mandated by the
-- campaign's required-declaration list, so the naming linter is disabled.
@[nolint defsWithUnderscore]
def robust_tuning_sigma_adaptation_law
    (Gamma : Matrix (Fin p) (Fin p) ℝ) (tau : Fin p → ℝ)
    (sigma : ℝ) (theta_hat : Fin p → ℝ) : Fin p → ℝ :=
  Gamma *ᵥ (tau - sigma • theta_hat)

/-- Parameter adaptation vector field for adaptive backstepping with parameter
box projection: `θ̂' = Γ *ᵥ Proj θᵐ θᴹ τ θ̂` (Kabziński–Mosiołek, equation 7.166).
The bound vectors are named `mlo`/`Mhi` to avoid shadowing. -/
-- The underscore in `robust_tuning_proj_adaptation_law` is mandated by the
-- campaign's required-declaration list, so the naming linter is disabled.
@[nolint defsWithUnderscore]
noncomputable def robust_tuning_proj_adaptation_law
    (Gamma : Matrix (Fin p) (Fin p) ℝ) (mlo Mhi : Fin p → ℝ)
    (tau : Fin p → ℝ) (theta_hat : Fin p → ℝ) : Fin p → ℝ :=
  Gamma *ᵥ (Proj mlo Mhi tau theta_hat)

/-! ### Internal calculus and algebra helpers

The calculus and algebra helpers below follow the compact private copies used by
`DynamicalSystems.Control.Adaptive.MRAC`,
`DynamicalSystems.Control.Adaptive.RobustMRAC` and
`DynamicalSystems.Control.Backstepping.Tuning`. -/

/-- Bilinear expansion of the second tuning function:
`θ̃ ⬝ᵥ τ₂ = e₁ (θ̃ ⬝ᵥ ϕ₁) + e₂ (θ̃ ⬝ᵥ z₂)`
(Kabziński–Mosiołek, equations 7.40 and 7.59). -/
private theorem tuning_cross_cancellation
    (e1 e2 : ℝ) (phi1 z2 theta_tilde : Fin p → ℝ) :
    theta_tilde ⬝ᵥ (tuning_tau2 (tuning_tau1 e1 phi1) e2 z2) =
      e1 * (theta_tilde ⬝ᵥ phi1) + e2 * (theta_tilde ⬝ᵥ z2) := by
  simp only [tuning_tau2, tuning_tau1, dotProduct_add, dotProduct_smul, smul_eq_mul]

/-! ### σ-modification theorems -/

/-- Derivative of the composite Lyapunov function `tuning_V2` along closed-loop
trajectories of the adaptive backstepping system with σ-modification:
`V̇₂ = -k₁ e₁² - k₂ e₂² + σ * ((θ - θ̂(t)) ⬝ᵥ θ̂(t))` (Kabziński–Mosiołek,
equation 7.137). -/
theorem robust_tuning_sigma_lyapunov_hasDerivAt
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma : ℝ}
    {e1 e2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi1 z2 : ℝ → (Fin p → ℝ)} {k1 k2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (he1 : HasDerivAt e1 (-k1 * e1 t + e2 t + ((theta - theta_hat t) ⬝ᵥ phi1 t)) t)
    (he2 : HasDerivAt e2 (-e1 t - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ z2 t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_tuning_sigma_adaptation_law Gamma
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) sigma (theta_hat t)) j) t) :
    HasDerivAt (fun s ↦ tuning_V2 Gamma_inv (e1 s) (e2 s) (theta - theta_hat s))
      (-k1 * (e1 t) ^ 2 - k2 * (e2 t) ^ 2 +
        sigma * ((theta - theta_hat t) ⬝ᵥ (theta_hat t))) t := by
  have hdiff : ∀ j, HasDerivAt (fun s ↦ (theta - theta_hat s) j)
      (-(robust_tuning_sigma_adaptation_law Gamma
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) sigma (theta_hat t)) j) t := by
    intro j
    simpa only [Pi.sub_apply] using (htheta_hat j).const_sub (theta j)
  have h1 := (he1.pow 2).const_mul (1 / 2 : ℝ)
  have h2 := (he2.pow 2).const_mul (1 / 2 : ℝ)
  have h3 := hasDerivAt_half_quadratic_form Gamma_inv hGamma_inv_symm hdiff
  have hfun : (fun s ↦ tuning_V2 Gamma_inv (e1 s) (e2 s) (theta - theta_hat s)) =
      (fun s ↦ (1 / 2 : ℝ) * (e1 s) ^ 2 + (1 / 2 : ℝ) * (e2 s) ^ 2
        + (1 / 2 : ℝ) * ((theta - theta_hat s) ⬝ᵥ
            (Gamma_inv *ᵥ (theta - theta_hat s)))) := by
    funext s
    rfl
  rw [hfun]
  refine ((h1.add h2).add h3).congr_deriv ?_
  rw [show (fun j ↦ -(robust_tuning_sigma_adaptation_law Gamma
      (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) sigma (theta_hat t)) j) =
      -(robust_tuning_sigma_adaptation_law Gamma
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) sigma
          (theta_hat t)) from rfl]
  rw [robust_tuning_sigma_adaptation_law,
    adaptation_sigma_cancellation Gamma Gamma_inv
      (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t))
      (theta - theta_hat t) (theta_hat t) sigma hGamma_inv]
  rw [tuning_cross_cancellation (e1 t) (e2 t) (phi1 t) (z2 t) (theta - theta_hat t)]
  ring

/-- Completing-the-square derivative bound for adaptive backstepping with
σ-modification: `V̇₂ ≤ -k₁ e₁² - k₂ e₂² - (σ/2) * ‖θ̃‖² + (σ/2) * ‖θ‖²`
(Kabziński–Mosiołek, equation 7.138). -/
theorem robust_tuning_sigma_deriv_le
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma : ℝ} (hsigma : 0 ≤ sigma)
    {e1 e2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi1 z2 : ℝ → (Fin p → ℝ)} {k1 k2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (he1 : HasDerivAt e1 (-k1 * e1 t + e2 t + ((theta - theta_hat t) ⬝ᵥ phi1 t)) t)
    (he2 : HasDerivAt e2 (-e1 t - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ z2 t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_tuning_sigma_adaptation_law Gamma
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) sigma (theta_hat t)) j) t) :
    deriv (fun s ↦ tuning_V2 Gamma_inv (e1 s) (e2 s) (theta - theta_hat s)) t ≤
      -k1 * (e1 t) ^ 2 - k2 * (e2 t) ^ 2 -
        (sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t)) +
        (sigma / 2) * (theta ⬝ᵥ theta) := by
  have hderiv :=
    robust_tuning_sigma_lyapunov_hasDerivAt hGamma_inv_symm hGamma_inv he1 he2 htheta_hat
  have hcross := robust_mrac_sigma_cross_term_le theta (theta_hat t)
  have hmul := mul_le_mul_of_nonneg_left hcross hsigma
  have hmul' : sigma * (-(1 / 2 : ℝ) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t)) +
        (1 / 2 : ℝ) * (theta ⬝ᵥ theta))
      = -(sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t)) +
        (sigma / 2) * (theta ⬝ᵥ theta) := by
    ring
  rw [hmul'] at hmul
  rw [hderiv.deriv]
  linarith

/-- Dissipation inequality for adaptive backstepping with σ-modification: under a
uniform coercivity/dissipation hypothesis
`c * V₂ ≤ k₁ e₁² + k₂ e₂² + (σ/2) ‖θ̃‖²` with `c > 0`, the Lyapunov derivative
satisfies `V̇₂ ≤ -c * V₂ + d`, where `d = (σ/2) * (θ ⬝ᵥ θ)`
(Kabziński–Mosiołek, equation 7.138). -/
theorem robust_tuning_sigma_dissipation_le
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma c : ℝ} (hsigma : 0 ≤ sigma)
    {e1 e2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi1 z2 : ℝ → (Fin p → ℝ)} {k1 k2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (he1 : HasDerivAt e1 (-k1 * e1 t + e2 t + ((theta - theta_hat t) ⬝ᵥ phi1 t)) t)
    (he2 : HasDerivAt e2 (-e1 t - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ z2 t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_tuning_sigma_adaptation_law Gamma
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) sigma (theta_hat t)) j) t)
    (hdiss : c * tuning_V2 Gamma_inv (e1 t) (e2 t) (theta - theta_hat t) ≤
      k1 * (e1 t) ^ 2 + k2 * (e2 t) ^ 2 +
        (sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t))) :
    deriv (fun s ↦ tuning_V2 Gamma_inv (e1 s) (e2 s) (theta - theta_hat s)) t ≤
      -c * tuning_V2 Gamma_inv (e1 t) (e2 t) (theta - theta_hat t) +
        (sigma / 2) * (theta ⬝ᵥ theta) := by
  have hderiv :=
    robust_tuning_sigma_lyapunov_hasDerivAt hGamma_inv_symm hGamma_inv he1 he2 htheta_hat
  have hcross := robust_mrac_sigma_cross_term_le theta (theta_hat t)
  have hmul := mul_le_mul_of_nonneg_left hcross hsigma
  have hmul' : sigma * (-(1 / 2 : ℝ) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t)) +
        (1 / 2 : ℝ) * (theta ⬝ᵥ theta))
      = -(sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t)) +
        (sigma / 2) * (theta ⬝ᵥ theta) := by
    ring
  rw [hmul'] at hmul
  rw [hderiv.deriv]
  linarith

/-- Uniform trajectory boundedness of the composite backstepping state under
σ-modification: for all `t ≥ 0`, `V₂(t) ≤ max (V₂(0)) (d / c)` where
`d = (σ/2) * (θ ⬝ᵥ θ)` (Kabziński–Mosiołek, Theorem 7.4). -/
theorem robust_tuning_sigma_bound_le_max
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma c : ℝ} (hc : 0 < c) (hsigma : 0 ≤ sigma)
    {e1 e2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi1 z2 : ℝ → (Fin p → ℝ)} {k1 k2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    (he1 : ∀ t ≥ 0, HasDerivAt e1 (-k1 * e1 t + e2 t + ((theta - theta_hat t) ⬝ᵥ phi1 t)) t)
    (he2 : ∀ t ≥ 0, HasDerivAt e2 (-e1 t - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ z2 t)) t)
    (htheta_hat : ∀ t ≥ 0, ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_tuning_sigma_adaptation_law Gamma
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) sigma (theta_hat t)) j) t)
    (hdiss : ∀ t ≥ 0, c * tuning_V2 Gamma_inv (e1 t) (e2 t) (theta - theta_hat t) ≤
      k1 * (e1 t) ^ 2 + k2 * (e2 t) ^ 2 +
        (sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t))) :
    let d := (sigma / 2) * (theta ⬝ᵥ theta)
    ∀ t ≥ 0, tuning_V2 Gamma_inv (e1 t) (e2 t) (theta - theta_hat t) ≤
      max (tuning_V2 Gamma_inv (e1 0) (e2 0) (theta - theta_hat 0)) (d / c) := by
  dsimp only
  intro t ht
  let v : ℝ → ℝ := fun s ↦ tuning_V2 Gamma_inv (e1 s) (e2 s) (theta - theta_hat s)
  have hderiv : ∀ s, 0 ≤ s → HasDerivAt v (deriv v s) s := by
    intro s hs
    have h := robust_tuning_sigma_lyapunov_hasDerivAt hGamma_inv_symm hGamma_inv
      (he1 s hs) (he2 s hs) (htheta_hat s hs)
    exact h.congr_deriv h.deriv.symm
  have hineq : ∀ s, 0 ≤ s → deriv v s ≤ -(c * v s) + (sigma / 2) * (theta ⬝ᵥ theta) := by
    intro s hs
    have h := robust_tuning_sigma_dissipation_le (hsigma := hsigma) hGamma_inv_symm hGamma_inv
      (he1 s hs) (he2 s hs) (htheta_hat s hs) (hdiss s hs)
    simpa only [v, neg_mul] using h
  have hbound := le_gronwallBound_of_hasDerivAt_le hc hderiv hineq t ht
  have hmax := gronwall_bound_le_max (v 0) c ((sigma / 2) * (theta ⬝ᵥ theta)) t hc ht
  simpa only [v] using hbound.trans hmax

/-- Asymptotic ultimate boundedness of adaptive backstepping with σ-modification:
for any target level `B > d / c` with `d = (σ/2) * (θ ⬝ᵥ θ)`, the Lyapunov
function `V₂(t)` eventually drops strictly below `B` (Kabziński–Mosiołek,
Theorem 7.4). -/
theorem robust_tuning_sigma_eventually_bounded
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma c B : ℝ} (hc : 0 < c) (hsigma : 0 ≤ sigma)
    {e1 e2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi1 z2 : ℝ → (Fin p → ℝ)} {k1 k2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    (he1 : ∀ t ≥ 0, HasDerivAt e1 (-k1 * e1 t + e2 t + ((theta - theta_hat t) ⬝ᵥ phi1 t)) t)
    (he2 : ∀ t ≥ 0, HasDerivAt e2 (-e1 t - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ z2 t)) t)
    (htheta_hat : ∀ t ≥ 0, ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_tuning_sigma_adaptation_law Gamma
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) sigma (theta_hat t)) j) t)
    (hdiss : ∀ t ≥ 0, c * tuning_V2 Gamma_inv (e1 t) (e2 t) (theta - theta_hat t) ≤
      k1 * (e1 t) ^ 2 + k2 * (e2 t) ^ 2 +
        (sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t)))
    (hB : (sigma / 2) * (theta ⬝ᵥ theta) / c < B) :
    ∀ᶠ t in Filter.atTop, tuning_V2 Gamma_inv (e1 t) (e2 t) (theta - theta_hat t) < B := by
  let v : ℝ → ℝ := fun s ↦ tuning_V2 Gamma_inv (e1 s) (e2 s) (theta - theta_hat s)
  have hderiv : ∀ s, 0 ≤ s → HasDerivAt v (deriv v s) s := by
    intro s hs
    have h := robust_tuning_sigma_lyapunov_hasDerivAt hGamma_inv_symm hGamma_inv
      (he1 s hs) (he2 s hs) (htheta_hat s hs)
    exact h.congr_deriv h.deriv.symm
  have hineq : ∀ s, 0 ≤ s → deriv v s ≤ -(c * v s) + (sigma / 2) * (theta ⬝ᵥ theta) := by
    intro s hs
    have h := robust_tuning_sigma_dissipation_le (hsigma := hsigma) hGamma_inv_symm hGamma_inv
      (he1 s hs) (he2 s hs) (htheta_hat s hs) (hdiss s hs)
    simpa only [v, neg_mul] using h
  have := eventually_lt_of_hasDerivAt_le_neg_mul_add (v := v)
    (d := (sigma / 2) * (theta ⬝ᵥ theta)) hc hB hderiv hineq
  simpa only [v] using this

/-! ### Parameter box projection theorems -/

/-- Derivative of `tuning_V2` along closed-loop trajectories of the adaptive
backstepping system with parameter box projection:
`V̇₂ = -k₁ e₁² - k₂ e₂² + (θ - θ̂(t)) ⬝ᵥ (τ₂(t) - Proj θᵐ θᴹ τ₂(t) θ̂(t))`
(Kabziński–Mosiołek, equation 7.167). -/
theorem robust_tuning_proj_lyapunov_hasDerivAt
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {mlo Mhi : Fin p → ℝ} {theta : Fin p → ℝ}
    {e1 e2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi1 z2 : ℝ → (Fin p → ℝ)} {k1 k2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (he1 : HasDerivAt e1 (-k1 * e1 t + e2 t + ((theta - theta_hat t) ⬝ᵥ phi1 t)) t)
    (he2 : HasDerivAt e2 (-e1 t - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ z2 t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_tuning_proj_adaptation_law Gamma mlo Mhi
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) (theta_hat t)) j) t) :
    let tau2 := tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)
    HasDerivAt (fun s ↦ tuning_V2 Gamma_inv (e1 s) (e2 s) (theta - theta_hat s))
      (-k1 * (e1 t) ^ 2 - k2 * (e2 t) ^ 2 +
        (theta - theta_hat t) ⬝ᵥ (tau2 - Proj mlo Mhi tau2 (theta_hat t))) t := by
  dsimp only
  have hdiff : ∀ j, HasDerivAt (fun s ↦ (theta - theta_hat s) j)
      (-(robust_tuning_proj_adaptation_law Gamma mlo Mhi
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) (theta_hat t)) j) t := by
    intro j
    simpa only [Pi.sub_apply] using (htheta_hat j).const_sub (theta j)
  have h1 := (he1.pow 2).const_mul (1 / 2 : ℝ)
  have h2 := (he2.pow 2).const_mul (1 / 2 : ℝ)
  have h3 := hasDerivAt_half_quadratic_form Gamma_inv hGamma_inv_symm hdiff
  have hfun : (fun s ↦ tuning_V2 Gamma_inv (e1 s) (e2 s) (theta - theta_hat s)) =
      (fun s ↦ (1 / 2 : ℝ) * (e1 s) ^ 2 + (1 / 2 : ℝ) * (e2 s) ^ 2
        + (1 / 2 : ℝ) * ((theta - theta_hat s) ⬝ᵥ
            (Gamma_inv *ᵥ (theta - theta_hat s)))) := by
    funext s
    rfl
  rw [hfun]
  refine ((h1.add h2).add h3).congr_deriv ?_
  rw [show (fun j ↦ -(robust_tuning_proj_adaptation_law Gamma mlo Mhi
      (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) (theta_hat t)) j) =
      -(robust_tuning_proj_adaptation_law Gamma mlo Mhi
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) (theta_hat t)) from rfl]
  rw [robust_tuning_proj_adaptation_law,
    adaptation_proj_cancellation Gamma Gamma_inv mlo Mhi
      (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) (theta - theta_hat t)
      (theta_hat t) hGamma_inv]
  rw [dotProduct_sub, tuning_cross_cancellation (e1 t) (e2 t) (phi1 t) (z2 t)
    (theta - theta_hat t)]
  ring

/-- Under the true parameter box bounds `mlo ≤ θ ≤ Mhi`, the parameter error cross
term is non-positive by `Proj_sum_nonpos`, so the Lyapunov derivative satisfies
`V̇₂ ≤ -k₁ e₁² - k₂ e₂²` (Kabziński–Mosiołek, equation 7.173 and Theorem 7.6). -/
theorem robust_tuning_proj_lyapunov_deriv_le
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {mlo Mhi : Fin p → ℝ} {theta : Fin p → ℝ}
    (hm : ∀ k, mlo k ≤ theta k) (hM : ∀ k, theta k ≤ Mhi k)
    {e1 e2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi1 z2 : ℝ → (Fin p → ℝ)} {k1 k2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (he1 : HasDerivAt e1 (-k1 * e1 t + e2 t + ((theta - theta_hat t) ⬝ᵥ phi1 t)) t)
    (he2 : HasDerivAt e2 (-e1 t - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ z2 t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_tuning_proj_adaptation_law Gamma mlo Mhi
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t)) (theta_hat t)) j) t) :
    deriv (fun s ↦ tuning_V2 Gamma_inv (e1 s) (e2 s) (theta - theta_hat s)) t ≤
      -k1 * (e1 t) ^ 2 - k2 * (e2 t) ^ 2 := by
  have h :=
    robust_tuning_proj_lyapunov_hasDerivAt hGamma_inv_symm hGamma_inv he1 he2 htheta_hat
  dsimp only at h
  have hproj : (theta - theta_hat t) ⬝ᵥ
      (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t) -
        Proj mlo Mhi (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t))
          (theta_hat t)) ≤ 0 := by
    simpa only [dotProduct, Pi.sub_apply] using
      Proj_sum_nonpos (m := mlo) (M := Mhi)
        (y := tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t))
        (theta := theta) (thetaHat := theta_hat t) hm hM
  rw [h.deriv]
  linarith
