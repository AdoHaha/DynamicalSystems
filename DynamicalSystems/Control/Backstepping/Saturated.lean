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
public import DynamicalSystems.Stability.Barbalat
public import DynamicalSystems.Stability.Comparison
public import DynamicalSystems.Stability.UltimateBoundedness
public import DynamicalSystems.Stability.Projection
public import DynamicalSystems.Control.Adaptive.RobustMRAC

/-!
# Adaptive backstepping with actuator saturation and anti-windup

This file formalizes the second-order saturated adaptive backstepping design with an
anti-windup auxiliary state, following Kabziński and Mosiołek,
*Projektowanie nieliniowych układów sterowania*, Komitet Automatyki i Robotyki PAN,
Monografie tom 22, Chapter 10, Sections 10.1–10.2, pages 181–187, Theorem 10.1,
equations (10.1)–(10.49).

## System description

The plant is the second-order strict-feedback system with actuator saturation
```
x₁' = x₂
x₂' = sat_U(v) + ϕ(x₁, x₂)ᵀ θ
```
where `θ ∈ ℝᵖ` is an unknown constant parameter vector, `ϕ ∈ ℝᵖ` is a known regressor,
`v` is the synthesized command and `sat_U` is the hard saturation operator (10.4). The
online saturation discrepancy is `Δ = sat_U(v) - v` (10.7), and the design drives the
anti-windup auxiliary filter
`p₁' = p₂ - c₁ p₁`, `p₂' = Δ - c₂ p₂` (10.8)–(10.10).

The tracking errors `e₁ = x₁ - x₁d`, `e₂ = x₂ - α₁ - x₁d'` are replaced by the auxiliary
coordinates `z₁ = e₁ - p₁`, `z₂ = e₂ - p₂` (10.11)–(10.12). With the stabilizing function
`α₁ = -c₁ e₁` (10.17) and the command `v = -θ̂ ⬝ᵥ ϕ + x₁d'' - c₂ e₂ + α₁'` (10.38), the
saturation discrepancy cancels identically along closed-loop trajectories and the cascade
```
z₁' = -c₁ z₁ + z₂,   z₂' = -c₂ z₂ + θ̃ ⬝ᵥ ϕ
```
(10.18) and (10.41) is recovered. The composite Lyapunov candidate
`V_z = (1/2) z₁² + (1/2) z₂² + (1/2) θ̃ ᵀΓ⁻¹θ̃` (10.35) then satisfies, for
`c₁ > 1/2` and `c₂ > 1/2`,
```
V_z' ≤ -(c₁ - 1/2) z₁² - (c₂ - 1/2) z₂² ≤ 0
```
by Young's inequality (10.19), (10.43), giving asymptotic convergence `z₁, z₂ → 0`
(Theorem 10.1) via the LaSalle–Yoshizawa / Barbălat bridge.

Robust variants using parameter-box projection and σ-modification (Section 10.4) are
also provided, together with the time-domain tracking reconstruction
`|e₁| ≤ |z₁| + |p₁|` of Corollary 10.1.

## Main definitions

* `sat`, `satDelta`: the saturation operator (10.4) and the discrepancy (10.7).
* `saturated_alpha1`, `saturated_control`: the stabilizing function (10.17) and the
  command (10.38).
* `saturated_filter_ode1`, `saturated_filter_ode2`: the anti-windup filter vector fields
  (10.8) and (10.10).
* `saturated_adaptation_law`, `saturated_proj_adaptation_law`,
  `saturated_sigma_adaptation_law`: nominal (10.42), projected and σ-modified adaptation
  vector fields.
* `saturated_Vz`: the composite quadratic Lyapunov candidate (10.35).

## Main results

* `saturated_z1_hasDerivAt`, `saturated_z2_hasDerivAt`: the closed-loop cascade
  (10.18) and (10.41), exhibiting the exact cancellation of the saturation discrepancy.
* `saturated_cross_term_bound`: Young's-inequality bound (10.19).
* `saturated_Vz_hasDerivAt`, `saturated_Vz_deriv_le`: the Lyapunov derivative identity
  and dissipation inequality (10.40), (10.43).
* `saturated_dissipation_tendsto_zero`, `saturated_tracking_tendsto_zero`: Theorem 10.1.
* `saturated_proj_lyapunov_deriv_le`, `saturated_sigma_dissipation_le`,
  `saturated_sigma_bound_le_max`, `saturated_sigma_eventually_bounded`: robust variants.
* `saturated_error_le`, `saturated_nominal_tracking_tendsto_zero`: Corollary 10.1's
  time-domain tracking reconstruction.

## References

* J. Kabziński, P. Mosiołek, *Projektowanie nieliniowych układów sterowania*,
  Komitet Automatyki i Robotyki PAN, Monografie tom 22, Chapter 10.
-/

open scoped Matrix

variable {p : ℕ}

@[expose] public section

/-! ### Actuator saturation operator

For `U ≥ 0`, `sat U` is the hard saturation operator of (10.4): it clamps its argument to
the interval `[-U, U]`. We define it as the composition `min U ∘ max (-U)` of the two
clamps, which agrees with (10.4) on the entire physically meaningful range `U ≥ 0` and,
unlike the raw case distinction, is continuous in the argument for every `U`. -/

/-- Hard actuator saturation operator `sat U v` (Kabziński–Mosiołek, equation 10.4).
For the saturation bound `U ≥ 0` it is `min U (max (-U) v)`, i.e. `sign v * U` for
`|v| ≥ U` and `v` otherwise. -/
def sat (U v : ℝ) : ℝ :=
  min U (max (-U) v)

/-- Online actuator saturation discrepancy `satDelta U v = sat U v - v`
(Kabziński–Mosiołek, equation 10.7), the unapplied control effort. -/
def satDelta (U v : ℝ) : ℝ :=
  sat U v - v

/-- Pointwise bound: `|sat U v| ≤ U` for a nonnegative saturation bound `U`
(Kabziński–Mosiołek, equation 10.4). -/
theorem sat_abs_le (U v : ℝ) (hU : 0 ≤ U) : |sat U v| ≤ U := by
  rw [sat, abs_le]
  constructor
  · exact le_min (by linarith) (le_max_left _ _)
  · exact min_le_left _ _

/-- Exact passthrough on the linear operating region: if `|v| ≤ U`, then `sat U v = v`
(Kabziński–Mosiołek, equation 10.4). -/
theorem sat_eq_self (U v : ℝ) (h : |v| ≤ U) : sat U v = v := by
  rw [abs_le] at h
  rw [sat, max_eq_right h.1, min_eq_right h.2]

/-- Discrepancy support: if `|v| ≤ U`, then the saturation discrepancy vanishes
(Kabziński–Mosiołek, equation 10.7). -/
theorem satDelta_eq_zero (U v : ℝ) (h : |v| ≤ U) : satDelta U v = 0 := by
  rw [satDelta, sat_eq_self U v h, sub_self]

/-- Algebraic decomposition: `sat U v = v + satDelta U v`
(Kabziński–Mosiołek, equation 10.7). -/
theorem sat_decomposition (U v : ℝ) : sat U v = v + satDelta U v := by
  rw [satDelta]
  ring

/-- Fundamental sign property of saturation: `v * satDelta U v ≤ 0` for `U ≥ 0`.
Actuator saturation never acts in the direction of increasing `|v|`
(Kabziński–Mosiołek, equation 10.7). -/
theorem mul_satDelta_nonpos (U v : ℝ) (hU : 0 ≤ U) : v * satDelta U v ≤ 0 := by
  rw [satDelta, sat]
  by_cases hv : v ≤ U
  · by_cases hv2 : -U ≤ v
    · rw [max_eq_right hv2, min_eq_right hv, sub_self, mul_zero]
    · rw [max_eq_left (le_of_lt (not_le.mp hv2)), min_eq_right (by linarith)]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [not_le.mp hv2])
        (by linarith [not_le.mp hv2])
  · rw [max_eq_right (by linarith [not_le.mp hv]), min_eq_left (le_of_lt (not_le.mp hv))]
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hU, not_le.mp hv])
      (by linarith [not_le.mp hv])

/-- Continuity of the saturation operator on `ℝ` (Kabziński–Mosiołek, equation 10.4). -/
theorem sat_continuous (U : ℝ) : Continuous (sat U) := by
  unfold sat
  fun_prop

/-! ### Anti-windup filter and saturated control law -/

/-- Virtual stabilizing control `α₁ = -c₁ e₁` (Kabziński–Mosiołek, equation 10.17). -/
-- The underscore is mandated by the campaign's required-declaration list.
@[nolint defsWithUnderscore]
def saturated_alpha1 (c1 e1 : ℝ) : ℝ :=
  -c1 * e1

/-- First anti-windup auxiliary filter vector field `p₁' = p₂ - c₁ p₁`
(Kabziński–Mosiołek, equation 10.8). -/
-- The underscore is mandated by the campaign's required-declaration list.
@[nolint defsWithUnderscore]
def saturated_filter_ode1 (c1 p1 p2 : ℝ) : ℝ :=
  p2 - c1 * p1

/-- Second anti-windup auxiliary filter vector field `p₂' = Δ - c₂ p₂` with
`Δ = satDelta U v` (Kabziński–Mosiołek, equation 10.10 for `n = 2`). -/
-- The underscore is mandated by the campaign's required-declaration list.
@[nolint defsWithUnderscore]
def saturated_filter_ode2 (c2 U p2 v : ℝ) : ℝ :=
  satDelta U v - c2 * p2

/-- Saturated backstepping command `v` before actuator limitation:
`v = -θ̂ ⬝ᵥ ϕ + x₁d'' - c₂ e₂ + α₁'` (Kabziński–Mosiołek, equations 10.38 and 10.39). -/
-- The underscore is mandated by the campaign's required-declaration list.
@[nolint defsWithUnderscore]
def saturated_control
    (c2 : ℝ) (e2 : ℝ) (theta_hat phi : Fin p → ℝ) (xd'' : ℝ) (alpha1' : ℝ) : ℝ :=
  -(theta_hat ⬝ᵥ phi) + xd'' - c2 * e2 + alpha1'

/-- Nominal parameter adaptation vector field `θ̂' = Γ *ᵥ (z₂ • ϕ)`
(Kabziński–Mosiołek, equation 10.42). -/
-- The underscore is mandated by the campaign's required-declaration list.
@[nolint defsWithUnderscore]
def saturated_adaptation_law
    (Gamma : Matrix (Fin p) (Fin p) ℝ) (z2 : ℝ) (phi : Fin p → ℝ) : Fin p → ℝ :=
  Gamma *ᵥ (z2 • phi)

/-- Projected parameter adaptation vector field `θ̂' = Γ *ᵥ Proj θᵐ θᴹ (z₂ • ϕ) θ̂`
(Kabziński–Mosiołek, Section 10.4). -/
-- The underscore is mandated by the campaign's required-declaration list.
@[nolint defsWithUnderscore]
noncomputable def saturated_proj_adaptation_law
    (Gamma : Matrix (Fin p) (Fin p) ℝ) (mlo Mhi : Fin p → ℝ)
    (z2 : ℝ) (phi : Fin p → ℝ) (theta_hat : Fin p → ℝ) : Fin p → ℝ :=
  Gamma *ᵥ (Proj mlo Mhi (z2 • phi) theta_hat)

/-- σ-modified parameter adaptation vector field `θ̂' = Γ *ᵥ (z₂ • ϕ - σ • θ̂)`
(Kabziński–Mosiołek, Section 10.4). -/
-- The underscore is mandated by the campaign's required-declaration list.
@[nolint defsWithUnderscore]
def saturated_sigma_adaptation_law
    (Gamma : Matrix (Fin p) (Fin p) ℝ) (z2 : ℝ) (phi : Fin p → ℝ)
    (sigma : ℝ) (theta_hat : Fin p → ℝ) : Fin p → ℝ :=
  Gamma *ᵥ (z2 • phi - sigma • theta_hat)

/-- Composite quadratic Lyapunov candidate for saturated backstepping:
`V_z(z₁, z₂, θ̃) = (1/2) z₁² + (1/2) z₂² + (1/2) θ̃ ᵀΓ⁻¹θ̃`
(Kabziński–Mosiołek, equations 10.16, 10.22 and 10.35). -/
-- The underscore is mandated by the campaign's required-declaration list.
@[nolint defsWithUnderscore]
noncomputable def saturated_Vz
    (Gamma_inv : Matrix (Fin p) (Fin p) ℝ) (z1 z2 : ℝ)
    (theta_tilde : Fin p → ℝ) : ℝ :=
  tuning_V2 Gamma_inv z1 z2 theta_tilde

/-! ### Internal calculus and algebra helpers

The calculus and algebra helpers below follow the compact private copies used by
`DynamicalSystems.Control.Adaptive.MRAC`,
`DynamicalSystems.Control.Adaptive.RobustMRAC`,
`DynamicalSystems.Control.Backstepping.Tuning` and
`DynamicalSystems.Control.Backstepping.Robust`. -/

/-- The composite Lyapunov candidate `saturated_Vz` is nonnegative when `Γ⁻¹` is positive
definite. -/
private theorem saturated_Vz_nonneg {Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    (hG : Gamma_inv.PosDef) (z1 z2 : ℝ) (theta_tilde : Fin p → ℝ) :
    0 ≤ saturated_Vz Gamma_inv z1 z2 theta_tilde := by
  have h1 : 0 ≤ z1 ^ 2 := sq_nonneg z1
  have h2 : 0 ≤ z2 ^ 2 := sq_nonneg z2
  have h3 := posDef_dotProduct_nonneg hG theta_tilde
  simp only [saturated_Vz, tuning_V2]
  nlinarith [h1, h2, h3]

/-- Common core of the closed-loop Lyapunov derivative identities: for any vector field
`w` representing the derivative of the parameter error `θ̃ = θ - θ̂`, the derivative of the
composite candidate `saturated_Vz` along the saturated cascade is
`-c₁ z₁² + z₁ z₂ - c₂ z₂² + z₂ (θ̃ ⬝ᵥ ϕ) + θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ w)`. -/
private theorem saturated_Vz_adaptation_hasDerivAt
    {Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ}
    {z1 z2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi : ℝ → (Fin p → ℝ)} {w : Fin p → ℝ} {c1 c2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    {t : ℝ}
    (hz1 : HasDerivAt z1 (-c1 * z1 t + z2 t) t)
    (hz2 : HasDerivAt z2 (-c2 * z2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (hdiff : ∀ j, HasDerivAt (fun s ↦ (theta - theta_hat s) j) (w j) t) :
    HasDerivAt (fun s ↦ saturated_Vz Gamma_inv (z1 s) (z2 s) (theta - theta_hat s))
      (-c1 * z1 t ^ 2 + z1 t * z2 t - c2 * z2 t ^ 2 +
        z2 t * ((theta - theta_hat t) ⬝ᵥ phi t) +
        (theta - theta_hat t) ⬝ᵥ (Gamma_inv *ᵥ w)) t := by
  have h1 := (hz1.pow 2).const_mul (1 / 2 : ℝ)
  have h2 := (hz2.pow 2).const_mul (1 / 2 : ℝ)
  have h3 := hasDerivAt_half_quadratic_form Gamma_inv hGamma_inv_symm hdiff
  have hfun : (fun s ↦ saturated_Vz Gamma_inv (z1 s) (z2 s) (theta - theta_hat s)) =
      (fun s ↦ (1 / 2 : ℝ) * (z1 s) ^ 2 + (1 / 2 : ℝ) * (z2 s) ^ 2
        + (1 / 2 : ℝ) * ((theta - theta_hat s) ⬝ᵥ
            (Gamma_inv *ᵥ (theta - theta_hat s)))) := by
    funext s
    rfl
  rw [hfun]
  refine ((h1.add h2).add h3).congr_deriv ?_
  ring_nf

/-! ### Closed-loop dynamics and Lyapunov dissipation -/

/-- Closed-loop derivative of the first auxiliary error coordinate `z₁ = e₁ - p₁`:
`z₁' = -c₁ z₁ + z₂` (Kabziński–Mosiołek, equation 10.18). The coupling term `c₁ p₁` of the
filter cancels against the stabilizing function `α₁ = -c₁ (z₁ + p₁)`. -/
theorem saturated_z1_hasDerivAt
    {c1 : ℝ} {e1 e2 p1 p2 : ℝ → ℝ} {t : ℝ}
    (he1 : HasDerivAt e1 (e2 t - c1 * e1 t) t)
    (hp1 : HasDerivAt p1 (saturated_filter_ode1 c1 (p1 t) (p2 t)) t) :
    HasDerivAt (fun s ↦ (e1 s - p1 s)) (-c1 * (e1 t - p1 t) + (e2 t - p2 t)) t := by
  refine (he1.sub hp1).congr_deriv ?_
  simp only [saturated_filter_ode1]
  ring

/-- Closed-loop derivative of the second auxiliary error coordinate `z₂ = e₂ - p₂`:
`z₂' = -c₂ z₂ + θ̃ ⬝ᵥ ϕ` (Kabziński–Mosiołek, equation 10.41). The saturation discrepancy
`satDelta U v` driving the filter cancels the saturated input `sat U v` of the plant
identically. -/
theorem saturated_z2_hasDerivAt
    {c2 U : ℝ} {theta : Fin p → ℝ}
    {e2 p2 : ℝ → ℝ} {theta_hat phi : ℝ → (Fin p → ℝ)}
    {xd'' alpha1' : ℝ → ℝ} {t : ℝ}
    (he2 : HasDerivAt e2
      (sat U (saturated_control c2 (e2 t) (theta_hat t) (phi t) (xd'' t) (alpha1' t)) +
        (theta ⬝ᵥ phi t) - alpha1' t - xd'' t) t)
    (hp2 : HasDerivAt p2
      (saturated_filter_ode2 c2 U (p2 t)
        (saturated_control c2 (e2 t) (theta_hat t) (phi t) (xd'' t) (alpha1' t))) t) :
    HasDerivAt (fun s ↦ (e2 s - p2 s))
      (-c2 * (e2 t - p2 t) + ((theta - theta_hat t) ⬝ᵥ phi t)) t := by
  refine (he2.sub hp2).congr_deriv ?_
  simp only [saturated_filter_ode2, saturated_control, satDelta, sub_dotProduct]
  ring

/-- Young's-inequality cross-term bound for the upper-triangular anti-windup cascade:
`-c₁ z₁² + z₁ z₂ - c₂ z₂² ≤ -(c₁ - 1/2) z₁² - (c₂ - 1/2) z₂²`
(Kabziński–Mosiołek, equations 10.19 and 10.43), proved from `(1/2) (z₁ - z₂)² ≥ 0`. -/
theorem saturated_cross_term_bound (c1 c2 z1 z2 : ℝ) :
    -c1 * z1 ^ 2 + z1 * z2 - c2 * z2 ^ 2 ≤
      -(c1 - 1 / 2) * z1 ^ 2 - (c2 - 1 / 2) * z2 ^ 2 := by
  nlinarith [sq_nonneg (z1 - z2)]

/-- Derivative of the composite Lyapunov function `saturated_Vz` along closed-loop
trajectories of the saturated adaptive backstepping system with the nominal adaptation law
`θ̂' = Γ *ᵥ (z₂ • ϕ)`: `V̇_z = -c₁ z₁² + z₁ z₂ - c₂ z₂²` (Kabziński–Mosiołek,
equation 10.40). The parameter error terms cancel exactly via the adaptation law and
`Γ⁻¹ * Γ = 1`. -/
theorem saturated_Vz_hasDerivAt
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ}
    {z1 z2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi : ℝ → (Fin p → ℝ)} {c1 c2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (hz1 : HasDerivAt z1 (-c1 * z1 t + z2 t) t)
    (hz2 : HasDerivAt z2 (-c2 * z2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((saturated_adaptation_law Gamma (z2 t) (phi t)) j) t) :
    HasDerivAt (fun s ↦ saturated_Vz Gamma_inv (z1 s) (z2 s) (theta - theta_hat s))
      (-c1 * (z1 t) ^ 2 + z1 t * z2 t - c2 * (z2 t) ^ 2) t := by
  have hdiff : ∀ j, HasDerivAt (fun s ↦ (theta - theta_hat s) j)
      ((-(saturated_adaptation_law Gamma (z2 t) (phi t))) j) t := by
    intro j
    simpa only [Pi.sub_apply, Pi.neg_apply] using (htheta_hat j).const_sub (theta j)
  have h := saturated_Vz_adaptation_hasDerivAt
    (w := -(saturated_adaptation_law Gamma (z2 t) (phi t)))
    hGamma_inv_symm hz1 hz2 hdiff
  refine h.congr_deriv ?_
  rw [saturated_adaptation_law,
    adaptation_cancellation Gamma Gamma_inv ((z2 t) • (phi t))
      (theta - theta_hat t) hGamma_inv]
  simp only [dotProduct_smul, smul_eq_mul]
  ring

/-- Upper-triangular dissipation bound: under the nominal adaptation law,
`V̇_z ≤ -(c₁ - 1/2) z₁² - (c₂ - 1/2) z₂²` (Kabziński–Mosiołek, equation 10.43). -/
theorem saturated_Vz_deriv_le
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ}
    {z1 z2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi : ℝ → (Fin p → ℝ)} {c1 c2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (hz1 : HasDerivAt z1 (-c1 * z1 t + z2 t) t)
    (hz2 : HasDerivAt z2 (-c2 * z2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((saturated_adaptation_law Gamma (z2 t) (phi t)) j) t) :
    deriv (fun s ↦ saturated_Vz Gamma_inv (z1 s) (z2 s) (theta - theta_hat s)) t ≤
      -(c1 - 1 / 2) * (z1 t) ^ 2 - (c2 - 1 / 2) * (z2 t) ^ 2 := by
  have h := saturated_Vz_hasDerivAt hGamma_inv_symm hGamma_inv hz1 hz2 htheta_hat
  rw [h.deriv]
  exact saturated_cross_term_bound c1 c2 (z1 t) (z2 t)

/-- Convergence of the dissipation rate `(c₁ - 1/2) z₁² + (c₂ - 1/2) z₂² → 0` as `t → ∞`
under Kabziński's gain conditions `c₁ > 1/2`, `c₂ > 1/2`, via the LaSalle–Yoshizawa /
Barbălat bridge (Kabziński–Mosiołek, Theorem 10.1). The composite candidate `saturated_Vz`
is nonnegative and nonincreasing with `V̇_z ≤ -w`, and `w` is uniformly continuous. -/
theorem saturated_dissipation_tendsto_zero
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ}
    {z1 z2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi : ℝ → (Fin p → ℝ)} {c1 c2 : ℝ}
    (hGamma_inv_pd : Gamma_inv.PosDef)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    (hc1 : 1 / 2 < c1) (hc2 : 1 / 2 < c2)
    (hz1 : ∀ t ≥ 0, HasDerivAt z1 (-c1 * z1 t + z2 t) t)
    (hz2 : ∀ t ≥ 0, HasDerivAt z2 (-c2 * z2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (htheta_hat : ∀ t ≥ 0, ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((saturated_adaptation_law Gamma (z2 t) (phi t)) j) t)
    (huc : UniformContinuousOn
      (fun t ↦ (c1 - 1 / 2) * (z1 t) ^ 2 + (c2 - 1 / 2) * (z2 t) ^ 2) (Set.Ici 0)) :
    Filter.Tendsto (fun t ↦ (c1 - 1 / 2) * (z1 t) ^ 2 + (c2 - 1 / 2) * (z2 t) ^ 2)
      Filter.atTop (nhds 0) := by
  let V : ℝ → ℝ := fun t ↦ saturated_Vz Gamma_inv (z1 t) (z2 t) (theta - theta_hat t)
  let w : ℝ → ℝ := fun t ↦ (c1 - 1 / 2) * (z1 t) ^ 2 + (c2 - 1 / 2) * (z2 t) ^ 2
  have hG_symm : Gamma_invᵀ = Gamma_inv := posDef_transpose_eq hGamma_inv_pd
  have hw_nonneg : ∀ t, 0 ≤ t → 0 ≤ w t := by
    intro t _
    have h1 : 0 ≤ (c1 - 1 / 2) * (z1 t) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h2 : 0 ≤ (c2 - 1 / 2) * (z2 t) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    dsimp only [w]
    linarith
  have hBdd : BddBelow (V '' Set.Ici 0) := by
    refine ⟨0, ?_⟩
    rintro y ⟨t, _ht, rfl⟩
    exact saturated_Vz_nonneg hGamma_inv_pd (z1 t) (z2 t) (theta - theta_hat t)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt V (deriv V t) t := by
    intro t ht
    have h := saturated_Vz_hasDerivAt hG_symm hGamma_inv (hz1 t ht) (hz2 t ht) (htheta_hat t ht)
    exact h.congr_deriv h.deriv.symm
  have hineq : ∀ t, 0 ≤ t → deriv V t ≤ -(w t) := by
    intro t ht
    have h := saturated_Vz_deriv_le hG_symm hGamma_inv (hz1 t ht) (hz2 t ht) (htheta_hat t ht)
    have hw : w t = (c1 - 1 / 2) * (z1 t) ^ 2 + (c2 - 1 / 2) * (z2 t) ^ 2 := rfl
    change deriv (fun s ↦ saturated_Vz Gamma_inv (z1 s) (z2 s) (theta - theta_hat s)) t ≤ -(w t)
    rw [hw]
    linarith
  simpa only [w] using
    Barbalat.tendsto_zero_of_hasDerivAt_le_neg_of_boundedBelow_of_uniformContinuousOn
      hBdd hw_nonneg hderiv hineq huc

/-- Theorem 10.1: asymptotic convergence of the auxiliary tracking errors. Under the gain
conditions `c₁ > 1/2`, `c₂ > 1/2` and convergence of the diagonal dissipation rate, both
coordinates converge to zero, `z₁(t) → 0` and `z₂(t) → 0` as `t → ∞`. -/
theorem saturated_tracking_tendsto_zero
    {z1 z2 : ℝ → ℝ} {c1 c2 : ℝ}
    (hc1 : 1 / 2 < c1) (hc2 : 1 / 2 < c2)
    (hw : Filter.Tendsto
      (fun t ↦ (c1 - 1 / 2) * (z1 t) ^ 2 + (c2 - 1 / 2) * (z2 t) ^ 2)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto z1 Filter.atTop (nhds 0) ∧ Filter.Tendsto z2 Filter.atTop (nhds 0) := by
  constructor
  · refine Barbalat.tendsto_zero_of_tendsto_zero_of_sq_le (c := c1 - 1 / 2)
      (sub_pos.mpr hc1) hw ?_
    intro t _
    have h2 : 0 ≤ (c2 - 1 / 2) * (z2 t) ^ 2 := mul_nonneg (sub_pos.mpr hc2).le (sq_nonneg _)
    linarith
  · refine Barbalat.tendsto_zero_of_tendsto_zero_of_sq_le (c := c2 - 1 / 2)
      (sub_pos.mpr hc2) hw ?_
    intro t _
    have h1 : 0 ≤ (c1 - 1 / 2) * (z1 t) ^ 2 := mul_nonneg (sub_pos.mpr hc1).le (sq_nonneg _)
    linarith

/-! ### Robust adaptation: parameter-box projection -/

/-- Derivative identity for `saturated_Vz` under parameter-box projection:
`V̇_z = -c₁ z₁² + z₁ z₂ - c₂ z₂² + θ̃ ⬝ᵥ ((z₂ • ϕ) - Proj θᵐ θᴹ (z₂ • ϕ) θ̂)`. -/
private theorem saturated_Vz_proj_hasDerivAt
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {mlo Mhi : Fin p → ℝ} {theta : Fin p → ℝ}
    {z1 z2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi : ℝ → (Fin p → ℝ)} {c1 c2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (hz1 : HasDerivAt z1 (-c1 * z1 t + z2 t) t)
    (hz2 : HasDerivAt z2 (-c2 * z2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((saturated_proj_adaptation_law Gamma mlo Mhi (z2 t) (phi t) (theta_hat t)) j) t) :
    HasDerivAt (fun s ↦ saturated_Vz Gamma_inv (z1 s) (z2 s) (theta - theta_hat s))
      (-c1 * z1 t ^ 2 + z1 t * z2 t - c2 * z2 t ^ 2 +
        (theta - theta_hat t) ⬝ᵥ
          ((z2 t • phi t) - Proj mlo Mhi (z2 t • phi t) (theta_hat t))) t := by
  have hdiff : ∀ j, HasDerivAt (fun s ↦ (theta - theta_hat s) j)
      ((-(saturated_proj_adaptation_law Gamma mlo Mhi (z2 t) (phi t) (theta_hat t))) j) t := by
    intro j
    simpa only [Pi.sub_apply, Pi.neg_apply] using (htheta_hat j).const_sub (theta j)
  have h := saturated_Vz_adaptation_hasDerivAt
    (w := -(saturated_proj_adaptation_law Gamma mlo Mhi (z2 t) (phi t) (theta_hat t)))
    hGamma_inv_symm hz1 hz2 hdiff
  refine h.congr_deriv ?_
  rw [saturated_proj_adaptation_law,
    adaptation_proj_cancellation Gamma Gamma_inv mlo Mhi ((z2 t) • (phi t))
      (theta - theta_hat t) (theta_hat t) hGamma_inv]
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

/-- Under the true parameter box bounds `mlo ≤ θ ≤ Mhi`, the projection error cross term is
non-positive by `Proj_sum_nonpos`, so the Lyapunov derivative satisfies
`V̇_z ≤ -(c₁ - 1/2) z₁² - (c₂ - 1/2) z₂²` without an energy offset
(Kabziński–Mosiołek, Section 10.4, Theorem D3.1). -/
theorem saturated_proj_lyapunov_deriv_le
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {mlo Mhi : Fin p → ℝ} {theta : Fin p → ℝ}
    (hm : ∀ k, mlo k ≤ theta k) (hM : ∀ k, theta k ≤ Mhi k)
    {z1 z2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi : ℝ → (Fin p → ℝ)} {c1 c2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (hz1 : HasDerivAt z1 (-c1 * z1 t + z2 t) t)
    (hz2 : HasDerivAt z2 (-c2 * z2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((saturated_proj_adaptation_law Gamma mlo Mhi (z2 t) (phi t) (theta_hat t)) j) t) :
    deriv (fun s ↦ saturated_Vz Gamma_inv (z1 s) (z2 s) (theta - theta_hat s)) t ≤
      -(c1 - 1 / 2) * (z1 t) ^ 2 - (c2 - 1 / 2) * (z2 t) ^ 2 := by
  have h := saturated_Vz_proj_hasDerivAt hGamma_inv_symm hGamma_inv hz1 hz2 htheta_hat
  have hproj : (theta - theta_hat t) ⬝ᵥ
      ((z2 t • phi t) - Proj mlo Mhi (z2 t • phi t) (theta_hat t)) ≤ 0 := by
    simpa only [dotProduct, Pi.sub_apply] using
      Proj_sum_nonpos (m := mlo) (M := Mhi) (y := z2 t • phi t) (theta := theta)
        (thetaHat := theta_hat t) hm hM
  rw [h.deriv]
  have hcross := saturated_cross_term_bound c1 c2 (z1 t) (z2 t)
  linarith

/-! ### Robust adaptation: σ-modification -/

/-- Derivative identity for `saturated_Vz` under σ-modification:
`V̇_z = -c₁ z₁² + z₁ z₂ - c₂ z₂² + σ * (θ̃ ⬝ᵥ θ̂)`. -/
private theorem saturated_Vz_sigma_hasDerivAt
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma : ℝ}
    {z1 z2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi : ℝ → (Fin p → ℝ)} {c1 c2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (hz1 : HasDerivAt z1 (-c1 * z1 t + z2 t) t)
    (hz2 : HasDerivAt z2 (-c2 * z2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((saturated_sigma_adaptation_law Gamma (z2 t) (phi t) sigma (theta_hat t)) j) t) :
    HasDerivAt (fun s ↦ saturated_Vz Gamma_inv (z1 s) (z2 s) (theta - theta_hat s))
      (-c1 * z1 t ^ 2 + z1 t * z2 t - c2 * z2 t ^ 2 +
        sigma * ((theta - theta_hat t) ⬝ᵥ (theta_hat t))) t := by
  have hdiff : ∀ j, HasDerivAt (fun s ↦ (theta - theta_hat s) j)
      ((-(saturated_sigma_adaptation_law Gamma (z2 t) (phi t) sigma (theta_hat t))) j) t := by
    intro j
    simpa only [Pi.sub_apply, Pi.neg_apply] using (htheta_hat j).const_sub (theta j)
  have h := saturated_Vz_adaptation_hasDerivAt
    (w := -(saturated_sigma_adaptation_law Gamma (z2 t) (phi t) sigma (theta_hat t)))
    hGamma_inv_symm hz1 hz2 hdiff
  refine h.congr_deriv ?_
  rw [saturated_sigma_adaptation_law,
    adaptation_sigma_cancellation Gamma Gamma_inv ((z2 t) • (phi t))
      (theta - theta_hat t) (theta_hat t) sigma hGamma_inv]
  simp only [dotProduct_smul, smul_eq_mul]
  ring

/-- Dissipative differential inequality for saturated backstepping with σ-modification:
under the coercivity/dissipation hypothesis
`c * V_z ≤ (c₁ - 1/2) z₁² + (c₂ - 1/2) z₂² + (σ/2) ‖θ̃‖²` with `c > 0`, the Lyapunov
derivative satisfies `V̇_z ≤ -c * V_z + d`, where `d = (σ/2) (θ ⬝ᵥ θ)`
(Kabziński–Mosiołek, Section 10.4, Theorem 7.4). -/
theorem saturated_sigma_dissipation_le
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma c : ℝ} (hsigma : 0 ≤ sigma)
    {z1 z2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi : ℝ → (Fin p → ℝ)} {c1 c2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (hz1 : HasDerivAt z1 (-c1 * z1 t + z2 t) t)
    (hz2 : HasDerivAt z2 (-c2 * z2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((saturated_sigma_adaptation_law Gamma (z2 t) (phi t) sigma (theta_hat t)) j) t)
    (hdiss : c * saturated_Vz Gamma_inv (z1 t) (z2 t) (theta - theta_hat t) ≤
      (c1 - 1 / 2) * (z1 t) ^ 2 + (c2 - 1 / 2) * (z2 t) ^ 2 +
        (sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t))) :
    deriv (fun s ↦ saturated_Vz Gamma_inv (z1 s) (z2 s) (theta - theta_hat s)) t ≤
      -c * saturated_Vz Gamma_inv (z1 t) (z2 t) (theta - theta_hat t) +
        (sigma / 2) * (theta ⬝ᵥ theta) := by
  have hderiv :=
    saturated_Vz_sigma_hasDerivAt hGamma_inv_symm hGamma_inv hz1 hz2 htheta_hat
  have hcross := robust_mrac_sigma_cross_term_le theta (theta_hat t)
  have hmul := mul_le_mul_of_nonneg_left hcross hsigma
  have hmul' : sigma * (-(1 / 2 : ℝ) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t)) +
        (1 / 2 : ℝ) * (theta ⬝ᵥ theta))
      = -(sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t)) +
        (sigma / 2) * (theta ⬝ᵥ theta) := by ring
  rw [hmul'] at hmul
  rw [hderiv.deriv]
  nlinarith [hmul, hdiss, sq_nonneg (z1 t - z2 t)]

/-- Uniform trajectory boundedness of the saturated backstepping state under
σ-modification: for all `t ≥ 0`, `V_z(t) ≤ max (V_z(0)) (d / c)` where
`d = (σ/2) * (θ ⬝ᵥ θ)` (Kabziński–Mosiołek, Section 10.4). -/
theorem saturated_sigma_bound_le_max
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma c : ℝ} (hc : 0 < c) (hsigma : 0 ≤ sigma)
    {z1 z2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi : ℝ → (Fin p → ℝ)} {c1 c2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    (hz1 : ∀ t ≥ 0, HasDerivAt z1 (-c1 * z1 t + z2 t) t)
    (hz2 : ∀ t ≥ 0, HasDerivAt z2 (-c2 * z2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (htheta_hat : ∀ t ≥ 0, ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((saturated_sigma_adaptation_law Gamma (z2 t) (phi t) sigma (theta_hat t)) j) t)
    (hdiss : ∀ t ≥ 0, c * saturated_Vz Gamma_inv (z1 t) (z2 t) (theta - theta_hat t) ≤
      (c1 - 1 / 2) * (z1 t) ^ 2 + (c2 - 1 / 2) * (z2 t) ^ 2 +
        (sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t))) :
    let d := (sigma / 2) * (theta ⬝ᵥ theta)
    ∀ t ≥ 0, saturated_Vz Gamma_inv (z1 t) (z2 t) (theta - theta_hat t) ≤
      max (saturated_Vz Gamma_inv (z1 0) (z2 0) (theta - theta_hat 0)) (d / c) := by
  dsimp only
  intro t ht
  let v : ℝ → ℝ := fun s ↦ saturated_Vz Gamma_inv (z1 s) (z2 s) (theta - theta_hat s)
  have hderiv : ∀ s, 0 ≤ s → HasDerivAt v (deriv v s) s := by
    intro s hs
    have h := saturated_Vz_sigma_hasDerivAt hGamma_inv_symm hGamma_inv
      (hz1 s hs) (hz2 s hs) (htheta_hat s hs)
    exact h.congr_deriv h.deriv.symm
  have hineq : ∀ s, 0 ≤ s → deriv v s ≤ -(c * v s) + (sigma / 2) * (theta ⬝ᵥ theta) := by
    intro s hs
    have h := saturated_sigma_dissipation_le (hsigma := hsigma) hGamma_inv_symm hGamma_inv
      (hz1 s hs) (hz2 s hs) (htheta_hat s hs) (hdiss s hs)
    simpa only [v, neg_mul] using h
  have hbound := le_gronwallBound_of_hasDerivAt_le hc hderiv hineq t ht
  have hmax := gronwall_bound_le_max (v 0) c ((sigma / 2) * (theta ⬝ᵥ theta)) t hc ht
  simpa only [v] using hbound.trans hmax

/-- Asymptotic ultimate boundedness under σ-modification: for any target level
`B > d / c` with `d = (σ/2) * (θ ⬝ᵥ θ)`, the Lyapunov function `V_z(t)` eventually drops
strictly below `B` (Kabziński–Mosiołek, Section 10.4). -/
theorem saturated_sigma_eventually_bounded
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma c B : ℝ} (hc : 0 < c) (hsigma : 0 ≤ sigma)
    {z1 z2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi : ℝ → (Fin p → ℝ)} {c1 c2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    (hz1 : ∀ t ≥ 0, HasDerivAt z1 (-c1 * z1 t + z2 t) t)
    (hz2 : ∀ t ≥ 0, HasDerivAt z2 (-c2 * z2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (htheta_hat : ∀ t ≥ 0, ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((saturated_sigma_adaptation_law Gamma (z2 t) (phi t) sigma (theta_hat t)) j) t)
    (hdiss : ∀ t ≥ 0, c * saturated_Vz Gamma_inv (z1 t) (z2 t) (theta - theta_hat t) ≤
      (c1 - 1 / 2) * (z1 t) ^ 2 + (c2 - 1 / 2) * (z2 t) ^ 2 +
        (sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t)))
    (hB : (sigma / 2) * (theta ⬝ᵥ theta) / c < B) :
    ∀ᶠ t in Filter.atTop, saturated_Vz Gamma_inv (z1 t) (z2 t) (theta - theta_hat t) < B := by
  let v : ℝ → ℝ := fun s ↦ saturated_Vz Gamma_inv (z1 s) (z2 s) (theta - theta_hat s)
  have hderiv : ∀ s, 0 ≤ s → HasDerivAt v (deriv v s) s := by
    intro s hs
    have h := saturated_Vz_sigma_hasDerivAt hGamma_inv_symm hGamma_inv
      (hz1 s hs) (hz2 s hs) (htheta_hat s hs)
    exact h.congr_deriv h.deriv.symm
  have hineq : ∀ s, 0 ≤ s → deriv v s ≤ -(c * v s) + (sigma / 2) * (theta ⬝ᵥ theta) := by
    intro s hs
    have h := saturated_sigma_dissipation_le (hsigma := hsigma) hGamma_inv_symm hGamma_inv
      (hz1 s hs) (hz2 s hs) (htheta_hat s hs) (hdiss s hs)
    simpa only [v, neg_mul] using h
  have h := eventually_lt_of_hasDerivAt_le_neg_mul_add (v := v)
    (d := (sigma / 2) * (theta ⬝ᵥ theta)) hc hB hderiv hineq
  simpa only [v] using h

/-! ### Tracking error reconstruction (Corollary 10.1, time domain) -/

/-- Tracking error triangle-inequality bound: `|e₁(t)| ≤ |z₁(t)| + |p₁(t)|`
(Kabziński–Mosiołek, equation 10.49). -/
theorem saturated_error_le (e1 z1 p1 : ℝ) (h : z1 = e1 - p1) :
    |e1| ≤ |z1| + |p1| := by
  have he1 : e1 = z1 + p1 := by linarith
  rw [he1]
  exact abs_add_le z1 p1

/-- Recovery of nominal asymptotic tracking: when the auxiliary tracking error satisfies
`z₁(t) → 0` and the auxiliary filter state satisfies `p₁(t) → 0`, the true tracking error
converges to zero, `e₁(t) → 0` as `t → ∞` (Kabziński–Mosiołek, Corollary 10.1). -/
theorem saturated_nominal_tracking_tendsto_zero
    {e1 z1 p1 : ℝ → ℝ} (h : ∀ t, z1 t = e1 t - p1 t)
    (hz1 : Filter.Tendsto z1 Filter.atTop (nhds 0))
    (hp1 : Filter.Tendsto p1 Filter.atTop (nhds 0)) :
    Filter.Tendsto e1 Filter.atTop (nhds 0) := by
  have he1 : e1 = fun t ↦ z1 t + p1 t := by
    funext t
    have := h t
    linarith
  rw [he1]
  simpa using hz1.add hp1
