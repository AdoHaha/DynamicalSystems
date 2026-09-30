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
public import DynamicalSystems.Stability.Barbalat

/-!
# Adaptive backstepping with tuning functions for second-order systems

This file formalizes adaptive backstepping with tuning functions for second-order
strict-feedback nonlinear systems with parametric uncertainty, following
Kabziński and Mosiołek, *Projektowanie nieliniowych układów sterowania*,
Komitet Automatyki i Robotyki PAN, Monografie tom 22, Chapter 7, Section 7.2,
pages 119–121, Theorem 7.2, equations (7.28)–(7.43).

## System description

The plant is the second-order system
```
x₁' = x₂ + ϕ₁(x₁)ᵀ θ
x₂' = u + ϕ₂(x₁, x₂)ᵀ θ
```
where `θ ∈ ℝᵖ` is an unknown constant parameter vector, `ϕ₁, ϕ₂ ∈ ℝᵖ` are known
regressors, and `u` is the control input. The control objective is asymptotic
tracking of a smooth reference trajectory `x_d`.

To prevent overparameterization (avoiding separate estimators for the two
occurrences of the same parameter vector `θ`), the tuning-functions design
introduces:
1. Tracking error `e₁ = x₁ - x_d`.
2. First tuning function `τ₁ = e₁ • ϕ₁` (equation 7.34).
3. Stabilizing function `α₁ = -k₁ e₁ - θ̂ᵀ ϕ₁ + x_d'` (equation 7.15).
4. Second error coordinate `e₂ = x₂ - α₁` (equation 7.7).
5. Second tuning function `τ₂ = τ₁ + e₂ • z₂` (equation 7.40), where `z₂` is the
   effective regressor of the second coordinate.
6. Single parameter estimator `θ̂' = Γ τ₂` (equation 7.41).

Along closed-loop trajectories the parameter estimation errors cancel exactly in
the derivative of the composite Lyapunov function
`V₂ = (1/2) e₁² + (1/2) e₂² + (1/2) θ̃ᵀ Γ⁻¹ θ̃`, yielding
`V̇₂ = -k₁ e₁² - k₂ e₂² ≤ 0`. Asymptotic tracking `e₁ → 0` and `e₂ → 0`
follows via the LaSalle–Yoshizawa / Barbălat bridge.

## Main definitions

* `tuning_alpha1`: stabilizing virtual control `α₁ = -k₁ e₁ - θ̂ ⬝ᵥ ϕ₁ + x_d'`
  (equations 7.15 and 7.52).
* `tuning_tau1`: first tuning function `τ₁ = e₁ • ϕ₁` (equations 7.34 and 7.55).
* `tuning_tau2`: second tuning function `τ₂ = τ₁ + e₂ • z₂`
  (equations 7.40 and 7.59).
* `tuning_adaptation_law`: adaptation vector field `θ̂' = Γ *ᵥ τ`
  (equations 7.41 and 7.90).
* `tuning_V2`: composite quadratic Lyapunov candidate
  `V₂(e₁, e₂, θ̃) = (1/2) e₁² + (1/2) e₂² + (1/2) (θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ θ̃))`
  (equations 7.29, 7.37 and 7.51).

## Main results

* `tuning_V2_hasDerivAt`: closed-loop Lyapunov derivative identity
  `V̇₂ = -k₁ e₁² - k₂ e₂²` (equations 7.43 and Theorem 7.2).
* `tuning_dissipation_tendsto_zero`: convergence of the dissipation rate
  `k₁ e₁² + k₂ e₂² → 0` via the LaSalle–Yoshizawa / Barbălat bridge (Theorem 7.2).
* `tuning_tracking_tendsto_zero`: asymptotic tracking `e₁(t) → 0` and
  `e₂(t) → 0` (Theorem 7.2).

## References

* J. Kabziński, P. Mosiołek, *Projektowanie nieliniowych układów sterowania*,
  Komitet Automatyki i Robotyki PAN, Monografie tom 22, Chapter 7, Section 7.2.
* M. Krstić, I. Kanellakopoulos, P. Kokotović, *Nonlinear and Adaptive Control
  Design*, Wiley, 1995.
-/

open scoped Matrix

variable {p : ℕ}

@[expose] public section

/-! ### Definitions -/

/-- Virtual control (stabilizing function) `α₁` for the second-order system with
parameter uncertainty: `α₁ = -k₁ e₁ - θ̂ ⬝ᵥ ϕ₁ + x_d'`
(Kabziński–Mosiołek, equations 7.15 and 7.52). -/
-- The underscore in `tuning_alpha1` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def tuning_alpha1
    (k1 : ℝ) (e1 : ℝ) (theta_hat phi1 : Fin p → ℝ) (xd' : ℝ) : ℝ :=
  -k1 * e1 - (theta_hat ⬝ᵥ phi1) + xd'

/-- First tuning function `τ₁ = e₁ • ϕ₁` (Kabziński–Mosiołek, equations 7.34 and
7.55), the tuning-functions replacement for the first adaptation law. -/
-- The underscore in `tuning_tau1` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def tuning_tau1 (e1 : ℝ) (phi1 : Fin p → ℝ) : Fin p → ℝ :=
  e1 • phi1

/-- Second tuning function `τ₂ = τ₁ + e₂ • z₂` (Kabziński–Mosiołek, equations
7.40 and 7.59), where `z₂` is the effective regressor in the second error
coordinate. -/
-- The underscore in `tuning_tau2` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def tuning_tau2
    (tau1 : Fin p → ℝ) (e2 : ℝ) (z2 : Fin p → ℝ) : Fin p → ℝ :=
  tau1 + e2 • z2

/-- Parameter adaptation vector field `θ̂' = Γ *ᵥ τ`
(Kabziński–Mosiołek, equations 7.41 and 7.90). -/
-- The underscore in `tuning_adaptation_law` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def tuning_adaptation_law
    (Gamma : Matrix (Fin p) (Fin p) ℝ) (tau : Fin p → ℝ) : Fin p → ℝ :=
  Gamma *ᵥ tau

/-- Composite quadratic Lyapunov candidate for adaptive backstepping with tuning
functions: `V₂(e₁, e₂, θ̃) = (1/2) e₁² + (1/2) e₂² + (1/2) (θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ θ̃))`
(Kabziński–Mosiołek, equations 7.29, 7.37 and 7.51). -/
-- The underscore in `tuning_V2` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
noncomputable def tuning_V2
    (Gamma_inv : Matrix (Fin p) (Fin p) ℝ) (e1 e2 : ℝ)
    (theta_tilde : Fin p → ℝ) : ℝ :=
  (1 / 2 : ℝ) * e1 ^ 2 + (1 / 2 : ℝ) * e2 ^ 2 +
    (1 / 2 : ℝ) * (theta_tilde ⬝ᵥ (Gamma_inv *ᵥ theta_tilde))

/-! ### Internal calculus and algebra helpers

The calculus and algebra helpers below follow the compact private copies used by
`DynamicalSystems.Control.Adaptive.MRAC` and
`DynamicalSystems.Control.Adaptive.RobustMRAC`. -/

/-- Product rule for the dot product of two vector trajectories. -/
private theorem hasDerivAt_dotProduct {ι : Type*} [Fintype ι]
    {u v : ℝ → (ι → ℝ)} {u' v' : ι → ℝ} {t : ℝ}
    (hu : ∀ i, HasDerivAt (fun s ↦ u s i) (u' i) t)
    (hv : ∀ i, HasDerivAt (fun s ↦ v s i) (v' i) t) :
    HasDerivAt (fun s ↦ (u s) ⬝ᵥ (v s)) (u' ⬝ᵥ (v t) + (u t) ⬝ᵥ v') t := by
  simp only [dotProduct]
  have h : HasDerivAt (∑ i ∈ (Finset.univ : Finset ι), fun s ↦ u s i * v s i)
      (∑ i ∈ (Finset.univ : Finset ι), (u' i * v t i + u t i * v' i)) t :=
    HasDerivAt.sum (fun i _ ↦ (hu i).mul (hv i))
  have hfun : (fun s ↦ ∑ i, u s i * v s i) =
      (∑ i ∈ (Finset.univ : Finset ι), fun s ↦ u s i * v s i) := by
    funext s
    rw [Finset.sum_apply]
  rw [hfun]
  exact h.congr_deriv Finset.sum_add_distrib

/-- Differentiating a constant matrix-vector product `s ↦ M *ᵥ u s`
coordinate-wise. -/
private theorem hasDerivAt_mulVec {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) {u : ℝ → (ι → ℝ)} {u' : ι → ℝ} {t : ℝ}
    (hu : ∀ j, HasDerivAt (fun s ↦ u s j) (u' j) t) (i : ι) :
    HasDerivAt (fun s ↦ (M *ᵥ (u s)) i) ((M *ᵥ u') i) t := by
  simp only [Matrix.mulVec, dotProduct]
  have h : HasDerivAt (∑ j ∈ (Finset.univ : Finset ι), fun s ↦ M i j * u s j)
      (∑ j ∈ (Finset.univ : Finset ι), M i j * u' j) t :=
    HasDerivAt.sum (fun j _ ↦ (hu j).const_mul (M i j))
  have hfun : (fun s ↦ ∑ x, M i x * u s x) =
      (∑ j ∈ (Finset.univ : Finset ι), fun s ↦ M i j * u s j) := by
    funext s
    rw [Finset.sum_apply]
  rw [hfun]
  exact h

/-- Derivative of a quadratic form `s ↦ (1/2) * (u s ⬝ᵥ (M *ᵥ u s))` along a
vector trajectory for a symmetric matrix `M`. -/
private theorem hasDerivAt_half_quadratic_form {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (hM_symm : Mᵀ = M)
    {u : ℝ → (ι → ℝ)} {u' : ι → ℝ} {t : ℝ}
    (hu : ∀ j, HasDerivAt (fun s ↦ u s j) (u' j) t) :
    HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ((u s) ⬝ᵥ (M *ᵥ (u s)))) ((u t) ⬝ᵥ (M *ᵥ u')) t := by
  have hw : ∀ j, HasDerivAt (fun s ↦ (M *ᵥ (u s)) j) ((M *ᵥ u') j) t :=
    fun j ↦ hasDerivAt_mulVec M hu j
  have hdp := hasDerivAt_dotProduct hu hw
  have hsym : u' ⬝ᵥ (M *ᵥ (u t)) = (u t) ⬝ᵥ (M *ᵥ u') := by
    have h := Matrix.dotProduct_transpose_mulVec M u' (u t)
    rwa [hM_symm] at h
  refine (hdp.const_mul (1 / 2 : ℝ)).congr_deriv ?_
  rw [hsym]
  ring

/-- Algebraic reduction of the first error-coordinate dynamics: with the plant
`x₁' = x₂ + θ ⬝ᵥ ϕ₁`, the reference velocity `x_d'`, the stabilizing function
`α₁ = -k₁ e₁ - θ̂ ⬝ᵥ ϕ₁ + x_d'`, the errors `e₁ = x₁ - x_d`, `e₂ = x₂ - α₁` and
the parameter error `θ̃ = θ - θ̂`, the error derivative `x₁' - x_d'` equals
`-k₁ e₁ + e₂ + θ̃ ⬝ᵥ ϕ₁` (Kabziński–Mosiołek, equations 7.8 and 7.53). -/
private theorem tuning_e1_dynamics_algebra
    (k1 : ℝ) (x1 x2 xd xd' : ℝ) (theta theta_hat phi1 : Fin p → ℝ) :
    let e1 := x1 - xd
    let alpha1 := tuning_alpha1 k1 e1 theta_hat phi1 xd'
    let e2 := x2 - alpha1
    let theta_tilde := theta - theta_hat
    (x2 + (theta ⬝ᵥ phi1)) - xd' = -k1 * e1 + e2 + (theta_tilde ⬝ᵥ phi1) := by
  simp only [tuning_alpha1, sub_dotProduct]
  ring

/-- Positive semidefiniteness of a quadratic form for a positive definite real
matrix. -/
private theorem posDef_dotProduct_nonneg {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.PosDef) (x : Fin p → ℝ) : 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp
  · exact le_of_lt (by
      have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hx
      simpa only [Pi.star_apply, star_trivial] using h)

/-- Hermitian parts of positive definite real matrices are symmetric. -/
private theorem posDef_transpose_eq {M : Matrix (Fin p) (Fin p) ℝ} (hM : M.PosDef) :
    Mᵀ = M := by
  have h := hM.1.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The composite Lyapunov candidate `tuning_V2` is nonnegative when `Γ⁻¹` is
positive definite. -/
private theorem tuning_V2_nonneg {Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    (hG : Gamma_inv.PosDef) (e1 e2 : ℝ) (theta_tilde : Fin p → ℝ) :
    0 ≤ tuning_V2 Gamma_inv e1 e2 theta_tilde := by
  have h1 : 0 ≤ e1 ^ 2 := sq_nonneg e1
  have h2 : 0 ≤ e2 ^ 2 := sq_nonneg e2
  have h3 := posDef_dotProduct_nonneg hG theta_tilde
  simp only [tuning_V2]
  nlinarith [h1, h2, h3]

/-- Exact parameter-adaptation cancellation: with the adaptation law
`θ̂' = Γ *ᵥ τ` and `Γ⁻¹ * Γ = 1`, the parameter-error derivative term
`θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ (-θ̂'))` equals `-(θ̃ ⬝ᵥ τ)`
(Kabziński–Mosiołek, equations 7.35 and 7.39). -/
private theorem tuning_adaptation_cancellation
    (Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ) (tau : Fin p → ℝ)
    (theta_tilde : Fin p → ℝ) (hGamma_inv : Gamma_inv * Gamma = 1) :
    theta_tilde ⬝ᵥ (Gamma_inv *ᵥ (-(tuning_adaptation_law Gamma tau))) =
      -(theta_tilde ⬝ᵥ tau) := by
  rw [Matrix.mulVec_neg, dotProduct_neg, tuning_adaptation_law]
  congr 1
  rw [Matrix.mulVec_mulVec, hGamma_inv, Matrix.one_mulVec]

/-- Bilinear expansion of the second tuning function:
`θ̃ ⬝ᵥ τ₂ = e₁ (θ̃ ⬝ᵥ ϕ₁) + e₂ (θ̃ ⬝ᵥ z₂)`
(Kabziński–Mosiołek, equations 7.40 and 7.59). -/
private theorem tuning_cross_cancellation
    (e1 e2 : ℝ) (phi1 z2 theta_tilde : Fin p → ℝ) :
    theta_tilde ⬝ᵥ (tuning_tau2 (tuning_tau1 e1 phi1) e2 z2) =
      e1 * (theta_tilde ⬝ᵥ phi1) + e2 * (theta_tilde ⬝ᵥ z2) := by
  simp only [tuning_tau2, tuning_tau1, dotProduct_add, dotProduct_smul, smul_eq_mul]

/-! ### Closed-loop dynamics and stability theorems -/

/-- Derivative of the composite Lyapunov function `tuning_V2` along closed-loop
trajectories of the adaptive backstepping system: `V̇₂ = -k₁ e₁² - k₂ e₂²`
(Kabziński–Mosiołek, equations 7.43 and Theorem 7.2).

The parameter error terms `e₁ (θ̃ ⬝ᵥ ϕ₁) + e₂ (θ̃ ⬝ᵥ z₂) = θ̃ ⬝ᵥ τ₂` cancel exactly
against `-θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ θ̂')` via the adaptation law `θ̂' = Γ *ᵥ τ₂` and
`Γ⁻¹ * Γ = 1`, while the skew-symmetric cross terms `e₁ e₂ - e₂ e₁` cancel. -/
theorem tuning_V2_hasDerivAt
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ}
    {e1 e2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi1 z2 : ℝ → (Fin p → ℝ)} {k1 k2 : ℝ}
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (he1 : HasDerivAt e1 (-k1 * e1 t + e2 t + ((theta - theta_hat t) ⬝ᵥ phi1 t)) t)
    (he2 : HasDerivAt e2 (-e1 t - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ z2 t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((tuning_adaptation_law Gamma
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t))) j) t) :
    HasDerivAt (fun s ↦ tuning_V2 Gamma_inv (e1 s) (e2 s) (theta - theta_hat s))
      (-k1 * (e1 t) ^ 2 - k2 * (e2 t) ^ 2) t := by
  have hdiff : ∀ j, HasDerivAt (fun s ↦ (theta - theta_hat s) j)
      (-(tuning_adaptation_law Gamma
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t))) j) t := by
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
  rw [show (fun j ↦ -(tuning_adaptation_law Gamma
      (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t))) j) =
      -(tuning_adaptation_law Gamma
        (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t))) from rfl]
  rw [tuning_adaptation_cancellation Gamma Gamma_inv
    (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t))
    (theta - theta_hat t) hGamma_inv]
  rw [tuning_cross_cancellation (e1 t) (e2 t) (phi1 t) (z2 t) (theta - theta_hat t)]
  ring

/-- Convergence of the dissipation rate `k₁ e₁² + k₂ e₂² → 0` as `t → ∞` via the
LaSalle–Yoshizawa / Barbălat bridge (Kabziński–Mosiołek, Theorem 3.7 and
Theorem 7.2).

The argument is the standard one: `V₂ ≥ 0` is decreasing along trajectories with
`V̇₂ = -(k₁ e₁² + k₂ e₂²) ≤ 0`, hence bounded below; uniform continuity of the
dissipation rate makes Barbălat's lemma applicable. -/
theorem tuning_dissipation_tendsto_zero
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ}
    {e1 e2 : ℝ → ℝ} {theta_hat : ℝ → (Fin p → ℝ)}
    {phi1 z2 : ℝ → (Fin p → ℝ)} {k1 k2 : ℝ}
    (hGamma_inv_pd : Gamma_inv.PosDef)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    (hk1 : 0 < k1) (hk2 : 0 < k2)
    (he1 : ∀ t ≥ 0, HasDerivAt e1 (-k1 * e1 t + e2 t + ((theta - theta_hat t) ⬝ᵥ phi1 t)) t)
    (he2 : ∀ t ≥ 0, HasDerivAt e2 (-e1 t - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ z2 t)) t)
    (htheta_hat : ∀ t ≥ 0, ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((tuning_adaptation_law Gamma (tuning_tau2 (tuning_tau1 (e1 t) (phi1 t)) (e2 t) (z2 t))) j) t)
    (huc : UniformContinuousOn (fun t ↦ k1 * (e1 t) ^ 2 + k2 * (e2 t) ^ 2) (Set.Ici 0)) :
    Filter.Tendsto (fun t ↦ k1 * (e1 t) ^ 2 + k2 * (e2 t) ^ 2) Filter.atTop (nhds 0) := by
  let V : ℝ → ℝ := fun t ↦ tuning_V2 Gamma_inv (e1 t) (e2 t) (theta - theta_hat t)
  let w : ℝ → ℝ := fun t ↦ k1 * (e1 t) ^ 2 + k2 * (e2 t) ^ 2
  have hG_symm : Gamma_invᵀ = Gamma_inv := posDef_transpose_eq hGamma_inv_pd
  have hw_nonneg : ∀ t, 0 ≤ t → 0 ≤ w t := by
    intro t _
    have h1 : 0 ≤ k1 * (e1 t) ^ 2 := mul_nonneg (le_of_lt hk1) (sq_nonneg _)
    have h2 : 0 ≤ k2 * (e2 t) ^ 2 := mul_nonneg (le_of_lt hk2) (sq_nonneg _)
    dsimp only [w]
    linarith
  have hBdd : BddBelow (V '' Set.Ici 0) := by
    refine ⟨0, ?_⟩
    rintro y ⟨t, _ht, rfl⟩
    exact tuning_V2_nonneg hGamma_inv_pd (e1 t) (e2 t) (theta - theta_hat t)
  have hVderiv : ∀ t, 0 ≤ t → HasDerivAt V (-(w t)) t := by
    intro t ht
    have h := tuning_V2_hasDerivAt hG_symm hGamma_inv (he1 t ht) (he2 t ht) (htheta_hat t ht)
    change HasDerivAt (fun s ↦ tuning_V2 Gamma_inv (e1 s) (e2 s) (theta - theta_hat s))
      (-(w t)) t
    refine h.congr_deriv ?_
    dsimp only [w]
    ring
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt V (deriv V t) t := by
    intro t ht
    exact (hVderiv t ht).congr_deriv (hVderiv t ht).deriv.symm
  have hineq : ∀ t, 0 ≤ t → deriv V t ≤ -(w t) := by
    intro t ht
    exact le_of_eq (hVderiv t ht).deriv
  simpa only [w] using
    Barbalat.tendsto_zero_of_hasDerivAt_le_neg_of_boundedBelow_of_uniformContinuousOn
      hBdd hw_nonneg hderiv hineq huc

/-- Asymptotic tracking convergence of the adaptive backstepping system: both
error coordinates converge to zero, `e₁(t) → 0` and `e₂(t) → 0` as `t → ∞`
(Kabziński–Mosiołek, Theorem 7.2).

The diagonal dissipation rate `k₁ e₁² + k₂ e₂²` dominates each single term, so the
quadratic squeeze lemma applies with coercivity constants `k₁` and `k₂`. -/
theorem tuning_tracking_tendsto_zero
    {e1 e2 : ℝ → ℝ} {k1 k2 : ℝ}
    (hk1 : 0 < k1) (hk2 : 0 < k2)
    (hw : Filter.Tendsto (fun t ↦ k1 * (e1 t) ^ 2 + k2 * (e2 t) ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto e1 Filter.atTop (nhds 0) ∧ Filter.Tendsto e2 Filter.atTop (nhds 0) := by
  constructor
  · refine Barbalat.tendsto_zero_of_tendsto_zero_of_sq_le (c := k1) hk1 hw ?_
    intro t _
    have h2 : 0 ≤ k2 * (e2 t) ^ 2 := mul_nonneg (le_of_lt hk2) (sq_nonneg _)
    linarith
  · refine Barbalat.tendsto_zero_of_tendsto_zero_of_sq_le (c := k2) hk2 hw ?_
    intro t _
    have h1 : 0 ≤ k1 * (e1 t) ^ 2 := mul_nonneg (le_of_lt hk1) (sq_nonneg _)
    linarith
