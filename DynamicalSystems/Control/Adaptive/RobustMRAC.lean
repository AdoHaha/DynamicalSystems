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
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import DynamicalSystems.Control.Calculus
public import DynamicalSystems.Control.Adaptive.MRAC
public import DynamicalSystems.Linear.LyapunovEquation
public import DynamicalSystems.Stability.Projection
public import DynamicalSystems.Stability.Comparison
public import DynamicalSystems.Stability.UltimateBoundedness

/-!
# Robust MRAC: σ-modification and parameter projection

This file formalizes the two robust modifications of the classical Model
Reference Adaptive Control adaptation law analysed by Kabziński and Mosiołek,
*Projektowanie nieliniowych układów sterowania*, Komitet Automatyki i Robotyki
PAN, Monografie tom 22, Chapter 5, Section 5.2.3 and Section 5.2.5, together with
Theorem 5.3, equations (5.72)–(5.114).

The plant is an `m`-input nonlinear system with matched parametric uncertainty
and a bounded external disturbance `d(t)`:
```
x' = A x + B F(x) + B u + d(t),   F(x) = ξ(x)ᵀ θ,   ‖d(t)‖ ≤ εmax
```
for an unknown constant parameter vector `θ`, a known regressor `ξ(x)`, and a
linear reference model `xₘ' = Aₘ xₘ + Bₘ v`. Along the tracking error
`e = x - xₘ` one has `e' = Aₘ e + B ξ(x)ᵀ θ̃ + d(t)` with `θ̃ = θ - θ̂`
(equation 5.74). The composite Lyapunov candidate is the public `mrac_V` of
`DynamicalSystems.Control.Adaptive.MRAC`.

## Main definitions

* `robust_mrac_sigma_adaptation_law`: σ-modified adaptation vector field
  `θ̂' = Γ (ξ Bᵀ P e - σ θ̂)` (equation 5.77).
* `robust_mrac_proj_adaptation_law`: projected adaptation vector field
  `θ̂' = Γ Proj_{θᵐ,θᴹ}(ξ Bᵀ P e, θ̂)` (equation 5.109).

## Main results

* `robust_mrac_sigma_lyapunov_hasDerivAt`: closed-loop derivative identity
  `V̇ = -eᵀ Q e + σ θ̃ᵀ θ̂` (equation 5.78).
* `robust_mrac_sigma_cross_term_le`: completing-the-square bound on the leakage
  term (equation 5.79).
* `robust_mrac_sigma_dissipation_le`: dissipation inequality `V̇ ≤ -c V + d`
  (equation 5.81).
* `robust_mrac_sigma_bound_le_max`: uniform trajectory bound
  `V(t) ≤ max (V(0)) (d/c)` (Theorem 5.3).
* `robust_mrac_sigma_eventually_bounded`: asymptotic ultimate boundedness
  `V(t) < B` for every `B > d/c` (Theorem 5.3).
* `robust_mrac_proj_lyapunov_hasDerivAt`: closed-loop derivative identity under
  projection (equation 5.110).
* `robust_mrac_proj_lyapunov_deriv_le`: non-positive dissipation bound
  `V̇ ≤ -eᵀ Q e` from the projection inequality (equation 5.111).

## References

* J. Kabziński, P. Mosiołek, *Projektowanie nieliniowych układów sterowania*,
  Komitet Automatyki i Robotyki PAN, Monografie tom 22, Chapter 5, Section 5.2.
-/

open scoped Matrix

variable {n m p : ℕ}

@[expose] public section

/-! ### Definitions -/

/-- Adaptation vector field for robust MRAC with σ-modification:
`θ̂' = Γ *ᵥ (ξ *ᵥ (Bᵀ *ᵥ (P *ᵥ e)) - σ • θ̂)` (Kabziński–Mosiołek, equation 5.77). -/
-- The underscore in `robust_mrac_sigma_adaptation_law` is mandated by the
-- campaign's required-declaration list, so the naming linter is disabled here.
@[nolint defsWithUnderscore]
def robust_mrac_sigma_adaptation_law
    (Gamma : Matrix (Fin p) (Fin p) ℝ) (xi : Matrix (Fin p) (Fin m) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (e : Fin n → ℝ) (sigma : ℝ) (theta_hat : Fin p → ℝ) : Fin p → ℝ :=
  Gamma *ᵥ (xi *ᵥ (Bᵀ *ᵥ (P *ᵥ e)) - sigma • theta_hat)

/-- Parameter adaptation vector field for MRAC with parameter box projection:
`θ̂' = Γ *ᵥ Proj θᵐ θᴹ (ξ *ᵥ (Bᵀ *ᵥ (P *ᵥ e))) θ̂` (Kabziński–Mosiołek, equation 5.109). -/
-- The underscore in `robust_mrac_proj_adaptation_law` is mandated by the
-- campaign's required-declaration list, so the naming linter is disabled here.
-- The bound vectors are named `mlo`/`Mhi` (rather than the book's `θᵐ`/`θᴹ`)
-- to avoid shadowing the ambient input-dimension variable `m`.
@[nolint defsWithUnderscore]
noncomputable def robust_mrac_proj_adaptation_law
    (Gamma : Matrix (Fin p) (Fin p) ℝ) (mlo Mhi : Fin p → ℝ)
    (xi : Matrix (Fin p) (Fin m) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ)
    (theta_hat : Fin p → ℝ) : Fin p → ℝ :=
  Gamma *ᵥ (Proj mlo Mhi (xi *ᵥ (Bᵀ *ᵥ (P *ᵥ e))) theta_hat)

/-! ### Internal calculus and algebra helpers

The calculus and algebra helpers below are compact private copies of the ones
used by `DynamicalSystems.Control.Adaptive.MRAC`; they are generalized to an
arbitrary finite index type so that they serve both the state space `Fin n` and
the parameter space `Fin p`. -/

/-- Transpose swap identity for the state-error coupling with parameter
uncertainty: for symmetric `P`, the scalar
`e ⬝ᵥ (P *ᵥ (B *ᵥ (ξᵀ *ᵥ θ̃)))` equals the transposed adaptation coupling
`θ̃ ⬝ᵥ (ξ *ᵥ (Bᵀ *ᵥ (P *ᵥ e)))` (Kabziński–Mosiołek, equation 5.50). -/
private theorem mrac_cancellation_algebra
    (P : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (xi : Matrix (Fin p) (Fin m) ℝ) (e : Fin n → ℝ) (theta_tilde : Fin p → ℝ)
    (hP_symm : Pᵀ = P) :
    e ⬝ᵥ (P *ᵥ (B *ᵥ (xiᵀ *ᵥ theta_tilde))) =
      theta_tilde ⬝ᵥ (xi *ᵥ (Bᵀ *ᵥ (P *ᵥ e))) := by
  have step1 : e ⬝ᵥ (P *ᵥ (B *ᵥ (xiᵀ *ᵥ theta_tilde))) =
      (B *ᵥ (xiᵀ *ᵥ theta_tilde)) ⬝ᵥ (P *ᵥ e) := by
    have h := Matrix.dotProduct_transpose_mulVec P e (B *ᵥ (xiᵀ *ᵥ theta_tilde))
    rwa [hP_symm] at h
  have step2 : (B *ᵥ (xiᵀ *ᵥ theta_tilde)) ⬝ᵥ (P *ᵥ e) =
      (xiᵀ *ᵥ theta_tilde) ⬝ᵥ (Bᵀ *ᵥ (P *ᵥ e)) := by
    rw [dotProduct_comm]
    exact (Matrix.dotProduct_transpose_mulVec B (xiᵀ *ᵥ theta_tilde) (P *ᵥ e)).symm
  have step3 : (xiᵀ *ᵥ theta_tilde) ⬝ᵥ (Bᵀ *ᵥ (P *ᵥ e)) =
      theta_tilde ⬝ᵥ (xi *ᵥ (Bᵀ *ᵥ (P *ᵥ e))) := by
    rw [dotProduct_comm]
    exact Matrix.dotProduct_transpose_mulVec xi (Bᵀ *ᵥ (P *ᵥ e)) theta_tilde
  rw [step1, step2, step3]

/-- Bridge from the matrix Lyapunov equation to the Lyapunov derivative: if
`Aₘᵀ * P + P * Aₘ = -(2 • Q)` and `P` is symmetric, then
`e ⬝ᵥ (P *ᵥ (Aₘ *ᵥ e)) = -(e ⬝ᵥ (Q *ᵥ e))`
(Kabziński–Mosiołek, equation 5.51). -/
private theorem mrac_lyapunov_derivative_algebra
    {Am Q P : Matrix (Fin n) (Fin n) ℝ}
    (hlyap : Amᵀ * P + P * Am = -((2 : ℝ) • Q))
    (hP_symm : Pᵀ = P) (e : Fin n → ℝ) :
    e ⬝ᵥ (P *ᵥ (Am *ᵥ e)) = -(e ⬝ᵥ (Q *ᵥ e)) := by
  have hqf := matrix_lyapunov_equation_quadratic_form (A := Am) (Q := (2 : ℝ) • Q)
    (P := P) hlyap e
  have hsym : (Am *ᵥ e) ⬝ᵥ (P *ᵥ e) = e ⬝ᵥ (P *ᵥ (Am *ᵥ e)) := by
    have h := Matrix.dotProduct_transpose_mulVec P (Am *ᵥ e) e
    rwa [hP_symm] at h
  have hsmul : e ⬝ᵥ (((2 : ℝ) • Q) *ᵥ e) = 2 * (e ⬝ᵥ (Q *ᵥ e)) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [hsym, hsmul] at hqf
  linarith

/-! ### σ-modification -/

/-- The composite Lyapunov function `mrac_V` satisfies the closed-loop derivative
identity `V̇ = -(e(t) ⬝ᵥ (Q *ᵥ e(t))) + σ * ((θ - θ̂(t)) ⬝ᵥ θ̂(t))` along
trajectories of the MRAC system with σ-modification (Kabziński–Mosiołek,
equation 5.78). -/
theorem robust_mrac_sigma_lyapunov_hasDerivAt
    {Am P Q : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma : ℝ}
    {e : ℝ → (Fin n → ℝ)} {theta_hat : ℝ → (Fin p → ℝ)}
    {xi : ℝ → Matrix (Fin p) (Fin m) ℝ}
    (hlyap : Amᵀ * P + P * Am = -((2 : ℝ) • Q))
    (hP_symm : Pᵀ = P) (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (he : ∀ i, HasDerivAt (fun s ↦ e s i)
      ((Am *ᵥ e t + B *ᵥ ((xi t)ᵀ *ᵥ (theta - theta_hat t))) i) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_mrac_sigma_adaptation_law Gamma (xi t) B P (e t) sigma (theta_hat t)) j) t) :
    HasDerivAt (fun s ↦ mrac_V P Gamma_inv (e s) (theta - theta_hat s))
      (-(e t ⬝ᵥ (Q *ᵥ e t)) + sigma * ((theta - theta_hat t) ⬝ᵥ (theta_hat t))) t := by
  have hdiff : ∀ j, HasDerivAt (fun s ↦ (theta - theta_hat s) j)
      (-(robust_mrac_sigma_adaptation_law Gamma (xi t) B P (e t) sigma (theta_hat t)) j) t := by
    intro j
    simpa only [Pi.sub_apply] using (htheta_hat j).const_sub (theta j)
  have h1 := hasDerivAt_half_quadratic_form P hP_symm he
  have h2 := hasDerivAt_half_quadratic_form Gamma_inv hGamma_inv_symm hdiff
  have hfun : (fun s ↦ mrac_V P Gamma_inv (e s) (theta - theta_hat s)) =
      (fun s ↦ (1 / 2 : ℝ) * ((e s) ⬝ᵥ (P *ᵥ (e s)))
        + (1 / 2 : ℝ) * ((theta - theta_hat s) ⬝ᵥ
            (Gamma_inv *ᵥ (theta - theta_hat s)))) := by
    funext s
    rfl
  rw [hfun]
  refine (h1.add h2).congr_deriv ?_
  rw [Matrix.mulVec_add, dotProduct_add]
  rw [show (fun j ↦
      -(robust_mrac_sigma_adaptation_law Gamma (xi t) B P (e t) sigma (theta_hat t)) j) =
      -(robust_mrac_sigma_adaptation_law Gamma (xi t) B P (e t) sigma (theta_hat t)) from rfl]
  have hparam : (theta - theta_hat t) ⬝ᵥ
      (Gamma_inv *ᵥ
        (-(robust_mrac_sigma_adaptation_law Gamma (xi t) B P (e t) sigma (theta_hat t))))
      = -((theta - theta_hat t) ⬝ᵥ
        (xi t *ᵥ (Bᵀ *ᵥ (P *ᵥ e t)) - sigma • (theta_hat t))) := by
    rw [robust_mrac_sigma_adaptation_law, Matrix.mulVec_neg, dotProduct_neg,
      Matrix.mulVec_mulVec, hGamma_inv, Matrix.one_mulVec]
  rw [hparam, mrac_cancellation_algebra P B (xi t) (e t) (theta - theta_hat t) hP_symm,
    mrac_lyapunov_derivative_algebra hlyap hP_symm (e t)]
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

/-- Algebraic completing-the-square bound on the σ-modification cross term:
`(θ - θ̂) ⬝ᵥ θ̂ ≤ -(1/2) * ((θ - θ̂) ⬝ᵥ (θ - θ̂)) + (1/2) * (θ ⬝ᵥ θ)`
(Kabziński–Mosiołek, equation 5.79). -/
theorem robust_mrac_sigma_cross_term_le (theta theta_hat : Fin p → ℝ) :
    (theta - theta_hat) ⬝ᵥ theta_hat ≤
      -(1 / 2 : ℝ) * ((theta - theta_hat) ⬝ᵥ (theta - theta_hat)) +
      (1 / 2 : ℝ) * (theta ⬝ᵥ theta) := by
  have hself : 0 ≤ theta_hat ⬝ᵥ theta_hat := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have h : (theta - theta_hat) ⬝ᵥ theta_hat
        + (1 / 2 : ℝ) * (theta_hat ⬝ᵥ theta_hat)
      = -(1 / 2 : ℝ) * ((theta - theta_hat) ⬝ᵥ (theta - theta_hat))
        + (1 / 2 : ℝ) * (theta ⬝ᵥ theta) := by
    simp only [dotProduct, Pi.sub_apply]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

/-- Dissipation inequality for MRAC with σ-modification: under a uniform
coercivity/dissipation hypothesis `c * V ≤ eᵀ Q e + (σ/2) ‖θ̃‖²` with `c > 0`, the
Lyapunov derivative satisfies `V̇ ≤ -c * V + d`, where `d = (σ/2) * (θ ⬝ᵥ θ)`
(Kabziński–Mosiołek, equation 5.81). -/
theorem robust_mrac_sigma_dissipation_le
    {Am P Q : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma c : ℝ} (hsigma : 0 ≤ sigma)
    {e : ℝ → (Fin n → ℝ)} {theta_hat : ℝ → (Fin p → ℝ)}
    {xi : ℝ → Matrix (Fin p) (Fin m) ℝ}
    (hlyap : Amᵀ * P + P * Am = -((2 : ℝ) • Q))
    (hP_symm : Pᵀ = P) (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (he : ∀ i, HasDerivAt (fun s ↦ e s i)
      ((Am *ᵥ e t + B *ᵥ ((xi t)ᵀ *ᵥ (theta - theta_hat t))) i) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_mrac_sigma_adaptation_law Gamma (xi t) B P (e t) sigma (theta_hat t)) j) t)
    (hdiss : c * mrac_V P Gamma_inv (e t) (theta - theta_hat t) ≤
      (e t ⬝ᵥ (Q *ᵥ e t)) + (sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t))) :
    deriv (fun s ↦ mrac_V P Gamma_inv (e s) (theta - theta_hat s)) t ≤
      -c * mrac_V P Gamma_inv (e t) (theta - theta_hat t) + (sigma / 2) * (theta ⬝ᵥ theta) := by
  have hderiv := robust_mrac_sigma_lyapunov_hasDerivAt hlyap hP_symm hGamma_inv_symm hGamma_inv
    he htheta_hat
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

/-- Uniform trajectory boundedness of the composite MRAC state under
σ-modification: for all `t ≥ 0`, `V(t) ≤ max (V(0)) (d / c)` where
`d = (σ/2) * (θ ⬝ᵥ θ)` (Kabziński–Mosiołek, Theorem 5.3). -/
theorem robust_mrac_sigma_bound_le_max
    {Am P Q : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma c : ℝ} (hc : 0 < c) (hsigma : 0 ≤ sigma)
    {e : ℝ → (Fin n → ℝ)} {theta_hat : ℝ → (Fin p → ℝ)}
    {xi : ℝ → Matrix (Fin p) (Fin m) ℝ}
    (hlyap : Amᵀ * P + P * Am = -((2 : ℝ) • Q))
    (hP_symm : Pᵀ = P) (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    (he : ∀ t ≥ 0, ∀ i, HasDerivAt (fun s ↦ e s i)
      ((Am *ᵥ e t + B *ᵥ ((xi t)ᵀ *ᵥ (theta - theta_hat t))) i) t)
    (htheta_hat : ∀ t ≥ 0, ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_mrac_sigma_adaptation_law Gamma (xi t) B P (e t) sigma (theta_hat t)) j) t)
    (hdiss : ∀ t ≥ 0, c * mrac_V P Gamma_inv (e t) (theta - theta_hat t) ≤
      (e t ⬝ᵥ (Q *ᵥ e t)) + (sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t))) :
    let d := (sigma / 2) * (theta ⬝ᵥ theta)
    ∀ t ≥ 0, mrac_V P Gamma_inv (e t) (theta - theta_hat t) ≤
      max (mrac_V P Gamma_inv (e 0) (theta - theta_hat 0)) (d / c) := by
  dsimp only
  intro t ht
  let v : ℝ → ℝ := fun s ↦ mrac_V P Gamma_inv (e s) (theta - theta_hat s)
  have hderiv : ∀ s, 0 ≤ s → HasDerivAt v (deriv v s) s := by
    intro s hs
    have h := robust_mrac_sigma_lyapunov_hasDerivAt hlyap hP_symm hGamma_inv_symm hGamma_inv
      (he s hs) (htheta_hat s hs)
    exact h.congr_deriv h.deriv.symm
  have hineq : ∀ s, 0 ≤ s → deriv v s ≤ -(c * v s) + (sigma / 2) * (theta ⬝ᵥ theta) := by
    intro s hs
    have h := robust_mrac_sigma_dissipation_le (hsigma := hsigma) hlyap hP_symm hGamma_inv_symm
      hGamma_inv (he s hs) (htheta_hat s hs) (hdiss s hs)
    simpa only [v, neg_mul] using h
  have hbound := le_gronwallBound_of_hasDerivAt_le hc hderiv hineq t ht
  have hmax := gronwall_bound_le_max (v 0) c ((sigma / 2) * (theta ⬝ᵥ theta)) t hc ht
  simpa only [v] using hbound.trans hmax

/-- Asymptotic ultimate boundedness of MRAC with σ-modification: for any target
level `B > d / c` with `d = (σ/2) * (θ ⬝ᵥ θ)`, the Lyapunov function `V(t)`
eventually drops strictly below `B` (Kabziński–Mosiołek, Theorem 5.3). -/
theorem robust_mrac_sigma_eventually_bounded
    {Am P Q : Matrix (Fin n) (Fin n) ℝ} {Bmat : Matrix (Fin n) (Fin m) ℝ}
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {sigma c B : ℝ} (hc : 0 < c) (hsigma : 0 ≤ sigma)
    {e : ℝ → (Fin n → ℝ)} {theta_hat : ℝ → (Fin p → ℝ)}
    {xi : ℝ → Matrix (Fin p) (Fin m) ℝ}
    (hlyap : Amᵀ * P + P * Am = -((2 : ℝ) • Q))
    (hP_symm : Pᵀ = P) (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    (he : ∀ t ≥ 0, ∀ i, HasDerivAt (fun s ↦ e s i)
      ((Am *ᵥ e t + Bmat *ᵥ ((xi t)ᵀ *ᵥ (theta - theta_hat t))) i) t)
    (htheta_hat : ∀ t ≥ 0, ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_mrac_sigma_adaptation_law Gamma (xi t) Bmat P (e t) sigma (theta_hat t)) j) t)
    (hdiss : ∀ t ≥ 0, c * mrac_V P Gamma_inv (e t) (theta - theta_hat t) ≤
      (e t ⬝ᵥ (Q *ᵥ e t)) + (sigma / 2) * ((theta - theta_hat t) ⬝ᵥ (theta - theta_hat t)))
    (hB : (sigma / 2) * (theta ⬝ᵥ theta) / c < B) :
    ∀ᶠ t in Filter.atTop, mrac_V P Gamma_inv (e t) (theta - theta_hat t) < B := by
  let v : ℝ → ℝ := fun s ↦ mrac_V P Gamma_inv (e s) (theta - theta_hat s)
  have hderiv : ∀ s, 0 ≤ s → HasDerivAt v (deriv v s) s := by
    intro s hs
    have h := robust_mrac_sigma_lyapunov_hasDerivAt hlyap hP_symm hGamma_inv_symm hGamma_inv
      (he s hs) (htheta_hat s hs)
    exact h.congr_deriv h.deriv.symm
  have hineq : ∀ s, 0 ≤ s → deriv v s ≤ -(c * v s) + (sigma / 2) * (theta ⬝ᵥ theta) := by
    intro s hs
    have h := robust_mrac_sigma_dissipation_le (hsigma := hsigma) hlyap hP_symm hGamma_inv_symm
      hGamma_inv (he s hs) (htheta_hat s hs) (hdiss s hs)
    simpa only [v, neg_mul] using h
  have := eventually_lt_of_hasDerivAt_le_neg_mul_add (v := v)
    (d := (sigma / 2) * (theta ⬝ᵥ theta)) hc hB hderiv hineq
  simpa only [v] using this

/-! ### Parameter box projection -/

/-- The composite Lyapunov function `mrac_V` satisfies the closed-loop derivative
identity under projected parameter adaptation:
`V̇ = -(e(t) ⬝ᵥ (Q *ᵥ e(t))) + (θ - θ̂(t)) ⬝ᵥ (y(t) - Proj θᵐ θᴹ y(t) θ̂(t))`
where `y(t) = ξ(t) *ᵥ (Bᵀ *ᵥ (P *ᵥ e(t)))` (Kabziński–Mosiołek, equation 5.110). -/
theorem robust_mrac_proj_lyapunov_hasDerivAt
    {Am P Q : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {mlo Mhi : Fin p → ℝ} {theta : Fin p → ℝ}
    {e : ℝ → (Fin n → ℝ)} {theta_hat : ℝ → (Fin p → ℝ)}
    {xi : ℝ → Matrix (Fin p) (Fin m) ℝ}
    (hlyap : Amᵀ * P + P * Am = -((2 : ℝ) • Q))
    (hP_symm : Pᵀ = P) (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (he : ∀ i, HasDerivAt (fun s ↦ e s i)
      ((Am *ᵥ e t + B *ᵥ ((xi t)ᵀ *ᵥ (theta - theta_hat t))) i) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_mrac_proj_adaptation_law Gamma mlo Mhi (xi t) B P (e t) (theta_hat t)) j) t) :
    let y := xi t *ᵥ (Bᵀ *ᵥ (P *ᵥ e t))
    HasDerivAt (fun s ↦ mrac_V P Gamma_inv (e s) (theta - theta_hat s))
      (-(e t ⬝ᵥ (Q *ᵥ e t)) + (theta - theta_hat t) ⬝ᵥ (y - Proj mlo Mhi y (theta_hat t))) t := by
  dsimp only
  have hdiff : ∀ j, HasDerivAt (fun s ↦ (theta - theta_hat s) j)
      (-(robust_mrac_proj_adaptation_law Gamma mlo Mhi (xi t) B P (e t) (theta_hat t)) j) t := by
    intro j
    simpa only [Pi.sub_apply] using (htheta_hat j).const_sub (theta j)
  have h1 := hasDerivAt_half_quadratic_form P hP_symm he
  have h2 := hasDerivAt_half_quadratic_form Gamma_inv hGamma_inv_symm hdiff
  have hfun : (fun s ↦ mrac_V P Gamma_inv (e s) (theta - theta_hat s)) =
      (fun s ↦ (1 / 2 : ℝ) * ((e s) ⬝ᵥ (P *ᵥ (e s)))
        + (1 / 2 : ℝ) * ((theta - theta_hat s) ⬝ᵥ
            (Gamma_inv *ᵥ (theta - theta_hat s)))) := by
    funext s
    rfl
  rw [hfun]
  refine (h1.add h2).congr_deriv ?_
  rw [Matrix.mulVec_add, dotProduct_add]
  rw [show (fun j ↦
      -(robust_mrac_proj_adaptation_law Gamma mlo Mhi (xi t) B P (e t) (theta_hat t)) j) =
      -(robust_mrac_proj_adaptation_law Gamma mlo Mhi (xi t) B P (e t) (theta_hat t)) from rfl]
  have hparam : (theta - theta_hat t) ⬝ᵥ
      (Gamma_inv *ᵥ
        (-(robust_mrac_proj_adaptation_law Gamma mlo Mhi (xi t) B P (e t) (theta_hat t))))
      = -((theta - theta_hat t) ⬝ᵥ
        (Proj mlo Mhi (xi t *ᵥ (Bᵀ *ᵥ (P *ᵥ e t))) (theta_hat t))) := by
    rw [robust_mrac_proj_adaptation_law, Matrix.mulVec_neg, dotProduct_neg,
      Matrix.mulVec_mulVec, hGamma_inv, Matrix.one_mulVec]
  rw [hparam, mrac_cancellation_algebra P B (xi t) (e t) (theta - theta_hat t) hP_symm,
    mrac_lyapunov_derivative_algebra hlyap hP_symm (e t)]
  rw [dotProduct_sub]
  ring

/-- Under the true parameter box bounds `m ≤ θ ≤ M`, the parameter error cross
term is non-positive by `Proj_sum_nonpos`, so the Lyapunov derivative satisfies
`V̇ ≤ -e(t) ⬝ᵥ (Q *ᵥ e(t))` (Kabziński–Mosiołek, equation 5.111). -/
theorem robust_mrac_proj_lyapunov_deriv_le
    {Am P Q : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {mlo Mhi : Fin p → ℝ} {theta : Fin p → ℝ}
    (hm : ∀ k, mlo k ≤ theta k) (hM : ∀ k, theta k ≤ Mhi k)
    {e : ℝ → (Fin n → ℝ)} {theta_hat : ℝ → (Fin p → ℝ)}
    {xi : ℝ → Matrix (Fin p) (Fin m) ℝ}
    (hlyap : Amᵀ * P + P * Am = -((2 : ℝ) • Q))
    (hP_symm : Pᵀ = P) (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (he : ∀ i, HasDerivAt (fun s ↦ e s i)
      ((Am *ᵥ e t + B *ᵥ ((xi t)ᵀ *ᵥ (theta - theta_hat t))) i) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((robust_mrac_proj_adaptation_law Gamma mlo Mhi (xi t) B P (e t) (theta_hat t)) j) t) :
    deriv (fun s ↦ mrac_V P Gamma_inv (e s) (theta - theta_hat s)) t ≤
      -(e t ⬝ᵥ (Q *ᵥ e t)) := by
  have h := robust_mrac_proj_lyapunov_hasDerivAt hlyap hP_symm hGamma_inv_symm hGamma_inv
    (mlo := mlo) (Mhi := Mhi) he htheta_hat
  dsimp only at h
  have hproj : (theta - theta_hat t) ⬝ᵥ
      (xi t *ᵥ (Bᵀ *ᵥ (P *ᵥ e t)) -
        Proj mlo Mhi (xi t *ᵥ (Bᵀ *ᵥ (P *ᵥ e t))) (theta_hat t)) ≤ 0 := by
    simpa only [dotProduct, Pi.sub_apply] using
      Proj_sum_nonpos (m := mlo) (M := Mhi) (y := xi t *ᵥ (Bᵀ *ᵥ (P *ᵥ e t)))
        (theta := theta) (thetaHat := theta_hat t) hm hM
  rw [h.deriv]
  linarith
