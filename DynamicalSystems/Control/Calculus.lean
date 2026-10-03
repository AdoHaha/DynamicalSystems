/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.LinearAlgebra.Matrix.Calculus
public import DynamicalSystems.Stability.Projection

/-!
# Shared finite-index matrix calculus for adaptive control

This file re-exports the elementary finite-index vector and matrix calculus and
positive-definiteness lemmas now living in
`DynamicalSystems.Mathlib.LinearAlgebra.Matrix.Calculus` (`hasDerivAt_dotProduct`,
`hasDerivAt_mulVec`, `hasDerivAt_half_quadratic_form`, `posDef_dotProduct_nonneg`,
`posDef_transpose_eq`), and adds the parameter-adaptation cancellation lemmas that
the Kabziński–Mosiołek control-design modules (`Adaptive.MRAC`, `Adaptive.RobustMRAC`,
`Backstepping.Tuning`, `Backstepping.Robust`, `Backstepping.Saturated` and
`Backstepping.Barrier`) previously copied as private helpers.

The lemmas are stated for an arbitrary finite index type `ι`; consuming modules
instantiate `ι` with the state or parameter index (`Fin n`, `Fin p`, …).

## Main results

* `adaptation_cancellation`: exact cancellation of the parameter-error term for
  the adaptation law `θ̂' = Γ *ᵥ τ`.
* `adaptation_sigma_cancellation`: the σ-modified counterpart
  `θ̂' = Γ *ᵥ (τ - σ • θ̂)`.
* `adaptation_proj_cancellation`: the projected counterpart
  `θ̂' = Γ *ᵥ Proj θᵐ θᴹ τ θ̂`.

## References

* J. Kabziński, P. Mosiołek, *Projektowanie nieliniowych układów sterowania*,
  Komitet Automatyki i Robotyki PAN, Monografie tom 22, Chapters 5–12.
-/

open scoped Matrix

@[expose] public section

variable {ι : Type*} [Fintype ι]

/-- Exact parameter-adaptation cancellation: with the adaptation law
`θ̂' = Γ *ᵥ τ` and `Γ⁻¹ * Γ = 1`, the parameter-error derivative term
`θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ (-θ̂'))` equals `-(θ̃ ⬝ᵥ τ)`
(Kabziński–Mosiołek, equations 7.35 and 7.39). -/
theorem adaptation_cancellation [DecidableEq ι]
    (Gamma Gamma_inv : Matrix ι ι ℝ) (tau theta_tilde : ι → ℝ)
    (hGamma_inv : Gamma_inv * Gamma = 1) :
    theta_tilde ⬝ᵥ (Gamma_inv *ᵥ (-(Gamma *ᵥ tau))) = -(theta_tilde ⬝ᵥ tau) := by
  rw [Matrix.mulVec_neg, dotProduct_neg, Matrix.mulVec_mulVec, hGamma_inv,
    Matrix.one_mulVec]

/-- Exact parameter-adaptation cancellation for the σ-modified law
`θ̂' = Γ *ᵥ (τ - σ • θ̂)`: the parameter-error derivative term
`θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ (-θ̂'))` equals `-(θ̃ ⬝ᵥ τ) + σ * (θ̃ ⬝ᵥ θ̂)`
(Kabziński–Mosiołek, equations 7.137 and 10.42). -/
theorem adaptation_sigma_cancellation [DecidableEq ι]
    (Gamma Gamma_inv : Matrix ι ι ℝ) (tau theta_tilde theta_hat : ι → ℝ) (sigma : ℝ)
    (hGamma_inv : Gamma_inv * Gamma = 1) :
    theta_tilde ⬝ᵥ (Gamma_inv *ᵥ (-(Gamma *ᵥ (tau - sigma • theta_hat)))) =
      -(theta_tilde ⬝ᵥ tau) + sigma * (theta_tilde ⬝ᵥ theta_hat) := by
  rw [Matrix.mulVec_neg, dotProduct_neg, Matrix.mulVec_mulVec, hGamma_inv,
    Matrix.one_mulVec]
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

/-- Exact parameter-adaptation cancellation for the projected law
`θ̂' = Γ *ᵥ Proj θᵐ θᴹ τ θ̂`: the parameter-error derivative term
`θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ (-θ̂'))` equals `-(θ̃ ⬝ᵥ Proj θᵐ θᴹ τ θ̂)`
(Kabziński–Mosiołek, equation 7.167). -/
theorem adaptation_proj_cancellation [DecidableEq ι]
    (Gamma Gamma_inv : Matrix ι ι ℝ) (mlo Mhi tau theta_tilde theta_hat : ι → ℝ)
    (hGamma_inv : Gamma_inv * Gamma = 1) :
    theta_tilde ⬝ᵥ (Gamma_inv *ᵥ (-(Gamma *ᵥ (Proj mlo Mhi tau theta_hat)))) =
      -(theta_tilde ⬝ᵥ Proj mlo Mhi tau theta_hat) := by
  rw [Matrix.mulVec_neg, dotProduct_neg, Matrix.mulVec_mulVec, hGamma_inv,
    Matrix.one_mulVec]
