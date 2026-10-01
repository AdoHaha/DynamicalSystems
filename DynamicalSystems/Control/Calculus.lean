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
public import DynamicalSystems.Stability.Projection

/-!
# Shared finite-index matrix calculus for adaptive control

This file collects the elementary finite-index vector and matrix calculus,
positive-definiteness and parameter-adaptation cancellation lemmas that the
Kabziński–Mosiołek control-design modules (`Adaptive.MRAC`, `Adaptive.RobustMRAC`,
`Backstepping.Tuning`, `Backstepping.Robust`, `Backstepping.Saturated` and
`Backstepping.Barrier`) previously copied as private helpers.

The lemmas are stated for an arbitrary finite index type `ι`; consuming modules
instantiate `ι` with the state or parameter index (`Fin n`, `Fin p`, …).

## Main results

* `hasDerivAt_dotProduct`: product rule for the dot product of two vector
  trajectories.
* `hasDerivAt_mulVec`: differentiation of a constant matrix-vector product.
* `hasDerivAt_half_quadratic_form`: derivative of a symmetric quadratic form.
* `posDef_dotProduct_nonneg`: positive semidefiniteness of a `PosDef` quadratic
  form.
* `posDef_transpose_eq`: real positive definite matrices are symmetric.
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

/-- Product rule for the dot product of two vector trajectories. -/
theorem hasDerivAt_dotProduct
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
theorem hasDerivAt_mulVec
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
theorem hasDerivAt_half_quadratic_form
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

/-- Positive semidefiniteness of a quadratic form for a positive definite real
matrix. -/
theorem posDef_dotProduct_nonneg {M : Matrix ι ι ℝ} (hM : M.PosDef) (x : ι → ℝ) :
    0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp
  · exact le_of_lt (by
      have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hx
      simpa only [Pi.star_apply, star_trivial] using h)

omit [Fintype ι] in
/-- Hermitian parts of positive definite real matrices are symmetric. -/
theorem posDef_transpose_eq {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    Mᵀ = M := by
  have h := hM.1.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

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
