/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-! # Persistent excitation: the sample-covariance quadratic form

This file formalizes the algebraic core of persistently exciting regressors of
I. D. Landau, R. Lozano, M'Saad and A. Karimi, *Adaptive Control: Algorithms,
Analysis and Applications*, 2nd ed., Springer 2011, Sect. 3.4.2 (eqs. 3.316–3.318)
and Theorem 3.4.

A finite window of regressors `Phi : Fin m → Fin n → ℝ` collects `m` observation
vectors `φ_j = Phi j`, each a vector indexed by `Fin n`, and `theta : Fin n → ℝ`
is a parameter vector. The *sample covariance* of the window is the symmetric
matrix `C = ∑_j φ_j φ_jᵀ`, i.e. `C k l = ∑_j Phi j k * Phi j l`. The window is
*persistently exciting* when `C` dominates `alpha • 1` in the quadratic-form order,
`alpha * ∑_k v k ^ 2 ≤ ∑_k ∑_l v k * v l * C k l` for every `v` (with `alpha ≥ 0`),
which is the finite-window form of `lim (1/t₁) ∑ φ(t) φᵀ(t) > 0` (eq. 3.296).

The main identity rewrites the squared norm of the regressor-parameter inner
products as the quadratic form of `C`; the lower bound then transfers the
persistent-excitation hypothesis to the actual window.

## Main results

* `sum_sq_dotProduct_eq_quadform`: `∑_j (∑_k Phi j k * theta k) ^ 2`
  `= ∑_k ∑_l theta k * theta l * (∑_j Phi j k * Phi j l)`.
* `pe_quadform_lower_bound`: under the persistent-excitation hypothesis on the
  sample covariance, `alpha * ∑_k theta k ^ 2 ≤ ∑_j (∑_k Phi j k * theta k) ^ 2`.
-/

@[expose] public section

/-- The squared-norm expansion of a finite regressor window: the sum of squared
regressor-parameter inner products equals the quadratic form of the sample
covariance `C k l = ∑_j Phi j k * Phi j l`.

This is the algebraic identity behind the finite-window form of the persistent
excitation condition (Landau 2nd ed., eqs. 3.316–3.318): expanding the square and
interchanging the sums exposes `C`. -/
theorem sum_sq_dotProduct_eq_quadform {n m : ℕ} (Phi : Fin m → Fin n → ℝ)
    (theta : Fin n → ℝ) :
    (∑ j, (∑ k, Phi j k * theta k) ^ 2) =
      ∑ k, ∑ l, theta k * theta l * (∑ j, Phi j k * Phi j l) := by
  have hinner : ∀ j, (∑ k, Phi j k * theta k) ^ 2 =
      ∑ k, ∑ l, (Phi j k * theta k) * (Phi j l * theta l) := by
    intro j
    rw [sq, Finset.sum_mul_sum]
  calc
    (∑ j, (∑ k, Phi j k * theta k) ^ 2)
        = ∑ j, ∑ k, ∑ l, (Phi j k * theta k) * (Phi j l * theta l) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hinner j
    _ = ∑ k, ∑ j, ∑ l, (Phi j k * theta k) * (Phi j l * theta l) := by
          rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, ∑ j, (Phi j k * theta k) * (Phi j l * theta l) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, theta k * theta l * (∑ j, Phi j k * Phi j l) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- Persistent-excitation lower bound. If the sample covariance
`C k l = ∑_j Phi j k * Phi j l` of the window dominates `alpha • 1` in quadratic
form (the finite-window persistent-excitation condition of Theorem 3.4), then the
window's squared regressor-parameter inner products are bounded below by
`alpha` times the squared parameter norm.

The hypothesis `halpha : 0 ≤ alpha` is part of the persistent-excitation contract
(`alpha` is the excitation level, which must be non-negative); the algebraic
implication `hC ⟹` conclusion uses only `hC`, so `halpha` is recorded but does not
enter the computation. -/
theorem pe_quadform_lower_bound {n m : ℕ} (Phi : Fin m → Fin n → ℝ)
    (theta : Fin n → ℝ) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hC : ∀ v : Fin n → ℝ, alpha * ∑ k, v k ^ 2 ≤
      ∑ k, ∑ l, v k * v l * (∑ j, Phi j k * Phi j l)) :
    alpha * ∑ k, theta k ^ 2 ≤ ∑ j, (∑ k, Phi j k * theta k) ^ 2 := by
  have hα : 0 ≤ alpha := halpha
  have h := hC theta
  rwa [← sum_sq_dotProduct_eq_quadform] at h
