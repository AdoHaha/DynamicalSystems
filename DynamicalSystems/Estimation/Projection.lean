/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Stability.Projection
public import DynamicalSystems.ParameterAdaptation.LyapunovAlgebra
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # PAA with projection: the projected Lyapunov step (Landau, Ch. 10, Thm 10.3)

This file formalizes the projection step of the parameter adaptation algorithm
(PAA) with projection of I. D. Landau, R. Lozano, M'Saad and A. Karimi,
*Adaptive Control: Algorithms, Analysis and Applications*, 2nd ed., Springer 2011,
Chapter 10 (Sect. 10.5, eqs. 10.60, 10.70 and Theorem 10.3).

The adaptation gain `F` and the inverse gain `P = F⁻¹` define the quadratic
Lyapunov function `paaV P θ̃ = θ̃ᵀ P θ̃` of
`DynamicalSystems.ParameterAdaptation.LyapunovAlgebra`. The unprojected update is
`θ̂ + y`; the projection `Proj m M y θ̂` of `DynamicalSystems.Stability.Projection`
clamps every coordinate that would leave the box `[m, M]`.

## Correction to the contract statement

The contract froze the general statement

`paaV P (θ - (θ̂ + Proj m M y θ̂)) ≤ paaV P (θ - (θ̂ + y))` for `F * P = 1`, `Fᵀ = F`.

This general inequality is **false**. `Proj` is the *Euclidean* coordinate-wise
projection, which is the orthogonal projection for the metric `P` only when `P` is
diagonal: for a non-diagonal symmetric `P` the cross terms of the quadratic form
can reverse the inequality, even when both `P` and `F` are positive definite. The
machine-checked counterexample is `not_projection_V_le`: with
`P = !![2, 1; 1, 1]`, `F = P⁻¹ = !![1, -1; -1, 2]`, `m = ![0, -100]`,
`M = ![100, 0]`, `θ = ![14, 0]`, `θ̂ = 0` and `y = ![-1, 14]` one has
`paaV P (θ - (θ̂ + Proj m M y θ̂)) = 392 > 226 = paaV P (θ - (θ̂ + y))`.

The theorem `projection_V_le` below is the corrected, machine-checked bound: it
holds whenever the metric `P` is diagonal with non-negative entries (which
includes the book's unit-gain case `P = F = 1` and the scalar/decoupled adaptation
gains). The book's general case (eqs. 10.71–10.78) instead projects in the
transformed coordinates `θ̌ = F^{-1/2} θ̂`, so that the metric becomes the identity;
formalizing that generality needs a symmetric matrix square root and is left to a
follow-up.

## Main results

* `projection_V_le`: the projection step cannot increase the diagonal-metric
  Lyapunov function, `V(θ̃_p) ≤ V(θ̃)`.
* `not_projection_V_le`: machine-checked refutation of the unconstrained general
  form of the contract statement.
-/

@[expose] public section

open scoped Matrix

/-- Coordinate-wise core of the projection Lyapunov bound: if `m ≤ θ ≤ M` and
`projCoord m M y θh` is the coordinate projection of `y` at `θh`, then the
projected parameter error is no farther from `θ` than the unprojected one,
`(θ - θh - proj)² ≤ (θ - θh - y)²`. -/
private lemma projCoord_sq_sub_le {m M θ θh y : ℝ} (hm : m ≤ θ) (hM : θ ≤ M) :
    (θ - θh - projCoord m M y θh) ^ 2 ≤ (θ - θh - y) ^ 2 := by
  rw [projCoord]
  split_ifs with h
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have ht : 0 ≤ θ - θh := by linarith
      have hy : y < 0 := h2
      have hprod : 0 ≤ y * (y - 2 * (θ - θh)) :=
        mul_nonneg_of_nonpos_of_nonpos hy.le (by linarith)
      nlinarith [hprod]
    · have ht : θ - θh ≤ 0 := by linarith
      have hy : 0 < y := h2
      have hprod : 0 ≤ y * (y - 2 * (θ - θh)) :=
        mul_nonneg hy.le (by linarith)
      nlinarith [hprod]
  · exact le_refl _

/-- The quadratic form of a diagonal matrix is the weighted sum of the squared
coordinates: `paaV (diagonal d) x = ∑ k, d k * x k ^ 2`. -/
private lemma paaV_diagonal {n : ℕ} (d x : Fin n → ℝ) :
    paaV (Matrix.diagonal d) x = ∑ k, d k * x k ^ 2 := by
  simp only [paaV, dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- **Projection Lyapunov bound (corrected form of the contract statement).** If the
inverse adaptation gain `P` is diagonal with non-negative diagonal entries, then
projecting the adaptation update `y` onto the box `[m, M]` cannot increase the PAA
Lyapunov function `paaV P θ̃ = θ̃ᵀ P θ̃`:

`paaV P (θ - (θ̂ + Proj m M y θ̂)) ≤ paaV P (θ - (θ̂ + y))`.

This is the machine-checked projection step of Theorem 10.3 (eq. 10.60/10.70) in
the metric for which the coordinate-wise `Proj` is the orthogonal projection. The
unconstrained general-`P` form is false; see `not_projection_V_le`. -/
theorem projection_V_le {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (m M theta thetaHat y : Fin n → ℝ)
    (hPdiag : P.IsDiag) (hPnn : ∀ k, 0 ≤ P k k)
    (hm : ∀ k, m k ≤ theta k) (hM : ∀ k, theta k ≤ M k) :
    paaV P (theta - (thetaHat + Proj m M y thetaHat)) ≤ paaV P (theta - (thetaHat + y)) := by
  have hP : P = Matrix.diagonal (fun k ↦ P k k) := (hPdiag.diagonal_diag).symm
  set p : Fin n → ℝ := Proj m M y thetaHat with hp
  set tt : Fin n → ℝ := theta - thetaHat with htt
  have hvec1 : theta - (thetaHat + p) = tt - p := by rw [htt, hp]; abel
  have hvec2 : theta - (thetaHat + y) = tt - y := by rw [htt]; abel
  rw [hvec1, hvec2, hP, paaV_diagonal, paaV_diagonal]
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (hPnn k)
  have hk : (tt k - p k) ^ 2 ≤ (tt k - y k) ^ 2 := by
    rw [hp, htt]
    simp only [Pi.sub_apply, Proj]
    exact projCoord_sq_sub_le (hm k) (hM k)
  exact hk

/-- **The unconstrained contract statement is false.** The general projection
Lyapunov bound

`paaV P (θ - (θ̂ + Proj m M y θ̂)) ≤ paaV P (θ - (θ̂ + y))`  for `F * P = 1`, `Fᵀ = F`

does not hold: it fails for the positive-definite data below, where the projected
left-hand side is `392` while the unprojected right-hand side is `226`. The
coordinate-wise projection `Proj` is only metric-compatible with a diagonal `P`;
the book's general case requires the change of coordinates (10.71)–(10.78). -/
theorem not_projection_V_le :
    ¬ (∀ {n : ℕ} (P F : Matrix (Fin n) (Fin n) ℝ) (_hFP : F * P = 1) (_hFsym : Fᵀ = F)
        (m M theta thetaHat y : Fin n → ℝ), (∀ k, m k ≤ theta k) →
        (∀ k, theta k ≤ M k) →
        paaV P (theta - (thetaHat + Proj m M y thetaHat)) ≤
          paaV P (theta - (thetaHat + y))) := by
  intro h
  have hFP : (!![1, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℝ) * !![2, 1; 1, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hFsym : (!![1, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = !![1, -1; -1, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  have hm : ∀ k, (![0, -100] : Fin 2 → ℝ) k ≤ ![14, 0] k := by
    intro k; fin_cases k <;> norm_num
  have hM : ∀ k, (![14, 0] : Fin 2 → ℝ) k ≤ ![100, 0] k := by
    intro k; fin_cases k <;> norm_num
  have hle := h (!![2, 1; 1, 1]) (!![1, -1; -1, 2]) hFP hFsym
      ![0, -100] ![100, 0] ![14, 0] ![0, 0] ![-1, 14] hm hM
  have hProj : Proj ![0, -100] ![100, 0] ![-1, 14] ![0, 0] = ![0, 0] := by
    funext k; fin_cases k <;> simp [Proj, projCoord]
  rw [hProj] at hle
  simp only [paaV, dotProduct, Matrix.mulVec, Fin.sum_univ_two] at hle
  norm_num at hle
