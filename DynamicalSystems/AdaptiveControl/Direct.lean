/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.AdaptiveControl.BoundedGrowth

/-! # Direct adaptive control: the normalized performance error and Theorem 11.1

This file formalizes the analytical core of *direct adaptive control* of
I. D. Landau, R. Lozano, M'Saad and A. Karimi, *Adaptive Control: Algorithms,
Analysis and Applications*, 2nd ed., Springer 2011, Chapter 11, Section 11.2.

The a priori performance error of the adaptive tracking scheme is linear in the
controller parameter error `θ̃` and the regressor `φ`, equation (11.14):

`ε₀ = θ̃ᵀ φ`.

The quantity that is actually driven to zero by the PAA of Theorem 3.2 is the
*normalized* performance error, equation (11.25):

`(ε₀)² / (1 + ‖φ‖²) → 0`.

`normalized_performance_error_le` is the deterministic pointwise bound behind
equation (11.25): Cauchy–Schwarz gives `(θ̃ᵀφ)² ≤ ‖θ̃‖² · ‖φ‖²`, and dividing by
`1 + ‖φ‖²` leaves the parameter-error norm `‖θ̃‖²` times `‖φ‖²/(1 + ‖φ‖²) ≤ 1`.

`direct_adaptive_stability` packages the Bounded Growth Lemma (Lemma 11.1) with a
summable parameter error. When the PAA output is `∑_t (ε₀(t + d + 1))² < ∞`, its
terms tend to `0`, and since `1 + (x t)² ≥ 1` the normalized error (11.25) tends to
`0` as well. Applying `bounded_growth` then yields the two conclusions of
Theorem 11.1: the weighted regressor norm `x` — and hence `φ_C` — is bounded
(11.26), and the a priori performance error tends to `0` (11.27).

## Main results

* `normalized_performance_error_le`: the normalized performance error is dominated
  by the squared parameter-error norm (Cauchy–Schwarz).
* `direct_adaptive_stability`: Theorem 11.1 at statement level; growth bound
  (11.24) plus a summable performance error give a bounded regressor and
  `ε₀(t + d + 1) → 0`.
-/

@[expose] public section

open scoped Topology

/-- **Equation (11.14) ⇒ (11.25), Cauchy–Schwarz step.** The normalized a priori
performance error of the direct adaptive control scheme is dominated by the
squared parameter-error norm:
`(∑ k, θ̃ k * φ k)² / (1 + ∑ k, (φ k)²) ≤ ∑ k, (θ̃ k)²`.
Indeed `(θ̃ᵀφ)² ≤ ‖θ̃‖² · ‖φ‖²` and `‖φ‖² / (1 + ‖φ‖²) ≤ 1`. -/
theorem normalized_performance_error_le {n : ℕ} (thetaTilde phi : Fin n → ℝ) :
    (∑ k, thetaTilde k * phi k) ^ 2 / (1 + ∑ k, (phi k) ^ 2) ≤
      ∑ k, (thetaTilde k) ^ 2 := by
  have hcs : (∑ k, thetaTilde k * phi k) ^ 2 ≤
      (∑ k, (thetaTilde k) ^ 2) * ∑ k, (phi k) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) thetaTilde phi
  have hA : (0 : ℝ) ≤ ∑ k, (phi k) ^ 2 := Finset.sum_nonneg (fun k _ ↦ sq_nonneg _)
  have hB : (0 : ℝ) ≤ ∑ k, (thetaTilde k) ^ 2 := Finset.sum_nonneg (fun k _ ↦ sq_nonneg _)
  have hden : (0 : ℝ) < 1 + ∑ k, (phi k) ^ 2 := by linarith
  have h1 : (∑ k, thetaTilde k * phi k) ^ 2 / (1 + ∑ k, (phi k) ^ 2)
      ≤ (∑ k, (thetaTilde k) ^ 2) * (∑ k, (phi k) ^ 2) / (1 + ∑ k, (phi k) ^ 2) :=
    div_le_div_of_nonneg_right hcs hden.le
  have h2 : (∑ k, (thetaTilde k) ^ 2) * (∑ k, (phi k) ^ 2) / (1 + ∑ k, (phi k) ^ 2)
      ≤ ∑ k, (thetaTilde k) ^ 2 := by
    rw [mul_div_assoc]
    exact mul_le_of_le_one_right hB (by rw [div_le_one hden]; linarith)
  linarith

/-- **Theorem 11.1 (direct adaptive control), statement level.** Assume the growth
bound (11.24) `x t ≤ C₁ + C₂ · max_{k ≤ t+D+1} e k` relating the weighted regressor
norm `x` to the performance error `e`, and assume that the PAA output — the squared
performance error — is summable, `∑_t (e (t+D+1))² < ∞` (the `ℓ²` conclusion of
Theorem 3.2 feeding (11.25)). Then `x` is bounded (11.26) and the a priori
performance error tends to `0`, `e (t+D+1) → 0` (11.27).

The summability of `(e (t+D+1))²` makes its terms tend to `0`; since
`1 + (x t)² ≥ 1`, the normalized error `(e (t+D+1))² / (1 + (x t)²)` tends to `0`
too, so the Bounded Growth Lemma `bounded_growth` applies. -/
theorem direct_adaptive_stability {x e : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t) (he : ∀ t, 0 ≤ e t)
    {C1 C2 : ℝ} (hC1 : 0 < C1) (hC2 : 0 < C2) (D : ℕ)
    (hbound : ∀ t, x t ≤ C1 + C2 * (Finset.range (t + D + 2)).sup' (by simp) e)
    (hsum : Summable (fun t ↦ (e (t + D + 1)) ^ 2)) :
    (∃ M, ∀ t, x t ≤ M) ∧ Filter.Tendsto (fun t ↦ e (t + D + 1)) Filter.atTop (𝓝 0) := by
  have hsq : Filter.Tendsto (fun t ↦ (e (t + D + 1)) ^ 2) Filter.atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero
  have hlim : Filter.Tendsto (fun t ↦ (e (t + D + 1)) ^ 2 / (1 + (x t) ^ 2))
      Filter.atTop (𝓝 0) := by
    apply squeeze_zero (fun t ↦ div_nonneg (sq_nonneg _) (by positivity))
    · intro t
      exact div_le_self (sq_nonneg _) (by nlinarith [sq_nonneg (x t)])
    · exact hsq
  exact bounded_growth hx he hC1 hC2 D hbound hlim
