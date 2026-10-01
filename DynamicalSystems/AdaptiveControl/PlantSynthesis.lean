/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.DiscreteTime.Convolution
public import DynamicalSystems.AdaptiveControl.RobustDirect
public import DynamicalSystems.AdaptiveControl.BoundedGrowth
public import DynamicalSystems.AdaptiveControl.Direct

/-! # Plant synthesis for direct adaptive control (Landau Theorem 11.1)

This file assembles the plant-level statements of *direct adaptive control* of
I. D. Landau, R. Lozano, M'Saad and A. Karimi, *Adaptive Control: Algorithms,
Analysis and Applications*, 2nd ed., Springer 2011, Theorem 11.1, printed
pp. 366–367 (equations (11.14), (11.24)–(11.31)).

The controller-parameter adaptation (the PAA of (11.19)–(11.23)) produces a bound
on the performance error `ε₀`, and the plant equations turn that bound into a
componentwise growth bound on the regressor `φ_C` (equations (11.29)–(11.31)):

`|φ k (t)| ≤ C₁ + C₂ · max_{j ≤ t+D+1} |ε₀(j)|`.

The first result, `regressor_growth_bound_of_components`, converts those
componentwise bounds into a bound on the Euclidean norm of the regressor,

`‖φ(t)‖ ≤ √n · (C₁ + C₂ · max_{j ≤ t+D+1} |ε₀(j)|)`,

which is the form (11.24) consumed by the Bounded Growth Lemma. The second result,
`physical_signals_bounded_of_regressor_bounded`, goes the other way: a bound on the
regressor norm bounds each physical signal component.

The third result, `ideal_direct_adaptive_tracking`, is the plant-level form of
Theorem 11.1 for the ideal (noiseless) case: a growth bound (11.24) together with
the PAA dissipation (11.25) yields boundedness of the regressor and
`ε₀(t + d + 1) → 0` (equations (11.26)–(11.27)).

## Main results

* `regressor_growth_bound_of_components`: componentwise regressor bounds
  (11.31) give the norm bound (11.24).
* `physical_signals_bounded_of_regressor_bounded`: a regressor-norm bound bounds
  each physical signal.
* `ideal_direct_adaptive_tracking`: Theorem 11.1 in the ideal noiseless case.
-/

@[expose] public section

open scoped Topology

/-- **Componentwise regressor bounds give the norm bound (11.24).** If every
component of the regressor is bounded by `C₁ + C₂ · max_{j ≤ t+D+1} |ε₀(j)|`, then
the Euclidean norm of the regressor is bounded by `√n` times the same quantity:
`‖φ(t)‖ ≤ √n · (C₁ + C₂ · max_{j ≤ t+D+1} |ε₀(j)|)`.

Indeed, writing `M` for the running maximum term, each `(φ k t)² ≤ M²`, so the sum
is at most `n · M²` and taking square roots gives the claim (`Real.sqrt_le_sqrt`
and `Real.sqrt_mul`). The constant `M` is positive because `C₁ > 0` and the
running maximum of absolute values is non-negative. -/
theorem regressor_growth_bound_of_components {n : ℕ} (phi : ℕ → Fin n → ℝ) (e : ℕ → ℝ)
    (D : ℕ) {C1 C2 : ℝ} (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hcomp : ∀ t k, |phi t k| ≤
      C1 + C2 * (Finset.range (t + D + 2)).sup' (by simp) (fun j ↦ |e j|)) :
    ∀ t, Real.sqrt (∑ k, (phi t k) ^ 2) ≤
      Real.sqrt n * (C1 + C2 * (Finset.range (t + D + 2)).sup' (by simp)
        (fun j ↦ |e j|)) := by
  intro t
  set S := (Finset.range (t + D + 2)).sup' (by simp) (fun j ↦ |e j|) with hS
  set M := C1 + C2 * S with hM
  have hS_nonneg : 0 ≤ S := by
    have hmem : 0 ∈ Finset.range (t + D + 2) := Finset.mem_range.mpr (by omega)
    exact (abs_nonneg (e 0)).trans (Finset.le_sup' (fun j ↦ |e j|) hmem)
  have hM_pos : 0 < M := by
    have : 0 ≤ C2 * S := mul_nonneg hC2.le hS_nonneg
    rw [hM]; linarith
  have hterm : ∀ k, (phi t k) ^ 2 ≤ M ^ 2 := by
    intro k
    rw [sq_le_sq, abs_of_nonneg hM_pos.le]
    rw [hM, hS]
    exact hcomp t k
  have hsum : (∑ k, (phi t k) ^ 2) ≤ (n : ℝ) * M ^ 2 := by
    have h := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin n))
      (fun k ↦ (phi t k) ^ 2) (M ^ 2) (fun k _ ↦ hterm k)
    simpa [Finset.card_univ, nsmul_eq_mul] using h
  calc Real.sqrt (∑ k, (phi t k) ^ 2) ≤ Real.sqrt ((n : ℝ) * M ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (n : ℝ) * M := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM_pos.le]
    _ = Real.sqrt n * (C1 + C2 * (Finset.range (t + D + 2)).sup' (by simp)
          (fun j ↦ |e j|)) := by
        rw [← hS, ← hM]

/-- **A regressor-norm bound bounds the physical signals.** If the Euclidean norm
of the regressor is bounded by `M`, `‖φ(t)‖ ≤ M`, then every component is bounded
by `M`, `|φ k (t)| ≤ M`.

This is the converse reading of the regressor bound: each component is at most the
norm, `|φ k (t)| ≤ ‖φ(t)‖` (`Real.abs_le_sqrt` applied to
`(φ k t)² ≤ ∑ j, (φ j t)²`), and the norm bound gives the claim. It formalizes the
sense in which the boundedness of `φ_C` in (11.26) means the physical signals
`u(t)` and `y(t)` are bounded. -/
theorem physical_signals_bounded_of_regressor_bounded {n : ℕ} (phi : ℕ → Fin n → ℝ) {M : ℝ}
    (hM : ∀ t, Real.sqrt (∑ k, (phi t k) ^ 2) ≤ M) (k : Fin n) :
    ∀ t, |phi t k| ≤ M := by
  intro t
  have hle : (phi t k) ^ 2 ≤ ∑ j, (phi t j) ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (phi t j)) (Finset.mem_univ k)
  calc |phi t k| ≤ Real.sqrt (∑ j, (phi t j) ^ 2) := Real.abs_le_sqrt hle
    _ ≤ M := hM t

/-- **Theorem 11.1 (direct adaptive control), ideal plant level.** Let `V` be a
non-negative Lyapunov sequence for the controller-parameter error. Assume the
regressor growth bound (11.24)
`‖φ(t)‖ ≤ C₁ + C₂ · max_{j ≤ t+D+1} |ε₀(j)|` and the PAA dissipation (11.25)
`V(t+1) ≤ V(t) − (ε₀(t+D+1))² / (1 + ‖φ(t)‖²)`. Then the regressor norm is bounded
(11.26) and the a priori performance error tends to zero,
`ε₀(t + D + 1) → 0` (11.27).

The proof applies the noiseless direct-adaptive stability theorem
`direct_adaptive_stability_of_dissipation` at `x t = ‖φ(t)‖` and at the
non-negative sequence `|ε₀|`; the growth bound and the dissipation match
`hbound` and `hdiss` after unfolding `‖φ(t)‖² = ∑ k, (φ k t)²` and
`|ε₀|² = ε₀²`, and the conclusion about `|ε₀|` transfers to `ε₀` by
`tendsto_zero_iff_abs_tendsto_zero`. -/
theorem ideal_direct_adaptive_tracking {V : ℕ → ℝ} {n : ℕ} (phi : ℕ → Fin n → ℝ)
    (e : ℕ → ℝ) {C1 C2 : ℝ} (D : ℕ) (hV : ∀ t, 0 ≤ V t) (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hbound : ∀ t, Real.sqrt (∑ k, (phi t k) ^ 2) ≤
      C1 + C2 * (Finset.range (t + D + 2)).sup' (by simp) (fun j ↦ |e j|))
    (hdiss : ∀ t, V (t + 1) ≤ V t - (e (t + D + 1)) ^ 2 / (1 + ∑ k, (phi t k) ^ 2)) :
    (∃ M, ∀ t, Real.sqrt (∑ k, (phi t k) ^ 2) ≤ M) ∧
      Filter.Tendsto (fun t ↦ e (t + D + 1)) Filter.atTop (𝓝 0) := by
  let x : ℕ → ℝ := fun t ↦ Real.sqrt (∑ k, (phi t k) ^ 2)
  let e' : ℕ → ℝ := fun t ↦ |e t|
  have hx : ∀ t, 0 ≤ x t := fun t ↦ Real.sqrt_nonneg _
  have he' : ∀ t, 0 ≤ e' t := fun t ↦ abs_nonneg _
  have hbound' : ∀ t, x t ≤ C1 + C2 * (Finset.range (t + D + 2)).sup' (by simp) e' := by
    intro t
    simpa only [x, e'] using hbound t
  have hstep' : ∀ t, V (t + 1) ≤ V t - (e' (t + D + 1)) ^ 2 / (1 + (x t) ^ 2) := by
    intro t
    have hx2 : (x t) ^ 2 = ∑ k, (phi t k) ^ 2 := by
      simp only [x]
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun k _ ↦ sq_nonneg _))]
    have he2 : (e' (t + D + 1)) ^ 2 = (e (t + D + 1)) ^ 2 := by
      simp only [e', sq_abs]
    rw [hx2, he2]
    exact hdiss t
  obtain ⟨hM, htend⟩ :=
    direct_adaptive_stability_of_dissipation hV hx he' hC1 hC2 D hbound' hstep'
  have htend_abs : Filter.Tendsto (fun t ↦ |e (t + D + 1)|) Filter.atTop (𝓝 0) := by
    simpa only [e'] using htend
  exact ⟨by simpa only [x] using hM,
    (tendsto_zero_iff_abs_tendsto_zero _).mpr htend_abs⟩
