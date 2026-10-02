/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Geometric contraction lemmas for homogeneous flows

This file collects the scalar and set-theoretic ingredients of the geometric-contraction
proof of Levant's Theorem 1 (A. Levant and L. Alelishvili, *Discontinuous Homogeneous
Control*, Chapter 4 of G. Bartolini, L. Fridman, A. Pisano and E. Usai (eds.), *Modern
Sliding Mode Control Theory: New Perspectives and Applications*, LNCIS 375, Springer 2008,
printed pp. 74–75, PDF pp. 90–91).

The key point is that a flow whose trajectories scale under a dilation action with a
*positive* time exponent `p` contracts a retractable domain by the factor `λ < 1` at each
step, and the accumulated settling time is the geometric series
`T * ∑_{k < N} (λ ^ p) ^ k → T / (1 - λ ^ p)`.

## Main definitions

* `geometricPartialSum`: the geometric partial sum `T * ∑_{k < N} (λ ^ p) ^ k`.

## Main results

* `rpow_pow_comm`: the power-law commutation `(x ^ N) ^ p = (x ^ p) ^ N` for `x ≥ 0`,
  reusing Mathlib's `Real.rpow_pow_comm`.
* `tendsto_geometricPartialSum`: the geometric partial sums converge to `T / (1 - λ ^ p)`
  for `0 ≤ λ < 1` and `0 < p`.
* `image_subset_of_le`: dilation-retractability makes the dilated images monotone,
  `d (λ ^ k) '' D ⊆ d (λ ^ N) '' D` for `k ≥ N`.
-/

open Filter
open scoped Topology

@[expose] public section

/-- **Power-law commutation.** For `x ≥ 0`, a real exponent `p` and a natural number `N`,
`(x ^ N) ^ p = (x ^ p) ^ N`. This is the identity that equates the time increment
`(λ ^ p) ^ N` with the homogeneity scaling `(λ ^ N) ^ p`, and is the riskiest arithmetic
step of the geometric-contraction proof. It is the symmetric form of Mathlib's
`Real.rpow_pow_comm`. -/
theorem rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (p : ℝ) (N : ℕ) :
    (x ^ N) ^ p = (x ^ p) ^ N :=
  (Real.rpow_pow_comm hx p N).symm

/-- The geometric partial sum `s_N = T * ∑_{k < N} (λ ^ p) ^ k`. Its limit as `N → ∞`
is the accumulated settling time of the geometric contraction. -/
noncomputable def geometricPartialSum (T l p : ℝ) (N : ℕ) : ℝ :=
  T * ∑ k ∈ Finset.range N, (l ^ p) ^ k

/-- **Geometric series limit.** For `0 ≤ λ < 1` and a positive time exponent `p`, the
geometric partial sums `T * ∑_{k < N} (λ ^ p) ^ k` converge to `T / (1 - λ ^ p)`.

The positivity `0 < p` is needed for `λ ^ p < 1`: for `p < 0` the ratio `λ ^ p` exceeds
`1` and the series diverges, while `p = 0` makes the ratio `1`. -/
theorem tendsto_geometricPartialSum {T l p : ℝ} (hp : 0 < p) (hl0 : 0 ≤ l)
    (hl1 : l < 1) :
    Filter.Tendsto (geometricPartialSum T l p) Filter.atTop (𝓝 (T / (1 - l ^ p))) := by
  have hlp0 : 0 ≤ l ^ p := Real.rpow_nonneg hl0 p
  have hlp1 : l ^ p < 1 := Real.rpow_lt_one hl0 hl1 hp
  have hsum : HasSum (fun k : ℕ ↦ (l ^ p) ^ k) ((1 - l ^ p)⁻¹) :=
    hasSum_geometric_of_lt_one hlp0 hlp1
  have htend : Filter.Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range N, (l ^ p) ^ k) Filter.atTop
      (𝓝 ((1 - l ^ p)⁻¹)) := hsum.tendsto_sum_nat
  exact Filter.Tendsto.const_mul T htend

/-- **Monotonicity of dilated images.** Let `d` be a dilation action (`d 1 = id` and
`d (κ * μ) = d κ ∘ d μ` for `κ, μ > 0`) that retracts a set `D` for contractions
(`0 < κ ≤ 1` implies `d κ '' D ⊆ D`). Then for `0 < λ < 1` and `k ≥ N` the image under
the larger contraction `d (λ ^ k)` is contained in the image under `d (λ ^ N)`.

Indeed `λ ^ k = λ ^ N * λ ^ (k - N)` with `λ ^ (k - N) ≤ 1`, so any `d (λ ^ k) y` is
`d (λ ^ N) (d (λ ^ (k - N)) y)` and the inner point still lies in `D`. -/
theorem image_subset_of_le {E : Type*} {d : ℝ → E → E}
    (hd : (d 1 = id) ∧ ∀ κ μ, 0 < κ → 0 < μ → ∀ x, d (κ * μ) x = d κ (d μ x))
    {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {D : Set E}
    (hD : ∀ κ, 0 < κ → κ ≤ 1 → ∀ y ∈ D, d κ y ∈ D) {N k : ℕ} (hkN : N ≤ k) :
    d (l ^ k) '' D ⊆ d (l ^ N) '' D := by
  rintro z ⟨y, hyD, rfl⟩
  refine ⟨d (l ^ (k - N)) y, hD (l ^ (k - N)) (pow_pos hl0 _)
    (pow_le_one₀ hl0.le hl1.le) y hyD, ?_⟩
  have hpow : l ^ N * l ^ (k - N) = l ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rw [← hd.2 (l ^ N) (l ^ (k - N)) (pow_pos hl0 _) (pow_pos hl0 _) y, hpow]
