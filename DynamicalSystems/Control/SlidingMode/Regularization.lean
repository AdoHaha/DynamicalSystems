/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.Basic
public import DynamicalSystems.Control.SlidingMode.Relay
public import Mathlib.Basic.Real.Sign
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Boundary-layer regularization of the sliding-mode relay

This file records the boundary-layer regularization of the discontinuous relay
feedback of G. Bartolini, E. Punta and T. Zolezzi, *Regularization of Second
Order Sliding Mode Control Systems*, Chapter 1 in G. Bartolini, L. Fridman,
A. Pisano and E. Usai (eds.), *Modern Sliding Mode Control Theory: New
Perspectives and Applications*, LNCIS 375, Springer 2008 (printed pp. 3–21,
PDF pp. 19–37).

The discontinuous relay `relay k s = k * Real.sign s` of
`DynamicalSystems.Control.SlidingMode.Relay` is replaced, inside the boundary
layer `{|s| < ε}`, by the saturated relay
`boundaryLayerRelay k ε s = k * sat (s / ε)`, where `sat s = max (-1) (min 1 s)`
clamps its argument into `[-1, 1]`. The saturation `sat` is the metric projection
of `ℝ` onto the interval `[-1, 1]`: it is `1`-Lipschitz and hence continuous.
Away from the switching level the regularized relay is *exactly* the ideal relay
once `ε` is smaller than `|s|`, and it converges to the ideal relay pointwise for
every `s`, including `s = 0`. The regularized values always lie in the Filippov
convexification `[-k, k] = filippovSet (relay k) 0` at the switching level, which
is the bridge to the discontinuous-feedback semantics of
`DynamicalSystems.Control.SlidingMode.Filippov`.

## Main definitions

* `sat s`: the scalar saturation `max (-1) (min 1 s)`, the projection of `ℝ` onto
  `Set.Icc (-1) 1`.
* `boundaryLayerRelay k ε s`: the boundary-layer regularized relay
  `k * sat (s / ε)`.

## Main statements

* `sat_of_one_le`, `sat_of_le_neg_one`, `sat_of_mem_Icc`: the three value rules of
  the saturation, `sat_zero`: `sat 0 = 0`, and `abs_sat_le_one`, `sat_neg`: the
  range and the odd symmetry.
* `lipschitzWith_sat`, `continuous_sat`: `sat` is `1`-Lipschitz, hence continuous.
* `abs_boundaryLayerRelay_le`: the regularized relay is bounded by `|k|`.
* `tendsto_sat_div_sign`: pointwise convergence `sat (s / ε) → Real.sign s` along
  `𝓝[>] 0`, for every `s` (the family is eventually constant).
* `tendsto_boundaryLayerRelay`: pointwise convergence of the regularized relay to
  the ideal relay.
* `sat_div_eq_sign_of_abs_ge`: outside the layer `{|s| ≥ δ}` the saturation agrees
  with `Real.sign s` exactly, for `0 < ε ≤ δ`.
* `boundaryLayerRelay_mem_filippovSet`: the regularized relay values lie in
  `filippovSet (relay k) 0 = Set.Icc (-k) k`.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-! ### The scalar saturation -/

/-- The scalar saturation `sat s = max (-1) (min 1 s)`: the metric projection of
`ℝ` onto the interval `Set.Icc (-1) 1`. It clamps every real number into `[-1, 1]`
and is the identity there. -/
def sat (s : ℝ) : ℝ := max (-1) (min 1 s)

/-- The saturation of a number at least `1` is `1`. -/
theorem sat_of_one_le {s : ℝ} (h : 1 ≤ s) : sat s = 1 := by
  simp [sat, min_eq_left h]

/-- The saturation of a number at most `-1` is `-1`. -/
theorem sat_of_le_neg_one {s : ℝ} (h : s ≤ -1) : sat s = -1 := by
  have h1 : s ≤ 1 := by linarith
  simp [sat, min_eq_right h1, max_eq_left h]

/-- The saturation is the identity on `Set.Icc (-1) 1`. -/
theorem sat_of_mem_Icc {s : ℝ} (h : s ∈ Set.Icc (-1 : ℝ) 1) : sat s = s := by
  simp [sat, min_eq_right h.2, max_eq_right h.1]

/-- `sat 0 = 0`. -/
@[simp] theorem sat_zero : sat 0 = 0 :=
  sat_of_mem_Icc ⟨by norm_num, by norm_num⟩

/-- The saturation takes values in `[-1, 1]`. -/
theorem abs_sat_le_one (s : ℝ) : |sat s| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The saturation is odd: `sat (-s) = -sat s`. -/
theorem sat_neg (s : ℝ) : sat (-s) = -sat s := by
  rcases le_total s (-1) with h | h
  · rw [sat_of_le_neg_one h, sat_of_one_le (by linarith), neg_neg]
  rcases le_total s 1 with h1 | h1
  · rw [sat_of_mem_Icc ⟨h, h1⟩, sat_of_mem_Icc ⟨by linarith, by linarith⟩]
  · rw [sat_of_one_le h1, sat_of_le_neg_one (by linarith)]

/-- The saturation is `1`-Lipschitz, being the metric projection onto
`Set.Icc (-1) 1`. -/
theorem lipschitzWith_sat : LipschitzWith 1 sat :=
  (LipschitzWith.id.const_min (1 : ℝ)).const_max (-1)

/-- The saturation is continuous. -/
theorem continuous_sat : Continuous sat :=
  lipschitzWith_sat.continuous

/-! ### Boundary-layer regularization of the relay -/

/-- The boundary-layer regularized relay `boundaryLayerRelay k ε s = k * sat (s / ε)`.
Inside the layer `{|s| < ε}` it interpolates linearly between `-k` and `k`, and
outside it agrees with the ideal relay `relay k s = k * Real.sign s`. -/
noncomputable def boundaryLayerRelay (k ε : ℝ) (s : ℝ) : ℝ := k * sat (s / ε)

/-- The pointwise unfolding of `boundaryLayerRelay` (a `simp` lemma). -/
@[simp] theorem boundaryLayerRelay_apply (k ε s : ℝ) :
    boundaryLayerRelay k ε s = k * sat (s / ε) := rfl

/-- The regularized relay is bounded in magnitude by `|k|`. -/
theorem abs_boundaryLayerRelay_le (k ε s : ℝ) : |boundaryLayerRelay k ε s| ≤ |k| := by
  rw [boundaryLayerRelay_apply, abs_mul]
  calc |k| * |sat (s / ε)| ≤ |k| * 1 :=
        mul_le_mul_of_nonneg_left (abs_sat_le_one _) (abs_nonneg k)
    _ = |k| := mul_one _

/-- Pointwise convergence of the saturation `sat (s / ε)` to `Real.sign s` along
`𝓝[>] 0`, for **every** `s` including `s = 0`: the family is eventually constant
with value `Real.sign s`. -/
theorem tendsto_sat_div_sign (s : ℝ) :
    Tendsto (fun ε : ℝ ↦ sat (s / ε)) (𝓝[>] 0) (𝓝 (Real.sign s)) := by
  rcases lt_trichotomy s 0 with hneg | rfl | hpos
  · have heq : (fun ε : ℝ ↦ sat (s / ε)) =ᶠ[𝓝[>] 0] (fun _ ↦ Real.sign s) := by
      change ∀ᶠ ε in 𝓝[>] (0 : ℝ), sat (s / ε) = Real.sign s
      rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_Iio.mem_nhds (neg_pos.mpr hneg)] with ε hε hεpos
      rw [Set.mem_Iio] at hε
      rw [Set.mem_Ioi] at hεpos
      have hdiv : s / ε ≤ -1 := by
        rw [div_le_iff₀ hεpos]
        linarith
      rw [sat_of_le_neg_one hdiv, Real.sign_of_neg hneg]
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  · have heq : (fun ε : ℝ ↦ sat ((0 : ℝ) / ε)) =ᶠ[𝓝[>] 0]
        (fun _ ↦ Real.sign (0 : ℝ)) := by
      change ∀ᶠ ε in 𝓝[>] (0 : ℝ), sat ((0 : ℝ) / ε) = Real.sign 0
      filter_upwards with ε
      rw [zero_div, sat_zero, Real.sign_zero]
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  · have heq : (fun ε : ℝ ↦ sat (s / ε)) =ᶠ[𝓝[>] 0] (fun _ ↦ Real.sign s) := by
      change ∀ᶠ ε in 𝓝[>] (0 : ℝ), sat (s / ε) = Real.sign s
      rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_Iio.mem_nhds hpos] with ε hε hεpos
      rw [Set.mem_Iio] at hε
      rw [Set.mem_Ioi] at hεpos
      have hdiv : 1 ≤ s / ε := by
        rw [le_div_iff₀ hεpos]
        linarith
      rw [sat_of_one_le hdiv, Real.sign_of_pos hpos]
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds

/-- Pointwise convergence of the regularized relay to the ideal relay `relay k s`
along `𝓝[>] 0`, for every `s`. -/
theorem tendsto_boundaryLayerRelay (k s : ℝ) :
    Tendsto (fun ε : ℝ ↦ boundaryLayerRelay k ε s) (𝓝[>] 0) (𝓝 (relay k s)) := by
  simp only [boundaryLayerRelay_apply, relay_apply]
  exact (tendsto_sat_div_sign s).const_mul k

/-- Outside the boundary layer `{|s| ≥ δ}` the saturation `sat (s / ε)` equals
`Real.sign s` exactly, for every `0 < ε ≤ δ`. -/
theorem sat_div_eq_sign_of_abs_ge {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε0 : 0 < ε)
    (hεδ : ε ≤ δ) {s : ℝ} (hs : δ ≤ |s|) : sat (s / ε) = Real.sign s := by
  rcases le_total 0 s with hspos | hsneg
  · have hs' : δ ≤ s := by rwa [abs_of_nonneg hspos] at hs
    have h1 : 1 ≤ s / ε := by
      rw [le_div_iff₀ hε0, one_mul]
      exact hεδ.trans hs'
    rw [sat_of_one_le h1, Real.sign_of_pos (hδ.trans_le hs')]
  · have hs' : δ ≤ -s := by rwa [abs_of_nonpos hsneg] at hs
    have h1 : s / ε ≤ -1 := by
      rw [div_le_iff₀ hε0]
      linarith
    rw [sat_of_le_neg_one h1, Real.sign_of_neg (by linarith)]

/-- **S6 bridge.** The regularized relay value always lies in the Filippov
convexification of the ideal relay at the switching level,
`filippovSet (relay k) 0 = Set.Icc (-k) k`. The hypothesis `0 < ε` is retained to
match the frozen signature; the inclusion holds for every `ε`. -/
theorem boundaryLayerRelay_mem_filippovSet (k ε s : ℝ) (hk : 0 ≤ k) (_hε : 0 < ε) :
    boundaryLayerRelay k ε s ∈ filippovSet (relay k) 0 := by
  rcases eq_or_lt_of_le hk with hk0 | hkpos
  · subst hk0
    rw [show relay 0 = fun _ : ℝ ↦ (0 : ℝ) from by funext t; simp [relay_apply],
      filippovSet_of_continuous continuous_const]
    simp [boundaryLayerRelay_apply]
  · rw [filippovSet_relay_zero hkpos, Set.mem_Icc, boundaryLayerRelay_apply]
    have hsat := abs_sat_le_one (s / ε)
    rw [abs_le] at hsat
    constructor <;> nlinarith [hsat.1, hsat.2]
