/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.DiscreteTime.Comparison
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Discrete ultimate boundedness from the comparison estimate

This file is the eventual (ultimate) counterpart of the discrete comparison
estimate of `DynamicalSystems.DiscreteTime.Comparison`. Given a non-negative
sequence satisfying the contraction

`v (t + 1) ≤ a * v t + d`,  `0 ≤ a < 1`,

the affine comparison bound `v t ≤ a ^ t * v 0 + d * (1 - a ^ t) / (1 - a)`
shows that `v` is bounded by `max (v 0) (d / (1 - a))` and that its excess over
the equilibrium level `d / (1 - a)` decays geometrically.

## A note on the requested statement

The campaign contract asks for

`eventually_le_of_succ_le_mul_add : ∀ᶠ t, v t ≤ d / (1 - a)`.

**That statement is false**, so it cannot be formalized here. The reason is that
the comparison bound is sharp: the sequence

`v t = d / (1 - a) + a ^ t * (v 0 - d / (1 - a))`

satisfies `v (t + 1) = a * v t + d`, `v ≥ 0` and `0 ≤ a < 1`, but for
`v 0 > d / (1 - a)` it exceeds `d / (1 - a)` at every finite time `t`, since
`a ^ t > 0`. For example, with `a = 1 / 2`, `d = 1`, `v 0 = 10` the sequence
`v t = 2 + 8 * (1 / 2) ^ t` is positive, satisfies the recurrence with equality,
and is `> 2 = d / (1 - a)` for every `t`. See
`not_eventually_le_of_succ_le_mul_add` below for a machine-checked version.

The correct and standard ultimate-bound statement carries an `ε` of slack, and is
provided as `eventually_le_add_of_succ_le_mul_add`:

`∀ ε > 0, ∀ᶠ t, v t ≤ d / (1 - a) + ε`.

This is exactly the statement needed downstream (a limit-superior bound, not a
pointwise eventual inequality).

## Main statements

* `le_max_of_succ_le_mul_add`: uniform bound `v t ≤ max (v 0) (d / (1 - a))`.
* `le_of_succ_le_mul_add_of_le`: when `v 0 ≤ d / (1 - a)`, the pointwise bound
  `v t ≤ d / (1 - a)` holds for *all* `t` (in particular eventually).
* `eventually_le_add_of_succ_le_mul_add`: the correct eventual bound with `ε`-slack.
* `not_eventually_le_of_succ_le_mul_add`: the requested pointwise eventual bound
  is false (counterexample).
-/

open Filter
open scoped Topology

@[expose] public section

/-- Uniform bound for a non-negative sequence satisfying `v (t + 1) ≤ a * v t + d`
with `0 ≤ a < 1`: `v t ≤ max (v 0) (d / (1 - a))`.

The comparison sequence `a ^ t * v 0 + d * (1 - a ^ t) / (1 - a)` is the convex
combination `d / (1 - a) + a ^ t * (v 0 - d / (1 - a))` of `v 0` and `d / (1 - a)`
with weights `a ^ t ∈ [0, 1]` and `1 - a ^ t`; hence it is at most the maximum of
the two endpoints. -/
theorem le_max_of_succ_le_mul_add {v : ℕ → ℝ} {a d : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hv : ∀ t, 0 ≤ v t) (h : ∀ t, v (t + 1) ≤ a * v t + d) (t : ℕ) :
    v t ≤ max (v 0) (d / (1 - a)) := by
  have hne : (1 : ℝ) - a ≠ 0 := by linarith
  have hB := le_of_succ_le_mul_add ha0 ha1 hv h t
  have hBeq : a ^ t * v 0 + d * (1 - a ^ t) / (1 - a)
      = d / (1 - a) + a ^ t * (v 0 - d / (1 - a)) := by
    field_simp
    ring
  rw [hBeq] at hB
  have hpow0 : 0 ≤ a ^ t := pow_nonneg ha0 t
  have hpow1 : a ^ t ≤ 1 := pow_le_one₀ (n := t) ha0 ha1.le
  rcases le_total (v 0) (d / (1 - a)) with hc | hc
  · have : d / (1 - a) + a ^ t * (v 0 - d / (1 - a)) ≤ d / (1 - a) := by
      have hle0 : a ^ t * (v 0 - d / (1 - a)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpow0 (by linarith)
      linarith
    exact hB.trans (this.trans (le_max_right _ _))
  · have : d / (1 - a) + a ^ t * (v 0 - d / (1 - a)) ≤ v 0 := by
      have h2 : a ^ t * (v 0 - d / (1 - a)) ≤ v 0 - d / (1 - a) := by
        nlinarith [mul_le_mul_of_nonneg_right hpow1 (by linarith : 0 ≤ v 0 - d / (1 - a))]
      linarith
    exact hB.trans (this.trans (le_max_left _ _))

/-- If `v 0 ≤ d / (1 - a)` (the initial value is already below the equilibrium
level), the pointwise bound `v t ≤ d / (1 - a)` holds for *every* `t`, hence in
particular eventually. This is the exact conclusion of the requested
`eventually_le_of_succ_le_mul_add` in the regime that excludes the
counterexample `not_eventually_le_of_succ_le_mul_add`. -/
theorem le_of_succ_le_mul_add_of_le {v : ℕ → ℝ} {a d : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hv : ∀ t, 0 ≤ v t) (h : ∀ t, v (t + 1) ≤ a * v t + d) (h0 : v 0 ≤ d / (1 - a))
    (t : ℕ) : v t ≤ d / (1 - a) := by
  have hmax := le_max_of_succ_le_mul_add ha0 ha1 hv h t
  rwa [max_eq_right h0] at hmax

/-- The correct eventual (ultimate) bound: if `v ≥ 0` and `v (t + 1) ≤ a * v t + d`
with `0 ≤ a < 1`, then for every `ε > 0` the sequence is eventually at most
`d / (1 - a) + ε`.

This is the standard limit-superior ultimate bound. The requested pointwise form
`∀ᶠ t, v t ≤ d / (1 - a)` (without slack) is false; see
`not_eventually_le_of_succ_le_mul_add`. -/
theorem eventually_le_add_of_succ_le_mul_add {v : ℕ → ℝ} {a d : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a < 1) (hv : ∀ t, 0 ≤ v t) (h : ∀ t, v (t + 1) ≤ a * v t + d) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ t in Filter.atTop, v t ≤ d / (1 - a) + ε := by
  have hne : (1 : ℝ) - a ≠ 0 := by linarith
  have hpow : Tendsto (fun t : ℕ ↦ a ^ t) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
  have hmul : Tendsto (fun t : ℕ ↦ a ^ t * (v 0 - d / (1 - a))) Filter.atTop (𝓝 0) := by
    simpa using hpow.mul_const (v 0 - d / (1 - a))
  have hev : ∀ᶠ t in Filter.atTop, a ^ t * (v 0 - d / (1 - a)) < ε :=
    hmul.eventually_lt tendsto_const_nhds hε
  have hBeq : ∀ t : ℕ, a ^ t * v 0 + d * (1 - a ^ t) / (1 - a)
      = d / (1 - a) + a ^ t * (v 0 - d / (1 - a)) := by
    intro t
    field_simp
    ring
  filter_upwards [hev] with t ht
  have hB := le_of_succ_le_mul_add ha0 ha1 hv h t
  rw [hBeq t] at hB
  linarith

/-- The pointwise eventual bound requested by the campaign contract is refuted by
the explicit sequence `v t = 2 + 8 * (1 / 2) ^ t` with `a = 1 / 2`, `d = 1`,
`v 0 = 10`: it is positive, satisfies `v (t + 1) = (1 / 2) * v t + 1`, but
`v t > 2 = d / (1 - a)` for every `t`. -/
theorem not_eventually_le_of_succ_le_mul_add :
    ¬ (∀ᶠ t in Filter.atTop,
        (fun t : ℕ ↦ 2 + 8 * (1 / 2 : ℝ) ^ t) t ≤ (1 : ℝ) / (1 - (1 / 2))) := by
  intro h
  obtain ⟨t, ht⟩ := h.exists
  have h2 : 2 < (fun t : ℕ ↦ 2 + 8 * (1 / 2 : ℝ) ^ t) t := by
    have : 0 < 8 * (1 / 2 : ℝ) ^ t := by positivity
    dsimp only
    linarith
  norm_num at ht
  linarith
