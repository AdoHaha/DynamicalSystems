/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.DiscreteTime.Lyapunov
public import Mathlib.Basic.Real.Sign

/-! # Dead-zone PAA scalar core

This file formalizes the scalar core of the parameter adaptation algorithm (PAA)
with dead zone of I. D. Landau, R. Lozano, M'Saad and A. Karimi, *Adaptive
Control: Algorithms, Analysis and Applications*, 2nd ed., Springer 2011,
Chapter 10 (Theorem 10.2, eqs. 10.36-10.39 and 10.45-10.47).

The dead-zone function maps an adaptation error `x` to `0` when `|x| ≤ Δ` and to
`x - Δ · sign x` otherwise. The dead zone makes the parameter update vanish for
errors below the disturbance bound `Δ`, which prevents parameter drift.

## Main definitions

* `deadZone Δ x`: the dead-zone function with level `Δ`.

## Main results

* `mul_deadZone_nonneg`: `x · deadZone Δ x ≥ 0`, so the dead-zoned error drives a
  non-negative Lyapunov dissipation rate.
* `abs_deadZone_le`: the dead zone does not increase the error magnitude,
  `|deadZone Δ x| ≤ |x|`.
* `deadZone_error_tendsto_zero`: the dead-zoned error of a Lyapunov sequence
  descending by `ν t · deadZone Δ (ν t)` tends to `0`.
-/

@[expose] public section

open scoped Topology

/-- The dead-zone function of Theorem 10.2: it vanishes inside `[-Δ, Δ]` and equals
`x - Δ · sign x` outside, so that the parameter update stops once the adaptation
error is below the disturbance bound `Δ`. -/
noncomputable def deadZone (Δ x : ℝ) : ℝ := if |x| ≤ Δ then 0 else x - Δ * Real.sign x

/-- The dead-zoned error makes non-negative progress: `0 ≤ x · deadZone Δ x` for
`Δ ≥ 0`. This is the non-negativity needed to feed the scalar dissipation bridge
`DiscreteTime.Lyapunov.tendsto_zero_of_succ_le_sub`. -/
theorem mul_deadZone_nonneg {Δ : ℝ} (hΔ : 0 ≤ Δ) (x : ℝ) : 0 ≤ x * deadZone Δ x := by
  rw [deadZone]
  split_ifs with hx
  · simp
  · rw [not_le] at hx
    rcases lt_trichotomy x 0 with hneg | hzero | hpos
    · rw [Real.sign_of_neg hneg]
      rw [abs_of_neg hneg] at hx
      exact mul_nonneg_of_nonpos_of_nonpos hneg.le (by linarith)
    · rw [hzero, abs_zero] at hx
      linarith
    · rw [Real.sign_of_pos hpos]
      rw [abs_of_pos hpos] at hx
      exact mul_nonneg hpos.le (by linarith)

/-- The dead zone does not increase the error magnitude: `|deadZone Δ x| ≤ |x|`
for `Δ ≥ 0`. -/
theorem abs_deadZone_le {Δ : ℝ} (hΔ : 0 ≤ Δ) (x : ℝ) : |deadZone Δ x| ≤ |x| := by
  rw [deadZone]
  split_ifs with hx
  · simp
  · rw [not_le] at hx
    rcases lt_trichotomy x 0 with hneg | hzero | hpos
    · rw [Real.sign_of_neg hneg, mul_neg_one, sub_neg_eq_add]
      rw [abs_of_neg hneg] at hx ⊢
      rw [abs_of_neg (by linarith : x + Δ < 0)]
      linarith
    · rw [hzero, abs_zero] at hx
      linarith
    · rw [Real.sign_of_pos hpos, mul_one]
      rw [abs_of_pos hpos] at hx ⊢
      rw [abs_of_pos (by linarith : 0 < x - Δ)]
      linarith

/-- The squared dead-zone value is dominated by the absolute value of the
Lyapunov dissipation rate `x · deadZone Δ x`. This upgrades the convergence of the
rate `ν t · deadZone Δ (ν t)` to convergence of `deadZone Δ (ν t)` itself. -/
private lemma sq_abs_deadZone_le {Δ : ℝ} (hΔ : 0 ≤ Δ) (x : ℝ) :
    |deadZone Δ x| ^ 2 ≤ |x * deadZone Δ x| := by
  have h := mul_le_mul_of_nonneg_right (abs_deadZone_le hΔ x) (abs_nonneg (deadZone Δ x))
  rw [abs_mul]
  calc |deadZone Δ x| ^ 2 = |deadZone Δ x| * |deadZone Δ x| := by ring
    _ ≤ |x| * |deadZone Δ x| := h

/-- Dead-zone PAA convergence (Theorem 10.2): if a non-negative Lyapunov sequence
`V` descends by the dead-zoned error, `V (t + 1) ≤ V t - ν t · deadZone Δ (ν t)`,
then the dead-zoned error tends to `0`. The scalar dissipation bridge applied to the
non-negative rate `w t = ν t · deadZone Δ (ν t)` yields `w → 0`; since
`|deadZone Δ (ν t)| ^ 2 ≤ |w t|`, taking square roots and squeezing gives
`deadZone Δ (ν t) → 0`. -/
theorem deadZone_error_tendsto_zero {V ν : ℕ → ℝ} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hV : ∀ t, 0 ≤ V t) (hstep : ∀ t, V (t + 1) ≤ V t - ν t * deadZone Δ (ν t)) :
    Filter.Tendsto (fun t ↦ deadZone Δ (ν t)) Filter.atTop (𝓝 0) := by
  have hw : Filter.Tendsto (fun t ↦ ν t * deadZone Δ (ν t)) Filter.atTop (𝓝 0) :=
    tendsto_zero_of_succ_le_sub hV (fun t ↦ mul_deadZone_nonneg hΔ (ν t)) hstep
  have hwabs :
      Filter.Tendsto (fun t ↦ |ν t * deadZone Δ (ν t)|) Filter.atTop (𝓝 0) := by
    simpa only [abs_zero] using hw.abs
  have hsqrt :
      Filter.Tendsto (fun t ↦ Real.sqrt |ν t * deadZone Δ (ν t)|) Filter.atTop (𝓝 0) := by
    have hcont : Filter.Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
      simpa using Real.continuous_sqrt.tendsto 0
    exact hcont.comp hwabs
  have hDabs : Filter.Tendsto (fun t ↦ |deadZone Δ (ν t)|) Filter.atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ abs_nonneg _)
      (fun t ↦ Real.le_sqrt_of_sq_le (sq_abs_deadZone_le hΔ (ν t))) hsqrt
  rwa [tendsto_zero_iff_abs_tendsto_zero]

/-- Book-faithful dead-zone stopping-rule result (Theorem 10.2, eqs. 10.45-10.48).
The switching signal `α` takes only the values `0` and `1`; `hcond` encodes the
stopping rule (the PAA is active, `α t = 1`, whenever the adaptation error exceeds
the disturbance bound `Δ`); and the driving term `α t · (ν t ^ 2 - Δ ^ 2)` converges
to `0`. Then `|ν|` is eventually bounded by `Δ + ε` for every `ε > 0`, i.e.
`limsup |ν| ≤ Δ`. Note this is the sharp conclusion: `ν` itself need not tend to
`0`, only its limsup is bounded by the disturbance level. -/
theorem deadzone_eventually_le {ν : ℕ → ℝ} {Δ : ℝ} (hΔ : 0 ≤ Δ) (alpha : ℕ → ℝ)
    (halpha : ∀ t, alpha t = 0 ∨ alpha t = 1)
    (hcond : ∀ t, Δ < |ν t| → alpha t = 1)
    (htend : Filter.Tendsto (fun t ↦ alpha t * (ν t ^ 2 - Δ ^ 2)) Filter.atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ t in Filter.atTop, |ν t| ≤ Δ + ε := by
  intro ε hε
  have _hα := halpha
  have hε2 : 0 < ε ^ 2 := by positivity
  have hlt : ∀ᶠ t in Filter.atTop, alpha t * (ν t ^ 2 - Δ ^ 2) < ε ^ 2 :=
    (tendsto_order.1 htend).2 (ε ^ 2) hε2
  filter_upwards [hlt] with t ht
  by_contra h
  rw [not_le] at h
  have hcond_t : alpha t = 1 := hcond t (by linarith)
  have hkey : ε ^ 2 < ν t ^ 2 - Δ ^ 2 := by
    have hsq : (Δ + ε) ^ 2 < ν t ^ 2 := by
      have hltabs : |Δ + ε| < |ν t| := by
        rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Δ + ε)]
      simpa only [sq_abs] using sq_lt_sq.mpr hltabs
    nlinarith [hΔ, hε.le]
  rw [hcond_t, one_mul] at ht
  linarith
