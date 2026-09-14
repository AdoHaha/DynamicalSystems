/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.UniformSpace.Basic

/-!
# Barbălat's lemma

This file proves Barbălat's lemma in the vector-valued form of [Farkas-Wegner2016,
Theorem 4]: a uniformly continuous function on the half-line `[0, ∞)` whose improper
integral converges must converge to zero at infinity.

The proof is the direct "hard analysis" estimate of [Farkas-Wegner2016, Theorem 1].
Because the improper integral `t ↦ ∫ x in 0..t, f x` is Cauchy at `+∞`, the tail
integral `∫ x in t..t+s, f x` is small for large `t` (for any fixed `s > 0`).
Writing `f t` as the mean of `f` over `[t, t + s]` together with the oscillation
`f t - f x`, and choosing `s` below the uniform-continuity modulus, makes the
oscillation term small; the mean term is controlled by the Cauchy property.

## Main statements

- `Barbalat.tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral`:
  Barbălat's lemma for `f : ℝ → E` with `E` a Banach space.
- `Barbalat.tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral_real`:
  the scalar (`E = ℝ`) corollary.

The main theorem would upstream to the root namespace under a Mathlib-style name.

## References

* [B. Farkas and S.-A. Wegner, *Variations on Barbălat's Lemma*][Farkas-Wegner2016]

[Farkas-Wegner2016]: https://arxiv.org/abs/1411.1611
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace Barbalat

/-- **Barbălat's lemma**, vector-valued form (Farkas–Wegner, Theorem 4). If `f : ℝ → E`
is uniformly continuous on `[0, ∞)` and the improper integral `t ↦ ∫ x in 0..t, f x`
converges as `t → ∞`, then `f t → 0`.

The completeness assumption on `E` is necessary: the Bochner integral is defined to be
zero on incomplete normed spaces, so without it the hypothesis would be vacuous while
the conclusion need not hold. -/
theorem tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (huc : UniformContinuousOn f (Set.Ici 0))
    (h : ∃ L, Tendsto (fun t : ℝ ↦ ∫ x in (0 : ℝ)..t, f x) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hcont : ContinuousOn f (Set.Ici 0) := huc.continuousOn
  -- Extract a uniform-continuity modulus for the tolerance `ε / 2`.
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) hε2
  -- The oscillation scale, chosen strictly below `δ`.
  set s : ℝ := δ / 2 with hs_def
  have hspos : 0 < s := half_pos hδpos
  have hslt : s < δ := half_lt_self hδpos
  rcases h with ⟨L, hL⟩
  -- Integrability on intervals contained in `[0, ∞)`.
  have hInt : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable f volume 0 t := fun t ht =>
    ContinuousOn.intervalIntegrable_of_Icc ht (hcont.mono fun _ hx => hx.1)
  have hInt2 : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable f volume t (t + s) := fun t ht =>
    ContinuousOn.intervalIntegrable_of_Icc (by linarith [hspos])
      (hcont.mono fun _ hx => le_trans ht hx.1)
  -- The difference of the shifted improper integrals is the tail interval integral.
  have htail_eq : ∀ t : ℝ, 0 ≤ t →
      ∫ x in t..(t + s), f x = (∫ x in (0 : ℝ)..(t + s), f x) - ∫ x in (0 : ℝ)..t, f x := by
    intro t ht
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hInt t ht) (hInt2 t ht)
    rw [← hadd]
    abel
  have hLs : Tendsto (fun t : ℝ ↦ ∫ x in (0 : ℝ)..(t + s), f x) atTop (𝓝 L) :=
    hL.comp (Filter.tendsto_atTop_add_const_right atTop s tendsto_id)
  have hD : Tendsto (fun t : ℝ ↦
      (∫ x in (0 : ℝ)..(t + s), f x) - ∫ x in (0 : ℝ)..t, f x) atTop (𝓝 0) := by
    simpa using hLs.sub hL
  -- Scaling by `1 / s`, this difference is eventually below `ε / 2`.
  have hev1 : ∀ᶠ t : ℝ in atTop,
      ‖(1 / s) • ((∫ x in (0 : ℝ)..(t + s), f x) - ∫ x in (0 : ℝ)..t, f x)‖ < ε / 2 := by
    have hD' := hD.const_smul (1 / s)
    have := (Metric.tendsto_nhds.mp (by simpa using hD')) (ε / 2) hε2
    simpa [dist_eq_norm] using this
  filter_upwards [eventually_ge_atTop (0 : ℝ), hev1] with t ht hnorm
  rw [← htail_eq t ht] at hnorm
  rw [dist_zero_right]
  have hg : IntervalIntegrable (fun _ : ℝ ↦ f t) volume t (t + s) :=
    intervalIntegrable_const
  -- The constant integral over an interval of length `s`.
  have hconst : (∫ x in t..(t + s), f t) = s • f t := by
    rw [intervalIntegral.integral_const, add_sub_cancel_left]
  -- The mean of `f` over the tail equals `f t` plus its oscillation.
  have hsub : (∫ x in t..(t + s), f x) - (∫ x in t..(t + s), (f x - f t)) = s • f t := by
    rw [intervalIntegral.integral_sub (hInt2 t ht) hg, hconst]
    abel
  have hft_eq : f t = (1 / s) • (∫ x in t..(t + s), f x) -
      (1 / s) • (∫ x in t..(t + s), (f x - f t)) := by
    rw [← smul_sub, hsub, smul_smul, one_div_mul_cancel hspos.ne', one_smul]
  -- The oscillation term is bounded by `ε / 2`.
  have hbound_int : ∀ x ∈ Set.uIoc t (t + s), ‖f x - f t‖ ≤ ε / 2 := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith [hspos])] at hx
    have hx0 : 0 ≤ x := le_trans ht hx.1.le
    have hdist : dist x t < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
      have : x - t ≤ s := by linarith [hx.2]
      linarith [hslt]
    have hh := hδ t ht x hx0 (by rwa [dist_comm])
    have h' : ‖f x - f t‖ < ε / 2 := by
      rwa [dist_eq_norm, norm_sub_rev] at hh
    exact h'.le
  have hB : ‖(1 / s) • (∫ x in t..(t + s), (f x - f t))‖ ≤ ε / 2 := by
    have hIntp := intervalIntegral.norm_integral_le_of_norm_le_const hbound_int
    have hIntp' : ‖∫ x in t..(t + s), (f x - f t)‖ ≤ (ε / 2) * s := by
      simpa [add_sub_cancel_left, abs_of_pos hspos] using hIntp
    calc
      ‖(1 / s) • (∫ x in t..(t + s), (f x - f t))‖
          = (1 / s) * ‖∫ x in t..(t + s), (f x - f t)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hspos)]
      _ ≤ (1 / s) * ((ε / 2) * s) := by gcongr
      _ = ε / 2 := by
            rw [mul_comm (ε / 2) s, ← mul_assoc, one_div_mul_cancel hspos.ne', one_mul]
  have hnorm_le : ‖f t‖ ≤ ‖(1 / s) • (∫ x in t..(t + s), f x)‖ +
      ‖(1 / s) • (∫ x in t..(t + s), (f x - f t))‖ := by
    have h := norm_sub_le ((1 / s) • (∫ x in t..(t + s), f x))
      ((1 / s) • (∫ x in t..(t + s), (f x - f t)))
    rwa [← hft_eq] at h
  calc
    ‖f t‖ ≤ ‖(1 / s) • (∫ x in t..(t + s), f x)‖ +
        ‖(1 / s) • (∫ x in t..(t + s), (f x - f t))‖ := hnorm_le
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hnorm hB
    _ = ε := by ring

/-- **Barbălat's lemma**, scalar form (Farkas–Wegner, Theorem 1). If `f : ℝ → ℝ` is
uniformly continuous on `[0, ∞)` and the improper integral `t ↦ ∫ x in 0..t, f x`
converges as `t → ∞`, then `f t → 0`. -/
theorem tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral_real
    {f : ℝ → ℝ} (huc : UniformContinuousOn f (Set.Ici 0))
    (h : ∃ L, Tendsto (fun t : ℝ ↦ ∫ x in (0 : ℝ)..t, f x) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 0) :=
  tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral huc h

end Barbalat
