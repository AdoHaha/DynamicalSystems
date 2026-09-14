/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.Order.OrderClosed
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

/-- The tail supremum `S(t) = ⨆ u ≥ t, ‖∫ x in t..u, f x‖` of the norms of the tail
integrals of `f`. This is the quantitative scale appearing in the direct proof of
Barbălat's lemma (Farkas–Wegner, Lemma 2). -/
def tailSup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (t : ℝ) : ℝ :=
  ⨆ u : {u : ℝ // t ≤ u}, ‖∫ x in t..u, f x‖

/-- The key estimate behind the quantitative core of Barbălat's lemma: for every `s > 0`,
`s * ‖f t‖ ≤ S(t) + ω s * s`, where `S(t) = tailSup f t` is the tail supremum and `ω` is a
nondecreasing modulus of continuity for `f`. -/
lemma mul_norm_le_tailSup_add_mul_modulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {ω : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 0))
    (hmod : ∀ x y, dist (f x) (f y) ≤ ω (dist x y))
    (hmono : Monotone ω)
    {t : ℝ} (ht : 0 ≤ t)
    (hS : BddAbove (Set.range fun u : {u : ℝ // t ≤ u} ↦ ‖∫ x in t..u, f x‖))
    {s : ℝ} (hs : 0 < s) :
    s * ‖f t‖ ≤ tailSup f t + ω s * s := by
  have hle : t ≤ t + s := by linarith
  have hInt : IntervalIntegrable f volume t (t + s) :=
    ContinuousOn.intervalIntegrable_of_Icc hle (hcont.mono fun x hx ↦ le_trans ht hx.1)
  have hub : ‖∫ x in t..(t + s), f x‖ ≤ tailSup f t := by
    simpa only [tailSup] using le_ciSup hS ⟨t + s, hle⟩
  have hosc : ‖∫ x in t..(t + s), (f x - f t)‖ ≤ ω s * s := by
    have hbound : ∀ x ∈ Set.uIoc t (t + s), ‖f x - f t‖ ≤ ω s := by
      intro x hx
      rw [Set.uIoc_of_le hle] at hx
      have hd : dist x t ≤ s := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
        linarith [hx.2]
      calc ‖f x - f t‖ ≤ ω (dist x t) := by simpa [dist_eq_norm] using hmod x t
        _ ≤ ω s := hmono hd
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    simpa [add_sub_cancel_left, abs_of_pos hs] using this
  have hconst : (∫ x in t..(t + s), (f t : E)) = s • f t := by
    rw [intervalIntegral.integral_const, add_sub_cancel_left]
  have hsplit : s • f t =
      (∫ x in t..(t + s), f x) - ∫ x in t..(t + s), (f x - f t) := by
    rw [intervalIntegral.integral_sub hInt intervalIntegrable_const, hconst]
    abel
  have h1 : ‖s • f t‖ = s * ‖f t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have h2 := norm_sub_le (∫ x in t..(t + s), f x)
    (∫ x in t..(t + s), (f x - f t))
  rw [← hsplit, h1] at h2
  linarith [hub, hosc]

/-- **Quantitative core of Barbălat's lemma** (Farkas–Wegner, Lemmas 2 and 3). Let `f` be
continuous on `[0, ∞)`, let `ω` be a nondecreasing modulus of continuity for `f` which is
continuous at `0`, and suppose the tail integrals of `f` starting at `t` are bounded, so that
`S(t) = tailSup f t` is a genuine real number. Then `‖f t‖ ≤ √(S t) + ω (√(S t))`. -/
theorem norm_le_sqrt_tail_add_modulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {ω : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 0))
    (hmod : ∀ x y, dist (f x) (f y) ≤ ω (dist x y))
    (hmono : Monotone ω)
    (hωcont : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (ω 0)))
    {t : ℝ} (ht : 0 ≤ t)
    (hS : BddAbove (Set.range fun u : {u : ℝ // t ≤ u} ↦ ‖∫ x in t..u, f x‖)) :
    ‖f t‖ ≤ Real.sqrt (tailSup f t) + ω (Real.sqrt (tailSup f t)) := by
  have hSnonneg : 0 ≤ tailSup f t := by
    calc (0 : ℝ) = ‖∫ x in t..t, f x‖ := by simp
      _ ≤ tailSup f t := by
          simpa only [tailSup] using le_ciSup hS ⟨t, le_rfl⟩
  -- The estimate `‖f t‖ ≤ S / s + ω s` for every `s > 0`.
  have hkey : ∀ s : ℝ, 0 < s → ‖f t‖ ≤ tailSup f t / s + ω s := by
    intro s hs
    have h := mul_norm_le_tailSup_add_mul_modulus hcont hmod hmono ht hS hs
    have hmul : s * (tailSup f t / s + ω s) = tailSup f t + ω s * s := by
      rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hs)]
      ring
    exact le_of_mul_le_mul_left (by rw [hmul]; exact h) hs
  rcases lt_or_eq_of_le hSnonneg with hSpos | hSzero
  · have hs : 0 < Real.sqrt (tailSup f t) := Real.sqrt_pos.mpr hSpos
    have h := hkey (Real.sqrt (tailSup f t)) hs
    have hdiv : tailSup f t / Real.sqrt (tailSup f t) = Real.sqrt (tailSup f t) := by
      rw [div_eq_iff (ne_of_gt hs)]
      simpa [pow_two, mul_comm] using (Real.sq_sqrt hSnonneg).symm
    rwa [hdiv] at h
  · have hb : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖f t‖ ≤ ω s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have h := hkey s hs
      rwa [← hSzero, zero_div, zero_add] at h
    have hle : ‖f t‖ ≤ ω 0 := ge_of_tendsto hωcont hb
    rw [hSzero.symm]
    simpa using hle

/-- The primitive `t ↦ ∫ x in 0..t, f x` of a function continuous on `[0, ∞)` is bounded on
`[0, ∞)` whenever its improper integral converges: it is bounded near `∞` by convergence and
on the initial compact interval by the uniform bound on `f`. -/
theorem exists_bound_primitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hcont : ContinuousOn f (Set.Ici 0))
    (h : ∃ L, Tendsto (fun t : ℝ ↦ ∫ x in (0 : ℝ)..t, f x) atTop (𝓝 L)) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖∫ x in (0 : ℝ)..t, f x‖ ≤ C := by
  obtain ⟨L, hL⟩ := h
  -- The primitive is eventually bounded, by convergence of the improper integral.
  have hev : ∀ᶠ t : ℝ in atTop, ‖∫ x in (0 : ℝ)..t, f x‖ ≤ ‖L‖ + 1 := by
    have h1 : ∀ᶠ t : ℝ in atTop, dist (∫ x in (0 : ℝ)..t, f x) L < 1 :=
      Filter.eventually_atTop.2 ((Metric.tendsto_atTop.mp hL) 1 zero_lt_one)
    filter_upwards [h1] with t ht
    calc ‖∫ x in (0 : ℝ)..t, f x‖
        = ‖((∫ x in (0 : ℝ)..t, f x) - L) + L‖ := by rw [sub_add_cancel]
      _ ≤ ‖(∫ x in (0 : ℝ)..t, f x) - L‖ + ‖L‖ := norm_add_le _ _
      _ = dist (∫ x in (0 : ℝ)..t, f x) L + ‖L‖ := by rw [dist_eq_norm]
      _ ≤ ‖L‖ + 1 := by linarith
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
  -- A uniform bound on `f` over the initial compact interval.
  obtain ⟨Cf, hCf⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
    (hcont.mono fun x hx ↦ hx.1 : ContinuousOn f (Set.Icc 0 T))
  refine ⟨max (max Cf 0 * max T 0) (‖L‖ + 1), fun t ht ↦ ?_⟩
  rcases le_total t T with htT | hTt
  · have hb : ∀ x ∈ Set.uIoc (0 : ℝ) t, ‖f x‖ ≤ max Cf 0 := by
      intro x hx
      rw [Set.uIoc_of_le ht] at hx
      exact le_trans (hCf x ⟨hx.1.le, le_trans hx.2 htT⟩) (le_max_left _ _)
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have hle : ‖∫ x in (0 : ℝ)..t, f x‖ ≤ max Cf 0 * t := by
      simpa [sub_zero, abs_of_nonneg ht] using hnorm
    calc ‖∫ x in (0 : ℝ)..t, f x‖ ≤ max Cf 0 * t := hle
      _ ≤ max Cf 0 * max T 0 := by
          exact mul_le_mul_of_nonneg_left (le_trans htT (le_max_left T 0)) (le_max_right Cf 0)
      _ ≤ max (max Cf 0 * max T 0) (‖L‖ + 1) := le_max_left _ _
  · exact le_trans (hT t hTt) (le_max_right _ _)

/-- The tail supremum `S(t) = ⨆ u ≥ t, ‖∫ x in t..u, f x‖` is finite (a genuine real number)
when the improper integral of `f` converges: away from the initial compact interval the tail
integral is a difference of two bounded primitives, and near it the integral is bounded by a
uniform bound on `f`. -/
theorem bddAbove_range_tailSup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hcont : ContinuousOn f (Set.Ici 0))
    (h : ∃ L, Tendsto (fun t : ℝ ↦ ∫ x in (0 : ℝ)..t, f x) atTop (𝓝 L))
    {t : ℝ} (ht : 0 ≤ t) :
    BddAbove (Set.range fun u : {u : ℝ // t ≤ u} ↦ ‖∫ x in t..u, f x‖) := by
  obtain ⟨C, hC⟩ := exists_bound_primitive hcont h
  refine ⟨2 * C, ?_⟩
  rintro _ ⟨⟨u, htu⟩, rfl⟩
  have hInt0t : IntervalIntegrable f volume (0 : ℝ) t :=
    ContinuousOn.intervalIntegrable_of_Icc ht (hcont.mono fun x hx ↦ hx.1)
  have hInttu : IntervalIntegrable f volume t u :=
    ContinuousOn.intervalIntegrable_of_Icc htu (hcont.mono fun x hx ↦ le_trans ht hx.1)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hInt0t hInttu
  have hsplit : (∫ x in t..u, f x) = (∫ x in (0 : ℝ)..u, f x) - ∫ x in (0 : ℝ)..t, f x := by
    rw [← hadd]
    abel
  change ‖∫ x in t..u, f x‖ ≤ 2 * C
  rw [hsplit]
  calc ‖(∫ x in (0 : ℝ)..u, f x) - ∫ x in (0 : ℝ)..t, f x‖
      ≤ ‖∫ x in (0 : ℝ)..u, f x‖ + ‖∫ x in (0 : ℝ)..t, f x‖ := norm_sub_le _ _
    _ ≤ C + C := add_le_add (hC u (le_trans ht htu)) (hC t ht)
    _ = 2 * C := by ring

/-- The quantitative scale `S(t) = ⨆ u ≥ t, ‖∫ x in t..u, f x‖` tends to `0` as `t → ∞`
whenever the improper integral of `f` converges (Farkas–Wegner, proof of Theorem 1: the Cauchy
property of the convergent improper integral makes the tail integrals uniformly small). -/
theorem tendsto_tailSup_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hcont : ContinuousOn f (Set.Ici 0))
    (h : ∃ L, Tendsto (fun t : ℝ ↦ ∫ x in (0 : ℝ)..t, f x) atTop (𝓝 L)) :
    Tendsto (tailSup f) atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := h
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp hL) (ε / 4) (by linarith)
  refine ⟨max T₀ 0, fun t ht ↦ ?_⟩
  have ht0 : 0 ≤ t := le_trans (le_max_right T₀ 0) ht
  have hT0 : T₀ ≤ t := le_trans (le_max_left T₀ 0) ht
  have hnonneg : 0 ≤ tailSup f t := by
    calc (0 : ℝ) = ‖∫ x in t..t, f x‖ := by simp
      _ ≤ tailSup f t := by
          simpa only [tailSup] using le_ciSup (bddAbove_range_tailSup hcont ⟨L, hL⟩ ht0)
            ⟨t, le_rfl⟩
  have hcauchy : ∀ u : {u : ℝ // t ≤ u}, ‖∫ x in t..u, f x‖ ≤ ε / 2 := by
    rintro ⟨u, htu⟩
    have hInt0t : IntervalIntegrable f volume (0 : ℝ) t :=
      ContinuousOn.intervalIntegrable_of_Icc ht0 (hcont.mono fun x hx ↦ hx.1)
    have hInttu : IntervalIntegrable f volume t u :=
      ContinuousOn.intervalIntegrable_of_Icc htu (hcont.mono fun x hx ↦ le_trans ht0 hx.1)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hInt0t hInttu
    have hsplit : (∫ x in t..u, f x) = (∫ x in (0 : ℝ)..u, f x) - ∫ x in (0 : ℝ)..t, f x := by
      rw [← hadd]
      abel
    have huT : T₀ ≤ u := le_trans hT0 htu
    have hdist : dist (∫ x in (0 : ℝ)..u, f x) (∫ x in (0 : ℝ)..t, f x) < ε / 2 := by
      calc dist (∫ x in (0 : ℝ)..u, f x) (∫ x in (0 : ℝ)..t, f x)
          ≤ dist (∫ x in (0 : ℝ)..u, f x) L + dist L (∫ x in (0 : ℝ)..t, f x) :=
              dist_triangle _ _ _
        _ < ε / 4 + ε / 4 := add_lt_add (hT₀ u huT) (by rw [dist_comm]; exact hT₀ t hT0)
        _ = ε / 2 := by ring
    rw [hsplit, ← dist_eq_norm]
    exact le_of_lt hdist
  have hiSup : tailSup f t ≤ ε / 2 := by
    simpa only [tailSup] using ciSup_le hcauchy
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  linarith

/-- **Hölder rate of convergence** (Farkas–Wegner, Theorem 8). If `f` is continuous on `[0, ∞)`
and Hölder continuous of order `α > 0` with constant `c ≥ 0`, then the quantitative bound of
`norm_le_sqrt_tail_add_modulus` improves to `‖f t‖ ≤ (1 + c) S(t)^(α/(1+α))`, where
`S(t) = tailSup f t`. -/
theorem norm_le_rpow_tailSup_of_holder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {c α : ℝ} (hc : 0 ≤ c) (hα : 0 < α)
    (hcont : ContinuousOn f (Set.Ici 0))
    (hholder : ∀ x y, dist (f x) (f y) ≤ c * dist x y ^ α)
    {t : ℝ} (ht : 0 ≤ t)
    (hS : BddAbove (Set.range fun u : {u : ℝ // t ≤ u} ↦ ‖∫ x in t..u, f x‖)) :
    ‖f t‖ ≤ (1 + c) * tailSup f t ^ (α / (1 + α)) := by
  have hSnonneg : 0 ≤ tailSup f t := by
    calc (0 : ℝ) = ‖∫ x in t..t, f x‖ := by simp
      _ ≤ tailSup f t := by
          simpa only [tailSup] using le_ciSup hS ⟨t, le_rfl⟩
  -- Hölder continuity as a modulus, made monotone on all of `ℝ`.
  let ω : ℝ → ℝ := fun τ ↦ c * (max τ 0) ^ α
  have hmod : ∀ x y, dist (f x) (f y) ≤ ω (dist x y) := by
    intro x y
    have hd : 0 ≤ dist x y := dist_nonneg
    calc dist (f x) (f y) ≤ c * dist x y ^ α := hholder x y
      _ = c * (max (dist x y) 0) ^ α := by rw [max_eq_left hd]
      _ = ω (dist x y) := rfl
  have hmono : Monotone ω := by
    intro a b hab
    have hmax : max a 0 ≤ max b 0 := max_le_max hab le_rfl
    have h0 : 0 ≤ max a 0 := le_max_right a 0
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 hmax hα.le) hc
  have hkey : ∀ s : ℝ, 0 < s → ‖f t‖ ≤ tailSup f t / s + c * s ^ α := by
    intro s hs
    have h := mul_norm_le_tailSup_add_mul_modulus hcont hmod hmono ht hS hs
    have hωs : ω s = c * s ^ α := by
      simp only [ω, max_eq_left hs.le]
    rw [hωs] at h
    have hmul : s * (tailSup f t / s + c * s ^ α) = tailSup f t + c * s ^ α * s := by
      rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hs)]
      ring
    exact le_of_mul_le_mul_left (by rw [hmul]; exact h) hs
  have hα1pos : 0 < 1 + α := by linarith
  have hpα : (1 / (1 + α)) * α = α / (1 + α) := by
    field_simp
  rcases lt_or_eq_of_le hSnonneg with hSpos | hSzero
  · have hs : 0 < tailSup f t ^ (1 / (1 + α)) := Real.rpow_pos_of_pos hSpos _
    have h := hkey (tailSup f t ^ (1 / (1 + α))) hs
    have hdiv : tailSup f t / tailSup f t ^ (1 / (1 + α)) = tailSup f t ^ (α / (1 + α)) := by
      rw [div_eq_iff (ne_of_gt hs), ← Real.rpow_add hSpos]
      rw [show α / (1 + α) + 1 / (1 + α) = 1 by field_simp; ring, Real.rpow_one]
    have hpow : (tailSup f t ^ (1 / (1 + α))) ^ α = tailSup f t ^ (α / (1 + α)) := by
      rw [← Real.rpow_mul hSnonneg, hpα]
    rw [hdiv, hpow] at h
    calc ‖f t‖ ≤ tailSup f t ^ (α / (1 + α)) + c * tailSup f t ^ (α / (1 + α)) := h
      _ = (1 + c) * tailSup f t ^ (α / (1 + α)) := by ring
  · have hlim : Tendsto (fun s : ℝ ↦ c * s ^ α) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcont0 : Tendsto (fun x : ℝ ↦ x ^ α) (𝓝 0) (𝓝 0) := by
        have h : Tendsto (fun x : ℝ ↦ x ^ α) (𝓝 0) (𝓝 ((0 : ℝ) ^ α)) :=
          Real.continuousAt_rpow_const 0 α (Or.inr hα.le)
        rwa [Real.zero_rpow hα.ne'] at h
      have h1 : Tendsto (fun x : ℝ ↦ x ^ α) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        hcont0.mono_left nhdsWithin_le_nhds
      simpa using h1.const_mul c
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖f t‖ ≤ c * s ^ α := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have h := hkey s hs
      rwa [← hSzero, zero_div, zero_add] at h
    have hle : ‖f t‖ ≤ 0 := ge_of_tendsto hlim hev
    rw [hSzero.symm, Real.zero_rpow (ne_of_gt (div_pos hα hα1pos)), mul_zero]
    exact hle

/-- **Hölder rate of convergence**, paper form (Farkas–Wegner, Theorem 8): if `f` is continuous
on `[0, ∞)`, Hölder continuous of order `α > 0` with constant `c ≥ 0`, and its improper
integral converges, then `‖f t‖ ≤ (1 + c) S(t)^(α/(1+α))` with `S(t) = tailSup f t`. -/
theorem norm_le_rpow_tailSup_of_holder_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {c α : ℝ} (hc : 0 ≤ c) (hα : 0 < α)
    (hcont : ContinuousOn f (Set.Ici 0))
    (hholder : ∀ x y, dist (f x) (f y) ≤ c * dist x y ^ α)
    (h : ∃ L, Tendsto (fun t : ℝ ↦ ∫ x in (0 : ℝ)..t, f x) atTop (𝓝 L))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖f t‖ ≤ (1 + c) * tailSup f t ^ (α / (1 + α)) :=
  norm_le_rpow_tailSup_of_holder hc hα hcont hholder ht (bddAbove_range_tailSup hcont h ht)

end Barbalat
