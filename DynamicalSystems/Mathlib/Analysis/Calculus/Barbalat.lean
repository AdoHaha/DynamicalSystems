/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.MetricSpace.Holder
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

* `Barbalat.tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral`:
  Barbălat's lemma for `f : ℝ → E` with `E` a Banach space.
* `Barbalat.tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral_real`:
  the scalar (`E = ℝ`) corollary.

The main theorem would upstream to the root namespace under a Mathlib-style name.

## References

* [B. Farkas and S.-A. Wegner, *Variations on Barbălat's Lemma*][Farkas-Wegner2016]

[Farkas-Wegner2016]: https://arxiv.org/abs/1411.1611
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal

namespace Barbalat

/-- **Barbălat's lemma**, vector-valued form (Farkas–Wegner, Theorem 4). If `f : ℝ → E`
is uniformly continuous on `[0, ∞)` and the improper integral `t ↦ ∫ x in 0..t, f x`
converges as `t → ∞`, then `f t → 0`.

The completeness assumption on `E` is needed and not vacuous: the Bochner integral is
only well behaved for complete codomains, so the Banach-space setting is the natural
one (the paper's Theorem 4 is likewise stated for a Banach space). -/
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
  have hInt : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable f volume 0 t := fun t ht ↦
    ContinuousOn.intervalIntegrable_of_Icc ht (hcont.mono fun _ hx ↦ hx.1)
  have hInt2 : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable f volume t (t + s) := fun t ht ↦
    ContinuousOn.intervalIntegrable_of_Icc (by linarith [hspos])
      (hcont.mono fun _ hx ↦ le_trans ht hx.1)
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

/-- **The Lyapunov/Barbălat bridge.** Let `V w : ℝ → ℝ` be such that `V` and `w` are
nonnegative on `[0, ∞)` and `V` has derivative `-w` there. If `w` is uniformly continuous on
`[0, ∞)`, then `w t → 0` as `t → ∞`.

This is the abstract form of the Lyapunov argument used in adaptive control: the primitive
`t ↦ ∫ x in 0..t, w x = V 0 - V t` is monotone and bounded above by `V 0`, hence convergent,
and Barbălat's lemma
`Barbalat.tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral` applies to the
uniformly continuous `w`. It refines the monotone-convergence statement
`exists_tendsto_of_hasDerivAt` (in `DynamicalSystems.Stability.LaSalle`), which only produces
a limit for `V` itself; here the limit of the *derivative signal* `w` is identified as `0`. -/
theorem tendsto_zero_of_hasDerivAt_neg_of_nonneg_of_uniformContinuousOn
    {V w : ℝ → ℝ} (hV : ∀ t, 0 ≤ t → 0 ≤ V t) (hw : ∀ t, 0 ≤ t → 0 ≤ w t)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt V (-(w t)) t)
    (huc : UniformContinuousOn w (Set.Ici 0)) :
    Tendsto w atTop (𝓝 0) := by
  have hcont : ContinuousOn w (Set.Ici 0) := huc.continuousOn
  -- The primitive `F t = ∫ x in 0..t, w x` of `w` is monotone on `[0, ∞)`.
  let F : ℝ → ℝ := fun t ↦ ∫ x in (0 : ℝ)..t, w x
  have hFmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → F a ≤ F b := by
    intro a b ha hab
    have hInt1 : IntervalIntegrable w volume (0 : ℝ) a :=
      ContinuousOn.intervalIntegrable_of_Icc ha (hcont.mono fun x hx ↦ hx.1)
    have hInt2 : IntervalIntegrable w volume a b :=
      ContinuousOn.intervalIntegrable_of_Icc hab (hcont.mono fun x hx ↦ le_trans ha hx.1)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2
    have hnn : 0 ≤ ∫ x in a..b, w x := by
      have hzero : (∫ x in a..b, (0 : ℝ)) = 0 := by simp
      rw [← hzero]
      exact intervalIntegral.integral_mono_on hab intervalIntegrable_const hInt2
        fun x hx ↦ hw x (le_trans ha hx.1)
    change (∫ x in (0 : ℝ)..a, w x) ≤ ∫ x in (0 : ℝ)..b, w x
    linarith
  -- The fundamental theorem of calculus identifies `F` with `V 0 - V`, so `F ≤ V 0`.
  have hFle : ∀ t : ℝ, 0 ≤ t → F t ≤ V 0 := by
    intro t ht
    have hderiv' : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt V (-(w x)) x := by
      intro x hx
      rw [Set.uIcc_of_le ht] at hx
      exact hderiv x hx.1
    have hcont' : ContinuousOn (fun x : ℝ ↦ -(w x)) (Set.Icc 0 t) :=
      (hcont.mono fun x hx ↦ hx.1).neg
    have hint : IntervalIntegrable (fun x : ℝ ↦ -(w x)) volume (0 : ℝ) t :=
      ContinuousOn.intervalIntegrable_of_Icc ht hcont'
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hint
    rw [intervalIntegral.integral_neg] at h
    change (∫ x in (0 : ℝ)..t, w x) ≤ V 0
    linarith [h, hV t ht]
  -- Clamp at `0` so that `tendsto_atTop_ciSup` applies to a globally monotone function.
  let G : ℝ → ℝ := fun t ↦ F (max t 0)
  have hGmono : Monotone G := by
    intro a b hab
    change F (max a 0) ≤ F (max b 0)
    exact hFmono (le_max_right a 0) (max_le_max hab le_rfl)
  have hGbdd : BddAbove (Set.range G) := by
    refine ⟨V 0, ?_⟩
    rintro y ⟨t, rfl⟩
    exact hFle (max t 0) (le_max_right t 0)
  have hGtend : Tendsto G atTop (𝓝 (⨆ t, G t)) := tendsto_atTop_ciSup hGmono hGbdd
  have hFeq : G =ᶠ[atTop] F := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    change F (max t 0) = F t
    rw [max_eq_left ht]
  have hconv : ∃ L, Tendsto F atTop (𝓝 L) := ⟨_, hGtend.congr' hFeq⟩
  exact tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral huc hconv

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

/-! ## Lemma 6: Hölder regularity from an `L^q` derivative -/

/-- Hölder's inequality on a compact interval, in the form needed for Lemma 6. If `g : ℝ → ℝ` is
nonnegative with finite `L^q` seminorm on `[0, ∞)` and `(∫ x in Ioi 0, g x ^ q) ^ (1 / q) ≤ C`,
then `∫ x in a..b, g x ≤ (b - a) ^ (1 / q') * C` for `1 < q` and `q' = q / (q - 1)`. -/
private lemma intervalIntegral_le_rpow_mul_of_integral_rpow_le
    {g : ℝ → ℝ} {q C : ℝ} (hq : 1 < q)
    (hg : MemLp g (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0)))
    (hgnn : ∀ x, 0 ≤ g x)
    (hC : (∫ x in Set.Ioi 0, g x ^ q) ^ (1 / q) ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ x in a..b, g x ≤ (b - a) ^ (1 / Real.conjExponent q) * C := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hconj : (Real.conjExponent q).HolderConjugate q :=
    (Real.HolderConjugate.conjExponent hq).symm
  have hsub : Set.Ioc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx ↦ lt_of_le_of_lt ha hx.1
  have hνle : volume.restrict (Set.Ioc a b) ≤ volume.restrict (Set.Ioi 0) :=
    Measure.restrict_mono hsub le_rfl
  have hgν : MemLp g (ENNReal.ofReal q) (volume.restrict (Set.Ioc a b)) :=
    hg.mono_measure hνle
  have h1ν : MemLp (fun _ : ℝ ↦ (1 : ℝ))
      (ENNReal.ofReal (Real.conjExponent q)) (volume.restrict (Set.Ioc a b)) :=
    memLp_const 1
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Eventually.of_forall fun _ ↦ zero_le_one)
    (Eventually.of_forall hgnn) h1ν hgν
  simp only [one_mul, Real.one_rpow] at hholder
  have hfirst : (∫ _x : ℝ, (1 : ℝ) ∂(volume.restrict (Set.Ioc a b))) = b - a := by
    rw [integral_const, smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith)]
  have hInt : Integrable (fun x ↦ g x ^ q) (volume.restrict (Set.Ioi 0)) :=
    (hg.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hqpos) ENNReal.ofReal_ne_top).congr
      (Eventually.of_forall fun x ↦ by
        simp only [ENNReal.toReal_ofReal hqpos.le, Real.norm_of_nonneg (hgnn x)])
  have hmono : (∫ x, g x ^ q ∂(volume.restrict (Set.Ioc a b))) ≤
      ∫ x, g x ^ q ∂(volume.restrict (Set.Ioi 0)) :=
    integral_mono_measure hνle (Eventually.of_forall fun x ↦ Real.rpow_nonneg (hgnn x) q) hInt
  have hsecond : (∫ x, g x ^ q ∂(volume.restrict (Set.Ioc a b))) ^ (1 / q) ≤ C :=
    le_trans (Real.rpow_le_rpow (integral_nonneg fun x ↦ Real.rpow_nonneg (hgnn x) q) hmono
      (by positivity)) hC
  rw [intervalIntegral.integral_of_le hab]
  calc ∫ x in Set.Ioc a b, g x
      ≤ (∫ _x : ℝ, (1 : ℝ) ∂(volume.restrict (Set.Ioc a b))) ^
          (1 / Real.conjExponent q) *
          (∫ x, g x ^ q ∂(volume.restrict (Set.Ioc a b))) ^ (1 / q) := hholder
    _ = (b - a) ^ (1 / Real.conjExponent q) *
          (∫ x, g x ^ q ∂(volume.restrict (Set.Ioc a b))) ^ (1 / q) := by rw [hfirst]
    _ ≤ (b - a) ^ (1 / Real.conjExponent q) * C := by
        exact mul_le_mul_of_nonneg_left hsecond (Real.rpow_nonneg (by linarith) _)

/-- **Lemma 6 of Farkas–Wegner** (Hölder regularity from an `L^q` derivative). Let `E` be a Banach
space, `f : ℝ → E` differentiable everywhere with derivative `f'`, and suppose that
`f' ∈ L^q(0, ∞)` for some `q ∈ (1, ∞)` with `L^q` seminorm bounded by `C`. Then `f` is Hölder
continuous on `[0, ∞)` with exponent `(q - 1) / q` and constant `C`.

Compared with the paper, this is the everywhere-differentiable special case: absolute continuity
and an a.e. derivative are replaced by the stronger hypothesis `∀ x, HasDerivAt f (f' x) x` (the
paper-faithful form is `holderOn_of_absolutelyContinuousOnInterval`). The derivative bound
`f' ∈ L^q(0, ∞)` is expressed through `MeasureTheory.MemLp` together with the norm bound
`eLpNorm f' (ofReal q) ≤ C`. The `L^p` assumption on `f` itself is needed only for the separate
boundedness half of Lemma 6, supplied by
`exists_bound_of_uniformContinuousOn_of_integrable_norm_rpow`, and not for this estimate. The proof
is exactly the paper's one-liner
`‖f y - f x‖ = ‖∫ t in x..y, f' t‖ ≤ (y - x) ^ (1/q') * ‖f'‖_q`, with Hölder's inequality for the
final step. -/
theorem holderOn_of_memLp_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {q : ℝ} (hq : 1 < q) {C : ℝ≥0}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hmem : MemLp f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0)))
    (hC : eLpNorm f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0)) ≤ (C : ENNReal)) :
    HolderOnWith C (Real.toNNReal ((q - 1) / q)) f (Set.Ici 0) := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hr : 0 ≤ (q - 1) / q := by positivity
  -- Extract the real-valued `L^q` bound from the `eLpNorm` hypothesis.
  have hreal : (∫ x in Set.Ioi 0, ‖f' x‖ ^ q) ^ (1 / q) ≤ (C : ℝ) := by
    have h := MemLp.eLpNorm_eq_integral_rpow_norm (μ := volume.restrict (Set.Ioi 0))
      (f := f') (p := ENNReal.ofReal q) (ENNReal.ofReal_ne_zero_iff.mpr hqpos)
      ENNReal.ofReal_ne_top hmem
    rw [ENNReal.toReal_ofReal hqpos.le] at h
    rw [h, ← ENNReal.ofReal_coe_nnreal (p := C)] at hC
    rw [ENNReal.ofReal_le_ofReal_iff C.coe_nonneg] at hC
    simpa only [one_div] using hC
  -- The key estimate `‖f y - f x‖ ≤ (y - x) ^ (1/q') * C` for `0 ≤ x ≤ y`.
  have hkey : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y →
      ‖f y - f x‖ ≤ (y - x) ^ ((q - 1) / q) * (C : ℝ) := by
    intro x y hx hxy
    have hmemν : MemLp f' (ENNReal.ofReal q) (volume.restrict (Set.Ioc x y)) :=
      hmem.mono_measure (Measure.restrict_mono (fun z hz ↦ lt_of_le_of_lt hx hz.1) le_rfl)
    have hint : IntervalIntegrable f' volume x y := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxy]
      exact hmemν.integrable (ENNReal.one_le_ofReal.mpr hq.le)
    have hftc : ∫ t in x..y, f' t = f y - f x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t) hint
    have hle := intervalIntegral_le_rpow_mul_of_integral_rpow_le hq hmem.norm
      (fun t ↦ norm_nonneg _) hreal hx hxy
    calc ‖f y - f x‖ = ‖∫ t in x..y, f' t‖ := by rw [hftc]
      _ ≤ ∫ t in x..y, ‖f' t‖ := intervalIntegral.norm_integral_le_integral_norm hxy
      _ ≤ (y - x) ^ (1 / Real.conjExponent q) * (C : ℝ) := hle
      _ = (y - x) ^ ((q - 1) / q) * (C : ℝ) := by rw [Real.conjExponent, one_div_div]
  intro x hx y hy
  have hd : dist (f x) (f y) ≤
      (C : ℝ) * dist x y ^ ((Real.toNNReal ((q - 1) / q)) : ℝ) := by
    rcases le_total x y with hxy | hyx
    · have hk := hkey hx hxy
      have hdf : dist (f x) (f y) = ‖f y - f x‖ := by rw [dist_eq_norm, norm_sub_rev]
      have hdist : dist x y = y - x := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
      rw [hdf, hdist, Real.coe_toNNReal _ hr]
      exact hk.trans_eq (by ring)
    · have hk := hkey hy hyx
      have hdf : dist (f x) (f y) = ‖f x - f y‖ := by rw [dist_eq_norm]
      have hdist : dist x y = x - y := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)]
      rw [hdf, hdist, Real.coe_toNNReal _ hr]
      exact hk.trans_eq (by ring)
  calc edist (f x) (f y) = ENNReal.ofReal (dist (f x) (f y)) := edist_dist _ _
    _ ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ ((Real.toNNReal ((q - 1) / q)) : ℝ)) :=
        ENNReal.ofReal_le_ofReal hd
    _ = (C : ℝ≥0∞) * edist x y ^ ((Real.toNNReal ((q - 1) / q)) : ℝ) := by
        rw [edist_dist, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity),
          ENNReal.ofReal_coe_nnreal]

/-- **Lemma 6 of Farkas–Wegner, absolutely continuous form** (paper form). Let `f : ℝ → ℝ` be
absolutely continuous on `[0, T]` for every `T ≥ 0` and let `f'` be an a.e. derivative of `f` on
`(0, ∞)`. If `f' ∈ L^q(0, ∞)` for some `q ∈ (1, ∞)` with `L^q` seminorm bounded by `C`, then `f`
is Hölder continuous on `[0, ∞)` with exponent `(q - 1) / q` and constant `C`.

This is the paper-faithful form of `holderOn_of_memLp_deriv`: the derivative is only required to
exist almost everywhere, and the fundamental theorem of calculus is supplied by
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` instead of an everywhere-differentiable
hypothesis. As in `holderOn_of_memLp_deriv`, the `L^p` assumption on `f` itself is not needed for
this estimate. The proof is the paper's one-liner
`‖f y - f x‖ = ‖∫ t in x..y, f' t‖ ≤ (y - x) ^ (1/q') * ‖f'‖_q`, with Hölder's inequality. -/
theorem holderOn_of_absolutelyContinuousOnInterval
    {f f' : ℝ → ℝ} {q : ℝ} (hq : 1 < q) {C : ℝ≥0}
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), HasDerivAt f (f' x) x)
    (hmem : MemLp f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0)))
    (hC : eLpNorm f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0)) ≤ (C : ENNReal)) :
    HolderOnWith C (Real.toNNReal ((q - 1) / q)) f (Set.Ici 0) := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hr : 0 ≤ (q - 1) / q := by positivity
  -- Extract the real-valued `L^q` bound from the `eLpNorm` hypothesis.
  have hreal : (∫ x in Set.Ioi 0, ‖f' x‖ ^ q) ^ (1 / q) ≤ (C : ℝ) := by
    have h := MemLp.eLpNorm_eq_integral_rpow_norm (μ := volume.restrict (Set.Ioi 0))
      (f := f') (p := ENNReal.ofReal q) (ENNReal.ofReal_ne_zero_iff.mpr hqpos)
      ENNReal.ofReal_ne_top hmem
    rw [ENNReal.toReal_ofReal hqpos.le] at h
    rw [h, ← ENNReal.ofReal_coe_nnreal (p := C)] at hC
    rw [ENNReal.ofReal_le_ofReal_iff C.coe_nonneg] at hC
    simpa only [one_div] using hC
  -- The key estimate `‖f y - f x‖ ≤ (y - x) ^ (1/q') * C` for `0 ≤ x ≤ y`.
  have hkey : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y →
      ‖f y - f x‖ ≤ (y - x) ^ ((q - 1) / q) * (C : ℝ) := by
    intro x y hx hxy
    have hy : 0 ≤ y := le_trans hx hxy
    -- Absolute continuity on `[x, y]`, hence the FTC for `deriv f`.
    have hacxy : AbsolutelyContinuousOnInterval f x y :=
      (hac y hy).mono fun z hz ↦ by
        rw [Set.uIcc_of_le hxy] at hz
        rw [Set.uIcc_of_le hy]
        exact ⟨le_trans hx hz.1, hz.2⟩
    have hftc : ∫ t in x..y, deriv f t = f y - f x := hacxy.integral_deriv_eq_sub
    -- On `(x, y]` the a.e. derivative `f'` agrees with `deriv f`.
    have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc x y)), f' t = deriv f t := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp hderiv] with t ht htioc
      exact (ht (lt_of_le_of_lt hx htioc.1)).deriv.symm
    have hint_eq : ∫ t in x..y, f' t = ∫ t in x..y, deriv f t := by
      rw [intervalIntegral.integral_of_le hxy, intervalIntegral.integral_of_le hxy]
      exact integral_congr_ae hae
    have hftc' : ∫ t in x..y, f' t = f y - f x := by rw [hint_eq, hftc]
    have hle := intervalIntegral_le_rpow_mul_of_integral_rpow_le hq hmem.norm
      (fun t ↦ norm_nonneg _) hreal hx hxy
    calc ‖f y - f x‖ = ‖∫ t in x..y, f' t‖ := by rw [hftc']
      _ ≤ ∫ t in x..y, ‖f' t‖ := intervalIntegral.norm_integral_le_integral_norm hxy
      _ ≤ (y - x) ^ (1 / Real.conjExponent q) * (C : ℝ) := hle
      _ = (y - x) ^ ((q - 1) / q) * (C : ℝ) := by rw [Real.conjExponent, one_div_div]
  intro x hx y hy
  have hd : dist (f x) (f y) ≤
      (C : ℝ) * dist x y ^ ((Real.toNNReal ((q - 1) / q)) : ℝ) := by
    rcases le_total x y with hxy | hyx
    · have hk := hkey hx hxy
      have hdf : dist (f x) (f y) = ‖f y - f x‖ := by rw [dist_eq_norm, norm_sub_rev]
      have hdist : dist x y = y - x := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
      rw [hdf, hdist, Real.coe_toNNReal _ hr]
      exact hk.trans_eq (by ring)
    · have hk := hkey hy hyx
      have hdf : dist (f x) (f y) = ‖f x - f y‖ := by rw [dist_eq_norm]
      have hdist : dist x y = x - y := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)]
      rw [hdf, hdist, Real.coe_toNNReal _ hr]
      exact hk.trans_eq (by ring)
  calc edist (f x) (f y) = ENNReal.ofReal (dist (f x) (f y)) := edist_dist _ _
    _ ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ ((Real.toNNReal ((q - 1) / q)) : ℝ)) :=
        ENNReal.ofReal_le_ofReal hd
    _ = (C : ℝ≥0∞) * edist x y ^ ((Real.toNNReal ((q - 1) / q)) : ℝ) := by
        rw [edist_dist, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity),
          ENNReal.ofReal_coe_nnreal]

/-- **Lemma 6 of Farkas–Wegner, endpoint `q = ∞`.** If `f : ℝ → E` is differentiable everywhere
with derivative `f'`, the derivative is in `L^∞(0, ∞)`, and `C` is an essential bound for `‖f'‖`,
then `f` is Lipschitz continuous on `[0, ∞)` with constant `C`. This is the `q = ∞` case of
`holderOn_of_memLp_deriv`, where the Hölder exponent `(q - 1) / q` tends to `1`. Again the
`L^p` assumption on `f` itself is not needed for the estimate.

The paper-faithful version, where differentiability is only assumed almost everywhere and absolute
continuity supplies the fundamental theorem of calculus, is
`lipschitzOn_of_absolutelyContinuousOnInterval`. -/
theorem lipschitzOn_of_memLp_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} (hderiv : ∀ x, HasDerivAt f (f' x) x) {C : ℝ≥0}
    (hmem : MemLp f' ∞ (volume.restrict (Set.Ioi 0)))
    (hC : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), ‖f' x‖ ≤ (C : ℝ)) :
    LipschitzOnWith C f (Set.Ici 0) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have key : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      dist (f a) (f b) ≤ (C : ℝ) * dist a b := by
    intro a b ha hab
    have hνle : volume.restrict (Set.Ioc a b) ≤ volume.restrict (Set.Ioi 0) :=
      Measure.restrict_mono (fun z hz ↦ lt_of_le_of_lt ha hz.1) le_rfl
    have hasm : AEStronglyMeasurable f' (volume.restrict (Set.Ioc a b)) :=
      hmem.aestronglyMeasurable.mono_measure hνle
    have hCae : ∀ᵐ z ∂(volume.restrict (Set.Ioc a b)), ‖f' z‖ ≤ (C : ℝ) :=
      hC.filter_mono (ae_mono hνle)
    have hint : IntervalIntegrable f' volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      exact IntegrableOn.of_bound (by simp) hasm C hCae
    have hftc : ∫ t in a..b, f' t = f b - f a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t) hint
    have hCae' : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ‖f' t‖ ≤ (C : ℝ) := by
      rw [Set.uIoc_of_le hab]
      exact (ae_restrict_iff' measurableSet_Ioc).mp hCae
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const_ae hCae'
    have hdf : dist (f a) (f b) = ‖f b - f a‖ := by rw [dist_eq_norm, norm_sub_rev]
    have hdist : dist a b = b - a := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    rw [hdf, hdist, ← hftc]
    simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using hbound
  rcases le_total x y with hxy | hyx
  · exact key hx hxy
  · rw [dist_comm (f x) (f y), dist_comm x y]
    exact key hy hyx

/-- **Lemma 6 of Farkas–Wegner, endpoint `q = ∞`, paper-faithful form.** Let `f : ℝ → ℝ` be
absolutely continuous on `[0, T]` for every `T ≥ 0` and let `f'` be an a.e. derivative of `f` on
`(0, ∞)`. If `C` is an essential bound for `‖f'‖`, then `f` is Lipschitz continuous on `[0, ∞)`
with constant `C`.

This is the paper-faithful form of `lipschitzOn_of_memLp_deriv`: the derivative is only required to
exist almost everywhere, and the fundamental theorem of calculus is supplied by
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` instead of an everywhere-differentiable
hypothesis. The estimate uses only the a.e. bound on `f'`, so no `L^∞` membership hypothesis is
needed. -/
theorem lipschitzOn_of_absolutelyContinuousOnInterval
    {f f' : ℝ → ℝ} {C : ℝ≥0}
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), HasDerivAt f (f' x) x)
    (hC : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), ‖f' x‖ ≤ (C : ℝ)) :
    LipschitzOnWith C f (Set.Ici 0) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have key : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      dist (f a) (f b) ≤ (C : ℝ) * dist a b := by
    intro a b ha hab
    have hb : 0 ≤ b := le_trans ha hab
    -- Absolute continuity on `[a, b]`, hence the FTC for `deriv f`.
    have hacab : AbsolutelyContinuousOnInterval f a b :=
      (hac b hb).mono fun z hz ↦ by
        rw [Set.uIcc_of_le hab] at hz
        rw [Set.uIcc_of_le hb]
        exact ⟨le_trans ha hz.1, hz.2⟩
    have hftc : ∫ t in a..b, deriv f t = f b - f a := hacab.integral_deriv_eq_sub
    -- On `(a, b]` the a.e. derivative `f'` agrees with `deriv f`.
    have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), f' t = deriv f t := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp hderiv] with t ht htioc
      exact (ht (lt_of_le_of_lt ha htioc.1)).deriv.symm
    have hint_eq : ∫ t in a..b, f' t = ∫ t in a..b, deriv f t := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      exact integral_congr_ae hae
    have hftc' : ∫ t in a..b, f' t = f b - f a := by rw [hint_eq, hftc]
    -- The a.e. bound on `f'` restricted to `(a, b]`.
    have hνle : volume.restrict (Set.Ioc a b) ≤ volume.restrict (Set.Ioi 0) :=
      Measure.restrict_mono (fun z hz ↦ lt_of_le_of_lt ha hz.1) le_rfl
    have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ‖f' t‖ ≤ (C : ℝ) := by
      rw [Set.uIoc_of_le hab]
      exact (ae_restrict_iff' measurableSet_Ioc).mp (hC.filter_mono (ae_mono hνle))
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const_ae hbound
    have hdf : dist (f a) (f b) = ‖f b - f a‖ := by rw [dist_eq_norm, norm_sub_rev]
    have hdist : dist a b = b - a := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    rw [hdf, hdist, ← hftc']
    simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using hnorm
  rcases le_total x y with hxy | hyx
  · exact key hx hxy
  · rw [dist_comm (f x) (f y), dist_comm x y]
    exact key hy hyx

/-! ## The mixed Sobolev space: Theorem 5

A function `f` on the half-line belongs to the mixed Sobolev space `W^{1,p,q}(0, ∞)` when
`f ∈ L^p(0, ∞)` and its derivative `f' ∈ L^q(0, ∞)`. The paper's Theorem 5 states that every such
function tends to zero at infinity. The proof has two steps: Lemma 6 (Hölder/Lipschitz regularity
of `f`, formalized in the previous section) makes `‖f‖^p` uniformly continuous, and then the main
Barbălat theorem applies to `‖f‖^p`, whose improper integral converges because `f ∈ L^p`. -/

/-- **Boundedness of a uniformly continuous `L^p` function on the half-line.** If `f : ℝ → E` is
uniformly continuous on `[0, ∞)` and `‖f‖^p` is integrable on `(0, ∞)` for some `p ≥ 1`, then `f`
is bounded on `[0, ∞)`. This supplies the boundedness part of Lemma 6 that the Hölder estimate alone
does not give: with a uniform-continuity modulus `δ` for the tolerance `1`, on `[t, t + δ]` the
norm `‖f‖` is at least `‖f t‖ - 1`, so `(‖f t‖ - 1)^p δ` is at most the integral of `‖f‖^p`. -/
theorem exists_bound_of_uniformContinuousOn_of_integrable_norm_rpow
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {p : ℝ} (hp : 1 ≤ p)
    (huc : UniformContinuousOn f (Set.Ici 0))
    (hint : Integrable (fun x ↦ ‖f x‖ ^ p) (volume.restrict (Set.Ioi 0))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ M := by
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff_le.mp huc) 1 zero_lt_one
  set I : ℝ := ∫ x in Set.Ioi 0, ‖f x‖ ^ p with hI
  have hInn : 0 ≤ I := integral_nonneg_of_ae (Eventually.of_forall fun x ↦
    Real.rpow_nonneg (norm_nonneg (f x)) p)
  refine ⟨1 + (I / δ) ^ (1 / p), ?_, fun t ht ↦ ?_⟩
  · positivity
  · by_cases hle : ‖f t‖ ≤ 1
    · have hnn : 0 ≤ (I / δ) ^ (1 / p) := Real.rpow_nonneg (div_nonneg hInn hδpos.le) _
      linarith
    · simp only [not_le] at hle
      set c : ℝ := ‖f t‖ - 1 with hc
      have hcpos : 0 < c := sub_pos.mpr hle
      have hpoint : ∀ x ∈ Set.Icc t (t + δ), c ^ p ≤ ‖f x‖ ^ p := by
        intro x hx
        have hx0 : 0 ≤ x := le_trans ht hx.1
        have hxt : dist x t ≤ δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
          linarith [hx.2]
        have hfx : dist (f x) (f t) ≤ 1 := hδ x hx0 t ht hxt
        have hcx : c ≤ ‖f x‖ := by
          have h1 : ‖f t‖ ≤ ‖f x‖ + ‖f t - f x‖ := by
            calc ‖f t‖ = ‖(f t - f x) + f x‖ := by rw [sub_add_cancel]
              _ ≤ ‖f t - f x‖ + ‖f x‖ := norm_add_le _ _
              _ = ‖f x‖ + ‖f t - f x‖ := by ring
          have h2 : ‖f t - f x‖ ≤ 1 := by
            rw [dist_eq_norm, norm_sub_rev] at hfx
            exact hfx
          rw [hc]
          linarith
        exact Real.rpow_le_rpow (le_of_lt hcpos) hcx (by linarith)
      have hIntv : IntervalIntegrable (fun x ↦ ‖f x‖ ^ p) volume t (t + δ) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
        exact (show IntegrableOn (fun x ↦ ‖f x‖ ^ p) (Set.Ioi 0) volume from hint).mono_set
          fun x hx ↦ lt_of_le_of_lt ht hx.1
      have hIntc : IntervalIntegrable (fun _ : ℝ ↦ c ^ p) volume t (t + δ) :=
        intervalIntegrable_const
      have hmono : (∫ x in t..(t + δ), c ^ p) ≤ ∫ x in t..(t + δ), ‖f x‖ ^ p :=
        intervalIntegral.integral_mono_on (by linarith) hIntc hIntv hpoint
      have hconst : (∫ x in t..(t + δ), c ^ p) = δ * c ^ p := by
        rw [intervalIntegral.integral_const, add_sub_cancel_left]
        simp [smul_eq_mul]
      have hupper : (∫ x in t..(t + δ), ‖f x‖ ^ p) ≤ I := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact setIntegral_mono_set
          (show IntegrableOn (fun x ↦ ‖f x‖ ^ p) (Set.Ioi 0) volume from hint)
          (Eventually.of_forall fun x ↦ Real.rpow_nonneg (norm_nonneg (f x)) p)
          (Eventually.of_forall fun x hx ↦ lt_of_le_of_lt ht hx.1)
      have hlow : δ * c ^ p ≤ I := by
        rw [← hconst]
        exact le_trans hmono hupper
      have hcp_pos : 0 < c ^ p := Real.rpow_pos_of_pos hcpos p
      have hIpos : 0 < I := lt_of_lt_of_le (mul_pos hδpos hcp_pos) hlow
      have hIδ : 0 < I / δ := div_pos hIpos hδpos
      have hcp_le : c ^ p ≤ I / δ := by
        rw [le_div_iff₀ hδpos]
        nlinarith [hlow]
      have hmain : c ≤ (I / δ) ^ (1 / p) := by
        rw [← Real.rpow_le_rpow_iff (le_of_lt hcpos)
          (le_of_lt (Real.rpow_pos_of_pos hIδ _)) (by linarith : (0 : ℝ) < p)]
        rw [← Real.rpow_mul (div_nonneg hInn hδpos.le) (1 / p) p,
          show (1 / p) * p = 1 by field_simp, Real.rpow_one]
        exact hcp_le
      rw [hc] at hmain
      linarith

/-- **Uniform continuity of `‖f‖^p` on the half-line.** If `f` is uniformly continuous and bounded
on `[0, ∞)` by `M ≥ 0` and `p ≥ 1`, then `t ↦ ‖f t‖^p` is uniformly continuous on `[0, ∞)`.
This is the paper's equation (1): the mean value theorem bounds the oscillation of `u ↦ u^p` on
`[0, M]` by `p M^{p-1} |u - v|`, while `|‖f x‖ - ‖f y‖| ≤ ‖f x - f y‖`. -/
theorem uniformContinuousOn_norm_rpow_of_bounded
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {p M : ℝ} (hp : 1 ≤ p) (hM : 0 ≤ M)
    (huc : UniformContinuousOn f (Set.Ici 0))
    (hb : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ M) :
    UniformContinuousOn (fun t : ℝ ↦ ‖f t‖ ^ p) (Set.Ici 0) := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  set L : ℝ := p * M ^ (p - 1) with hL
  have hLnn : 0 ≤ L := by
    rw [hL]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hM _)
  have hderiv : ∀ x ∈ Set.Icc 0 M, DifferentiableAt ℝ (fun y : ℝ ↦ y ^ p) x :=
    fun x _ ↦ (Real.hasDerivAt_rpow_const (Or.inr hp)).differentiableAt
  have hbound : ∀ x ∈ Set.Icc 0 M, ‖deriv (fun y : ℝ ↦ y ^ p) x‖ ≤ L := by
    intro x hx
    rw [Real.deriv_rpow_const, hL, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ p),
      abs_of_nonneg (Real.rpow_nonneg hx.1 _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.1 hx.2 (by linarith)) (by linarith)
  have hlip : ∀ u ∈ Set.Icc 0 M, ∀ v ∈ Set.Icc 0 M,
      ‖(fun z : ℝ ↦ z ^ p) v - (fun z : ℝ ↦ z ^ p) u‖ ≤ L * ‖v - u‖ :=
    fun u hu v hv ↦
      Convex.norm_image_sub_le_of_norm_deriv_le hderiv hbound (convex_Icc 0 M) hu hv
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff.mp huc) (ε / (L + 1)) (by positivity)
  refine ⟨δ, hδpos, fun x hx y hy hxy ↦ ?_⟩
  have hfx : ‖f x‖ ∈ Set.Icc 0 M := ⟨norm_nonneg _, hb x hx⟩
  have hfy : ‖f y‖ ∈ Set.Icc 0 M := ⟨norm_nonneg _, hb y hy⟩
  have hdist : dist (‖f x‖ ^ p) (‖f y‖ ^ p) ≤ L * dist (f x) (f y) := by
    have h1 : dist (‖f x‖ ^ p) (‖f y‖ ^ p) ≤ L * dist (‖f x‖) (‖f y‖) := by
      rw [dist_eq_norm, dist_eq_norm, norm_sub_rev ((fun z : ℝ ↦ z ^ p) (‖f x‖)),
        norm_sub_rev (‖f x‖) (‖f y‖)]
      exact hlip (‖f x‖) hfx (‖f y‖) hfy
    have h2 : dist (‖f x‖) (‖f y‖) ≤ dist (f x) (f y) := by
      rw [dist_eq_norm, dist_eq_norm]
      exact abs_norm_sub_norm_le (f x) (f y)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hLnn)
  have hδ' : dist (f x) (f y) < ε / (L + 1) := hδ x hx y hy hxy
  have h2 : L * (ε / (L + 1)) < ε := by
    have hlt : L / (L + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    calc L * (ε / (L + 1)) = ε * (L / (L + 1)) := by ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hlt hε
      _ = ε := mul_one ε
  exact lt_of_le_of_lt hdist (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hδ'.le hLnn) h2)

/-- **Barbălat's lemma applied to `‖f‖^p`** (the final step of Theorem 5). Suppose `f` is uniformly
continuous and bounded on `[0, ∞)`, `p ≥ 1` and `‖f‖^p` is integrable on `(0, ∞)`. Then `f → 0`
at infinity: `t ↦ ‖f t‖^p` is uniformly continuous, and its improper integral converges since it is
nonnegative and integrable, so the main Barbălat theorem gives `‖f t‖^p → 0`, hence `f t → 0`. -/
theorem tendsto_zero_of_uniformContinuousOn_of_integrable_norm_rpow
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {p M : ℝ} (hp : 1 ≤ p) (hM : 0 ≤ M)
    (huc : UniformContinuousOn f (Set.Ici 0))
    (hb : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ M)
    (hint : Integrable (fun x ↦ ‖f x‖ ^ p) (volume.restrict (Set.Ioi 0))) :
    Tendsto f atTop (𝓝 0) := by
  have hucp := uniformContinuousOn_norm_rpow_of_bounded hp hM huc hb
  have hconv : ∃ L, Tendsto (fun t : ℝ ↦ ∫ x in (0 : ℝ)..t, ‖f x‖ ^ p) atTop (𝓝 L) := by
    have hunion : (⋃ t : ℝ, Set.Ioc (0 : ℝ) t) = Set.Ioi 0 := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
      exact ⟨fun ⟨t, hx0, _⟩ ↦ hx0, fun hx ↦ ⟨x, hx, le_rfl⟩⟩
    have hmono : Monotone (fun t : ℝ ↦ Set.Ioc (0 : ℝ) t) :=
      fun a b hab x hx ↦ ⟨hx.1, le_trans hx.2 hab⟩
    have hset := tendsto_setIntegral_of_monotone (μ := volume)
      (f := fun x ↦ ‖f x‖ ^ p) (fun t ↦ measurableSet_Ioc) hmono (by rw [hunion]; exact hint)
    rw [hunion] at hset
    refine ⟨∫ x in Set.Ioi 0, ‖f x‖ ^ p, hset.congr' ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (intervalIntegral.integral_of_le ht).symm
  have hpow : Tendsto (fun t : ℝ ↦ ‖f t‖ ^ p) atTop (𝓝 0) :=
    tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral hucp hconv
  rw [Metric.tendsto_nhds] at hpow ⊢
  intro ε hε
  have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
  filter_upwards [hpow (ε ^ p) hεp] with t ht
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (f t)) p)] at ht
  rw [dist_zero_right]
  exact (Real.rpow_lt_rpow_iff (norm_nonneg (f t)) hε.le (by linarith : (0 : ℝ) < p)).mp ht

/-- **Theorem 5 of Farkas–Wegner for finite `q`.** Let `p ≥ 1` and `q > 1`, and let
`f : ℝ → E` be differentiable everywhere with derivative `f'`. If `f ∈ L^p(0, ∞)` and
`f' ∈ L^q(0, ∞)`, then `f t → 0` as `t → ∞`. The proof combines Lemma 6 (via
`holderOn_of_memLp_deriv`, giving uniform continuity) with the boundedness of an `L^p` uniformly
continuous function, and then applies the main Barbălat theorem to `‖f‖^p`. -/
theorem tendsto_zero_of_memLp_deriv_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {p q : ℝ} (hp : 1 ≤ p) (hq : 1 < q)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0))) :
    Tendsto f atTop (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hr : 0 ≤ (q - 1) / q := by positivity
  set C : ℝ≥0 := (eLpNorm f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0))).toNNReal with hC
  have hCtop : (C : ℝ≥0∞) = eLpNorm f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0)) :=
    ENNReal.coe_toNNReal (hf'.eLpNorm_lt_top).ne
  have hholder : HolderOnWith C (Real.toNNReal ((q - 1) / q)) f (Set.Ici 0) :=
    holderOn_of_memLp_deriv hq hderiv hf' (le_of_eq hCtop.symm)
  have hαpos : 0 < (Real.toNNReal ((q - 1) / q) : ℝ) := by
    rw [Real.coe_toNNReal _ hr]
    positivity
  have huc : UniformContinuousOn f (Set.Ici 0) := hholder.uniformContinuousOn hαpos
  have hint : Integrable (fun x ↦ ‖f x‖ ^ p) (volume.restrict (Set.Ioi 0)) := by
    have h := hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal hp0.le] using h
  obtain ⟨M, hM, hb⟩ :=
    exists_bound_of_uniformContinuousOn_of_integrable_norm_rpow hp huc hint
  exact tendsto_zero_of_uniformContinuousOn_of_integrable_norm_rpow hp hM huc hb hint

/-- **Theorem 5 of Farkas–Wegner, endpoint `q = ∞`** (Tao's hypothesis with a general `p`). Let
`p ≥ 1`, and let `f : ℝ → E` be differentiable everywhere with derivative `f'`. If
`f ∈ L^p(0, ∞)` and `f' ∈ L^∞(0, ∞)`, then `f t → 0` as `t → ∞`. Here the derivative bound makes
`f` Lipschitz (the `q = ∞` endpoint of Lemma 6), and the rest of the argument is unchanged. -/
theorem tendsto_zero_of_memLp_deriv_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {p : ℝ} (hp : 1 ≤ p)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' ∞ (volume.restrict (Set.Ioi 0))) :
    Tendsto f atTop (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
    (by simpa only [eLpNorm_exponent_top hf'.aestronglyMeasurable] using hf'.eLpNorm_lt_top)
  have hC' : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), ‖f' x‖ ≤ (C : ℝ) :=
    (Filter.eventually_map.mp hC).mono fun x hx ↦ by exact_mod_cast hx
  have huc : UniformContinuousOn f (Set.Ici 0) :=
    (lipschitzOn_of_memLp_deriv hderiv hf' hC').uniformContinuousOn
  have hint : Integrable (fun x ↦ ‖f x‖ ^ p) (volume.restrict (Set.Ioi 0)) := by
    have h := hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal hp0.le] using h
  obtain ⟨M, hM, hb⟩ :=
    exists_bound_of_uniformContinuousOn_of_integrable_norm_rpow hp huc hint
  exact tendsto_zero_of_uniformContinuousOn_of_integrable_norm_rpow hp hM huc hb hint

/-- **Theorem 5 of Farkas–Wegner, everywhere-differentiable special case.** Let `p ∈ [1, ∞)` and
`q ∈ (1, ∞]`. If `f : ℝ → E` is differentiable everywhere with derivative `f'`, with `f ∈ L^p(0, ∞)`
and `f' ∈ L^q(0, ∞)`, then `f t → 0` at infinity. This is the everywhere-differentiable special
case of the paper's mixed Sobolev space `W^{1,p,q}(0, ∞)`; the paper-faithful statement, which
assumes only an a.e. derivative together with absolute continuity instead of
`∀ x, HasDerivAt f (f' x) x`, is `tendsto_zero_of_absolutelyContinuous_memLp`. The finite and
infinite exponents are dispatched to `tendsto_zero_of_memLp_deriv_finite` and
`tendsto_zero_of_memLp_deriv_top`. -/
theorem tendsto_zero_of_memLp_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {p : ℝ} {q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 < q)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' q (volume.restrict (Set.Ioi 0))) :
    Tendsto f atTop (𝓝 0) := by
  rcases eq_or_ne q ∞ with rfl | hqtop
  · exact tendsto_zero_of_memLp_deriv_top hp hderiv hf hf'
  · have hqreal : 1 < q.toReal := by
      simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqtop).mpr hq
    have hqeq : q = ENNReal.ofReal q.toReal := (ENNReal.ofReal_toReal hqtop).symm
    rw [hqeq] at hf'
    exact tendsto_zero_of_memLp_deriv_finite hp hqreal hderiv hf hf'

/-- **Theorem 5 of Farkas–Wegner, absolutely continuous form, finite `q`.** Let `p ≥ 1` and `q > 1`,
let `f : ℝ → ℝ` be absolutely continuous on `[0, T]` for every `T ≥ 0` with an a.e. derivative `f'`
on `(0, ∞)`. If `f ∈ L^p(0, ∞)` and `f' ∈ L^q(0, ∞)`, then `f t → 0` as `t → ∞`. This uses the
paper-faithful Hölder estimate `holderOn_of_absolutelyContinuousOnInterval` for uniform continuity
and `exists_bound_of_uniformContinuousOn_of_integrable_norm_rpow` for boundedness, then applies the
main Barbălat theorem to `‖f‖^p`. -/
theorem tendsto_zero_of_absolutelyContinuous_memLp_finite
    {f f' : ℝ → ℝ} {p q : ℝ} (hp : 1 ≤ p) (hq : 1 < q)
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), HasDerivAt f (f' x) x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0))) :
    Tendsto f atTop (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hr : 0 ≤ (q - 1) / q := by positivity
  set C : ℝ≥0 := (eLpNorm f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0))).toNNReal with hC
  have hCtop : (C : ℝ≥0∞) = eLpNorm f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0)) :=
    ENNReal.coe_toNNReal (hf'.eLpNorm_lt_top).ne
  have hholder : HolderOnWith C (Real.toNNReal ((q - 1) / q)) f (Set.Ici 0) :=
    holderOn_of_absolutelyContinuousOnInterval hq hac hderiv hf' (le_of_eq hCtop.symm)
  have hαpos : 0 < (Real.toNNReal ((q - 1) / q) : ℝ) := by
    rw [Real.coe_toNNReal _ hr]
    positivity
  have huc : UniformContinuousOn f (Set.Ici 0) := hholder.uniformContinuousOn hαpos
  have hint : Integrable (fun x ↦ ‖f x‖ ^ p) (volume.restrict (Set.Ioi 0)) := by
    have h := hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal hp0.le] using h
  obtain ⟨M, hM, hb⟩ :=
    exists_bound_of_uniformContinuousOn_of_integrable_norm_rpow hp huc hint
  exact tendsto_zero_of_uniformContinuousOn_of_integrable_norm_rpow hp hM huc hb hint

/-- **Theorem 5 of Farkas–Wegner, absolutely continuous form, `q = ∞`.** Let `p ≥ 1`, let
`f : ℝ → ℝ` be absolutely continuous on `[0, T]` for every `T ≥ 0` with an a.e. derivative `f'` on
`(0, ∞)`. If `f ∈ L^p(0, ∞)` and `f' ∈ L^∞(0, ∞)`, then `f t → 0` as `t → ∞`. The derivative
bound makes `f` Lipschitz via `lipschitzOn_of_absolutelyContinuousOnInterval`, and the rest of the
argument is unchanged. -/
theorem tendsto_zero_of_absolutelyContinuous_memLp_top
    {f f' : ℝ → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), HasDerivAt f (f' x) x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' ∞ (volume.restrict (Set.Ioi 0))) :
    Tendsto f atTop (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
    (by simpa only [eLpNorm_exponent_top hf'.aestronglyMeasurable] using hf'.eLpNorm_lt_top)
  have hC' : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), ‖f' x‖ ≤ (C : ℝ) :=
    (Filter.eventually_map.mp hC).mono fun x hx ↦ by exact_mod_cast hx
  have huc : UniformContinuousOn f (Set.Ici 0) :=
    (lipschitzOn_of_absolutelyContinuousOnInterval hac hderiv hC').uniformContinuousOn
  have hint : Integrable (fun x ↦ ‖f x‖ ^ p) (volume.restrict (Set.Ioi 0)) := by
    have h := hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal hp0.le] using h
  obtain ⟨M, hM, hb⟩ :=
    exists_bound_of_uniformContinuousOn_of_integrable_norm_rpow hp huc hint
  exact tendsto_zero_of_uniformContinuousOn_of_integrable_norm_rpow hp hM huc hb hint

/-- **Theorem 5 of Farkas–Wegner, paper-faithful absolutely continuous form.** Let `p ≥ 1` and
`q ∈ (1, ∞]`. Let `f : ℝ → ℝ` be absolutely continuous on `[0, T]` for every `T ≥ 0` with an a.e.
derivative `f'` on `(0, ∞)`. If `f ∈ L^p(0, ∞)` and `f' ∈ L^q(0, ∞)`, then `f t → 0` as `t → ∞`.
This is the paper's mixed Sobolev class `W^{1,p,q}(0, ∞)` with the a.e. derivative encoded by
absolute continuity, so it is the paper-faithful replacement for the everywhere-differentiable
`tendsto_zero_of_memLp_deriv`. The finite and infinite exponents are dispatched to
`tendsto_zero_of_absolutelyContinuous_memLp_finite` and
`tendsto_zero_of_absolutelyContinuous_memLp_top`. -/
theorem tendsto_zero_of_absolutelyContinuous_memLp
    {f f' : ℝ → ℝ} {p : ℝ} {q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 < q)
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), HasDerivAt f (f' x) x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' q (volume.restrict (Set.Ioi 0))) :
    Tendsto f atTop (𝓝 0) := by
  rcases eq_or_ne q ∞ with rfl | hqtop
  · exact tendsto_zero_of_absolutelyContinuous_memLp_top hp hac hderiv hf hf'
  · have hqreal : 1 < q.toReal := by
      simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqtop).mpr hq
    have hqeq : q = ENNReal.ofReal q.toReal := (ENNReal.ofReal_toReal hqtop).symm
    rw [hqeq] at hf'
    exact tendsto_zero_of_absolutelyContinuous_memLp_finite hp hqreal hac hderiv hf hf'

/-- **Tao's case**, paper-faithful absolutely continuous form (Farkas–Wegner, Section 2): if
`f ∈ L²(0, ∞)` and `f' ∈ L^∞(0, ∞)`, with `f` absolutely continuous on `[0, T]` for every `T ≥ 0`
and `f'` an a.e. derivative of `f` on `(0, ∞)`, then `f t → 0` at infinity. This is the case
`p = 2`, `q = ∞` of `tendsto_zero_of_absolutelyContinuous_memLp`; it is the paper-faithful
replacement for the everywhere-differentiable `tendsto_zero_of_memLp_two_deriv_top`. -/
theorem tendsto_zero_of_absolutelyContinuous_memLp_two_top
    {f f' : ℝ → ℝ}
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), HasDerivAt f (f' x) x)
    (hf : MemLp f 2 (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' ∞ (volume.restrict (Set.Ioi 0))) :
    Tendsto f atTop (𝓝 0) :=
  tendsto_zero_of_absolutelyContinuous_memLp (p := 2) (q := ∞) (by norm_num) (by norm_num)
    hac hderiv (by simpa using hf) hf'

/-- **The `p = q` case**, paper-faithful absolutely continuous form (Desoer–Vidyasagar, Teel). If
`p > 1` and both `f` and `f'` lie in `L^p(0, ∞)`, with `f` absolutely continuous on `[0, T]` for
every `T ≥ 0` and `f'` an a.e. derivative of `f` on `(0, ∞)`, then `f t → 0` at infinity. This is
the case `q = p` of `tendsto_zero_of_absolutelyContinuous_memLp`; it is the paper-faithful
replacement for the everywhere-differentiable `tendsto_zero_of_memLp_deriv_self`. -/
theorem tendsto_zero_of_absolutelyContinuous_memLp_self
    {f f' : ℝ → ℝ} {p : ℝ} (hp : 1 < p)
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), HasDerivAt f (f' x) x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0))) :
    Tendsto f atTop (𝓝 0) :=
  tendsto_zero_of_absolutelyContinuous_memLp (p := p) (q := ENNReal.ofReal p) hp.le
    (ENNReal.one_lt_ofReal.mpr hp) hac hderiv hf hf'

/-- **Tao's case**, everywhere-differentiable form (Farkas–Wegner, Section 2): if `f ∈ L²(0, ∞)`
and `f' ∈ L^∞(0, ∞)`, then `f t → 0` at infinity. This is the case `p = 2`, `q = ∞` of
`tendsto_zero_of_memLp_deriv`; the paper-faithful statement, which assumes absolute continuity with
an a.e. derivative instead of `∀ x, HasDerivAt f (f' x) x`, is
`tendsto_zero_of_absolutelyContinuous_memLp_two_top`. -/
theorem tendsto_zero_of_memLp_two_deriv_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : MemLp f 2 (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' ∞ (volume.restrict (Set.Ioi 0))) :
    Tendsto f atTop (𝓝 0) :=
  tendsto_zero_of_memLp_deriv (p := 2) (q := ∞) (by norm_num) (by norm_num)
    hderiv (by simpa using hf) hf'

/-- **The `p = q` case**, everywhere-differentiable form (Desoer–Vidyasagar, Teel). If `p > 1` and
both `f` and `f'` lie in `L^p(0, ∞)`, then `f t → 0` at infinity. This is
`tendsto_zero_of_memLp_deriv` with `q = p`; the paper-faithful statement, which assumes absolute
continuity with an a.e. derivative instead of `∀ x, HasDerivAt f (f' x) x`, is
`tendsto_zero_of_absolutelyContinuous_memLp_self`. -/
theorem tendsto_zero_of_memLp_deriv_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {p : ℝ} (hp : 1 < p)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0))) :
    Tendsto f atTop (𝓝 0) :=
  tendsto_zero_of_memLp_deriv (p := p) (q := ENNReal.ofReal p) hp.le
    (ENNReal.one_lt_ofReal.mpr hp) hderiv hf hf'

/-! ## Corollary 9: the quantitative rate in `W^{1,p,q}` -/

/-- The mean value estimate for `u ↦ u ^ p` on `[0, M]`: for `a, b ∈ [0, M]` and `p ≥ 1`,
`|a ^ p - b ^ p| ≤ p * M ^ (p - 1) * |a - b|`. This is the derivative bound used in the
paper's equation (1) to turn Hölder continuity of `f` into Hölder continuity of `‖f‖ ^ p`. -/
private lemma abs_rpow_sub_rpow_le_mul_abs_sub
    {p M a b : ℝ} (hp : 1 ≤ p)
    (ha : a ∈ Set.Icc 0 M) (hb : b ∈ Set.Icc 0 M) :
    |a ^ p - b ^ p| ≤ p * M ^ (p - 1) * |a - b| := by
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) M, DifferentiableAt ℝ (fun y : ℝ ↦ y ^ p) x :=
    fun x _ ↦ (Real.hasDerivAt_rpow_const (Or.inr hp)).differentiableAt
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) M,
      ‖deriv (fun y : ℝ ↦ y ^ p) x‖ ≤ p * M ^ (p - 1) := by
    intro x hx
    rw [Real.deriv_rpow_const, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ p),
      abs_of_nonneg (Real.rpow_nonneg hx.1 _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.1 hx.2 (by linarith)) (by linarith)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hderiv hbound (convex_Icc 0 M) ha hb
  have h' : |b ^ p - a ^ p| ≤ p * M ^ (p - 1) * |b - a| := by
    simpa only [Real.norm_eq_abs] using h
  calc |a ^ p - b ^ p| = |b ^ p - a ^ p| := abs_sub_comm _ _
    _ ≤ p * M ^ (p - 1) * |b - a| := h'
    _ = p * M ^ (p - 1) * |a - b| := by rw [abs_sub_comm]

/-- The improper integral `t ↦ ∫ x in 0..t, g x` of an integrable real-valued function `g`
converges: the integrals over the increasing family `Ioc 0 t` converge to the integral over
`Ioi 0`. -/
private lemma tendsto_intervalIntegral_of_integrableOn_Ioi
    {g : ℝ → ℝ} (hg : Integrable g (volume.restrict (Set.Ioi 0))) :
    ∃ L, Tendsto (fun t : ℝ ↦ ∫ x in (0 : ℝ)..t, g x) atTop (𝓝 L) := by
  have hunion : (⋃ t : ℝ, Set.Ioc (0 : ℝ) t) = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
    exact ⟨fun ⟨t, hx0, _⟩ ↦ hx0, fun hx ↦ ⟨x, hx, le_rfl⟩⟩
  have hmono : Monotone (fun t : ℝ ↦ Set.Ioc (0 : ℝ) t) :=
    fun a b hab x hx ↦ ⟨hx.1, le_trans hx.2 hab⟩
  have hset := tendsto_setIntegral_of_monotone (μ := volume) (f := g)
    (fun t ↦ measurableSet_Ioc) hmono (by rw [hunion]; exact hg)
  rw [hunion] at hset
  refine ⟨∫ x in Set.Ioi 0, g x, hset.congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (intervalIntegral.integral_of_le ht).symm

/-- Transfer a half-line Hölder bound to the quantitative decay estimate for `‖f‖^p. -/
private theorem norm_pow_le_tailIntegral_rate_of_holder
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {p q : ℝ} (hp : 1 ≤ p) (hq : 1 < q)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ s : ℝ, 0 ≤ s → ‖f s‖ ≤ M)
    {C : ℝ≥0} (hfHolder : HolderOnWith C (Real.toNNReal ((q - 1) / q)) f (Set.Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖f t‖ ^ p ≤
      (1 + p * M ^ (p - 1) * (C : ℝ)) *
        tailSup (fun x : ℝ ↦ ‖f x‖ ^ p) t ^ ((q - 1) / (2 * q - 1)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hαpos : 0 < (q - 1) / q := by positivity
  have hαnonneg : 0 ≤ (q - 1) / q := hαpos.le
  have hexp : ((q - 1) / q) / (1 + (q - 1) / q) = (q - 1) / (2 * q - 1) := by
    field_simp
    ring
  have hfHolder' : ∀ x ∈ Set.Ici (0 : ℝ), ∀ y ∈ Set.Ici (0 : ℝ),
      dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ ((q - 1) / q) := by
    intro x hx y hy
    have h := hfHolder.dist_le hx hy
    rwa [Real.coe_toNNReal _ hαnonneg] at h
  have hcontf : ContinuousOn f (Set.Ici 0) := hfHolder.continuousOn (Real.toNNReal_pos.mpr hαpos)
  -- The function `‖f‖^p` whose tail supremum is `S(t)`.
  set g : ℝ → ℝ := fun x ↦ ‖f x‖ ^ p with hg
  have hgHolder : ∀ x ∈ Set.Ici (0 : ℝ), ∀ y ∈ Set.Ici (0 : ℝ),
      dist (g x) (g y) ≤ (p * M ^ (p - 1) * (C : ℝ)) * dist x y ^ ((q - 1) / q) := by
    intro x hx y hy
    have hxM : ‖f x‖ ∈ Set.Icc (0 : ℝ) M := ⟨norm_nonneg _, hb x hx⟩
    have hyM : ‖f y‖ ∈ Set.Icc (0 : ℝ) M := ⟨norm_nonneg _, hb y hy⟩
    have hpow := abs_rpow_sub_rpow_le_mul_abs_sub hp hxM hyM
    have hdist_norm : |‖f x‖ - ‖f y‖| ≤ dist (f x) (f y) := by
      rw [dist_eq_norm]
      exact abs_norm_sub_norm_le (f x) (f y)
    have hfxy := hfHolder' x hx y hy
    have hcoef : 0 ≤ p * M ^ (p - 1) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hM _)
    calc dist (g x) (g y) = |‖f x‖ ^ p - ‖f y‖ ^ p| := by
          simp only [g, Real.dist_eq]
      _ ≤ p * M ^ (p - 1) * |‖f x‖ - ‖f y‖| := hpow
      _ ≤ p * M ^ (p - 1) * dist (f x) (f y) :=
          mul_le_mul_of_nonneg_left hdist_norm hcoef
      _ ≤ p * M ^ (p - 1) * ((C : ℝ) * dist x y ^ ((q - 1) / q)) :=
          mul_le_mul_of_nonneg_left hfxy hcoef
      _ = (p * M ^ (p - 1) * (C : ℝ)) * dist x y ^ ((q - 1) / q) := by ring
  have hcontg : ContinuousOn g (Set.Ici 0) := by
    have h2 : ContinuousOn (fun x : ℝ ↦ ‖f x‖ ^ p) (Set.Ici 0) :=
      hcontf.norm.rpow_const fun x _ ↦ Or.inr hp0.le
    simpa only [g] using h2
  -- Clamp the argument at `0` so that the global Hölder rate of Theorem 8 applies.
  let G : ℝ → ℝ := fun x ↦ g (max x 0)
  have hcontG : ContinuousOn G (Set.Ici 0) :=
    hcontg.congr fun x hx ↦ by simp only [G, max_eq_left (Set.mem_Ici.mp hx)]
  have hholderG : ∀ x y : ℝ, dist (G x) (G y)
      ≤ (p * M ^ (p - 1) * (C : ℝ)) * dist x y ^ ((q - 1) / q) := by
    intro x y
    have hx0 : max x 0 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (le_max_right x 0)
    have hy0 : max y 0 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (le_max_right y 0)
    have h1 := hgHolder (max x 0) hx0 (max y 0) hy0
    have h2 : dist (max x 0) (max y 0) ≤ dist x y := by
      rw [Real.dist_eq, Real.dist_eq]
      exact abs_max_sub_max_le_abs x y 0
    have h3 : dist (max x 0) (max y 0) ^ ((q - 1) / q) ≤ dist x y ^ ((q - 1) / q) :=
      Real.rpow_le_rpow dist_nonneg h2 hαnonneg
    have hcoef : 0 ≤ p * M ^ (p - 1) * (C : ℝ) :=
      mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hM _)) C.coe_nonneg
    calc dist (G x) (G y) = dist (g (max x 0)) (g (max y 0)) := rfl
      _ ≤ (p * M ^ (p - 1) * (C : ℝ)) * dist (max x 0) (max y 0) ^ ((q - 1) / q) := h1
      _ ≤ (p * M ^ (p - 1) * (C : ℝ)) * dist x y ^ ((q - 1) / q) :=
          mul_le_mul_of_nonneg_left h3 hcoef
  -- The tail supremum is finite because `‖f‖^p` is integrable.
  have hint : Integrable g (volume.restrict (Set.Ioi 0)) := by
    have h := hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp0.le, g] using h
  have hconv : ∃ L, Tendsto (fun s : ℝ ↦ ∫ x in (0 : ℝ)..s, g x) atTop (𝓝 L) :=
    tendsto_intervalIntegral_of_integrableOn_Ioi hint
  have hSg : BddAbove (Set.range fun u : {u : ℝ // t ≤ u} ↦ ‖∫ x in t..u, g x‖) :=
    bddAbove_range_tailSup hcontg hconv ht
  -- The clamped function has the same tail integrals and the same value at `t`.
  have hIntEq : ∀ u : {u : ℝ // t ≤ u}, (∫ x in t..u, G x) = ∫ x in t..u, g x := by
    rintro ⟨u, htu⟩
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [Set.uIcc_of_le htu] at hx
    simp only [G]
    rw [max_eq_left (le_trans ht hx.1)]
  have hSG : BddAbove (Set.range fun u : {u : ℝ // t ≤ u} ↦ ‖∫ x in t..u, G x‖) := by
    obtain ⟨b, hb'⟩ := hSg
    refine ⟨b, ?_⟩
    rintro _ ⟨u, rfl⟩
    change ‖∫ x in t..u, G x‖ ≤ b
    rw [hIntEq u]
    exact hb' ⟨u, rfl⟩
  have htail : tailSup G t = tailSup g t := by
    simp only [tailSup]
    exact iSup_congr fun u ↦ by rw [hIntEq u]
  have hmain := norm_le_rpow_tailSup_of_holder
    (show 0 ≤ p * M ^ (p - 1) * (C : ℝ) from
      mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hM _)) C.coe_nonneg)
    hαpos hcontG hholderG ht hSG
  have hGt : G t = ‖f t‖ ^ p := by
    simp only [G, g, max_eq_left ht]
  rw [hGt, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg (f t)) p), htail, hexp]
    at hmain
  exact hmain

/-- **Corollary 9 of Farkas–Wegner** (the quantitative rate in `W^{1,p,q}`). Let `p ≥ 1` and
`q > 1`, let `f : ℝ → E` be differentiable everywhere with derivative `f'`, with `f ∈ L^p(0, ∞)`
and `f' ∈ L^q(0, ∞)`, and let `M ≥ 0` bound `‖f‖` on `[0, ∞)` and `C` bound the `L^q` seminorm
of `f'`. Then for every `t ≥ 0`,
`‖f t‖^p ≤ (1 + p M^{p-1} C) S(t)^((q-1)/(2q-1))`, where `S(t) = ⨆ u ≥ t, ‖∫ x in t..u, ‖f x‖^p‖`
is the tail supremum of the primitive of `‖f‖^p`. This reuses the Hölder rate
`norm_le_rpow_tailSup_of_holder` (Theorem 8) with exponent `α = (q - 1) / q` and the Hölder
modulus `holderOn_of_memLp_deriv` (Lemma 6); note `α / (1 + α) = (q - 1) / (2q - 1)`. -/
theorem norm_pow_le_tailIntegral_rate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {p q : ℝ} (hp : 1 ≤ p) (hq : 1 < q)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0)))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ s : ℝ, 0 ≤ s → ‖f s‖ ≤ M)
    {C : ℝ≥0}
    (hC : eLpNorm f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0)) ≤ (C : ENNReal))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖f t‖ ^ p ≤
      (1 + p * M ^ (p - 1) * (C : ℝ)) *
        tailSup (fun x : ℝ ↦ ‖f x‖ ^ p) t ^ ((q - 1) / (2 * q - 1)) := by
  exact norm_pow_le_tailIntegral_rate_of_holder hp hq hf hM hb
    (holderOn_of_memLp_deriv hq hderiv hf' hC) ht

/-- **Corollary 9 of Farkas–Wegner, paper-faithful absolutely continuous form.** Let `p ≥ 1` and
`q > 1`, let `f : ℝ → ℝ` be absolutely continuous on `[0, T]` for every `T ≥ 0` with an a.e.
derivative `f'` on `(0, ∞)`. If `f ∈ L^p(0, ∞)` and `f' ∈ L^q(0, ∞)`, `M ≥ 0` bounds `‖f‖` on
`[0, ∞)`, and `C` bounds the `L^q` seminorm of `f'`, then for every `t ≥ 0`,
`‖f t‖^p ≤ (1 + p M^{p-1} C) S(t)^((q-1)/(2q-1))`, where
`S(t) = ⨆ u ≥ t, ‖∫ x in t..u, ‖f x‖^p‖` is the tail supremum of the primitive of `‖f‖^p`.

This is the paper-faithful (absolutely continuous, a.e. derivative) form of
`norm_pow_le_tailIntegral_rate`: the Hölder continuity of `f` is supplied by
`holderOn_of_absolutelyContinuousOnInterval` (Lemma 6) instead of the everywhere-differentiable
`holderOn_of_memLp_deriv`, while the mean value transfer to `‖f‖^p`, the clamping argument and
Theorem 8 are unchanged. As in the rest of this file, the statement is scalar-valued
(`f : ℝ → ℝ`) because Mathlib's Lebesgue fundamental theorem of calculus
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` is only available for scalar codomains. -/
theorem norm_pow_le_tailIntegral_rate_of_absolutelyContinuous
    {f f' : ℝ → ℝ} {p q : ℝ} (hp : 1 ≤ p) (hq : 1 < q)
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), HasDerivAt f (f' x) x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0)))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ s : ℝ, 0 ≤ s → ‖f s‖ ≤ M)
    {C : ℝ≥0}
    (hC : eLpNorm f' (ENNReal.ofReal q) (volume.restrict (Set.Ioi 0)) ≤ (C : ENNReal))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖f t‖ ^ p ≤
      (1 + p * M ^ (p - 1) * (C : ℝ)) *
        tailSup (fun x : ℝ ↦ ‖f x‖ ^ p) t ^ ((q - 1) / (2 * q - 1)) := by
  exact norm_pow_le_tailIntegral_rate_of_holder hp hq hf hM hb
    (holderOn_of_absolutelyContinuousOnInterval hq hac hderiv hf' hC) ht

/-- **Corollary 9 of Farkas–Wegner, endpoint `q = ∞`.** Let `p ≥ 1`, let `f : ℝ → E` lie in
`L^p(0, ∞)`, let `M ≥ 0` bound `‖f‖` on `[0, ∞)`, and let `C` be a Lipschitz constant for `f` on
`[0, ∞)` (equivalently `f ∈ W^{1,p,∞}(0, ∞)` with `C` an essential bound for `f'`). Then for every
`t ≥ 0`,
`‖f t‖^p ≤ (1 + p M^{p-1} C) S(t)^(1/2)`, where `S(t) = ⨆ u ≥ t, ‖∫ x in t..u, ‖f x‖^p‖` is the
tail supremum of the primitive of `‖f‖^p`.

This is the `q = ∞` endpoint of `norm_pow_le_tailIntegral_rate`: the Hölder exponent
`(q - 1) / q` tends to `1`, so the exponent `(q - 1) / (2q - 1)` tends to `1/2`. The proof reuses
the clamping device of the finite-`q` case and applies `norm_le_rpow_tailSup_of_holder`
(Theorem 8) with `α = 1`, where `α / (1 + α) = 1 / 2`. -/
theorem norm_pow_le_tailIntegral_rate_top
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {p : ℝ} (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ s : ℝ, 0 ≤ s → ‖f s‖ ≤ M)
    {C : ℝ≥0} (hL : LipschitzOnWith C f (Set.Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖f t‖ ^ p ≤
      (1 + p * M ^ (p - 1) * (C : ℝ)) *
        tailSup (fun x : ℝ ↦ ‖f x‖ ^ p) t ^ ((1 : ℝ) / 2) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hexp : (1 : ℝ) / (1 + 1) = (1 : ℝ) / 2 := by norm_num
  have hcontf : ContinuousOn f (Set.Ici 0) := hL.continuousOn
  -- The function `‖f‖^p` whose tail supremum is `S(t)`.
  set g : ℝ → ℝ := fun x ↦ ‖f x‖ ^ p with hg
  have hgLip : ∀ x ∈ Set.Ici (0 : ℝ), ∀ y ∈ Set.Ici (0 : ℝ),
      dist (g x) (g y) ≤ (p * M ^ (p - 1) * (C : ℝ)) * dist x y := by
    intro x hx y hy
    have hxM : ‖f x‖ ∈ Set.Icc (0 : ℝ) M := ⟨norm_nonneg _, hb x hx⟩
    have hyM : ‖f y‖ ∈ Set.Icc (0 : ℝ) M := ⟨norm_nonneg _, hb y hy⟩
    have hpow := abs_rpow_sub_rpow_le_mul_abs_sub hp hxM hyM
    have hdist_norm : |‖f x‖ - ‖f y‖| ≤ dist (f x) (f y) := by
      rw [dist_eq_norm]
      exact abs_norm_sub_norm_le (f x) (f y)
    have hfxy := hL.dist_le_mul x hx y hy
    have hcoef : 0 ≤ p * M ^ (p - 1) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hM _)
    calc dist (g x) (g y) = |‖f x‖ ^ p - ‖f y‖ ^ p| := by
          simp only [g, Real.dist_eq]
      _ ≤ p * M ^ (p - 1) * |‖f x‖ - ‖f y‖| := hpow
      _ ≤ p * M ^ (p - 1) * dist (f x) (f y) :=
          mul_le_mul_of_nonneg_left hdist_norm hcoef
      _ ≤ p * M ^ (p - 1) * ((C : ℝ) * dist x y) :=
          mul_le_mul_of_nonneg_left hfxy hcoef
      _ = (p * M ^ (p - 1) * (C : ℝ)) * dist x y := by ring
  have hcontg : ContinuousOn g (Set.Ici 0) := by
    have h2 : ContinuousOn (fun x : ℝ ↦ ‖f x‖ ^ p) (Set.Ici 0) :=
      hcontf.norm.rpow_const fun x _ ↦ Or.inr hp0.le
    simpa only [g] using h2
  -- Clamp the argument at `0` so that the global Hölder rate of Theorem 8 applies.
  let G : ℝ → ℝ := fun x ↦ g (max x 0)
  have hcontG : ContinuousOn G (Set.Ici 0) :=
    hcontg.congr fun x hx ↦ by simp only [G, max_eq_left (Set.mem_Ici.mp hx)]
  have hholderG : ∀ x y : ℝ, dist (G x) (G y)
      ≤ (p * M ^ (p - 1) * (C : ℝ)) * dist x y ^ (1 : ℝ) := by
    intro x y
    have hx0 : max x 0 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (le_max_right x 0)
    have hy0 : max y 0 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (le_max_right y 0)
    have h1 := hgLip (max x 0) hx0 (max y 0) hy0
    have h2 : dist (max x 0) (max y 0) ≤ dist x y := by
      rw [Real.dist_eq, Real.dist_eq]
      exact abs_max_sub_max_le_abs x y 0
    have hcoef : 0 ≤ p * M ^ (p - 1) * (C : ℝ) :=
      mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hM _)) C.coe_nonneg
    calc dist (G x) (G y) = dist (g (max x 0)) (g (max y 0)) := rfl
      _ ≤ (p * M ^ (p - 1) * (C : ℝ)) * dist (max x 0) (max y 0) := h1
      _ ≤ (p * M ^ (p - 1) * (C : ℝ)) * dist x y :=
          mul_le_mul_of_nonneg_left h2 hcoef
      _ = (p * M ^ (p - 1) * (C : ℝ)) * dist x y ^ (1 : ℝ) := by rw [Real.rpow_one]
  -- The tail supremum is finite because `‖f‖^p` is integrable.
  have hint : Integrable g (volume.restrict (Set.Ioi 0)) := by
    have h := hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp0.le, g] using h
  have hconv : ∃ L, Tendsto (fun s : ℝ ↦ ∫ x in (0 : ℝ)..s, g x) atTop (𝓝 L) :=
    tendsto_intervalIntegral_of_integrableOn_Ioi hint
  have hSg : BddAbove (Set.range fun u : {u : ℝ // t ≤ u} ↦ ‖∫ x in t..u, g x‖) :=
    bddAbove_range_tailSup hcontg hconv ht
  -- The clamped function has the same tail integrals and the same value at `t`.
  have hIntEq : ∀ u : {u : ℝ // t ≤ u}, (∫ x in t..u, G x) = ∫ x in t..u, g x := by
    rintro ⟨u, htu⟩
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [Set.uIcc_of_le htu] at hx
    simp only [G]
    rw [max_eq_left (le_trans ht hx.1)]
  have hSG : BddAbove (Set.range fun u : {u : ℝ // t ≤ u} ↦ ‖∫ x in t..u, G x‖) := by
    obtain ⟨b, hb'⟩ := hSg
    refine ⟨b, ?_⟩
    rintro _ ⟨u, rfl⟩
    change ‖∫ x in t..u, G x‖ ≤ b
    rw [hIntEq u]
    exact hb' ⟨u, rfl⟩
  have htail : tailSup G t = tailSup g t := by
    simp only [tailSup]
    exact iSup_congr fun u ↦ by rw [hIntEq u]
  have hmain := norm_le_rpow_tailSup_of_holder
    (show 0 ≤ p * M ^ (p - 1) * (C : ℝ) from
      mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hM _)) C.coe_nonneg)
    (by norm_num : (0 : ℝ) < 1) hcontG hholderG ht hSG
  have hGt : G t = ‖f t‖ ^ p := by simp only [G, g, max_eq_left ht]
  rw [hGt, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg (f t)) p), htail, hexp]
    at hmain
  exact hmain

/-- **Boundedness half of Lemma 6 of Farkas–Wegner.** Let `p ≥ 1` and `q ∈ (1, ∞]`, and let
`f : ℝ → E` be differentiable everywhere with derivative `f'`, with `f ∈ L^p(0, ∞)` and
`f' ∈ L^q(0, ∞)`. Then `f` is bounded on `[0, ∞)`.

The derivative bound makes `f` uniformly continuous on the half-line
(`lipschitzOn_of_memLp_deriv` for `q = ∞`, `holderOn_of_memLp_deriv` for finite `q`), and
`‖f‖^p ∈ L¹` together with uniform continuity gives boundedness via
`exists_bound_of_uniformContinuousOn_of_integrable_norm_rpow`. This bundles the boundedness half
of Lemma 6 that the convergence theorem `tendsto_zero_of_memLp_deriv` obtains internally. -/
theorem boundedOn_of_memLp_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {p : ℝ} {q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 < q)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' q (volume.restrict (Set.Ioi 0))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ M := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hint : Integrable (fun x ↦ ‖f x‖ ^ p) (volume.restrict (Set.Ioi 0)) := by
    have h := hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal hp0.le] using h
  have huc : UniformContinuousOn f (Set.Ici 0) := by
    rcases eq_or_ne q ∞ with rfl | hqtop
    · obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
        (by simpa only [eLpNorm_exponent_top hf'.aestronglyMeasurable] using hf'.eLpNorm_lt_top)
      have hC' : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), ‖f' x‖ ≤ (C : ℝ) :=
        (Filter.eventually_map.mp hC).mono fun x hx ↦ by exact_mod_cast hx
      exact (lipschitzOn_of_memLp_deriv hderiv hf' hC').uniformContinuousOn
    · have hqreal : 1 < q.toReal := by
        simpa only [ENNReal.toReal_one] using
          (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqtop).mpr hq
      have hqeq : q = ENNReal.ofReal q.toReal := (ENNReal.ofReal_toReal hqtop).symm
      rw [hqeq] at hf'
      set C : ℝ≥0 :=
        (eLpNorm f' (ENNReal.ofReal q.toReal) (volume.restrict (Set.Ioi 0))).toNNReal with hCdef
      have hCtop : (C : ℝ≥0∞) =
          eLpNorm f' (ENNReal.ofReal q.toReal) (volume.restrict (Set.Ioi 0)) :=
        ENNReal.coe_toNNReal (hf'.eLpNorm_lt_top).ne
      have hr : 0 ≤ (q.toReal - 1) / q.toReal := by positivity
      have hholder := holderOn_of_memLp_deriv hqreal hderiv hf' (le_of_eq hCtop.symm)
      have hαpos : 0 < (Real.toNNReal ((q.toReal - 1) / q.toReal) : ℝ) := by
        rw [Real.coe_toNNReal _ hr]
        positivity
      exact hholder.uniformContinuousOn hαpos
  exact exists_bound_of_uniformContinuousOn_of_integrable_norm_rpow hp huc hint

/-- **Boundedness half of Lemma 6 of Farkas–Wegner, paper-faithful form.** Let `p ≥ 1` and
`q ∈ (1, ∞]`, and let `f : ℝ → ℝ` be absolutely continuous on `[0, T]` for every `T ≥ 0` with an
a.e. derivative `f'` on `(0, ∞)`, with `f ∈ L^p(0, ∞)` and `f' ∈ L^q(0, ∞)`. Then `f` is bounded
on `[0, ∞)`.

This is the paper-faithful form of `boundedOn_of_memLp_deriv`: the derivative is only required to
exist almost everywhere, and absolute continuity supplies the fundamental theorem of calculus. The
derivative bound makes `f` uniformly continuous on the half-line
(`lipschitzOn_of_absolutelyContinuousOnInterval` for `q = ∞`,
`holderOn_of_absolutelyContinuousOnInterval` for finite `q`), and `‖f‖^p ∈ L¹` together with
uniform continuity gives boundedness via
`exists_bound_of_uniformContinuousOn_of_integrable_norm_rpow`. This bundles the boundedness half
of Lemma 6 for the paper's mixed Sobolev class `W^{1,p,q}(0, ∞)`, and is the AC-faithful companion
of the Hölder estimate `holderOn_of_absolutelyContinuousOnInterval`. -/
theorem boundedOn_of_absolutelyContinuous_memLp
    {f f' : ℝ → ℝ} {p : ℝ} {q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 < q)
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), HasDerivAt f (f' x) x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hf' : MemLp f' q (volume.restrict (Set.Ioi 0))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ M := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hint : Integrable (fun x ↦ ‖f x‖ ^ p) (volume.restrict (Set.Ioi 0)) := by
    have h := hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal hp0.le] using h
  have huc : UniformContinuousOn f (Set.Ici 0) := by
    rcases eq_or_ne q ∞ with rfl | hqtop
    · obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
        (by simpa only [eLpNorm_exponent_top hf'.aestronglyMeasurable] using hf'.eLpNorm_lt_top)
      have hC' : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), ‖f' x‖ ≤ (C : ℝ) :=
        (Filter.eventually_map.mp hC).mono fun x hx ↦ by exact_mod_cast hx
      exact (lipschitzOn_of_absolutelyContinuousOnInterval hac hderiv hC').uniformContinuousOn
    · have hqreal : 1 < q.toReal := by
        simpa only [ENNReal.toReal_one] using
          (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqtop).mpr hq
      have hqeq : q = ENNReal.ofReal q.toReal := (ENNReal.ofReal_toReal hqtop).symm
      rw [hqeq] at hf'
      set C : ℝ≥0 :=
        (eLpNorm f' (ENNReal.ofReal q.toReal) (volume.restrict (Set.Ioi 0))).toNNReal
      have hCtop : (C : ℝ≥0∞) =
          eLpNorm f' (ENNReal.ofReal q.toReal) (volume.restrict (Set.Ioi 0)) :=
        ENNReal.coe_toNNReal (hf'.eLpNorm_lt_top).ne
      have hr : 0 ≤ (q.toReal - 1) / q.toReal := by positivity
      have hholder : HolderOnWith C (Real.toNNReal ((q.toReal - 1) / q.toReal)) f (Set.Ici 0) :=
        holderOn_of_absolutelyContinuousOnInterval hqreal hac hderiv hf' (le_of_eq hCtop.symm)
      have hαpos : 0 < (Real.toNNReal ((q.toReal - 1) / q.toReal) : ℝ) := by
        rw [Real.coe_toNNReal _ hr]
        positivity
      exact hholder.uniformContinuousOn hαpos
  exact exists_bound_of_uniformContinuousOn_of_integrable_norm_rpow hp huc hint

end Barbalat
