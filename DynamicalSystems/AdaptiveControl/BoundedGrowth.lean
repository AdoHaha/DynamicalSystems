/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.MetricSpace.Basic

/-! # The Bounded Growth Lemma (Goodwin–Sin)

This file formalizes the *Bounded Growth Lemma* of Goodwin and Sin, in the form
used for the analysis of direct adaptive control in I. D. Landau, R. Lozano,
M'Saad and A. Karimi, *Adaptive Control: Algorithms, Analysis and Applications*,
2nd ed., Springer 2011, Lemma 11.1, Section 11.2 (equations (11.24)–(11.27)).

The scalar data are a weighted regressor norm `x` and an a priori performance
error `e`, both non-negative. The growth assumption (11.24) bounds `x` by a
constant plus the running maximum of `e`,

`x t ≤ C₁ + C₂ · max_{k ≤ t+D+1} e k`,

and the normalized error assumption (11.25) is

`(e (t+D+1))² / (1 + (x t)²) → 0`.

The conclusions are (11.26) `x` is bounded and (11.27) `e (t+D+1) → 0`.

## Main results

* `bounded_growth`: the Bounded Growth Lemma.
-/

@[expose] public section

open scoped Topology

/-- Auxiliary real inequality behind the Bounded Growth Lemma: if `y` is large
enough that `(C₁ + 1) / C₂ < y` and `X ≤ C₁ + C₂ · y`, then the normalized ratio
`y² / (1 + X²)` is bounded below by `1 / (5 C₂²)`.

Writing `u = C₂ y`, the hypotheses give `C₁ < u` and `1 ≤ u`, so that
`C₁ + C₂ y = C₁ + u ≤ 2u` and `1 + X² ≤ 1 + 4u² ≤ 5u²`. -/
private lemma bounded_growth_ratio_lower {C1 C2 X y : ℝ} (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hy : (C1 + 1) / C2 < y) (hX : X ≤ C1 + C2 * y) (hX0 : 0 ≤ X) :
    1 / (5 * C2 ^ 2) ≤ y ^ 2 / (1 + X ^ 2) := by
  have hy_gt : C1 + 1 < C2 * y := by
    have h := (div_lt_iff₀ hC2).mp hy
    linarith
  have hy0 : 0 < y := by
    have h1 : 0 < (C1 + 1) / C2 := div_pos (by linarith) hC2
    linarith
  have hC1le : C1 ≤ C2 * y := by linarith
  have hC2y1 : 1 ≤ C2 * y := by linarith
  have hXle : X ≤ 2 * (C2 * y) := by linarith
  have hXsq : X ^ 2 ≤ (2 * (C2 * y)) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hX0, abs_of_nonneg (by positivity)]
    exact hXle
  have hden : 1 + X ^ 2 ≤ 5 * (C2 * y) ^ 2 := by nlinarith
  have hden_pos : 0 < 1 + X ^ 2 := by positivity
  have hRhs_pos : 0 < 5 * C2 ^ 2 := by positivity
  rw [div_le_div_iff₀ hRhs_pos hden_pos]
  nlinarith [hden]

/-- **Lemma 11.1 (Bounded Growth).** Let `x` and `e` be non-negative sequences with
`x t ≤ C₁ + C₂ · max_{k ≤ t+D+1} e k` (equation (11.24)) and
`(e (t+D+1))² / (1 + (x t)²) → 0` (equation (11.25)). Then `x` is bounded
(equation (11.26)) and `e (t+D+1) → 0` (equation (11.27)).

The proof tracks the running maximum `M s = max_{k ≤ s} e k`. Since `M` is
non-decreasing and always attained at a *record* time `k` (`M k = e k`), the
growth bound at `t = k - (D+1)` gives

`(e k)² / (1 + (x (k-(D+1)))²) ≥ (e k)² / (1 + (C₁ + C₂ e k)²)`,

which tends to `1/C₂² > 0` as `e k → ∞` along record times. The normalized-error
limit forces every sufficiently large record value to be bounded, so `M` — and
hence `x` — is bounded; the error limit then follows by multiplying (11.25) by the
bounded factor `1 + (x t)²`. -/
theorem bounded_growth {x e : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t) (he : ∀ t, 0 ≤ e t)
    {C1 C2 : ℝ} (hC1 : 0 < C1) (hC2 : 0 < C2) (D : ℕ)
    (hbound : ∀ t, x t ≤ C1 + C2 * (Finset.range (t + D + 2)).sup' (by simp) e)
    (hlim : Filter.Tendsto (fun t ↦ (e (t + D + 1)) ^ 2 / (1 + (x t) ^ 2)) Filter.atTop (𝓝 0)) :
    (∃ M, ∀ t, x t ≤ M) ∧ Filter.Tendsto (fun t ↦ e (t + D + 1)) Filter.atTop (𝓝 0) := by
  -- Running maximum of `e`.
  let M : ℕ → ℝ := fun s ↦ (Finset.range (s + 1)).sup' (by simp) e
  have hM_ge : ∀ s, e s ≤ M s := fun s ↦
    Finset.le_sup' e (Finset.mem_range.mpr (Nat.lt_succ_self s))
  have hM_mono : Monotone M := by
    intro a b hab
    dsimp only [M]
    rw [Finset.sup'_le_iff]
    intro c hc
    exact Finset.le_sup' e (Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hc
      omega))
  -- Every finite range maximum is attained at a record time.
  have hrecord : ∀ s, ∃ k, k ≤ s ∧ M k = e k ∧ M s = e k := by
    intro s
    obtain ⟨k, hk_mem, hk_eq⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (s + 1)) (by simp) e
    have hks : k ≤ s := by
      have := Finset.mem_range.mp hk_mem
      omega
    refine ⟨k, hks, ?_, ?_⟩
    · exact le_antisymm ((hM_mono hks).trans_eq hk_eq) (hM_ge k)
    · exact hk_eq
  set ε : ℝ := 1 / (10 * C2 ^ 2) with hε_def
  have hε : 0 < ε := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop).mp hlim ε hε
  set R : ℝ := (C1 + 1) / C2 with hR_def
  set B : ℝ := max R (M (N + D)) with hB_def
  have hM_bound : ∀ s, M s ≤ B := by
    intro s
    obtain ⟨k, hks, hMk, hMs⟩ := hrecord s
    by_cases hk : k ≤ N + D
    · calc M s = e k := hMs
        _ ≤ M k := hM_ge k
        _ ≤ M (N + D) := hM_mono hk
        _ ≤ B := le_max_right _ _
    · push Not at hk
      have hk_ge : N + D + 1 ≤ k := by omega
      set t : ℕ := k - (D + 1) with ht_def
      have htD : t + D + 1 = k := by omega
      have htN : N ≤ t := by omega
      have hek_le_R : e k ≤ R := by
        by_contra hcon
        push Not at hcon
        have hratelt : (e k) ^ 2 / (1 + (x t) ^ 2) < ε := by
          have hd := hN t htN
          rw [htD, Real.dist_eq, sub_zero] at hd
          exact (abs_lt.mp hd).2
        have hsup_le : (Finset.range (t + D + 2)).sup' (by simp) e ≤ e k := by
          apply Finset.sup'_le
          intro c hc
          have hc' : c ∈ Finset.range (k + 1) := by
            rw [Finset.mem_range] at hc ⊢
            omega
          exact (Finset.le_sup' e hc').trans hMk.le
        have hx_bound : x t ≤ C1 + C2 * e k := by
          have hb := hbound t
          have := mul_le_mul_of_nonneg_left hsup_le hC2.le
          linarith
        have hlow : 1 / (5 * C2 ^ 2) ≤ (e k) ^ 2 / (1 + (x t) ^ 2) :=
          bounded_growth_ratio_lower hC1 hC2 hcon hx_bound (hx t)
        have hεlt : ε < 1 / (5 * C2 ^ 2) := by
          rw [hε_def]
          exact one_div_lt_one_div_of_lt (by positivity)
            (by nlinarith [sq_pos_of_ne_zero (ne_of_gt hC2)])
        linarith
      calc M s = e k := hMs
        _ ≤ R := hek_le_R
        _ ≤ B := le_max_left _ _
  have hM_nonneg : 0 ≤ B := by
    have h1 : 0 ≤ M (N + D) := (he (N + D)).trans (hM_ge (N + D))
    exact h1.trans (le_max_right _ _)
  have hx_bound_all : ∀ t, x t ≤ C1 + C2 * B := by
    intro t
    calc x t ≤ C1 + C2 * M (t + D + 1) := by
          have hsup_le : (Finset.range (t + D + 2)).sup' (by simp) e ≤ M (t + D + 1) := by
            dsimp only [M]
            apply Finset.sup'_le
            intro c hc
            exact Finset.le_sup' e (Finset.mem_range.mpr (by
              rw [Finset.mem_range] at hc
              omega))
          have hb := hbound t
          have := mul_le_mul_of_nonneg_left hsup_le hC2.le
          linarith
      _ ≤ C1 + C2 * B := by
          have := hM_bound (t + D + 1)
          nlinarith [hC2.le, this]
  refine ⟨⟨C1 + C2 * B, hx_bound_all⟩, ?_⟩
  set Mx : ℝ := C1 + C2 * B with hMx_def
  have hMx_pos : 0 < Mx := by
    have : 0 ≤ C2 * B := mul_nonneg hC2.le hM_nonneg
    rw [hMx_def]; linarith
  have hmul_tendsto : Filter.Tendsto
      (fun t ↦ (e (t + D + 1)) ^ 2 / (1 + (x t) ^ 2) * (1 + Mx ^ 2)) Filter.atTop (𝓝 0) := by
    simpa using hlim.mul_const (1 + Mx ^ 2)
  have hsq_tendsto : Filter.Tendsto (fun t ↦ (e (t + D + 1)) ^ 2) Filter.atTop (𝓝 0) := by
    apply squeeze_zero (fun t ↦ sq_nonneg _) (fun t ↦ ?_) hmul_tendsto
    have hxle : x t ≤ Mx := hx_bound_all t
    have hxnn : 0 ≤ x t := hx t
    have hxx : (x t) ^ 2 ≤ Mx ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hxnn, abs_of_nonneg hMx_pos.le]
      exact hxle
    have hden : 0 < 1 + (x t) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith [sq_nonneg (e (t + D + 1))]
  have hsqrt_tendsto : Filter.Tendsto (fun t ↦ Real.sqrt ((e (t + D + 1)) ^ 2))
      Filter.atTop (𝓝 0) := by
    have := hsq_tendsto.sqrt
    rwa [Real.sqrt_zero] at this
  have heq : (fun t ↦ Real.sqrt ((e (t + D + 1)) ^ 2)) = fun t ↦ e (t + D + 1) :=
    funext fun t ↦ Real.sqrt_sq (he (t + D + 1))
  rwa [heq] at hsqrt_tendsto
