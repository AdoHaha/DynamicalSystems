/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.Calculus.Barbalat
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Barbălat's lemma for the Hou–Duan–Guo adaptive control system

This file applies Barbălat's lemma to the adaptive control system of
[Hou-Duan-Guo, Example 3.1], which is reproduced as Example 10 in
[Farkas-Wegner2016]. The system is

```
e'(t) = -e(t) + θ(t) ω(t)
θ'(t) = -e(t) ω(t)
```

with `ω` continuous and bounded. The Lyapunov function `V = e² + θ²` satisfies
`V' = -2 e² ≤ 0` along solutions, so `V` is nonincreasing, `e` and `θ` are bounded,
and the primitive `t ↦ ∫ x in 0..t, e x ^ 2` is nondecreasing and bounded by `V 0`.
Hence `e ^ 2` has a convergent improper integral and, being Lipschitz on `[0, ∞)` because
the derivative `2 e e'` is bounded, it is uniformly continuous. Barbălat's lemma then
yields `e² → 0`, hence `e → 0`.

The ordinary differential equations are taken as hypotheses, together with the
differentiability they assert; no existence or uniqueness of trajectories is formalized.

## Main statements

* `Barbalat.adaptiveControl_error_tendsto_zero`: for any trajectory `(e, θ)` of the
  Hou–Duan–Guo system with bounded continuous `ω`, the error `e t` tends to `0` as
  `t → ∞`.

## References

* [B. Farkas and S.-A. Wegner, *Variations on Barbălat's Lemma*][Farkas-Wegner2016]
* M. Hou, G. Duan, L. Guo, *New versions of Barbălat's lemma with applications*,
  J. Control Theory Appl. (2010).

[Farkas-Wegner2016]: https://arxiv.org/abs/1411.1611
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace Barbalat

/-- **Example 10 of Farkas–Wegner** (Hou–Duan–Guo adaptive control). Let
`e θ ω : ℝ → ℝ` satisfy the adaptive control equations
`e'(t) = -e(t) + θ(t) ω(t)` and `θ'(t) = -e(t) ω(t)` for all `t ≥ 0`, with `ω`
continuous and bounded. Then the error `e t` tends to `0` as `t → ∞`.

The ODEs and the differentiability they assert are hypotheses; only the asymptotic
behaviour of the trajectory is proved. -/
theorem adaptiveControl_error_tendsto_zero
    {e theta omega : ℝ → ℝ}
    (hω : Continuous omega ∧ ∃ C : ℝ, ∀ t : ℝ, |omega t| ≤ C)
    (he : ∀ t : ℝ, 0 ≤ t → HasDerivAt e (-e t + theta t * omega t) t)
    (hθ : ∀ t : ℝ, 0 ≤ t → HasDerivAt theta (-(e t) * omega t) t) :
    Tendsto e atTop (𝓝 0) := by
  obtain ⟨Cω, hCω⟩ := hω.2
  have hCω_nonneg : 0 ≤ Cω := le_trans (abs_nonneg (omega 0)) (hCω 0)
  -- The Lyapunov function `V = e ^ 2 + theta ^ 2`.
  let V : ℝ → ℝ := fun t ↦ e t ^ 2 + theta t ^ 2
  have hVnonneg : ∀ t : ℝ, 0 ≤ V t := by
    intro t
    change 0 ≤ e t ^ 2 + theta t ^ 2
    nlinarith [sq_nonneg (e t), sq_nonneg (theta t)]
  -- `V` is differentiable on the half-line, with derivative `-2 e ^ 2`.
  have hVderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt V (-(2 * e t ^ 2)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ ↦ e s ^ 2)
        (2 * e t * (-e t + theta t * omega t)) t := by
      refine HasDerivAt.congr_deriv ((he t ht).pow 2) ?_
      ring_nf
    have h2 : HasDerivAt (fun s : ℝ ↦ theta s ^ 2)
        (2 * theta t * (-(e t) * omega t)) t := by
      refine HasDerivAt.congr_deriv ((hθ t ht).pow 2) ?_
      ring_nf
    change HasDerivAt (fun s : ℝ ↦ e s ^ 2 + theta s ^ 2) (-(2 * e t ^ 2)) t
    exact HasDerivAt.congr_deriv (HasDerivAt.add h1 h2) (by ring)
  have hcont_e : ContinuousOn e (Set.Ici 0) :=
    fun x hx ↦ (he x hx).continuousAt.continuousWithinAt
  have hcont_θ : ContinuousOn theta (Set.Ici 0) :=
    fun x hx ↦ (hθ x hx).continuousAt.continuousWithinAt
  -- **Step 1.** `V` is nonincreasing on `[0, ∞)`.
  have hVanti : AntitoneOn V (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · change ContinuousOn (fun t : ℝ ↦ e t ^ 2 + theta t ^ 2) (Set.Ici 0)
      exact (hcont_e.pow 2).add (hcont_θ.pow 2)
    · intro x hx
      rw [interior_Ici] at hx ⊢
      have hx0 : 0 ≤ x := le_of_lt hx
      change DifferentiableWithinAt ℝ (fun t : ℝ ↦ e t ^ 2 + theta t ^ 2) (Set.Ioi 0) x
      exact (((he x hx0).pow 2).add ((hθ x hx0).pow 2)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 ≤ x := le_of_lt hx
      rw [(hVderiv x hx0).deriv]
      nlinarith [sq_nonneg (e x)]
  have hVle : ∀ t : ℝ, 0 ≤ t → V t ≤ V 0 :=
    fun t ht ↦ hVanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  -- **Step 2.** Boundedness of `e` and `theta`.
  have he_sq_le : ∀ t : ℝ, 0 ≤ t → e t ^ 2 ≤ V 0 := by
    intro t ht
    have h1 : e t ^ 2 ≤ V t := by
      change e t ^ 2 ≤ e t ^ 2 + theta t ^ 2
      nlinarith [sq_nonneg (theta t)]
    exact le_trans h1 (hVle t ht)
  have hθ_sq_le : ∀ t : ℝ, 0 ≤ t → theta t ^ 2 ≤ V 0 := by
    intro t ht
    have h1 : theta t ^ 2 ≤ V t := by
      change theta t ^ 2 ≤ e t ^ 2 + theta t ^ 2
      nlinarith [sq_nonneg (e t)]
    exact le_trans h1 (hVle t ht)
  let A : ℝ := Real.sqrt (V 0)
  have hA : 0 ≤ A := Real.sqrt_nonneg (V 0)
  have he_abs_le : ∀ t : ℝ, 0 ≤ t → |e t| ≤ A := by
    intro t ht
    have h := Real.sqrt_le_sqrt (he_sq_le t ht)
    rwa [Real.sqrt_sq_eq_abs] at h
  have hθ_abs_le : ∀ t : ℝ, 0 ≤ t → |theta t| ≤ A := by
    intro t ht
    have h := Real.sqrt_le_sqrt (hθ_sq_le t ht)
    rwa [Real.sqrt_sq_eq_abs] at h
  -- **Step 3.** A uniform bound for the derivative of `e ^ 2`.
  let B : ℝ := A + A * Cω
  let M : ℝ := 2 * A * B
  have hB : 0 ≤ B := add_nonneg hA (mul_nonneg hA hCω_nonneg)
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (by norm_num) hA) hB
  have hderiv_e2 : ∀ x : ℝ, 0 ≤ x →
      deriv (fun t : ℝ ↦ e t ^ 2) x = 2 * e x * (-e x + theta x * omega x) := by
    intro x hx
    have h2 : HasDerivAt (fun t : ℝ ↦ e t ^ 2)
        (2 * e x * (-e x + theta x * omega x)) x := by
      refine HasDerivAt.congr_deriv ((he x hx).pow 2) ?_
      ring_nf
    exact h2.deriv
  have hderiv_bound : ∀ x ∈ Set.Ici (0 : ℝ),
      ‖deriv (fun t : ℝ ↦ e t ^ 2) x‖ ≤ M := by
    intro x hx
    rw [hderiv_e2 x hx, Real.norm_eq_abs]
    have he1 : |e x| ≤ A := he_abs_le x hx
    have hθ1 : |theta x| ≤ A := hθ_abs_le x hx
    have hx_ω : |omega x| ≤ Cω := hCω x
    have hinside : |(-e x + theta x * omega x)| ≤ B := by
      calc |(-e x + theta x * omega x)|
          ≤ |-e x| + |theta x * omega x| := abs_add_le _ _
        _ = |e x| + |theta x| * |omega x| := by rw [abs_neg, abs_mul]
        _ ≤ A + A * Cω := add_le_add he1 (mul_le_mul hθ1 hx_ω (abs_nonneg _) hA)
        _ = B := rfl
    calc |2 * e x * (-e x + theta x * omega x)|
        = 2 * |e x| * |(-e x + theta x * omega x)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * A * B := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left he1 (by norm_num)) hinside
            (abs_nonneg _) (mul_nonneg (by norm_num) hA)
      _ = M := rfl
  -- **Step 4.** `e ^ 2` is uniformly continuous on `[0, ∞)`.
  have huc : UniformContinuousOn (fun t : ℝ ↦ e t ^ 2) (Set.Ici 0) := by
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    refine ⟨ε / (M + 1), by positivity, ?_⟩
    intro x hx y hy hxy
    have hdist : dist (e x ^ 2) (e y ^ 2) ≤ M * dist x y := by
      have hderiv : ∀ z ∈ Set.Ici (0 : ℝ),
          DifferentiableAt ℝ (fun t : ℝ ↦ e t ^ 2) z :=
        fun z hz ↦ ((he z hz).pow 2).differentiableAt
      have hbound : ∀ z ∈ Set.Ici (0 : ℝ),
          ‖deriv (fun t : ℝ ↦ e t ^ 2) z‖ ≤ M := hderiv_bound
      have h := Convex.norm_image_sub_le_of_norm_deriv_le hderiv hbound (convex_Ici 0) hx hy
      simpa only [dist_eq_norm, norm_sub_rev] using h
    rcases eq_or_lt_of_le hM with hM0 | hMpos
    · rw [← hM0, zero_mul] at hdist
      exact lt_of_le_of_lt hdist hε
    · refine lt_of_le_of_lt hdist ?_
      calc M * dist x y < M * (ε / (M + 1)) := mul_lt_mul_of_pos_left hxy hMpos
        _ = ε * (M / (M + 1)) := by ring
        _ < ε * 1 := by
            refine mul_lt_mul_of_pos_left ?_ hε
            rw [div_lt_one (by linarith : (0 : ℝ) < M + 1)]
            linarith
        _ = ε := mul_one ε
  -- **Step 5.** The primitive of `e ^ 2` is monotone and bounded; hence it converges.
  have hcont_e2 : ContinuousOn (fun t : ℝ ↦ e t ^ 2) (Set.Ici 0) := hcont_e.pow 2
  let F : ℝ → ℝ := fun t ↦ ∫ x in (0 : ℝ)..t, e x ^ 2
  have hFmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → F a ≤ F b := by
    intro a b ha hab
    have hInt1 : IntervalIntegrable (fun x : ℝ ↦ e x ^ 2) volume (0 : ℝ) a :=
      ContinuousOn.intervalIntegrable_of_Icc ha (hcont_e2.mono fun x hx ↦ hx.1)
    have hInt2 : IntervalIntegrable (fun x : ℝ ↦ e x ^ 2) volume a b :=
      ContinuousOn.intervalIntegrable_of_Icc hab (hcont_e2.mono fun x hx ↦ le_trans ha hx.1)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2
    have hnn : 0 ≤ ∫ x in a..b, e x ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hab fun x ↦ sq_nonneg (e x)
    change (∫ x in (0 : ℝ)..a, e x ^ 2) ≤ ∫ x in (0 : ℝ)..b, e x ^ 2
    linarith
  have hFle : ∀ t : ℝ, 0 ≤ t → F t ≤ V 0 := by
    intro t ht
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt V (-(2 * e x ^ 2)) x := by
      intro x hx
      rw [Set.uIcc_of_le ht] at hx
      exact hVderiv x hx.1
    have hcont_deriv : ContinuousOn (fun x : ℝ ↦ -(2 * e x ^ 2)) (Set.Icc 0 t) :=
      (((hcont_e.pow 2).mono fun x hx ↦ hx.1).const_mul (2 : ℝ)).neg
    have hint : IntervalIntegrable (fun x : ℝ ↦ -(2 * e x ^ 2)) volume (0 : ℝ) t :=
      ContinuousOn.intervalIntegrable_of_Icc ht hcont_deriv
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at h
    have hVt0 : 0 ≤ V t := hVnonneg t
    have hVtV0 : V t ≤ V 0 := hVle t ht
    change (∫ x in (0 : ℝ)..t, e x ^ 2) ≤ V 0
    nlinarith [h, hVt0, hVtV0]
  let G : ℝ → ℝ := fun t ↦ F (max t 0)
  have hGmono : Monotone G := by
    intro a b hab
    change F (max a 0) ≤ F (max b 0)
    exact hFmono (le_max_right a 0) (max_le_max hab le_rfl)
  have hGbdd : BddAbove (Set.range G) := by
    refine ⟨V 0, ?_⟩
    rintro y ⟨t, rfl⟩
    change F (max t 0) ≤ V 0
    exact hFle (max t 0) (le_max_right t 0)
  have hGtend : Tendsto G atTop (𝓝 (⨆ t, G t)) := tendsto_atTop_ciSup hGmono hGbdd
  have hFeq : G =ᶠ[atTop] F := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    change F (max t 0) = F t
    rw [max_eq_left ht]
  have hconv : ∃ L, Tendsto (fun t : ℝ ↦ ∫ x in (0 : ℝ)..t, e x ^ 2) atTop (𝓝 L) :=
    ⟨_, hGtend.congr' hFeq⟩
  -- **Step 6.** Apply Barbălat's lemma to `e ^ 2`, then extract `e → 0`.
  have hmain : Tendsto (fun t : ℝ ↦ e t ^ 2) atTop (𝓝 0) :=
    tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral huc hconv
  have habs : Tendsto (fun t : ℝ ↦ |e t|) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun t : ℝ ↦ Real.sqrt (e t ^ 2)) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hmain
      rw [Real.sqrt_zero] at h
      exact h
    simpa only [Real.sqrt_sq_eq_abs] using hsqrt
  rw [Metric.tendsto_nhds] at habs ⊢
  intro ε hε
  filter_upwards [habs ε hε] with t ht
  simpa only [Real.dist_eq, sub_zero, abs_abs] using ht

end Barbalat
