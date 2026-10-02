/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.Filippov
public import DynamicalSystems.NonSmooth.ChainRule
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-! # Non-smooth finite-time Lyapunov theory

This file develops the finite-time Lyapunov comparison for absolutely continuous scalar
functions and its trajectory-level consequence for Filippov solutions of a discontinuous
vector field.

The scalar comparison is the almost-everywhere form of the sliding-mode finite-time
condition `V̇ ≤ -c V ^ α` with `α < 1` and `c > 0`: an absolutely continuous non-negative
`z` satisfying `deriv z ≤ -c * z ^ α` almost everywhere on `[0, T]` vanishes by the settling
time `z 0 ^ (1 - α) / (c * (1 - α))`. The proof integrates the derivative of
`s ↦ z s ^ (1 - α)` using the fundamental theorem of calculus for absolutely continuous
functions.

The trajectory-level theorem feeds the Clarke decay inequality
`ξ v ≤ -c V x ^ α` for every `ξ` in the Clarke generalized gradient of the Lyapunov
function `V` and every `v` in the Filippov set `F x` into the scalar comparison along the
curve `t ↦ V (γ t)`.

## Main statements

* `eq_zero_of_ae_deriv_le_neg_mul_rpow`: the scalar almost-everywhere finite-time comparison.
* `nonsmooth_lyapunov_finite_time`: finite-time convergence of a Filippov solution under a
  Clarke Lyapunov-decay inequality.

## The differentiability hypothesis

The trajectory-level theorem carries the hypothesis `hV_diff`, that `V` is differentiable at
`γ t` for almost every `t ∈ [0, T]`. This is **not** the Lusin (N) property of the absolutely
continuous curve `γ`, and it does not follow from absolute continuity: for `n ≥ 2` the image of
an absolutely continuous curve `γ : ℝ → ℝⁿ` is Lebesgue-null, and if that image lies inside the
non-differentiability set of the locally Lipschitz `V` the hypothesis fails. For instance, with
`E = ℝ²`, `V (x₁, x₂) = |x₂|` and `γ t = (t, 0)`, the function `V` is non-differentiable at
every `γ t`, while `V ∘ γ` is absolutely continuous. The hypothesis is instead forced by the
Fréchet-derivative route taken here: the reduction expresses `deriv (V ∘ γ) t` through
`fderiv ℝ V (γ t)` and then invokes `fderiv_mem_clarkeGradient`, which needs `V` differentiable
at `γ t`. Clarke's theorem avoids Fréchet derivatives and requires no such hypothesis.

Under that hypothesis the reduction is elementary: `t ↦ V (γ t)` is absolutely continuous
(`absolutelyContinuousOnInterval_comp_locallyLipschitz`), non-negative by `hV_pos`, and at
almost every `t` the ordinary chain rule gives
`deriv (V ∘ γ) t = fderiv ℝ V (γ t) (deriv γ t)`; since `fderiv ℝ V (γ t)` lies in
`clarkeGradient V (γ t)` (`fderiv_mem_clarkeGradient`) and `deriv γ t ∈ F (γ t)`
(`hsol.2`), the decay hypothesis bounds this by `-c * (V (γ t)) ^ α`, and
`eq_zero_of_ae_deriv_le_neg_mul_rpow` concludes.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

/-- **Scalar finite-time comparison, almost-everywhere form.** Let `z : ℝ → ℝ` be
absolutely continuous on `[0, T]` and non-negative there, and suppose
`deriv z t ≤ -c * z t ^ α` for almost every `t ∈ [0, T]`, with `c > 0` and `α < 1`. Then `z`
vanishes by the settling time `z 0 ^ (1 - α) / (c * (1 - α))`.

The proof sets `p = 1 - α > 0`. First `deriv z ≤ 0` a.e. makes `z` non-increasing. Fix `t`
with `z 0 ^ p / (c * p) ≤ t` and suppose `z t > 0`; then `z > 0` on `[0, t]`, so the function
`w = z ^ p` is absolutely continuous there (composition of `z` with the `C¹` map `y ↦ y ^ p`
on the positive range of `z`) and satisfies `deriv w ≤ -c * p` a.e. The fundamental theorem
of calculus then gives `z t ^ p - z 0 ^ p = ∫ deriv w ≤ -c * p * t`, so
`z t ^ p ≤ z 0 ^ p - c * p * t ≤ 0`, contradicting `z t > 0`. -/
theorem eq_zero_of_ae_deriv_le_neg_mul_rpow {z : ℝ → ℝ} {c α : ℝ} {T : ℝ}
    (hc : 0 < c) (hα1 : α < 1) (hT : 0 ≤ T) (hz_ac : AbsolutelyContinuousOnInterval z 0 T)
    (hnonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ z t)
    (hineq : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), deriv z t ≤ -c * z t ^ α) :
    ∀ t ∈ Set.Icc 0 T, z 0 ^ (1 - α) / (c * (1 - α)) ≤ t → z t = 0 := by
  have hp : 0 < 1 - α := by linarith
  have hc' : 0 < c * (1 - α) := mul_pos hc hp
  -- Rewrite the almost-everywhere inequality in unrestricted form.
  rw [ae_restrict_iff' measurableSet_Icc] at hineq
  -- `deriv z ≤ 0` almost everywhere on `[0, T]`.
  have hae0 : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), deriv z t ≤ 0 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hineq] with t ht htmem
    have hzα : 0 ≤ z t ^ α := Real.rpow_nonneg (hnonneg t htmem) α
    have h := ht htmem
    nlinarith [hc.le, hzα]
  -- `z` is non-increasing on `[0, T]`.
  have hmono : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → b ≤ T → z b ≤ z a := by
    intro a b ha hab hbT
    have hsub : Set.uIcc a b ⊆ Set.uIcc 0 T := by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le hT]
      exact Set.Icc_subset_Icc ha hbT
    have hsub' : Set.Icc a b ⊆ Set.Icc 0 T := Set.Icc_subset_Icc ha hbT
    have habac : AbsolutelyContinuousOnInterval z a b := hz_ac.mono hsub
    have hle : ∫ x in a..b, deriv z x ≤ 0 := by
      have h0int : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b := intervalIntegrable_const
      have hae : (fun x => deriv z x) ≤ᵐ[volume.restrict (Set.Icc a b)] (fun _ => (0 : ℝ)) :=
        (ae_mono (Measure.restrict_mono hsub' le_rfl)) hae0
      have h := intervalIntegral.integral_mono_ae_restrict hab
        habac.intervalIntegrable_deriv h0int hae
      simpa using h
    have hFTC := habac.integral_deriv_eq_sub
    linarith
  intro t ht htz
  by_contra hzt
  have ht0 : 0 ≤ t := ht.1
  have htt : t ≤ T := ht.2
  have hztpos : 0 < z t := lt_of_le_of_ne (hnonneg t ht) (Ne.symm hzt)
  -- `z` is strictly positive on `[0, t]`.
  have hzpos : ∀ s ∈ Set.Icc 0 t, 0 < z s := by
    intro s hs
    exact lt_of_lt_of_le hztpos (hmono hs.1 hs.2 htt)
  have hzt_ac : AbsolutelyContinuousOnInterval z 0 t := by
    refine hz_ac.mono ?_
    rw [Set.uIcc_of_le ht0, Set.uIcc_of_le hT]
    exact Set.Icc_subset_Icc le_rfl htt
  -- The `C¹` map `y ↦ y ^ (1 - α)` is Lipschitz on the range of `z` over `[0, t]`.
  obtain ⟨K, hK⟩ : ∃ K : NNReal, LipschitzOnWith K (fun y : ℝ => y ^ (1 - α))
      (Set.uIcc (z t) (z 0)) := by
    refine ContDiffOn.exists_lipschitzOnWith (n := 1) ?_ ?_ ?_ ?_
    · refine ContDiffOn.rpow_const_of_ne contDiffOn_id ?_
      intro y hy
      have hylow : z t ≤ y := by
        rw [Set.uIcc_of_le (hmono le_rfl ht0 htt)] at hy
        exact hy.1
      exact ne_of_gt (lt_of_lt_of_le hztpos hylow)
    · exact one_ne_zero
    · exact convex_uIcc _ _
    · exact isCompact_uIcc
  have hMaps : MapsTo z (Set.uIcc 0 t) (Set.uIcc (z t) (z 0)) := by
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    rw [Set.uIcc_of_le (hmono le_rfl ht0 htt)]
    exact ⟨hmono hs.1 hs.2 htt, hmono le_rfl hs.1 (le_trans hs.2 htt)⟩
  let w : ℝ → ℝ := fun s => z s ^ (1 - α)
  have hw_ac : AbsolutelyContinuousOnInterval w 0 t := by
    have := hK.comp_absolutelyContinuousOnInterval hMaps hzt_ac
    simpa only [w, Function.comp_def] using this
  -- Almost-everywhere bound on `deriv w`.
  have hboundae : ∀ᵐ s ∂volume.restrict (Set.Icc 0 t), deriv w s ≤ -c * (1 - α) := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hw_ac.ae_differentiableAt, hzt_ac.ae_differentiableAt, hineq]
      with s hws hzs hineqs
    intro hs
    have hzsd : DifferentiableAt ℝ z s := hzs (by rw [Set.uIcc_of_le ht0]; exact hs)
    have hzspos : 0 < z s := hzpos s hs
    have hdw : deriv w s = deriv z s * (1 - α) * z s ^ ((1 - α) - 1) := by
      have h := hzsd.hasDerivAt.rpow_const (p := 1 - α) (Or.inl (ne_of_gt hzspos))
      simpa only [w] using h.deriv
    rw [hdw]
    have hP : 0 ≤ z s ^ ((1 - α) - 1) := Real.rpow_nonneg hzspos.le _
    have hstep1 : deriv z s * (1 - α) ≤ (-c * z s ^ α) * (1 - α) :=
      mul_le_mul_of_nonneg_right (hineqs ⟨hs.1, le_trans hs.2 htt⟩) hp.le
    have hstep2 : deriv z s * (1 - α) * z s ^ ((1 - α) - 1)
        ≤ (-c * z s ^ α) * (1 - α) * z s ^ ((1 - α) - 1) :=
      mul_le_mul_of_nonneg_right hstep1 hP
    have haux : z s ^ α * z s ^ ((1 - α) - 1) = 1 := by
      rw [← Real.rpow_add hzspos, show α + ((1 - α) - 1) = 0 by ring, Real.rpow_zero]
    have hident : (-c * z s ^ α) * (1 - α) * z s ^ ((1 - α) - 1) = -c * (1 - α) := by
      calc (-c * z s ^ α) * (1 - α) * z s ^ ((1 - α) - 1)
          = -c * (1 - α) * (z s ^ α * z s ^ ((1 - α) - 1)) := by ring
        _ = -c * (1 - α) := by rw [haux, mul_one]
    linarith
  -- Fundamental theorem of calculus for `w`.
  have hFTC : ∫ s in 0..t, deriv w s = w t - w 0 := hw_ac.integral_deriv_eq_sub
  have hconst : IntervalIntegrable (fun _ : ℝ => -c * (1 - α)) volume 0 t :=
    intervalIntegrable_const
  have hle : ∫ s in 0..t, deriv w s ≤ ∫ s in 0..t, (-c * (1 - α)) :=
    intervalIntegral.integral_mono_ae_restrict ht0 hw_ac.intervalIntegrable_deriv hconst hboundae
  have hconstval : ∫ s in 0..t, (-c * (1 - α)) = -c * (1 - α) * t := by
    rw [intervalIntegral.integral_const]; ring
  have hstep : w t - w 0 ≤ -c * (1 - α) * t := by
    rw [← hFTC]
    exact hle.trans_eq hconstval
  have hwt : z t ^ (1 - α) ≤ z 0 ^ (1 - α) - c * (1 - α) * t := by
    have h := hstep
    rw [show w t = z t ^ (1 - α) from rfl, show w 0 = z 0 ^ (1 - α) from rfl] at h
    linarith
  have ht' : z 0 ^ (1 - α) ≤ c * (1 - α) * t := by
    rw [div_le_iff₀ hc'] at htz
    calc z 0 ^ (1 - α) ≤ t * (c * (1 - α)) := htz
      _ = c * (1 - α) * t := by ring
  have hle0 : z t ^ (1 - α) ≤ 0 := by linarith
  have hpos : 0 < z t ^ (1 - α) := Real.rpow_pos_of_pos hztpos _
  linarith

/-- **Finite-time convergence of a Filippov solution under a Clarke decay inequality.** Let
`V : E → ℝ` be a non-negative locally Lipschitz Lyapunov function and `γ` a Filippov solution of
`ẋ ∈ F x` on `[0, T]`, differentiable into `F` almost everywhere. Suppose that for every `x`,
every `v ∈ F x` and every `ξ` in the Clarke generalized gradient of `V` at `x` one has
`ξ v ≤ -c * (V x) ^ α`, with `c > 0` and `α < 1`. Assume moreover that `V` is differentiable
at `γ t` for almost every `t` (the differentiability hypothesis on the curve). Then
`V (γ t) = 0` for all `t ∈ [0, T]` past the settling time `V (γ 0) ^ (1 - α) / (c * (1 - α))`.

The proof applies the scalar comparison `eq_zero_of_ae_deriv_le_neg_mul_rpow` to the absolutely
continuous, non-negative function `t ↦ V (γ t)`. At almost every `t` the ordinary chain rule
(`hV_diff` together with the almost-everywhere differentiability in `hsol`) gives
`deriv (V ∘ γ) t = fderiv ℝ V (γ t) (deriv γ t)`; the Fréchet derivative belongs to the Clarke
gradient (`fderiv_mem_clarkeGradient`), and `deriv γ t ∈ F (γ t)` (`hsol.2`), so the decay
hypothesis bounds the derivative by `-c * (V (γ t)) ^ α`. -/
theorem nonsmooth_lyapunov_finite_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → ℝ} (hV_pos : ∀ x, 0 ≤ V x) (hV_lip : LocallyLipschitz V)
    {F : E → Set E} {γ : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hsol : IsFilippovSolutionOn γ F (Set.Icc 0 T)) {c α : ℝ} (hc : 0 < c) (hα1 : α < 1)
    (hV_diff : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), DifferentiableAt ℝ V (γ t))
    (hdecay : ∀ x, ∀ v ∈ F x, ∀ ξ ∈ clarkeGradient V x, ξ v ≤ -c * (V x) ^ α) :
    ∀ t ∈ Set.Icc 0 T, V (γ 0) ^ (1 - α) / (c * (1 - α)) ≤ t → V (γ t) = 0 := by
  have hsub : Set.uIcc (0 : ℝ) T ⊆ Set.Icc 0 T := by rw [Set.uIcc_of_le hT.le]
  have hz_ac : AbsolutelyContinuousOnInterval (V ∘ γ) 0 T :=
    absolutelyContinuousOnInterval_comp_locallyLipschitz hV_lip (hsol.1 0 T hsub)
  have hineq : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
      deriv (V ∘ γ) t ≤ -c * (V ∘ γ) t ^ α := by
    filter_upwards [hV_diff, hsol.2] with t hVt hsol_t
    have hchain : HasDerivAt (V ∘ γ) (fderiv ℝ V (γ t) (deriv γ t)) t :=
      hVt.hasFDerivAt.comp_hasDerivAt t hsol_t.1
    rw [hchain.deriv]
    exact hdecay (γ t) (deriv γ t) hsol_t.2 (fderiv ℝ V (γ t))
      (fderiv_mem_clarkeGradient hVt)
  exact eq_zero_of_ae_deriv_le_neg_mul_rpow hc hα1 hT.le hz_ac
    (fun t _ ↦ hV_pos (γ t)) hineq
