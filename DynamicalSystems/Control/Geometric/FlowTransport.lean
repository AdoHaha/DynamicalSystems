/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.VariationalEquation

/-! # Local transport along a continuously differentiable flow

The spatial derivative of the flow is invertible near time zero. Differentiating
its inverse and using the variational equation proves the transported
Lie-derivative identity at every sufficiently small time, at the fixed initial
point. These results make no claim about the entire original flow box or about
uniformity in the initial point.
-/

@[expose] public section

open Set Filter
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]

/-- The spatial derivative of the local flow is a unit for sufficiently small
times, since it depends continuously on time and equals the identity at zero. -/
theorem eventually_isUnit_fderiv_localFlow
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (fderiv ℝ (localFlow hf t) x₀) := by
  have hnhds : {A : X →L[ℝ] X | IsUnit A} ∈
      𝓝 (fderiv ℝ (localFlow hf 0) x₀) := by
    rw [flow_deriv_at_zero f x₀ hf]
    exact Units.isOpen.mem_nhds (isUnit_one : IsUnit (1 : X →L[ℝ] X))
  exact (flow_deriv_firstOrder hf).continuousAt.eventually hnhds

/-- The local flow has invertible spatial derivative at its base point for all
sufficiently small times. -/
theorem eventually_isInvertible_fderiv_localFlow
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (fderiv ℝ (localFlow hf t) x₀).IsInvertible := by
  filter_upwards [eventually_isUnit_fderiv_localFlow hf] with t ht
  obtain ⟨u, hu⟩ := ht
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ X u, hu⟩

/-- The pullback of a `C¹` vector field along a `C¹` flow satisfies the
transported Lie-derivative identity at all sufficiently small times, at the
fixed initial point. The variational equation and invertibility are proved
consequences of the hypotheses. -/
theorem eventually_lieDerivative_along_flow
    {f g : X → X} {x₀ : X}
    (hf : ContDiffAt ℝ 1 f x₀) (hg : ContDiffAt ℝ 1 g x₀) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun u ↦ VectorField.pullback ℝ (localFlow hf u) g x₀)
        (VectorField.pullback ℝ (localFlow hf t) (lieBracket f g) x₀) t := by
  have htend : Tendsto (fun t ↦ localFlow hf t x₀) (𝓝 (0 : ℝ)) (𝓝 x₀) := by
    simpa only [localFlow_zero_apply f x₀ hf] using
      (localFlow_hasDerivAt_zero f x₀ hf).continuousAt.tendsto
  have htime : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun u ↦ localFlow hf u x₀) (f (localFlow hf t x₀)) t := by
    have hε := (getLocalFlowData hf).hε
    filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hε) hε] with t ht
    exact (getLocalFlowData hf).ϕ_hasDerivAt t ht x₀
      (Metric.mem_closedBall_self (getLocalFlowData hf).hr.le)
  filter_upwards [eventually_hasDerivAt_fderiv_localFlow hf,
    eventually_isUnit_fderiv_localFlow hf, htime,
    htend.eventually (hg.eventually (by simp))] with t hJ hu hΦ hg'
  obtain ⟨u, hu⟩ := hu
  have hInv : HasDerivAt
      (fun s ↦ Ring.inverse (fderiv ℝ (localFlow hf s) x₀))
      ((-ContinuousLinearMap.mulLeftRight ℝ (X →L[ℝ] X)
          (↑u⁻¹) (↑u⁻¹))
        ((fderiv ℝ f (localFlow hf t x₀)).comp
          (fderiv ℝ (localFlow hf t) x₀))) t := by
    have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hu] at h
    exact h.comp_hasDerivAt t hJ
  have hG : HasDerivAt (fun s ↦ g (localFlow hf s x₀))
      (fderiv ℝ g (localFlow hf t x₀) (f (localFlow hf t x₀))) t :=
    hg'.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t hΦ
  have hprod := hInv.clm_apply hG
  have hfun : (fun s ↦ VectorField.pullback ℝ (localFlow hf s) g x₀) =
      fun s ↦ Ring.inverse (fderiv ℝ (localFlow hf s) x₀) (g (localFlow hf s x₀)) := by
    funext s
    rw [ContinuousLinearMap.ringInverse_eq_inverse]
    rfl
  rw [hfun]
  convert hprod using 1
  rw [VectorField.pullback, lieBracket_apply, ← ContinuousLinearMap.ringInverse_eq_inverse,
    ← hu]
  simp only [neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    ← ContinuousLinearMap.mul_def, mul_assoc, Units.mul_inv, mul_one,
    Ring.inverse_unit, mul_apply_eq_comp, map_sub]
  abel
