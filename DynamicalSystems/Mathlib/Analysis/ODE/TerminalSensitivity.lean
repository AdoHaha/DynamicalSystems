/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.Asymptotics.Uniform
public import DynamicalSystems.Mathlib.Analysis.Calculus.TaylorRemainder
public import DynamicalSystems.Mathlib.Analysis.ODE.StateTransitionPiecewise
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Compact

/-!
# Terminal sensitivity of ODE trajectories

The propagated first-order terminal displacement of a trajectory subject to an
initial perturbation, derived from the actual right ODE, uniform `O(ε)`
displacement, a local jump, and continuous spatial derivatives. The hypotheses
contain no control-theoretic data.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Interval Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual terminal sensitivity from a local needle jump and the actual
post-spike ODE. No flow derivative, sensitivity conclusion, or Duhamel
cancellation is supplied as a premise. -/
theorem terminal_sensitivity_of_right_ODE
    {F : ℝ → E → E} {D : ℝ → E → E →L[ℝ] E}
    {x : ℝ → E} {y : ℝ → ℝ → E} {τ T C : ℝ} {g : E}
    {Phi : ℝ → ℝ → E →L[ℝ] E}
    (hτT : τ ≤ T) (hC : 0 ≤ C)
    (hdiag : Phi T T = ContinuousLinearMap.id ℝ E)
    (hback : ∀ s ∈ Icc τ T,
      HasDerivAt (fun r => Phi T r) (-((Phi T s).comp (D s (x s)))) s)
    (hF : Continuous F.uncurry)
    (hxc : ContinuousOn x (Icc τ T))
    (hx : ∀ t ∈ Ioo τ T, HasDerivWithinAt x (F t (x t)) (Ici t) t)
    (hD : ∀ t ∈ Icc τ T, ∀ z, HasFDerivAt (F t) (D t z) z)
    (hDc : ∀ t ∈ Icc τ T, ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x t))
    (hyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ContinuousOn (y ε) (Icc τ T))
    (hy : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Ioo τ T,
      HasDerivWithinAt (y ε) (F t (y ε t)) (Ici t) t)
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc τ T, ‖y ε t - x t‖ ≤ C * ε)
    (hjump : Tendsto (fun ε : ℝ => ε⁻¹ • (y ε τ - x τ - ε • g))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ε⁻¹ •
      (y ε T - x T - ε • Phi T τ g)) (𝓝[>] 0) (𝓝 0) := by
  let r : ℝ → ℝ → E := fun ε t => taylorError (F t) (D t (x t)) (x t) (y ε t)
  have hr : UniformSmall r (Icc τ T) :=
    uniformSmall_taylorError hC hxc hD hDc hbound
  have hPc : ContinuousOn (fun s => Phi T s) (Icc τ T) :=
    fun s hs => (hback s hs).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hPc
  have hsmall : UniformSmall (fun ε t => Phi T t (r ε t)) (uIcc τ T) := by
    rw [uIcc_of_le hτT]
    exact _root_.UniformSmall.clm_apply hr (le_max_right B 0)
      (fun t ht => (hB t ht).trans (le_max_left B 0))
  have hrem := hsmall.tendsto_scaled_integral
  have hAc : ContinuousOn (fun t => D t (x t)) (Icc τ T) := by
    intro t ht
    exact (hDc t ht).comp_continuousWithinAt (f := fun s : ℝ => (s, x s))
      (continuousWithinAt_id.prodMk (hxc t ht))
  have hduhamel : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      y ε T - x T = Phi T τ (y ε τ - x τ) + ∫ t in τ..T, Phi T t (r ε t) := by
    filter_upwards [hyc, hy] with ε hycε hyε
    have hec : ContinuousOn (fun t => y ε t - x t) (Icc τ T) := hycε.sub hxc
    have hrc : ContinuousOn (r ε) (Icc τ T) :=
      ((hF.comp_continuousOn (continuousOn_id.prodMk hycε)).sub
        (hF.comp_continuousOn (continuousOn_id.prodMk hxc))).sub (hAc.clm_apply hec)
    have hint : IntervalIntegrable (fun t => Phi T t (r ε t)) volume τ T := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le hτT] using hPc.clm_apply hrc
    apply variationOfConstants_right_of_backward hτT hdiag hback hec _ hint
    intro t ht
    convert (hyε t ht).sub (hx t ht) using 1
    dsimp [r, taylorError]
    abel
  have hstart : Tendsto (fun ε : ℝ =>
      ε⁻¹ • (Phi T τ (y ε τ - x τ) - ε • Phi T τ g)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Phi T τ).continuous.continuousAt.tendsto.comp hjump
    simpa only [Function.comp_def, map_smul, map_sub, map_zero] using h
  have hsum := hstart.add hrem
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hduhamel] with ε hε
  rw [hε]
  simp only [← smul_add]
  congr 1
  abel

/-- The uncentered terminal tangent limit, in the form used by endpoint
variation cones and Hahn–Banach separation. -/
theorem terminal_tangent_of_right_ODE
    {F : ℝ → E → E} {D : ℝ → E → E →L[ℝ] E}
    {x : ℝ → E} {y : ℝ → ℝ → E} {τ T C : ℝ} {g : E}
    {Phi : ℝ → ℝ → E →L[ℝ] E}
    (hτT : τ ≤ T) (hC : 0 ≤ C)
    (hdiag : Phi T T = ContinuousLinearMap.id ℝ E)
    (hback : ∀ s ∈ Icc τ T,
      HasDerivAt (fun r => Phi T r) (-((Phi T s).comp (D s (x s)))) s)
    (hF : Continuous F.uncurry)
    (hxc : ContinuousOn x (Icc τ T))
    (hx : ∀ t ∈ Ioo τ T, HasDerivWithinAt x (F t (x t)) (Ici t) t)
    (hD : ∀ t ∈ Icc τ T, ∀ z, HasFDerivAt (F t) (D t z) z)
    (hDc : ∀ t ∈ Icc τ T, ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x t))
    (hyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ContinuousOn (y ε) (Icc τ T))
    (hy : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Ioo τ T,
      HasDerivWithinAt (y ε) (F t (y ε t)) (Ici t) t)
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc τ T, ‖y ε t - x t‖ ≤ C * ε)
    (hjump : Tendsto (fun ε : ℝ => ε⁻¹ • (y ε τ - x τ - ε • g))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (y ε T - x T))
      (𝓝[>] 0) (𝓝 (Phi T τ g)) := by
  have h := terminal_sensitivity_of_right_ODE hτT hC hdiag hback hF hxc hx
    hD hDc hyc hy hbound hjump
  have hsum := h.add_const (Phi T τ g)
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hpos
  have hε : ε ≠ (0 : ℝ) := ne_of_gt hpos
  simp [smul_sub, smul_smul, hε]
