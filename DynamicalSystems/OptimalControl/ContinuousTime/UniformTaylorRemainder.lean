/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.Asymptotics.Uniform
public import DynamicalSystems.Mathlib.Analysis.Calculus.TaylorRemainder
public import DynamicalSystems.OptimalControl.ContinuousTime.NeedleCostRemainder
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Uniform spatial Taylor errors from continuous derivatives

Continuity of the actual spatial derivative along the compact reference graph
implies a uniform Taylor estimate for nearby states. Consequently every family
whose state displacement is uniformly `O(ε)` has a Taylor _root_.needleCostRemainder uniformly
`o(ε)`. This derives the estimate from derivative data; no modulus or trajectory
sensitivity is supplied by the caller.
-/

@[expose] public section

open Set Filter MeasureTheory Asymptotics
open scoped Topology Interval


section Normed

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The actual state-dependent control increment has a uniform linear bound
when both branches have continuous spatial derivatives. In particular this
allows quadratic and other non-globally-Lipschitz running costs. -/
theorem exists_eventually_controlIncrementError_le_linear
    {F₀ Fv : ℝ → E → G} {D₀ Dv : ℝ → E → E →L[ℝ] G}
    {x : ℝ → E} {y : ℝ → ℝ → E} {a b C : ℝ}
    (hC : 0 ≤ C) (hx : ContinuousOn x (Icc a b))
    (hD₀ : ∀ t ∈ Icc a b, ∀ z, HasFDerivAt (F₀ t) (D₀ t z) z)
    (hD₀c : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => D₀ q.1 q.2) (t, x t))
    (hDv : ∀ t ∈ Icc a b, ∀ z, HasFDerivAt (Fv t) (Dv t z) z)
    (hDvc : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => Dv q.1 q.2) (t, x t))
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc a b, ‖y ε t - x t‖ ≤ C * ε) :
    ∃ B ≥ 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc a b,
      ‖controlIncrementError (Fv t) (F₀ t) (x t) (y ε t)‖ ≤ B * ε := by
  obtain ⟨B₀, hB₀, h₀⟩ := exists_eventually_increment_le_linear hC hx hD₀ hD₀c hbound
  obtain ⟨Bv, hBv, hv⟩ := exists_eventually_increment_le_linear hC hx hDv hDvc hbound
  refine ⟨Bv + B₀, add_nonneg hBv hB₀, ?_⟩
  filter_upwards [h₀, hv] with ε h₀ε hvε
  intro t ht
  exact (norm_sub_le _ _).trans
    ((add_le_add (hvε t ht) (h₀ε t ht)).trans_eq (by ring))

end Normed


section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Combining a terminal first-order error, nominal Taylor errors, and the
shrinking-interval branch correction produces an `o(ε)` total cost error.
The preceding derivative lemmas establish the smallness hypotheses from
actual problem data and actual perturbed trajectories. -/
theorem _root_.tendsto_scaled_needleCostRemainder_of_uniformSmall
    {rK : ℝ → ℝ} {rL cL : ℝ → ℝ → ℝ} {rf cf : ℝ → ℝ → E}
    {p : ℝ → E} {T τ P D : ℝ}
    (hT : 0 ≤ T) (hP : 0 ≤ P)
    (hp : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ P)
    (hK : Tendsto (fun ε : ℝ => ε⁻¹ * rK ε) (𝓝[>] 0) (𝓝 0))
    (hL : UniformSmall rL (Icc 0 T))
    (hf : UniformSmall rf (Icc 0 T))
    (hshort : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (τ - ε) τ,
      ‖cL ε t + inner ℝ (p t) (cf ε t)‖ ≤ D * ε) :
    Tendsto (fun ε : ℝ => ε⁻¹ * _root_.needleCostRemainder rK rL cL rf cf p T τ ε)
      (𝓝[>] 0) (𝓝 0) := by
  have hnom := hL.add (hf.inner_left hP hp)
  have hnom' : UniformSmall (fun ε t => rL ε t + inner ℝ (p t) (rf ε t))
      (uIcc 0 T) := by
    simpa only [uIcc_of_le hT] using hnom
  have hnomlim : Tendsto
      (fun ε : ℝ => ε⁻¹ * ∫ t in 0..T, rL ε t + inner ℝ (p t) (rf ε t))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [smul_eq_mul] using hnom'.tendsto_scaled_integral
  have hshortlim := tendsto_scaled_needle_integral hshort
  simpa only [_root_.needleCostRemainder, mul_add, zero_add, add_zero] using
    (hK.add hnomlim).add hshortlim

end InnerProduct
