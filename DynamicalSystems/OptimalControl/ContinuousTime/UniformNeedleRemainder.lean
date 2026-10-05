/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.Asymptotics.Uniform
public import DynamicalSystems.OptimalControl.ContinuousTime.NeedleCostRemainder

/-!
# Continuous control branches on a shrinking needle

The control-increment correction is supported on a shrinking interval.
Its divided integral vanishes as soon as the correction tends uniformly to
zero, which follows from joint continuity along the compact reference graph.
Neither a derivative nor a spatial Lipschitz bound for the test running-cost
branch is needed for this argument.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval


section Normed

variable {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]

/-- The actual control-increment correction vanishes uniformly under joint
continuity of both original branches, without spatial differentiability. -/
theorem uniformVanishing_controlIncrementError
    {F₀ Fv : ℝ → E → G} {x : ℝ → E} {y : ℝ → ℝ → E} {a b C : ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hF₀ : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => F₀ q.1 q.2) (t, x t))
    (hFv : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => Fv q.1 q.2) (t, x t))
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc a b, ‖y ε t - x t‖ ≤ C * ε) :
    UniformVanishing
      (fun ε t => controlIncrementError (Fv t) (F₀ t) (x t) (y ε t)) (Icc a b) :=
  (uniformVanishing_increment hx hFv hbound).sub
    (uniformVanishing_increment hx hF₀ hbound)

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nominal `o(ε)` Taylor error and a uniformly vanishing needle correction
combine into a total `o(ε)` error after the exact adjoint cancellation. -/
theorem _root_.tendsto_scaled_needleCostRemainder_of_uniformVanishing
    {rK : ℝ → ℝ} {rL cL : ℝ → ℝ → ℝ} {rf cf : ℝ → ℝ → E}
    {p : ℝ → E} {T τ P : ℝ}
    (hτ : 0 < τ) (hτT : τ ≤ T) (hP : 0 ≤ P)
    (hp : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ P)
    (hK : Tendsto (fun ε : ℝ => ε⁻¹ * rK ε) (𝓝[>] 0) (𝓝 0))
    (hL : UniformSmall rL (Icc 0 T)) (hf : UniformSmall rf (Icc 0 T))
    (hcL : UniformVanishing cL (Icc 0 T)) (hcf : UniformVanishing cf (Icc 0 T)) :
    Tendsto (fun ε : ℝ => ε⁻¹ * _root_.needleCostRemainder rK rL cL rf cf p T τ ε)
      (𝓝[>] 0) (𝓝 0) := by
  have hT : 0 ≤ T := hτ.le.trans hτT
  have hnom := hL.add (hf.inner_left hP hp)
  have hnom' : UniformSmall (fun ε t => rL ε t + inner ℝ (p t) (rf ε t))
      (uIcc 0 T) := by
    simpa only [uIcc_of_le hT] using hnom
  have hnomlim : Tendsto
      (fun ε : ℝ => ε⁻¹ * ∫ t in 0..T, rL ε t + inner ℝ (p t) (rf ε t))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [smul_eq_mul] using hnom'.tendsto_scaled_integral
  have hshortlim := (hcL.add (hcf.inner_left hP hp)).tendsto_scaled_needle_integral hτ hτT
  simpa only [_root_.needleCostRemainder, mul_add, zero_add, add_zero] using
    (hK.add hnomlim).add hshortlim

end InnerProduct
