/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.UniformTaylorRemainder

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

/-- Uniform convergence to zero on a fixed time set. -/
def UniformVanishing (r : ℝ → ℝ → G) (s : Set ℝ) : Prop :=
  ∀ η > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ s, ‖r ε t‖ ≤ η

/-- Uniform continuity along the compact reference graph turns actual state
closeness into uniform vanishing of the original function increments. -/
theorem uniformVanishing_increment
    {F : ℝ → E → G} {x : ℝ → E} {y : ℝ → ℝ → E} {a b C : ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hF : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => F q.1 q.2) (t, x t))
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc a b, ‖y ε t - x t‖ ≤ C * ε) :
    UniformVanishing (fun ε t => F t (y ε t) - F t (x t)) (Icc a b) := by
  intro η hη
  let K : Set (ℝ × E) := (fun t => (t, x t)) '' Icc a b
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hx)
  have hcont : ∀ q ∈ K, ContinuousAt (fun q : ℝ × E => F q.1 q.2) q := by
    rintro q ⟨t, ht, rfl⟩
    exact hF t ht
  have hunif := hK.uniformContinuousAt_of_continuousAt
    (fun q : ℝ × E => F q.1 q.2) hcont (Metric.dist_mem_uniformity hη)
  obtain ⟨δ, hδ, hclose⟩ := Metric.mem_uniformity_dist.mp hunif
  have hεsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C * ε < δ := by
    have ht : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
    exact ht.eventually (gt_mem_nhds hδ)
  filter_upwards [hbound, hεsmall] with ε hε heδ
  intro t ht
  have hdist : dist (t, x t) (t, y ε t) < δ := by
    rw [dist_prod_same_left, dist_eq_norm, norm_sub_rev]
    exact (hε t ht).trans_lt heδ
  have hh := hclose hdist (show (t, x t) ∈ K from ⟨t, ht, rfl⟩)
  change dist (F t (x t)) (F t (y ε t)) < η at hh
  rw [dist_eq_norm, norm_sub_rev] at hh
  exact hh.le

/-- Addition preserves uniform vanishing. -/
theorem UniformVanishing.add
    {r q : ℝ → ℝ → G} {s : Set ℝ}
    (hr : UniformVanishing r s) (hq : UniformVanishing q s) :
    UniformVanishing (fun ε t => r ε t + q ε t) s := by
  intro η hη
  filter_upwards [hr (η / 2) (by positivity), hq (η / 2) (by positivity)]
    with ε hrε hqε
  intro t ht
  exact (norm_add_le _ _).trans
    ((add_le_add (hrε t ht) (hqε t ht)).trans_eq (by ring))

/-- Subtraction preserves uniform vanishing. -/
theorem UniformVanishing.sub
    {r q : ℝ → ℝ → G} {s : Set ℝ}
    (hr : UniformVanishing r s) (hq : UniformVanishing q s) :
    UniformVanishing (fun ε t => r ε t - q ε t) s := by
  intro η hη
  filter_upwards [hr (η / 2) (by positivity), hq (η / 2) (by positivity)]
    with ε hrε hqε
  intro t ht
  exact (norm_sub_le _ _).trans
    ((add_le_add (hrε t ht) (hqε t ht)).trans_eq (by ring))

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

/-- Uniform vanishing gives a vanishing average on every sufficiently small
left needle interval, including needles ending at the terminal time. -/
theorem UniformVanishing.tendsto_scaled_needle_integral
    {r : ℝ → ℝ → ℝ} {T τ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T)
    (h : UniformVanishing r (Icc 0 T)) :
    Tendsto (fun ε : ℝ => ε⁻¹ * ∫ t in (τ - ε)..τ, r ε t) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hεsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < τ :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hτ)
  filter_upwards [h (η / 2) (by positivity), hεsmall, self_mem_nhdsWithin]
    with ε hε heτ hpos
  have hεpos : 0 < ε := hpos
  rw [dist_zero_right, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hεpos]
  have hib : ‖∫ t in (τ - ε)..τ, r ε t‖ ≤ (η / 2) * ε := by
    have hbound : ∀ t ∈ Ι (τ - ε) τ, ‖r ε t‖ ≤ η / 2 := by
      intro t ht
      rw [uIoc_of_le (by linarith : τ - ε ≤ τ)] at ht
      exact hε t ⟨by linarith [ht.1], ht.2.trans hτT⟩
    simpa only [sub_sub_cancel, abs_of_pos hεpos] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  calc
    _ ≤ ε⁻¹ * ((η / 2) * ε) :=
      mul_le_mul_of_nonneg_left hib (inv_nonneg.mpr hεpos.le)
    _ = η / 2 := by field_simp [ne_of_gt hεpos]
    _ < η := by linarith

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pairing with a bounded costate preserves uniform vanishing. -/
theorem UniformVanishing.inner_left
    {r : ℝ → ℝ → E} {p : ℝ → E} {s : Set ℝ} {P : ℝ}
    (hr : UniformVanishing r s) (hP : 0 ≤ P)
    (hp : ∀ t ∈ s, ‖p t‖ ≤ P) :
    UniformVanishing (fun ε t => inner ℝ (p t) (r ε t)) s := by
  intro η hη
  have hPp : 0 < P + 1 := by linarith
  filter_upwards [hr (η / (P + 1)) (div_pos hη hPp)] with ε hrε
  intro t ht
  calc
    _ ≤ ‖p t‖ * ‖r ε t‖ := norm_inner_le_norm _ _
    _ ≤ P * (η / (P + 1)) :=
      mul_le_mul (hp t ht) (hrε t ht) (norm_nonneg _) hP
    _ = η * (P / (P + 1)) := by ring
    _ ≤ η * 1 := by
      apply mul_le_mul_of_nonneg_left _ hη.le
      exact (div_le_one hPp).mpr (by linarith)
    _ = _ := mul_one _

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

