/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

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

/-- Uniform first-order smallness on a fixed time set. -/
def UniformSmall (r : ℝ → ℝ → G) (s : Set ℝ) : Prop :=
  ∀ η > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ s, ‖r ε t‖ ≤ η * ε

/-- Spatial Taylor's estimate uniformly along a compact reference graph.
Only continuity at the graph points is required of the derivative; the
nearby evaluation points need not belong to the graph or a compact tube. -/
theorem uniform_taylorError_near_reference
    {F : ℝ → E → G} {D : ℝ → E → E →L[ℝ] G} {x : ℝ → E}
    {a b : ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hD : ∀ t ∈ Icc a b, ∀ y, HasFDerivAt (F t) (D t y) y)
    (hDc : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x t))
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ t ∈ Icc a b, ∀ y, ‖y - x t‖ < δ →
      ‖taylorError (F t) (D t (x t)) (x t) y‖ ≤ η * ‖y - x t‖ := by
  let K : Set (ℝ × E) := (fun t => (t, x t)) '' Icc a b
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hx)
  have hcont : ∀ q ∈ K, ContinuousAt (fun q : ℝ × E => D q.1 q.2) q := by
    rintro q ⟨t, ht, rfl⟩
    exact hDc t ht
  have hunif := hK.uniformContinuousAt_of_continuousAt
    (fun q : ℝ × E => D q.1 q.2) hcont (Metric.dist_mem_uniformity hη)
  obtain ⟨δ, hδ, hclose⟩ := Metric.mem_uniformity_dist.mp hunif
  refine ⟨δ, hδ, fun t ht y hy => ?_⟩
  apply norm_taylorError_le_of_derivative_bound (fun z _ => hD t ht z)
  intro z hz
  have hzclose : dist (t, x t) (t, z) < δ := by
    rw [dist_prod_same_left, dist_eq_norm, norm_sub_rev]
    exact (norm_sub_le_of_mem_segment hz).trans_lt hy
  have hh := hclose hzclose (show (t, x t) ∈ K from ⟨t, ht, rfl⟩)
  change dist (D t (x t)) (D t z) < η at hh
  rw [dist_eq_norm, norm_sub_rev] at hh
  exact hh.le


/-- Continuous spatial derivatives along the compact reference graph give a
uniform local Lipschitz increment bound, without any global Lipschitz premise. -/
theorem exists_uniform_increment_bound_near_reference
    {F : ℝ → E → G} {D : ℝ → E → E →L[ℝ] G} {x : ℝ → E} {a b : ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hD : ∀ t ∈ Icc a b, ∀ z, HasFDerivAt (F t) (D t z) z)
    (hDc : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x t)) :
    ∃ δ > 0, ∃ M ≥ 0, ∀ t ∈ Icc a b, ∀ y, ‖y - x t‖ < δ →
      ‖F t y - F t (x t)‖ ≤ M * ‖y - x t‖ := by
  obtain ⟨δ, hδ, hTaylor⟩ := uniform_taylorError_near_reference hx hD hDc zero_lt_one
  have hDpath : ContinuousOn (fun t => D t (x t)) (Icc a b) := by
    intro t ht
    exact (hDc t ht).comp_continuousWithinAt (f := fun r : ℝ => (r, x r))
      (continuousWithinAt_id.prodMk (hx t ht))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hDpath
  refine ⟨δ, hδ, max B 0 + 1, by positivity, fun t ht y hy => ?_⟩
  calc
    ‖F t y - F t (x t)‖ =
        ‖taylorError (F t) (D t (x t)) (x t) y + D t (x t) (y - x t)‖ := by
      rw [taylorError, sub_add_cancel]
    _ ≤ ‖taylorError (F t) (D t (x t)) (x t) y‖ + ‖D t (x t) (y - x t)‖ :=
      norm_add_le _ _
    _ ≤ 1 * ‖y - x t‖ + max B 0 * ‖y - x t‖ := by
      apply add_le_add (hTaylor t ht y hy)
      exact (D t (x t)).le_opNorm (y - x t) |>.trans
        (mul_le_mul_of_nonneg_right ((hB t ht).trans (le_max_left _ _)) (norm_nonneg _))
    _ = (max B 0 + 1) * ‖y - x t‖ := by ring

/-- Actual `O(ε)` displacements eventually lie in the derived local Lipschitz
neighborhood; their nonlinear function increments are uniformly `O(ε)`. -/
theorem exists_eventually_increment_le_linear
    {F : ℝ → E → G} {D : ℝ → E → E →L[ℝ] G}
    {x : ℝ → E} {y : ℝ → ℝ → E} {a b C : ℝ}
    (hC : 0 ≤ C)
    (hx : ContinuousOn x (Icc a b))
    (hD : ∀ t ∈ Icc a b, ∀ z, HasFDerivAt (F t) (D t z) z)
    (hDc : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x t))
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc a b, ‖y ε t - x t‖ ≤ C * ε) :
    ∃ B ≥ 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc a b,
      ‖F t (y ε t) - F t (x t)‖ ≤ B * ε := by
  obtain ⟨δ, hδ, M, hM, hlocal⟩ :=
    exists_uniform_increment_bound_near_reference hx hD hDc
  have hεsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C * ε < δ := by
    have ht : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
    exact ht.eventually (gt_mem_nhds hδ)
  refine ⟨M * C, mul_nonneg hM hC, ?_⟩
  filter_upwards [hbound, hεsmall] with ε hε heδ
  intro t ht
  calc
    _ ≤ M * ‖y ε t - x t‖ := hlocal t ht (y ε t) ((hε t ht).trans_lt heδ)
    _ ≤ M * (C * ε) := mul_le_mul_of_nonneg_left (hε t ht) hM
    _ = (M * C) * ε := by ring

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

/-- Uniform `O(ε)` trajectory displacement makes the actual nominal Taylor
error uniformly `o(ε)`, using only the continuous spatial derivative. -/
theorem uniformSmall_taylorError
    {F : ℝ → E → G} {D : ℝ → E → E →L[ℝ] G}
    {x : ℝ → E} {y : ℝ → ℝ → E} {a b C : ℝ}
    (hC : 0 ≤ C)
    (hx : ContinuousOn x (Icc a b))
    (hD : ∀ t ∈ Icc a b, ∀ z, HasFDerivAt (F t) (D t z) z)
    (hDc : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x t))
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc a b, ‖y ε t - x t‖ ≤ C * ε) :
    UniformSmall (fun ε t => taylorError (F t) (D t (x t)) (x t) (y ε t))
      (Icc a b) := by
  intro η hη
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨δ, hδ, hTaylor⟩ := uniform_taylorError_near_reference hx hD hDc
    (div_pos hη hCp)
  have hεsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C * ε < δ := by
    have ht : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
    exact ht.eventually (gt_mem_nhds hδ)
  filter_upwards [hbound, hεsmall, self_mem_nhdsWithin] with ε hε hsmall hpos
  intro t ht
  have hεpos : 0 < ε := hpos
  calc
    _ ≤ (η / (C + 1)) * ‖y ε t - x t‖ :=
      hTaylor t ht (y ε t) ((hε t ht).trans_lt hsmall)
    _ ≤ (η / (C + 1)) * (C * ε) :=
      mul_le_mul_of_nonneg_left (hε t ht) (div_nonneg hη.le hCp.le)
    _ ≤ η * ε := by
      have hcfrac : C / (C + 1) ≤ 1 := (div_le_one hCp).mpr (by linarith)
      calc
        _ = (η * ε) * (C / (C + 1)) := by ring
        _ ≤ (η * ε) * 1 := mul_le_mul_of_nonneg_left hcfrac (by positivity)
        _ = _ := mul_one _

/-- Uniform first-order smallness passes through a fixed finite integral. -/
theorem UniformSmall.tendsto_scaled_integral
    {r : ℝ → ℝ → G} {a b : ℝ}
    (h : UniformSmall r (uIcc a b)) :
    Tendsto (fun ε : ℝ => ε⁻¹ • ∫ t in a..b, r ε t) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hlen : 0 < |b - a| + 1 := by positivity
  filter_upwards [h (η / (2 * (|b - a| + 1))) (by positivity),
    self_mem_nhdsWithin] with ε hε hpos
  have hεpos : 0 < ε := hpos
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hεpos]
  have hib : ‖∫ t in a..b, r ε t‖ ≤
      (η / (2 * (|b - a| + 1)) * ε) * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht => hε t (uIoc_subset_uIcc ht))
  calc
    _ ≤ ε⁻¹ * ((η / (2 * (|b - a| + 1)) * ε) * |b - a|) :=
      mul_le_mul_of_nonneg_left hib (inv_nonneg.mpr hεpos.le)
    _ = (η / 2) * (|b - a| / (|b - a| + 1)) := by
      field_simp [ne_of_gt hεpos]
    _ ≤ (η / 2) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_one hlen).mpr (by linarith)
    _ < η := by linarith

/-- Terminal Taylor error needs only Fréchet differentiability at the
reference endpoint, together with an actual `O(ε)` endpoint displacement. -/
theorem tendsto_scaled_terminal_taylorError
    {K : E → G} {k : E →L[ℝ] G} {x : E} {y : ℝ → E} {C : ℝ}
    (hK : HasFDerivAt K k x)
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖y ε - x‖ ≤ C * ε) :
    Tendsto (fun ε : ℝ => ε⁻¹ • taylorError K k x (y ε)) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
  have hd : Tendsto (fun ε => y ε - x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound ht)
  have hy : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    simpa only [sub_add_cancel, zero_add] using hd.add_const x
  have hbig : (fun ε => y ε - x) =O[𝓝[>] (0 : ℝ)] (fun ε : ℝ => ε) := by
    apply IsBigO.of_bound C
    filter_upwards [hbound, self_mem_nhdsWithin] with ε hε hpos
    simpa only [Real.norm_eq_abs, abs_of_pos (show 0 < ε from hpos)] using hε
  exact ((hK.isLittleO.comp_tendsto hy).trans_isBigO hbig).tendsto_inv_smul_nhds_zero

end Normed


section UniformSmallRules

variable {G : Type*} [NormedAddCommGroup G]

/-- Addition preserves uniform first-order smallness. -/
theorem UniformSmall.add
    {r q : ℝ → ℝ → G} {s : Set ℝ}
    (hr : UniformSmall r s) (hq : UniformSmall q s) :
    UniformSmall (fun ε t => r ε t + q ε t) s := by
  intro η hη
  filter_upwards [hr (η / 2) (by positivity), hq (η / 2) (by positivity)]
    with ε hrε hqε
  intro t ht
  exact (norm_add_le _ _).trans
    ((add_le_add (hrε t ht) (hqε t ht)).trans_eq (by ring))

end UniformSmallRules

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A bounded costate preserves a uniform first-order error under pairing. -/
theorem UniformSmall.inner_left
    {r : ℝ → ℝ → E} {p : ℝ → E} {s : Set ℝ} {P : ℝ}
    (hr : UniformSmall r s) (hP : 0 ≤ P)
    (hp : ∀ t ∈ s, ‖p t‖ ≤ P) :
    UniformSmall (fun ε t => inner ℝ (p t) (r ε t)) s := by
  intro η hη
  have hPp : 0 < P + 1 := by linarith
  filter_upwards [hr (η / (P + 1)) (div_pos hη hPp), self_mem_nhdsWithin]
    with ε hrε hpos
  intro t ht
  have hεpos : 0 < ε := hpos
  calc
    _ ≤ ‖p t‖ * ‖r ε t‖ := norm_inner_le_norm _ _
    _ ≤ P * (η / (P + 1) * ε) :=
      mul_le_mul (hp t ht) (hrε t ht) (norm_nonneg _) hP
    _ = (η * ε) * (P / (P + 1)) := by ring
    _ ≤ (η * ε) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_one hPp).mpr (by linarith)
    _ = _ := mul_one _

/-- The state-dependent control-increment error on a shrinking needle has
quadratic integral size. This lemma needs a linear displacement bound only. -/
theorem tendsto_scaled_needle_integral
    {r : ℝ → ℝ → ℝ} {τ D : ℝ}
    (hr : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (τ - ε) τ, ‖r ε t‖ ≤ D * ε) :
    Tendsto (fun ε : ℝ => ε⁻¹ * ∫ t in (τ - ε)..τ, r ε t) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_scaled_of_quadratic_bound (B := D)
  filter_upwards [hr, self_mem_nhdsWithin] with ε hε hpos
  have hεpos : 0 < ε := hpos
  have hbound : ∀ t ∈ Ι (τ - ε) τ, ‖r ε t‖ ≤ D * ε := by
    intro t ht
    rw [uIoc_of_le (by linarith : τ - ε ≤ τ)] at ht
    exact hε t ⟨ht.1.le, ht.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [sub_sub_cancel, abs_of_pos hεpos, pow_two, mul_assoc] using h

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

