/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Uniform smallness and vanishing of parameterised families

Generic right-sided uniform smallness (`O(ε)`) and uniform vanishing (`o(1)`)
of a family indexed by a small parameter and a time set, together with their
closure under addition, subtraction, integration, and pairing with bounded
families. These are the asymptotic tools used by the ODE and needle analyses;
no control-theoretic data appears in the statements.
-/

@[expose] public section

open Set Filter MeasureTheory Asymptotics
open scoped Topology Interval


section QuadraticBound

/-- A quadratic error vanishes after division by the positive needle width. -/
theorem tendsto_scaled_of_quadratic_bound
    {R : ℝ → ℝ} {B : ℝ}
    (hR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖R ε‖ ≤ B * ε ^ 2) :
    Tendsto (fun ε : ℝ => ε⁻¹ * R ε) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖ε⁻¹ * R ε‖ ≤ B * ε := by
    filter_upwards [hR, self_mem_nhdsWithin] with ε hε hpos
    have hεpos : 0 < ε := hpos
    rw [norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hεpos]
    calc
      ε⁻¹ * ‖R ε‖ ≤ ε⁻¹ * (B * ε ^ 2) :=
        mul_le_mul_of_nonneg_left hε (inv_nonneg.mpr hεpos.le)
      _ = B * ε := by field_simp [ne_of_gt hεpos]
  have hlinear : Tendsto (fun ε : ℝ => B * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hlinear

end QuadraticBound


section UniformVanishing

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

end UniformVanishing


section UniformVanishingInner

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

end UniformVanishingInner


section UniformSmall

variable {G : Type*} [NormedAddCommGroup G]

/-- Uniform first-order smallness on a fixed time set. -/
def UniformSmall (r : ℝ → ℝ → G) (s : Set ℝ) : Prop :=
  ∀ η > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ s, ‖r ε t‖ ≤ η * ε

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

end UniformSmall


section UniformSmallIntegral

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

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

end UniformSmallIntegral


section UniformSmallInner

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

end UniformSmallInner


section UniformSmallCLM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A uniformly bounded operator family preserves uniform first-order smallness. -/
theorem _root_.UniformSmall.clm_apply
    {r : ℝ → ℝ → E} {P : ℝ → E →L[ℝ] E} {s : Set ℝ} {B : ℝ}
    (hr : UniformSmall r s) (hB : 0 ≤ B) (hP : ∀ t ∈ s, ‖P t‖ ≤ B) :
    UniformSmall (fun ε t => P t (r ε t)) s := by
  intro η hη
  have hBp : 0 < B + 1 := by linarith
  filter_upwards [hr (η / (B + 1)) (div_pos hη hBp), self_mem_nhdsWithin]
    with ε hrε hpos
  intro t ht
  have hεpos : 0 < ε := hpos
  calc
    ‖P t (r ε t)‖ ≤ ‖P t‖ * ‖r ε t‖ := (P t).le_opNorm _
    _ ≤ B * (η / (B + 1) * ε) :=
      mul_le_mul (hP t ht) (hrε t ht) (norm_nonneg _) hB
    _ = (η * ε) * (B / (B + 1)) := by ring
    _ ≤ (η * ε) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_one hBp).mpr (by linarith)
    _ = _ := mul_one _

end UniformSmallCLM
