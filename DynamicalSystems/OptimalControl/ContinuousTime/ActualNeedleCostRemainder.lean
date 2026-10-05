/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.Calculus.TaylorRemainder
public import DynamicalSystems.OptimalControl.ContinuousTime.UniformNeedleRemainder
public import DynamicalSystems.OptimalControl.ContinuousTime.UniformTaylorRemainder

/-!
# An actual nonlinear needle _root_.needleCostRemainder from primitive data

This adapter specializes the uniform Taylor and shrinking-interval estimates
to the original nominal/test dynamics and running costs. Its hypotheses are
derivatives, continuity, ordinary spatial Lipschitz bounds, a bounded costate,
and the already-derived uniform `O(ε)` trajectory displacement. The actual
total _root_.needleCostRemainder divided by `ε` is a conclusion.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval NNReal


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact Taylor/control-increment expression left by adjoint cancellation.
Every term is defined from the original dynamics and costs at the actual states. -/
noncomputable def _root_.actualNeedleCostFamilyRemainder
    (F₀ Fv : ℝ → E → E) (L₀ Lv : ℝ → E → ℝ) (K : E → ℝ)
    (A : ℝ → E →L[ℝ] E) (ell : ℝ → E →L[ℝ] ℝ) (k : E →L[ℝ] ℝ)
    (x : ℝ → E) (y : ℝ → ℝ → E) (p : ℝ → E) (T τ ε : ℝ) : ℝ :=
  _root_.needleCostRemainder (fun ε => taylorError K k (x T) (y ε T))
    (fun ε t => taylorError (L₀ t) (ell t) (x t) (y ε t))
    (fun ε t => controlIncrementError (Lv t) (L₀ t) (x t) (y ε t))
    (fun ε t => taylorError (F₀ t) (A t) (x t) (y ε t))
    (fun ε t => controlIncrementError (Fv t) (F₀ t) (x t) (y ε t))
    p T τ ε

/-- The full actual error is `o(ε)`. Continuous nominal derivatives suffice;
no Lipschitz derivative, supplied Taylor modulus, or cost sensitivity is needed.
The four branch Lipschitz bounds only control the shrinking needle interval. -/
theorem _root_.tendsto_scaled_actualNeedleCostFamilyRemainder
    {F₀ Fv : ℝ → E → E} {L₀ Lv : ℝ → E → ℝ} {K : E → ℝ}
    {DF : ℝ → E → E →L[ℝ] E} {DL : ℝ → E → E →L[ℝ] ℝ}
    {k : E →L[ℝ] ℝ} {x : ℝ → E} {y : ℝ → ℝ → E} {p : ℝ → E}
    {T τ C P : ℝ} {K₀ Kv M₀ Mv : ℝ≥0}
    (hτ : 0 < τ) (hτT : τ ≤ T) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hx : ContinuousOn x (Icc 0 T))
    (hDF : ∀ t ∈ Icc 0 T, ∀ z, HasFDerivAt (F₀ t) (DF t z) z)
    (hDFc : ∀ t ∈ Icc 0 T,
      ContinuousAt (fun q : ℝ × E => DF q.1 q.2) (t, x t))
    (hDL : ∀ t ∈ Icc 0 T, ∀ z, HasFDerivAt (L₀ t) (DL t z) z)
    (hDLc : ∀ t ∈ Icc 0 T,
      ContinuousAt (fun q : ℝ × E => DL q.1 q.2) (t, x t))
    (hK : HasFDerivAt K k (x T))
    (hF₀ : ∀ t ∈ Icc 0 T, LipschitzWith K₀ (F₀ t))
    (hFv : ∀ t ∈ Icc 0 T, LipschitzWith Kv (Fv t))
    (hL₀ : ∀ t ∈ Icc 0 T, LipschitzWith M₀ (L₀ t))
    (hLv : ∀ t ∈ Icc 0 T, LipschitzWith Mv (Lv t))
    (hp : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ P)
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc 0 T, ‖y ε t - x t‖ ≤ C * ε) :
    Tendsto (fun ε : ℝ => ε⁻¹ * _root_.actualNeedleCostFamilyRemainder F₀ Fv L₀ Lv K
      (fun t => DF t (x t)) (fun t => DL t (x t)) k x y p T τ ε)
      (𝓝[>] 0) (𝓝 0) := by
  have hT : 0 ≤ T := hτ.le.trans hτT
  have hKbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖y ε T - x T‖ ≤ C * ε := by
    filter_upwards [hbound] with ε hε
    exact hε T ⟨hT, le_rfl⟩
  have hKlim : Tendsto
      (fun ε : ℝ => ε⁻¹ * taylorError K k (x T) (y ε T)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [smul_eq_mul] using tendsto_scaled_terminal_taylorError hK hKbound
  have hfsmall := uniformSmall_taylorError hC hx hDF hDFc hbound
  have hLsmall := uniformSmall_taylorError hC hx hDL hDLc hbound
  have hεsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < τ :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hτ)
  have hshort : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (τ - ε) τ,
      ‖controlIncrementError (Lv t) (L₀ t) (x t) (y ε t) +
        inner ℝ (p t) (controlIncrementError (Fv t) (F₀ t) (x t) (y ε t))‖ ≤
        (((Mv : ℝ) + M₀ + P * ((Kv : ℝ) + K₀)) * C) * ε := by
    filter_upwards [hbound, hεsmall] with ε hε heτ
    intro t ht
    have htT : t ∈ Icc (0 : ℝ) T := ⟨(by linarith [ht.1]), ht.2.trans hτT⟩
    have hcf : ‖controlIncrementError (Fv t) (F₀ t) (x t) (y ε t)‖ ≤
        ((Kv : ℝ) + K₀) * ‖y ε t - x t‖ := by
      apply norm_controlIncrementError_le
      · simpa only [dist_eq_norm] using (hFv t htT).dist_le_mul (y ε t) (x t)
      · simpa only [dist_eq_norm] using (hF₀ t htT).dist_le_mul (y ε t) (x t)
    have hcL : ‖controlIncrementError (Lv t) (L₀ t) (x t) (y ε t)‖ ≤
        ((Mv : ℝ) + M₀) * ‖y ε t - x t‖ := by
      apply norm_controlIncrementError_le
      · simpa only [dist_eq_norm] using (hLv t htT).dist_le_mul (y ε t) (x t)
      · simpa only [dist_eq_norm] using (hL₀ t htT).dist_le_mul (y ε t) (x t)
    calc
      _ ≤ ‖controlIncrementError (Lv t) (L₀ t) (x t) (y ε t)‖ +
          ‖inner ℝ (p t) (controlIncrementError (Fv t) (F₀ t) (x t) (y ε t))‖ :=
        norm_add_le _ _
      _ ≤ ((Mv : ℝ) + M₀) * ‖y ε t - x t‖ +
          P * (((Kv : ℝ) + K₀) * ‖y ε t - x t‖) := by
        apply add_le_add hcL
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (hp t htT) hcf (norm_nonneg _) hP)
      _ = ((Mv : ℝ) + M₀ + P * ((Kv : ℝ) + K₀)) * ‖y ε t - x t‖ := by ring
      _ ≤ ((Mv : ℝ) + M₀ + P * ((Kv : ℝ) + K₀)) * (C * ε) :=
        mul_le_mul_of_nonneg_left (hε t htT) (by positivity)
      _ = _ := by ring
  exact _root_.tendsto_scaled_needleCostRemainder_of_uniformSmall hT hP hp hKlim hLsmall hfsmall hshort


/-- Actual nonlinear _root_.needleCostRemainder under continuous spatial derivatives of the
running costs. No global spatial Lipschitz assumption is imposed on either
running-cost branch; a uniform local increment bound is derived along the
compact reference graph. Thus this version includes quadratic state costs. -/
theorem _root_.tendsto_scaled_actualNeedleCostFamilyRemainder_of_C1
    {F₀ Fv : ℝ → E → E} {L₀ Lv : ℝ → E → ℝ} {K : E → ℝ}
    {DF : ℝ → E → E →L[ℝ] E} {DL₀ DLv : ℝ → E → E →L[ℝ] ℝ}
    {k : E →L[ℝ] ℝ} {x : ℝ → E} {y : ℝ → ℝ → E} {p : ℝ → E}
    {T τ C P : ℝ} {K₀ Kv : ℝ≥0}
    (hτ : 0 < τ) (hτT : τ ≤ T) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hx : ContinuousOn x (Icc 0 T))
    (hDF : ∀ t ∈ Icc 0 T, ∀ z, HasFDerivAt (F₀ t) (DF t z) z)
    (hDFc : ∀ t ∈ Icc 0 T,
      ContinuousAt (fun q : ℝ × E => DF q.1 q.2) (t, x t))
    (hDL₀ : ∀ t ∈ Icc 0 T, ∀ z, HasFDerivAt (L₀ t) (DL₀ t z) z)
    (hDL₀c : ∀ t ∈ Icc 0 T,
      ContinuousAt (fun q : ℝ × E => DL₀ q.1 q.2) (t, x t))
    (hDLv : ∀ t ∈ Icc 0 T, ∀ z, HasFDerivAt (Lv t) (DLv t z) z)
    (hDLvc : ∀ t ∈ Icc 0 T,
      ContinuousAt (fun q : ℝ × E => DLv q.1 q.2) (t, x t))
    (hK : HasFDerivAt K k (x T))
    (hF₀ : ∀ t ∈ Icc 0 T, LipschitzWith K₀ (F₀ t))
    (hFv : ∀ t ∈ Icc 0 T, LipschitzWith Kv (Fv t))
    (hp : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ P)
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc 0 T, ‖y ε t - x t‖ ≤ C * ε) :
    Tendsto (fun ε : ℝ => ε⁻¹ * _root_.actualNeedleCostFamilyRemainder F₀ Fv L₀ Lv K
      (fun t => DF t (x t)) (fun t => DL₀ t (x t)) k x y p T τ ε)
      (𝓝[>] 0) (𝓝 0) := by
  have hT : 0 ≤ T := hτ.le.trans hτT
  have hKbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖y ε T - x T‖ ≤ C * ε := by
    filter_upwards [hbound] with ε hε
    exact hε T ⟨hT, le_rfl⟩
  have hKlim : Tendsto
      (fun ε : ℝ => ε⁻¹ * taylorError K k (x T) (y ε T)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [smul_eq_mul] using tendsto_scaled_terminal_taylorError hK hKbound
  have hfsmall := uniformSmall_taylorError hC hx hDF hDFc hbound
  have hLsmall := uniformSmall_taylorError hC hx hDL₀ hDL₀c hbound
  obtain ⟨BL, _, hctrlL⟩ := exists_eventually_controlIncrementError_le_linear
    hC hx hDL₀ hDL₀c hDLv hDLvc hbound
  have hεsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < τ :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hτ)
  have hshort : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (τ - ε) τ,
      ‖controlIncrementError (Lv t) (L₀ t) (x t) (y ε t) +
        inner ℝ (p t) (controlIncrementError (Fv t) (F₀ t) (x t) (y ε t))‖ ≤
        (BL + P * (((Kv : ℝ) + K₀) * C)) * ε := by
    filter_upwards [hbound, hctrlL, hεsmall] with ε hε hcL heτ
    intro t ht
    have htT : t ∈ Icc (0 : ℝ) T := ⟨(by linarith [ht.1]), ht.2.trans hτT⟩
    have hcf : ‖controlIncrementError (Fv t) (F₀ t) (x t) (y ε t)‖ ≤
        ((Kv : ℝ) + K₀) * ‖y ε t - x t‖ := by
      apply norm_controlIncrementError_le
      · simpa only [dist_eq_norm] using (hFv t htT).dist_le_mul (y ε t) (x t)
      · simpa only [dist_eq_norm] using (hF₀ t htT).dist_le_mul (y ε t) (x t)
    have hcf' : ‖controlIncrementError (Fv t) (F₀ t) (x t) (y ε t)‖ ≤
        (((Kv : ℝ) + K₀) * C) * ε := by
      calc
        _ ≤ ((Kv : ℝ) + K₀) * ‖y ε t - x t‖ := hcf
        _ ≤ ((Kv : ℝ) + K₀) * (C * ε) :=
          mul_le_mul_of_nonneg_left (hε t htT) (by positivity)
        _ = _ := by ring
    calc
      _ ≤ ‖controlIncrementError (Lv t) (L₀ t) (x t) (y ε t)‖ +
          ‖inner ℝ (p t) (controlIncrementError (Fv t) (F₀ t) (x t) (y ε t))‖ :=
        norm_add_le _ _
      _ ≤ BL * ε + P * ((((Kv : ℝ) + K₀) * C) * ε) := by
        apply add_le_add (hcL t htT)
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (hp t htT) hcf' (norm_nonneg _) hP)
      _ = _ := by ring
  exact _root_.tendsto_scaled_needleCostRemainder_of_uniformSmall hT hP hp hKlim hLsmall hfsmall hshort


/-- The weakest branch-regularity version: only the nominal spatial
linearizations and terminal derivative are needed. Both test branches merely
need joint continuity along the reference graph, because their nonlinear
control-increment corrections are supported on the shrinking needle interval.
In particular, fixed-control running costs need not have spatial derivatives
or global Lipschitz bounds. -/
theorem _root_.tendsto_scaled_actualNeedleCostFamilyRemainder_of_continuous
    {F₀ Fv : ℝ → E → E} {L₀ Lv : ℝ → E → ℝ} {K : E → ℝ}
    {DF : ℝ → E → E →L[ℝ] E} {DL : ℝ → E → E →L[ℝ] ℝ}
    {k : E →L[ℝ] ℝ} {x : ℝ → E} {y : ℝ → ℝ → E} {p : ℝ → E}
    {T τ C P : ℝ}
    (hτ : 0 < τ) (hτT : τ ≤ T) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hx : ContinuousOn x (Icc 0 T))
    (hDF : ∀ t ∈ Icc 0 T, ∀ z, HasFDerivAt (F₀ t) (DF t z) z)
    (hDFc : ∀ t ∈ Icc 0 T,
      ContinuousAt (fun q : ℝ × E => DF q.1 q.2) (t, x t))
    (hDL : ∀ t ∈ Icc 0 T, ∀ z, HasFDerivAt (L₀ t) (DL t z) z)
    (hDLc : ∀ t ∈ Icc 0 T,
      ContinuousAt (fun q : ℝ × E => DL q.1 q.2) (t, x t))
    (hK : HasFDerivAt K k (x T))
    (hF₀ : ∀ t ∈ Icc 0 T, ContinuousAt (fun q : ℝ × E => F₀ q.1 q.2) (t, x t))
    (hFv : ∀ t ∈ Icc 0 T, ContinuousAt (fun q : ℝ × E => Fv q.1 q.2) (t, x t))
    (hL₀ : ∀ t ∈ Icc 0 T, ContinuousAt (fun q : ℝ × E => L₀ q.1 q.2) (t, x t))
    (hLv : ∀ t ∈ Icc 0 T, ContinuousAt (fun q : ℝ × E => Lv q.1 q.2) (t, x t))
    (hp : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ P)
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc 0 T, ‖y ε t - x t‖ ≤ C * ε) :
    Tendsto (fun ε : ℝ => ε⁻¹ * _root_.actualNeedleCostFamilyRemainder F₀ Fv L₀ Lv K
      (fun t => DF t (x t)) (fun t => DL t (x t)) k x y p T τ ε)
      (𝓝[>] 0) (𝓝 0) := by
  have hT : 0 ≤ T := hτ.le.trans hτT
  have hKbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖y ε T - x T‖ ≤ C * ε := by
    filter_upwards [hbound] with ε hε
    exact hε T ⟨hT, le_rfl⟩
  have hKlim : Tendsto
      (fun ε : ℝ => ε⁻¹ * taylorError K k (x T) (y ε T)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [smul_eq_mul] using tendsto_scaled_terminal_taylorError hK hKbound
  have hfsmall := uniformSmall_taylorError hC hx hDF hDFc hbound
  have hLsmall := uniformSmall_taylorError hC hx hDL hDLc hbound
  have hcf := uniformVanishing_controlIncrementError hx hF₀ hFv hbound
  have hcL := uniformVanishing_controlIncrementError hx hL₀ hLv hbound
  exact _root_.tendsto_scaled_needleCostRemainder_of_uniformVanishing hτ hτT hP hp hKlim
    hLsmall hfsmall hcL hcf

