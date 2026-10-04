/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.FlowTransport

/-! # Neighbourhood statements for local flows

This file packages the uniform variational results as neighbourhood statements for
the chosen local flow at a fixed base point. In particular, commuting vector fields
are preserved by the spatial derivative of that same flow, uniformly in time and
initial state near the base point. This is the transport identity used in the
classical simultaneous rectification argument; see Krener, *Encyclopedia of
Systems and Control*, second edition, and Sontag, *Mathematical Control Theory*,
Chapter 4, §4.2.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]

omit [CompleteSpace X] [FiniteDimensional ℝ X] in
/-- Local regularity and any additional neighbourhood property hold on some
common closed ball. The time parameter of the resulting domain is positive. -/
theorem CommonFlowDomain.exists_of_contDiffAt_of_eventually
    {f g : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀)
    (hg : ContDiffAt ℝ 1 g x₀) {P : X → Prop} (hP : ∀ᶠ y in 𝓝 x₀, P y) :
    ∃ D : CommonFlowDomain f g x₀, ∀ y ∈ closedBall x₀ D.r, P y := by
  have h : ∀ᶠ y in 𝓝 x₀, ContDiffAt ℝ 1 f y ∧ ContDiffAt ℝ 1 g y ∧ P y :=
    (hf.eventually (by simp)).and ((hg.eventually (by simp)).and hP)
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.eventually_iff.mp h
  exact ⟨⟨1, r, zero_lt_one, hr, fun y hy ↦ (hball hy).1,
    fun y hy ↦ (hball hy).2.1⟩, fun y hy ↦ (hball hy).2.2⟩

omit [CompleteSpace X] [FiniteDimensional ℝ X] in
/-- Two fields that are continuously differentiable at a point have a common
domain around that point. -/
theorem CommonFlowDomain.nonempty_of_contDiffAt
    {f g : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀)
    (hg : ContDiffAt ℝ 1 g x₀) : Nonempty (CommonFlowDomain f g x₀) := by
  obtain ⟨D, -⟩ := CommonFlowDomain.exists_of_contDiffAt_of_eventually hf hg
    (Filter.Eventually.of_forall fun _ ↦ True.intro)
  exact ⟨D⟩

/-- Spatial differentiability of the fixed chosen flow holds on a product
neighbourhood of time zero and the base point. -/
theorem eventually_differentiableAt_localFlow_spatial
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ p : ℝ × X in 𝓝 (0, x₀),
      DifferentiableAt ℝ (localFlow hf p.1) p.2 := by
  obtain ⟨D⟩ := CommonFlowDomain.nonempty_of_contDiffAt hf hf
  obtain ⟨T, hT, r, hr, hmain⟩ := uniformDifferentiability_onBox D
  filter_upwards [prod_mem_nhds (Ioo_mem_nhds (neg_neg_of_pos hT) hT)
    (ball_mem_nhds x₀ hr)] with p hp
  exact hmain p.2 hp.2 p.1 (abs_lt.mpr hp.1)

omit [FiniteDimensional ℝ X] in
/-- The time derivative identity of the fixed chosen flow holds on a product
neighbourhood of time zero and the base point. -/
theorem eventually_hasDerivAt_localFlow_time
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ p : ℝ × X in 𝓝 (0, x₀),
      HasDerivAt (fun t ↦ localFlow hf t p.2)
        (f (localFlow hf p.1 p.2)) p.1 := by
  let d := getLocalFlowData hf
  filter_upwards [prod_mem_nhds (Ioo_mem_nhds (neg_neg_of_pos d.hε) d.hε)
    (closedBall_mem_nhds x₀ d.hr)] with p hp
  exact d.ϕ_hasDerivAt p.1 hp.1 p.2 hp.2

/-- If the bracket vanishes on a common domain, the derivative of its chosen
flow preserves the second field on one smaller time and space box. -/
theorem uniform_fderiv_localFlow_apply_onBox
    {f g : X → X} {x₀ : X} (D : CommonFlowDomain f g x₀)
    (hbr : ∀ y ∈ closedBall x₀ D.r, lieBracket f g y = 0) :
    ∃ T > 0, ∃ r > 0, ∀ y ∈ ball x₀ r, ∀ t : ℝ, |t| < T →
      fderiv ℝ (localFlow D.hf0 t) y (g y) = g (localFlow D.hf0 t y) := by
  obtain ⟨T₁, hT₁, r₁, hr₁, htrans⟩ := uniformTransport_onBox D
  obtain ⟨T₂, hT₂, r₂, hr₂, hinv⟩ := uniformInvertibility_onBox D
  obtain ⟨T₃, hT₃, r₃, hr₃, hstay⟩ := uniformFlowInvariance D
  let T := min T₁ (min T₂ T₃)
  let r := min r₁ (min r₂ (min r₃ (localFlowRadius D.hf0)))
  have hT : 0 < T := lt_min hT₁ (lt_min hT₂ hT₃)
  have hr : 0 < r := lt_min hr₁ (lt_min hr₂ (lt_min hr₃ (getLocalFlowData D.hf0).hr))
  have hTle : T ≤ T₁ ∧ T ≤ T₂ ∧ T ≤ T₃ := by
    dsimp [T]
    exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  have hrle : r ≤ r₁ ∧ r ≤ r₂ ∧ r ≤ r₃ ∧ r ≤ localFlowRadius D.hf0 := by
    dsimp [r]
    exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  refine ⟨T, hT, r, hr, fun y hy t ht ↦ ?_⟩
  have hy₁ := ball_subset_ball hrle.1 hy
  have hy₂ := ball_subset_ball hrle.2.1 hy
  have hy₃ := ball_subset_ball hrle.2.2.1 hy
  have hyr := ball_subset_ball hrle.2.2.2 hy
  have hderiv : ∀ u ∈ Ioo (-T) T,
      HasDerivAt (fun v ↦ VectorField.pullback ℝ (localFlow D.hf0 v) g y) 0 u := by
    intro u hu
    have hu' : |u| < T := abs_lt.mpr hu
    have hz : lieBracket f g (localFlow D.hf0 u y) = 0 :=
      hbr _ (hstay u (hu'.trans_le hTle.2.2) y hy₃).1
    simpa [VectorField.pullback, hz] using htrans y hy₁ u (hu'.trans_le hTle.1)
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun u hu ↦ (hderiv u hu).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ (hderiv u hu).deriv) (abs_lt.mp ht)
    (show (0 : ℝ) ∈ Ioo (-T) T from ⟨neg_neg_of_pos hT, hT⟩)
  have hzero : VectorField.pullback ℝ (localFlow D.hf0 0) g y = g y := by
    simp only [VectorField.pullback, flow_deriv_zero_of_mem_ball f x₀ D.hf0 hyr,
      ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply]
    congr 1
    exact (getLocalFlowData D.hf0).ϕ_zero y (ball_subset_closedBall hyr)
  rw [hzero] at hconst
  have hinvertible : (fderiv ℝ (localFlow D.hf0 t) y).IsInvertible := by
    obtain ⟨u, hu⟩ := hinv y hy₂ t (ht.trans_le hTle.2.1)
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ X u, hu⟩
  rw [← VectorField.fderiv_pullback (𝕜 := ℝ) (localFlow D.hf0 t) g y hinvertible,
    hconst]

/-- Commuting fields are preserved by the derivative of the fixed local flow,
uniformly for time and initial state near the base point. -/
theorem eventually_fderiv_localFlow_apply
    {f g : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀)
    (hg : ContDiffAt ℝ 1 g x₀) (hbr : ∀ᶠ y in 𝓝 x₀, lieBracket f g y = 0) :
    ∀ᶠ p : ℝ × X in 𝓝 (0, x₀),
      fderiv ℝ (localFlow hf p.1) p.2 (g p.2) = g (localFlow hf p.1 p.2) := by
  obtain ⟨D, hD⟩ := CommonFlowDomain.exists_of_contDiffAt_of_eventually hf hg hbr
  obtain ⟨T, hT, r, hr, hmain⟩ := uniform_fderiv_localFlow_apply_onBox D hD
  filter_upwards [prod_mem_nhds (Ioo_mem_nhds (neg_neg_of_pos hT) hT)
    (ball_mem_nhds x₀ hr)] with p hp
  exact hmain p.2 hp.2 p.1 (abs_lt.mpr hp.1)
