/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.Rectification
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # Existence of the linear tangent equation

The coefficient `Df (localFlow hf t x₀)` is continuous on a neighborhood of zero.
Picard--Lindelöf therefore supplies an operator-valued solution of the tangent
equation with initial value the identity. This construction uses only time
regularity of the existing flow; it does not assume differentiability of the
flow with respect to its initial point.

The identification of the constructed solution with the spatial derivative is
a separate argument. None of the results in this file assume that identification.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous family of bounded linear operators admits a local solution
through any initial value. Continuity is required only on a neighborhood of
the initial time, and no finite-dimensionality assumption is needed. -/
theorem ContinuousOn.exists_local_linearODE_solution
    {A : ℝ → E →L[ℝ] E} {s : Set ℝ}
    (hA : ContinuousOn A s) (hs : s ∈ 𝓝 (0 : ℝ)) (y₀ : E) :
    ∃ δ > (0 : ℝ), ∃ y : ℝ → E,
      y 0 = y₀ ∧ ∀ t, |t| < δ → HasDerivAt y (A t (y t)) t := by
  obtain ⟨ε, hε, hεs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hs
  have hAc : ContinuousOn A (closedBall (0 : ℝ) ε) := hA.mono hεs
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ) ε).exists_bound_of_continuousOn hAc
  have hC₀ : 0 ≤ C :=
    (norm_nonneg (A 0)).trans (hC 0 (mem_closedBall_self hε.le))
  let L : ℝ := C * (1 + ‖y₀‖) + 1
  have hL : 0 < L := by dsimp [L]; positivity
  let δ : ℝ := min ε (1 / L)
  have hδ : 0 < δ := lt_min hε (one_div_pos.mpr hL)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδL : L * δ ≤ 1 := by
    have h := min_le_right ε (1 / L)
    change δ ≤ 1 / L at h
    have h' := (le_div_iff₀ hL).mp h
    simpa only [mul_comm] using h'
  have htime : Icc (-δ) δ ⊆ closedBall (0 : ℝ) ε := by
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_0_eq_abs]
    exact (abs_le.mpr ht).trans hδε
  have hnorm : ∀ y ∈ closedBall y₀ (1 : ℝ), ‖y‖ ≤ 1 + ‖y₀‖ := by
    intro y hy
    calc
      ‖y‖ ≤ ‖y - y₀‖ + ‖y₀‖ := norm_le_norm_sub_add y y₀
      _ ≤ 1 + ‖y₀‖ := by linarith [mem_closedBall_iff_norm.mp hy]
  have hpl : IsPicardLindelof (fun t y ↦ A t y)
      (tmin := -δ) (tmax := δ)
      ⟨0, ⟨by linarith, hδ.le⟩⟩ y₀ 1 0 ⟨L, hL.le⟩ ⟨C, hC₀⟩ := by
    constructor
    · intro t ht
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le
        (f := A t) (K := ⟨C, hC₀⟩) (hC t (htime ht))).lipschitzOnWith
    · intro y _hy
      exact (hAc.mono htime).clm_apply continuousOn_const
    · intro t ht y hy
      calc
        ‖A t y‖ ≤ ‖A t‖ * ‖y‖ := (A t).le_opNorm y
        _ ≤ C * (1 + ‖y₀‖) :=
          mul_le_mul (hC t (htime ht)) (hnorm y hy) (norm_nonneg _) hC₀
        _ ≤ L := by dsimp [L]; linarith
    · change L * max (δ - 0) (0 - -δ) ≤ (1 : ℝ) - 0
      simpa only [sub_zero, zero_sub, neg_neg, max_self] using hδL
  obtain ⟨y, hy₀, hy⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨δ, hδ, y, hy₀, ?_⟩
  intro t ht
  have ht' : t ∈ Ioo (-δ) δ := abs_lt.mp ht
  exact (hy t (Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The coefficients of the tangent equation are continuous at every sufficiently
small time. This follows from `C¹` regularity of the field and the time derivative
of the already constructed local flow. -/
theorem eventually_continuousAt_fderiv_localFlow
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      ContinuousAt (fun u ↦ fderiv ℝ f (localFlow hf u x₀)) t := by
  let d := getLocalFlowData hf
  have hx₀ : x₀ ∈ closedBall x₀ d.r := mem_closedBall_self d.hr.le
  have hzero : d.ϕ 0 x₀ = x₀ := d.ϕ_zero x₀ hx₀
  have htime : Ioo (-d.ε) d.ε ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [d.hε]) d.hε
  have hzero_mem : (0 : ℝ) ∈ Ioo (-d.ε) d.ε := mem_of_mem_nhds htime
  have htend : Tendsto (fun t ↦ localFlow hf t x₀) (𝓝 (0 : ℝ)) (𝓝 x₀) := by
    have h := (d.ϕ_hasDerivAt 0 hzero_mem x₀ hx₀).continuousAt.tendsto
    rw [hzero] at h
    simpa only [localFlow, d] using h
  filter_upwards [htime, htend.eventually (hf.eventually (by simp))] with t ht hft
  apply (hft.continuousAt_fderiv (by simp)).comp
    (f := fun u : ℝ ↦ localFlow hf u x₀) (x := t)
  simpa only [localFlow, d] using (d.ϕ_hasDerivAt t ht x₀ hx₀).continuousAt

/-- The variational equation along the local flow has a local operator-valued
solution starting from the identity. The theorem constructs a candidate for the
spatial derivative without assuming that the spatial derivative exists. -/
theorem exists_localFlow_tangent_solution
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∃ δ > (0 : ℝ), ∃ J : ℝ → X →L[ℝ] X,
      J 0 = ContinuousLinearMap.id ℝ X ∧
        ∀ t, |t| < δ → HasDerivAt J
          ((fderiv ℝ f (localFlow hf t x₀)).comp (J t)) t := by
  let A : ℝ → X →L[ℝ] X := fun t ↦ fderiv ℝ f (localFlow hf t x₀)
  let s : Set ℝ := {t | ContinuousAt A t}
  have hs : s ∈ 𝓝 (0 : ℝ) := eventually_continuousAt_fderiv_localFlow hf
  have hA : ContinuousOn A s := fun _ ht ↦ ht.continuousWithinAt
  have hB : ContinuousOn
      (fun t ↦ ContinuousLinearMap.compL ℝ X X X (A t)) s :=
    (ContinuousLinearMap.compL ℝ X X X).continuous.comp_continuousOn hA
  exact hB.exists_local_linearODE_solution hs (ContinuousLinearMap.id ℝ X)
