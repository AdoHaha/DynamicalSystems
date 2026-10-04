/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform first-order remainders near a continuously differentiable point

On a finite-dimensional domain, continuous differentiability near a point gives a
first-order Taylor remainder estimate uniform in the expansion point on a smaller
ball. The proof uses uniform continuity of the derivative on a compact ball and
the mean value inequality on the intersection of two balls.

This is the local uniform remainder used in proofs of differentiable dependence
of ODE solutions on their initial conditions; see Hartman, *Ordinary Differential
Equations*, Chapter V.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A continuously differentiable function on a finite-dimensional domain has a
first-order remainder, uniform in both points on a fixed neighborhood. The
neighborhood is independent of the requested error coefficient. -/
theorem ContDiffAt.exists_uniform_fderiv_remainder {f : X → Y} {x₀ : X}
    (hf : ContDiffAt ℝ 1 f x₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ v ∈ ball x₀ r, ∀ w ∈ ball x₀ r, dist v w < δ →
        ‖f v - f w - (fderiv ℝ f w) (v - w)‖ ≤ η * ‖v - w‖ := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hf.eventually (by simp))
  have hreg : ∀ z ∈ ball x₀ R, ContDiffAt ℝ 1 f z := fun z hz ↦ hball hz
  have hC : ContDiffOn ℝ 1 f (ball x₀ R) :=
    fun z hz ↦ (hreg z hz).contDiffWithinAt
  have hsub : closedBall x₀ (R / 2) ⊆ ball x₀ R :=
    closedBall_subset_ball (half_lt_self hR)
  have hU : UniformContinuousOn (fderiv ℝ f) (closedBall x₀ (R / 2)) :=
    (isCompact_closedBall x₀ (R / 2)).uniformContinuousOn_of_continuous
      ((hC.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono hsub)
  refine ⟨R / 2, half_pos hR, ?_⟩
  intro η hη
  obtain ⟨δ, hδ, hδspec⟩ := Metric.uniformContinuousOn_iff.mp hU η hη
  refine ⟨δ, hδ, ?_⟩
  intro v hv w hw hvw
  let s := ball x₀ (R / 2) ∩ ball w δ
  have hs : Convex ℝ s := (convex_ball _ _).inter (convex_ball _ _)
  have hd : ∀ z ∈ s, DifferentiableAt ℝ f z := by
    intro z hz
    exact (hreg z (hsub (ball_subset_closedBall hz.1))).differentiableAt_one
  have hb : ∀ z ∈ s, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ η := by
    intro z hz
    simpa only [dist_eq_norm] using
      (hδspec z (ball_subset_closedBall hz.1) w (ball_subset_closedBall hw) hz.2).le
  exact hs.norm_image_sub_le_of_norm_fderiv_le' hd hb
    ⟨hw, mem_ball_self hδ⟩ ⟨hv, hvw⟩
