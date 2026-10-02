/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.Basic
public import DynamicalSystems.Control.SlidingMode.Filippov
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Sign
public import Mathlib.Topology.Order.OrderClosed

/-! # The relay feedback and its Filippov convexification

This file records the scalar relay feedback

`relay k s = k * Real.sign s`

of G. Bartolini, L. Fridman, A. Pisano and E. Usai (eds.), *Modern Sliding Mode
Control Theory: New Perspectives and Applications*, LNCIS 375, Springer 2008
(Chapter 4, A. Levant and L. Alelishvili, *Discontinuous Homogeneous Control*,
Section 2, printed pp. 73–75): the relay is bounded and discontinuous exactly on
the switching level `s = 0`, and its Filippov convexification there is the
classical input interval `[-k, k]`. Off the switching level it is locally
constant, hence its Filippov set is the singleton of its value.

The last statement, `relay_tangent_selection`, is the equivalent-control
selection on the switching surface: among the control values in the
convexified relay range `[-k, k]` the only one for which the affine sliding
dynamics `σ̇ = a + b u` vanishes is `u = -a / b`, precisely the equivalent
control of `DynamicalSystems.Control.SlidingMode.Basic`.

## Main definitions

* `relay k`: the scalar relay `s ↦ k * sign s`.

## Main statements

* `filippovSet_relay_zero`: for `k > 0` the Filippov set of the relay at the
  switching level `0` is the interval `[-k, k]`.
* `filippovSet_relay_ne`: off the switching level the relay is continuous and its
  Filippov set is the singleton `{relay k s}`.
* `relay_tangent_selection`: on the switching surface the only control value in
  `[-k, k]` that zeroes `σ̇ = a + b u` is the equivalent control `-a / b`.
* `relay_tangent_selection_unique`: its uniqueness half, reusing
  `equivalentControl_unique` of `DynamicalSystems.Control.SlidingMode.Basic`.
-/

@[expose] public section

open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scalar relay `s ↦ k * sign s`. It is the elementary discontinuous
feedback of the sliding-mode setting: it saturates at `±k` away from the
switching level and is zero there. -/
noncomputable def relay (k : ℝ) : ℝ → ℝ := fun s ↦ k * Real.sign s

/-- The pointwise unfolding of `relay` (a `simp` lemma). -/
@[simp] theorem relay_apply (k s : ℝ) : relay k s = k * Real.sign s := rfl

/-- Local form of `filippovSet_of_continuous`: if a vector field `f` is continuous
at `x` then the Filippov convexification at `x` is the singleton `{f x}`. This is
the germ-local refinement needed when the field is continuous only off a switching
level. -/
theorem filippovSet_of_continuousAt {f : E → E} {x : E} (hf : ContinuousAt f x) :
    filippovSet f x = {f x} := by
  apply Set.Subset.antisymm
  · intro y hy
    rw [Set.mem_singleton_iff]
    apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨δ, hδ0, hδ⟩ := (Metric.continuousAt_iff.mp hf) ε hε
    have hsubset : f '' Metric.ball x δ ⊆ Metric.ball (f x) ε := by
      rintro _ ⟨z, hz, rfl⟩
      exact hδ hz
    have hball : convexHull ℝ (f '' Metric.ball x δ) ⊆ Metric.closedBall (f x) ε := by
      calc convexHull ℝ (f '' Metric.ball x δ)
          ⊆ convexHull ℝ (Metric.ball (f x) ε) := convexHull_mono hsubset
        _ = Metric.ball (f x) ε := (convex_ball (f x) ε).convexHull_eq
        _ ⊆ Metric.closedBall (f x) ε := Metric.ball_subset_closedBall
    have hyδ : y ∈ closure (convexHull ℝ (f '' Metric.ball x δ)) := by
      rw [filippovSet] at hy
      exact mem_iInter.mp (mem_iInter.mp hy δ) hδ0
    exact closure_minimal hball Metric.isClosed_closedBall hyδ
  · rintro y rfl
    rw [filippovSet]
    refine mem_iInter.mpr fun δ ↦ mem_iInter.mpr fun hδ ↦ ?_
    exact subset_closure
      (subset_convexHull ℝ (f '' Metric.ball x δ) (mem_image_of_mem f (Metric.mem_ball_self hδ)))

/-- The relay is continuous at every nonzero point: it is locally constant there.
This is the key fact making its Filippov set off the switching level a singleton. -/
theorem continuousAt_relay (k : ℝ) {s : ℝ} (hs : s ≠ 0) : ContinuousAt (relay k) s := by
  have hconst : relay k =ᶠ[𝓝 s] (fun _ ↦ relay k s) := by
    rcases lt_or_gt_of_ne hs with hsneg | hspos
    · filter_upwards [isOpen_Iio.mem_nhds hsneg] with z hz
      rw [relay_apply, relay_apply, Real.sign_of_neg hz, Real.sign_of_neg hsneg]
    · filter_upwards [isOpen_Ioi.mem_nhds hspos] with z hz
      rw [relay_apply, relay_apply, Real.sign_of_pos hz, Real.sign_of_pos hspos]
  exact (continuousAt_const (x := s) (y := relay k s)).congr hconst.symm

/-- Off the switching level the relay is continuous, so its Filippov
convexification is the singleton of its value there. -/
theorem filippovSet_relay_ne {k : ℝ} {s : ℝ} (hs : s ≠ 0) :
    filippovSet (relay k) s = {relay k s} :=
  filippovSet_of_continuousAt (continuousAt_relay k hs)

/-- The image of a ball about `0` under the relay is the three-point set
`{-k, 0, k}`, because the sign function only takes the values `-1`, `0` and `1`
(and each is attained, for `δ > 0`). -/
theorem relay_image_ball (k δ : ℝ) (hδ : 0 < δ) :
    relay k '' Metric.ball (0 : ℝ) δ = ({-k, 0, k} : Set ℝ) := by
  ext y
  constructor
  · rintro ⟨z, _, rfl⟩
    rcases Real.sign_apply_eq z with h | h | h
    · left
      rw [relay_apply, h, mul_neg, mul_one]
    · right; left
      rw [relay_apply, h, mul_zero]
    · right; right
      rw [relay_apply, h, mul_one]
      rfl
  · intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · refine ⟨-δ / 2, ?_, ?_⟩
      · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
        constructor <;> linarith
      · rw [relay_apply, Real.sign_of_neg (by linarith : -δ / 2 < 0), mul_neg, mul_one]
    · exact ⟨0, Metric.mem_ball_self hδ, by rw [relay_apply, Real.sign_zero, mul_zero]⟩
    · refine ⟨δ / 2, ?_, ?_⟩
      · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
        constructor <;> linarith
      · rw [relay_apply, Real.sign_of_pos (by linarith : 0 < δ / 2), mul_one]

/-- The convex hull of the three-point set `{-k, 0, k}` is the interval
`[-k, k]` (for `k ≥ 0`). -/
theorem convexHull_relay_three {k : ℝ} (hk : 0 ≤ k) :
    convexHull ℝ ({-k, 0, k} : Set ℝ) = Set.Icc (-k) k := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_Icc _ _)
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [Set.mem_Icc]; exact ⟨le_rfl, by linarith⟩
    · rw [Set.mem_Icc]; exact ⟨by linarith, hk⟩
    · rw [Set.mem_Icc]; exact ⟨by linarith, le_rfl⟩
  · intro y hy
    rw [Set.mem_Icc] at hy
    rcases le_total 0 y with hy0 | hy0
    · have hyc : y ∈ convexHull ℝ ({0, k} : Set ℝ) := by
        rw [convexHull_pair, segment_eq_Icc hk]
        exact ⟨hy0, hy.2⟩
      exact convexHull_mono (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto) hyc
    · have hyc : y ∈ convexHull ℝ ({-k, 0} : Set ℝ) := by
        rw [convexHull_pair, segment_eq_Icc (by linarith : -k ≤ 0)]
        exact ⟨hy.1, hy0⟩
      exact convexHull_mono (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto) hyc

/-- At the switching level the relay's Filippov set is the classic input interval
`[-k, k]` (for `k > 0`): the image of every ball about `0` is exactly
`{-k, 0, k}`, whose convex hull is `[-k, k]`, closed. -/
theorem filippovSet_relay_zero {k : ℝ} (hk : 0 < k) :
    filippovSet (relay k) 0 = Set.Icc (-k) k := by
  have hterm : ∀ δ, 0 < δ →
      closure (convexHull ℝ (relay k '' Metric.ball (0 : ℝ) δ)) = Set.Icc (-k) k := by
    intro δ hδ
    rw [relay_image_ball k δ hδ, convexHull_relay_three hk.le, closure_Icc]
  rw [filippovSet]
  ext y
  simp only [Set.mem_iInter, Set.mem_Ioi]
  constructor
  · intro hy
    exact (hterm 1 one_pos) ▸ hy 1 one_pos
  · intro hy δ hδ
    rwa [hterm δ hδ]

/-- The equivalent control of `DynamicalSystems.Control.SlidingMode.Basic`,
specialized to the scalar affine sliding dynamics `σ̇ = a + b u` (output
`σ = id`), is `-a / b`. This identifies the selection of
`relay_tangent_selection` with the equivalent control. -/
theorem equivalentControl_relay_eq {a b : ℝ} :
    equivalentControl (fun y : ℝ ↦ y) (fun _ ↦ a) (fun _ ↦ b) 0 = -a / b := by
  simp only [equivalentControl, slidingDerivative, fderiv_fun_id, ContinuousLinearMap.id_apply]

/-- The uniqueness half of the tangent selection, phrased through
`equivalentControl_unique`: a control value `u` that zeroes the affine sliding
dynamics `a + b u = 0` must be the equivalent control `-a / b`. -/
theorem relay_tangent_selection_unique {a b u : ℝ} (hb : b ≠ 0) (hu : a + b * u = 0) :
    u = -a / b := by
  have hb' : slidingDerivative (fun y : ℝ ↦ y) (fun _ ↦ b) 0 ≠ 0 := by
    simpa only [slidingDerivative, fderiv_fun_id, ContinuousLinearMap.id_apply] using hb
  have hu' : slidingDerivative (fun y : ℝ ↦ y) (fun _ ↦ a) 0
      + u * slidingDerivative (fun y : ℝ ↦ y) (fun _ ↦ b) 0 = 0 := by
    have h1 : slidingDerivative (fun y : ℝ ↦ y) (fun _ ↦ a) 0 = a := by
      simp only [slidingDerivative, fderiv_fun_id, ContinuousLinearMap.id_apply]
    have h2 : slidingDerivative (fun y : ℝ ↦ y) (fun _ ↦ b) 0 = b := by
      simp only [slidingDerivative, fderiv_fun_id, ContinuousLinearMap.id_apply]
    rw [h1, h2, mul_comm u b]
    exact hu
  calc u = equivalentControl (fun y : ℝ ↦ y) (fun _ ↦ a) (fun _ ↦ b) 0 :=
        equivalentControl_unique _ _ _ u 0 hb' hu'
    _ = -a / b := equivalentControl_relay_eq

/-- **Equivalent-control tangent selection.** On the switching surface, the only
control value in the convexified relay range `[-k, k]` that keeps the affine
sliding dynamics `σ̇ = a + b u = 0` is the equivalent control `-a / b`, whenever
it lies in range (`|a / b| ≤ k`). -/
theorem relay_tangent_selection {a b k : ℝ} (hb : b ≠ 0) (hab : |a / b| ≤ k) :
    {u ∈ Set.Icc (-k) k | a + b * u = 0} = {-a / b} := by
  ext u
  rw [Set.mem_sep_iff, Set.mem_Icc, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨-, -⟩, hzero⟩
    exact relay_tangent_selection_unique hb hzero
  · rintro rfl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have habs := abs_le.mp hab
      rw [neg_div b a]
      linarith [habs.2]
    · have habs := abs_le.mp hab
      rw [neg_div b a]
      linarith [habs.1]
    · rw [neg_div b a, mul_neg, mul_div_cancel₀ a hb]
      ring
