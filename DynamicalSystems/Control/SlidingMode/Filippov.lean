/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-! # Filippov convexification of a discontinuous vector field

This file records the differential-inclusion semantics of state-discontinuous
feedback control, as used in the sliding-mode setting of G. Bartolini,
L. Fridman, A. Pisano and E. Usai (eds.), *Modern Sliding Mode Control Theory:
New Perspectives and Applications*, LNCIS 375, Springer 2008. A relay or
bang-bang feedback `u = -k · sign σ` is discontinuous on the switching manifold
`{σ = 0}`, so the closed-loop vector field `f + g u` has no classical solution
across the manifold. Filippov's convention replaces the field at each point by
the closed convex hull of its limiting values on shrinking neighbourhoods, and
asks for a (locally absolutely continuous) curve whose derivative lies in that
set almost everywhere.

The *Filippov set-valued map* (convexification) of a vector field `f` at `x` is

`filippovSet f x = ⋂_{δ > 0} closure (convexHull ℝ (f '' ball x δ))`,

the intersection of the closed convex hulls of the images of shrinking balls.
For a continuous field the shrinking images collapse onto `{f x}` and the
convexification is the singleton `{f x}` (`filippovSet_of_continuous`). For the
scalar relay this recovers the classical interval `[-k, k]` on the switching
level (see `DynamicalSystems.Control.SlidingMode.Relay`).

## Main definitions

* `IsFilippovInclusion F`: a Filippov differential inclusion `ẋ ∈ F x`, namely a
  set-valued map with nonempty, closed, convex values that is locally bounded and
  upper semicontinuous. The upper semicontinuity field is Mathlib's
  `UpperHemicontinuous` (`Mathlib.Topology.Semicontinuity.Hemicontinuity`), which
  characterises exactly the outer/Vietoris condition that every open set
  containing `F x` contains `F y` for `y` near `x`.
* `filippovSet f x`: the Filippov convexification of the field `f` at `x`.
* `filippovSetMeasure f x`: the measure-zero-refined Filippov convexification of
  the field `f` at `x`, where shrinking balls are intersected with the
  complements of arbitrary null sets before convexifying.
* `IsLocallyAbsolutelyContinuousOn γ s`: `γ` is absolutely continuous on every
  closed interval `uIcc a b` contained in `s`.
* `IsFilippovSolutionOn γ F s`: a curve `γ` that is locally absolutely continuous
  on `s` and whose derivative lies in `F (γ t)` for almost every `t ∈ s`.

## Main statements

* `filippovSet_of_continuousAt`: if `f` is continuous at `x`, then
  `filippovSet f x = {f x}`.
* `filippovSet_of_continuous`: for a continuous field `f`, `filippovSet f x = {f x}`.
* `filippovSetMeasure_subset_filippovSet`: the measure-zero-refined Filippov set
  is contained in the plain one.
* `filippovSetMeasure_relay_zero`: at the switching level the measure-zero-refined
  Filippov set of the scalar relay `s ↦ k * sign s` is the interval `[-k, k]`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Filippov differential inclusion `ẋ ∈ F x`: a set-valued map with nonempty,
closed and convex values which is locally bounded and upper semicontinuous. This
is the precise setting in which Filippov solutions of a discontinuous vector
field are studied.

This structure records the standard Filippov regularity of the right-hand side; the
local existence theorem for solutions is proved in
`DynamicalSystems.Control.SlidingMode.FilippovExistence`
(`exists_filippovSolution_local`).  The library does not yet prove that
`filippovSet f` has these properties.  The associated scoped solution concept `IsFilippovSolutionOn` is
built on absolute continuity, so — unlike bare continuity together with
almost-everywhere differentiability — it excludes singular continuous curves
such as the Cantor staircase, in line with the full Filippov theory. -/
structure IsFilippovInclusion (F : E → Set E) : Prop where
  /-- Every value `F x` is nonempty. -/
  nonempty : ∀ x, (F x).Nonempty
  /-- Every value `F x` is closed. -/
  isClosed : ∀ x, IsClosed (F x)
  /-- Every value `F x` is convex. -/
  convex : ∀ x, Convex ℝ (F x)
  /-- `F` is locally bounded: near each point the union of its values is bounded. -/
  locallyBounded : ∀ x, ∃ U ∈ 𝓝 x, Bornology.IsBounded (⋃ y ∈ U, F y)
  /-- `F` is upper semicontinuous. -/
  upperSemicontinuous : UpperHemicontinuous F

/-- The **Filippov set-valued map** (convexification) of a vector field `f` at `x`:
the intersection over all `δ > 0` of the closure of the convex hull of the image
of the open ball of radius `δ` about `x`. This is the closed convex set of
limiting values of `f` near `x` used to define Filippov solutions of a
state-discontinuous feedback. -/
noncomputable def filippovSet (f : E → E) (x : E) : Set E :=
  ⋂ δ ∈ Set.Ioi (0 : ℝ), closure (convexHull ℝ (f '' Metric.ball x δ))

/-- If a vector field `f` is continuous at `x`, then the Filippov convexification
at `x` is the singleton `{f x}`. This is the germ-local form of
`filippovSet_of_continuous`, needed when the field is continuous only off a
switching level: shrinking balls around `x` map into arbitrarily small balls
around `f x`, and the convex hull of a subset of a ball stays in the (convex)
ball. -/
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

/-- For a continuous vector field `f` the Filippov convexification collapses to
the singleton `{f x}`; this is the pointwise specialisation of
`filippovSet_of_continuousAt` to a globally continuous field. -/
theorem filippovSet_of_continuous {f : E → E} (hf : Continuous f) (x : E) :
    filippovSet f x = {f x} :=
  filippovSet_of_continuousAt hf.continuousAt

/-- Local absolute continuity on a set: `γ` is absolutely continuous on every
closed interval `uIcc a b` contained in `s`. This is the curve regularity
required of a Filippov solution; it is stronger than continuity (it excludes the
Cantor staircase) and is exactly the class for which the fundamental theorem of
calculus holds. -/
def IsLocallyAbsolutelyContinuousOn (γ : ℝ → E) (s : Set ℝ) : Prop :=
  ∀ a b, Set.uIcc a b ⊆ s → AbsolutelyContinuousOnInterval γ a b

/-- A Filippov solution of the differential inclusion `ẋ ∈ F x` on the set `s`:
a curve `γ` that is locally absolutely continuous on `s` and whose derivative
lies in `F (γ t)` for almost every `t ∈ s`. This is the solution concept for a
state-discontinuous feedback, whose closed-loop field is replaced by its Filippov
convexification.

The absolute-continuity requirement (rather than mere continuity together with
almost-everywhere differentiability) is what makes the concept match the full
Filippov theory: it excludes singular continuous curves such as the Cantor
staircase, which is continuous with zero derivative almost everywhere but is not
absolutely continuous, and so must not count as a solution of `ẋ ∈ F x` when
`0 ∈ F x`.

Its local existence theorem `exists_filippovSolution_local` is proved in
`DynamicalSystems.Control.SlidingMode.FilippovExistence`. -/
def IsFilippovSolutionOn (γ : ℝ → E) (F : E → Set E) (s : Set ℝ) : Prop :=
  IsLocallyAbsolutelyContinuousOn γ s ∧
    ∀ᵐ t ∂volume.restrict s, HasDerivAt γ (deriv γ t) t ∧ deriv γ t ∈ F (γ t)

section MeasureZeroRefinement

variable [MeasureSpace E]

/-- The **measure-zero-refined Filippov set-valued map** of a vector field `f` at
`x`. Following Shtessel, Edwards, Fridman and Levant, *Sliding Mode Control and
Observation*, Definition 2.3 eq. (2.5), the convexification is formed not merely
from shrinking balls but from shrinking balls with an arbitrary measure-zero set
`N` removed. Explicitly,

`filippovSetMeasure f x
  = ⋂_{δ > 0} ⋂_{μ(N) = 0} closure (convexHull ℝ (f '' (ball x δ \ N)))`.

Since the intersection ranges over all null sets — in particular `N = ∅` — the
measure-zero-refined set is contained in the plain `filippovSet`. This is the
definition under which a vector field may be redefined on an arbitrary null set
without changing its Filippov convexification. -/
noncomputable def filippovSetMeasure (f : E → E) (x : E) : Set E :=
  ⋂ δ ∈ Set.Ioi (0 : ℝ), ⋂ (N : Set E), ⋂ (_ : volume N = 0),
    closure (convexHull ℝ (f '' (Metric.ball x δ \ N)))

/-- The measure-zero-refined Filippov set is contained in the plain Filippov set:
the latter is exactly the term of the intersection indexed by the null set
`N = ∅`. -/
theorem filippovSetMeasure_subset_filippovSet (f : E → E) (x : E) :
    filippovSetMeasure f x ⊆ filippovSet f x := by
  intro y hy
  rw [filippovSet]
  refine mem_iInter.mpr fun δ ↦ mem_iInter.mpr fun hδ ↦ ?_
  have h : y ∈ closure (convexHull ℝ (f '' (Metric.ball x δ \ ∅))) :=
    mem_iInter.mp (mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hy δ) hδ) ∅) measure_empty
  simpa using h

end MeasureZeroRefinement

/-- The measure-zero-refined Filippov set of the scalar relay `s ↦ k * sign s`
(definitionally the relay `DynamicalSystems.Control.SlidingMode.Relay.relay k`)
at the switching level `0` is the classical input interval `[-k, k]` for `k > 0`.
The excision of a null set can never remove the whole positive (nor the whole
negative) half of a ball, so the extreme values `±k` always survive, while the
closed convex hull can never leave `[-k, k]`. -/
theorem filippovSetMeasure_relay_zero {k : ℝ} (hk : 0 < k) :
    filippovSetMeasure (fun s : ℝ ↦ k * Real.sign s) 0 = Set.Icc (-k) k := by
  have hterm : ∀ δ, 0 < δ → ∀ N : Set ℝ, volume N = 0 →
      closure (convexHull ℝ
        ((fun s : ℝ ↦ k * Real.sign s) '' (Metric.ball (0 : ℝ) δ \ N)))
        = Set.Icc (-k) k := by
    intro δ hδ N hN
    apply Set.Subset.antisymm
    · apply closure_minimal
      · apply convexHull_min _ (convex_Icc _ _)
        rintro y ⟨z, -, rfl⟩
        change k * Real.sign z ∈ Set.Icc (-k) k
        rw [Set.mem_Icc]
        rcases Real.sign_apply_eq z with h | h | h
        · rw [h, mul_neg, mul_one]; constructor <;> linarith
        · rw [h, mul_zero]; constructor <;> linarith
        · rw [h, mul_one]; constructor <;> linarith
      · exact isClosed_Icc
    · have hpos : ∃ z ∈ Set.Ioo (0 : ℝ) δ, z ∉ N := by
        by_contra h
        push Not at h
        have hsub : Set.Ioo (0 : ℝ) δ ⊆ N := fun z hz ↦ h z hz
        have hle : volume (Set.Ioo (0 : ℝ) δ) ≤ volume N := measure_mono hsub
        rw [Real.volume_Ioo, hN] at hle
        simp only [sub_zero] at hle
        exact absurd (ENNReal.ofReal_pos.mpr hδ) (not_lt_of_ge hle)
      have hneg : ∃ z ∈ Set.Ioo (-δ) (0 : ℝ), z ∉ N := by
        by_contra h
        push Not at h
        have hsub : Set.Ioo (-δ) (0 : ℝ) ⊆ N := fun z hz ↦ h z hz
        have hle : volume (Set.Ioo (-δ) (0 : ℝ)) ≤ volume N := measure_mono hsub
        rw [Real.volume_Ioo, hN] at hle
        rw [show (0 : ℝ) - -δ = δ by ring] at hle
        exact absurd (ENNReal.ofReal_pos.mpr hδ) (not_lt_of_ge hle)
      obtain ⟨zp, hzp, hzpN⟩ := hpos
      obtain ⟨zn, hzn, hznN⟩ := hneg
      have hk_mem : k ∈ convexHull ℝ
          ((fun s : ℝ ↦ k * Real.sign s) '' (Metric.ball (0 : ℝ) δ \ N)) := by
        refine subset_convexHull ℝ _ ⟨zp, ⟨?_, hzpN⟩, ?_⟩
        · rw [Real.ball_eq_Ioo]
          constructor <;> linarith [hzp.1, hzp.2]
        · change k * Real.sign zp = k
          rw [Real.sign_of_pos hzp.1, mul_one]
      have hneg_mem : -k ∈ convexHull ℝ
          ((fun s : ℝ ↦ k * Real.sign s) '' (Metric.ball (0 : ℝ) δ \ N)) := by
        refine subset_convexHull ℝ _ ⟨zn, ⟨?_, hznN⟩, ?_⟩
        · rw [Real.ball_eq_Ioo]
          constructor <;> linarith [hzn.1, hzn.2]
        · change k * Real.sign zn = -k
          rw [Real.sign_of_neg hzn.2, mul_neg, mul_one]
      rintro y hy
      have hseg : convexHull ℝ ({-k, k} : Set ℝ) ⊆ convexHull ℝ
          ((fun s : ℝ ↦ k * Real.sign s) '' (Metric.ball (0 : ℝ) δ \ N)) :=
        convexHull_min (by
          intro w hw
          rcases hw with rfl | rfl
          · exact hneg_mem
          · exact hk_mem) (convex_convexHull ℝ _)
      have hyc : y ∈ convexHull ℝ ({-k, k} : Set ℝ) := by
        rw [convexHull_pair, segment_eq_Icc (by linarith : -k ≤ k)]
        exact hy
      exact subset_closure (hseg hyc)
  rw [filippovSetMeasure]
  ext y
  simp only [Set.mem_iInter, Set.mem_Ioi]
  constructor
  · intro hy
    exact (hterm 1 one_pos ∅ measure_empty) ▸ hy 1 one_pos ∅ measure_empty
  · intro hy δ hδ N hN
    rw [hterm δ hδ N hN]
    exact hy
