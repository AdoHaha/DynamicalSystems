/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Finite measures representing positive continuous functionals

This adapter applies the compactly-supported Riesz--Markov theorem to the
sup-norm space `C(X, ℝ)` on a compact Hausdorff space. The resulting measure is
constructed from the functional; it is not an extra representation hypothesis.
-/

@[expose] public section

open Set MeasureTheory
open scoped CompactlySupported

namespace ContinuousLinearMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- Restriction of a positive continuous functional to compactly supported
continuous functions. -/
noncomputable def positiveOnCompactSupport (q : C(X, ℝ) →L[ℝ] ℝ)
    (hq : ∀ f, 0 ≤ f → 0 ≤ q f) : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toFun f := q f.toContinuousMap
  map_add' f g := by change q (f.toContinuousMap + g.toContinuousMap) = _; exact q.map_add _ _
  map_smul' c f := by change q (c • f.toContinuousMap) = _; exact q.map_smul c _
  monotone' f g hfg := by
    have h := hq (g.toContinuousMap - f.toContinuousMap) (fun x => sub_nonneg.mpr (hfg x))
    simpa only [map_sub, sub_nonneg] using h

/-- The finite nonnegative measure constructed from a positive functional. -/
noncomputable def positiveRepresentingMeasure (q : C(X, ℝ) →L[ℝ] ℝ)
    (hq : ∀ f, 0 ≤ f → 0 ≤ q f) : Measure X :=
  RealRMK.rieszMeasure (q.positiveOnCompactSupport hq)

instance (q : C(X, ℝ) →L[ℝ] ℝ) (hq : ∀ f, 0 ≤ f → 0 ≤ q f) :
    IsFiniteMeasure (q.positiveRepresentingMeasure hq) :=
  inferInstanceAs (IsFiniteMeasure (RealRMK.rieszMeasure (q.positiveOnCompactSupport hq)))

/-- Riesz representation for every continuous function on the compact space. -/
theorem integral_positiveRepresentingMeasure (q : C(X, ℝ) →L[ℝ] ℝ)
    (hq : ∀ f, 0 ≤ f → 0 ≤ q f) (f : C(X, ℝ)) :
    (∫ x, f x ∂q.positiveRepresentingMeasure hq) = q f := by
  let g : C_c(X, ℝ) := ⟨f, HasCompactSupport.of_compactSpace _⟩
  exact RealRMK.integral_rieszMeasure (q.positiveOnCompactSupport hq) g

/-- The representing measure vanishes exactly when the functional vanishes. -/
theorem positiveRepresentingMeasure_ne_zero (q : C(X, ℝ) →L[ℝ] ℝ)
    (hq : ∀ f, 0 ≤ f → 0 ≤ q f) (hne : q ≠ 0) :
    q.positiveRepresentingMeasure hq ≠ 0 := by
  intro hzero
  apply hne
  ext f
  have h := q.integral_positiveRepresentingMeasure hq f
  rw [hzero] at h
  simpa using h.symm

end ContinuousLinearMap
