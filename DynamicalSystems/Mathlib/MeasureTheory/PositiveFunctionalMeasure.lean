/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Positive continuous functionals on a compact space as finite measures -/

@[expose] public section

open Set MeasureTheory
open scoped CompactlySupported

namespace PositiveFunctional

variable {τ : Type*} [TopologicalSpace τ] [CompactSpace τ] [T2Space τ]
  [MeasurableSpace τ] [BorelSpace τ]

/-- Restrict a positive functional to compactly supported continuous functions. -/
def toCompactlySupported (Λ : C(τ, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ g, 0 ≤ g → 0 ≤ Λ g) : C_c(τ, ℝ) →ₚ[ℝ] ℝ where
  toFun f := Λ f.toContinuousMap
  map_add' f g := by exact map_add Λ _ _
  map_smul' c f := by exact map_smul Λ _ _
  monotone' := by
    intro f g hfg
    have h := hΛ (g.toContinuousMap - f.toContinuousMap) (sub_nonneg.mpr hfg)
    simpa only [map_sub, sub_nonneg] using h

/-- The representing measure is constructed, not supplied. -/
noncomputable def measure (Λ : C(τ, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ g, 0 ≤ g → 0 ≤ Λ g) : Measure τ :=
  RealRMK.rieszMeasure (toCompactlySupported Λ hΛ)

instance (Λ : C(τ, ℝ) →L[ℝ] ℝ) (hΛ : ∀ g, 0 ≤ g → 0 ≤ Λ g) :
    IsFiniteMeasure (measure Λ hΛ) := by
  unfold measure RealRMK.rieszMeasure
  infer_instance

/-- Riesz representation for every continuous real function on the compact domain. -/
theorem integral_eq (Λ : C(τ, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ g, 0 ≤ g → 0 ≤ Λ g) (g : C(τ, ℝ)) :
    (∫ t, g t ∂measure Λ hΛ) = Λ g := by
  let gc : C_c(τ, ℝ) := ⟨g, HasCompactSupport.of_compactSpace _⟩
  exact RealRMK.integral_rieszMeasure (toCompactlySupported Λ hΛ) gc

/-- No nonzero functional is lost in passing to its representing measure. -/
theorem ne_zero_of_ne_zero (Λ : C(τ, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ g, 0 ≤ g → 0 ≤ Λ g) (hne : Λ ≠ 0) : measure Λ hΛ ≠ 0 := by
  intro hμ
  apply hne
  ext g
  have h := integral_eq Λ hΛ g
  rw [hμ, integral_zero_measure] at h
  exact h.symm

end PositiveFunctional
