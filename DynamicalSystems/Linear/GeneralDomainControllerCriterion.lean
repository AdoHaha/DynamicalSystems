/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GeneralDomainNecessity
public import DynamicalSystems.Linear.GeneralDomainObserverGain

/-! # General-domain external-stabilization criterion

The stable-nonzero geometric criterion of Trentelman–Stoorvogel–Hautus,
Corollary 6.22, is expressed for an arbitrary real-conjugation-invariant
stability domain. The plant is strictly proper, and the measurement disturbance
feedthrough is zero as in the cited system (6.11).
-/

@[expose] public section

noncomputable section

namespace LinearSystem

universe u

variable {X U Y D Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

omit [FiniteDimensional ℝ U] in
/-- A well-posed finite-dimensional dynamic controller places all external
transfer poles in `Cg` exactly when the two domain-relative geometric
inclusions hold. -/
theorem anyStateWellPosedExternalPolesIn_iff_externalStabilizationConditionsIn
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    AnyStateWellPosedExternalPolesIn Cg sys E 0 H ↔
      ExternalStabilizationConditionsIn Cg sys E H := by
  constructor
  · exact externalStabilizationConditionsIn_of_anyStateWellPosedExternalPolesIn
      Cg hCg sys E H
  · intro h
    obtain ⟨F, hF, hFq⟩ :=
      exists_stateFeedbackQuotientMapIn_isStableIn Cg hCg sys H
    obtain ⟨G, hG, hGq⟩ :=
      exists_observerErrorQuotientMapIn_isStableIn Cg hCg sys E
    exact externalPolesIn_of_geometricQuotientGains
      Cg hCg sys hD E H h F G hF hG hFq hGq

end LinearSystem
