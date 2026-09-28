/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.TransferPoleDomains
public import DynamicalSystems.Linear.TransferPoleControllerCriterion

/-! # Transfer-pole stability with well-posed feedthrough

The pole criterion applies to any well-posed dynamic interconnection, including
nonzero plant control feedthrough `D` and measurement disturbance feedthrough
`F`. The effective disturbance map is `disturbanceMapWithF`, not the zero-`F`
map. This module does not identify the resulting existence condition with the
zero-feedthrough geometric conditions of Corollary 6.22.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

universe u

namespace LinearSystem

variable {X U Y W D Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- For a well-posed interconnection, poles in an arbitrary domain are
equivalent to spectral inclusion for the minimal realization of its *total*
disturbance-to-controlled-output channel. -/
theorem DynamicInterconnection.externalPolesIn_iff_minimalSpectrum
    (ic : DynamicInterconnection ℝ X U Y W D Z) (hwp : ic.IsWellPosed)
    (Cg : Set ℂ) :
    MinimalRealizationAllChannelsPolesIn Cg
        (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap ↔
      ∀ z : ℂ,
        (Polynomial.map (algebraMap ℝ ℂ)
          (LinearMap.controllableObservableRealization
            (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap 0).A.charpoly
        ).IsRoot z → z ∈ Cg :=
  minimalRealizationAllChannelsPolesIn_iff_spectrum Cg
    (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap

/-- In the Hurwitz domain, poles of the well-posed interconnection's total
disturbance channel lie in the left half-plane exactly when its external impulse
response decays in every disturbance direction. -/
theorem DynamicInterconnection.externalPolesIn_leftHalfPlane_iff_response_tendsto
    (ic : DynamicInterconnection ℝ X U Y W D Z) (hwp : ic.IsWellPosed) :
    MinimalRealizationAllChannelsPolesIn {z : ℂ | z.re < 0}
        (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap ↔
      ∀ d : D, Tendsto (fun t : ℝ ↦ ic.externalResponse hwp t d) atTop (nhds 0) := by
  have hp := controllableObservableRealization_all_channels_poleStable_iff_channelReadout_tendsto
    (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap
  have heq : MinimalRealizationAllChannelsPolesIn {z : ℂ | z.re < 0}
        (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap ↔
      minimalRealizationAllChannelsPoleStable
        (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap := by
    rfl
  rw [heq, hp]
  apply forall_congr'
  intro d
  have hfun : (fun t : ℝ ↦ ic.externalResponse hwp t d) =
      fun t : ℝ ↦ ic.outputMap
        (NormedSpace.exp (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
          (ic.disturbanceMapWithF hwp d)) := by
    funext t
    rw [ic.externalResponse_apply hwp t d, ic.closedLoopSystem_expFlow_eq hwp t]
  rw [hfun]

/-- An arbitrary finite-dimensional dynamic controller is well posed with the
plant and places every pole of the total external transfer channel in `Cg`.
Both plant feedthrough `D` and measurement disturbance feedthrough `F` are
allowed. -/
def AnyStateWellPosedExternalPolesIn (Cg : Set ℂ) (sys : LinearSystem ℝ X U Y)
    (E : D →ₗ[ℝ] X) (F : D →ₗ[ℝ] Y) (H : X →ₗ[ℝ] Z) : Prop :=
  ∃ (V : Type u) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V)
      (_ : FiniteDimensional ℝ V),
    ∃ ctrl : DynamicController ℝ V Y U,
      let ic : DynamicInterconnection ℝ X U Y V D Z := ⟨sys, ctrl, E, F, H⟩
      ∃ hwp : ic.IsWellPosed,
        MinimalRealizationAllChannelsPolesIn Cg
          (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap

/-- An arbitrary finite-dimensional dynamic controller is well posed with the
plant and gives a decaying external impulse response for the total disturbance
channel. -/
def AnyStateWellPosedStableExternalResponse (sys : LinearSystem ℝ X U Y)
    (E : D →ₗ[ℝ] X) (F : D →ₗ[ℝ] Y) (H : X →ₗ[ℝ] Z) : Prop :=
  ∃ (V : Type u) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V)
      (_ : FiniteDimensional ℝ V),
    ∃ ctrl : DynamicController ℝ V Y U,
      let ic : DynamicInterconnection ℝ X U Y V D Z := ⟨sys, ctrl, E, F, H⟩
      ∃ hwp : ic.IsWellPosed,
        ∀ d : D, Tendsto (fun t : ℝ ↦ ic.externalResponse hwp t d) atTop (nhds 0)

/-- The Hurwitz-domain pole criterion and response decay agree even with
nonzero feedthrough, provided the controller interconnection is well posed. -/
theorem anyStateWellPosedExternalPolesIn_leftHalfPlane_iff_stableExternalResponse
    (sys : LinearSystem ℝ X U Y) (E : D →ₗ[ℝ] X)
    (F : D →ₗ[ℝ] Y) (H : X →ₗ[ℝ] Z) :
    AnyStateWellPosedExternalPolesIn {z : ℂ | z.re < 0} sys E F H ↔
      AnyStateWellPosedStableExternalResponse sys E F H := by
  constructor
  · rintro ⟨V, hV1, hV2, hV3, ctrl, hwp, hpole⟩
    letI : NormedAddCommGroup V := hV1
    letI : NormedSpace ℝ V := hV2
    letI : FiniteDimensional ℝ V := hV3
    exact ⟨V, hV1, hV2, hV3, ctrl, hwp,
      (DynamicInterconnection.externalPolesIn_leftHalfPlane_iff_response_tendsto
        (⟨sys, ctrl, E, F, H⟩ : DynamicInterconnection ℝ X U Y V D Z) hwp).mp hpole⟩
  · rintro ⟨V, hV1, hV2, hV3, ctrl, hwp, hdec⟩
    letI : NormedAddCommGroup V := hV1
    letI : NormedSpace ℝ V := hV2
    letI : FiniteDimensional ℝ V := hV3
    exact ⟨V, hV1, hV2, hV3, ctrl, hwp,
      (DynamicInterconnection.externalPolesIn_leftHalfPlane_iff_response_tendsto
        (⟨sys, ctrl, E, F, H⟩ : DynamicInterconnection ℝ X U Y V D Z) hwp).mpr hdec⟩

/-- The well-posed feedthrough predicate conservatively extends the previous
strictly proper, zero-measurement-disturbance pole criterion. -/
theorem anyStateWellPosedExternalPolesIn_zero_iff_anyStatePoleStableExternalResponse
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    AnyStateWellPosedExternalPolesIn {z : ℂ | z.re < 0} sys E 0 H ↔
      AnyStatePoleStableExternalResponse sys hD E H := by
  constructor
  · rintro ⟨V, hV1, hV2, hV3, ctrl, hwp, hpole⟩
    letI : NormedAddCommGroup V := hV1
    letI : NormedSpace ℝ V := hV2
    letI : FiniteDimensional ℝ V := hV3
    let ic : DynamicInterconnection ℝ X U Y V D Z := ⟨sys, ctrl, E, 0, H⟩
    have hpole' : minimalRealizationAllChannelsPoleStable
        (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap := hpole
    rw [ic.disturbanceMapWithF_of_F_eq_zero hwp rfl] at hpole'
    exact ⟨V, hV1, hV2, hV3, ctrl, hpole'⟩
  · rintro ⟨V, hV1, hV2, hV3, ctrl, hpole⟩
    letI : NormedAddCommGroup V := hV1
    letI : NormedSpace ℝ V := hV2
    letI : FiniteDimensional ℝ V := hV3
    let ic : DynamicInterconnection ℝ X U Y V D Z := ⟨sys, ctrl, E, 0, H⟩
    let hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
    have hpole' : minimalRealizationAllChannelsPoleStable
        (ic.closedLoopMap hwp) ic.disturbanceMap ic.outputMap := hpole
    rw [← ic.disturbanceMapWithF_of_F_eq_zero hwp rfl] at hpole'
    exact ⟨V, hV1, hV2, hV3, ctrl, hwp, hpole'⟩

end LinearSystem
