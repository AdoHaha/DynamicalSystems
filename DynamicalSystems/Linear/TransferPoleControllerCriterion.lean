/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.TransferPoleDecay

/-! # Stable transfer poles of arbitrary-order dynamic controllers

For a strictly proper finite-dimensional real plant with zero measurement
disturbance feedthrough, existence of an arbitrary finite-dimensional dynamic
controller whose closed-loop disturbance-to-output transfer matrix has only
left-half-plane poles is equivalent to the Corollary 6.22 geometric conditions.
The proof passes through the time-domain decay criterion. Arbitrary stability
domains are not asserted.
-/

@[expose] public section


open Filter
open scoped Topology

universe u

namespace LinearSystem

noncomputable section

variable {X U Y D Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- There is a finite-dimensional dynamic controller whose well-posed closed-loop
disturbance-to-output channel has stable reduced transfer poles. -/
def AnyStatePoleStableExternalResponse (sys : LinearSystem ℝ X U Y)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) : Prop :=
  ∃ (W : Type u) (_ : NormedAddCommGroup W) (_ : NormedSpace ℝ W)
      (_ : FiniteDimensional ℝ W),
    ∃ ctrl : DynamicController ℝ W Y U,
      let ic := genericZeroFInterconnection sys ctrl E H
      minimalRealizationAllChannelsPoleStable
        (ic.closedLoopMap (ic.isWellPosed_of_D_eq_zero hD))
        ic.disturbanceMap ic.outputMap

/-- For arbitrary finite-dimensional controller state, left-half-plane pole
stability of the closed-loop external transfer is equivalent to decay of its
impulse response. -/
theorem anyStatePoleStableExternalResponse_iff_anyStateStableExternalResponse
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    AnyStatePoleStableExternalResponse sys hD E H ↔
      AnyStateStableExternalResponse sys hD E H := by
  constructor
  · rintro ⟨W, hW1, hW2, hW3, ctrl, hpole⟩
    letI : NormedAddCommGroup W := hW1
    letI : NormedSpace ℝ W := hW2
    letI : FiniteDimensional ℝ W := hW3
    let ic := genericZeroFInterconnection sys ctrl E H
    let hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
    refine ⟨W, hW1, hW2, hW3, ctrl, ?_⟩
    intro d
    have hdec :=
      (controllableObservableRealization_all_channels_poleStable_iff_channelReadout_tendsto
        (ic.closedLoopMap hwp) ic.disturbanceMap ic.outputMap).mp hpole d
    have hfun : (fun t : ℝ => ic.externalResponse hwp t d) =
        fun t : ℝ => ic.outputMap
          (NormedSpace.exp (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
            (ic.disturbanceMap d)) := by
      funext t
      rw [ic.externalResponse_apply hwp t d, ic.closedLoopSystem_expFlow_eq hwp t]
      rw [ic.disturbanceMapWithF_of_F_eq_zero hwp (by rfl)]
    rw [hfun]
    exact hdec
  · rintro ⟨W, hW1, hW2, hW3, ctrl, hdec⟩
    letI : NormedAddCommGroup W := hW1
    letI : NormedSpace ℝ W := hW2
    letI : FiniteDimensional ℝ W := hW3
    let ic := genericZeroFInterconnection sys ctrl E H
    let hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
    refine ⟨W, hW1, hW2, hW3, ctrl, ?_⟩
    apply (controllableObservableRealization_all_channels_poleStable_iff_channelReadout_tendsto
      (ic.closedLoopMap hwp) ic.disturbanceMap ic.outputMap).mpr
    intro d
    have hfun : (fun t : ℝ => ic.externalResponse hwp t d) =
        fun t : ℝ => ic.outputMap
          (NormedSpace.exp (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
            (ic.disturbanceMap d)) := by
      funext t
      rw [ic.externalResponse_apply hwp t d, ic.closedLoopSystem_expFlow_eq hwp t]
      rw [ic.disturbanceMapWithF_of_F_eq_zero hwp (by rfl)]
    rw [← hfun]
    exact hdec d

variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y]

/-- Hurwitz-domain transfer-pole form of the geometric external stabilization
criterion for arbitrary finite-dimensional dynamic controllers. -/
theorem anyStatePoleStableExternalResponse_iff_externalStabilizationConditions
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    AnyStatePoleStableExternalResponse sys hD E H ↔
      ExternalStabilizationConditions sys E H :=
  (anyStatePoleStableExternalResponse_iff_anyStateStableExternalResponse sys hD E H).trans
    (anyStateStableExternalResponse_iff_externalStabilizationConditions sys hD E H)

end

end LinearSystem
