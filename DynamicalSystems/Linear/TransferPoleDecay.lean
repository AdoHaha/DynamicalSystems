/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.TransferCoordinateBridge
public import DynamicalSystems.Linear.ArbitraryControllerCriterion

/-! # Pole stability and channel-response decay

For a finite-dimensional real input-output channel, all reduced scalar
entries of its controllable–observable realization have left-half-plane
poles exactly when every impulse-response direction decays. This is the
Hurwitz-domain transfer-to-time-domain bridge; arbitrary stability domains
are not encoded by decay.
-/

@[expose] public section

noncomputable section

namespace LinearSystem

universe u

variable {X D Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

open Filter
open scoped Topology

/-- Pole stability of every reduced scalar transfer entry of the minimal
realization is equivalent to decay of the original channel's impulse readout.
The result uses the left-half-plane (Hurwitz) stability domain. -/
theorem controllableObservableRealization_all_channels_poleStable_iff_channelReadout_tendsto
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    minimalRealizationAllChannelsPoleStable A E H ↔
      ∀ d : D, Tendsto
        (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) (E d)))
        atTop (nhds 0) := by
  have hp := controllableObservableRealization_all_channels_poleStable_iff_hurwitz A E H
  have hd := isHurwitz_minimalRealization_iff_channelReadout_tendsto A E H
  exact hp.trans hd

end LinearSystem
