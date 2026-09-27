/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GenericControllerDualResponse

/-! # Stable external response with arbitrary controller state

For a strictly proper finite-dimensional real plant, existence of a dynamic
controller with any finite-dimensional real state space and decaying external
time-domain response is equivalent to the two geometric inclusions of
Corollary 6.22 for the Hurwitz (left-half-plane) stability choice. Equivalence
between this decay predicate and the book's transfer-function stability
predicate, or a formulation for an arbitrary stability domain, is not
established here.
The necessity proof extracts the first inclusion from the plant trajectory
and obtains the second by transposing the explicit closed-loop readout.
-/

@[expose] public section

open Filter
open scoped Topology

universe u

namespace LinearSystem

variable {X U Y D Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- Any finite-dimensional dynamic controller with a decaying external
time-domain response forces both Corollary 6.22 geometric inclusions. The controller state
space is existentially quantified and need not equal the plant state space. -/
theorem externalStabilizationConditions_of_anyStateStableExternalResponse
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : AnyStateStableExternalResponse sys hD E H) :
    ExternalStabilizationConditions sys E H := by
  have hfirst : LinearMap.range E ≤ outputStabilizableSubspace sys.A sys.B H :=
    first_inclusion_of_anyStateStableExternalResponse sys hD E H h
  obtain ⟨W, hW1, hW2, hW3, ctrl, hdec⟩ := h
  letI : NormedAddCommGroup W := hW1
  letI : NormedSpace ℝ W := hW2
  letI : FiniteDimensional ℝ W := hW3
  let ic : DynamicInterconnection ℝ X U Y W D Z :=
    genericZeroFInterconnection sys ctrl E H
  let icD : DynamicInterconnection ℝ (Module.Dual ℝ X) (Module.Dual ℝ Y)
      (Module.Dual ℝ U) (Module.Dual ℝ W) (Module.Dual ℝ Z) (Module.Dual ℝ D) :=
    genericDualInterconnection sys ctrl E H
  let hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
  let hwpD : icD.IsWellPosed := icD.isWellPosed_of_D_eq_zero (dual_D_eq_zero sys hD)
  have hdec' : ∀ d : D, Tendsto
      (fun t : ℝ => ic.outputMap
        (NormedSpace.exp (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
          (ic.disturbanceMap d))) atTop (nhds 0) := by
    intro d
    have hfun : (fun t : ℝ => ic.externalResponse hwp t d) =
        fun t : ℝ => ic.outputMap
          (NormedSpace.exp (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
            (ic.disturbanceMap d)) := by
      funext t
      rw [ic.externalResponse_apply hwp t d, ic.closedLoopSystem_expFlow_eq hwp t]
      rw [ic.disturbanceMapWithF_of_F_eq_zero hwp (by rfl)]
    rw [← hfun]
    simpa [ic, hwp] using hdec d
  have htrans := dualReadout_tendsto_of_readout_tendsto
    (ic.closedLoopMap hwp) ic.disturbanceMap ic.outputMap hdec'
  have hdecD : ∀ z : Module.Dual ℝ Z, Tendsto
      (fun t : ℝ => icD.outputMap
        (NormedSpace.exp (t • (icD.closedLoopMap hwpD).toContinuousLinearMap)
          (icD.disturbanceMap z))) atTop (nhds 0) := by
    intro z
    convert htrans z using 1
    funext t
    exact genericW_dualExplicitResponse sys hD ctrl E H ic icD rfl rfl hwp hwpD t z
  have hdualRange : LinearMap.range H.dualMap ≤
      outputStabilizableSubspace sys.A.dualMap sys.C.dualMap E.dualMap := by
    simpa [dual_A, dual_B] using
      (firstInclusion_of_explicitReadout sys.dual (dual_D_eq_zero sys hD)
        H.dualMap E.dualMap ctrl.dual icD rfl hwpD hdecD)
  exact ⟨hfirst, secondInclusion_of_dual_range_le sys E H hdualRange⟩

/-- The time-domain stable-external-response criterion corresponding to
Corollary 6.22 for arbitrary finite-dimensional controller state and Hurwitz
stability. The transfer-function formulation is not identified with this
predicate. -/
theorem anyStateStableExternalResponse_iff_externalStabilizationConditions
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    AnyStateStableExternalResponse sys hD E H ↔
      ExternalStabilizationConditions sys E H := by
  constructor
  · exact externalStabilizationConditions_of_anyStateStableExternalResponse sys hD E H
  · exact anyStateStableExternalResponse_of_externalStabilizationConditions sys hD E H

end LinearSystem
