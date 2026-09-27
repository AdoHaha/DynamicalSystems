/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.RealBohlTransport

/-! # Necessity of stable nonzero dynamic external-response control

For a strictly proper finite-dimensional real plant, a stable dynamic external
response transposes to a stable response of the dual plant. Applying the
real-coordinate finite-Bohl necessity bridge on both sides establishes the
geometric conditions of Corollary 6.22 for the repository's controller class
with state space equal to the plant state space; the existing observer
construction supplies the converse. Arbitrary controller state spaces are not
covered by this module.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LinearSystem

section DualBridge

variable {X U Y D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

local instance : IsTopologicalRing
    (Module.Dual ℝ (X × X) →L[ℝ] Module.Dual ℝ (X × X)) :=
  { continuous_add := continuous_add
    continuous_mul := Continuous.clm_comp continuous_fst continuous_snd
    continuous_neg := continuous_neg }

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] in
/-- The dual cab-pair external response is the transposed readout of the primal
closed-loop channel. -/
lemma dualExternalResponse_eq_transposedReadout
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (ctrl : DynamicController ℝ X Y U) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (t : ℝ) (z : Module.Dual ℝ Z) :
    (cabPairInterconnection_dual sys ctrl E H).externalResponse
      ((cabPairInterconnection_dual sys ctrl E H).isWellPosed_of_D_eq_zero
        (dual_D_eq_zero sys hD)) t z =
      ((cabPairInterconnection sys ctrl E H).disturbanceMapWithF
          ((cabPairInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD)).dualMap
        (NormedSpace.exp (t • ((cabPairInterconnection sys ctrl E H).closedLoopMap
          ((cabPairInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero
            hD)).dualMap.toContinuousLinearMap)
          ((cabPairInterconnection sys ctrl E H).outputMap.dualMap z)) := by
  let ic := cabPairInterconnection sys ctrl E H
  let icD := cabPairInterconnection_dual sys ctrl E H
  let hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
  let hwpD : icD.IsWellPosed := icD.isWellPosed_of_D_eq_zero (dual_D_eq_zero sys hD)
  let T := ic.closedLoopMap hwp
  let Ee := ic.disturbanceMapWithF hwp
  let q : Module.Dual ℝ X × Module.Dual ℝ X := (H.dualMap z, 0)
  have hEe : Ee = ic.disturbanceMap := by
    exact ic.disturbanceMapWithF_of_F_eq_zero hwp (by simp [ic, cabPairInterconnection])
  have hq : prodDualEquiv (X := X) q = ic.outputMap.dualMap z := by
    apply LinearMap.ext
    intro p
    rcases p with ⟨x, w⟩
    simp [q, ic, cabPairInterconnection, prodDualEquiv, Module.dualProdDualEquivDual_apply,
      LinearMap.coprod_apply, LinearMap.dualMap_apply]
  have hprod : prodDualEquiv (X := X)
      (NormedSpace.exp (t • (icD.closedLoopMap hwpD).toContinuousLinearMap) q) =
      NormedSpace.exp (t • T.dualMap.toContinuousLinearMap) (prodDualEquiv (X := X) q) := by
    simpa [icD, ic, hwpD, hwp, T, q] using
      (prodDualEquiv_closedLoop_exp_apply sys hD ctrl E H t q)
  have hEeq : ∀ r : Module.Dual ℝ X × Module.Dual ℝ X,
      Ee.dualMap (prodDualEquiv (X := X) r) = E.dualMap r.1 := by
    intro r
    apply LinearMap.ext
    intro d
    simp [Ee, hEe, ic, cabPairInterconnection, prodDualEquiv,
      LinearMap.dualMap_apply, add_zero]
  calc
    icD.externalResponse hwpD t z
        = icD.outputMap (NormedSpace.exp (t • (icD.closedLoopMap hwpD).toContinuousLinearMap)
            (icD.disturbanceMapWithF hwpD z)) := by
              rw [icD.externalResponse_apply hwpD t z, icD.closedLoopSystem_expFlow_eq hwpD t]
        _ = icD.outputMap (NormedSpace.exp (t • (icD.closedLoopMap hwpD).toContinuousLinearMap)
            (icD.disturbanceMap z)) := by
              rw [icD.disturbanceMapWithF_of_F_eq_zero hwpD
                (by simp [icD, cabPairInterconnection_dual])]
        _ = icD.outputMap
            (NormedSpace.exp (t • (icD.closedLoopMap hwpD).toContinuousLinearMap) q) := by
              rw [icD.disturbanceMap_apply]
              rfl
        _ = E.dualMap
            (NormedSpace.exp (t • (icD.closedLoopMap hwpD).toContinuousLinearMap) q).1 := by
              rw [icD.outputMap_apply]
              rfl
        _ = Ee.dualMap
            (NormedSpace.exp (t • T.dualMap.toContinuousLinearMap) (ic.outputMap.dualMap z)) := by
              rw [← hEeq]
              rw [hprod, hq]

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] in
/-- **The dual stable-nonzero external-response bridge.** A stable nonzero
external response of the primal strictly proper plant transposes to a stable
nonzero external response of the dual plant, realized by the transposed
controller. -/
theorem stableNonzeroExternalResponse_dual
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : StableNonzeroExternalResponse sys hD E H) :
    StableNonzeroExternalResponse sys.dual (dual_D_eq_zero sys hD) H.dualMap E.dualMap := by
  obtain ⟨ctrl, hdec⟩ := h
  refine ⟨ctrl.dual, ?_⟩
  intro z
  let ic := cabPairInterconnection sys ctrl E H
  let icD := cabPairInterconnection_dual sys ctrl E H
  let hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
  let hwpD : icD.IsWellPosed := icD.isWellPosed_of_D_eq_zero (dual_D_eq_zero sys hD)
  change Filter.Tendsto (fun t : ℝ => icD.externalResponse hwpD t z) Filter.atTop (nhds 0)
  have hdec' : ∀ d : D, Filter.Tendsto
      (fun t : ℝ => ic.outputMap (NormedSpace.exp
        (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
        (ic.disturbanceMapWithF hwp d))) Filter.atTop (nhds 0) := by
    intro d
    have hfun : (fun t : ℝ => ic.externalResponse hwp t d) =
        fun t : ℝ => ic.outputMap (NormedSpace.exp
          (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
          (ic.disturbanceMapWithF hwp d)) := by
      funext t
      rw [ic.externalResponse_apply hwp t d, ic.closedLoopSystem_expFlow_eq hwp t]
    rw [← hfun]
    simpa [ic, hwp] using hdec d
  have htrans := dualReadout_tendsto_of_readout_tendsto
    (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap hdec'
  have hfun : (fun t : ℝ => icD.externalResponse hwpD t z) =
      fun t : ℝ => (ic.disturbanceMapWithF hwp).dualMap
        (NormedSpace.exp (t • (ic.closedLoopMap hwp).dualMap.toContinuousLinearMap)
          (ic.outputMap.dualMap z)) := by
    funext t
    exact dualExternalResponse_eq_transposedReadout sys hD ctrl E H t z
  rw [hfun]
  exact htrans z

/-- **Necessity for the fixed-state stable-nonzero criterion.** The
first geometric inclusion is the real finite-Bohl first-inclusion theorem
applied to the dual plant, using the dual response bridge above; the second
inclusion follows from the transposed-`W_g` assembly in `RealBohlTransport`. -/
theorem externalStabilizationConditions_of_stableNonzeroExternalResponse
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : StableNonzeroExternalResponse sys hD E H) :
    ExternalStabilizationConditions sys E H := by
  have hdual : StableNonzeroExternalResponse sys.dual (dual_D_eq_zero sys hD)
      H.dualMap E.dualMap :=
    stableNonzeroExternalResponse_dual sys hD E H h
  have hdualRange : LinearMap.range H.dualMap ≤
      outputStabilizableSubspace sys.A.dualMap sys.C.dualMap E.dualMap := by
    simpa [dual_A, dual_B] using
      (range_E_le_outputStabilizableSubspace_of_stableNonzeroExternalResponse
        (sys := sys.dual) (hD := dual_D_eq_zero sys hD) (E := H.dualMap) (H := E.dualMap)
        hdual)
  exact externalStabilizationConditions_of_stableNonzeroExternalResponse_of_dualRange
    sys hD E H h hdualRange

/-- **Stable-nonzero equivalence for controllers with state space `X`.**
Necessity is the dual bridge above; sufficiency is the observer-based
controller of the geometric conditions. The book's arbitrary-controller-state
quantifier is not part of `StableNonzeroExternalResponse`. -/
theorem stableNonzeroExternalResponse_iff_externalStabilizationConditions
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    StableNonzeroExternalResponse sys hD E H ↔ ExternalStabilizationConditions sys E H := by
  constructor
  · exact externalStabilizationConditions_of_stableNonzeroExternalResponse sys hD E H
  · intro hc
    exact stableNonzeroExternalResponse_of_externalStabilizationConditions sys hD E H hc

end DualBridge

end LinearSystem
