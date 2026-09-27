/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GenericControllerDuality

/-! # Explicit dual response for a generic controller state

The channel-level dual response is expressed using the closed-loop exponential
and the two channel maps. This form avoids an elaboration blow-up when the
recursive external-response definition is used directly over dual spaces.
-/

@[expose] public section

open scoped Topology

namespace LinearSystem

variable {X W U Y D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

local instance : IsTopologicalRing
    (Module.Dual ℝ (X × W) →L[ℝ] Module.Dual ℝ (X × W)) :=
  { continuous_add := continuous_add
    continuous_mul := Continuous.clm_comp continuous_fst continuous_snd
    continuous_neg := continuous_neg }

/-- The explicit dual closed-loop readout equals the transpose of the primal
closed-loop disturbance-to-output channel. The interconnections are passed as
typed arguments to keep elaboration bounded. -/
theorem genericW_dualExplicitResponse
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (ctrl : DynamicController ℝ W Y U) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (ic : DynamicInterconnection ℝ X U Y W D Z)
    (icD : DynamicInterconnection ℝ (Module.Dual ℝ X) (Module.Dual ℝ Y)
      (Module.Dual ℝ U) (Module.Dual ℝ W) (Module.Dual ℝ Z) (Module.Dual ℝ D))
    (hic : ic = ⟨sys, ctrl, E, 0, H⟩)
    (hicD : icD = genericDualInterconnection sys ctrl E H)
    (hwp : ic.IsWellPosed) (hwpD : icD.IsWellPosed)
    (t : ℝ) (z : Module.Dual ℝ Z) :
    icD.outputMap
      (NormedSpace.exp (t • (icD.closedLoopMap hwpD).toContinuousLinearMap)
        (icD.disturbanceMap z)) =
      ic.disturbanceMap.dualMap
        (NormedSpace.exp (t • (ic.closedLoopMap hwp).dualMap.toContinuousLinearMap)
          (ic.outputMap.dualMap z)) := by
  subst ic
  subst icD
  let p : Module.Dual ℝ X × Module.Dual ℝ W := (H.dualMap z, 0)
  have hp : prodDualEquivW (X := X) (W := W) p =
      (DynamicInterconnection.mk sys ctrl E 0 H).outputMap.dualMap z := by
    apply LinearMap.ext
    intro q
    rcases q with ⟨x, w⟩
    simp [p, prodDualEquivW, Module.dualProdDualEquivDual_apply,
      LinearMap.coprod_apply, LinearMap.dualMap_apply,
      DynamicInterconnection.outputMap_apply]
  have hExp : prodDualEquivW (X := X) (W := W)
      (NormedSpace.exp (t • ((genericDualInterconnection sys ctrl E H).closedLoopMap
        hwpD).toContinuousLinearMap) p) =
      NormedSpace.exp (t • ((DynamicInterconnection.mk sys ctrl E 0 H).closedLoopMap
        hwp).dualMap.toContinuousLinearMap)
        (prodDualEquivW (X := X) (W := W) p) := by
    simpa only using genericW_closedLoop_exp_apply sys hD ctrl E H t p
  have hE : ∀ q : Module.Dual ℝ X × Module.Dual ℝ W,
      (DynamicInterconnection.mk sys ctrl E 0 H).disturbanceMap.dualMap
        (prodDualEquivW (X := X) (W := W) q) = E.dualMap q.1 := by
    intro q
    apply LinearMap.ext
    intro d
    simp [prodDualEquivW, LinearMap.dualMap_apply,
      DynamicInterconnection.disturbanceMap_apply]
  calc
    (genericDualInterconnection sys ctrl E H).outputMap
        (NormedSpace.exp (t • ((genericDualInterconnection sys ctrl E H).closedLoopMap
          hwpD).toContinuousLinearMap)
          ((genericDualInterconnection sys ctrl E H).disturbanceMap z)) =
        E.dualMap
          (NormedSpace.exp (t • ((genericDualInterconnection sys ctrl E H).closedLoopMap
            hwpD).toContinuousLinearMap) p).1 := by
              simp only [genericDualInterconnection,
                DynamicInterconnection.outputMap_apply,
                DynamicInterconnection.disturbanceMap_apply, p]
    _ = (DynamicInterconnection.mk sys ctrl E 0 H).disturbanceMap.dualMap
          (NormedSpace.exp (t • ((DynamicInterconnection.mk sys ctrl E 0 H).closedLoopMap
            hwp).dualMap.toContinuousLinearMap)
            ((DynamicInterconnection.mk sys ctrl E 0 H).outputMap.dualMap z)) := by
              rw [← hE, hExp, hp]

end LinearSystem

namespace LinearSystem

variable {X W U Y D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The generic first geometric inclusion can be applied when decay is stated
using the explicit closed-loop exponential rather than `externalResponse`. -/
theorem firstInclusion_of_explicitReadout
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (ctrl : DynamicController ℝ W Y U)
    (ic : DynamicInterconnection ℝ X U Y W D Z)
    (hic : ic = genericZeroFInterconnection sys ctrl E H)
    (hwp : ic.IsWellPosed)
    (hdec : ∀ d : D, Filter.Tendsto
      (fun t : ℝ => ic.outputMap
        (NormedSpace.exp (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
          (ic.disturbanceMap d))) Filter.atTop (nhds 0)) :
    LinearMap.range E ≤ outputStabilizableSubspace sys.A sys.B H := by
  subst ic
  apply range_E_le_outputStabilizableSubspace_of_genericStableResponse
    sys hD E H ctrl
  intro d
  convert hdec d using 1
  funext t
  rw [DynamicInterconnection.externalResponse_apply,
    DynamicInterconnection.closedLoopSystem_expFlow_eq]
  rw [DynamicInterconnection.disturbanceMapWithF_of_F_eq_zero]
  rfl

end LinearSystem
