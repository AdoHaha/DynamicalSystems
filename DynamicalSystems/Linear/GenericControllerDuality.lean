/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.ArbitraryControllerResponse

/-! # Closed-loop transpose with generic controller state

The product-dual equivalence identifies the closed-loop operator and its
exponential for an arbitrary finite-dimensional controller state space with
the transposes of the original closed-loop operator and exponential.
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

/-- Identify the product of the plant and controller dual state spaces with
the dual of their product. -/
noncomputable def prodDualEquivW :
    (Module.Dual ℝ X × Module.Dual ℝ W) ≃ₗ[ℝ] Module.Dual ℝ (X × W) :=
  Module.dualProdDualEquivDual ℝ X W

/-- The dual zero-`F` interconnection, with controller state `Module.Dual ℝ W`. -/
noncomputable def genericDualInterconnection (sys : LinearSystem ℝ X U Y)
    (ctrl : DynamicController ℝ W Y U) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    DynamicInterconnection ℝ (Module.Dual ℝ X) (Module.Dual ℝ Y) (Module.Dual ℝ U)
      (Module.Dual ℝ W) (Module.Dual ℝ Z) (Module.Dual ℝ D) :=
  { plant := sys.dual
    controller := ctrl.dual
    E := H.dualMap
    F := 0
    H := E.dualMap }

omit [FiniteDimensional ℝ W] in
/-- The dual closed-loop map is conjugate to the transpose of the primal
closed-loop map under the product-dual equivalence. -/
theorem genericW_closedLoopMap_apply
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (ctrl : DynamicController ℝ W Y U) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (p : Module.Dual ℝ X × Module.Dual ℝ W) :
    prodDualEquivW (X := X) (W := W)
      ((genericDualInterconnection sys ctrl E H).closedLoopMap
        ((genericDualInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero
          (by change sys.dual.D = 0; exact dual_D_eq_zero sys hD)) p) =
      ((DynamicInterconnection.mk sys ctrl E 0 H).closedLoopMap
        ((DynamicInterconnection.mk sys ctrl E 0 H).isWellPosed_of_D_eq_zero hD)).dualMap
        (prodDualEquivW (X := X) (W := W) p) := by
  let ic : DynamicInterconnection ℝ X U Y W D Z := ⟨sys, ctrl, E, 0, H⟩
  let icD := genericDualInterconnection sys ctrl E H
  let h : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
  have hD' : icD.plant.D = 0 := by
    change sys.dual.D = 0
    exact dual_D_eq_zero sys hD
  let h' : icD.IsWellPosed := icD.isWellPosed_of_D_eq_zero hD'
  change prodDualEquivW (icD.closedLoopMap h' p) =
    (ic.closedLoopMap h).dualMap (prodDualEquivW p)
  rw [icD.closedLoopMap_of_D_eq_zero hD' h' p]
  obtain ⟨ξ, ψ⟩ := p
  apply LinearMap.ext
  intro q
  rcases q with ⟨x, w⟩
  rw [LinearMap.dualMap_apply, ic.closedLoopMap_of_D_eq_zero hD h (x, w)]
  simp only [prodDualEquivW, Module.dualProdDualEquivDual_apply,
    LinearMap.coprod_apply, LinearMap.add_apply, LinearMap.comp_apply,
    DynamicController.dual_K, DynamicController.dual_L, DynamicController.dual_M,
    DynamicController.dual_N, LinearMap.dualMap_comp_dualMap,
    LinearMap.dualMap_apply, map_add, icD, genericDualInterconnection,
    LinearSystem.dual, ic, LinearMap.add_apply, LinearMap.comp_apply]
  abel

local instance : IsTopologicalRing
    (Module.Dual ℝ (X × W) →L[ℝ] Module.Dual ℝ (X × W)) :=
  { continuous_add := continuous_add
    continuous_mul := Continuous.clm_comp continuous_fst continuous_snd
    continuous_neg := continuous_neg }

set_option synthInstance.maxHeartbeats 1000000 in
-- Elaborating the conjugated operator exponential needs extra instance-search time.
/-- The closed-loop exponential obeys the same product-dual conjugacy. -/
theorem genericW_closedLoop_exp_apply
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (ctrl : DynamicController ℝ W Y U) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (t : ℝ) (p : Module.Dual ℝ X × Module.Dual ℝ W) :
    prodDualEquivW (X := X) (W := W)
      (NormedSpace.exp (t • ((genericDualInterconnection sys ctrl E H).closedLoopMap
        ((genericDualInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero
          (dual_D_eq_zero sys hD))).toContinuousLinearMap) p) =
      NormedSpace.exp (t • (((DynamicInterconnection.mk sys ctrl E 0 H).closedLoopMap
        ((DynamicInterconnection.mk sys ctrl E 0 H).isWellPosed_of_D_eq_zero
          hD)).dualMap).toContinuousLinearMap)
        (prodDualEquivW (X := X) (W := W) p) := by
  let L := (prodDualEquivW (X := X) (W := W)).toContinuousLinearEquiv
  let ic : DynamicInterconnection ℝ X U Y W D Z := ⟨sys, ctrl, E, 0, H⟩
  let icD := genericDualInterconnection sys ctrl E H
  let A := (icD.closedLoopMap
    (icD.isWellPosed_of_D_eq_zero (dual_D_eq_zero sys hD))).toContinuousLinearMap
  let B := ((ic.closedLoopMap (ic.isWellPosed_of_D_eq_zero hD)).dualMap).toContinuousLinearMap
  have hconj : L.conjContinuousAlgEquiv A = B := by
    apply ContinuousLinearMap.ext
    intro q
    change L (A (L.symm q)) = B q
    simpa [L, A, B, ic, icD, genericDualInterconnection] using
      genericW_closedLoopMap_apply sys hD ctrl E H (L.symm q)
  have key := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (L.conjContinuousAlgEquiv)
    (L.conjContinuousAlgEquiv).continuous (t • A)
    ((NormedSpace.expSeries_radius_eq_top ℝ
      (Module.Dual ℝ X × Module.Dual ℝ W →L[ℝ]
        Module.Dual ℝ X × Module.Dual ℝ W)).symm ▸ edist_lt_top _ _)
  have hsmul : L.conjContinuousAlgEquiv (t • A) = t • B := by rw [map_smul, hconj]
  rw [hsmul] at key
  have happ := congrArg (fun f : _ => f (L p)) key
  simpa [L, A, B, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply] using happ

end LinearSystem
