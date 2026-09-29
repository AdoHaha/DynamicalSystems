/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GeneralStabilityDomain

/-! # Extended invariant pair for a general stability domain

The algebraic part of Trentelman–Stoorvogel–Hautus Lemma 6.21 does not
depend on the shape of the stability domain. The two domain-relative geometric
subspaces give a nested invariant pair for the observer-based closed loop.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace LinearMap

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup Y] [Module ℝ Y]

/-- The domain-relative antistable spectral subspace is invariant under the
plant state map. -/
theorem map_antistableSubspaceIn_le (Cg : Set ℂ) (A : X →ₗ[ℝ] X) :
    Submodule.map A (antistableSubspaceIn Cg A) ≤ antistableSubspaceIn Cg A := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_comap]
  rw [antistableSubspaceIn, Submodule.mem_comap, Submodule.restrictScalars_mem] at hx ⊢
  have hcoord : (Module.finBasis ℝ X).equivFun (A x) =
      (LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A) *ᵥ
        ((Module.finBasis ℝ X).equivFun x) := by
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact (LinearMap.toMatrix_mulVec_repr (Module.finBasis ℝ X)
      (Module.finBasis ℝ X) A x).symm
  change ofRealPi ((Module.finBasis ℝ X).equivFun (A x)) ∈ _
  rw [hcoord, ofRealPi_mulVec]
  rw [← Matrix.toLin'_apply]
  exact map_complexSpectralSubspaceOfBasis_le (Module.finBasis ℝ X) A
    (fun μ ↦ μ ∉ Cg) ⟨_, hx, rfl⟩

/-- The domain-relative detectable subspace is invariant under the plant. -/
theorem map_detectableSubspaceIn_le (Cg : Set ℂ)
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) :
    Submodule.map A (detectableSubspaceIn Cg C A) ≤ detectableSubspaceIn Cg C A := by
  rw [detectableSubspaceIn]
  exact le_trans (Submodule.map_inf_le A)
    (inf_le_inf (map_unobservableSubspace_le C A) (map_antistableSubspaceIn_le Cg A))

/-- The intersection of a conditioned-invariant subspace and the
domain-relative detectable subspace is plant-invariant. -/
theorem map_conditionedInvariant_inf_detectableSubspaceIn_le
    {D : Type*} [AddCommGroup D] [Module ℝ D]
    (Cg : Set ℂ) (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) :
    Submodule.map A
      (conditionedInvariantSubspace C A (LinearMap.range E) ⊓
        detectableSubspaceIn Cg C A) ≤
      conditionedInvariantSubspace C A (LinearMap.range E) ⊓
        detectableSubspaceIn Cg C A := by
  let S := conditionedInvariantSubspace C A (LinearMap.range E)
  let T := S ⊓ detectableSubspaceIn Cg C A
  have hTker : T ≤ LinearMap.ker C :=
    inf_le_right.trans (inf_le_left.trans (unobservableSubspace_le_ker C A))
  have hS : IsConditionedInvariant C A S :=
    isConditionedInvariant_conditionedInvariantSubspace C A (LinearMap.range E)
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · exact hS ⟨x, ⟨hx.1, hTker hx⟩, rfl⟩
  · exact map_detectableSubspaceIn_le Cg C A ⟨x, hx.2, rfl⟩

end LinearMap

namespace LinearSystem

universe u

variable {X U Y Z D : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

/-- The domain-relative geometric output-stabilizable subspace. -/
abbrev WIn (Cg : Set ℂ) (sys : LinearSystem ℝ X U Y) (H : X →ₗ[ℝ] Z) :
    Submodule ℝ X :=
  Vstar sys H ⊔ LinearMap.stabilizableSubspaceIn Cg sys.A sys.B

/-- The domain-relative conditioned/detectable intersection. -/
abbrev TIn (Cg : Set ℂ) (sys : LinearSystem ℝ X U Y) (E : D →ₗ[ℝ] X) :
    Submodule ℝ X :=
  Sstar sys E ⊓ LinearMap.detectableSubspaceIn Cg sys.C sys.A

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ D] in
/-- The first geometric condition places the disturbance-generated
conditioned-invariant subspace inside the domain-relative `W`. -/
theorem Sstar_le_WIn_of_externalStabilizationConditionsIn
    (Cg : Set ℂ) (sys : LinearSystem ℝ X U Y)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : ExternalStabilizationConditionsIn Cg sys E H) :
    Sstar sys E ≤ WIn Cg sys H := by
  apply LinearMap.conditionedInvariantSubspace_le h.1
  change Submodule.map sys.A (WIn Cg sys H ⊓ LinearMap.ker sys.C) ≤ WIn Cg sys H
  exact (Submodule.map_mono inf_le_left).trans
    (LinearMap.map_sup_stabilizableSubspaceIn_le Cg sys.A sys.B
      (LinearMap.isControlledInvariant_controlledInvariantSubspace
        sys.A sys.B (LinearMap.ker H)))

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ D] in
/-- Algebraic extended-pair part of book Lemma 6.21 for any stability domain.
The quotient-spectrum step is separate. -/
theorem extendedPairSubspaces_of_externalStabilizationConditionsIn
    (Cg : Set ℂ) (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : ExternalStabilizationConditionsIn Cg sys E H)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X)
    (hF : Submodule.map (sys.A + sys.B.comp F) (Vstar sys H) ≤ Vstar sys H)
    (hG : Submodule.map (sys.A + G.comp sys.C) (Sstar sys E) ≤ Sstar sys E)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G 0) E H).IsWellPosed) :
    let V := Vstar sys H
    let W := WIn Cg sys H
    let S := Sstar sys E
    let T := TIn Cg sys E
    let Vₑ₁ := extendedPairSubspace T V
    let Vₑ₂ := extendedPairSubspace S W
    Vₑ₁ ≤ Vₑ₂ ∧
      Submodule.map
        ((cabPairInterconnection sys (cabPairController sys F G 0) E H).closedLoopMap hwp)
        Vₑ₁ ≤ Vₑ₁ ∧
      Submodule.map
        ((cabPairInterconnection sys (cabPairController sys F G 0) E H).closedLoopMap hwp)
        Vₑ₂ ≤ Vₑ₂ ∧
      LinearMap.range
        (cabPairInterconnection sys (cabPairController sys F G 0) E H).disturbanceMap ≤ Vₑ₂ ∧
      Vₑ₁ ≤ LinearMap.ker
        (cabPairInterconnection sys (cabPairController sys F G 0) E H).outputMap := by
  let V := Vstar sys H
  let W := WIn Cg sys H
  let S := Sstar sys E
  let T := TIn Cg sys E
  have hAT : Submodule.map sys.A T ≤ T :=
    LinearMap.map_conditionedInvariant_inf_detectableSubspaceIn_le Cg sys.C sys.A E
  have hTkerC : T ≤ LinearMap.ker sys.C :=
    inf_le_right.trans (inf_le_left.trans (LinearMap.unobservableSubspace_le_ker sys.C sys.A))
  have hTV : T ≤ V := by
    apply LinearMap.le_controlledInvariantSubspace h.2
    exact hAT.trans le_sup_left
  have hSW : S ≤ W := Sstar_le_WIn_of_externalStabilizationConditionsIn Cg sys E H h
  have hAW : Submodule.map sys.A W ≤ W :=
    LinearMap.map_sup_stabilizableSubspaceIn_le Cg sys.A sys.B
      (LinearMap.isControlledInvariant_controlledInvariantSubspace
        sys.A sys.B (LinearMap.ker H))
  have hASW : Submodule.map sys.A S ≤ W := (Submodule.map_mono hSW).trans hAW
  have hATV : Submodule.map sys.A T ≤ V := hAT.trans hTV
  have hFW : Submodule.map (sys.A + sys.B.comp F) W ≤ W :=
    LinearMap.map_add_feedback_sup_stabilizableSubspaceIn_le Cg sys.A sys.B F hF
  have hGT : Submodule.map (sys.A + G.comp sys.C) T ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have hCx : sys.C x = 0 := LinearMap.mem_ker.mp (hTkerC hx)
    simpa [LinearMap.add_apply, LinearMap.comp_apply, hCx] using hAT ⟨x, hx, rfl⟩
  have hE_S : LinearMap.range E ≤ S :=
    LinearMap.le_conditionedInvariantSubspace sys.C sys.A (LinearMap.range E)
  have hVker : V ≤ LinearMap.ker H :=
    LinearMap.controlledInvariantSubspace_le_K sys.A sys.B (LinearMap.ker H)
  dsimp
  refine ⟨extendedPairSubspace_mono inf_le_left le_sup_left, ?_, ?_, ?_, ?_⟩
  · exact extendedPairSubspace_invariant_cabPairController_zero
      sys hD E H T V F G hTV hATV hF hGT hwp
  · exact extendedPairSubspace_invariant_cabPairController_zero
      sys hD E H S W F G hSW hASW hFW hG hwp
  · exact disturbanceMap_range_le_extendedPairSubspace
      sys (cabPairController sys F G 0) E H S W hE_S
  · exact extendedPairSubspace_le_outputMap_ker
      sys (cabPairController sys F G 0) E H T V h.2 hVker

end LinearSystem
