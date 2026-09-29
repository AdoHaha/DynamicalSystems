/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.TransferPoleFeedthrough

/-! # Geometric objects for a general stability domain

Book Definition 2.12 requires a stability domain to meet the real axis and to
be invariant under complex conjugation. The stable and antistable spectral
subspaces below use the existing generalized-eigenspace construction. This
module identifies their Hurwitz specializations; the arbitrary-domain
controller-existence theorem requires further spectral gain construction.
-/

@[expose] public section

noncomputable section

open scoped Matrix

/-- A stability domain in the sense of Trentelman–Stoorvogel–Hautus,
Definition 2.12. -/
def IsStabilityDomain (Cg : Set ℂ) : Prop :=
  (∃ r : ℝ, (r : ℂ) ∈ Cg) ∧ ∀ z : ℂ, z ∈ Cg → star z ∈ Cg

/-- The open left half-plane is a stability domain. -/
theorem leftHalfPlane_isStabilityDomain :
    IsStabilityDomain {z : ℂ | z.re < 0} := by
  refine ⟨⟨-1, by simp⟩, ?_⟩
  intro z hz
  simpa using hz

namespace LinearMap

variable {X U Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]

/-- The real stable spectral subspace selected by `Cg`. -/
def stableSubspaceIn (Cg : Set ℂ) (A : X →ₗ[ℝ] X) : Submodule ℝ X :=
  ((complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A
    (fun μ ↦ μ ∈ Cg)).restrictScalars ℝ).comap
      (ofRealPi.comp (Module.finBasis ℝ X).equivFun.toLinearMap)

/-- The real antistable spectral subspace selected by the complement of `Cg`. -/
def antistableSubspaceIn (Cg : Set ℂ) (A : X →ₗ[ℝ] X) : Submodule ℝ X :=
  ((complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A
    (fun μ ↦ μ ∉ Cg)).restrictScalars ℝ).comap
      (ofRealPi.comp (Module.finBasis ℝ X).equivFun.toLinearMap)

omit [FiniteDimensional ℝ X] in
/-- The selected complex generalized-eigenspace sum is invariant under the
complexified state map, for any spectral predicate. -/
theorem map_complexSpectralSubspaceOfBasis_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ X) (A : X →ₗ[ℝ] X) (q : ℂ → Prop) :
    Submodule.map (Matrix.toLin' ((LinearMap.toMatrix b b A).map (algebraMap ℝ ℂ)))
      (complexSpectralSubspaceOfBasis b A q) ≤
        complexSpectralSubspaceOfBasis b A q := by
  rw [complexSpectralSubspaceOfBasis, Submodule.map_iSup]
  refine iSup_le fun μ ↦ ?_
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  exact Submodule.mem_iSup_of_mem μ
    (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ.1 hy)

/-- The real spectral subspace selected by an arbitrary set of eigenvalues is
invariant under the real state map. -/
theorem map_stableSubspaceIn_le (Cg : Set ℂ) (A : X →ₗ[ℝ] X) :
    Submodule.map A (stableSubspaceIn Cg A) ≤ stableSubspaceIn Cg A := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_comap]
  rw [stableSubspaceIn, Submodule.mem_comap, Submodule.restrictScalars_mem] at hx ⊢
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
    (fun μ ↦ μ ∈ Cg) ⟨_, hx, rfl⟩

/-- For the left half-plane, the general stable subspace is the established
Hurwitz subspace. -/
theorem stableSubspaceIn_leftHalfPlane (A : X →ₗ[ℝ] X) :
    stableSubspaceIn {z : ℂ | z.re < 0} A = hurwitzSubspace A := rfl

/-- For the left half-plane, the general antistable subspace is the
established unstable subspace. -/
theorem antistableSubspaceIn_leftHalfPlane (A : X →ₗ[ℝ] X) :
    antistableSubspaceIn {z : ℂ | z.re < 0} A = unstableSubspace A := rfl

/-- The domain-relative stabilizable subspace is the sum of stable and
reachable states. -/
def stabilizableSubspaceIn (Cg : Set ℂ) (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) :
    Submodule ℝ X :=
  stableSubspaceIn Cg A ⊔ reachableSubspace A B

/-- The domain-relative detectable subspace is the unobservable part of the
antistable state space. -/
def detectableSubspaceIn (Cg : Set ℂ) (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) :
    Submodule ℝ X :=
  unobservableSubspace C A ⊓ antistableSubspaceIn Cg A

theorem stabilizableSubspaceIn_leftHalfPlane (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) :
    stabilizableSubspaceIn {z : ℂ | z.re < 0} A B = stabilizableSubspace A B := rfl

theorem detectableSubspaceIn_leftHalfPlane (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) :
    detectableSubspaceIn {z : ℂ | z.re < 0} C A = detectableSubspace C A := rfl

end LinearMap

namespace LinearSystem

universe u

variable {X U Y D Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The two subspace inclusions of Corollary 6.22 with the stable and
detectable subspaces interpreted relative to `Cg`. -/
def ExternalStabilizationConditionsIn (Cg : Set ℂ) (sys : LinearSystem ℝ X U Y)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) : Prop :=
  LinearMap.range E ≤
      LinearMap.controlledInvariantSubspace sys.A sys.B (LinearMap.ker H) ⊔
        LinearMap.stabilizableSubspaceIn Cg sys.A sys.B ∧
    LinearMap.conditionedInvariantSubspace sys.C sys.A (LinearMap.range E) ⊓
        LinearMap.detectableSubspaceIn Cg sys.C sys.A ≤ LinearMap.ker H

/-- The domain-relative conditions recover the established Hurwitz geometric
conditions definitionally. -/
theorem externalStabilizationConditionsIn_leftHalfPlane
    (sys : LinearSystem ℝ X U Y) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    ExternalStabilizationConditionsIn {z : ℂ | z.re < 0} sys E H ↔
      ExternalStabilizationConditions sys E H := by
  rfl

variable [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]

/-- Enlarging the stability domain preserves a minimal realization's pole
inclusion. -/
theorem minimalRealizationAllChannelsPolesIn_mono {Cg Ch : Set ℂ}
    (hsub : Cg ⊆ Ch) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : MinimalRealizationAllChannelsPolesIn Cg A E H) :
    MinimalRealizationAllChannelsPolesIn Ch A E H := by
  intro i j z hz
  exact hsub (h i j z hz)

/-- Enlarging the stability domain preserves existence of a well-posed
controller with poles in that domain. -/
theorem anyStateWellPosedExternalPolesIn_mono {Cg Ch : Set ℂ}
    (hsub : Cg ⊆ Ch) (sys : LinearSystem ℝ X U Y)
    (E : D →ₗ[ℝ] X) (F : D →ₗ[ℝ] Y) (H : X →ₗ[ℝ] Z)
    (h : AnyStateWellPosedExternalPolesIn Cg sys E F H) :
    AnyStateWellPosedExternalPolesIn Ch sys E F H := by
  obtain ⟨V, hV1, hV2, hV3, ctrl, hwp, hpole⟩ := h
  letI : NormedAddCommGroup V := hV1
  letI : NormedSpace ℝ V := hV2
  letI : FiniteDimensional ℝ V := hV3
  exact ⟨V, hV1, hV2, hV3, ctrl, hwp,
    minimalRealizationAllChannelsPolesIn_mono hsub _ _ _ hpole⟩

variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y]

/-- The domain-parameterized statement recovers the proved Corollary 6.22 iff
at the Hurwitz domain and zero feedthrough. -/
theorem anyStateExternalPolesIn_leftHalfPlane_iff_geometricConditionsIn
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    AnyStateWellPosedExternalPolesIn {z : ℂ | z.re < 0} sys E 0 H ↔
      ExternalStabilizationConditionsIn {z : ℂ | z.re < 0} sys E H :=
  (anyStateWellPosedExternalPolesIn_zero_iff_anyStatePoleStableExternalResponse
    sys hD E H).trans
    ((anyStatePoleStableExternalResponse_iff_externalStabilizationConditions
      sys hD E H).trans
      (externalStabilizationConditionsIn_leftHalfPlane sys E H).symm)

/-- The established Hurwitz geometric conditions suffice for any larger
stability domain, using the same controller. -/
theorem externalPolesIn_of_geometricConditions_of_leftHalfPlane_subset
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (Cg : Set ℂ)
    (hsub : {z : ℂ | z.re < 0} ⊆ Cg)
    (hgeom : ExternalStabilizationConditions sys E H) :
    AnyStateWellPosedExternalPolesIn Cg sys E 0 H := by
  apply anyStateWellPosedExternalPolesIn_mono hsub
  apply (anyStateWellPosedExternalPolesIn_zero_iff_anyStatePoleStableExternalResponse
    sys hD E H).mpr
  exact (anyStatePoleStableExternalResponse_iff_externalStabilizationConditions
    sys hD E H).mpr hgeom

/-- For a smaller stability domain, any controller with poles in that domain
necessarily satisfies the established Hurwitz geometric conditions. -/
theorem geometricConditions_of_externalPolesIn_of_subset_leftHalfPlane
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (Cg : Set ℂ)
    (hsub : Cg ⊆ {z : ℂ | z.re < 0})
    (hpole : AnyStateWellPosedExternalPolesIn Cg sys E 0 H) :
    ExternalStabilizationConditions sys E H := by
  have hh := anyStateWellPosedExternalPolesIn_mono hsub sys E 0 H hpole
  have hbase := (anyStateWellPosedExternalPolesIn_zero_iff_anyStatePoleStableExternalResponse
    sys hD E H).mp hh
  exact (anyStatePoleStableExternalResponse_iff_externalStabilizationConditions
    sys hD E H).mp hbase

end LinearSystem
