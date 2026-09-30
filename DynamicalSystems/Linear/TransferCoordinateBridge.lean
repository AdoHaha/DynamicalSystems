/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.MinimalTransferPoles
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Basis

/-! # Coordinate invariance of minimality

Controllability and observability of finite-dimensional real linear maps
transfer to their matrices in finite bases. Input and output coordinate
changes are handled separately from the state-space conjugation.
-/

@[expose] public section


noncomputable section

open LinearMap


namespace LinearMap

variable {𝕜 X U Y U' Y' : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable [AddCommGroup U'] [Module 𝕜 U']
variable [AddCommGroup Y'] [Module 𝕜 Y']

theorem reachableSubspace_comp_equiv (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (e : U' ≃ₗ[𝕜] U) :
    reachableSubspace A (B.comp e.toLinearMap) = reachableSubspace A B := by
  rw [reachableSubspace, reachableSubspace]
  congr 1
  funext k
  apply le_antisymm
  · rintro x ⟨u, rfl⟩
    exact ⟨e u, by simp [LinearMap.comp_apply]⟩
  · rintro x ⟨u, rfl⟩
    obtain ⟨u', rfl⟩ := e.surjective u
    exact ⟨u', by simp [LinearMap.comp_apply]⟩

theorem isControllable_comp_equiv (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (e : U' ≃ₗ[𝕜] U) :
    IsControllable A (B.comp e.toLinearMap) ↔ IsControllable A B := by
  rw [isControllable_iff, isControllable_iff, reachableSubspace_comp_equiv]

theorem unobservableSubspace_comp_equiv (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (e : Y ≃ₗ[𝕜] Y') :
    unobservableSubspace (e.toLinearMap.comp C) A = unobservableSubspace C A := by
  ext x
  rw [mem_unobservableSubspace, mem_unobservableSubspace]
  simp only [LinearMap.comp_apply]
  constructor
  · intro hx k
    have := hx k
    exact e.injective (by simpa using this)
  · intro hx k
    simp [hx k]

theorem isObservable_comp_equiv (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (e : Y ≃ₗ[𝕜] Y') :
    IsObservable (e.toLinearMap.comp C) A ↔ IsObservable C A := by
  rw [isObservable_iff, isObservable_iff, unobservableSubspace_comp_equiv]

end LinearMap

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Y] [Module ℝ Y]
variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

omit [DecidableEq κ] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
theorem toMatrix_mulVecLin_eq_equivFun_conj
    (bX : Module.Basis ι ℝ X) (bY : Module.Basis κ ℝ Y) (f : X →ₗ[ℝ] Y) :
  (LinearMap.toMatrix bX bY f).mulVecLin =
      bY.equivFun.toLinearMap.comp (f.comp bX.equivFun.symm.toLinearMap) := by
  apply DFunLike.ext
  intro v
  funext k
  change ((LinearMap.toMatrix bX bY f) *ᵥ v) k = _
  have h := LinearMap.toMatrix_mulVec_repr (v₁ := bX) (v₂ := bY) f
    (bX.equivFun.symm v)
  calc
    _ = bY.equivFun (f (bX.equivFun.symm v)) k := by
      simpa only [← Module.Basis.equivFun_apply, bX.equivFun.apply_symm_apply] using congrFun h k
    _ = (bY.equivFun.toLinearMap.comp
        (f.comp bX.equivFun.symm.toLinearMap)) v k := rfl

theorem isControllable_toMatrix_mulVecLin
    (A : X →ₗ[ℝ] X) (B : Y →ₗ[ℝ] X) :
    LinearMap.IsControllable A B ↔
      LinearMap.IsControllable
        ((LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A).mulVecLin)
        ((LinearMap.toMatrix (Module.finBasis ℝ Y) (Module.finBasis ℝ X) B).mulVecLin) := by
  let bX := Module.finBasis ℝ X
  let bY := Module.finBasis ℝ Y
  let eX := bX.equivFun
  let eY := bY.equivFun
  have hstate := LinearMap.isControllable_changeState A B eX.symm
  have hinput := LinearMap.isControllable_comp_equiv
    (eX.toLinearMap.comp (A.comp eX.symm.toLinearMap))
    (eX.toLinearMap.comp B) eY.symm
  rw [toMatrix_mulVecLin_eq_equivFun_conj bX bX A,
    toMatrix_mulVecLin_eq_equivFun_conj bY bX B]
  simpa [bX, bY, eX, eY, LinearEquiv.conj_apply, ← LinearMap.comp_assoc] using
    hstate.trans hinput.symm

theorem isObservable_toMatrix_mulVecLin
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) :
    LinearMap.IsObservable C A ↔
      LinearMap.IsObservable
        ((LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ Y) C).mulVecLin)
        ((LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A).mulVecLin) := by
  let bX := Module.finBasis ℝ X
  let bY := Module.finBasis ℝ Y
  let eX := bX.equivFun
  let eY := bY.equivFun
  have hstate := LinearMap.isObservable_changeState C A eX.symm
  have houtput := LinearMap.isObservable_comp_equiv
    (C.comp eX.symm.toLinearMap) (eX.toLinearMap.comp (A.comp eX.symm.toLinearMap)) eY
  rw [toMatrix_mulVecLin_eq_equivFun_conj bX bY C,
    toMatrix_mulVecLin_eq_equivFun_conj bX bX A]
  simpa [bX, bY, eX, eY, LinearEquiv.conj_apply, ← LinearMap.comp_assoc] using
    hstate.trans houtput.symm

end Matrix

namespace LinearSystem

variable {X D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

open Filter
open scoped Topology

/-- Every scalar entry of the complexified transfer matrix of the
controllable–observable realization has its reduced-denominator roots in the
open left half-plane. Coordinates use the fixed finite bases. -/
def minimalRealizationAllChannelsPoleStable
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) : Prop :=
  let S := (LinearMap.reachableSubspace A E) ⧸ LinearMap.reachableIntersection A E H
  let M := LinearMap.controllableObservableRealization A E H 0
  let bS : Module.Basis (Fin (Module.finrank ℝ S)) ℝ S := Module.finBasis ℝ S
  let bD : Module.Basis (Fin (Module.finrank ℝ D)) ℝ D := Module.finBasis ℝ D
  let bZ : Module.Basis (Fin (Module.finrank ℝ Z)) ℝ Z := Module.finBasis ℝ Z
  let AM := M.A.toMatrix bS bS
  let BM := M.B.toMatrix bD bS
  let HM := M.C.toMatrix bS bZ
  ∀ (i : Fin (Module.finrank ℝ Z)) (j : Fin (Module.finrank ℝ D)),
    RatFunc.IsPoleStable (Matrix.channelTransferRatFunc (AM.map (algebraMap ℝ ℂ))
      (fun k ↦ (HM i k : ℂ)) (fun k ↦ (BM k j : ℂ)))

/-- Pole stability of every entry of the minimal realization is equivalent
to Hurwitz stability of its state map. -/
theorem controllableObservableRealization_all_channels_poleStable_iff_hurwitz
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    minimalRealizationAllChannelsPoleStable A E H ↔
      LinearMap.IsHurwitz (LinearMap.controllableObservableRealization A E H 0).A := by
  let S := (LinearMap.reachableSubspace A E) ⧸ LinearMap.reachableIntersection A E H
  let M := LinearMap.controllableObservableRealization A E H 0
  let bS : Module.Basis (Fin (Module.finrank ℝ S)) ℝ S := Module.finBasis ℝ S
  let bD : Module.Basis (Fin (Module.finrank ℝ D)) ℝ D := Module.finBasis ℝ D
  let bZ : Module.Basis (Fin (Module.finrank ℝ Z)) ℝ Z := Module.finBasis ℝ Z
  let AM := M.A.toMatrix bS bS
  let BM := M.B.toMatrix bD bS
  let HM := M.C.toMatrix bS bZ
  have hctrlM : LinearMap.IsControllable M.A M.B := by
    exact LinearMap.isControllable_controllableObservableRealization A E H 0
  have hobsM : LinearMap.IsObservable M.C M.A := by
    exact LinearMap.isObservable_controllableObservableRealization A E H 0
  have hctrl : LinearMap.IsControllable AM.mulVecLin BM.mulVecLin := by
    simpa [AM, BM, bS, bD] using
      (Matrix.isControllable_toMatrix_mulVecLin M.A M.B).mp hctrlM
  have hobs : LinearMap.IsObservable HM.mulVecLin AM.mulVecLin := by
    simpa [AM, HM, bS, bZ] using
      (Matrix.isObservable_toMatrix_mulVecLin M.C M.A).mp hobsM
  have hmatrix := Matrix.real_all_channels_pole_stable_iff_charpoly_hurwitz_of_minimal
    AM BM HM hctrl hobs
  have hchar : (∀ z : ℂ, (AM.charpoly.map (algebraMap ℝ ℂ)).IsRoot z → z.re < 0) ↔
      LinearMap.IsHurwitz M.A := by
    simpa [LinearMap.IsHurwitz, Matrix.charpoly_map, LinearMap.charpoly_toMatrix,
      Polynomial.IsRoot.def, AM, bS]
  change (∀ (i : Fin (Module.finrank ℝ Z)) (j : Fin (Module.finrank ℝ D)),
    RatFunc.IsPoleStable (Matrix.channelTransferRatFunc (AM.map (algebraMap ℝ ℂ))
      (fun k => (HM i k : ℂ)) (fun k => (BM k j : ℂ)))) ↔
    LinearMap.IsHurwitz M.A
  exact hmatrix.trans hchar

end LinearSystem
