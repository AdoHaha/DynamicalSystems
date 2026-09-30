/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.TransferCoordinateBridge

/-! # Transfer poles in an arbitrary stability domain

The pole/spectrum correspondence for minimal finite-dimensional realizations is
algebraic and does not depend on the shape of the chosen domain. In particular,
decay is not used here: it is specific to the open left half-plane.
-/

@[expose] public section

noncomputable section

namespace RatFunc

/-- All roots of the reduced transfer denominator belong to `Cg`. -/
def HasPolesIn (Cg : Set ℂ) (f : RatFunc ℂ) : Prop :=
  ∀ z : ℂ, f.denom.IsRoot z → z ∈ Cg

end RatFunc

namespace Matrix

variable {n m p : Type*} [Fintype n] [DecidableEq n]
variable [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

omit [DecidableEq p] in
/-- A minimal complex realization has all transfer poles in `Cg` precisely
when all roots of its state characteristic polynomial lie in `Cg`. -/
theorem all_channels_poles_in_iff_charpoly_roots_in_of_minimal
    (Cg : Set ℂ) (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix p n ℂ)
    (hctrl : LinearMap.IsControllable A.mulVecLin B.mulVecLin)
    (hobs : LinearMap.IsObservable C.mulVecLin A.mulVecLin) :
    (∀ (i : p) (j : m),
      RatFunc.HasPolesIn Cg (channelTransferRatFunc A (C i) (fun k ↦ B k j))) ↔
      ∀ z : ℂ, A.charpoly.IsRoot z → z ∈ Cg := by
  constructor
  · intro h z hz
    obtain ⟨i, j, hpole⟩ := exists_scalar_transfer_pole_of_minimal A B C
      hctrl hobs z hz
    exact h i j z hpole
  · intro h i j z hz
    exact h z (hz.dvd (channelTransferRatFunc_denom_dvd_charpoly A (C i)
      (fun k ↦ B k j)))

omit [DecidableEq p] in
/-- Real minimal realizations satisfy the same correspondence after
coefficient-wise complexification. -/
theorem real_all_channels_poles_in_iff_charpoly_roots_in_of_minimal
    (Cg : Set ℂ) (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix p n ℝ)
    (hctrl : LinearMap.IsControllable A.mulVecLin B.mulVecLin)
    (hobs : LinearMap.IsObservable C.mulVecLin A.mulVecLin) :
    (∀ (i : p) (j : m),
      RatFunc.HasPolesIn Cg
        (channelTransferRatFunc (A.map (algebraMap ℝ ℂ))
          ((C.map (algebraMap ℝ ℂ)) i)
          (fun k ↦ (B.map (algebraMap ℝ ℂ)) k j))) ↔
      ∀ z : ℂ, (A.charpoly.map (algebraMap ℝ ℂ)).IsRoot z → z ∈ Cg := by
  have hcctrl := (LinearMap.isControllable_complexify_iff A B).mp hctrl
  have hcobs := (LinearMap.isObservable_complexify_iff C A).mp hobs
  have h := all_channels_poles_in_iff_charpoly_roots_in_of_minimal
    Cg (A.map (algebraMap ℝ ℂ)) (B.map (algebraMap ℝ ℂ))
    (C.map (algebraMap ℝ ℂ)) hcctrl hcobs
  simpa only [Matrix.charpoly_map] using h

end Matrix

namespace LinearSystem

variable {X D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- Every scalar entry of the minimal realization's complexified transfer
matrix has its reduced-denominator roots in `Cg`. -/
def MinimalRealizationAllChannelsPolesIn (Cg : Set ℂ)
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
    RatFunc.HasPolesIn Cg (Matrix.channelTransferRatFunc (AM.map (algebraMap ℝ ℂ))
      (fun k ↦ (HM i k : ℂ)) (fun k ↦ (BM k j : ℂ)))

/-- The general-domain pole criterion is exactly the spectral criterion for
the controllable-observable state map. -/
theorem minimalRealizationAllChannelsPolesIn_iff_spectrum
    (Cg : Set ℂ) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    MinimalRealizationAllChannelsPolesIn Cg A E H ↔
      ∀ z : ℂ,
        (Polynomial.map (algebraMap ℝ ℂ)
          (LinearMap.controllableObservableRealization A E H 0).A.charpoly).IsRoot z →
          z ∈ Cg := by
  let S := (LinearMap.reachableSubspace A E) ⧸ LinearMap.reachableIntersection A E H
  let M := LinearMap.controllableObservableRealization A E H 0
  let bS : Module.Basis (Fin (Module.finrank ℝ S)) ℝ S := Module.finBasis ℝ S
  let bD : Module.Basis (Fin (Module.finrank ℝ D)) ℝ D := Module.finBasis ℝ D
  let bZ : Module.Basis (Fin (Module.finrank ℝ Z)) ℝ Z := Module.finBasis ℝ Z
  let AM := M.A.toMatrix bS bS
  let BM := M.B.toMatrix bD bS
  let HM := M.C.toMatrix bS bZ
  have hctrlM : LinearMap.IsControllable M.A M.B :=
    LinearMap.isControllable_controllableObservableRealization A E H 0
  have hobsM : LinearMap.IsObservable M.C M.A :=
    LinearMap.isObservable_controllableObservableRealization A E H 0
  have hctrl : LinearMap.IsControllable AM.mulVecLin BM.mulVecLin := by
    simpa [AM, BM, bS, bD] using
      (Matrix.isControllable_toMatrix_mulVecLin M.A M.B).mp hctrlM
  have hobs : LinearMap.IsObservable HM.mulVecLin AM.mulVecLin := by
    simpa [AM, HM, bS, bZ] using
      (Matrix.isObservable_toMatrix_mulVecLin M.C M.A).mp hobsM
  have hmatrix := Matrix.real_all_channels_poles_in_iff_charpoly_roots_in_of_minimal
    Cg AM BM HM hctrl hobs
  have hchar : AM.charpoly = M.A.charpoly := by
    simpa [AM, bS] using (LinearMap.charpoly_toMatrix bS M.A).symm
  have hrow (i : Fin (Module.finrank ℝ Z)) :
      (HM.map (algebraMap ℝ ℂ)) i = fun k ↦ (HM i k : ℂ) := by
    funext k
    rfl
  have hcol (j : Fin (Module.finrank ℝ D)) :
      (fun k ↦ (BM.map (algebraMap ℝ ℂ)) k j) = fun k ↦ (BM k j : ℂ) := by
    funext k
    rfl
  change (∀ (i : Fin (Module.finrank ℝ Z)) (j : Fin (Module.finrank ℝ D)),
    RatFunc.HasPolesIn Cg (Matrix.channelTransferRatFunc (AM.map (algebraMap ℝ ℂ))
      (fun k ↦ (HM i k : ℂ)) (fun k ↦ (BM k j : ℂ)))) ↔ _
  simpa only [hrow, hcol, hchar, M] using hmatrix

end LinearSystem
