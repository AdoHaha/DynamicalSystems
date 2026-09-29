/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GeneralDomainQuotientFeedback
public import DynamicalSystems.Linear.GeneralDomainExtendedPair
public import DynamicalSystems.Linear.GeneralDomainControllerAssembly
public import DynamicalSystems.Linear.GeneralDomainDuality

/-! # Observer quotient gain for a general stability domain

The observer-side quotient gain is obtained by state feedback on the dual
controlled-invariant quotient and transported back through finite-dimensional
duality.
-/

@[expose] public section

noncomputable section

namespace LinearMap

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- Spectral inclusion is invariant under the duality equivalence for nested
quotients. -/
theorem isStableIn_nestedQuotient_iff_dualNestedQuotientMapInd
    (Cg : Set ℂ) (T : X →ₗ[ℝ] X) {S₁ S₂ : Submodule ℝ X}
    (hS₁S₂ : S₁ ≤ S₂) (hT₁ : S₁ ≤ S₁.comap T) (hT₂ : S₂ ≤ S₂.comap T) :
    IsStableIn Cg (nestedQuotientMap T hT₁ hT₂) ↔
      IsStableIn Cg (dualNestedQuotientMapInd T hS₁S₂ hT₁ hT₂) := by
  rw [← dualNestedQuotientMap_eq_ind T hS₁S₂ hT₁ hT₂]
  rw [dualNestedQuotientMap]
  rw [IsStableIn, IsStableIn]
  rw [LinearEquiv.charpoly_conj]
  rw [charpoly_dualMap_ofField]

lemma isStableIn_nestedQuotientMap_of_isStableIn_mapQ_restrict
    (Cg : Set ℂ) (T : X →ₗ[ℝ] X) {S₁ S₂ : Submodule ℝ X}
    (hT₁ : Submodule.map T S₁ ≤ S₁) (hT₂ : Submodule.map T S₂ ≤ S₂) :
    IsStableIn Cg (Submodule.mapQ (S₁.comap S₂.subtype) (S₁.comap S₂.subtype)
      (T.restrict (fun x hx => hT₂ ⟨x, hx, rfl⟩))
      (fun x hx => hT₁ ⟨(x : X), hx, rfl⟩)) →
    IsStableIn Cg (nestedQuotientMap T
      (Submodule.map_le_iff_le_comap.mp hT₁)
      (Submodule.map_le_iff_le_comap.mp hT₂)) := by
  intro hQ
  have hEq : Submodule.mapQ (S₁.comap S₂.subtype) (S₁.comap S₂.subtype)
      (T.restrict (fun x hx => hT₂ ⟨x, hx, rfl⟩))
      (fun x hx => hT₁ ⟨(x : X), hx, rfl⟩) =
    nestedQuotientMap T
      (Submodule.map_le_iff_le_comap.mp hT₁)
      (Submodule.map_le_iff_le_comap.mp hT₂) := by
    unfold nestedQuotientMap restrictT
    apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on (p := S₁.comap S₂.subtype) q ?_
    intro x
    simp only [Submodule.mapQ_apply]
    congr 1
  rw [← hEq]
  exact hQ

lemma isStableIn_nestedQuotientMap_congr
    (Cg : Set ℂ) (T T' : X →ₗ[ℝ] X) (S₁ S₂ S₁' S₂' : Submodule ℝ X)
    (hT : T = T') (hS₁ : S₁ = S₁') (hS₂ : S₂ = S₂')
    (hT₁ : S₁ ≤ S₁.comap T) (hT₂ : S₂ ≤ S₂.comap T)
    (hT₁' : S₁' ≤ S₁'.comap T') (hT₂' : S₂' ≤ S₂'.comap T') :
    IsStableIn Cg (nestedQuotientMap T hT₁ hT₂) →
    IsStableIn Cg (nestedQuotientMap T' hT₁' hT₂') := by
  intro hQ
  subst T
  subst S₁
  subst S₂
  exact hQ

lemma isStableIn_mapQ_restrict_of_isStableIn_nestedQuotientMap
    (Cg : Set ℂ) (T : X →ₗ[ℝ] X) {S₁ S₂ : Submodule ℝ X}
    (hT₁ : Submodule.map T S₁ ≤ S₁) (hT₂ : Submodule.map T S₂ ≤ S₂) :
    IsStableIn Cg (nestedQuotientMap T
      (Submodule.map_le_iff_le_comap.mp hT₁)
      (Submodule.map_le_iff_le_comap.mp hT₂)) →
    IsStableIn Cg (Submodule.mapQ (S₁.comap S₂.subtype) (S₁.comap S₂.subtype)
      (T.restrict (fun x hx => hT₂ ⟨x, hx, rfl⟩))
      (fun x hx => hT₁ ⟨(x : X), hx, rfl⟩)) := by
  intro hQ
  have hEq : Submodule.mapQ (S₁.comap S₂.subtype) (S₁.comap S₂.subtype)
      (T.restrict (fun x hx => hT₂ ⟨x, hx, rfl⟩))
      (fun x hx => hT₁ ⟨(x : X), hx, rfl⟩) =
    nestedQuotientMap T
      (Submodule.map_le_iff_le_comap.mp hT₁)
      (Submodule.map_le_iff_le_comap.mp hT₂) := by
    unfold nestedQuotientMap restrictT
    apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on (p := S₁.comap S₂.subtype) q ?_
    intro x
    simp only [Submodule.mapQ_apply]
    congr 1
  rw [hEq]
  exact hQ

end LinearMap

namespace LinearSystem

universe u

variable {X U Y D : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ D] in
/-- An output injection preserves the conditioned-invariant subspace and places
all observer-error quotient poles in the chosen stability domain. -/
theorem exists_observerErrorQuotientMapIn_isStableIn
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (sys : LinearSystem ℝ X U Y) (E : D →ₗ[ℝ] X) :
    ∃ G : Y →ₗ[ℝ] X,
      ∃ hG : Submodule.map (sys.A + G.comp sys.C) (Sstar sys E) ≤ Sstar sys E,
        LinearMap.IsStableIn Cg (observerErrorQuotientMapIn Cg sys E G hG) := by
  let Vd : Submodule ℝ (Module.Dual ℝ X) :=
    LinearMap.controlledInvariantSubspace sys.A.dualMap sys.C.dualMap
      (LinearMap.ker E.dualMap)
  let Wd : Submodule ℝ (Module.Dual ℝ X) :=
    Vd ⊔ LinearMap.stabilizableSubspaceIn Cg sys.A.dualMap sys.C.dualMap
  have hVd : Vd = (Sstar sys E).dualAnnihilator := by
    dsimp [Vd, Sstar]
    exact (LinearMap.conditionedInvariantSubspace_dualAnnihilator_eq sys.C sys.A E).symm
  have hWd : Wd = (TIn Cg sys E).dualAnnihilator := by
    dsimp [Wd, Vd, TIn, Sstar]
    exact (LinearMap.conditionedInvariantSubspace_inf_detectableSubspaceIn_dualAnnihilator_eq
      Cg hCg sys.C sys.A E).symm
  obtain ⟨F', ⟨⟨hFV', hQ⟩⟩⟩ :=
    LinearMap.exists_feedback_isStableIn_quotient_of_geometricCondition
      Cg hCg sys.A.dualMap sys.C.dualMap Vd
      (LinearMap.isControlledInvariant_controlledInvariantSubspace
        sys.A.dualMap sys.C.dualMap (LinearMap.ker E.dualMap))
  obtain ⟨G, hGdual⟩ := LinearMap.dualMap_surjective (X := X) (Y := Y) F'
  have hFV : Submodule.map (sys.A.dualMap + sys.C.dualMap.comp G.dualMap) Vd ≤ Vd := by
    simpa only [hGdual] using hFV'
  have hG : Submodule.map (sys.A + G.comp sys.C) (Sstar sys E) ≤ Sstar sys E := by
    simpa only [Sstar] using
      (LinearMap.outputInjection_preserves_conditionedInvariant_of_dual_feedback
        sys.C sys.A E G (by simpa only [Vd] using hFV))
  refine ⟨G, hG, ?_⟩
  let N : X →ₗ[ℝ] X := sys.A + G.comp sys.C
  let S : Submodule ℝ X := Sstar sys E
  let T : Submodule ℝ X := TIn Cg sys E
  have hTS : T ≤ S := inf_le_left
  have hSmap : Submodule.map N S ≤ S := hG
  have hTmap : Submodule.map N T ≤ T := by
    rintro y ⟨x, hx, rfl⟩
    have hCx : sys.C x = 0 := by
      apply LinearMap.mem_ker.mp
      exact (inf_le_right.trans
        (inf_le_left.trans (LinearMap.unobservableSubspace_le_ker sys.C sys.A))) hx
    change N x ∈ T
    have hAx : sys.A x ∈ T :=
      LinearMap.map_conditionedInvariant_inf_detectableSubspaceIn_le Cg sys.C sys.A E
        ⟨x, hx, rfl⟩
    simpa [N, LinearMap.add_apply, LinearMap.comp_apply, hCx] using hAx
  have hWmap :
      Submodule.map (sys.A.dualMap + sys.C.dualMap.comp G.dualMap) Wd ≤ Wd := by
    simpa only [Wd] using
      (LinearMap.map_add_feedback_sup_stabilizableSubspaceIn_le
        Cg sys.A.dualMap sys.C.dualMap G.dualMap hFV)
  have hQ' : LinearMap.IsStableIn Cg
      (Submodule.mapQ (Vd.comap Wd.subtype) (Vd.comap Wd.subtype)
        ((sys.A.dualMap + sys.C.dualMap.comp G.dualMap).restrict
          (fun x hx =>
            LinearMap.map_add_feedback_sup_stabilizableSubspaceIn_le
              Cg sys.A.dualMap sys.C.dualMap G.dualMap hFV ⟨x, hx, rfl⟩))
        (fun x hx => hFV ⟨(x : Module.Dual ℝ X), hx, rfl⟩)) := by
    simpa [Vd, Wd, hGdual] using hQ
  have hNest0 : LinearMap.IsStableIn Cg
      (LinearMap.nestedQuotientMap
        (sys.A.dualMap + sys.C.dualMap.comp G.dualMap)
        (Submodule.map_le_iff_le_comap.mp hFV)
        (Submodule.map_le_iff_le_comap.mp hWmap)) :=
    LinearMap.isStableIn_nestedQuotientMap_of_isStableIn_mapQ_restrict Cg
      (sys.A.dualMap + sys.C.dualMap.comp G.dualMap) hFV hWmap hQ'
  have hNdual : N.dualMap = sys.A.dualMap + sys.C.dualMap.comp G.dualMap := by
    dsimp [N]
    rw [LinearMap.dualMap_add, LinearMap.dualMap_comp_dualMap]
  have hPmap : S.dualAnnihilator ≤ S.dualAnnihilator.comap N.dualMap := by
    intro φ hφ
    exact LinearMap.dualMap_mem_dualAnnihilator
      (Submodule.map_le_iff_le_comap.mp hSmap) hφ
  have hQmap : T.dualAnnihilator ≤ T.dualAnnihilator.comap N.dualMap := by
    intro φ hφ
    exact LinearMap.dualMap_mem_dualAnnihilator
      (Submodule.map_le_iff_le_comap.mp hTmap) hφ
  have hNestDual : LinearMap.IsStableIn Cg
      (LinearMap.nestedQuotientMap N.dualMap hPmap hQmap) :=
    LinearMap.isStableIn_nestedQuotientMap_congr Cg
      (sys.A.dualMap + sys.C.dualMap.comp G.dualMap) N.dualMap
      Vd Wd S.dualAnnihilator T.dualAnnihilator hNdual.symm
      (by simpa only [S] using hVd) (by simpa only [T] using hWd)
      (Submodule.map_le_iff_le_comap.mp hFV)
      (Submodule.map_le_iff_le_comap.mp hWmap) hPmap hQmap hNest0
  have hPQ : S.dualAnnihilator ≤ T.dualAnnihilator := by
    rw [← hVd, ← hWd]
    exact le_sup_left
  let e : LinearMap.NestedQuotient S.dualAnnihilator T.dualAnnihilator ≃ₗ[ℝ]
      ↥(T.dualAnnihilator.map (S.dualAnnihilator).mkQ) :=
    LinearMap.imageQuotientEquiv hPQ
  have hImage : LinearMap.IsStableIn Cg
      (LinearMap.imageMapInd N.dualMap hPmap hQmap) := by
    rw [← LinearMap.imageQuotientEquiv_conj_nestedQuotientMap_eq_imageMapInd
      N.dualMap hPQ hPmap hQmap]
    change LinearMap.IsStableIn Cg (e.conj
      (LinearMap.nestedQuotientMap N.dualMap hPmap hQmap))
    intro z hz
    apply hNestDual z
    have hchar := LinearEquiv.charpoly_conj e
      (LinearMap.nestedQuotientMap N.dualMap hPmap hQmap)
    rw [hchar] at hz
    exact hz
  have hDualInd : LinearMap.IsStableIn Cg
      (LinearMap.dualNestedQuotientMapInd N hTS
        (Submodule.map_le_iff_le_comap.mp hTmap)
        (Submodule.map_le_iff_le_comap.mp hSmap)) := by
    simpa only [LinearMap.dualNestedQuotientMapInd, LinearMap.imageMapInd] using hImage
  have hNest : LinearMap.IsStableIn Cg
      (LinearMap.nestedQuotientMap N
        (Submodule.map_le_iff_le_comap.mp hTmap)
        (Submodule.map_le_iff_le_comap.mp hSmap)) :=
    (LinearMap.isStableIn_nestedQuotient_iff_dualNestedQuotientMapInd
      Cg N hTS
      (Submodule.map_le_iff_le_comap.mp hTmap)
      (Submodule.map_le_iff_le_comap.mp hSmap)).mpr hDualInd
  have hMap : LinearMap.IsStableIn Cg
      (Submodule.mapQ (T.comap S.subtype) (T.comap S.subtype)
        (N.restrict (fun x hx => hSmap ⟨x, hx, rfl⟩))
        (fun x hx => hTmap ⟨(x : X), hx, rfl⟩)) :=
    LinearMap.isStableIn_mapQ_restrict_of_isStableIn_nestedQuotientMap
      Cg N hTmap hSmap hNest
  simpa only [observerErrorQuotientMapIn, N, S, T] using hMap

end LinearSystem
