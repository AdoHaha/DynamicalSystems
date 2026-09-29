/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GeneralDomainPBH
public import DynamicalSystems.Linear.GeneralDomainSpectral

/-! # Quotient feedback for a general stability domain

The quotient construction isolates the unreachable spectral directions from a
controlled-invariant subspace and places the remaining poles by state feedback.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace LinearMap

variable {X U : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- An uncontrollable eigenvalue is retained by every state feedback, so a
feedback whose spectrum lies in `Cg` forces that eigenvalue to lie in `Cg`. -/
theorem mem_of_isUncontrollableEigenvalue_of_feedback_isStableIn
    (Cg : Set ℂ) (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (F : X →ₗ[ℝ] U) (hF : IsStableIn Cg (A + B.comp F))
    {μ : ℂ} (hμ : IsUncontrollableEigenvalue A B μ) : μ ∈ Cg := by
  obtain ⟨η, hη, hAη, hBη⟩ := hμ
  have hT : η.comp ((A + B.comp F).baseChange ℂ) = μ • η := by
    have hbase : (A + B.comp F).baseChange ℂ =
        A.baseChange ℂ + (B.comp F).baseChange ℂ :=
      map_add (Module.End.baseChangeHom ℝ ℂ X) A (B.comp F)
    have hcomp : (B.comp F).baseChange ℂ =
        (B.baseChange ℂ).comp (F.baseChange ℂ) :=
      LinearMap.baseChange_comp F B
    rw [hbase, hcomp, LinearMap.comp_add, hAη, ← LinearMap.comp_assoc, hBη,
      LinearMap.zero_comp]
    simp
  have heig : Module.End.HasEigenvalue ((A + B.comp F).baseChange ℂ).dualMap μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (by
          rw [LinearMap.dualMap_apply']
          exact hT), hη⟩)
  have hroot : (((A + B.comp F).baseChange ℂ).dualMap).charpoly.IsRoot μ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp heig
  rw [charpoly_dualMap_ofField] at hroot
  rw [LinearMap.charpoly_baseChange] at hroot
  exact hF μ hroot

/-- A left eigenvector annihilating the input and `VW` must have its eigenvalue
in `Cg` when `VW` and the domain-relative stabilizable subspace span `W`. -/
theorem mem_of_isUncontrollableEigenvalue_of_sup_stabilizableSubspaceIn
    {W U' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U'] [NormedSpace ℝ U']
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (AW : W →ₗ[ℝ] W) (BW : U' →ₗ[ℝ] W) (VW : Submodule ℝ W)
    (hVW : VW ⊔ LinearMap.stabilizableSubspaceIn Cg AW BW = ⊤)
    (η : (ℂ ⊗[ℝ] W) →ₗ[ℂ] ℂ) (μ : ℂ) (hη : η ≠ 0)
    (hAη : η.comp (AW.baseChange ℂ) = μ • η)
    (hBη : η.comp (BW.baseChange ℂ) = 0)
    (hVη : ∀ x : VW, η ((1 : ℂ) ⊗ₜ[ℝ] (x : W)) = 0) :
    μ ∈ Cg := by
  let evalη : W →ₗ[ℝ] ℂ := (η.restrictScalars ℝ).comp (TensorProduct.mk ℝ ℂ W 1)
  let L : Submodule ℝ W := LinearMap.ker evalη
  have hB_L : LinearMap.range BW ≤ L := by
    rintro y ⟨u, rfl⟩
    change evalη (BW u) = 0
    change η ((1 : ℂ) ⊗ₜ[ℝ] (BW u)) = 0
    rw [show (1 : ℂ) ⊗ₜ[ℝ] (BW u) = BW.baseChange ℂ ((1 : ℂ) ⊗ₜ[ℝ] u) from
      (LinearMap.baseChange_tmul (A := ℂ) (f := BW) (1 : ℂ) u).symm]
    have h := congrFun (congrArg DFunLike.coe hBη) ((1 : ℂ) ⊗ₜ[ℝ] u)
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  have hA_L : Submodule.map AW L ≤ L := by
    rintro y ⟨x, hx, rfl⟩
    change evalη (AW x) = 0
    change η ((1 : ℂ) ⊗ₜ[ℝ] (AW x)) = 0
    rw [show (1 : ℂ) ⊗ₜ[ℝ] (AW x) = AW.baseChange ℂ ((1 : ℂ) ⊗ₜ[ℝ] x) from
      (LinearMap.baseChange_tmul (A := ℂ) (f := AW) (1 : ℂ) x).symm]
    have hx' : η ((1 : ℂ) ⊗ₜ[ℝ] x) = 0 := hx
    have h := congrFun (congrArg DFunLike.coe hAη) ((1 : ℂ) ⊗ₜ[ℝ] x)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [h, hx', mul_zero]
  have hR_L : LinearMap.reachableSubspace AW BW ≤ L :=
    LinearMap.reachableSubspace_le AW BW hB_L hA_L
  have hV_L : VW ≤ L := by
    intro x hx
    change evalη x = 0
    change η ((1 : ℂ) ⊗ₜ[ℝ] x) = 0
    simpa using hVη ⟨x, hx⟩
  have hsup : VW ⊔ LinearMap.stableSubspaceIn Cg AW ⊔ LinearMap.reachableSubspace AW BW = ⊤ := by
    rw [← hVW, LinearMap.stabilizableSubspaceIn, sup_assoc]
  have hex : ∃ w : W, evalη w ≠ 0 := by
    by_contra h
    push Not at h
    apply hη
    refine LinearMap.ext fun z => ?_
    change η z = 0
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c w =>
        have hcw : c ⊗ₜ[ℝ] w = c • ((1 : ℂ) ⊗ₜ[ℝ] w) := by
          rw [TensorProduct.smul_tmul']
          simp
        have hw' : η ((1 : ℂ) ⊗ₜ[ℝ] w) = 0 := h w
        rw [hcw, map_smul, hw', smul_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  obtain ⟨w, hw⟩ := hex
  have hwmem : w ∈ VW ⊔ LinearMap.stableSubspaceIn Cg AW ⊔
      LinearMap.reachableSubspace AW BW := by rw [hsup]; trivial
  obtain ⟨a, ha, r, hr, rfl⟩ := Submodule.mem_sup.mp hwmem
  obtain ⟨v, hv, h, hh, rfl⟩ := Submodule.mem_sup.mp ha
  have hr0 : evalη r = 0 := hR_L hr
  have hv0 : evalη v = 0 := hV_L hv
  have hh0 : evalη h ≠ 0 := by
    have hsum : evalη (v + h + r) = evalη h := by
      rw [map_add, map_add, hv0, hr0, zero_add, add_zero]
    rwa [hsum] at hw
  let H : Submodule ℝ W := LinearMap.stableSubspaceIn Cg AW
  have hHinv : ∀ x ∈ H, AW x ∈ H := fun x hx =>
    LinearMap.map_stableSubspaceIn_le Cg AW ⟨x, hx, rfl⟩
  let TH : H →ₗ[ℝ] H := AW.restrict hHinv
  have hTH : LinearMap.IsStableIn Cg TH :=
    LinearMap.isStableIn_restrict_stableSubspaceIn Cg hCg AW
  have hsub : H.subtype.comp TH = AW.comp H.subtype := by
    ext x
    rfl
  have hcomp : (η.comp (H.subtype.baseChange ℂ)).comp (TH.baseChange ℂ) =
      μ • (η.comp (H.subtype.baseChange ℂ)) := by
    have hbc := congrArg (fun f => f.baseChange ℂ) hsub
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hbc
    calc (η.comp (H.subtype.baseChange ℂ)).comp (TH.baseChange ℂ)
        = η.comp ((H.subtype.baseChange ℂ).comp (TH.baseChange ℂ)) := by
          rw [LinearMap.comp_assoc]
      _ = η.comp ((AW.baseChange ℂ).comp (H.subtype.baseChange ℂ)) := by rw [hbc]
      _ = (η.comp (AW.baseChange ℂ)).comp (H.subtype.baseChange ℂ) := by
          rw [LinearMap.comp_assoc]
      _ = (μ • η).comp (H.subtype.baseChange ℂ) := by rw [hAη]
      _ = μ • (η.comp (H.subtype.baseChange ℂ)) := by rw [LinearMap.smul_comp]
  have hηH : η.comp (H.subtype.baseChange ℂ) ≠ 0 := by
    intro hzero
    apply hh0
    have h := congrFun (congrArg DFunLike.coe hzero) ((1 : ℂ) ⊗ₜ[ℝ] ⟨h, hh⟩)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
    rw [LinearMap.baseChange_tmul] at h
    simpa [evalη] using h
  exact mem_of_isUncontrollableEigenvalue_of_feedback_isStableIn Cg TH
    (0 : U' →ₗ[ℝ] H) 0 (by simpa using hTH)
    ⟨η.comp (H.subtype.baseChange ℂ), hηH, hcomp, by simp⟩

/-- Pull an uncontrollable quotient eigenvector back to the original space. -/
theorem mem_of_isUncontrollableEigenvalue_quotient
    {W U' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U'] [NormedSpace ℝ U']
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (AW : W →ₗ[ℝ] W) (BW : U' →ₗ[ℝ] W) (VW : Submodule ℝ W)
    (hVW : VW ⊔ LinearMap.stabilizableSubspaceIn Cg AW BW = ⊤)
    (μ : ℂ) (η : (ℂ ⊗[ℝ] (W ⧸ VW)) →ₗ[ℂ] ℂ) (hη : η ≠ 0)
    (hBη : η.comp ((VW.mkQ.comp BW).baseChange ℂ) = 0)
    (hAη : (η.comp (VW.mkQ.baseChange ℂ)).comp (AW.baseChange ℂ) =
      μ • (η.comp (VW.mkQ.baseChange ℂ))) :
    μ ∈ Cg := by
  let ηt : (ℂ ⊗[ℝ] W) →ₗ[ℂ] ℂ := η.comp (VW.mkQ.baseChange ℂ)
  have hsurj : Function.Surjective (VW.mkQ.baseChange ℂ) :=
    LinearMap.baseChange_surjective ℂ (Submodule.mkQ_surjective VW)
  have hηne : ηt ≠ 0 := by
    intro h0
    apply hη
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := hsurj y
    have hz := congrArg (fun f : (ℂ ⊗[ℝ] W) →ₗ[ℂ] ℂ => f z) h0
    simpa [ηt, LinearMap.comp_apply] using hz
  have hηA : ηt.comp (AW.baseChange ℂ) = μ • ηt :=
    hAη
  have hηB : ηt.comp (BW.baseChange ℂ) = 0 := by
    have hbc : (VW.mkQ.comp BW).baseChange ℂ =
        (VW.mkQ.baseChange ℂ).comp (BW.baseChange ℂ) :=
      LinearMap.baseChange_comp BW VW.mkQ
    calc ηt.comp (BW.baseChange ℂ)
        = η.comp ((VW.mkQ.baseChange ℂ).comp (BW.baseChange ℂ)) := by
          rw [← LinearMap.comp_assoc]
      _ = η.comp ((VW.mkQ.comp BW).baseChange ℂ) := by rw [hbc]
      _ = 0 := hBη
  have hVη : ∀ x : VW, ηt ((1 : ℂ) ⊗ₜ[ℝ] (x : W)) = 0 := by
    intro x
    have hx0 : VW.mkQ (x : W) = 0 :=
      LinearMap.mem_ker.mp (by rw [Submodule.ker_mkQ]; exact x.2)
    have h1 : (VW.mkQ.baseChange ℂ) ((1 : ℂ) ⊗ₜ[ℝ] (x : W)) = 0 := by
      simp [LinearMap.baseChange_tmul, hx0]
    change η ((VW.mkQ.baseChange ℂ) ((1 : ℂ) ⊗ₜ[ℝ] (x : W))) = 0
    rw [h1, map_zero]
  exact mem_of_isUncontrollableEigenvalue_of_sup_stabilizableSubspaceIn Cg hCg AW BW VW
    hVW ηt μ hηne hηA hηB hVη

/-- An uncontrollable eigenvalue of the quotient pair lies in `Cg`. -/
theorem mem_of_isUncontrollableEigenvalue_quotient_mapQ
    {W U' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U'] [NormedSpace ℝ U']
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (AW : W →ₗ[ℝ] W) (BW : U' →ₗ[ℝ] W) (VW : Submodule ℝ W)
    (hmap : ∀ v ∈ VW, AW v ∈ VW)
    (hVW : VW ⊔ LinearMap.stabilizableSubspaceIn Cg AW BW = ⊤)
    (μ : ℂ) (η : (ℂ ⊗[ℝ] (W ⧸ VW)) →ₗ[ℂ] ℂ) (hη : η ≠ 0)
    (hAη : η.comp ((Submodule.mapQ VW VW AW hmap).baseChange ℂ) = μ • η)
    (hBη : η.comp ((VW.mkQ.comp BW).baseChange ℂ) = 0) :
    μ ∈ Cg := by
  apply mem_of_isUncontrollableEigenvalue_quotient Cg hCg AW BW VW hVW μ η hη hBη
  have hbc : VW.mkQ.baseChange ℂ ∘ₗ AW.baseChange ℂ =
      (Submodule.mapQ VW VW AW hmap).baseChange ℂ ∘ₗ VW.mkQ.baseChange ℂ := by
    have h := congrArg (fun f : W →ₗ[ℝ] (W ⧸ VW) => f.baseChange ℂ)
      (Submodule.mapQ_mkQ (p := VW) (q := VW) (f := AW) (h := hmap))
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h
    exact h.symm
  calc (η.comp (VW.mkQ.baseChange ℂ)).comp (AW.baseChange ℂ)
      = η.comp ((VW.mkQ.baseChange ℂ).comp (AW.baseChange ℂ)) := by
        rw [LinearMap.comp_assoc]
    _ = η.comp ((Submodule.mapQ VW VW AW hmap).baseChange ℂ ∘ₗ VW.mkQ.baseChange ℂ) := by
        rw [hbc]
    _ = (η.comp ((Submodule.mapQ VW VW AW hmap).baseChange ℂ)).comp
          (VW.mkQ.baseChange ℂ) := by rw [← LinearMap.comp_assoc]
    _ = μ • (η.comp (VW.mkQ.baseChange ℂ)) := by rw [hAη, LinearMap.smul_comp]

/-- A quotient pair admits a gain placing all its poles in `Cg` when the
domain-relative stabilizable subspace spans modulo `VW`. -/
theorem exists_feedback_isStableIn_quotient_of_sup_stabilizableSubspaceIn
    {W U' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U'] [NormedSpace ℝ U']
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (AW : W →ₗ[ℝ] W) (BW : U' →ₗ[ℝ] W) (VW : Submodule ℝ W)
    (hmap : ∀ v ∈ VW, AW v ∈ VW)
    (hVW : VW ⊔ LinearMap.stabilizableSubspaceIn Cg AW BW = ⊤) :
    ∃ G : (W ⧸ VW) →ₗ[ℝ] U', IsStableIn Cg
      (Submodule.mapQ VW VW AW hmap + (VW.mkQ.comp BW).comp G) := by
  have hPBH : ∀ μ : ℂ,
      IsUncontrollableEigenvalue (Submodule.mapQ VW VW AW hmap) (VW.mkQ.comp BW) μ →
        μ ∈ Cg := by
    intro μ hμ
    obtain ⟨η, hη, hAη, hBη⟩ := hμ
    exact mem_of_isUncontrollableEigenvalue_quotient_mapQ Cg hCg AW BW VW hmap hVW
      μ η hη hAη hBη
  exact exists_feedback_isStableIn_of_uncontrollableEigenvalues Cg hCg
    (Submodule.mapQ VW VW AW hmap) (VW.mkQ.comp BW) hPBH

/-- An intertwiner carries stable spectral directions into stable directions. -/
theorem map_stableSubspaceIn_intertwiner_le_forQuotient (Cg : Set ℂ)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (A : X →ₗ[ℝ] X) (T : Y →ₗ[ℝ] Y) (q : X →ₗ[ℝ] Y)
    (hq : q.comp A = T.comp q) :
    Submodule.map q (stableSubspaceIn Cg A) ≤ stableSubspaceIn Cg T := by
  have hmat : LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ Y) q *
        LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A =
      LinearMap.toMatrix (Module.finBasis ℝ Y) (Module.finBasis ℝ Y) T *
        LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ Y) q := by
    rw [← LinearMap.toMatrix_comp (v₁ := Module.finBasis ℝ X)
      (v₂ := Module.finBasis ℝ X) (v₃ := Module.finBasis ℝ Y) q A,
      hq, LinearMap.toMatrix_comp (v₁ := Module.finBasis ℝ X)
        (v₂ := Module.finBasis ℝ Y) (v₃ := Module.finBasis ℝ Y) T q]
  have hmatc : (LinearMap.toMatrix (Module.finBasis ℝ X)
        (Module.finBasis ℝ Y) q).map (algebraMap ℝ ℂ) *
        (LinearMap.toMatrix (Module.finBasis ℝ X)
          (Module.finBasis ℝ X) A).map (algebraMap ℝ ℂ) =
      (LinearMap.toMatrix (Module.finBasis ℝ Y)
        (Module.finBasis ℝ Y) T).map (algebraMap ℝ ℂ) *
        (LinearMap.toMatrix (Module.finBasis ℝ X)
          (Module.finBasis ℝ Y) q).map (algebraMap ℝ ℂ) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hmat]
  have hmap : Submodule.map
      (Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℝ X)
        (Module.finBasis ℝ Y) q).map (algebraMap ℝ ℂ)))
      (complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∈ Cg)) ≤
      complexSpectralSubspaceOfBasis (Module.finBasis ℝ Y) T (fun μ ↦ μ ∈ Cg) := by
    rw [complexSpectralSubspaceOfBasis, Submodule.map_iSup]
    refine iSup_le fun μ ↦ ?_
    rw [complexSpectralSubspaceOfBasis]
    exact le_iSup_of_le μ (map_toLin'_maxGenEigenspace _ _ _ μ.1 hmatc)
  rintro y ⟨x, hx, rfl⟩
  have hx' : ofRealPi ((Module.finBasis ℝ X).equivFun x) ∈
      complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∈ Cg) :=
    hx
  have hqx := hmap ⟨_, hx', rfl⟩
  change ofRealPi ((Module.finBasis ℝ Y).equivFun (q x)) ∈
    complexSpectralSubspaceOfBasis (Module.finBasis ℝ Y) T (fun μ ↦ μ ∈ Cg)
  rw [← ofRealPi_equivFun_toLin'_apply q x]
  exact hqx

/-- An intertwiner carries complementary spectral directions into the
corresponding complementary directions. -/
theorem map_antistableSubspaceIn_intertwiner_le_forQuotient (Cg : Set ℂ)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (A : X →ₗ[ℝ] X) (T : Y →ₗ[ℝ] Y) (q : X →ₗ[ℝ] Y)
    (hq : q.comp A = T.comp q) :
    Submodule.map q (antistableSubspaceIn Cg A) ≤ antistableSubspaceIn Cg T := by
  have hmat : LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ Y) q *
        LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A =
      LinearMap.toMatrix (Module.finBasis ℝ Y) (Module.finBasis ℝ Y) T *
        LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ Y) q := by
    rw [← LinearMap.toMatrix_comp (v₁ := Module.finBasis ℝ X)
      (v₂ := Module.finBasis ℝ X) (v₃ := Module.finBasis ℝ Y) q A,
      hq, LinearMap.toMatrix_comp (v₁ := Module.finBasis ℝ X)
        (v₂ := Module.finBasis ℝ Y) (v₃ := Module.finBasis ℝ Y) T q]
  have hmatc : (LinearMap.toMatrix (Module.finBasis ℝ X)
        (Module.finBasis ℝ Y) q).map (algebraMap ℝ ℂ) *
        (LinearMap.toMatrix (Module.finBasis ℝ X)
          (Module.finBasis ℝ X) A).map (algebraMap ℝ ℂ) =
      (LinearMap.toMatrix (Module.finBasis ℝ Y)
        (Module.finBasis ℝ Y) T).map (algebraMap ℝ ℂ) *
        (LinearMap.toMatrix (Module.finBasis ℝ X)
          (Module.finBasis ℝ Y) q).map (algebraMap ℝ ℂ) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hmat]
  have hmap : Submodule.map
      (Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℝ X)
        (Module.finBasis ℝ Y) q).map (algebraMap ℝ ℂ)))
      (complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∉ Cg)) ≤
      complexSpectralSubspaceOfBasis (Module.finBasis ℝ Y) T (fun μ ↦ μ ∉ Cg) := by
    rw [complexSpectralSubspaceOfBasis, Submodule.map_iSup]
    refine iSup_le fun μ ↦ ?_
    rw [complexSpectralSubspaceOfBasis]
    exact le_iSup_of_le μ (map_toLin'_maxGenEigenspace _ _ _ μ.1 hmatc)
  rintro y ⟨x, hx, rfl⟩
  have hx' : ofRealPi ((Module.finBasis ℝ X).equivFun x) ∈
      complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∉ Cg) :=
    hx
  have hqx := hmap ⟨_, hx', rfl⟩
  change ofRealPi ((Module.finBasis ℝ Y).equivFun (q x)) ∈
    complexSpectralSubspaceOfBasis (Module.finBasis ℝ Y) T (fun μ ↦ μ ∉ Cg)
  rw [← ofRealPi_equivFun_toLin'_apply q x]
  exact hqx

theorem map_stableSubspaceIn_quotientReachable_le
    (Cg : Set ℂ) (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    [IsClosed (reachableSubspace A B : Set X)] :
    Submodule.map (reachableSubspace A B).mkQ (stableSubspaceIn Cg A) ≤
      stableSubspaceIn Cg (quotientReachableA A B) := by
  let R := reachableSubspace A B
  let Aq : (X ⧸ R) →ₗ[ℝ] (X ⧸ R) := R.mapQ R A
    ((Submodule.map_le_iff_le_comap).mp (map_reachableSubspace_le A B))
  have hR : R ≤ R.comap A := fun x hx => map_reachableSubspace_le A B ⟨x, hx, rfl⟩
  have hq : R.mkQ.comp A = Aq.comp R.mkQ := by
    ext x
    exact (congrFun (congrArg DFunLike.coe
      (Submodule.mapQ_mkQ R R A (h := hR))) x).symm
  exact map_stableSubspaceIn_intertwiner_le_forQuotient Cg A Aq R.mkQ hq

/-- **Unstable spectral subspaces pass to the uncontrollable quotient.** This is
the closed-right-half-plane counterpart of
`map_stableSubspaceIn_quotientReachable_le`. -/
theorem map_antistableSubspaceIn_quotientReachable_le_forFeedback
    (Cg : Set ℂ) (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    [IsClosed (reachableSubspace A B : Set X)] :
    Submodule.map (reachableSubspace A B).mkQ (antistableSubspaceIn Cg A) ≤
      antistableSubspaceIn Cg (quotientReachableA A B) := by
  let R := reachableSubspace A B
  let Aq : (X ⧸ R) →ₗ[ℝ] (X ⧸ R) := R.mapQ R A
    ((Submodule.map_le_iff_le_comap).mp (map_reachableSubspace_le A B))
  have hR : R ≤ R.comap A := fun x hx => map_reachableSubspace_le A B ⟨x, hx, rfl⟩
  have hq : R.mkQ.comp A = Aq.comp R.mkQ := by
    ext x
    exact (congrFun (congrArg DFunLike.coe
      (Submodule.mapQ_mkQ R R A (h := hR))) x).symm
  exact map_antistableSubspaceIn_intertwiner_le_forQuotient Cg A Aq R.mkQ hq

/-- The inverse image of the reachable quotient's stable subspace is exactly
the domain-relative stabilizable subspace. -/
theorem comap_stableSubspaceIn_quotientReachable_eq
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    [IsClosed (reachableSubspace A B : Set X)] :
    Submodule.comap (reachableSubspace A B).mkQ
      (stableSubspaceIn Cg (quotientReachableA A B)) =
      stableSubspaceIn Cg A ⊔ reachableSubspace A B := by
  apply le_antisymm
  · let R := reachableSubspace A B
    let Aq : (X ⧸ R) →ₗ[ℝ] (X ⧸ R) := R.mapQ R A
      ((Submodule.map_le_iff_le_comap).mp (map_reachableSubspace_le A B))
    intro x hx
    have hxQ : R.mkQ x ∈ stableSubspaceIn Cg Aq := by
      simpa [Aq, quotientReachableA, R] using hx
    have hxsplit : x ∈ stableSubspaceIn Cg A ⊔ antistableSubspaceIn Cg A := by
      rw [stableSubspaceIn_sup_antistableSubspaceIn_eq_top Cg hCg]
      trivial
    obtain ⟨xg, hxg, xb, hxb, hsum⟩ := Submodule.mem_sup.mp hxsplit
    have hxgQ : R.mkQ xg ∈ stableSubspaceIn Cg Aq := by
      have h := map_stableSubspaceIn_quotientReachable_le Cg A B ⟨xg, hxg, rfl⟩
      simpa [Aq, quotientReachableA, R] using h
    have hxbQ_unstable : R.mkQ xb ∈ antistableSubspaceIn Cg Aq := by
      have h := map_antistableSubspaceIn_quotientReachable_le_forFeedback Cg A B ⟨xb, hxb, rfl⟩
      simpa [Aq, quotientReachableA, R] using h
    have hsumQ : R.mkQ xg + R.mkQ xb = R.mkQ x := by
      rw [← hsum, map_add]
    have hxbQ_hurwitz : R.mkQ xb ∈ stableSubspaceIn Cg Aq := by
      have hsub := (stableSubspaceIn Cg Aq).sub_mem hxQ hxgQ
      have heq : R.mkQ xb = R.mkQ x - R.mkQ xg := by
        calc
          R.mkQ xb = R.mkQ xg + R.mkQ xb - R.mkQ xg := by abel
          _ = R.mkQ x - R.mkQ xg := by rw [hsumQ]
      rw [heq]
      exact hsub
    have hxbQ_bot : R.mkQ xb = 0 := by
      have hmem : R.mkQ xb ∈ stableSubspaceIn Cg Aq ⊓ antistableSubspaceIn Cg Aq :=
        ⟨hxbQ_hurwitz, hxbQ_unstable⟩
      have hdisj := disjoint_iff.mp (disjoint_stableSubspaceIn_antistableSubspaceIn Cg Aq)
      rw [hdisj] at hmem
      simpa using hmem
    have hxbR : xb ∈ R := by
      rw [← Submodule.ker_mkQ R]
      exact hxbQ_bot
    exact Submodule.mem_sup.mpr ⟨xg, hxg, xb, hxbR, hsum⟩
  · intro x hx
    rw [Submodule.mem_comap]
    rw [Submodule.mem_sup] at hx
    obtain ⟨xg, hxg, xr, hxr, hsum⟩ := hx
    rw [← hsum, map_add]
    have hxgQ : (reachableSubspace A B).mkQ xg ∈
        stableSubspaceIn Cg (quotientReachableA A B) :=
      map_stableSubspaceIn_quotientReachable_le Cg A B ⟨xg, hxg, rfl⟩
    have hxrQ : (reachableSubspace A B).mkQ xr = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hxr
    rw [hxrQ, add_zero]
    exact hxgQ

/-- For any invariant subspace, the inverse image of its stable quotient
subspace is the sum of the ambient stable subspace and that invariant subspace. -/
theorem comap_stableSubspaceIn_mapQ_eq
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) (A : X →ₗ[ℝ] X) (R : Submodule ℝ X)
    (hR : ∀ x ∈ R, A x ∈ R) [IsClosed (R : Set X)] :
    Submodule.comap R.mkQ
      (stableSubspaceIn Cg (R.mapQ R A hR)) =
      stableSubspaceIn Cg A ⊔ R := by
  apply le_antisymm
  · let Aq : (X ⧸ R) →ₗ[ℝ] (X ⧸ R) := R.mapQ R A hR
    have hq : R.mkQ.comp A = Aq.comp R.mkQ := by
      simpa only [Aq] using
        (Submodule.mapQ_mkQ (p := R) (q := R) (f := A) (h := hR)).symm
    intro x hx
    have hxQ : R.mkQ x ∈ stableSubspaceIn Cg Aq := by
      change R.mkQ x ∈ stableSubspaceIn Cg (R.mapQ R A hR) at hx
      exact hx
    have hxsplit : x ∈ stableSubspaceIn Cg A ⊔ antistableSubspaceIn Cg A := by
      rw [stableSubspaceIn_sup_antistableSubspaceIn_eq_top Cg hCg]
      trivial
    obtain ⟨xg, hxg, xb, hxb, hsum⟩ := Submodule.mem_sup.mp hxsplit
    have hxgQ : R.mkQ xg ∈ stableSubspaceIn Cg Aq := by
      have h := map_stableSubspaceIn_intertwiner_le_forQuotient Cg A Aq R.mkQ hq ⟨xg, hxg, rfl⟩
      simpa only [Aq] using h
    have hxbQ_unstable : R.mkQ xb ∈ antistableSubspaceIn Cg Aq := by
      have h := map_antistableSubspaceIn_intertwiner_le_forQuotient Cg A Aq R.mkQ hq ⟨xb, hxb, rfl⟩
      simpa only [Aq] using h
    have hsumQ : R.mkQ xg + R.mkQ xb = R.mkQ x := by
      rw [← hsum, map_add]
    have hxbQ_hurwitz : R.mkQ xb ∈ stableSubspaceIn Cg Aq := by
      have hsub := (stableSubspaceIn Cg Aq).sub_mem hxQ hxgQ
      have heq : R.mkQ xb = R.mkQ x - R.mkQ xg := by
        calc
          R.mkQ xb = R.mkQ xg + R.mkQ xb - R.mkQ xg := by abel
          _ = R.mkQ x - R.mkQ xg := by rw [hsumQ]
      rw [heq]
      exact hsub
    have hxbQ_bot : R.mkQ xb = 0 := by
      have hmem : R.mkQ xb ∈ stableSubspaceIn Cg Aq ⊓ antistableSubspaceIn Cg Aq :=
        ⟨hxbQ_hurwitz, hxbQ_unstable⟩
      have hdisj := disjoint_iff.mp (disjoint_stableSubspaceIn_antistableSubspaceIn Cg Aq)
      rw [hdisj] at hmem
      simpa using hmem
    have hxbR : xb ∈ R := by
      rw [← Submodule.ker_mkQ R]
      exact hxbQ_bot
    exact Submodule.mem_sup.mpr ⟨xg, hxg, xb, hxbR, hsum⟩
  · intro x hx
    rw [Submodule.mem_comap]
    rw [Submodule.mem_sup] at hx
    obtain ⟨xg, hxg, xr, hxr, hsum⟩ := hx
    rw [← hsum, map_add]
    have hq : R.mkQ.comp A = (R.mapQ R A hR).comp R.mkQ := by
      simpa only using
        (Submodule.mapQ_mkQ (p := R) (q := R) (f := A) (h := hR)).symm
    have hxgQ : R.mkQ xg ∈
        stableSubspaceIn Cg (R.mapQ R A hR) :=
      map_stableSubspaceIn_intertwiner_le_forQuotient Cg A (R.mapQ R A hR) R.mkQ hq
        ⟨xg, hxg, rfl⟩
    have hxrQ : R.mkQ xr = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hxr
    rw [hxrQ, add_zero]
    exact hxgQ

/-- State feedback preserves the domain-relative stabilizable subspace. -/
theorem stabilizableSubspaceIn_add_feedback_eq
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (F : X →ₗ[ℝ] U) :
    stabilizableSubspaceIn Cg (A + B.comp F) B = stabilizableSubspaceIn Cg A B := by
  let R := reachableSubspace A B
  have hClosed : IsClosed (R : Set X) := R.closed_of_finiteDimensional
  have hAinv : ∀ x ∈ R, A x ∈ R := fun x hx =>
    map_reachableSubspace_le A B ⟨x, hx, rfl⟩
  have hMinv : ∀ x ∈ R, (A + B.comp F) x ∈ R := by
    intro x hx
    exact R.add_mem (hAinv x hx)
      (range_le_reachableSubspace A B ⟨F x, rfl⟩)
  have hQ : R.mapQ R (A + B.comp F) hMinv = R.mapQ R A hAinv := by
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on (p := R) x ?_
    intro y
    simp only [Submodule.mapQ_apply, LinearMap.add_apply, LinearMap.comp_apply]
    rw [Submodule.Quotient.mk_add]
    have hB : (Submodule.Quotient.mk (B (F y)) : X ⧸ R) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact range_le_reachableSubspace A B ⟨F y, rfl⟩
    rw [hB, add_zero]
  have hM : Submodule.comap R.mkQ (stableSubspaceIn Cg
      (R.mapQ R (A + B.comp F) hMinv)) =
      stabilizableSubspaceIn Cg (A + B.comp F) B := by
    rw [comap_stableSubspaceIn_mapQ_eq Cg hCg (A + B.comp F) R hMinv]
    simp only [stabilizableSubspaceIn, R, reachableSubspace_add_comp]
  have hA : Submodule.comap R.mkQ (stableSubspaceIn Cg (R.mapQ R A hAinv)) =
      stabilizableSubspaceIn Cg A B := by
    rw [comap_stableSubspaceIn_mapQ_eq Cg hCg A R hAinv]
    rfl
  calc
    stabilizableSubspaceIn Cg (A + B.comp F) B =
        Submodule.comap R.mkQ (stableSubspaceIn Cg (R.mapQ R (A + B.comp F) hMinv)) :=
      hM.symm
    _ = Submodule.comap R.mkQ (stableSubspaceIn Cg (R.mapQ R A hAinv)) := by rw [hQ]
    _ = stabilizableSubspaceIn Cg A B := hA

/-- A controlled-invariant subspace admits a preserving feedback that places
the poles of the associated stabilizable quotient inside `Cg`. -/
theorem exists_feedback_isStableIn_quotient_of_geometricCondition
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (V : Submodule ℝ X)
    (hV : Submodule.map A V ≤ V ⊔ LinearMap.range B) :
    ∃ F : X →ₗ[ℝ] U,
      Nonempty {hFV : Submodule.map (A + B.comp F) V ≤ V //
      let W : Submodule ℝ X := V ⊔ LinearMap.stabilizableSubspaceIn Cg A B
      let hWinv : ∀ x ∈ W, (A + B.comp F) x ∈ W := fun x hx =>
        map_add_feedback_sup_stabilizableSubspaceIn_le Cg A B F hFV ⟨x, hx, rfl⟩
      let VW : Submodule ℝ W := V.comap W.subtype
      let hmap : ∀ x ∈ VW, ((A + B.comp F).restrict hWinv) x ∈ VW := fun x hx => by
        change ((A + B.comp F) (x : X)) ∈ V
        exact hFV ⟨(x : X), hx, rfl⟩
      LinearMap.IsStableIn Cg (Submodule.mapQ VW VW ((A + B.comp F).restrict hWinv) hmap)} := by
  classical
  obtain ⟨F₀, hF₀⟩ := LinearMap.exists_stateFeedback_of_isControlledInvariant hV
  let W : Submodule ℝ X := V ⊔ LinearMap.stabilizableSubspaceIn Cg A B
  have hWle : V ≤ W := le_sup_left
  have hBleW : LinearMap.range B ≤ W :=
    le_trans (range_le_stabilizableSubspaceIn Cg A B) le_sup_right
  have hWinv : ∀ x ∈ W, (A + B.comp F₀) x ∈ W := fun x hx =>
    map_add_feedback_sup_stabilizableSubspaceIn_le Cg A B F₀ hF₀ ⟨x, hx, rfl⟩
  let AW : W →ₗ[ℝ] W := (A + B.comp F₀).restrict hWinv
  let BW : U →ₗ[ℝ] W :=
    B.codRestrict W (fun u => hBleW (LinearMap.mem_range_self B u))
  let VW : Submodule ℝ W := V.comap W.subtype
  have hVWinv : ∀ v ∈ VW, AW v ∈ VW := by
    intro v hv
    rw [Submodule.mem_comap] at hv ⊢
    exact hF₀ ⟨(v : X), hv, rfl⟩
  have hmono : (LinearMap.stabilizableSubspaceIn Cg A B).comap W.subtype ≤
      (LinearMap.stabilizableSubspaceIn Cg (A + B.comp F₀) B).comap W.subtype :=
    Submodule.comap_mono (by rw [stabilizableSubspaceIn_add_feedback_eq Cg hCg A B F₀])
  have hsupV : VW ⊔ (LinearMap.stabilizableSubspaceIn Cg A B).comap W.subtype = ⊤ :=
    LinearSystem.comap_sup_subtype_eq_top hWle le_sup_right (by rfl)
  have hsup : VW ⊔ LinearMap.stabilizableSubspaceIn Cg AW BW = ⊤ := by
    rw [stabilizableSubspaceIn_restrict_eq Cg hCg (A + B.comp F₀) B W hWinv hBleW]
    apply le_antisymm le_top
    calc ⊤ = VW ⊔ (LinearMap.stabilizableSubspaceIn Cg A B).comap W.subtype := hsupV.symm
      _ ≤ VW ⊔ (LinearMap.stabilizableSubspaceIn Cg (A + B.comp F₀) B).comap W.subtype :=
          sup_le_sup_left hmono _
  obtain ⟨G, hG⟩ :=
    exists_feedback_isStableIn_quotient_of_sup_stabilizableSubspaceIn Cg hCg
      AW BW VW hVWinv hsup
  obtain ⟨F₁, hF₁⟩ := LinearMap.exists_extend (G.comp VW.mkQ)
  let F : X →ₗ[ℝ] U := F₀ + F₁
  have hFV : Submodule.map (A + B.comp F) V ≤ V := by
    rintro y ⟨v, hv, rfl⟩
    have hvW : v ∈ W := hWle hv
    have hvVW : (⟨v, hvW⟩ : W) ∈ VW := by
      rw [Submodule.mem_comap]; exact hv
    have hF1v : F₁ v = 0 := by
      have h := congrArg (fun f : W →ₗ[ℝ] U => f ⟨v, hvW⟩) hF₁
      have h' : F₁ (W.subtype ⟨v, hvW⟩) = G (VW.mkQ ⟨v, hvW⟩) := by
        simpa only [LinearMap.comp_apply] using h
      have hv' : W.subtype ⟨v, hvW⟩ = v := rfl
      have hG0 : G (VW.mkQ ⟨v, hvW⟩) = 0 := by
        have hmk : VW.mkQ ⟨v, hvW⟩ = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact hvVW
        rw [hmk, map_zero]
      rw [hv'] at h'
      rw [h', hG0]
    have hEq : (A + B.comp F) v = (A + B.comp F₀) v := by
      simp [F, hF1v]
    rw [hEq]
    exact hF₀ ⟨v, hv, rfl⟩
  have hMinv : ∀ x ∈ W, (A + B.comp F) x ∈ W :=
    fun x hx => map_add_feedback_sup_stabilizableSubspaceIn_le Cg A B F hFV ⟨x, hx, rfl⟩
  have hmap : ∀ x ∈ VW, ((A + B.comp F).restrict hMinv) x ∈ VW := fun x hx => by
    have hxV : (x : X) ∈ V := hx
    change (((A + B.comp F).restrict hMinv) x : X) ∈ V
    have hrestrict : (((A + B.comp F).restrict hMinv) x : X) =
        (A + B.comp F) (x : X) := rfl
    rw [hrestrict]
    exact hFV ⟨(x : X), hxV, rfl⟩
  have hmapEq : Submodule.mapQ VW VW ((A + B.comp F).restrict hMinv) hmap =
      Submodule.mapQ VW VW AW hVWinv + (VW.mkQ.comp BW).comp G := by
    apply LinearMap.ext
    intro y
    refine Submodule.Quotient.induction_on (p := VW) y ?_
    intro x
    have hF1x : F₁ x = G (VW.mkQ x) := by
      have := congrArg (fun f : W →ₗ[ℝ] U => f x) hF₁
      simpa using this
    have hxM : ((A + B.comp F).restrict hMinv) x = AW x + BW (G (VW.mkQ x)) := by
      apply Subtype.ext
      simp only [LinearMap.restrict_apply, LinearMap.add_apply, LinearMap.comp_apply,
        Submodule.coe_add, AW, F, hF1x, map_add]
      abel
    simp only [Submodule.mapQ_apply, LinearMap.add_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, hxM]
    rw [← Submodule.Quotient.mk_add]
  have hQ : LinearMap.IsStableIn Cg
      (Submodule.mapQ VW VW ((A + B.comp F).restrict hMinv) hmap) := by
    rw [hmapEq]; exact hG
  refine ⟨F, ⟨⟨hFV, ?_⟩⟩⟩
  simpa only [W, VW] using hQ

end LinearMap
