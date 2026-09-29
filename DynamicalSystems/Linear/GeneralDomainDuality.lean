/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GeneralDomainSpectral
public import DynamicalSystems.Linear.GeneralDomainSpectrum

/-! # Duality of spectral subspaces for a general stability domain -/

@[expose] public section

noncomputable section

namespace LinearMap

/-- The complex stable spectral sum lies in the annihilator of the complementary
spectral sum of the original operator. -/
theorem stableSpectralSubspace_le_dualAnnihilator_antistableSpectralSubspace
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (Cg : Set ℂ) (A : E →ₗ[ℂ] E) :
    (⨆ ν : {ν : ℂ // ν ∈ Cg}, Module.End.maxGenEigenspace A.dualMap ν.1) ≤
      (⨆ μ : {μ : ℂ // μ ∉ Cg},
        Module.End.maxGenEigenspace A μ.1).dualAnnihilator := by
  rw [Submodule.dualAnnihilator_iSup_eq]
  refine iSup_le fun ν ↦ ?_
  refine le_iInf fun μ ↦ ?_
  have hμν : μ.1 ≠ ν.1 := by
    intro h
    exact μ.2 (h ▸ ν.2)
  rw [← dualAnnihilator_genEigenrange_finrank_eq_maxGenEigenspace A ν.1]
  exact Subspace.dualAnnihilator_le_dualAnnihilator_iff.mpr
    (maxGenEigenspace_le_genEigenrange_of_ne A hμν)

/-- The annihilator of the complementary spectral sum is the selected spectral
sum of the transpose. -/
theorem dualAnnihilator_antistableSpectralSubspace_eq_stableSpectralSubspace
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (Cg : Set ℂ) (A : E →ₗ[ℂ] E) :
    (⨆ μ : {μ : ℂ // μ ∉ Cg},
        Module.End.maxGenEigenspace A μ.1).dualAnnihilator =
      (⨆ ν : {ν : ℂ // ν ∈ Cg}, Module.End.maxGenEigenspace A.dualMap ν.1) := by
  classical
  let p : ℂ → Submodule ℂ E := fun μ ↦ Module.End.maxGenEigenspace A μ
  let q : ℂ → Submodule ℂ (Module.Dual ℂ E) :=
    fun ν ↦ Module.End.maxGenEigenspace A.dualMap ν
  change (⨆ μ : {μ : ℂ // μ ∉ Cg}, p μ.1).dualAnnihilator =
    (⨆ ν : {ν : ℂ // ν ∈ Cg}, q ν.1)
  have hp : iSupIndep p := Module.End.independent_maxGenEigenspace A
  have hq : iSupIndep q := Module.End.independent_maxGenEigenspace A.dualMap
  let s : Finset ℂ :=
    (iSupIndep.fintypeNeBotOfFiniteDimensional hp).elems.image Subtype.val
  have hs : ∀ μ, p μ ≠ ⊥ → μ ∈ s := fun μ hμ ↦
      Finset.mem_image.mpr ⟨⟨μ, hμ⟩,
        (iSupIndep.fintypeNeBotOfFiniteDimensional hp).complete ⟨μ, hμ⟩, rfl⟩
  have hs_q : ∀ ν, q ν ≠ ⊥ → ν ∈ s := by
    intro ν hν
    apply hs ν
    intro hpbot
    apply hν
    have heq : Module.finrank ℂ (p ν) = Module.finrank ℂ (q ν) :=
      finrank_maxGenEigenspace_dualMap A ν
    have hz : Module.finrank ℂ (p ν) = 0 := by rw [hpbot]; simp
    rw [hz] at heq
    exact Submodule.finrank_eq_zero.mp heq.symm
  have hU : Module.finrank ℂ ↥(⨆ μ : {μ : ℂ // μ ∉ Cg}, p μ.1) =
      ∑ μ ∈ s.filter (fun μ : ℂ ↦ μ ∉ Cg), Module.finrank ℂ ↥(p μ) :=
    finrank_iSup_subtype_eq_sum_filter (P := fun μ : ℂ ↦ μ ∉ Cg) p hp s hs
  have hV : Module.finrank ℂ ↥(⨆ ν : {ν : ℂ // ν ∈ Cg}, q ν.1) =
      ∑ ν ∈ s.filter (fun ν : ℂ ↦ ν ∈ Cg), Module.finrank ℂ ↥(q ν) :=
    finrank_iSup_subtype_eq_sum_filter (P := fun ν : ℂ ↦ ν ∈ Cg) q hq s hs_q
  have hV' : Module.finrank ℂ ↥(⨆ ν : {ν : ℂ // ν ∈ Cg}, q ν.1) =
      ∑ ν ∈ s.filter (fun ν : ℂ ↦ ν ∈ Cg), Module.finrank ℂ ↥(p ν) := by
    rw [hV]
    apply Finset.sum_congr rfl
    intro ν _
    exact (finrank_maxGenEigenspace_dualMap A ν).symm
  have hE : Module.finrank ℂ E = ∑ μ ∈ s, Module.finrank ℂ ↥(p μ) := by
    have h := finrank_iSup_subtype_eq_sum_filter (P := fun _ : ℂ ↦ True) p hp s hs
    simp only [Finset.filter_true] at h
    rw [show (⨆ μ : {μ : ℂ // True}, p μ.1) = ⨆ μ : ℂ, p μ by
      rw [iSup_subtype]; simp] at h
    rw [Module.End.iSup_maxGenEigenspace_eq_top A, finrank_top] at h
    exact h
  have h2 : Module.finrank ℂ ↥(⨆ μ : {μ : ℂ // μ ∉ Cg}, p μ.1) +
      Module.finrank ℂ ↥(⨆ ν : {ν : ℂ // ν ∈ Cg}, q ν.1) = Module.finrank ℂ E := by
    rw [hU, hV', hE, add_comm]
    rw [Finset.sum_filter_add_sum_filter_not s (fun μ : ℂ ↦ μ ∈ Cg)
      (fun μ ↦ Module.finrank ℂ ↥(p μ))]
  have h1 : Module.finrank ℂ ↥(⨆ μ : {μ : ℂ // μ ∉ Cg}, p μ.1) +
      Module.finrank ℂ ↥((⨆ μ : {μ : ℂ // μ ∉ Cg}, p μ.1)).dualAnnihilator =
      Module.finrank ℂ E :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq _
  have hdim : Module.finrank ℂ ↥(⨆ ν : {ν : ℂ // ν ∈ Cg}, q ν.1) =
      Module.finrank ℂ ↥((⨆ μ : {μ : ℂ // μ ∉ Cg}, p μ.1)).dualAnnihilator := by
    omega
  exact (Submodule.eq_of_le_of_finrank_eq
    (stableSpectralSubspace_le_dualAnnihilator_antistableSpectralSubspace Cg A)
    hdim).symm

open scoped TensorProduct

/-- The canonical complexification of the spectral subspace selected by `Cg`. -/
def complexStableSubspaceIn {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Cg : Set ℂ) (A : M →ₗ[ℝ] M) : Submodule ℂ (ℂ ⊗[ℝ] M) :=
  ⨆ μ : {μ : ℂ // μ ∈ Cg}, Module.End.maxGenEigenspace (A.baseChange ℂ) μ.1

/-- The canonical complexification of the spectral subspace selected by the
complement of `Cg`. -/
def complexAntistableSubspaceIn {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Cg : Set ℂ) (A : M →ₗ[ℝ] M) : Submodule ℂ (ℂ ⊗[ℝ] M) :=
  ⨆ μ : {μ : ℂ // μ ∉ Cg}, Module.End.maxGenEigenspace (A.baseChange ℂ) μ.1

/-- Basis-defined stable subspace for algebraic modules, including algebraic
duals that carry no canonical norm. -/
def stableSubspaceOfBasisIn {M ι : Type*}
    [AddCommGroup M] [Module ℝ M] [Fintype ι] [DecidableEq ι]
    (Cg : Set ℂ) (b : Module.Basis ι ℝ M) (A : M →ₗ[ℝ] M) : Submodule ℝ M :=
  ((complexSpectralSubspaceOfBasis b A (fun μ ↦ μ ∈ Cg)).restrictScalars ℝ).comap
    (ofRealPi.comp b.equivFun.toLinearMap)

/-- Complex coordinates identify the canonical selected spectral subspace. -/
theorem map_complexStableSubspaceIn {M ι : Type*}
    [AddCommGroup M] [Module ℝ M] [Fintype ι] [DecidableEq ι]
    (Cg : Set ℂ) (b : Module.Basis ι ℝ M) (A : M →ₗ[ℝ] M) :
    Submodule.map (b.baseChange ℂ).equivFun.toLinearMap (complexStableSubspaceIn Cg A) =
      complexSpectralSubspaceOfBasis b A (fun μ ↦ μ ∈ Cg) := by
  rw [complexStableSubspaceIn, complexSpectralSubspaceOfBasis, Submodule.map_iSup]
  apply iSup_congr
  intro μ
  exact map_maxGenEigenspace_of_equiv (b.baseChange ℂ).equivFun (A.baseChange ℂ)
    (Matrix.toLin' ((LinearMap.toMatrix b b A).map (algebraMap ℝ ℂ))) μ.1
    (baseChange_repr_comp_gen b A).symm

/-- Complex coordinates identify the canonical complementary spectral subspace. -/
theorem map_complexAntistableSubspaceIn {M ι : Type*}
    [AddCommGroup M] [Module ℝ M] [Fintype ι] [DecidableEq ι]
    (Cg : Set ℂ) (b : Module.Basis ι ℝ M) (A : M →ₗ[ℝ] M) :
    Submodule.map (b.baseChange ℂ).equivFun.toLinearMap (complexAntistableSubspaceIn Cg A) =
      complexSpectralSubspaceOfBasis b A (fun μ ↦ μ ∉ Cg) := by
  rw [complexAntistableSubspaceIn, complexSpectralSubspaceOfBasis, Submodule.map_iSup]
  apply iSup_congr
  intro μ
  exact map_maxGenEigenspace_of_equiv (b.baseChange ℂ).equivFun (A.baseChange ℂ)
    (Matrix.toLin' ((LinearMap.toMatrix b b A).map (algebraMap ℝ ℂ))) μ.1
    (baseChange_repr_comp_gen b A).symm

/-- Membership in the basis-defined subspace is membership of the pure tensor
in the canonical complex spectral sum. -/
theorem mem_stableSubspaceOfBasisIn_iff {M ι : Type*}
    [AddCommGroup M] [Module ℝ M] [Fintype ι] [DecidableEq ι]
    (Cg : Set ℂ) (b : Module.Basis ι ℝ M) (A : M →ₗ[ℝ] M) {x : M} :
    x ∈ stableSubspaceOfBasisIn Cg b A ↔
      (1 : ℂ) ⊗ₜ[ℝ] x ∈ complexStableSubspaceIn Cg A := by
  rw [stableSubspaceOfBasisIn, Submodule.mem_comap, Submodule.restrictScalars_mem,
    ← map_complexStableSubspaceIn Cg b A]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have he1 : (b.baseChange ℂ).equivFun.toLinearMap ((1 : ℂ) ⊗ₜ[ℝ] x) =
        ofRealPi (b.equivFun x) := by
      rw [← baseChange_equivFun_symm_one_tmul_gen b x]
      exact (b.baseChange ℂ).equivFun.apply_symm_apply _
    have : y = (1 : ℂ) ⊗ₜ[ℝ] x := by
      apply (b.baseChange ℂ).equivFun.injective
      change (b.baseChange ℂ).equivFun.toLinearMap y =
        (b.baseChange ℂ).equivFun.toLinearMap ((1 : ℂ) ⊗ₜ[ℝ] x)
      simp only [LinearMap.comp_apply] at hyx
      rw [hyx, he1]
      rfl
    rwa [this] at hy
  · intro hx
    exact ⟨(1 : ℂ) ⊗ₜ[ℝ] x, hx, by
      rw [← baseChange_equivFun_symm_one_tmul_gen b x]
      exact (b.baseChange ℂ).equivFun.apply_symm_apply _⟩

/-- The canonical complex antistable subspace is the complex span of its real
points, equivalently the base change of the real antistable subspace. -/
theorem complexAntistableSubspaceIn_eq_baseChange_antistableSubspaceIn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) (A : X →ₗ[ℝ] X) :
    complexAntistableSubspaceIn Cg A = (antistableSubspaceIn Cg A).baseChange ℂ := by
  let b := Module.finBasis ℝ X
  let eX : ℂ ⊗[ℝ] X →ₗ[ℂ] (Fin (Module.finrank ℝ X) → ℂ) :=
    (b.baseChange ℂ).equivFun.toLinearMap
  have einj : Function.Injective eX := (b.baseChange ℂ).equivFun.injective
  let ψ : X →ₗ[ℝ] (Fin (Module.finrank ℝ X) → ℂ) :=
    ofRealPi.comp b.equivFun.toLinearMap
  have hcomp_fun : ∀ x : X, eX (TensorProduct.mk ℝ ℂ X 1 x) = ψ x := by
    intro x
    change (b.baseChange ℂ).equivFun (1 ⊗ₜ[ℝ] x) = ofRealPi (b.equivFun x)
    rw [← baseChange_equivFun_symm_one_tmul x]
    exact (b.baseChange ℂ).equivFun.apply_symm_apply _
  have hmapAnti : Submodule.map eX (complexAntistableSubspaceIn Cg A) =
      complexSpectralSubspaceOfBasis b A (fun μ ↦ μ ∉ Cg) := by
    exact map_complexAntistableSubspaceIn Cg b A
  have hψU : Set.image ψ (antistableSubspaceIn Cg A : Set X) =
      ((complexSpectralSubspaceOfBasis b A (fun μ ↦ μ ∉ Cg) : Submodule ℂ _) : Set _) ∩
        Set.range ofRealPi := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ⟨b.equivFun x, rfl⟩⟩
      change x ∈ antistableSubspaceIn Cg A at hx
      rw [antistableSubspaceIn, Submodule.mem_comap, Submodule.restrictScalars_mem] at hx
      exact hx
    · rintro ⟨hzV, y, hy⟩
      refine ⟨b.equivFun.symm y, ?_, ?_⟩
      · change b.equivFun.symm y ∈ antistableSubspaceIn Cg A
        rw [antistableSubspaceIn, Submodule.mem_comap, Submodule.restrictScalars_mem]
        change ofRealPi (b.equivFun (b.equivFun.symm y)) ∈ _
        rw [b.equivFun.apply_symm_apply]
        exact hy.symm ▸ hzV
      · simp only [ψ, LinearMap.comp_apply]
        exact (congrArg ofRealPi (b.equivFun.apply_symm_apply y)).trans hy
  have hstar : ∀ v ∈ complexSpectralSubspaceOfBasis b A (fun μ ↦ μ ∉ Cg),
      star v ∈ complexSpectralSubspaceOfBasis b A (fun μ ↦ μ ∉ Cg) := by
    intro v hv
    exact star_mem_iSup_maxGenEigenspace A (fun μ ↦ μ ∉ Cg)
      (fun μ hμ hstar ↦ hμ (by simpa only [star_star] using hCg.2 (star μ) hstar)) hv
  have hspan : Submodule.span ℂ (Set.image ψ (antistableSubspaceIn Cg A : Set X)) =
      complexSpectralSubspaceOfBasis b A (fun μ ↦ μ ∉ Cg) := by
    rw [hψU]
    exact span_inter_range_ofRealPi_eq_of_star_mem _ hstar
  have hmapBase : Submodule.map eX ((antistableSubspaceIn Cg A).baseChange ℂ) =
      complexSpectralSubspaceOfBasis b A (fun μ ↦ μ ∉ Cg) := by
    rw [Submodule.baseChange_eq_span, Submodule.map_span]
    rw [show (↑(Submodule.map (TensorProduct.mk ℝ ℂ X 1) (antistableSubspaceIn Cg A)) :
        Set _) = (TensorProduct.mk ℝ ℂ X 1) '' (antistableSubspaceIn Cg A : Set X) from rfl]
    rw [show eX '' ((TensorProduct.mk ℝ ℂ X 1) ''
        (antistableSubspaceIn Cg A : Set X)) =
        Set.image ψ (antistableSubspaceIn Cg A : Set X) from ?_]
    · exact hspan
    · rw [← Set.image_comp]
      exact Set.image_congr (fun x _ ↦ hcomp_fun x)
  have : Submodule.map eX ((antistableSubspaceIn Cg A).baseChange ℂ) =
      Submodule.map eX (complexAntistableSubspaceIn Cg A) := by
    rw [hmapBase, hmapAnti]
  exact Submodule.map_injective_of_injective einj this.symm

/-- The dual base-change equivalence transports the selected complex spectral
sum of the transpose to the selected sum of the complex transpose. -/
theorem map_toDualBaseChange_complexStableSubspaceIn
    {X : Type*} [AddCommGroup X] [Module ℝ X] [Module.Free ℝ X] [Module.Finite ℝ X]
    (Cg : Set ℂ) (A : X →ₗ[ℝ] X) :
    Submodule.map (TensorProduct.isBaseChange ℝ X ℂ).toDualBaseChange.toLinearMap
        (complexStableSubspaceIn Cg A.dualMap) =
      ⨆ ν : {ν : ℂ // ν ∈ Cg},
        Module.End.maxGenEigenspace ((A.baseChange ℂ).dualMap) ν.1 := by
  rw [complexStableSubspaceIn, Submodule.map_iSup]
  apply iSup_congr
  intro ν
  exact map_maxGenEigenspace_of_equiv
    (TensorProduct.isBaseChange ℝ X ℂ).toDualBaseChange
    ((A.dualMap).baseChange ℂ) ((A.baseChange ℂ).dualMap) ν.1
    (toDualBaseChange_comp_dualMap_baseChange A)

/-- Real spectral duality: the annihilator of the complementary spectral
subspace is the selected spectral subspace of the algebraic transpose. The
basis-defined RHS works for the algebraic dual without a norm choice. -/
theorem dualAnnihilator_antistableSubspaceIn_eq_stableSubspaceOfBasisIn_dualMap
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) (A : X →ₗ[ℝ] X) :
    (antistableSubspaceIn Cg A).dualAnnihilator =
      stableSubspaceOfBasisIn Cg (Module.finBasis ℝ (Module.Dual ℝ X)) A.dualMap := by
  ext φ
  rw [Submodule.mem_dualAnnihilator, mem_stableSubspaceOfBasisIn_iff]
  have h1 : (∀ x ∈ antistableSubspaceIn Cg A, φ x = 0) ↔
      Module.Dual.baseChange ℂ φ ∈ (complexAntistableSubspaceIn Cg A).dualAnnihilator := by
    rw [complexAntistableSubspaceIn_eq_baseChange_antistableSubspaceIn Cg hCg A,
      ← Submodule.mem_dualAnnihilator]
    exact (dualAnnihilator_baseChange_iff (antistableSubspaceIn Cg A) φ).symm
  rw [h1]
  unfold complexAntistableSubspaceIn
  rw [dualAnnihilator_antistableSpectralSubspace_eq_stableSpectralSubspace Cg
    (A.baseChange ℂ)]
  rw [← toDualBaseChange_one_tmul φ,
    ← map_toDualBaseChange_complexStableSubspaceIn Cg A]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h : y = (1 : ℂ) ⊗ₜ[ℝ] φ :=
      (TensorProduct.isBaseChange ℝ X ℂ).toDualBaseChange.injective hyx
    rwa [h] at hy
  · intro h
    exact ⟨_, h, rfl⟩

/-- The canonical-basis form of real spectral duality. -/
theorem dualAnnihilator_antistableSubspaceIn_eq_stableSubspaceIn_dualMap
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) (A : X →ₗ[ℝ] X) :
    (antistableSubspaceIn Cg A).dualAnnihilator = stableSubspaceIn Cg A.dualMap := by
  exact dualAnnihilator_antistableSubspaceIn_eq_stableSubspaceOfBasisIn_dualMap
    Cg hCg A

/-- The annihilator of the domain-relative detectable subspace is the
domain-relative stabilizable subspace of the dual pair. -/
theorem dualAnnihilator_detectableSubspaceIn
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) :
    (detectableSubspaceIn Cg C A).dualAnnihilator =
      stabilizableSubspaceIn Cg A.dualMap C.dualMap := by
  rw [detectableSubspaceIn, Subspace.dualAnnihilator_inf_eq,
    ← reachableSubspace_dualMap,
    dualAnnihilator_antistableSubspaceIn_eq_stableSubspaceIn_dualMap Cg hCg A]
  rw [stabilizableSubspaceIn, sup_comm]

/-- The annihilator of the domain-relative observer geometry is the dual
controlled-invariant subspace enlarged by the dual stabilizable subspace. -/
theorem conditionedInvariantSubspace_inf_detectableSubspaceIn_dualAnnihilator_eq
    {X Y D : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) :
    (conditionedInvariantSubspace C A (LinearMap.range E) ⊓
        detectableSubspaceIn Cg C A).dualAnnihilator =
      controlledInvariantSubspace A.dualMap C.dualMap (LinearMap.ker E.dualMap) ⊔
        stabilizableSubspaceIn Cg A.dualMap C.dualMap := by
  rw [Subspace.dualAnnihilator_inf_eq,
    conditionedInvariantSubspace_dualAnnihilator_eq C A E,
    dualAnnihilator_detectableSubspaceIn Cg hCg C A]

end LinearMap
