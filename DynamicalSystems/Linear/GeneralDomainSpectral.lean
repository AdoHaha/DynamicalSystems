/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GeneralStabilityDomain
public import DynamicalSystems.Linear.DynamicFeedback

/-! # Spectral decomposition for a general stability domain -/

@[expose] public section

noncomputable section

namespace LinearMap

variable {X U : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]

private theorem star_mem_complexSpectralSubspaceOfBasis
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) (A : X →ₗ[ℝ] X)
    {z : Fin (Module.finrank ℝ X) → ℂ}
    (hz : z ∈ complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A
      (fun μ ↦ μ ∈ Cg)) :
    star z ∈ complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A
      (fun μ ↦ μ ∈ Cg) := by
  exact star_mem_iSup_maxGenEigenspace A (fun μ ↦ μ ∈ Cg) hCg.2 hz

private theorem star_mem_complementSpectralSubspaceOfBasis
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) (A : X →ₗ[ℝ] X)
    {z : Fin (Module.finrank ℝ X) → ℂ}
    (hz : z ∈ complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A
      (fun μ ↦ μ ∉ Cg)) :
    star z ∈ complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A
      (fun μ ↦ μ ∉ Cg) := by
  exact star_mem_iSup_maxGenEigenspace A (fun μ ↦ μ ∉ Cg)
    (fun μ hμ hstar ↦ hμ (by simpa only [star_star] using hCg.2 (star μ) hstar)) hz

/-- The `Cg` stable and antistable spectral subspaces span the real state space. -/
theorem stableSubspaceIn_sup_antistableSubspaceIn_eq_top
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) (A : X →ₗ[ℝ] X) :
    stableSubspaceIn Cg A ⊔ antistableSubspaceIn Cg A = ⊤ := by
  have hcomplex :
      complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∈ Cg) ⊔
        complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∉ Cg) = ⊤ := by
    let f : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℂ]
        (Fin (Module.finrank ℝ X) → ℂ) :=
      Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))
    have htop : (⨆ μ : ℂ, Module.End.maxGenEigenspace f μ) = ⊤ :=
      Module.End.iSup_maxGenEigenspace_eq_top f
    apply le_antisymm le_top
    rw [← htop]
    apply iSup_le
    intro μ
    by_cases hμ : μ ∈ Cg
    · refine le_sup_of_le_left ?_
      change Module.End.maxGenEigenspace f μ ≤
        complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∈ Cg)
      rw [complexSpectralSubspaceOfBasis]
      exact le_iSup (fun μ' : {μ : ℂ // μ ∈ Cg} ↦
        Module.End.maxGenEigenspace f μ'.1) ⟨μ, hμ⟩
    · refine le_sup_of_le_right ?_
      change Module.End.maxGenEigenspace f μ ≤
        complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∉ Cg)
      rw [complexSpectralSubspaceOfBasis]
      exact le_iSup (fun μ' : {μ : ℂ // μ ∉ Cg} ↦
        Module.End.maxGenEigenspace f μ'.1) ⟨μ, hμ⟩
  apply le_antisymm le_top
  intro x _
  set φ : X →ₗ[ℝ] (Fin (Module.finrank ℝ X) → ℂ) :=
    ofRealPi.comp (Module.finBasis ℝ X).equivFun.toLinearMap with hφ
  have hmem : φ x ∈
      complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∈ Cg) ⊔
        complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∉ Cg) := by
    rw [hcomplex]; exact Submodule.mem_top
  obtain ⟨g, hg, b, hb, hgb⟩ := Submodule.mem_sup.mp hmem
  have hstar_g := star_mem_complexSpectralSubspaceOfBasis Cg hCg A hg
  have hstar_b := star_mem_complementSpectralSubspaceOfBasis Cg hCg A hb
  set g' : Fin (Module.finrank ℝ X) → ℂ := (1/2 : ℂ) • (g + star g) with hg'
  set b' : Fin (Module.finrank ℝ X) → ℂ := (1/2 : ℂ) • (b + star b) with hb'
  have hg'mem : g' ∈
      complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∈ Cg) :=
    Submodule.smul_mem _ _ (Submodule.add_mem _ hg hstar_g)
  have hb'mem : b' ∈
      complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∉ Cg) :=
    Submodule.smul_mem _ _ (Submodule.add_mem _ hb hstar_b)
  have hz_fixed : star (φ x) = φ x := by
    rw [hφ]
    ext i
    simp [ofRealPi]
  have hg'fix : star g' = g' := by
    rw [hg']
    ext i
    simp only [Pi.star_apply, Pi.smul_apply, Pi.add_apply]
    rw [smul_eq_mul, star_mul, star_add, star_star]
    rw [show star (1/2 : ℂ) = 1/2 by simp]
    ring
  have hb'fix : star b' = b' := by
    rw [hb']
    ext i
    simp only [Pi.star_apply, Pi.smul_apply, Pi.add_apply]
    rw [smul_eq_mul, star_mul, star_add, star_star]
    rw [show star (1/2 : ℂ) = 1/2 by simp]
    ring
  have hsum : g' + b' = φ x := by
    rw [hg', hb', ← smul_add]
    rw [show (g + star g) + (b + star b) = (g + b) + star (g + b) by
      rw [star_add]; abel]
    rw [hgb, hz_fixed]
    module
  obtain ⟨ag, hag⟩ := exists_ofRealPi_of_star_eq hg'fix
  obtain ⟨ab, hab⟩ := exists_ofRealPi_of_star_eq hb'fix
  have hφin : ∀ a : Fin (Module.finrank ℝ X) → ℝ,
      φ ((Module.finBasis ℝ X).equivFun.symm a) = ofRealPi a := by
    intro a
    rw [hφ]
    simp only [LinearMap.comp_apply]
    congr 1
    exact (Module.finBasis ℝ X).equivFun.apply_symm_apply a
  have hg'pre : (Module.finBasis ℝ X).equivFun.symm ag ∈ stableSubspaceIn Cg A := by
    rw [stableSubspaceIn, Submodule.mem_comap, Submodule.restrictScalars_mem, hφin, hag]
    exact hg'mem
  have hb'pre : (Module.finBasis ℝ X).equivFun.symm ab ∈ antistableSubspaceIn Cg A := by
    rw [antistableSubspaceIn, Submodule.mem_comap, Submodule.restrictScalars_mem,
      hφin, hab]
    exact hb'mem
  rw [Submodule.mem_sup]
  refine ⟨_, hg'pre, _, hb'pre, ?_⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    rw [hφ] at hab
    simp only [LinearMap.comp_apply] at hab
    have hfun : (Module.finBasis ℝ X).equivFun a = (Module.finBasis ℝ X).equivFun b := by
      funext i
      have hi := congrFun hab i
      exact_mod_cast (by simpa [ofRealPi] using hi)
    exact (Module.finBasis ℝ X).equivFun.injective hfun
  apply hinj
  rw [map_add, hφin, hφin, hag, hab, hsum]

/-- The spectral subspaces indexed by a domain and its complement are disjoint. -/
theorem disjoint_stableSubspaceIn_antistableSubspaceIn
    (Cg : Set ℂ) (A : X →ₗ[ℝ] X) :
    Disjoint (stableSubspaceIn Cg A) (antistableSubspaceIn Cg A) := by
  let F := Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))
  have hf : iSupIndep (Module.End.maxGenEigenspace F) :=
    Module.End.independent_maxGenEigenspace F
  have hd := hf.disjoint_biSup_biSup (s := Cg) (t := Cgᶜ) (by
    rw [Set.disjoint_left]
    intro μ h1 h2
    exact h2 h1)
  have hc : complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A
      (fun μ ↦ μ ∈ Cg) ⊓ complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A
      (fun μ ↦ μ ∉ Cg) = ⊥ := by
    apply disjoint_iff.mp
    simpa only [complexSpectralSubspaceOfBasis, iSup_subtype, Set.mem_ofPred_eq,
      Set.mem_compl_iff, F, hurwitzMatrix] using hd
  rw [disjoint_iff, stableSubspaceIn, antistableSubspaceIn, ← Submodule.comap_inf,
    ← Submodule.restrictScalars_inf, hc, Submodule.restrictScalars_bot, Submodule.comap_bot,
    LinearMap.ker_eq_bot]
  exact ofRealPi_injective.comp (Module.finBasis ℝ X).equivFun.injective

/-- The two spectral subspaces form a direct sum over the reals. -/
theorem isCompl_stableSubspaceIn_antistableSubspaceIn
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) (A : X →ₗ[ℝ] X) :
    IsCompl (stableSubspaceIn Cg A) (antistableSubspaceIn Cg A) :=
  ⟨disjoint_stableSubspaceIn_antistableSubspaceIn Cg A,
    codisjoint_iff.mpr (stableSubspaceIn_sup_antistableSubspaceIn_eq_top Cg hCg A)⟩

private theorem antistableComplexSubspace_eq_bot_of_isStableIn
    (Cg : Set ℂ) (A : X →ₗ[ℝ] X) (hA : IsStableIn Cg A) :
    complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∉ Cg) = ⊥ := by
  rw [complexSpectralSubspaceOfBasis, iSup_eq_bot]
  intro μ
  rw [Submodule.eq_bot_iff]
  intro z hz
  by_contra hz0
  have heig := hasEigenvalue_of_mem_maxGenEigenspace hz hz0
  have hroot : (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))).charpoly.IsRoot μ.1 :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp heig
  rw [charpoly_hurwitzMatrix_map_eq] at hroot
  exact μ.2 (hA μ.1 hroot)

/-- A stable operator has no antistable spectral states. -/
theorem antistableSubspaceIn_eq_bot_of_isStableIn
    (Cg : Set ℂ) (A : X →ₗ[ℝ] X) (hA : IsStableIn Cg A) :
    antistableSubspaceIn Cg A = ⊥ := by
  rw [antistableSubspaceIn, antistableComplexSubspace_eq_bot_of_isStableIn Cg A hA,
    Submodule.restrictScalars_bot, Submodule.comap_bot, LinearMap.ker_eq_bot]
  exact ofRealPi_injective.comp (Module.finBasis ℝ X).equivFun.injective

/-- An operator whose spectrum lies in `Cg` has every state in its stable
spectral subspace. -/
theorem stableSubspaceIn_eq_top_of_isStableIn
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (hA : IsStableIn Cg A) :
    stableSubspaceIn Cg A = ⊤ := by
  have hsup := stableSubspaceIn_sup_antistableSubspaceIn_eq_top Cg hCg A
  rw [antistableSubspaceIn_eq_bot_of_isStableIn Cg A hA, sup_bot_eq] at hsup
  exact hsup

/-- Vanishing of the real antistable subspace forces the complex antistable
spectral sum to vanish. -/
private theorem antistableComplexSubspace_eq_bot_of_antistableSubspaceIn_eq_bot
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) (A : X →ₗ[ℝ] X)
    (h : antistableSubspaceIn Cg A = ⊥) :
    complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∉ Cg) = ⊥ := by
  let V := complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A (fun μ ↦ μ ∉ Cg)
  have hstar : ∀ v ∈ V, star v ∈ V :=
    fun v hv ↦ star_mem_complementSpectralSubspaceOfBasis Cg hCg A hv
  have hspan := span_inter_range_ofRealPi_eq_of_star_mem V hstar
  change V = ⊥
  rw [← hspan]
  apply le_antisymm ?_ bot_le
  rw [Submodule.span_le]
  rintro z ⟨hz, a, rfl⟩
  have hx : (Module.finBasis ℝ X).equivFun.symm a ∈ antistableSubspaceIn Cg A := by
    rw [antistableSubspaceIn, Submodule.mem_comap, Submodule.restrictScalars_mem]
    simp only [LinearMap.comp_apply]
    change ofRealPi ((Module.finBasis ℝ X).equivFun
      ((Module.finBasis ℝ X).equivFun.symm a)) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    exact hz
  rw [h, Submodule.mem_bot] at hx
  have ha : a = 0 := by
    rw [← (Module.finBasis ℝ X).equivFun.apply_symm_apply a, hx, map_zero]
  simp [ha]

/-- If the antistable spectral subspace vanishes, the spectrum lies in `Cg`. -/
theorem isStableIn_of_antistableSubspaceIn_eq_bot
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (h : antistableSubspaceIn Cg A = ⊥) :
    IsStableIn Cg A := by
  intro μ hμ
  by_contra hμCg
  have hUc : complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A
      (fun ν ↦ ν ∉ Cg) ≠ ⊥ := by
    intro hbot
    have heig : Module.End.HasEigenvalue
        (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr (by
        rw [charpoly_hurwitzMatrix_map_eq]; exact hμ)
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have hv0 : v ≠ 0 := hv.2
    have hveig : v ∈ Module.End.maxGenEigenspace
        (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) μ := by
      rw [Module.End.mem_maxGenEigenspace]
      refine ⟨1, ?_⟩
      rw [pow_one]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        Module.End.mem_eigenspace_iff.mp hv.1, sub_self]
    have hmem : v ∈ complexSpectralSubspaceOfBasis (Module.finBasis ℝ X) A
        (fun ν ↦ ν ∉ Cg) := by
      rw [complexSpectralSubspaceOfBasis]
      exact Submodule.mem_iSup_of_mem ⟨μ, hμCg⟩ hveig
    exact hv0 (by rw [hbot] at hmem; exact hmem)
  exact hUc (antistableComplexSubspace_eq_bot_of_antistableSubspaceIn_eq_bot Cg hCg A h)

/-- The stable spectral subspace of an invariant restriction maps into the
stable spectral subspace of the ambient operator. -/
theorem map_stableSubspaceIn_restrict_le (Cg : Set ℂ)
    (A : X →ₗ[ℝ] X) (W : Submodule ℝ X) (hW : ∀ x ∈ W, A x ∈ W) :
    Submodule.map W.subtype (stableSubspaceIn Cg (A.restrict hW)) ≤
      stableSubspaceIn Cg A := by
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  rw [Submodule.mem_comap]
  rw [stableSubspaceIn, Submodule.mem_comap, Submodule.restrictScalars_mem] at hy ⊢
  simp only [LinearMap.comp_apply] at hy ⊢
  change ofRealPi ((Module.finBasis ℝ X).equivFun (W.subtype y)) ∈ _
  rw [← ofRealPi_equivFun_toLin'_apply W.subtype y]
  exact map_iSup_maxGenEigenspace_restrict_le A W hW (fun μ ↦ μ ∈ Cg)
    ⟨_, hy, rfl⟩

/-- The antistable spectral subspace of an invariant restriction maps into the
antistable spectral subspace of the ambient operator. -/
theorem map_antistableSubspaceIn_restrict_le (Cg : Set ℂ)
    (A : X →ₗ[ℝ] X) (W : Submodule ℝ X) (hW : ∀ x ∈ W, A x ∈ W) :
    Submodule.map W.subtype (antistableSubspaceIn Cg (A.restrict hW)) ≤
      antistableSubspaceIn Cg A := by
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  rw [Submodule.mem_comap]
  rw [antistableSubspaceIn, Submodule.mem_comap, Submodule.restrictScalars_mem] at hy ⊢
  simp only [LinearMap.comp_apply] at hy ⊢
  change ofRealPi ((Module.finBasis ℝ X).equivFun (W.subtype y)) ∈ _
  rw [← ofRealPi_equivFun_toLin'_apply W.subtype y]
  exact map_iSup_maxGenEigenspace_restrict_le A W hW (fun μ ↦ μ ∉ Cg)
    ⟨_, hy, rfl⟩

/-- The trace of the ambient stable subspace on an invariant subspace comes
from the stable subspace of the restricted operator. -/
theorem stableSubspaceIn_inf_le_map_stableSubspaceIn_restrict
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (W : Submodule ℝ X) (hW : ∀ x ∈ W, A x ∈ W) :
    stableSubspaceIn Cg A ⊓ W ≤
      Submodule.map W.subtype (stableSubspaceIn Cg (A.restrict hW)) := by
  intro x hx
  obtain ⟨hxA, hxW⟩ := hx
  let xW : W := ⟨x, hxW⟩
  have hsup := stableSubspaceIn_sup_antistableSubspaceIn_eq_top Cg hCg (A.restrict hW)
  have hxmem : xW ∈ stableSubspaceIn Cg (A.restrict hW) ⊔
      antistableSubspaceIn Cg (A.restrict hW) := by
    rw [hsup]; trivial
  obtain ⟨g, hg, b, hb, hgb⟩ := Submodule.mem_sup.mp hxmem
  refine ⟨g, hg, ?_⟩
  have hgX : (g : X) ∈ stableSubspaceIn Cg A :=
    map_stableSubspaceIn_restrict_le Cg A W hW ⟨g, hg, rfl⟩
  have hbX : (b : X) ∈ antistableSubspaceIn Cg A :=
    map_antistableSubspaceIn_restrict_le Cg A W hW ⟨b, hb, rfl⟩
  have hb_eq : (b : X) = x - (g : X) := by
    have h := congrArg (Subtype.val) hgb
    simp only [Submodule.coe_add] at h
    rw [eq_sub_iff_add_eq, add_comm]
    exact h
  have hbH : (b : X) ∈ stableSubspaceIn Cg A := by
    rw [hb_eq]
    exact (stableSubspaceIn Cg A).sub_mem hxA hgX
  have hb0 : (b : X) = 0 := by
    have hmem : (b : X) ∈ stableSubspaceIn Cg A ⊓ antistableSubspaceIn Cg A :=
      ⟨hbH, hbX⟩
    rw [disjoint_iff.mp (disjoint_stableSubspaceIn_antistableSubspaceIn Cg A),
      Submodule.mem_bot] at hmem
    exact hmem
  have hgx : (g : X) = x := by
    have h := congrArg (Subtype.val) hgb
    simp only [Submodule.coe_add] at h
    rw [hb0, add_zero] at h
    exact h
  exact hgx

/-- The stable subspace of the restricted operator is the trace of the
ambient stable subspace. -/
theorem comap_stableSubspaceIn_le_stableSubspaceIn_restrict
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (W : Submodule ℝ X) (hW : ∀ x ∈ W, A x ∈ W) :
    (stableSubspaceIn Cg A).comap W.subtype ≤
      stableSubspaceIn Cg (A.restrict hW) := by
  intro x hx
  rw [Submodule.mem_comap] at hx
  obtain ⟨g, hg, hgx⟩ : ∃ g ∈ stableSubspaceIn Cg (A.restrict hW),
      (g : X) = (x : X) :=
    stableSubspaceIn_inf_le_map_stableSubspaceIn_restrict Cg hCg A W hW ⟨hx, x.2⟩
  rw [← Subtype.ext hgx]
  exact hg

/-- Restriction preserves the domain-relative stabilizable subspace when the
invariant subspace contains the image of the input map. -/
theorem stabilizableSubspaceIn_restrict_eq (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (W : Submodule ℝ X) (hW : ∀ x ∈ W, A x ∈ W) (hB : LinearMap.range B ≤ W) :
    stabilizableSubspaceIn Cg (A.restrict hW)
        (B.codRestrict W (fun u ↦ hB (LinearMap.mem_range_self B u))) =
      (stabilizableSubspaceIn Cg A B).comap W.subtype := by
  apply le_antisymm
  · intro x hx
    rw [stabilizableSubspaceIn, Submodule.mem_sup] at hx
    obtain ⟨g, hg, r, hr, hgr⟩ := hx
    rw [Submodule.mem_comap, stabilizableSubspaceIn, Submodule.mem_sup]
    refine ⟨(g : X), map_stableSubspaceIn_restrict_le Cg A W hW ⟨g, hg, rfl⟩,
      (r : X), ?_, ?_⟩
    · rw [← LinearSystem.map_reachableSubspace_restrict_eq A B W hW hB]
      exact ⟨r, hr, rfl⟩
    · exact congrArg (Subtype.val) hgr
  · intro x hx
    rw [Submodule.mem_comap, stabilizableSubspaceIn, Submodule.mem_sup] at hx
    obtain ⟨g, hg, r, hr, hgr⟩ := hx
    have hRW : LinearMap.reachableSubspace A B ≤ W :=
      LinearMap.reachableSubspace_le A B hB (by
        rintro y ⟨w, hw, rfl⟩; exact hW w hw)
    have hrW : r ∈ W := hRW hr
    have hgW : g ∈ W := by
      have heq : g = (x : X) - r := eq_sub_iff_add_eq.mpr hgr
      rw [heq]
      exact W.sub_mem x.2 hrW
    have hr' : (⟨r, hrW⟩ : W) ∈ reachableSubspace (A.restrict hW)
        (B.codRestrict W (fun u ↦ hB (LinearMap.mem_range_self B u))) :=
      LinearSystem.comap_reachableSubspace_le_reachableSubspace_restrict A B W hW hB
        (by rw [Submodule.mem_comap]; exact hr)
    have hg' : (⟨g, hgW⟩ : W) ∈ stableSubspaceIn Cg (A.restrict hW) :=
      comap_stableSubspaceIn_le_stableSubspaceIn_restrict Cg hCg A W hW
        (by rw [Submodule.mem_comap]; exact hg)
    rw [stabilizableSubspaceIn, Submodule.mem_sup]
    refine ⟨⟨g, hgW⟩, hg', ⟨r, hrW⟩, hr', ?_⟩
    apply Subtype.ext
    rw [Submodule.coe_add]; exact hgr

/-- The restriction of an operator to its `Cg` stable spectral subspace has
all poles in `Cg`. -/
theorem isStableIn_restrict_stableSubspaceIn
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) (A : X →ₗ[ℝ] X) :
    IsStableIn Cg (A.restrict (fun x hx ↦
      map_stableSubspaceIn_le Cg A ⟨x, hx, rfl⟩)) := by
  let H := stableSubspaceIn Cg A
  let hHinv : ∀ x ∈ H, A x ∈ H := fun x hx ↦
    map_stableSubspaceIn_le Cg A ⟨x, hx, rfl⟩
  have htop : stableSubspaceIn Cg (A.restrict hHinv) = ⊤ := by
    apply le_antisymm le_top
    intro x _
    exact comap_stableSubspaceIn_le_stableSubspaceIn_restrict Cg hCg A H hHinv
      (by rw [Submodule.mem_comap]; exact x.2)
  have hbot : antistableSubspaceIn Cg (A.restrict hHinv) = ⊥ := by
    have hdisj := disjoint_iff.mp (disjoint_stableSubspaceIn_antistableSubspaceIn Cg
      (A.restrict hHinv))
    rw [htop, top_inf_eq] at hdisj
    exact hdisj
  exact isStableIn_of_antistableSubspaceIn_eq_bot Cg hCg (A.restrict hHinv) hbot

end LinearMap
