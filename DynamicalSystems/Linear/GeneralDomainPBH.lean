/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GeneralStabilityDomain

/-! # PBH feedback criterion for a general stability domain

The uncontrollable poles of a real pair must already lie in the prescribed
stability domain. A complementary reachable block and pole placement give the
converse: a feedback gain places every closed-loop pole in that domain.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace LinearMap

variable {X U : Type*}
variable [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]

/-- If all uncontrollable eigenvalues lie in a stability domain, a real
state-feedback gain places the entire spectrum there. -/
theorem exists_feedback_isStableIn_of_uncontrollableEigenvalues
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (h : ∀ μ : ℂ, IsUncontrollableEigenvalue A B μ → μ ∈ Cg) :
    ∃ F : X →ₗ[ℝ] U, IsStableIn Cg (A + B.comp F) := by
  classical
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (reachableSubspace A B)
  let W := reachableSubspace A B
  let πW : X →ₗ[ℝ] W := W.projectionOnto Q hQ
  let πQ : X →ₗ[ℝ] Q := Q.projectionOnto W hQ.symm
  let A11 : W →ₗ[ℝ] W := reachableRestrictionA A B
  let B1 : U →ₗ[ℝ] W := reachableRestrictionB A B
  let A12 : Q →ₗ[ℝ] W := πW.comp (A.comp Q.subtype)
  let A22 : Q →ₗ[ℝ] Q := πQ.comp (A.comp Q.subtype)
  have hπWA : ∀ w : W, (W.projectionOnto Q hQ) (A (w : X)) = A11 w := by
    intro w
    have hmem : A (w : X) ∈ W := map_reachableSubspace_le A B ⟨_, w.2, rfl⟩
    rw [show (W.projectionOnto Q hQ) (A (w:X)) = ⟨A (w:X), hmem⟩ from
      Submodule.projectionOnto_apply_of_mem_left hQ hmem]
    apply Subtype.ext
    simp [A11, reachableRestrictionA, LinearMap.restrict_apply]
  have hπWB : ∀ u : U, (W.projectionOnto Q hQ) (B u) = B1 u := by
    intro u
    have hmem : B u ∈ W := range_le_reachableSubspace A B ⟨u, rfl⟩
    rw [show (W.projectionOnto Q hQ) (B u) = ⟨B u, hmem⟩ from
      Submodule.projectionOnto_apply_of_mem_left hQ hmem]
    apply Subtype.ext
    simp [B1, reachableRestrictionB, LinearMap.codRestrict_apply]
  have hπQA : ∀ w : W, (Q.projectionOnto W hQ.symm) (A (w : X)) = 0 := by
    intro w
    rw [Submodule.projectionOnto_apply_eq_zero_iff]
    exact map_reachableSubspace_le A B ⟨_, w.2, rfl⟩
  have hπWw : ∀ w : W, (W.projectionOnto Q hQ) (w : X) = w := by
    intro w
    exact Submodule.projectionOnto_apply_of_mem_left hQ w.2
  have hπWq : ∀ q : Q, (W.projectionOnto Q hQ) (q : X) = 0 := by
    intro q
    exact Submodule.projectionOnto_apply_right hQ q
  have hdecomp : ∀ x : X, ((πW x : X) + (πQ x : X)) = x := by
    intro x
    have hh := Submodule.projection_add_projection_eq_self hQ x
    simpa only [πW, πQ, Submodule.coe_projectionOnto_apply] using hh
  have hπQ_A : πQ.comp A = A22.comp πQ := by
    apply LinearMap.ext
    intro x
    change πQ (A x) = A22 (πQ x)
    calc πQ (A x)
        = πQ (A ((πW x : X) + (πQ x : X))) := by rw [hdecomp]
      _ = πQ (A (πW x : X) + A (πQ x : X)) := by rw [map_add]
      _ = πQ (A (πW x : X)) + πQ (A (πQ x : X)) := by rw [map_add]
      _ = A22 (πQ x) := by
          have hmem : A (πW x : X) ∈ W := map_reachableSubspace_le A B ⟨_, (πW x).2, rfl⟩
          have hz : πQ (A (πW x : X)) = 0 := by
            rw [Submodule.projectionOnto_apply_eq_zero_iff]; exact hmem
          rw [hz, zero_add]; rfl
  have hπQ_B : πQ.comp B = 0 := by
    apply LinearMap.ext
    intro u
    change πQ (B u) = 0
    rw [Submodule.projectionOnto_apply_eq_zero_iff]
    exact range_le_reachableSubspace A B ⟨u, rfl⟩
  have hA22 : IsStableIn Cg A22 := by
    intro μ hμ
    set A22c : (ℂ ⊗[ℝ] Q) →ₗ[ℂ] (ℂ ⊗[ℝ] Q) := A22.baseChange ℂ with hA22c
    have hchar : A22c.charpoly = A22.charpoly.map (algebraMap ℝ ℂ) :=
      LinearMap.charpoly_baseChange A22 ℂ
    have hroot : A22c.charpoly.IsRoot μ := by rw [hchar]; exact hμ
    have hroot' : A22c.dualMap.charpoly.IsRoot μ := by
      rw [charpoly_dualMap_ofField]; exact hroot
    have heig : Module.End.HasEigenvalue A22c.dualMap μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly A22c.dualMap μ).mpr hroot'
    obtain ⟨ξ, hξ⟩ := heig.exists_hasEigenvector
    have hξne : ξ ≠ 0 := hξ.2
    have hξeig : A22c.dualMap ξ = μ • ξ := Module.End.mem_eigenspace_iff.mp hξ.1
    have hξcomp : ξ.comp A22c = μ • ξ := by
      apply LinearMap.ext
      intro v
      change ξ (A22c v) = (μ • ξ) v
      have hh := congrArg (fun (f : (ℂ ⊗[ℝ] Q) →ₗ[ℂ] ℂ) => f v) hξeig
      simpa [LinearMap.dualMap_apply'] using hh
    let η : (ℂ ⊗[ℝ] X) →ₗ[ℂ] ℂ := ξ.comp (πQ.baseChange ℂ)
    have hηne : η ≠ 0 := by
      have hright : (πQ.baseChange ℂ).comp (Q.subtype.baseChange ℂ) = LinearMap.id := by
        rw [← LinearMap.baseChange_comp, Submodule.projectionOnto_comp_subtype,
          LinearMap.baseChange_id]
      have hsurj : Function.Surjective (πQ.baseChange ℂ) := by
        intro y
        exact ⟨(Q.subtype.baseChange ℂ) y, by
          have hh := congrArg (fun f : (ℂ ⊗[ℝ] Q) →ₗ[ℂ] (ℂ ⊗[ℝ] Q) => f y) hright
          simpa using hh⟩
      intro hη0
      apply hξne
      apply LinearMap.ext
      intro y
      change ξ y = 0
      obtain ⟨z, rfl⟩ := hsurj y
      have hz := congrArg (fun f : (ℂ ⊗[ℝ] X) →ₗ[ℂ] ℂ => f z) hη0
      simpa [η, LinearMap.comp_apply] using hz
    have hηA : η.comp (A.baseChange ℂ) = μ • η := by
      have hbase : (πQ.baseChange ℂ).comp (A.baseChange ℂ) =
          (A22.baseChange ℂ).comp (πQ.baseChange ℂ) := by
        have hh := congrArg (fun f : X →ₗ[ℝ] Q => f.baseChange ℂ) hπQ_A
        simpa only [LinearMap.baseChange_comp] using hh
      apply LinearMap.ext
      intro v
      change η ((A.baseChange ℂ) v) = (μ • η) v
      calc η ((A.baseChange ℂ) v)
          = ξ ((πQ.baseChange ℂ) ((A.baseChange ℂ) v)) := rfl
        _ = ξ (((πQ.baseChange ℂ).comp (A.baseChange ℂ)) v) := rfl
        _ = ξ (((A22.baseChange ℂ).comp (πQ.baseChange ℂ)) v) := by rw [hbase]
        _ = ξ ((A22.baseChange ℂ) ((πQ.baseChange ℂ) v)) := rfl
        _ = (ξ.comp (A22.baseChange ℂ)) ((πQ.baseChange ℂ) v) := rfl
        _ = (μ • ξ) ((πQ.baseChange ℂ) v) := by rw [hξcomp]
        _ = (μ • η) v := rfl
    have hηB : η.comp (B.baseChange ℂ) = 0 := by
      have hbase : (πQ.baseChange ℂ).comp (B.baseChange ℂ) = 0 := by
        have hh := congrArg (fun f : U →ₗ[ℝ] Q => f.baseChange ℂ) hπQ_B
        simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_zero] using hh
      rw [show η.comp (B.baseChange ℂ) =
        ξ.comp ((πQ.baseChange ℂ).comp (B.baseChange ℂ)) by rw [LinearMap.comp_assoc]]
      rw [hbase, LinearMap.comp_zero]
    exact h μ ⟨η, hηne, hηA, hηB⟩
  obtain ⟨F1, hF1⟩ := exists_feedback_isStableIn_of_isControllable Cg hCg A11 B1
    (isControllable_reachableRestriction A B)
  refine ⟨F1.comp πW, ?_⟩
  let e := W.prodEquivOfIsCompl Q hQ
  let T' : W × Q →ₗ[ℝ] W × Q := LinearMap.prod
    ((A11 + B1.comp F1).comp (LinearMap.fst ℝ W Q) + A12.comp (LinearMap.snd ℝ W Q))
    (A22.comp (LinearMap.snd ℝ W Q))
  have hconj : e.symm.conj (A + B.comp (F1.comp πW)) = T' := by
    apply LinearMap.ext
    intro p
    obtain ⟨w, q⟩ := p
    rw [LinearEquiv.conj_apply_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply]
    rw [LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl']
    apply Prod.ext
    · apply Subtype.ext
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.prod_apply,
        Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply, T']
      rw [show (W.projectionOnto Q hQ) ((w : X) + (q : X)) = w by
        rw [map_add, hπWw w, hπWq q, add_zero]]
      rw [map_add, map_add, map_add]
      rw [hπWA w]
      rw [show (W.projectionOnto Q hQ) (A (q:X)) = A12 q from rfl]
      rw [hπWB (F1 w)]
      abel_nf
    · apply Subtype.ext
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.prod_apply,
        Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply, T']
      rw [show (W.projectionOnto Q hQ) ((w : X) + (q : X)) = w by
        rw [map_add, hπWw w, hπWq q, add_zero]]
      rw [map_add, map_add, map_add]
      rw [show (Q.projectionOnto W hQ.symm) (A (w:X)) = 0 from hπQA w]
      rw [show (Q.projectionOnto W hQ.symm) (A (q:X)) = A22 q from rfl]
      rw [show (Q.projectionOnto W hQ.symm) (B (F1 w)) = 0 from by
        rw [Submodule.projectionOnto_apply_eq_zero_iff]
        exact range_le_reachableSubspace A B ⟨_, rfl⟩]
      rw [zero_add, add_zero]
  refine fun μ hμ => ?_
  have hchar : (A + B.comp (F1.comp πW)).charpoly = T'.charpoly := by
    rw [← LinearEquiv.charpoly_conj e.symm (A + B.comp (F1.comp πW)), hconj]
  have hTchar : T'.charpoly = (A11 + B1.comp F1).charpoly * A22.charpoly :=
    charpoly_prodMap_of_lower_zero _ _ _
  rw [hchar, hTchar] at hμ
  simp only [Polynomial.map_mul, Polynomial.eval_mul] at hμ
  rcases mul_eq_zero.mp hμ with h1 | h2
  · exact hF1 μ h1
  · exact hA22 μ h2


end LinearMap
