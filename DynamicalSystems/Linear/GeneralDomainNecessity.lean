/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GeneralDomainSpectral

/-! # Spectral necessity for a general stability domain

The closed-loop transfer poles constrain its reachable, observable part.  The
first step is to show that an antistable direction of an invariant subspace
must lie in the quotient kernel whenever the induced quotient has spectrum in
the stability domain.
-/

@[expose] public section

noncomputable section

namespace LinearMap

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- An intertwiner carries antistable spectral directions to antistable
spectral directions for the codomain operator. -/
theorem map_antistableSubspaceIn_intertwiner_le (Cg : Set ℂ)
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

/-- The stable spectral subspace is functorial for real intertwiners. -/
theorem map_stableSubspaceIn_intertwiner_le (Cg : Set ℂ)
    (A : X →ₗ[ℝ] X) (T : Y →ₗ[ℝ] Y) (q : X →ₗ[ℝ] Y)
    (hq : q.comp A = T.comp q) :
    Submodule.map q (stableSubspaceIn Cg A) ≤ stableSubspaceIn Cg T := by
  have hX : stableSubspaceIn Cg A = antistableSubspaceIn Cgᶜ A := by
    simp [stableSubspaceIn, antistableSubspaceIn]
  have hY : stableSubspaceIn Cg T = antistableSubspaceIn Cgᶜ T := by
    simp [stableSubspaceIn, antistableSubspaceIn]
  rw [hX, hY]
  exact map_antistableSubspaceIn_intertwiner_le Cgᶜ A T q hq

/-- If an invariant quotient is spectrally stable, its kernel contains every
antistable spectral direction of the original operator. -/
theorem antistableSubspaceIn_le_of_isStableIn_quotient (Cg : Set ℂ)
    (A : X →ₗ[ℝ] X) (V : Submodule ℝ X)
    (hV : ∀ x ∈ V, A x ∈ V)
    (hQ : IsStableIn Cg (Submodule.mapQ V V A (fun x hx ↦ hV x hx))) :
    antistableSubspaceIn Cg A ≤ V := by
  have _ : IsClosed (V : Set X) := V.closed_of_finiteDimensional
  let T := Submodule.mapQ V V A (fun x hx ↦ hV x hx)
  have hq : V.mkQ.comp A = T.comp V.mkQ := by
    simpa only [T] using
      (Submodule.mapQ_mkQ (p := V) (q := V) (f := A)
        (h := fun x hx ↦ hV x hx)).symm
  have hmap : Submodule.map V.mkQ (antistableSubspaceIn Cg A) ≤
      antistableSubspaceIn Cg T :=
    map_antistableSubspaceIn_intertwiner_le Cg A (T := T) (q := V.mkQ) hq
  rw [antistableSubspaceIn_eq_bot_of_isStableIn Cg T hQ] at hmap
  intro x hx
  have hzero : V.mkQ x = 0 := by
    simpa using hmap ⟨x, hx, rfl⟩
  rwa [← Submodule.ker_mkQ V, LinearMap.mem_ker]

/-- A quotient is stable when its kernel contains all antistable spectral
directions of the ambient operator. -/
theorem isStableIn_quotient_of_antistableSubspaceIn_le
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (V : Submodule ℝ X)
    (hV : ∀ x ∈ V, A x ∈ V)
    (hAnti : antistableSubspaceIn Cg A ≤ V) :
    IsStableIn Cg (Submodule.mapQ V V A (fun x hx ↦ hV x hx)) := by
  have _ : IsClosed (V : Set X) := V.closed_of_finiteDimensional
  let T := Submodule.mapQ V V A (fun x hx ↦ hV x hx)
  have hq : V.mkQ.comp A = T.comp V.mkQ := by
    simpa only [T] using
      (Submodule.mapQ_mkQ (p := V) (q := V) (f := A)
        (h := fun x hx ↦ hV x hx)).symm
  have hspan : stableSubspaceIn Cg A ⊔ V = ⊤ := by
    apply le_antisymm le_top
    calc ⊤ = stableSubspaceIn Cg A ⊔ antistableSubspaceIn Cg A :=
          (stableSubspaceIn_sup_antistableSubspaceIn_eq_top Cg hCg A).symm
      _ ≤ stableSubspaceIn Cg A ⊔ V := sup_le_sup_left hAnti _
  have hsurj : Submodule.map V.mkQ (stableSubspaceIn Cg A) = ⊤ := by
    apply le_antisymm le_top
    intro y _
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective V y
    have hx : x ∈ stableSubspaceIn Cg A ⊔ V := by rw [hspan]; trivial
    obtain ⟨g, hg, v, hv, hgv⟩ := Submodule.mem_sup.mp hx
    have hv0 : V.mkQ v = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hv
    refine ⟨g, hg, ?_⟩
    rw [← hgv, map_add, hv0, add_zero]
  have hstable : stableSubspaceIn Cg T = ⊤ := by
    apply le_antisymm le_top
    calc ⊤ = Submodule.map V.mkQ (stableSubspaceIn Cg A) := hsurj.symm
      _ ≤ stableSubspaceIn Cg T :=
        map_stableSubspaceIn_intertwiner_le Cg A T V.mkQ hq
  have hantiT : antistableSubspaceIn Cg T = ⊥ := by
    have hd := disjoint_iff.mp (disjoint_stableSubspaceIn_antistableSubspaceIn Cg T)
    rw [hstable, top_inf_eq] at hd
    exact hd
  exact isStableIn_of_antistableSubspaceIn_eq_bot Cg hCg T hantiT

/-- If a state has stable image in an invariant quotient, then it differs
from a stable state by an element of the quotient kernel. -/
theorem mem_sup_stableSubspaceIn_of_stable_quotient
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (T : Y →ₗ[ℝ] Y) (q : X →ₗ[ℝ] Y)
    (hq : q.comp A = T.comp q) (V : Submodule ℝ X)
    (hker : LinearMap.ker q ≤ V) (x : X)
    (hx : q x ∈ stableSubspaceIn Cg T) :
    x ∈ stableSubspaceIn Cg A ⊔ V := by
  have hsplit : x ∈ stableSubspaceIn Cg A ⊔ antistableSubspaceIn Cg A := by
    rw [stableSubspaceIn_sup_antistableSubspaceIn_eq_top Cg hCg A]
    trivial
  obtain ⟨g, hg, b, hb, hgb⟩ := Submodule.mem_sup.mp hsplit
  have hqg : q g ∈ stableSubspaceIn Cg T :=
    map_stableSubspaceIn_intertwiner_le Cg A T q hq ⟨g, hg, rfl⟩
  have hqb : q b ∈ antistableSubspaceIn Cg T :=
    map_antistableSubspaceIn_intertwiner_le Cg A T q hq ⟨b, hb, rfl⟩
  have hqbS : q b ∈ stableSubspaceIn Cg T := by
    have heq : q b = q x - q g := by
      rw [← hgb, map_add, add_sub_cancel_left]
    rw [heq]
    exact (stableSubspaceIn Cg T).sub_mem hx hqg
  have hqb0 : q b = 0 := by
    have hboth : q b ∈ stableSubspaceIn Cg T ⊓ antistableSubspaceIn Cg T :=
      ⟨hqbS, hqb⟩
    rw [disjoint_iff.mp (disjoint_stableSubspaceIn_antistableSubspaceIn Cg T),
      Submodule.mem_bot] at hboth
    exact hboth
  have hbV : b ∈ V := hker (LinearMap.mem_ker.mpr hqb0)
  exact Submodule.mem_sup.mpr ⟨g, hg, b, hbV, hgb⟩

/-- If every reachable antistable state is unobservable, every reachable
state is the sum of a stable and an unobservable state. -/
theorem reachable_le_stableSubspaceIn_sup_unobservable_of_antistable_le
    {D Z : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hbad : reachableSubspace A E ⊓ antistableSubspaceIn Cg A ≤
      unobservableSubspace H A) :
    reachableSubspace A E ≤
      stableSubspaceIn Cg A ⊔ unobservableSubspace H A := by
  let R : Submodule ℝ X := reachableSubspace A E
  have hR : ∀ x ∈ R, A x ∈ R := fun x hx ↦
    map_reachableSubspace_le A E ⟨x, hx, rfl⟩
  intro x hx
  let y : R := ⟨x, hx⟩
  have hsplit : y ∈ stableSubspaceIn Cg (A.restrict hR) ⊔
      antistableSubspaceIn Cg (A.restrict hR) := by
    rw [stableSubspaceIn_sup_antistableSubspaceIn_eq_top Cg hCg (A.restrict hR)]
    trivial
  obtain ⟨g, hg, b, hb, hgb⟩ := Submodule.mem_sup.mp hsplit
  have hgA : (g : X) ∈ stableSubspaceIn Cg A :=
    map_stableSubspaceIn_restrict_le Cg A R hR ⟨g, hg, rfl⟩
  have hbA : (b : X) ∈ antistableSubspaceIn Cg A :=
    map_antistableSubspaceIn_restrict_le Cg A R hR ⟨b, hb, rfl⟩
  have hbN : (b : X) ∈ unobservableSubspace H A := hbad ⟨b.2, hbA⟩
  exact Submodule.mem_sup.mpr ⟨(g : X), hgA, (b : X), hbN,
    congrArg (Subtype.val) hgb⟩

/-- The antistable part of an invariant subspace is the trace of the ambient
antistable part.  This is the complement-domain counterpart of the stable
restriction-transport theorem. -/
theorem antistableSubspaceIn_inf_le_map_antistableSubspaceIn_restrict
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (W : Submodule ℝ X) (hW : ∀ x ∈ W, A x ∈ W) :
    antistableSubspaceIn Cg A ⊓ W ≤
      Submodule.map W.subtype (antistableSubspaceIn Cg (A.restrict hW)) := by
  intro x hx
  obtain ⟨hxA, hxW⟩ := hx
  let xW : W := ⟨x, hxW⟩
  have hsup := stableSubspaceIn_sup_antistableSubspaceIn_eq_top Cg hCg (A.restrict hW)
  have hxmem : xW ∈ stableSubspaceIn Cg (A.restrict hW) ⊔
      antistableSubspaceIn Cg (A.restrict hW) := by
    rw [hsup]; trivial
  obtain ⟨g, hg, b, hb, hgb⟩ := Submodule.mem_sup.mp hxmem
  refine ⟨b, hb, ?_⟩
  have hgX : (g : X) ∈ stableSubspaceIn Cg A :=
    map_stableSubspaceIn_restrict_le Cg A W hW ⟨g, hg, rfl⟩
  have hbX : (b : X) ∈ antistableSubspaceIn Cg A :=
    map_antistableSubspaceIn_restrict_le Cg A W hW ⟨b, hb, rfl⟩
  have hg_eq : (g : X) = x - (b : X) := by
    have h := congrArg (Subtype.val) hgb
    simp only [Submodule.coe_add] at h
    exact eq_sub_iff_add_eq.mpr h
  have hgA : (g : X) ∈ antistableSubspaceIn Cg A := by
    rw [hg_eq]
    exact (antistableSubspaceIn Cg A).sub_mem hxA hbX
  have hg0 : (g : X) = 0 := by
    have hmem : (g : X) ∈ stableSubspaceIn Cg A ⊓ antistableSubspaceIn Cg A :=
      ⟨hgX, hgA⟩
    rw [disjoint_iff.mp (disjoint_stableSubspaceIn_antistableSubspaceIn Cg A),
      Submodule.mem_bot] at hmem
    exact hmem
  have hbx : (b : X) = x := by
    have h := congrArg (Subtype.val) hgb
    simp only [Submodule.coe_add] at h
    rw [hg0, zero_add] at h
    exact h
  exact hbx

/-- Stable poles of a channel force every reachable antistable mode to be
unobservable.  This is the spectral necessity at the channel level. -/
theorem reachable_inf_antistableSubspaceIn_le_unobservable_of_polesIn
    {D Z : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hPole : LinearSystem.MinimalRealizationAllChannelsPolesIn Cg A E H) :
    reachableSubspace A E ⊓ antistableSubspaceIn Cg A ≤
      unobservableSubspace H A := by
  let R : Submodule ℝ X := reachableSubspace A E
  let I : Submodule ℝ R := reachableIntersection A E H
  let AR : R →ₗ[ℝ] R := reachableRestrictionA A E
  let M := controllableObservableRealization A E H 0
  have hM : IsStableIn Cg M.A :=
    (LinearSystem.minimalRealizationAllChannelsPolesIn_iff_spectrum Cg A E H).mp hPole
  have hI : ∀ x ∈ I, AR x ∈ I := fun x hx ↦
    map_reachableIntersection_le A E H ⟨x, hx, rfl⟩
  have hanti : antistableSubspaceIn Cg AR ≤ I :=
    antistableSubspaceIn_le_of_isStableIn_quotient Cg AR I hI hM
  have hR : ∀ x ∈ R, A x ∈ R := fun x hx ↦
    map_reachableSubspace_le A E ⟨x, hx, rfl⟩
  intro x hx
  have hx' : x ∈ antistableSubspaceIn Cg A ⊓ R := ⟨hx.2, hx.1⟩
  obtain ⟨y, hy, hyx⟩ :=
    antistableSubspaceIn_inf_le_map_antistableSubspaceIn_restrict Cg hCg A R hR hx'
  have hyI : y ∈ I := hanti hy
  have hxN : x ∈ reachableSubspace A E ⊓ unobservableSubspace H A := by
    have hyN : (y : X) ∈ reachableSubspace A E ⊓ unobservableSubspace H A := hyI
    rw [← hyx]
    exact hyN
  exact hxN.2

/-- Conversely, if every reachable antistable mode is unobservable, then all
reduced transfer poles lie in the chosen stability domain. -/
theorem polesIn_of_reachable_inf_antistableSubspaceIn_le_unobservable
    {D Z : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : reachableSubspace A E ⊓ antistableSubspaceIn Cg A ≤
      unobservableSubspace H A) :
    LinearSystem.MinimalRealizationAllChannelsPolesIn Cg A E H := by
  let R : Submodule ℝ X := reachableSubspace A E
  let I : Submodule ℝ R := reachableIntersection A E H
  let AR : R →ₗ[ℝ] R := reachableRestrictionA A E
  have hR : ∀ x ∈ R, A x ∈ R := fun x hx ↦
    map_reachableSubspace_le A E ⟨x, hx, rfl⟩
  have hI : ∀ x ∈ I, AR x ∈ I := fun x hx ↦
    map_reachableIntersection_le A E H ⟨x, hx, rfl⟩
  have hAnti : antistableSubspaceIn Cg AR ≤ I := by
    intro x hx
    have hxA : (x : X) ∈ antistableSubspaceIn Cg A :=
      map_antistableSubspaceIn_restrict_le Cg A R hR ⟨x, hx, rfl⟩
    have hxN : (x : X) ∈ unobservableSubspace H A := h ⟨x.2, hxA⟩
    exact ⟨x.2, hxN⟩
  have hQ : IsStableIn Cg (Submodule.mapQ I I AR (fun x hx ↦ hI x hx)) :=
    isStableIn_quotient_of_antistableSubspaceIn_le Cg hCg AR I hI hAnti
  exact (LinearSystem.minimalRealizationAllChannelsPolesIn_iff_spectrum Cg A E H).mpr hQ

/-- A reduced transfer channel has poles in `Cg` exactly when no reachable
antistable spectral direction remains observable. -/
theorem minimalRealizationAllChannelsPolesIn_iff_reachable_inf_antistable_le
    {D Z : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    LinearSystem.MinimalRealizationAllChannelsPolesIn Cg A E H ↔
      reachableSubspace A E ⊓ antistableSubspaceIn Cg A ≤
        unobservableSubspace H A := by
  constructor
  · exact reachable_inf_antistableSubspaceIn_le_unobservable_of_polesIn Cg hCg A E H
  · exact polesIn_of_reachable_inf_antistableSubspaceIn_le_unobservable Cg hCg A E H

/-- Stable reduced poles place every reachable channel state in the sum of
the ambient stable and unobservable subspaces. -/
theorem reachable_le_stableSubspaceIn_sup_unobservable_of_polesIn
    {D Z : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hPole : LinearSystem.MinimalRealizationAllChannelsPolesIn Cg A E H) :
    reachableSubspace A E ≤
      stableSubspaceIn Cg A ⊔ unobservableSubspace H A :=
  reachable_le_stableSubspaceIn_sup_unobservable_of_antistable_le Cg hCg A E H
    ((minimalRealizationAllChannelsPolesIn_iff_reachable_inf_antistable_le
      Cg hCg A E H).mp hPole)

/-- An antistable state lying in a sum of stable and invariant hidden states
must itself be hidden. -/
theorem antistable_inf_stable_sup_invariant_le
    (Cg : Set ℂ) (A : X →ₗ[ℝ] X) (N : Submodule ℝ X)
    (hN : ∀ x ∈ N, A x ∈ N) :
    antistableSubspaceIn Cg A ⊓ (stableSubspaceIn Cg A ⊔ N) ≤ N := by
  have _ : IsClosed (N : Set X) := N.closed_of_finiteDimensional
  let T : (X ⧸ N) →ₗ[ℝ] (X ⧸ N) :=
    Submodule.mapQ N N A (fun x hx ↦ hN x hx)
  let q : X →ₗ[ℝ] X ⧸ N := N.mkQ
  have hq : q.comp A = T.comp q := by
    simpa only [q, T] using
      (Submodule.mapQ_mkQ (p := N) (q := N) (f := A)
        (h := fun x hx ↦ hN x hx)).symm
  intro x hx
  have hqxB : q x ∈ antistableSubspaceIn Cg T :=
    map_antistableSubspaceIn_intertwiner_le Cg A T q hq ⟨x, hx.1, rfl⟩
  obtain ⟨s, hs, n, hn, hsn⟩ := Submodule.mem_sup.mp hx.2
  have hqs : q s ∈ stableSubspaceIn Cg T :=
    map_stableSubspaceIn_intertwiner_le Cg A T q hq ⟨s, hs, rfl⟩
  have hqn : q n = 0 := by
    change N.mkQ n = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hn
  have hqxS : q x ∈ stableSubspaceIn Cg T := by
    rw [← hsn, map_add, hqn, add_zero]
    exact hqs
  have hzero : q x = 0 := by
    have hboth : q x ∈ stableSubspaceIn Cg T ⊓ antistableSubspaceIn Cg T :=
      ⟨hqxS, hqxB⟩
    rw [disjoint_iff.mp (disjoint_stableSubspaceIn_antistableSubspaceIn Cg T),
      Submodule.mem_bot] at hboth
    exact hboth
  rw [← Submodule.ker_mkQ N, LinearMap.mem_ker]
  exact hzero

end LinearMap

namespace LinearSystem

universe u

variable {X U Y W D Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- For a well-posed dynamic interconnection, all reduced external poles lie
in `Cg` exactly when its reachable antistable modes are invisible at the
controlled output. This holds for the total disturbance map of the loop. -/
theorem DynamicInterconnection.externalPolesIn_iff_reachable_inf_antistable_le
    (ic : DynamicInterconnection ℝ X U Y W D Z) (hwp : ic.IsWellPosed)
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) :
    MinimalRealizationAllChannelsPolesIn Cg
        (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap ↔
      LinearMap.reachableSubspace (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ⊓
        LinearMap.antistableSubspaceIn Cg (ic.closedLoopMap hwp) ≤
          LinearMap.unobservableSubspace ic.outputMap (ic.closedLoopMap hwp) :=
  LinearMap.minimalRealizationAllChannelsPolesIn_iff_reachable_inf_antistable_le
    Cg hCg (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap

omit [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] in
/-- The plant projection of a stable closed-loop spectral state lies in the
plant's domain-relative stabilizable subspace. -/
theorem DynamicInterconnection.stableProjection_le_stabilizableSubspaceIn
    (ic : DynamicInterconnection ℝ X U Y W D Z) (hwp : ic.IsWellPosed)
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) :
    Submodule.map (LinearMap.fst ℝ X W)
      (LinearMap.stableSubspaceIn Cg (ic.closedLoopMap hwp)) ≤
        LinearMap.stabilizableSubspaceIn Cg ic.plant.A ic.plant.B := by
  let R : Submodule ℝ X := LinearMap.reachableSubspace ic.plant.A ic.plant.B
  have hR : ∀ x ∈ R, ic.plant.A x ∈ R := fun x hx ↦
    LinearMap.map_reachableSubspace_le ic.plant.A ic.plant.B ⟨x, hx, rfl⟩
  have _ : IsClosed (R : Set X) := R.closed_of_finiteDimensional
  let T : (X ⧸ R) →ₗ[ℝ] (X ⧸ R) :=
    Submodule.mapQ R R ic.plant.A (fun x hx ↦ hR x hx)
  let q : X →ₗ[ℝ] X ⧸ R := R.mkQ
  let p : (X × W) →ₗ[ℝ] X ⧸ R := q.comp (LinearMap.fst ℝ X W)
  have hq : q.comp ic.plant.A = T.comp q := by
    simpa only [q, T] using
      (Submodule.mapQ_mkQ (p := R) (q := R) (f := ic.plant.A)
        (h := fun x hx ↦ hR x hx)).symm
  have hp : p.comp (ic.closedLoopMap hwp) = T.comp p := by
    apply LinearMap.ext
    intro s
    change q ((ic.closedLoopMap hwp s).1) = T (q s.1)
    rw [ic.closedLoopMap_fst, map_add]
    have hB : q (ic.plant.B (ic.solvedInput hwp s)) = 0 := by
      change R.mkQ (ic.plant.B (ic.solvedInput hwp s)) = 0
      rw [← LinearMap.mem_ker]
      rw [Submodule.ker_mkQ]
      exact LinearMap.range_le_reachableSubspace ic.plant.A ic.plant.B
        ⟨ic.solvedInput hwp s, rfl⟩
    rw [hB, add_zero]
    exact congrArg (fun f : X →ₗ[ℝ] X ⧸ R ↦ f s.1) hq
  rintro _ ⟨s, hs, rfl⟩
  have hps : p s ∈ LinearMap.stableSubspaceIn Cg T :=
    LinearMap.map_stableSubspaceIn_intertwiner_le Cg (ic.closedLoopMap hwp) T p hp
      ⟨s, hs, rfl⟩
  have hxs : s.1 ∈ LinearMap.stableSubspaceIn Cg ic.plant.A ⊔ R :=
    LinearMap.mem_sup_stableSubspaceIn_of_stable_quotient Cg hCg ic.plant.A T q hq R
      (by change LinearMap.ker R.mkQ ≤ R; rw [Submodule.ker_mkQ]) s.1 hps
  exact hxs

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ W]
  [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] in
/-- Projecting the closed loop's unobservable subspace yields a controlled
invariant subspace contained in the plant output kernel. -/
theorem DynamicInterconnection.unobservableProjection_le_controlledInvariantSubspace
    (ic : DynamicInterconnection ℝ X U Y W D Z) (hwp : ic.IsWellPosed) :
    DynamicInterconnection.extendedProjection
        (LinearMap.unobservableSubspace ic.outputMap (ic.closedLoopMap hwp)) ≤
      LinearMap.controlledInvariantSubspace ic.plant.A ic.plant.B (LinearMap.ker ic.H) := by
  let N := LinearMap.unobservableSubspace ic.outputMap (ic.closedLoopMap hwp)
  have hN : Submodule.map (ic.closedLoopMap hwp) N ≤ N :=
    LinearMap.map_unobservableSubspace_le ic.outputMap (ic.closedLoopMap hwp)
  have hCI : LinearMap.IsControlledInvariant ic.plant.A ic.plant.B
      (DynamicInterconnection.extendedProjection N) :=
    ic.isControlledInvariant_extendedProjection hwp N hN
  have hKer : DynamicInterconnection.extendedProjection N ≤ LinearMap.ker ic.H := by
    intro x hx
    obtain ⟨w, hw⟩ := DynamicInterconnection.mem_extendedProjection.mp hx
    have hzero := LinearMap.unobservableSubspace_le_ker ic.outputMap
      (ic.closedLoopMap hwp) hw
    simpa [LinearMap.mem_ker, ic.outputMap_apply] using hzero
  exact LinearMap.le_controlledInvariantSubspace hKer hCI

/-- General-domain first geometric necessity inclusion for a well-posed
dynamic controller with no disturbance feedthrough in the measurement.
The plant control feedthrough may be nonzero here. -/
theorem DynamicInterconnection.range_E_le_geometricFirst_of_externalPolesIn
    (ic : DynamicInterconnection ℝ X U Y W D Z) (hwp : ic.IsWellPosed)
    (hF : ic.F = 0) (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (hPole : MinimalRealizationAllChannelsPolesIn Cg
      (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap) :
    LinearMap.range ic.E ≤
      LinearMap.controlledInvariantSubspace ic.plant.A ic.plant.B (LinearMap.ker ic.H) ⊔
        LinearMap.stabilizableSubspaceIn Cg ic.plant.A ic.plant.B := by
  let Ae := ic.closedLoopMap hwp
  let Ee := ic.disturbanceMapWithF hwp
  let He := ic.outputMap
  let N := LinearMap.unobservableSubspace He Ae
  have hReach : LinearMap.reachableSubspace Ae Ee ≤
      LinearMap.stableSubspaceIn Cg Ae ⊔ N :=
    LinearMap.reachable_le_stableSubspaceIn_sup_unobservable_of_polesIn
      Cg hCg Ae Ee He hPole
  have hStable : Submodule.map (LinearMap.fst ℝ X W)
      (LinearMap.stableSubspaceIn Cg Ae) ≤
        LinearMap.stabilizableSubspaceIn Cg ic.plant.A ic.plant.B :=
    ic.stableProjection_le_stabilizableSubspaceIn hwp Cg hCg
  have hHidden : DynamicInterconnection.extendedProjection N ≤
      LinearMap.controlledInvariantSubspace ic.plant.A ic.plant.B (LinearMap.ker ic.H) :=
    ic.unobservableProjection_le_controlledInvariantSubspace hwp
  rintro x ⟨d, rfl⟩
  have hdist : Ee d = (ic.E d, 0) := by
    change ic.disturbanceMapWithF hwp d = (ic.E d, 0)
    rw [ic.disturbanceMapWithF_of_F_eq_zero hwp hF, ic.disturbanceMap_apply]
  have hdR : Ee d ∈ LinearMap.reachableSubspace Ae Ee :=
    LinearMap.range_le_reachableSubspace Ae Ee ⟨d, rfl⟩
  obtain ⟨s, hs, n, hn, hsn⟩ := Submodule.mem_sup.mp (hReach hdR)
  have hsX : s.1 ∈ LinearMap.stabilizableSubspaceIn Cg ic.plant.A ic.plant.B :=
    hStable ⟨s, hs, rfl⟩
  have hnX : n.1 ∈
      LinearMap.controlledInvariantSubspace ic.plant.A ic.plant.B (LinearMap.ker ic.H) :=
    hHidden (DynamicInterconnection.mem_extendedProjection.mpr ⟨n.2, by simpa using hn⟩)
  have hEq : n.1 + s.1 = ic.E d := by
    have hh := congrArg Prod.fst hsn
    rw [hdist] at hh
    simpa [add_comm] using hh
  exact Submodule.mem_sup.mpr ⟨n.1, hnX, s.1, hsX, hEq⟩

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ W]
  [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] in
/-- On states invisible to the plant measurement, the closed-loop map
intertwines the plant map with the embedding `x ↦ (x, 0)`. -/
theorem DynamicInterconnection.closedLoopMap_inl_of_mem_unobservable
    (ic : DynamicInterconnection ℝ X U Y W D Z) (hwp : ic.IsWellPosed)
    {x : X} (hx : x ∈ LinearMap.unobservableSubspace ic.plant.C ic.plant.A) :
    ic.closedLoopMap hwp (x, 0) = (ic.plant.A x, 0) := by
  have hxC : ic.plant.C x = 0 :=
    LinearMap.C_eq_zero_of_mem_unobservableSubspace hx
  have hy0 : ic.solvedMeasurement hwp (x, 0) = 0 := by
    apply hwp.1
    rw [ic.loopMap_solvedMeasurement hwp (x, 0), map_zero]
    simp [ic.loopForcing_apply, hxC]
  have hu0 : ic.solvedInput hwp (x, 0) = 0 := by
    rw [ic.solvedInput_apply, hy0]
    simp
  rw [ic.closedLoopMap_apply, hu0, hy0]
  simp

omit [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] in
/-- A plant antistable state invisible to the measurement embeds as an
antistable closed-loop state with zero controller state. -/
theorem DynamicInterconnection.antistable_inl_of_unobservable
    (ic : DynamicInterconnection ℝ X U Y W D Z) (hwp : ic.IsWellPosed)
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg) {x : X}
    (hxA : x ∈ LinearMap.antistableSubspaceIn Cg ic.plant.A)
    (hxN : x ∈ LinearMap.unobservableSubspace ic.plant.C ic.plant.A) :
    (x, (0 : W)) ∈ LinearMap.antistableSubspaceIn Cg (ic.closedLoopMap hwp) := by
  let N : Submodule ℝ X := LinearMap.unobservableSubspace ic.plant.C ic.plant.A
  have hN : ∀ x ∈ N, ic.plant.A x ∈ N := fun x hx ↦
    LinearMap.map_unobservableSubspace_le ic.plant.C ic.plant.A ⟨x, hx, rfl⟩
  let J : N →ₗ[ℝ] X × W :=
    (LinearMap.inl ℝ X W).comp N.subtype
  have hJ : J.comp (ic.plant.A.restrict hN) =
      (ic.closedLoopMap hwp).comp J := by
    apply LinearMap.ext
    intro y
    change ((ic.plant.A (y : X)), (0 : W)) = ic.closedLoopMap hwp ((y : X), 0)
    exact (ic.closedLoopMap_inl_of_mem_unobservable hwp y.2).symm
  have hxR : x ∈ LinearMap.antistableSubspaceIn Cg ic.plant.A ⊓ N :=
    ⟨hxA, hxN⟩
  obtain ⟨y, hy, hyx⟩ :=
    LinearMap.antistableSubspaceIn_inf_le_map_antistableSubspaceIn_restrict
      Cg hCg ic.plant.A N hN hxR
  have hJy : J y ∈ LinearMap.antistableSubspaceIn Cg (ic.closedLoopMap hwp) :=
    LinearMap.map_antistableSubspaceIn_intertwiner_le Cg
      (ic.plant.A.restrict hN) (ic.closedLoopMap hwp) J hJ ⟨y, hy, rfl⟩
  change ((y : X), (0 : W)) ∈ _ at hJy
  have hcoex : (y : X) = x := by simpa using hyx
  rw [hcoex] at hJy
  exact hJy

/-- General-domain second geometric necessity inclusion for a well-posed
dynamic controller with no disturbance feedthrough in the measurement. -/
theorem DynamicInterconnection.geometricSecond_of_externalPolesIn
    (ic : DynamicInterconnection ℝ X U Y W D Z) (hwp : ic.IsWellPosed)
    (hF : ic.F = 0) (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (hPole : MinimalRealizationAllChannelsPolesIn Cg
      (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap) :
    LinearMap.conditionedInvariantSubspace ic.plant.C ic.plant.A (LinearMap.range ic.E) ⊓
        LinearMap.detectableSubspaceIn Cg ic.plant.C ic.plant.A ≤ LinearMap.ker ic.H := by
  let Ae := ic.closedLoopMap hwp
  let Ee := ic.disturbanceMapWithF hwp
  let He := ic.outputMap
  let N := LinearMap.unobservableSubspace He Ae
  let Ve := LinearMap.stableSubspaceIn Cg Ae ⊔ N
  have hN : Submodule.map Ae N ≤ N := LinearMap.map_unobservableSubspace_le He Ae
  have hVe : Submodule.map Ae Ve ≤ Ve := by
    change Submodule.map Ae (LinearMap.stableSubspaceIn Cg Ae ⊔ N) ≤ Ve
    rw [Submodule.map_sup]
    exact sup_le
      (le_trans (LinearMap.map_stableSubspaceIn_le Cg Ae) le_sup_left)
      (le_trans hN le_sup_right)
  have hReach : LinearMap.reachableSubspace Ae Ee ≤ Ve :=
    LinearMap.reachable_le_stableSubspaceIn_sup_unobservable_of_polesIn
      Cg hCg Ae Ee He hPole
  have hE : LinearMap.range ic.E ≤ DynamicInterconnection.extendedIntersection Ve := by
    rintro x ⟨d, rfl⟩
    rw [DynamicInterconnection.mem_extendedIntersection]
    have hdist : Ee d = (ic.E d, 0) := by
      change ic.disturbanceMapWithF hwp d = (ic.E d, 0)
      rw [ic.disturbanceMapWithF_of_F_eq_zero hwp hF, ic.disturbanceMap_apply]
    rw [← hdist]
    exact hReach (LinearMap.range_le_reachableSubspace Ae Ee ⟨d, rfl⟩)
  have hCI : LinearMap.IsConditionedInvariant ic.plant.C ic.plant.A
      (DynamicInterconnection.extendedIntersection Ve) :=
    ic.isConditionedInvariant_extendedIntersection hwp Ve hVe
  have hS : LinearMap.conditionedInvariantSubspace ic.plant.C ic.plant.A
      (LinearMap.range ic.E) ≤ DynamicInterconnection.extendedIntersection Ve :=
    LinearMap.conditionedInvariantSubspace_le hE hCI
  intro x hx
  have hxS : x ∈ LinearMap.conditionedInvariantSubspace ic.plant.C ic.plant.A
      (LinearMap.range ic.E) := hx.1
  have hxDet : x ∈ LinearMap.unobservableSubspace ic.plant.C ic.plant.A ⊓
      LinearMap.antistableSubspaceIn Cg ic.plant.A := hx.2
  have hxVe : (x, (0 : W)) ∈ Ve :=
    DynamicInterconnection.mem_extendedIntersection.mp (hS hxS)
  have hxAnti : (x, (0 : W)) ∈ LinearMap.antistableSubspaceIn Cg Ae :=
    ic.antistable_inl_of_unobservable hwp Cg hCg hxDet.2 hxDet.1
  have hxN : (x, (0 : W)) ∈ N :=
    LinearMap.antistable_inf_stable_sup_invariant_le Cg Ae N
      (fun y hy ↦ hN ⟨y, hy, rfl⟩) ⟨hxAnti, hxVe⟩
  have hxKer : (x, (0 : W)) ∈ LinearMap.ker He :=
    LinearMap.unobservableSubspace_le_ker He Ae hxN
  simpa [LinearMap.mem_ker, He, ic.outputMap_apply] using hxKer

/-- Arbitrary-domain necessity of both Corollary 6.22 geometric inclusions.
The controller may have any finite-dimensional state space. The measurement
disturbance feedthrough is zero, as in the book's system (6.11); a well-posed
controller is quantified explicitly, so no plant feedthrough assumption is
needed for this implication. -/
theorem externalStabilizationConditionsIn_of_anyStateWellPosedExternalPolesIn
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (sys : LinearSystem ℝ X U Y) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : AnyStateWellPosedExternalPolesIn Cg sys E 0 H) :
    ExternalStabilizationConditionsIn Cg sys E H := by
  obtain ⟨V, hV1, hV2, hV3, ctrl, hwp, hPole⟩ := h
  let hVadd : NormedAddCommGroup V := hV1
  let hVspace : NormedSpace ℝ V := hV2
  let hVfinite : FiniteDimensional ℝ V := hV3
  let ic : DynamicInterconnection ℝ X U Y V D Z := ⟨sys, ctrl, E, 0, H⟩
  constructor
  · exact ic.range_E_le_geometricFirst_of_externalPolesIn hwp rfl Cg hCg hPole
  · exact ic.geometricSecond_of_externalPolesIn hwp rfl Cg hCg hPole

end LinearSystem
