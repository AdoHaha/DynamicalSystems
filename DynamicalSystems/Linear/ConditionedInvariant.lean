/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.ControlledInvariant
public import Mathlib.RingTheory.Noetherian.Defs

/-! # Conditioned invariant subspaces

This file formalises the algebraic core of Chapter 5 of Trentelman, Stoorvogel
and Hautus, *Control Theory for Linear Systems*. For a pair `(C, A)` with
`A : X →ₗ[𝕜] X` and `C : X →ₗ[𝕜] Y` a subspace `S` is *conditioned invariant*
(also called `(C, A)`-invariant) when

`Submodule.map A (S ⊓ ker C) ≤ S`,

the geometric characterisation (ii) of Theorem 5.5. The output-injection
characterisation (iii) is `IsOutputInjectionInvariant C A S`, the existence of
a linear map `G : Y →ₗ[𝕜] X` with `(A + G C) S ⊆ S`, and the main equivalence
is `isConditionedInvariant_iff_exists_outputInjection`.

The two notions are dual: `S` is `(C, A)`-invariant if and only if its
annihilator `Sᵃⁿⁿ` is `(Aᵀ, Cᵀ)`-invariant. This is
`isConditionedInvariant_iff_isControlledInvariant_dualMap`, Theorem 5.6; it uses
the algebraic transpose `LinearMap.dualMap` (no inner product) and the general
identity `(W ⊓ W').dualAnnihilator = W.dualAnnihilator ⊔ W'.dualAnnihilator`.

Finally the *conditioned invariant subspace algorithm* (CISA) of Section 5.1,

`S₀ = E`, `Sₖ₊₁ = E ⊔ A (Sₖ ⊓ ker C)`,

and its limit `conditionedInvariantSubspace C A E = ⨆ k, Sₖ` are formalised. In
finite dimension the increasing sequence terminates and the limit is the
smallest conditioned invariant subspace containing `E`, i.e. `S*(E)` of
Theorem 5.7/5.8.

The observer characterization in Theorem 5.5(i) and the sharper CISA termination
bound `k ≤ finrank 𝕜 X - finrank 𝕜 E` are separate from these algebraic results.

## Main definitions

* `LinearMap.IsConditionedInvariant`, `LinearMap.IsOutputInjectionInvariant`
* `LinearMap.conditionedInvariantSeq`, `LinearMap.conditionedInvariantSubspace`

## Main theorems

* `LinearMap.isConditionedInvariant_iff_exists_outputInjection`
* `LinearMap.isConditionedInvariant_iff_isControlledInvariant_dualMap`
* `LinearMap.isLeast_conditionedInvariantSubspace`

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Chapter 5, in particular Definitions 5.1 and 5.2,
  Theorems 5.5, 5.6, 5.7 and 5.8.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 X U Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-! ## Definitions -/

/-- A subspace `S` is **conditioned invariant** (or `(C, A)`-invariant) for the
pair `(C, A)` if `A (S ∩ ker C) ⊆ S`.

This is the geometric characterisation (ii) of
Trentelman–Stoorvogel–Hautus, Theorem 5.5. -/
def IsConditionedInvariant (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (S : Submodule 𝕜 X) : Prop :=
  Submodule.map A (S ⊓ ker C) ≤ S

/-- A subspace `S` is **output-injection invariant** for the pair `(C, A)` if
there is a linear map `G : Y →ₗ[𝕜] X` with `(A + G C) S ⊆ S`.

This is the output-injection characterisation (iii) of
Trentelman–Stoorvogel–Hautus, Theorem 5.5. -/
def IsOutputInjectionInvariant (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (S : Submodule 𝕜 X) : Prop :=
  ∃ G : Y →ₗ[𝕜] X, Submodule.map (A + G.comp C) S ≤ S

/-- Unfolding lemma for `IsConditionedInvariant`. -/
theorem isConditionedInvariant_iff (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (S : Submodule 𝕜 X) :
    IsConditionedInvariant C A S ↔ Submodule.map A (S ⊓ ker C) ≤ S := Iff.rfl

/-- Unfolding lemma for `IsOutputInjectionInvariant`. -/
theorem isOutputInjectionInvariant_iff (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (S : Submodule 𝕜 X) :
    IsOutputInjectionInvariant C A S ↔
      ∃ G : Y →ₗ[𝕜] X, Submodule.map (A + G.comp C) S ≤ S := Iff.rfl

/-! ## The output-injection characterisation -/

/-- **Conditioned invariance gives an output injection.** If
`A (S ∩ ker C) ⊆ S`, then there is `G : Y →ₗ[𝕜] X` with `(A + G C) S ⊆ S`.

The map `x ↦ A x mod S` defined on `S` vanishes on `S ∩ ker C`, so it descends
to `S ⧸ (S ∩ ker C)`, which is isomorphic through `C` to the image `C S ≤ Y`;
extending along `C S ≤ Y` and splitting the quotient map `X → X ⧸ S` (vector
spaces are projective) produces the output injection.

Source: Trentelman–Stoorvogel–Hautus, Theorem 5.5, implication (ii) ⇒ (iii). -/
theorem exists_outputInjection_of_isConditionedInvariant
    {C : X →ₗ[𝕜] Y} {A : X →ₗ[𝕜] X} {S : Submodule 𝕜 X}
    (hS : IsConditionedInvariant C A S) :
    IsOutputInjectionInvariant C A S := by
  let f : S →ₗ[𝕜] X ⧸ S := S.mkQ.comp (A.comp S.subtype)
  have hker : ker (C.comp S.subtype) ≤ ker f := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [LinearMap.comp_apply] at hx
    change S.mkQ (A (x : X)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hS ⟨x, Submodule.mem_inf.mpr ⟨x.2, hx⟩, rfl⟩
  let fbar : S ⧸ ker (C.comp S.subtype) →ₗ[𝕜] X ⧸ S :=
    (ker (C.comp S.subtype)).liftQ f hker
  let e := (C.comp S.subtype).quotKerEquivRange
  let ψ : range (C.comp S.subtype) →ₗ[𝕜] X ⧸ S :=
    fbar.comp e.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ψ
  obtain ⟨G, hG⟩ :=
    Module.projective_lifting_property S.mkQ (-g) (Submodule.mkQ_surjective S)
  refine ⟨G, ?_⟩
  rintro x ⟨s, hs, rfl⟩
  change A s + G (C s) ∈ S
  rw [← Submodule.Quotient.mk_eq_zero S]
  change S.mkQ (A s + G (C s)) = 0
  have hGs : S.mkQ (G (C s)) = -g (C s) := by
    have := congrArg (fun h => h (C s)) hG
    simpa using this
  have hCs : C s ∈ range (C.comp S.subtype) := ⟨⟨s, hs⟩, rfl⟩
  have hgs : g (C s) = ψ ⟨C s, hCs⟩ := by
    have := congrArg (fun h => h ⟨C s, hCs⟩) hg
    simpa using this
  have hψ : ψ ⟨C s, hCs⟩ = S.mkQ (A s) := by
    have he : e (Submodule.Quotient.mk ⟨s, hs⟩) = ⟨C s, hCs⟩ := by
      apply Subtype.ext
      rw [LinearMap.quotKerEquivRange_apply_mk]
      rfl
    have hes : e.symm ⟨C s, hCs⟩ = Submodule.Quotient.mk ⟨s, hs⟩ := by
      rw [← he, LinearEquiv.symm_apply_apply]
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hes, fbar,
      Submodule.liftQ_apply, f, Submodule.mkQ_apply]
    rfl
  rw [map_add, hGs, hgs, hψ]
  abel

/-- **An output injection gives conditioned invariance.** If `(A + G C) S ⊆ S`,
then `A (S ∩ ker C) ⊆ S`, because `A = (A + G C) - G C` and `C` vanishes on
`S ∩ ker C`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 5.5, implication (iii) ⇒ (ii). -/
theorem isConditionedInvariant_of_exists_outputInjection
    {C : X →ₗ[𝕜] Y} {A : X →ₗ[𝕜] X} {S : Submodule 𝕜 X}
    (h : IsOutputInjectionInvariant C A S) : IsConditionedInvariant C A S := by
  obtain ⟨G, hG⟩ := h
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨hyS, hyC⟩ := Submodule.mem_inf.mp hy
  have hyC0 : C y = 0 := LinearMap.mem_ker.mp hyC
  have : A y = (A + G.comp C) y := by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hyC0, map_zero, add_zero]
  rw [this]
  exact hG ⟨y, hyS, rfl⟩

/-- **Theorem 5.5.** A subspace is conditioned invariant if and only if it is
invariant under a suitable output injection.

Source: Trentelman–Stoorvogel–Hautus, Theorem 5.5, equivalence of (ii) and
(iii). -/
theorem isConditionedInvariant_iff_exists_outputInjection
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (S : Submodule 𝕜 X) :
    IsConditionedInvariant C A S ↔ IsOutputInjectionInvariant C A S :=
  ⟨exists_outputInjection_of_isConditionedInvariant,
    isConditionedInvariant_of_exists_outputInjection⟩

/-- **Invariance under output injection.** The classes of conditioned invariant
subspaces of `(C, A)` and `(C, A + G C)` coincide.

Source: Trentelman–Stoorvogel–Hautus, Section 5.1, the remark following
Theorem 5.5. -/
theorem isConditionedInvariant_outputInjection_iff
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (G : Y →ₗ[𝕜] X) (S : Submodule 𝕜 X) :
    IsConditionedInvariant C (A + G.comp C) S ↔ IsConditionedInvariant C A S := by
  have hmap : Submodule.map (A + G.comp C) (S ⊓ ker C) =
      Submodule.map A (S ⊓ ker C) := by
    apply le_antisymm <;> rintro x ⟨y, hy, rfl⟩
    · have hyC : C y = 0 := (Submodule.mem_inf.mp hy).2
      exact ⟨y, hy, by simp only [LinearMap.add_apply, LinearMap.comp_apply, hyC,
        map_zero, add_zero]⟩
    · have hyC : C y = 0 := (Submodule.mem_inf.mp hy).2
      exact ⟨y, hy, by simp only [LinearMap.add_apply, LinearMap.comp_apply, hyC,
        map_zero, add_zero]⟩
  rw [isConditionedInvariant_iff, isConditionedInvariant_iff, hmap]

/-- **Invariance under an output-space isomorphism.** Replacing the output map
`C` by `T C` with `T` an isomorphism does not change the conditioned invariant
subspaces.

Source: Trentelman–Stoorvogel–Hautus, Section 5.1, the remark following
Theorem 5.5. -/
theorem isConditionedInvariant_changeOutput_iff {Y' : Type*} [AddCommGroup Y']
    [Module 𝕜 Y'] (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (T : Y ≃ₗ[𝕜] Y')
    (S : Submodule 𝕜 X) :
    IsConditionedInvariant (T.toLinearMap.comp C) A S ↔ IsConditionedInvariant C A S := by
  have hker : ker (T.toLinearMap.comp C) = ker C := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    exact ⟨fun h => T.injective (by simpa using h), fun h => by simp [h]⟩
  rw [isConditionedInvariant_iff, isConditionedInvariant_iff, hker]

/-! ## Closure properties -/

/-- The whole state space is conditioned invariant. -/
theorem isConditionedInvariant_top (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    IsConditionedInvariant C A (⊤ : Submodule 𝕜 X) := by
  simp [IsConditionedInvariant]

/-- **The intersection of two conditioned invariant subspaces is conditioned
invariant.**

Source: Trentelman–Stoorvogel–Hautus, Section 5.1, the remark following
Theorem 5.5. -/
theorem isConditionedInvariant_inf {C : X →ₗ[𝕜] Y} {A : X →ₗ[𝕜] X}
    {S T : Submodule 𝕜 X} (hS : IsConditionedInvariant C A S)
    (hT : IsConditionedInvariant C A T) :
    IsConditionedInvariant C A (S ⊓ T) := by
  simp only [IsConditionedInvariant] at hS hT ⊢
  refine le_inf ?_ ?_
  · exact le_trans (Submodule.map_mono (inf_le_inf inf_le_left le_rfl)) hS
  · exact le_trans (Submodule.map_mono (inf_le_inf inf_le_right le_rfl)) hT

/-- **The infimum of any family of conditioned invariant subspaces is
conditioned invariant.** This is the "intersection of any number" statement of
Trentelman–Stoorvogel–Hautus, Section 5.1. -/
theorem isConditionedInvariant_iInf {ι : Sort*} {C : X →ₗ[𝕜] Y} {A : X →ₗ[𝕜] X}
    {S : ι → Submodule 𝕜 X} (hS : ∀ i, IsConditionedInvariant C A (S i)) :
    IsConditionedInvariant C A (⨅ i, S i) := by
  simp only [IsConditionedInvariant] at hS ⊢
  refine le_iInf fun i => ?_
  exact le_trans (Submodule.map_mono (inf_le_inf (iInf_le S i) le_rfl)) (hS i)

/-! ## Duality with controlled invariance -/

/-- The annihilator of `map A (S ∩ ker C)` expressed through the transpose:
`(A (S ∩ ker C))ᵃⁿⁿ = (Aᵀ)⁻¹ (Sᵃⁿⁿ + im Cᵀ)`. -/
theorem dualAnnihilator_map_inf_ker (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (S : Submodule 𝕜 X) :
    (Submodule.map A (S ⊓ ker C)).dualAnnihilator =
      Submodule.comap A.dualMap (S.dualAnnihilator ⊔ range C.dualMap) := by
  have hmapA : Submodule.map A (S ⊓ ker C) =
      LinearMap.range (A.comp (S ⊓ ker C).subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hmapA, ← LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    ← LinearMap.dualMap_comp_dualMap (S ⊓ ker C).subtype A, LinearMap.ker_comp,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, Submodule.range_subtype,
    Subspace.dualAnnihilator_inf_eq,
    ← LinearMap.range_dualMap_eq_dualAnnihilator_ker C]

/-- **Theorem 5.6 (duality).** A subspace `S` is `(C, A)`-invariant if and only
if its annihilator `Sᵃⁿⁿ` is `(Aᵀ, Cᵀ)`-invariant.

Source: Trentelman–Stoorvogel–Hautus, Theorem 5.6. -/
theorem isConditionedInvariant_iff_isControlledInvariant_dualMap
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (S : Submodule 𝕜 X) :
    IsConditionedInvariant C A S ↔
      IsControlledInvariant A.dualMap C.dualMap S.dualAnnihilator := by
  have hmap := dualAnnihilator_map_inf_ker C A S
  constructor
  · intro h
    change Submodule.map A.dualMap S.dualAnnihilator ≤
      S.dualAnnihilator ⊔ range C.dualMap
    rw [Submodule.map_le_iff_le_comap, ← hmap]
    exact Subspace.dualAnnihilator_le_dualAnnihilator_iff.mpr h
  · intro h
    change Submodule.map A (S ⊓ ker C) ≤ S
    rw [← Subspace.dualAnnihilator_le_dualAnnihilator_iff, hmap,
      ← Submodule.map_le_iff_le_comap]
    exact h

/-- The other direction of geometric duality: controlled invariance of a subspace
is equivalent to conditioned invariance of its algebraic annihilator. -/
theorem isControlledInvariant_iff_isConditionedInvariant_dualMap
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (V : Submodule 𝕜 X) :
    IsControlledInvariant A B V ↔
      IsConditionedInvariant B.dualMap A.dualMap V.dualAnnihilator := by
  have hmap : (Submodule.map A V).dualAnnihilator =
      Submodule.comap A.dualMap V.dualAnnihilator := by
    rw [← Submodule.range_subtype V, ← LinearMap.range_comp,
      ← LinearMap.ker_dualMap_eq_dualAnnihilator_range,
      ← LinearMap.dualMap_comp_dualMap, LinearMap.ker_comp,
      LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  rw [IsControlledInvariant, ← Subspace.dualAnnihilator_le_dualAnnihilator_iff,
    Submodule.dualAnnihilator_sup_eq, hmap,
    ← LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    IsConditionedInvariant, Submodule.map_le_iff_le_comap]

/-! ## The conditioned invariant subspace algorithm -/

/-- The **conditioned invariant subspace algorithm (CISA)** of
Trentelman–Stoorvogel–Hautus, Section 5.1, display (5.5):

`S₀ = E`, `Sₖ₊₁ = E ⊔ A (Sₖ ⊓ ker C)`. -/
def conditionedInvariantSeq (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (E : Submodule 𝕜 X) :
    ℕ → Submodule 𝕜 X
  | 0 => E
  | n + 1 => E ⊔ Submodule.map A (conditionedInvariantSeq C A E n ⊓ ker C)

@[simp]
theorem conditionedInvariantSeq_zero (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (E : Submodule 𝕜 X) :
    conditionedInvariantSeq C A E 0 = E := rfl

@[simp]
theorem conditionedInvariantSeq_succ (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (E : Submodule 𝕜 X) (n : ℕ) :
    conditionedInvariantSeq C A E (n + 1) =
      E ⊔ Submodule.map A (conditionedInvariantSeq C A E n ⊓ ker C) := rfl

/-- The CISA sequence is increasing (Theorem 5.8 (i)). -/
theorem conditionedInvariantSeq_le_succ (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (E : Submodule 𝕜 X) (n : ℕ) :
    conditionedInvariantSeq C A E n ≤ conditionedInvariantSeq C A E (n + 1) := by
  induction n with
  | zero => exact le_sup_left
  | succ n ih =>
      rw [conditionedInvariantSeq_succ, conditionedInvariantSeq_succ]
      exact sup_le_sup le_rfl (Submodule.map_mono (inf_le_inf ih le_rfl))

/-- The CISA sequence is monotone. -/
theorem conditionedInvariantSeq_monotone (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (E : Submodule 𝕜 X) :
    Monotone (conditionedInvariantSeq C A E) :=
  monotone_nat_of_le_succ (conditionedInvariantSeq_le_succ C A E)

/-- **Every conditioned invariant subspace containing `E` contains every CISA
subspace.** This is the invariance half of Theorem 5.8 (iv). -/
theorem conditionedInvariantSeq_le_of_isConditionedInvariant {C : X →ₗ[𝕜] Y}
    {A : X →ₗ[𝕜] X} {E S : Submodule 𝕜 X} (hE : E ≤ S)
    (hS : IsConditionedInvariant C A S) (n : ℕ) :
    conditionedInvariantSeq C A E n ≤ S := by
  induction n with
  | zero => exact hE
  | succ n ih =>
      refine sup_le hE ?_
      calc Submodule.map A (conditionedInvariantSeq C A E n ⊓ ker C)
          ≤ Submodule.map A (S ⊓ ker C) := Submodule.map_mono (inf_le_inf ih le_rfl)
        _ ≤ S := hS

/-- The **limit of the CISA**, `S*(E) = ⨆ k, Sₖ`. In finite dimension this is
the smallest conditioned invariant subspace containing `E`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 5.7 and display (5.5). -/
noncomputable def conditionedInvariantSubspace (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (E : Submodule 𝕜 X) : Submodule 𝕜 X :=
  ⨆ n, conditionedInvariantSeq C A E n

/-- The initial subspace is contained in the CISA limit (Theorem 5.7 (ii)). -/
theorem le_conditionedInvariantSubspace (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (E : Submodule 𝕜 X) :
    E ≤ conditionedInvariantSubspace C A E := by
  simpa only [conditionedInvariantSubspace, conditionedInvariantSeq_zero]
    using le_iSup (fun n => conditionedInvariantSeq C A E n) 0

/-- **Universal property of the CISA limit.** Every conditioned invariant
subspace containing `E` contains `S*(E)` (Theorem 5.7 (iii)). -/
theorem conditionedInvariantSubspace_le {C : X →ₗ[𝕜] Y} {A : X →ₗ[𝕜] X}
    {E S : Submodule 𝕜 X} (hE : E ≤ S) (hS : IsConditionedInvariant C A S) :
    conditionedInvariantSubspace C A E ≤ S :=
  iSup_le fun n => conditionedInvariantSeq_le_of_isConditionedInvariant hE hS n

/-- **Finite termination of the CISA.** Over a finite-dimensional state space
the increasing sequence `Sₖ` stabilises, by the ascending chain condition on
subspaces.

Source: the finite-termination part of Trentelman–Stoorvogel–Hautus,
Theorem 5.8 (ii); its dimension bound is not asserted here. -/
theorem exists_conditionedInvariantSeq_stabilizes [FiniteDimensional 𝕜 X]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (E : Submodule 𝕜 X) :
    ∃ k, conditionedInvariantSeq C A E k = conditionedInvariantSeq C A E (k + 1) := by
  obtain ⟨k, hk⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian 𝕜 X)
    ({ toFun := fun n => conditionedInvariantSeq C A E n
       monotone' := fun _ _ hmn => conditionedInvariantSeq_monotone C A E hmn } :
        ℕ →o Submodule 𝕜 X)
  exact ⟨k, hk (k + 1) (Nat.le_succ k)⟩

/-- Once the CISA has stabilised at step `k` it is constant from `k` on
(Theorem 5.8 (iii)). -/
theorem conditionedInvariantSeq_eq_of_stabilizes {C : X →ₗ[𝕜] Y} {A : X →ₗ[𝕜] X}
    {E : Submodule 𝕜 X} {k : ℕ}
    (hstab : conditionedInvariantSeq C A E k = conditionedInvariantSeq C A E (k + 1))
    {n : ℕ} (hn : k ≤ n) :
    conditionedInvariantSeq C A E n = conditionedInvariantSeq C A E k := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
      have : conditionedInvariantSeq C A E (n + 1) =
          conditionedInvariantSeq C A E (k + 1) := by
        rw [conditionedInvariantSeq_succ, conditionedInvariantSeq_succ, ih]
      rw [this, hstab]

/-- If the CISA stabilises at step `k`, then its limit is the stable value
(Theorem 5.8 (iv), first part). -/
theorem conditionedInvariantSubspace_eq_of_stabilizes {C : X →ₗ[𝕜] Y} {A : X →ₗ[𝕜] X}
    {E : Submodule 𝕜 X} {k : ℕ}
    (hstab : conditionedInvariantSeq C A E k = conditionedInvariantSeq C A E (k + 1)) :
    conditionedInvariantSubspace C A E = conditionedInvariantSeq C A E k := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    by_cases hnk : n ≤ k
    · exact conditionedInvariantSeq_monotone C A E hnk
    · exact le_of_eq <|
        conditionedInvariantSeq_eq_of_stabilizes hstab (le_of_lt (not_le.mp hnk))
  · exact le_iSup (fun n => conditionedInvariantSeq C A E n) k

/-- **The CISA limit is conditioned invariant in finite dimension**
(Theorem 5.7 (i) via Theorem 5.8 (iv)). -/
theorem isConditionedInvariant_conditionedInvariantSubspace [FiniteDimensional 𝕜 X]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (E : Submodule 𝕜 X) :
    IsConditionedInvariant C A (conditionedInvariantSubspace C A E) := by
  obtain ⟨k, hstab⟩ := exists_conditionedInvariantSeq_stabilizes C A E
  rw [conditionedInvariantSubspace_eq_of_stabilizes hstab]
  rw [IsConditionedInvariant]
  intro x hx
  rw [hstab, conditionedInvariantSeq_succ]
  exact Submodule.mem_sup_right hx

/-- **`S*(E)` is the smallest conditioned invariant subspace containing `E`**
(Theorem 5.7, in the form of a least-element statement). -/
theorem isLeast_conditionedInvariantSubspace [FiniteDimensional 𝕜 X]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (E : Submodule 𝕜 X) :
    IsLeast {S : Submodule 𝕜 X | E ≤ S ∧ IsConditionedInvariant C A S}
      (conditionedInvariantSubspace C A E) :=
  ⟨⟨le_conditionedInvariantSubspace C A E,
      isConditionedInvariant_conditionedInvariantSubspace C A E⟩,
    fun _ hS => conditionedInvariantSubspace_le hS.1 hS.2⟩

end LinearMap
