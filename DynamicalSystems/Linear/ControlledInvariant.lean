/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Duality
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Artinian.Module

/-! # Controlled invariant subspaces

This file formalises the algebraic core of Chapter 4 of Trentelman, Stoorvogel
and Hautus, *Control Theory for Linear Systems*. For a pair `(A, B)` with
`A : X →ₗ[𝕜] X` and `B : U →ₗ[𝕜] X` we define a subspace `V` to be
*controlled invariant* (also called `(A, B)`-invariant) when

`Submodule.map A V ≤ V ⊔ range B`,

the geometric characterisation (ii) of Theorem 4.2. We prove its equivalence with
the feedback characterisation (iii), and an input-coordinate invariance property:

* `LinearMap.IsStateFeedbackInvariant A B V`, the existence of a state feedback
  `F : X →ₗ[𝕜] U` with `(A + B F) V ≤ V` (characterisation (iii));
* the corresponding statement with the input map `B G` for an isomorphism `G`
  of the input space.

The main equivalence is

`LinearMap.isControlledInvariant_iff_exists_stateFeedback`.

The construction of the feedback gain is explicit: the sum map
`V × U → V ⊔ range B` is surjective, it is split using that vector spaces are
projective modules, and the resulting input component is negated and extended
from `V` to `X`.

We also formalise the *invariant subspace algorithm* (ISA) of Section 4.3,
`controlledInvariantSeq`, the recurrence

`V₀ = K`, `Vₖ₊₁ = K ⊓ (Vₖ ⊔ range B).comap A`,

and its limit `controlledInvariantSubspace A B K = ⨅ k, Vₖ`. In finite
dimension the sequence terminates and the limit is the largest controlled
invariant subspace contained in `K`, the algebraic characterization of `V*(K)` in
Theorems 4.5/4.10. The universal property is recorded in both directions by
`LinearMap.le_controlledInvariantSubspace` and
`LinearMap.isGreatest_controlledInvariantSubspace`.

The trajectory characterization in Theorem 4.2(i)/Definition 4.4 and the sharper
termination bound `k ≤ dim K` are not proved here. The algorithm is defined
algebraically, without assuming either characterization or bound.

## Main definitions

* `LinearMap.IsControlledInvariant`, `LinearMap.IsStateFeedbackInvariant`
* `LinearMap.controlledInvariantSeq`, `LinearMap.controlledInvariantSubspace`

## Main theorems

* `LinearMap.isControlledInvariant_iff_exists_stateFeedback`
* `LinearMap.isControlledInvariant_stateFeedback_iff`
* `LinearMap.isGreatest_controlledInvariantSubspace`

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Chapter 4, in particular Definition 4.1,
  Theorem 4.2, Definition 4.4, Theorems 4.5 and 4.10.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 X U Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-! ## Definitions -/

/-- A subspace `V` is **controlled invariant** (or `(A, B)`-invariant) for the
pair `(A, B)` if `A V ⊆ V + im B`.

This is the geometric characterisation (ii) of
Trentelman–Stoorvogel–Hautus, Theorem 4.2. -/
def IsControlledInvariant (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (V : Submodule 𝕜 X) : Prop :=
  Submodule.map A V ≤ V ⊔ range B

/-- A subspace `V` is **state-feedback invariant** for the pair `(A, B)` if
there is a linear map `F : X →ₗ[𝕜] U` with `(A + B F) V ⊆ V`.

This is the closed-loop characterisation (iii) of
Trentelman–Stoorvogel–Hautus, Theorem 4.2. -/
def IsStateFeedbackInvariant (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (V : Submodule 𝕜 X) : Prop :=
  ∃ F : X →ₗ[𝕜] U, Submodule.map (A + B.comp F) V ≤ V

/-- Unfolding lemma for `IsControlledInvariant`. -/
theorem isControlledInvariant_iff (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (V : Submodule 𝕜 X) :
    IsControlledInvariant A B V ↔ Submodule.map A V ≤ V ⊔ range B := Iff.rfl

/-- Unfolding lemma for `IsStateFeedbackInvariant`. -/
theorem isStateFeedbackInvariant_iff (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (V : Submodule 𝕜 X) :
    IsStateFeedbackInvariant A B V ↔
      ∃ F : X →ₗ[𝕜] U, Submodule.map (A + B.comp F) V ≤ V := Iff.rfl

/-! ## The feedback characterisation -/

/-- **Controlled invariance gives a feedback gain.** If `A V ⊆ V + im B`, then
there is a linear `F : X →ₗ[𝕜] U` with `(A + B F) V ⊆ V`.

The map `V × U → V ⊔ im B`, `(v, u) ↦ v + B u`, is surjective. Since vector
spaces are projective, it splits: there is `g : V → V × U` with
`g v = (v₁, u)` and `v₁ + B u = A v`. The second component, negated, is the
desired feedback on `V`; it extends to all of `X` by
`LinearMap.exists_extend`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 4.2, implication (ii) ⇒ (iii). -/
theorem exists_stateFeedback_of_isControlledInvariant
    {A : X →ₗ[𝕜] X} {B : U →ₗ[𝕜] X} {V : Submodule 𝕜 X}
    (hV : IsControlledInvariant A B V) :
    IsStateFeedbackInvariant A B V := by
  let W : Submodule 𝕜 X := V ⊔ range B
  have hmem : ∀ x : X, x ∈ W ↔ ∃ v ∈ V, ∃ u : U, v + B u = x := by
    intro x
    rw [Submodule.mem_sup]
    constructor
    · rintro ⟨v, hv, w, hw, rfl⟩
      obtain ⟨u, rfl⟩ := hw
      exact ⟨v, hv, u, rfl⟩
    · rintro ⟨v, hv, u, rfl⟩
      exact ⟨v, hv, B u, ⟨u, rfl⟩, rfl⟩
  let σ : V × U →ₗ[𝕜] W :=
    (V.subtype.coprod B).codRestrict W (by
      rintro ⟨v, u⟩
      exact (hmem _).mpr ⟨v, v.2, u, rfl⟩)
  have hσ : Function.Surjective σ := by
    rintro ⟨x, hx⟩
    obtain ⟨v, hv, u, huv⟩ := (hmem x).mp hx
    refine ⟨(⟨v, hv⟩, u), ?_⟩
    apply Subtype.ext
    simp [σ, LinearMap.coprod_apply, huv]
  let ψ : V →ₗ[𝕜] W :=
    (A.comp V.subtype).codRestrict W (by
      intro v
      exact hV ⟨v, v.2, rfl⟩)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property σ ψ hσ
  obtain ⟨F, hF⟩ := LinearMap.exists_extend (-(LinearMap.snd 𝕜 V U).comp g)
  refine ⟨F, ?_⟩
  rintro x ⟨v, hv, rfl⟩
  change A v + B (F v) ∈ V
  have hgv : σ (g ⟨v, hv⟩) = ψ ⟨v, hv⟩ := by
    have := congrArg (fun f => f ⟨v, hv⟩) hg
    simpa using this
  have hcoord : ((g ⟨v, hv⟩).1 : X) + B (g ⟨v, hv⟩).2 = A v := by
    have := congrArg Subtype.val hgv
    simpa [σ, ψ, LinearMap.coprod_apply] using this
  have hFv : F v = -((g ⟨v, hv⟩).2) := by
    have := congrArg (fun f => f ⟨v, hv⟩) hF
    simpa [LinearMap.snd_apply] using this
  have : A v + B (F v) = ((g ⟨v, hv⟩).1 : X) := by
    rw [hFv, map_neg, ← hcoord]
    abel
  rw [this]
  exact (g ⟨v, hv⟩).1.2

/-- **A feedback gain gives controlled invariance.** If `(A + B F) V ⊆ V`, then
`A V ⊆ V + im B`, because `A = (A + B F) - B F` and `im (B F) ⊆ im B`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 4.2, implication (iii) ⇒ (ii). -/
theorem isControlledInvariant_of_exists_stateFeedback
    {A : X →ₗ[𝕜] X} {B : U →ₗ[𝕜] X} {V : Submodule 𝕜 X}
    (h : IsStateFeedbackInvariant A B V) : IsControlledInvariant A B V := by
  obtain ⟨F, hF⟩ := h
  intro x hx
  rw [Submodule.mem_map] at hx
  obtain ⟨v, hv, rfl⟩ := hx
  have hsplit : A v = (A + B.comp F) v + B (-(F v)) := by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_neg]
    abel
  rw [hsplit]
  exact Submodule.mem_sup.mpr
    ⟨(A + B.comp F) v, hF ⟨v, hv, rfl⟩, B (-(F v)), ⟨-(F v), rfl⟩, rfl⟩

/-- **Theorem 4.2.** A subspace is controlled invariant if and only if it can be
made invariant by a suitable state feedback.

Source: Trentelman–Stoorvogel–Hautus, Theorem 4.2, equivalence of (ii) and
(iii). -/
theorem isControlledInvariant_iff_exists_stateFeedback
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (V : Submodule 𝕜 X) :
    IsControlledInvariant A B V ↔ IsStateFeedbackInvariant A B V :=
  ⟨exists_stateFeedback_of_isControlledInvariant,
    isControlledInvariant_of_exists_stateFeedback⟩

/-- **Invariance under state feedback.** The classes of controlled invariant
subspaces of `(A, B)` and `(A + B F, B)` coincide.

Source: Trentelman–Stoorvogel–Hautus, Section 4.1, the remark following
Theorem 4.2. -/
theorem isControlledInvariant_stateFeedback_iff
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (F : X →ₗ[𝕜] U) (V : Submodule 𝕜 X) :
    IsControlledInvariant (A + B.comp F) B V ↔ IsControlledInvariant A B V := by
  rw [isControlledInvariant_iff_exists_stateFeedback,
    isControlledInvariant_iff_exists_stateFeedback]
  constructor
  · rintro ⟨F₀, hF₀⟩
    refine ⟨F + F₀, ?_⟩
    have hcomp : (A + B.comp F) + B.comp F₀ = A + B.comp (F + F₀) := by
      ext x
      simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
      abel
    rwa [hcomp] at hF₀
  · rintro ⟨F₀, hF₀⟩
    refine ⟨F₀ - F, ?_⟩
    have hcomp : (A + B.comp F) + B.comp (F₀ - F) = A + B.comp F₀ := by
      ext x
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, map_sub]
      abel
    rwa [hcomp]

/-- **Invariance under an input-space isomorphism.** Replacing the input map
`B` by `B G` with `G` an isomorphism does not change the controlled invariant
subspaces.

Source: Trentelman–Stoorvogel–Hautus, Section 4.1, the remark following
Theorem 4.2. -/
theorem isControlledInvariant_changeInput_iff {U' : Type*} [AddCommGroup U']
    [Module 𝕜 U'] (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (G : U' ≃ₗ[𝕜] U)
    (V : Submodule 𝕜 X) :
    IsControlledInvariant A (B.comp G.toLinearMap) V ↔ IsControlledInvariant A B V := by
  have hrange : range (B.comp G.toLinearMap) = range B := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rw [isControlledInvariant_iff, isControlledInvariant_iff, hrange]

/-! ## Invariance under a state-space linear equivalence -/

section ChangeState

variable {X' : Type*} [AddCommGroup X'] [Module 𝕜 X']

/-- **Conjugation commutes with `Submodule.map`.** Changing the state coordinates
by `e : X' ≃ₗ[𝕜] X` sends `A` to `e.symm.conj A` and a subspace `W` to
`Submodule.map e.symm.toLinearMap W`; the image subspace `A '' W` is carried to
`(e.symm.conj A) '' (e.symm '' W)`. -/
theorem map_conj_changeState (A : X →ₗ[𝕜] X) (W : Submodule 𝕜 X) (e : X' ≃ₗ[𝕜] X) :
    Submodule.map (e.symm.conj A) (Submodule.map e.symm.toLinearMap W) =
      Submodule.map e.symm.toLinearMap (Submodule.map A W) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp [LinearEquiv.conj_apply]

/-- **`A`-invariance is invariant under a state-space equivalence.** This is
Mathlib's `LinearEquiv.map_mem_invtSubmodule_conj_iff` phrased with explicit
transported maps: `e.symm '' V` is invariant under `e.symm.conj A` if and only if
`V` is invariant under `A`. -/
theorem map_le_self_changeState_iff (A : X →ₗ[𝕜] X) (e : X' ≃ₗ[𝕜] X)
    (V : Submodule 𝕜 X) :
    Submodule.map (e.symm.conj A) (Submodule.map e.symm.toLinearMap V) ≤
        Submodule.map e.symm.toLinearMap V ↔
      Submodule.map A V ≤ V := by
  rw [← Module.End.mem_invtSubmodule_iff_map_le,
    ← Module.End.mem_invtSubmodule_iff_map_le]
  exact LinearEquiv.map_mem_invtSubmodule_conj_iff

/-- **Transport of an invariance relation.** For `A' = e.symm.conj A`,
`W' = e.symm '' W` and `S' = e.symm '' S` we have `A' W' ≤ S'` if and only if
`A W ≤ S`. The special case `W = S` is `map_le_self_changeState_iff`. -/
theorem map_le_changeState_iff (A : X →ₗ[𝕜] X) (W S : Submodule 𝕜 X)
    (e : X' ≃ₗ[𝕜] X) :
    Submodule.map (e.symm.conj A) (Submodule.map e.symm.toLinearMap W) ≤
        Submodule.map e.symm.toLinearMap S ↔
      Submodule.map A W ≤ S := by
  rw [map_conj_changeState]
  exact Submodule.map_le_map_iff_of_injective e.symm.injective _ _

/-- **Controlled invariance is invariant under a state-space equivalence.**
Changing the state coordinates by `e : X' ≃ₗ[𝕜] X` transports the controlled
invariant subspaces: with `A' = e.symm.conj A`, `B' = e.symm ∘ B` and
`V' = e.symm '' V`, the subspace `V` is `(A, B)`-invariant if and only if `V'` is
`(A', B')`-invariant.

The invariance half is `map_le_changeState_iff`; the `range B` half is
transported with `LinearMap.range_comp` and `Submodule.map_sup`.

Source: Trentelman–Stoorvogel–Hautus, Section 4.1, invariance of the class of
controlled invariant subspaces under a state-space isomorphism. -/
theorem isControlledInvariant_changeState_iff (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (e : X' ≃ₗ[𝕜] X) (V : Submodule 𝕜 X) :
    IsControlledInvariant A B V ↔
      IsControlledInvariant (e.symm.conj A) (e.symm.toLinearMap.comp B)
        (Submodule.map e.symm.toLinearMap V) := by
  simp only [IsControlledInvariant]
  rw [LinearMap.range_comp, ← Submodule.map_sup]
  exact (map_le_changeState_iff A V (V ⊔ range B) e).symm

end ChangeState

/-! ## Closure properties -/

/-- The zero subspace is controlled invariant. -/
theorem isControlledInvariant_bot (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    IsControlledInvariant A B (⊥ : Submodule 𝕜 X) := by
  simp [IsControlledInvariant]

/-- The whole state space is controlled invariant. -/
theorem isControlledInvariant_top (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    IsControlledInvariant A B (⊤ : Submodule 𝕜 X) := by
  simp [IsControlledInvariant]

/-- **The sum of two controlled invariant subspaces is controlled invariant.**

Source: Trentelman–Stoorvogel–Hautus, Section 4.1, first paragraph after
Definition 4.1. -/
theorem isControlledInvariant_sup {A : X →ₗ[𝕜] X} {B : U →ₗ[𝕜] X}
    {V W : Submodule 𝕜 X} (hV : IsControlledInvariant A B V)
    (hW : IsControlledInvariant A B W) :
    IsControlledInvariant A B (V ⊔ W) := by
  rw [IsControlledInvariant] at hV hW ⊢
  rw [Submodule.map_sup]
  calc Submodule.map A V ⊔ Submodule.map A W
      ≤ (V ⊔ range B) ⊔ (W ⊔ range B) := sup_le_sup hV hW
    _ = (V ⊔ W) ⊔ range B := by ac_rfl

/-- **The supremum of any family of controlled invariant subspaces is controlled
invariant.** This is the "sum of any number" statement of
Trentelman–Stoorvogel–Hautus, Section 4.1. -/
theorem isControlledInvariant_iSup {ι : Sort*} {A : X →ₗ[𝕜] X} {B : U →ₗ[𝕜] X}
    {V : ι → Submodule 𝕜 X} (hV : ∀ i, IsControlledInvariant A B (V i)) :
    IsControlledInvariant A B (⨆ i, V i) := by
  simp only [IsControlledInvariant] at hV ⊢
  rw [Submodule.map_iSup]
  refine iSup_le fun i => ?_
  exact le_trans (hV i) (sup_le_sup_right (le_iSup V i) (range B))

/-! ## The invariant subspace algorithm -/

/-- The **invariant subspace algorithm (ISA)** of
Trentelman–Stoorvogel–Hautus, Section 4.3:

`V₀ = K`, `Vₖ₊₁ = K ⊓ (Vₖ ⊔ im B).comap A`.

The source motivates this recurrence by finite discrete-time trajectories;
that trajectory interpretation is not asserted by this definition. -/
def controlledInvariantSeq (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (K : Submodule 𝕜 X) :
    ℕ → Submodule 𝕜 X
  | 0 => K
  | n + 1 => K ⊓ (controlledInvariantSeq A B K n ⊔ range B).comap A

@[simp]
theorem controlledInvariantSeq_zero (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (K : Submodule 𝕜 X) :
    controlledInvariantSeq A B K 0 = K := rfl

@[simp]
theorem controlledInvariantSeq_succ (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (K : Submodule 𝕜 X) (n : ℕ) :
    controlledInvariantSeq A B K (n + 1) =
      K ⊓ (controlledInvariantSeq A B K n ⊔ range B).comap A := rfl

/-- Membership in one ISA step: `x ∈ Vₖ₊₁` iff `x ∈ K` and
`A x ∈ Vₖ + im B`. -/
theorem mem_controlledInvariantSeq_succ {A : X →ₗ[𝕜] X} {B : U →ₗ[𝕜] X}
    {K : Submodule 𝕜 X} {n : ℕ} {x : X} :
    x ∈ controlledInvariantSeq A B K (n + 1) ↔
      x ∈ K ∧ A x ∈ controlledInvariantSeq A B K n ⊔ range B := by
  simp only [controlledInvariantSeq_succ, Submodule.mem_inf, Submodule.mem_comap]

/-- Every ISA subspace is contained in the initial subspace `K`. -/
theorem controlledInvariantSeq_le_K (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (K : Submodule 𝕜 X) (n : ℕ) :
    controlledInvariantSeq A B K n ≤ K := by
  induction n with
  | zero => exact le_rfl
  | succ n _ => exact inf_le_left

/-- The ISA sequence is decreasing (Theorem 4.10 (i)). -/
theorem controlledInvariantSeq_succ_le (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (K : Submodule 𝕜 X) (n : ℕ) :
    controlledInvariantSeq A B K (n + 1) ≤ controlledInvariantSeq A B K n := by
  induction n with
  | zero => exact inf_le_left
  | succ n ih =>
      refine le_inf inf_le_left ?_
      exact inf_le_right.trans (Submodule.comap_mono (sup_le_sup_right ih (range B)))

/-- The ISA sequence is antitone. -/
theorem controlledInvariantSeq_antitone (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (K : Submodule 𝕜 X) :
    Antitone (controlledInvariantSeq A B K) :=
  antitone_nat_of_succ_le (controlledInvariantSeq_succ_le A B K)

/-- **Every controlled invariant subspace of `K` is contained in every ISA
subspace.** This is the invariance half of Theorem 4.10 (iv). -/
theorem le_controlledInvariantSeq {A : X →ₗ[𝕜] X} {B : U →ₗ[𝕜] X}
    {K V : Submodule 𝕜 X} (hK : V ≤ K) (hV : IsControlledInvariant A B V) (n : ℕ) :
    V ≤ controlledInvariantSeq A B K n := by
  induction n with
  | zero => exact hK
  | succ n ih =>
      refine le_inf hK ?_
      intro x hx
      exact (sup_le_sup_right ih (range B)) (hV ⟨x, hx, rfl⟩)

/-- The **limit of the ISA**, `V*(K) = ⨅ k, Vₖ`. In finite dimension this is
the largest controlled invariant subspace contained in `K`.

Source: Trentelman–Stoorvogel–Hautus, Definition 4.4 and Theorem 4.5. -/
noncomputable def controlledInvariantSubspace (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (K : Submodule 𝕜 X) : Submodule 𝕜 X :=
  ⨅ n, controlledInvariantSeq A B K n

/-- The ISA limit is contained in `K` (Theorem 4.5 (ii)). -/
theorem controlledInvariantSubspace_le_K (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (K : Submodule 𝕜 X) :
    controlledInvariantSubspace A B K ≤ K := by
  simpa only [controlledInvariantSubspace, controlledInvariantSeq_zero]
    using iInf_le (fun n => controlledInvariantSeq A B K n) 0

/-- **Universal property of the ISA limit.** Every controlled invariant
subspace contained in `K` is contained in `V*(K)` (Theorem 4.5 (iii)). -/
theorem le_controlledInvariantSubspace {A : X →ₗ[𝕜] X} {B : U →ₗ[𝕜] X}
    {K V : Submodule 𝕜 X} (hK : V ≤ K) (hV : IsControlledInvariant A B V) :
    V ≤ controlledInvariantSubspace A B K :=
  le_iInf fun n => le_controlledInvariantSeq hK hV n

/-- **Finite termination of the ISA.** Over a finite-dimensional state space
the decreasing sequence `Vₖ` stabilises, by the descending chain condition on
subspaces.

Source: the finite-termination part of Trentelman–Stoorvogel–Hautus,
Theorem 4.10 (ii); its dimension bound is not asserted here. -/
theorem exists_controlledInvariantSeq_stabilizes [FiniteDimensional 𝕜 X]
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (K : Submodule 𝕜 X) :
    ∃ k, controlledInvariantSeq A B K k = controlledInvariantSeq A B K (k + 1) := by
  obtain ⟨k, hk⟩ := IsArtinian.monotone_stabilizes
    ({ toFun := fun n => OrderDual.toDual (controlledInvariantSeq A B K n)
       monotone' := fun m n hmn => by
         rw [OrderDual.toDual_le_toDual]
         exact controlledInvariantSeq_antitone A B K hmn } : ℕ →o (Submodule 𝕜 X)ᵒᵈ)
  exact ⟨k, OrderDual.toDual_inj.mp (hk (k + 1) (Nat.le_succ k))⟩

/-- Once the ISA has stabilised at step `k` it is constant from `k` on
(Theorem 4.10 (iii)). -/
theorem controlledInvariantSeq_eq_of_stabilizes {A : X →ₗ[𝕜] X} {B : U →ₗ[𝕜] X}
    {K : Submodule 𝕜 X} {k : ℕ}
    (hstab : controlledInvariantSeq A B K k = controlledInvariantSeq A B K (k + 1))
    {n : ℕ} (hn : k ≤ n) :
    controlledInvariantSeq A B K n = controlledInvariantSeq A B K k := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
      have : controlledInvariantSeq A B K (n + 1) =
          controlledInvariantSeq A B K (k + 1) := by
        rw [controlledInvariantSeq_succ, controlledInvariantSeq_succ, ih]
      rw [this, ← hstab]

/-- If the ISA stabilises at step `k`, then its limit is the stable value
(Theorem 4.10 (iv), first part). -/
theorem controlledInvariantSubspace_eq_of_stabilizes {A : X →ₗ[𝕜] X} {B : U →ₗ[𝕜] X}
    {K : Submodule 𝕜 X} {k : ℕ}
    (hstab : controlledInvariantSeq A B K k = controlledInvariantSeq A B K (k + 1)) :
    controlledInvariantSubspace A B K = controlledInvariantSeq A B K k := by
  apply le_antisymm
  · exact iInf_le (fun n => controlledInvariantSeq A B K n) k
  · refine le_iInf fun n => ?_
    by_cases hnk : n ≤ k
    · exact controlledInvariantSeq_antitone A B K hnk
    · exact le_of_eq
        (controlledInvariantSeq_eq_of_stabilizes hstab (le_of_lt (not_le.mp hnk))).symm

/-- **The ISA limit is controlled invariant in finite dimension**
(Theorem 4.5 (i) via Theorem 4.10 (iv)). -/
theorem isControlledInvariant_controlledInvariantSubspace [FiniteDimensional 𝕜 X]
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (K : Submodule 𝕜 X) :
    IsControlledInvariant A B (controlledInvariantSubspace A B K) := by
  obtain ⟨k, hstab⟩ := exists_controlledInvariantSeq_stabilizes A B K
  rw [controlledInvariantSubspace_eq_of_stabilizes hstab]
  rw [IsControlledInvariant, Submodule.map_le_iff_le_comap]
  intro x hx
  have hx' : x ∈ controlledInvariantSeq A B K (k + 1) := hstab ▸ hx
  exact (mem_controlledInvariantSeq_succ.mp hx').2

/-- **`V*(K)` is the largest controlled invariant subspace contained in `K`**
(Theorem 4.5, in the form of a greatest-element statement). -/
theorem isGreatest_controlledInvariantSubspace [FiniteDimensional 𝕜 X]
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (K : Submodule 𝕜 X) :
    IsGreatest {V : Submodule 𝕜 X | V ≤ K ∧ IsControlledInvariant A B V}
      (controlledInvariantSubspace A B K) :=
  ⟨⟨controlledInvariantSubspace_le_K A B K,
      isControlledInvariant_controlledInvariantSubspace A B K⟩,
    fun _ hV => le_controlledInvariantSubspace hV.1 hV.2⟩

end LinearMap
