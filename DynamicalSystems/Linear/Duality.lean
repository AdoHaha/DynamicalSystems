/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Kalman
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Algebraic duality, coordinate invariance and Kalman decomposition

This file carries out the article-level duality and decomposition results of
Trentelman–Stoorvogel–Hautus, *Control Theory for Linear Systems*,
Sections 3.3–3.5, at the level of the algebraic pair APIs defined in
`DynamicalSystems.Linear.Subspaces`.

## Algebraic duals versus Hilbert adjoints

Every result in this file is about the **algebraic dual** `Module.Dual 𝕜 X`
and the **algebraic transpose** `f.dualMap`, whose defining property is
`f.dualMap φ = φ ∘ f` (`LinearMap.dualMap_apply`). No inner product is
involved: the transpose exists over any field and turns a linear map
`f : X →ₗ[𝕜] Y` into a map on the algebraic duals in the *opposite*
direction. This is exactly the operation that transposes a matrix, so the
pair `(A, B)` becomes `(Aᵀ, Bᵀ)`.

The **Hilbert adjoint** `f†` of a continuous linear map between inner product
spaces is a different operation: it is the unique map satisfying
`⟪f x, y⟫ = ⟪x, f† y⟫`, and it requires an inner product and completeness.
In finite dimensions, the comparison uses the Riesz identification with the
dual, which is conjugate-linear over `ℂ`. In infinite dimensions the Riesz map
identifies a Hilbert space with its continuous dual, not its full algebraic
dual. Thus a statement about `dualMap` is not by itself a statement about the
Hilbert adjoint. The duality below is stated and proved for algebraic duals only.

## Duality

* `LinearMap.unobservableSubspace_dualMap`: the unobservable subspace of the
  transposed pair is the annihilator of the reachable subspace,
  `⟨ker Bᵀ | Aᵀ⟩ = (⟨A | im B⟩)ᵃⁿⁿ`.
* `LinearMap.isControllable_iff_isObservable_dualMap`: `(A, B)` is controllable
  if and only if `(Bᵀ, Aᵀ)` is observable. This is the coordinate-free form of
  the rank identity in Section 3.3, "(C, A) is observable iff (Aᵀ, Cᵀ) is
  controllable".
* `LinearMap.reachableSubspace_dualMap` and
  `LinearMap.isObservable_iff_isControllable_dualMap`: the dual statements,
  using the finite Krylov reduction of `DynamicalSystems.Linear.Kalman`.

## Coordinate invariance

* `LinearMap.reachableSubspace_changeState`, `LinearMap.isControllable_changeState`
* `LinearMap.unobservableSubspace_changeState`, `LinearMap.isObservable_changeState`

These are the geometric form of Theorem 3.10 (i)–(ii): the pair is transported
by the conjugation `A ↦ e.symm ∘ A ∘ e`, `B ↦ e.symm ∘ B`, `C ↦ C ∘ e`, and
controllability and observability are invariant.

## Kalman decomposition

For a pair `(A, B)` with reachable subspace `W = reachableSubspace A B`:

* `LinearMap.isControllable_reachableRestriction`: the restriction
  `(A|_W, B|_W)` is controllable — the *controllable subsystem* of
  Theorem 3.11.
* `LinearMap.reachableSubspace_quotientReachable_eq_bot`: the quotient
  `X ⧸ W` carries `Ā` and `B̄ = 0`, hence is completely uncontrollable — the
  *uncontrollable quotient system* of Section 3.4.
* `LinearMap.reachableSubspace_compl_snd_eq_zero` and
  `LinearMap.range_compl_snd_eq_zero`: for any chosen complement `V` of `W`
  the block `A₂₁` acting from `W` to `V` and the block `B₂` vanish. The block
  `A₁₂` need **not** vanish, since `V` is not assumed `A`-invariant; this is
  the partial two-block form of Theorem 3.11, not the full four-block Kalman
  form.

Dually, for a pair `(C, A)` with unobservable subspace `N = unobservableSubspace C A`:

* `LinearMap.isObservable_quotientUnobservable`: the quotient `X ⧸ N` carries
  the induced pair `(C̄, Ā)`, which is observable; since `N ≤ ker C`, the readout
  descends to the quotient.
* `LinearMap.unobservableSubspace_restrict_eq_top`: the restriction of `(C, A)`
  to the invariant subspace `N` is completely unobservable.
* `LinearMap.unobservableSubspace_compl_snd_eq_zero` and
  `LinearMap.unobservableSubspace_compl_C_eq_zero`: complement block identities.

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Sections 3.3–3.5.
-/

@[expose] public section

section ConjPow

variable {𝕜 X : Type*} [Field 𝕜] [AddCommGroup X] [Module 𝕜 X]
variable {X' : Type*} [AddCommGroup X'] [Module 𝕜 X']

namespace LinearEquiv

/-- **Conjugation commutes with powers.** Changing state coordinates by a
linear equivalence `e : X' ≃ₗ[𝕜] X` sends the state map `A` to `e.symm.conj A`,
and this operation commutes with taking natural powers:
`(e.symm.conj A) ^ k = e.symm.conj (A ^ k)`.

This is the closed form of `map_pow (LinearEquiv.conjRingEquiv e.symm) A k`
that the state-coordinate invariance proofs in `Duality.lean` and
`DisturbanceDecoupling.lean` all need. -/
theorem conj_pow (e : X' ≃ₗ[𝕜] X) (A : X →ₗ[𝕜] X) (k : ℕ) :
    (e.symm.conj A) ^ k = e.symm.conj (A ^ k) :=
  (map_pow (LinearEquiv.conjRingEquiv e.symm) A k).symm

end LinearEquiv

end ConjPow

namespace LinearMap

variable {𝕜 X U Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-! ## Algebraic duality of a pair -/

/-- **The transpose commutes with powers.** The algebraic transpose of `A ^ k`
is the `k`-th power of the transpose of `A`.

This is the algebraic-transpose analogue of `(Aᵏ)ᵀ = (Aᵀ)ᵏ`. -/
theorem dualMap_pow (A : X →ₗ[𝕜] X) (k : ℕ) :
    A.dualMap ^ k = (A ^ k).dualMap := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero, Module.End.one_eq_id, Module.End.one_eq_id,
        LinearMap.dualMap_id]
  | succ k ih =>
      rw [pow_succ, ih, Module.End.mul_eq_comp, dualMap_comp_dualMap,
        ← Module.End.iterate_succ']

/-- **A pair with zero input map is completely uncontrollable.** The reachable
subspace of `(A, 0)` is `⊥`. -/
theorem reachableSubspace_zero (A : X →ₗ[𝕜] X) :
    reachableSubspace A (0 : U →ₗ[𝕜] X) = ⊥ := by
  apply le_antisymm ?_ bot_le
  exact reachableSubspace_le A 0 (by simp) (by simp)

/-- **Duality of the reachable and unobservable subspaces.** The unobservable
subspace of the transposed pair `(Bᵀ, Aᵀ)` is the annihilator of the reachable
subspace of `(A, B)`. In the notation of the sources,
`⟨ker Bᵀ | Aᵀ⟩ = ⟨A | im B⟩ᵃⁿⁿ`.

Source: Trentelman–Stoorvogel–Hautus, Section 3.3, display preceding
Theorem 3.8; the coordinate-free form of the duality `(C, A) ↦ (Aᵀ, Cᵀ)`. -/
theorem unobservableSubspace_dualMap (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    unobservableSubspace B.dualMap A.dualMap =
      (reachableSubspace A B).dualAnnihilator := by
  rw [reachableSubspace, unobservableSubspace, Submodule.dualAnnihilator_iSup_eq]
  refine iInf_congr fun k => ?_
  rw [← LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  congr 1
  rw [dualMap_pow]
  exact dualMap_comp_dualMap B (A ^ k)

/-- **Controllability is dual to observability.** The pair `(A, B)` is
controllable if and only if the transposed pair `(Bᵀ, Aᵀ)` is observable.

Source: Trentelman–Stoorvogel–Hautus, Section 3.3, the observation that
`(C, A)` is observable if and only if `(Aᵀ, Cᵀ)` is controllable. -/
theorem isControllable_iff_isObservable_dualMap (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    IsControllable A B ↔ IsObservable B.dualMap A.dualMap := by
  rw [isControllable_iff, isObservable_iff, unobservableSubspace_dualMap,
    Submodule.dualAnnihilator_eq_bot_iff]

/-- **Dual form: the reachable subspace of the transposed pair is the
annihilator of the unobservable subspace.** This is the finite-dimensional
form of the same duality, obtained from the finite Krylov description of the
unobservable subspace.

Source: Trentelman–Stoorvogel–Hautus, Section 3.3 and Corollary 3.4 (iii). -/
theorem reachableSubspace_dualMap [FiniteDimensional 𝕜 X]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    reachableSubspace A.dualMap C.dualMap =
      (unobservableSubspace C A).dualAnnihilator := by
  have hterm : ∀ k : Fin (Module.finrank 𝕜 X),
      range ((A.dualMap ^ (k : ℕ)).comp C.dualMap) =
        (ker (C.comp (A ^ (k : ℕ)))).dualAnnihilator := by
    intro k
    rw [dualMap_pow, dualMap_comp_dualMap (A ^ (k : ℕ)) C,
      LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  rw [reachableSubspace_eq_iSup_finrank, Subspace.dual_finrank_eq,
    unobservableSubspace_eq_iInf_finrank, Subspace.dualAnnihilator_iInf_eq]
  simp_rw [hterm]

/-- **Observability is dual to controllability.** The pair `(C, A)` is
observable if and only if the transposed pair `(Aᵀ, Cᵀ)` is controllable.

This is the converse direction of `isControllable_iff_isObservable_dualMap`;
it uses finite-dimensionality of the state space through the finite Krylov
reduction.

Source: Trentelman–Stoorvogel–Hautus, Section 3.3. -/
theorem isObservable_iff_isControllable_dualMap [FiniteDimensional 𝕜 X]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    IsObservable C A ↔ IsControllable A.dualMap C.dualMap := by
  rw [isObservable_iff, isControllable_iff, reachableSubspace_dualMap,
    Submodule.dualAnnihilator_eq_top_iff]

/-! ## Invariance under a state-space linear equivalence -/

section ChangeState

variable {X' : Type*} [AddCommGroup X'] [Module 𝕜 X']

/-- **Reachable subspace under a state-space equivalence.** If the state
coordinates are changed by `e : X' ≃ₗ[𝕜] X`, so that `A' = e.symm ∘ A ∘ e` and
`B' = e.symm ∘ B`, then the reachable subspace transforms by `e.symm`:
`W' = e.symm '' W`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.10 (i), in geometric form. -/
theorem reachableSubspace_changeState (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (e : X' ≃ₗ[𝕜] X) :
    reachableSubspace (e.symm.conj A) (e.symm.toLinearMap.comp B) =
      Submodule.map e.symm.toLinearMap (reachableSubspace A B) := by
  have hpow : ∀ k : ℕ, (e.symm.conj A) ^ k = e.symm.conj (A ^ k) :=
    LinearEquiv.conj_pow e A
  have hcomp : ∀ k : ℕ,
      ((e.symm.conj A) ^ k).comp (e.symm.toLinearMap.comp B) =
        e.symm.toLinearMap.comp ((A ^ k).comp B) := by
    intro k
    rw [hpow k, LinearEquiv.conj_apply]
    ext x
    simp
  rw [reachableSubspace, reachableSubspace, Submodule.map_iSup]
  refine iSup_congr fun k => ?_
  rw [hcomp k, LinearMap.range_comp]

/-- **Controllability is invariant under a state-space equivalence.**

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.10 (i). -/
theorem isControllable_changeState (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (e : X' ≃ₗ[𝕜] X) :
    IsControllable A B ↔
      IsControllable (e.symm.conj A) (e.symm.toLinearMap.comp B) := by
  rw [isControllable_iff, isControllable_iff, reachableSubspace_changeState,
    Submodule.map_eq_top_iff]

/-- **Unobservable subspace under a state-space equivalence.** With
`A' = e.symm ∘ A ∘ e` and `C' = C ∘ e`, the unobservable subspace transforms
by `e.symm`: `N' = e.symm '' N`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.10 (ii), in geometric form. -/
theorem unobservableSubspace_changeState (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (e : X' ≃ₗ[𝕜] X) :
    unobservableSubspace (C.comp e.toLinearMap) (e.symm.conj A) =
      Submodule.map e.symm.toLinearMap (unobservableSubspace C A) := by
  have hpow : ∀ k : ℕ, (e.symm.conj A) ^ k = e.symm.conj (A ^ k) :=
    LinearEquiv.conj_pow e A
  have hkey : ∀ (k : ℕ) (x : X'),
      (C.comp e.toLinearMap) (((e.symm.conj A) ^ k) x) = C ((A ^ k) (e x)) := by
    intro k x
    rw [hpow k, LinearEquiv.conj_apply]
    simp
  ext x
  rw [Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨e x, ?_, by simp⟩
    rw [mem_unobservableSubspace] at hx ⊢
    intro k
    have := hx k
    rw [hkey k] at this
    exact this
  · rintro ⟨y, hy, rfl⟩
    rw [mem_unobservableSubspace] at hy ⊢
    intro k
    rw [hkey k]
    simpa using hy k

/-- **Observability is invariant under a state-space equivalence.**

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.10 (ii). -/
theorem isObservable_changeState (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (e : X' ≃ₗ[𝕜] X) :
    IsObservable C A ↔
      IsObservable (C.comp e.toLinearMap) (e.symm.conj A) := by
  rw [isObservable_iff, isObservable_iff, unobservableSubspace_changeState,
    Submodule.map_eq_bot_iff]

end ChangeState

/-! ## Kalman decomposition: the reachable/controllable part -/

/-- The restriction of the state map `A` to the reachable subspace
`W = reachableSubspace A B`, which is `A`-invariant. This is the state map
`A` of the controllable subsystem of Theorem 3.11. -/
noncomputable def reachableRestrictionA (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    reachableSubspace A B →ₗ[𝕜] reachableSubspace A B :=
  A.restrict fun _ hx => map_reachableSubspace_le A B ⟨_, hx, rfl⟩

/-- The input map `B` corestricted to the reachable subspace. This is the input
map `B` of the controllable subsystem of Theorem 3.11. -/
noncomputable def reachableRestrictionB (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    U →ₗ[𝕜] reachableSubspace A B :=
  B.codRestrict _ fun u => range_le_reachableSubspace A B ⟨u, rfl⟩

/-- **The restricted reachable pair is controllable.** With
`W = reachableSubspace A B`, the pair `(A|_W, B|_W)` is controllable; this is
the *controllable subsystem* of the Kalman decomposition.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.11 and Section 3.4. -/
theorem isControllable_reachableRestriction (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    IsControllable (reachableRestrictionA A B) (reachableRestrictionB A B) := by
  rw [isControllable_iff, eq_top_iff]
  intro w _
  let V : Submodule 𝕜 X := Submodule.map (reachableSubspace A B).subtype
    (reachableSubspace (reachableRestrictionA A B) (reachableRestrictionB A B))
  have hrange : range B ≤ V := by
    rintro _ ⟨u, rfl⟩
    exact ⟨reachableRestrictionB A B u,
      range_le_reachableSubspace _ _ (mem_range_self _ u), rfl⟩
  have hAinv : Submodule.map A V ≤ V := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨reachableRestrictionA A B y,
      map_reachableSubspace_le _ _ ⟨y, hy, rfl⟩, rfl⟩
  have hWle : reachableSubspace A B ≤ V := reachableSubspace_le A B hrange hAinv
  obtain ⟨y, hy, hyeq⟩ := hWle w.2
  have : y = w := Subtype.ext hyeq
  rwa [← this]

/-- The induced state map `Ā` on the quotient `X ⧸ W` by the reachable
subspace. This is the state map of the uncontrollable quotient system of
Section 3.4. -/
noncomputable def quotientReachableA (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    X ⧸ reachableSubspace A B →ₗ[𝕜] X ⧸ reachableSubspace A B :=
  (reachableSubspace A B).mapQ (reachableSubspace A B) A
    ((Submodule.map_le_iff_le_comap).mp (map_reachableSubspace_le A B))

/-- **The quotient input map vanishes.** Since `im B ⊆ W = reachableSubspace A B`,
the composite `W.mkQ ∘ B` is the zero map. This is `B̄ = 0` of
Trentelman–Stoorvogel–Hautus, Section 3.4, equation (3.11). -/
theorem mkQ_reachableSubspace_comp (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    (reachableSubspace A B).mkQ.comp B = 0 := by
  ext u
  rw [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply]
  exact (Submodule.Quotient.mk_eq_zero (reachableSubspace A B)).mpr
    (range_le_reachableSubspace A B ⟨u, rfl⟩)

/-- **The quotient by the reachable subspace is completely uncontrollable.**
The quotient system has `B̄ = 0`, so its reachable subspace is `⊥`.

Source: Trentelman–Stoorvogel–Hautus, Section 3.4, equation (3.11). -/
theorem reachableSubspace_quotientReachable_eq_bot (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    reachableSubspace (quotientReachableA A B) (0 : U →ₗ[𝕜] X ⧸ reachableSubspace A B) =
      ⊥ :=
  reachableSubspace_zero (quotientReachableA A B)

/-- **The quotient input map is the zero map in the pair.** This is
`reachableSubspace_quotientReachable_eq_bot` stated with the explicit quotient
input map `W.mkQ ∘ B`. -/
theorem reachableSubspace_quotientReachable_mkQ (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    reachableSubspace (quotientReachableA A B) ((reachableSubspace A B).mkQ.comp B) = ⊥ := by
  rw [mkQ_reachableSubspace_comp]
  exact reachableSubspace_zero (quotientReachableA A B)

/-- **Complement block identity: `A₂₁ = 0`.** For any chosen complement `V` of
the reachable subspace `W`, the component of `A x` along `V` vanishes for
`x ∈ W`. This is the geometric content of the block `A₂₁ = 0` in the
two-block form of Theorem 3.11. -/
theorem reachableSubspace_compl_snd_eq_zero (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    {V : Submodule 𝕜 X} (h : IsCompl (reachableSubspace A B) V)
    {x : X} (hx : x ∈ reachableSubspace A B) :
    ((Submodule.prodEquivOfIsCompl (reachableSubspace A B) V h).symm (A x)).2 = 0 :=
  (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero (p := reachableSubspace A B) (q := V)
    h).mpr
    (map_reachableSubspace_le A B ⟨x, hx, rfl⟩)

/-- **Complement block identity: `B₂ = 0`.** For any chosen complement `V` of
the reachable subspace `W`, the component of `B u` along `V` vanishes. This is
the geometric content of the block `B₂ = 0` in the two-block form of
Theorem 3.11. -/
theorem range_compl_snd_eq_zero (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    {V : Submodule 𝕜 X} (h : IsCompl (reachableSubspace A B) V) (u : U) :
    ((Submodule.prodEquivOfIsCompl (reachableSubspace A B) V h).symm (B u)).2 = 0 :=
  (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero (p := reachableSubspace A B) (q := V)
    h).mpr
    (range_le_reachableSubspace A B (LinearMap.mem_range_self B u))

/-! ## Kalman decomposition: the unobservable quotient -/

/-- The induced state map `Ā` on the quotient `X ⧸ N` by the unobservable
subspace `N = unobservableSubspace C A`, which is `A`-invariant. -/
noncomputable def quotientUnobservableA (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    X ⧸ unobservableSubspace C A →ₗ[𝕜] X ⧸ unobservableSubspace C A :=
  (unobservableSubspace C A).mapQ (unobservableSubspace C A) A
    ((Submodule.map_le_iff_le_comap).mp (map_unobservableSubspace_le C A))

/-- The readout `C̄` descended to the quotient `X ⧸ N`, using `N ≤ ker C`. -/
noncomputable def quotientUnobservableC (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    X ⧸ unobservableSubspace C A →ₗ[𝕜] Y :=
  (unobservableSubspace C A).liftQ C (unobservableSubspace_le_ker C A)

/-- The quotient state map commutes with the quotient projection on powers:
`Āᵏ (x mod N) = (Aᵏ x) mod N`. -/
theorem quotientUnobservableA_pow_mkQ (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    ∀ (k : ℕ) (x : X),
      (quotientUnobservableA C A ^ k) ((unobservableSubspace C A).mkQ x) =
        (unobservableSubspace C A).mkQ ((A ^ k) x) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply]
      rw [show quotientUnobservableA C A ((unobservableSubspace C A).mkQ x) =
          (unobservableSubspace C A).mkQ (A x) from by
        simp [quotientUnobservableA]]
      rw [ih]
      rfl

/-- **The quotient by the unobservable subspace is observable.** With
`N = unobservableSubspace C A`, the induced pair `(C̄, Ā)` on `X ⧸ N` is
observable. This is the dual of the controllable-subsystem statement and is
the geometric form of the observable quotient in the Kalman decomposition.

Source: Trentelman–Stoorvogel–Hautus, Section 3.4 ("dual results can be given
for observability"). -/
theorem isObservable_quotientUnobservable (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    IsObservable (quotientUnobservableC C A) (quotientUnobservableA C A) := by
  rw [isObservable_iff, Submodule.eq_bot_iff]
  intro z hz
  rw [mem_unobservableSubspace] at hz
  obtain ⟨x, rfl⟩ := (unobservableSubspace C A).mkQ_surjective z
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [mem_unobservableSubspace]
  intro k
  have hpow := quotientUnobservableA_pow_mkQ C A k x
  have hk := hz k
  rw [hpow, quotientUnobservableC, Submodule.mkQ_apply, Submodule.liftQ_apply] at hk
  exact hk

/-! ## Kalman decomposition: the unobservable part -/

/-- The restriction of the state map `A` to the `A`-invariant unobservable
subspace `N = unobservableSubspace C A`. -/
noncomputable def unobservableRestrictionA (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    unobservableSubspace C A →ₗ[𝕜] unobservableSubspace C A :=
  A.restrict fun _ hx => map_unobservableSubspace_le C A ⟨_, hx, rfl⟩

/-- The readout restricted to the unobservable subspace. Since `N ≤ ker C`
this map is zero; this is the geometric content of `C|_N = 0`. -/
theorem unobservableRestrictionA_C_eq_zero (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    C.comp (unobservableSubspace C A).subtype = 0 := by
  ext x
  exact C_eq_zero_of_mem_unobservableSubspace (C := C) (A := A) (x := (x : X)) x.2

/-- **A pair with zero readout is completely unobservable.** The unobservable
subspace of `(0, A)` is `⊤`. -/
theorem unobservableSubspace_zero (A : X →ₗ[𝕜] X) :
    unobservableSubspace (0 : X →ₗ[𝕜] Y) A = ⊤ := by
  apply le_antisymm le_top
  intro x _
  rw [mem_unobservableSubspace]
  intro k
  simp

/-- **The restriction to the unobservable subspace is completely
unobservable.** Since the readout vanishes on `N`, the pair
`(C|_N, A|_N)` has unobservable subspace `⊤`. -/
theorem unobservableSubspace_restrict_eq_top (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    unobservableSubspace (C.comp (unobservableSubspace C A).subtype)
      (unobservableRestrictionA C A) = ⊤ := by
  rw [unobservableRestrictionA_C_eq_zero]
  exact unobservableSubspace_zero (unobservableRestrictionA C A)

/-- **Complement block identity: `A₂₁ = 0` for the unobservable subspace.**
For any chosen complement `V` of the unobservable subspace `N`, the component
of `A x` along `V` vanishes for `x ∈ N`. -/
theorem unobservableSubspace_compl_snd_eq_zero (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    {V : Submodule 𝕜 X} (h : IsCompl (unobservableSubspace C A) V)
    {x : X} (hx : x ∈ unobservableSubspace C A) :
    ((Submodule.prodEquivOfIsCompl (unobservableSubspace C A) V h).symm (A x)).2 = 0 :=
  (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero (p := unobservableSubspace C A) (q := V)
    h).mpr
    (map_unobservableSubspace_le C A ⟨x, hx, rfl⟩)

/-- **Complement block identity: `C|_N = 0`.** The readout vanishes on the
unobservable subspace, equivalently the component in `Y` of `C x` is zero for
`x ∈ N`. -/
theorem unobservableSubspace_compl_C_eq_zero (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    {x : X} (hx : x ∈ unobservableSubspace C A) : C x = 0 :=
  C_eq_zero_of_mem_unobservableSubspace hx

end LinearMap

namespace LinearSystem

open LinearMap

variable {𝕜 X U Y X' : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable [AddCommGroup X'] [Module 𝕜 X']

/-- **Coordinate invariance for a `LinearSystem`.** Changing state coordinates
by `e : X' ≃ₗ[𝕜] X` preserves controllability of the underlying pair.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.10 (i). -/
theorem isControllable_changeState (sys : LinearSystem 𝕜 X U Y) (e : X' ≃ₗ[𝕜] X) :
    IsControllable sys.A sys.B ↔
      IsControllable (sys.changeState e).A (sys.changeState e).B := by
  rw [changeState_A, changeState_B]
  exact LinearMap.isControllable_changeState sys.A sys.B e

/-- **Coordinate invariance of observability for a `LinearSystem`.** Changing
state coordinates by `e : X' ≃ₗ[𝕜] X` preserves observability of the
underlying pair.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.10 (ii). -/
theorem isObservable_changeState (sys : LinearSystem 𝕜 X U Y) (e : X' ≃ₗ[𝕜] X) :
    IsObservable sys.C sys.A ↔
      IsObservable (sys.changeState e).C (sys.changeState e).A := by
  rw [changeState_C, changeState_A]
  exact LinearMap.isObservable_changeState sys.C sys.A e

end LinearSystem
