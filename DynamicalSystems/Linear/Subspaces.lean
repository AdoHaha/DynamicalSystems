/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Basic
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.LinearMap.End

/-! # Reachable and unobservable subspaces of a linear pair

This file formalises the algebraic pair APIs attached to the structural results
of Chapters 3–4 of Trentelman, Stoorvogel and Hautus, *Control Theory for Linear
Systems*. For linear maps `A : X →ₗ[𝕜] X`, `B : U →ₗ[𝕜] X` and
`C : X →ₗ[𝕜] Y` we define

* `LinearMap.reachableSubspace A B`, the reachable subspace
  `⨆ k, range ((A ^ k).comp B)`;
* `LinearMap.unobservableSubspace C A`, the unobservable subspace
  `⨅ k, ker (C.comp (A ^ k))`;
* `LinearMap.IsControllable A B`, meaning `reachableSubspace A B = ⊤`;
* `LinearMap.IsObservable C A`, meaning `unobservableSubspace C A = ⊥`.

The main results are the two extremal characterisations:

* `LinearMap.reachableSubspace_le`: the reachable subspace is the *least*
  `A`-invariant subspace containing `range B`
  (Trentelman–Stoorvogel–Hautus, Corollary 3.3);
* `LinearMap.le_unobservableSubspace`: the unobservable subspace is the
  *greatest* `A`-invariant subspace contained in `ker C`
  (Trentelman–Stoorvogel–Hautus, Section 3.3).

Their companions `LinearMap.range_le_reachableSubspace`,
`LinearMap.unobservableSubspace_le_ker`, `LinearMap.map_reachableSubspace_le` and
`LinearMap.map_unobservableSubspace_le` state containment and invariance
explicitly. No finite-dimensionality hypothesis is required for any of the
statements in this file.

## Main definitions

* `LinearMap.reachableSubspace`, `LinearMap.unobservableSubspace`
* `LinearMap.IsControllable`, `LinearMap.IsObservable`

## Main theorems

* `LinearMap.reachableSubspace_le`, `LinearMap.le_unobservableSubspace`
* `LinearMap.map_reachableSubspace_le`, `LinearMap.map_unobservableSubspace_le`
* `LinearMap.range_le_reachableSubspace`, `LinearMap.unobservableSubspace_le_ker`

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Sections 3.2–3.3.
-/

@[expose] public section

namespace Submodule

variable {𝕜 X : Type*} [Field 𝕜] [AddCommGroup X] [Module 𝕜 X]

/-- If a subspace `V` is invariant under `A` (i.e. `Submodule.map A V ≤ V`), then
it is invariant under every power of `A`. This is the elementary induction that
underlies the extremal characterisations of the reachable and unobservable
subspaces. -/
theorem map_pow_le {A : X →ₗ[𝕜] X} {V : Submodule 𝕜 X}
    (hA : Submodule.map A V ≤ V) (k : ℕ) : Submodule.map (A ^ k) V ≤ V := by
  induction k with
  | zero =>
      rw [pow_zero, Module.End.one_eq_id]
      exact le_of_eq (map_id V)
  | succ k ih =>
      rw [Module.End.iterate_succ, Submodule.map_comp]
      exact le_trans (Submodule.map_mono hA) ih

end Submodule

namespace LinearMap

variable {𝕜 X U Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-! ### Definitions -/

/-- The reachable subspace of the pair `(A, B)`, i.e. the supremum of the ranges
of `(A ^ k).comp B` over all `k : ℕ`.

This is the algebraic version of the reachable space `W` of
Trentelman–Stoorvogel–Hautus, Corollary 3.2. -/
def reachableSubspace (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) : Submodule 𝕜 X :=
  ⨆ k : ℕ, LinearMap.range ((A ^ k).comp B)

/-- The unobservable subspace of the pair `(C, A)`, i.e. the infimum of the
kernels of `C.comp (A ^ k)` over all `k : ℕ`.

This is the algebraic version of `⟨ker C | A⟩` of
Trentelman–Stoorvogel–Hautus, Section 3.3. -/
def unobservableSubspace (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) : Submodule 𝕜 X :=
  ⨅ k : ℕ, LinearMap.ker (C.comp (A ^ k))

/-- The pair `(A, B)` is controllable if its reachable subspace is the whole
state space. -/
def IsControllable (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) : Prop :=
  reachableSubspace A B = ⊤

/-- The pair `(C, A)` is observable if its unobservable subspace is trivial. -/
def IsObservable (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) : Prop :=
  unobservableSubspace C A = ⊥

/-! ### Membership and containment lemmas -/

/-- Every element of `range B` lies in the reachable subspace. -/
theorem range_le_reachableSubspace (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    range B ≤ reachableSubspace A B := by
  rw [reachableSubspace]
  refine le_trans ?_ (le_iSup (fun k => range ((A ^ k).comp B)) 0)
  rintro x ⟨u, rfl⟩
  exact ⟨u, by simp⟩

/-- A particular image `(A ^ k) (B u)` lies in the reachable subspace. -/
theorem mem_reachableSubspace_of_mem (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (k : ℕ) (u : U) :
    (A ^ k) (B u) ∈ reachableSubspace A B := by
  rw [reachableSubspace]
  exact Submodule.mem_iSup_of_mem k ⟨u, rfl⟩

/-- The reachable subspace contains `range B`. -/
theorem mem_reachableSubspace_of_mem_range {A : X →ₗ[𝕜] X} {B : U →ₗ[𝕜] X} {x : X}
    (hx : x ∈ range B) : x ∈ reachableSubspace A B :=
  range_le_reachableSubspace A B hx

/-- Membership in the unobservable subspace: a state is unobservable exactly
when every `C A ^ k` annihilates it. This is the zero-input output condition of
Trentelman–Stoorvogel–Hautus, Section 3.3. -/
theorem mem_unobservableSubspace {C : X →ₗ[𝕜] Y} {A : X →ₗ[𝕜] X} {x : X} :
    x ∈ unobservableSubspace C A ↔ ∀ k : ℕ, C ((A ^ k) x) = 0 := by
  rw [unobservableSubspace, Submodule.mem_iInf]
  simp only [mem_ker, comp_apply]

/-- The unobservable subspace is contained in `ker C`: an unobservable state
produces zero output under zero input. -/
theorem unobservableSubspace_le_ker (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    unobservableSubspace C A ≤ ker C := by
  rw [unobservableSubspace]
  exact le_trans (iInf_le (fun k => ker (C.comp (A ^ k))) 0)
    (le_of_eq (by rw [pow_zero, Module.End.one_eq_id, LinearMap.comp_id]))

/-- Unobservable states have zero instantaneous output. -/
theorem C_eq_zero_of_mem_unobservableSubspace {C : X →ₗ[𝕜] Y} {A : X →ₗ[𝕜] X} {x : X}
    (hx : x ∈ unobservableSubspace C A) : C x = 0 :=
  mem_ker.mp (unobservableSubspace_le_ker C A hx)

/-! ### Extremal characterisations -/

/-- The reachable subspace is the *least* `A`-invariant subspace containing
`range B`. Equivalently, if `V` contains `range B` and is `A`-invariant, then it
contains the reachable subspace.

Source: Trentelman–Stoorvogel–Hautus, Corollary 3.3. -/
theorem reachableSubspace_le (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    {V : Submodule 𝕜 X} (hB : range B ≤ V) (hA : Submodule.map A V ≤ V) :
    reachableSubspace A B ≤ V := by
  rw [reachableSubspace]
  refine iSup_le fun k => ?_
  rw [range_comp]
  exact le_trans (Submodule.map_mono hB) (Submodule.map_pow_le hA k)

/-- The unobservable subspace is the *greatest* `A`-invariant subspace contained
in `ker C`. Equivalently, if `V` is `A`-invariant and `V ≤ ker C`, then
`V` is contained in the unobservable subspace.

Source: Trentelman–Stoorvogel–Hautus, Section 3.3. -/
theorem le_unobservableSubspace (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    {V : Submodule 𝕜 X} (hC : V ≤ ker C) (hA : Submodule.map A V ≤ V) :
    V ≤ unobservableSubspace C A := by
  rw [unobservableSubspace]
  refine le_iInf fun k => ?_
  intro x hx
  rw [mem_ker, comp_apply]
  exact mem_ker.mp (hC (Submodule.map_pow_le hA k ⟨x, hx, rfl⟩))

/-! ### Invariance -/

/-- The reachable subspace is `A`-invariant. -/
theorem map_reachableSubspace_le (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    Submodule.map A (reachableSubspace A B) ≤ reachableSubspace A B := by
  rw [reachableSubspace, Submodule.map_iSup]
  refine iSup_le fun k => ?_
  calc Submodule.map A (range ((A ^ k).comp B))
      = range (A.comp ((A ^ k).comp B)) := (range_comp ((A ^ k).comp B) A).symm
    _ = range ((A ^ (k + 1)).comp B) := by
          rw [Module.End.iterate_succ', LinearMap.comp_assoc]
    _ ≤ ⨆ j, range ((A ^ j).comp B) := le_iSup (fun j => range ((A ^ j).comp B)) (k + 1)

/-- The unobservable subspace is `A`-invariant. -/
theorem map_unobservableSubspace_le (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    Submodule.map A (unobservableSubspace C A) ≤ unobservableSubspace C A := by
  rw [unobservableSubspace]
  refine le_iInf fun k => ?_
  intro y hy
  rw [Submodule.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [mem_ker, comp_apply]
  have hx' : x ∈ ker (C.comp (A ^ (k + 1))) :=
    iInf_le (fun j => ker (C.comp (A ^ j))) (k + 1) hx
  rw [mem_ker, comp_apply] at hx'
  simpa only [Module.End.iterate_succ, comp_apply] using hx'

/-- The reachable subspace belongs to Mathlib's lattice of invariant submodules. -/
theorem reachableSubspace_mem_invtSubmodule (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    reachableSubspace A B ∈ Module.End.invtSubmodule A :=
  (Module.End.mem_invtSubmodule_iff_map_le A).mpr (map_reachableSubspace_le A B)

/-- The unobservable subspace belongs to Mathlib's lattice of invariant submodules. -/
theorem unobservableSubspace_mem_invtSubmodule (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    unobservableSubspace C A ∈ Module.End.invtSubmodule A :=
  (Module.End.mem_invtSubmodule_iff_map_le A).mpr (map_unobservableSubspace_le C A)

/-! ### Controllability and observability -/

/-- Unfolding lemma for controllability. -/
theorem isControllable_iff (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    IsControllable A B ↔ reachableSubspace A B = ⊤ := Iff.rfl

/-- Unfolding lemma for observability. -/
theorem isObservable_iff (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    IsObservable C A ↔ unobservableSubspace C A = ⊥ := Iff.rfl

end LinearMap
