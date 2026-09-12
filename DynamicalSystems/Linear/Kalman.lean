/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Subspaces
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Logic.Equiv.Prod

/-! # Finite Krylov descriptions of the reachable and unobservable subspaces

The algebraic definitions in `DynamicalSystems.Linear.Subspaces` describe the
reachable subspace `reachableSubspace A B = ⨆ k : ℕ, range ((A ^ k).comp B)` and
the unobservable subspace `unobservableSubspace C A = ⨅ k : ℕ, ker (C.comp (A ^ k))`
as suprema/infima over *all* natural powers. The Cayley–Hamilton theorem shows
that only the powers below the state dimension are needed.

Using `LinearMap.pow_eq_aeval_mod_charpoly`, every power `A ^ k` is the
evaluation of the remainder of `X ^ k` modulo the characteristic polynomial
`A.charpoly`. That remainder either vanishes (so the power is zero) or has
`natDegree` strictly below `natDegree A.charpoly = Module.finrank 𝕜 X`. This is
the finite-dimensional Krylov reduction underlying
Trentelman–Stoorvogel–Hautus, Corollary 3.2 and the display (3.7) of Section 3.3.

* `LinearMap.exists_pow_eq_sum_finrank`: every power of `A` is a linear
  combination of the powers `A ^ i` with `i < Module.finrank 𝕜 X`;
* `LinearMap.reachableSubspace_eq_iSup_finrank`: the reachable subspace is the
  supremum of `range ((A ^ k).comp B)` over `k : Fin (Module.finrank 𝕜 X)`;
* `LinearMap.unobservableSubspace_eq_iInf_finrank`: the unobservable subspace
  is the infimum of `ker (C.comp (A ^ k))` over `k : Fin (Module.finrank 𝕜 X)`.

Both statements include the zero-dimensional case: when `Module.finrank 𝕜 X = 0`
the index type `Fin 0` is empty, and the corresponding supremum/infimum is
`⊥`/`⊤`; the auxiliary reduction handles the (necessarily zero) remainder
separately, since `natDegree` of the zero polynomial gives no bound.

We also record the coordinate-free Kalman controllability and observability maps
with their range and kernel descriptions, together with surjectivity,
injectivity and rank criteria.

## Main definitions

* `LinearMap.kalmanControllabilityMap`, `LinearMap.kalmanObservabilityMap`

## Main theorems

* `LinearMap.reachableSubspace_eq_iSup_finrank`
* `LinearMap.unobservableSubspace_eq_iInf_finrank`

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Corollary 3.2 and Section 3.3.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 X U Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ]

open Polynomial
open Module

/-! ### Cayley–Hamilton reduction of powers -/

/-- **Cayley–Hamilton reduction of powers.** For an endomorphism `A` of a
finite-dimensional `𝕜`-vector space `X`, every power `A ^ k` is a linear
combination of the powers `A ^ i` with `i < Module.finrank 𝕜 X`.

This is the finite Krylov reduction obtained from
`LinearMap.pow_eq_aeval_mod_charpoly` and `Polynomial.aeval_eq_sum_range'`. The
remainder of `X ^ k` modulo `A.charpoly` is treated separately: if it vanishes
then `A ^ k = 0`, which together with the empty-index convention covers the
zero-dimensional case.

Source: Trentelman–Stoorvogel–Hautus, Corollary 3.2 (Cayley–Hamilton step). -/
theorem exists_pow_eq_sum_finrank [FiniteDimensional 𝕜 X] (A : X →ₗ[𝕜] X) (k : ℕ) :
    ∃ c : Fin (Module.finrank 𝕜 X) → 𝕜,
      A ^ k = ∑ i : Fin (Module.finrank 𝕜 X), c i • A ^ (i : ℕ) := by
  by_cases hr : Polynomial.X ^ k %ₘ A.charpoly = 0
  · refine ⟨0, ?_⟩
    have hzero : A ^ k = 0 := by
      rw [A.pow_eq_aeval_mod_charpoly k, hr, map_zero]
    rw [hzero]
    simp
  · have hq : A.charpoly ≠ 1 := fun hc => hr (by rw [hc, Polynomial.modByMonic_one])
    have hdeg : (Polynomial.X ^ k %ₘ A.charpoly).natDegree < Module.finrank 𝕜 X := by
      rw [← A.charpoly_natDegree]
      exact Polynomial.natDegree_modByMonic_lt _ A.charpoly_monic hq
    refine ⟨fun i => (Polynomial.X ^ k %ₘ A.charpoly).coeff (i : ℕ), ?_⟩
    rw [A.pow_eq_aeval_mod_charpoly k, Polynomial.aeval_eq_sum_range' hdeg A,
      Finset.sum_range]

/-! ### Finite descriptions of the pair subspaces -/

/-- **Finite Krylov description of the reachable subspace.** The reachable
subspace is the supremum of the ranges of `(A ^ k).comp B` for `k` below the
state dimension.

Source: Trentelman–Stoorvogel–Hautus, Corollary 3.2 and Corollary 3.3. -/
theorem reachableSubspace_eq_iSup_finrank [FiniteDimensional 𝕜 X]
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    reachableSubspace A B =
      ⨆ k : Fin (Module.finrank 𝕜 X), range ((A ^ (k : ℕ)).comp B) := by
  apply le_antisymm
  · rw [reachableSubspace]
    refine iSup_le fun k => ?_
    obtain ⟨c, hc⟩ := A.exists_pow_eq_sum_finrank k
    rintro x ⟨u, rfl⟩
    rw [hc]
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ (c i)
      (le_iSup (fun j : Fin (Module.finrank 𝕜 X) =>
        range ((A ^ (j : ℕ)).comp B)) i (LinearMap.mem_range_self _ u))
  · rw [reachableSubspace]
    exact iSup_le fun k => le_iSup (fun j : ℕ => range ((A ^ j).comp B)) (k : ℕ)

/-- **Finite Krylov description of the unobservable subspace.** The unobservable
subspace is the infimum of the kernels of `C.comp (A ^ k)` for `k` below the
state dimension.

Source: Trentelman–Stoorvogel–Hautus, Section 3.3, display (3.7). -/
theorem unobservableSubspace_eq_iInf_finrank [FiniteDimensional 𝕜 X]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    unobservableSubspace C A =
      ⨅ k : Fin (Module.finrank 𝕜 X), ker (C.comp (A ^ (k : ℕ))) := by
  apply le_antisymm
  · rw [unobservableSubspace]
    exact le_iInf fun k => iInf_le (fun j : ℕ => ker (C.comp (A ^ j))) (k : ℕ)
  · rw [unobservableSubspace]
    refine le_iInf fun k => ?_
    obtain ⟨c, hc⟩ := A.exists_pow_eq_sum_finrank k
    intro x hx
    rw [mem_ker, comp_apply, hc, LinearMap.sum_apply, map_sum]
    simp only [LinearMap.smul_apply, map_smul]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi : x ∈ ker (C.comp (A ^ (i : ℕ))) :=
      iInf_le (fun j : Fin (Module.finrank 𝕜 X) =>
        ker (C.comp (A ^ (j : ℕ)))) i hx
    rw [mem_ker, comp_apply] at hi
    rw [hi, smul_zero]

/-! ### Kalman controllability and observability maps -/

/-- The Kalman controllability map `(u_0, …, u_{n-1}) ↦ ∑_{k<n} A ^ k (B u_k)`.

Its range is the reachable subspace truncated to the first `n` powers of `A`;
taking `n = Module.finrank 𝕜 X` recovers `reachableSubspace A B` by
`LinearMap.reachableSubspace_eq_iSup_finrank`. -/
noncomputable def kalmanControllabilityMap (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (n : ℕ) :
    (Fin n → U) →ₗ[𝕜] X :=
  ∑ k : Fin n, (A ^ (k : ℕ)).comp (B.comp (LinearMap.proj k))

/-- Evaluation lemma for the Kalman controllability map. -/
@[simp]
theorem kalmanControllabilityMap_apply (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (n : ℕ)
    (u : Fin n → U) :
    kalmanControllabilityMap A B n u =
      ∑ k : Fin n, (A ^ (k : ℕ)) (B (u k)) := by
  simp [kalmanControllabilityMap]

/-- The range of the Kalman controllability map is the supremum of the ranges of
`(A ^ k).comp B` over `k < n`. -/
theorem range_kalmanControllabilityMap (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (n : ℕ) :
    range (kalmanControllabilityMap A B n) =
      ⨆ k : Fin n, range ((A ^ (k : ℕ)).comp B) := by
  apply le_antisymm
  · rintro x ⟨u, rfl⟩
    rw [kalmanControllabilityMap_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    exact le_iSup (fun j : Fin n => range ((A ^ (j : ℕ)).comp B)) k
      (LinearMap.mem_range_self _ (u k))
  · refine iSup_le fun k => ?_
    rintro x ⟨u, rfl⟩
    refine ⟨Pi.single k u, ?_⟩
    rw [kalmanControllabilityMap_apply, Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, map_zero, map_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk

/-- The Kalman observability map `x ↦ (C x, C A x, …, C A^{n-1} x)`.

Its kernel is the unobservable subspace truncated to the first `n` powers of
`A`; taking `n = Module.finrank 𝕜 X` recovers `unobservableSubspace C A` by
`LinearMap.unobservableSubspace_eq_iInf_finrank`. -/
noncomputable def kalmanObservabilityMap (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (n : ℕ) :
    X →ₗ[𝕜] (Fin n → Y) :=
  LinearMap.pi fun k : Fin n => C.comp (A ^ (k : ℕ))

/-- Evaluation lemma for the Kalman observability map. -/
@[simp]
theorem kalmanObservabilityMap_apply (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (n : ℕ) (x : X) :
    kalmanObservabilityMap C A n x = fun k : Fin n => C ((A ^ (k : ℕ)) x) := by
  rfl

/-- The kernel of the Kalman observability map is the infimum of the kernels of
`C.comp (A ^ k)` over `k < n`. -/
theorem ker_kalmanObservabilityMap (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (n : ℕ) :
    ker (kalmanObservabilityMap C A n) =
      ⨅ k : Fin n, ker (C.comp (A ^ (k : ℕ))) := by
  rw [kalmanObservabilityMap, LinearMap.ker_pi]

/-- The reachable subspace is the range of the Kalman controllability map. -/
theorem reachableSubspace_eq_range_kalmanControllabilityMap [FiniteDimensional 𝕜 X]
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    reachableSubspace A B =
      range (kalmanControllabilityMap A B (Module.finrank 𝕜 X)) := by
  rw [reachableSubspace_eq_iSup_finrank, range_kalmanControllabilityMap]

/-- The unobservable subspace is the kernel of the Kalman observability map. -/
theorem unobservableSubspace_eq_ker_kalmanObservabilityMap [FiniteDimensional 𝕜 X]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    unobservableSubspace C A =
      ker (kalmanObservabilityMap C A (Module.finrank 𝕜 X)) := by
  rw [unobservableSubspace_eq_iInf_finrank, ker_kalmanObservabilityMap]

/-! ### Surjectivity, injectivity and rank criteria -/

/-- `(A, B)` is controllable exactly when the Kalman controllability map is
surjective. -/
theorem isControllable_iff_surjective_kalmanControllabilityMap [FiniteDimensional 𝕜 X]
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    IsControllable A B ↔
      Function.Surjective (kalmanControllabilityMap A B (Module.finrank 𝕜 X)) := by
  rw [isControllable_iff, reachableSubspace_eq_range_kalmanControllabilityMap,
    LinearMap.range_eq_top]

/-- `(C, A)` is observable exactly when the Kalman observability map is
injective. -/
theorem isObservable_iff_injective_kalmanObservabilityMap [FiniteDimensional 𝕜 X]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    IsObservable C A ↔
      Function.Injective (kalmanObservabilityMap C A (Module.finrank 𝕜 X)) := by
  rw [isObservable_iff, unobservableSubspace_eq_ker_kalmanObservabilityMap,
    LinearMap.ker_eq_bot]

/-- **Rank criterion for controllability.** `(A, B)` is controllable exactly
when the range of the Kalman controllability map has full dimension. -/
theorem isControllable_iff_finrank_range_kalmanControllabilityMap [FiniteDimensional 𝕜 X]
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    IsControllable A B ↔
      Module.finrank 𝕜 (range (kalmanControllabilityMap A B (Module.finrank 𝕜 X))) =
        Module.finrank 𝕜 X := by
  rw [isControllable_iff, reachableSubspace_eq_range_kalmanControllabilityMap]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    exact Submodule.eq_top_of_finrank_eq h

/-- **Rank criterion for observability.** `(C, A)` is observable exactly when
the kernel of the Kalman observability map has dimension zero. -/
theorem isObservable_iff_finrank_ker_kalmanObservabilityMap [FiniteDimensional 𝕜 X]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    IsObservable C A ↔
      Module.finrank 𝕜 (ker (kalmanObservabilityMap C A (Module.finrank 𝕜 X))) = 0 := by
  rw [isObservable_iff, unobservableSubspace_eq_ker_kalmanObservabilityMap]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    exact Submodule.finrank_eq_zero.mp h

/-! ### Basis-dependent Kalman matrices

With bases `bX` of the state space and `bU` of the input space, the Kalman
controllability matrix is the matrix of `kalmanControllabilityMap` with respect
to `bX` and the product basis of `Fin n → U` induced by `bU`. Its rank equals
the dimension of the reachable subspace, giving the matrix rank criterion of
Trentelman–Stoorvogel–Hautus, Corollary 3.4 (iii). Dually, the Kalman
observability matrix has rank equal to the dimension of the range of the
observability map, giving Theorem 3.8 (v). -/

/-- The product basis of `Fin n → U` induced by a basis of `U`. -/
noncomputable def piBasis (bU : Basis κ 𝕜 U) (n : ℕ) :
    Basis (Fin n × κ) 𝕜 (Fin n → U) :=
  (Pi.basis fun _ : Fin n => bU).reindex (Equiv.sigmaEquivProd (Fin n) κ)

/-- The Kalman controllability matrix `[B AB ⋯ A^{n-1}B]` of `(A, B)` with
respect to bases `bX` of `X` and `bU` of `U`. -/
noncomputable def kalmanControllabilityMatrix {n : ℕ} (bX : Basis (Fin n) 𝕜 X)
    (bU : Basis κ 𝕜 U) (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    Matrix (Fin n) (Fin n × κ) 𝕜 := by
  classical
  exact LinearMap.toMatrix (piBasis bU n) bX (kalmanControllabilityMap A B n)

/-- The rank of the Kalman controllability matrix is the dimension of the range
of the Kalman controllability map. -/
theorem kalmanControllabilityMatrix_rank {n : ℕ} (bX : Basis (Fin n) 𝕜 X)
    (bU : Basis κ 𝕜 U) (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    (kalmanControllabilityMatrix bX bU A B).rank =
      Module.finrank 𝕜 (range (kalmanControllabilityMap A B n)) := by
  classical
  rw [kalmanControllabilityMatrix,
    Matrix.rank_eq_finrank_range_toLin _ bX (piBasis bU n),
    Matrix.toLin_toMatrix]

/-- **Matrix rank criterion for controllability.** `(A, B)` is controllable
exactly when the Kalman controllability matrix has full rank. -/
theorem isControllable_iff_kalmanControllabilityMatrix_rank [FiniteDimensional 𝕜 X]
    (bX : Basis (Fin (Module.finrank 𝕜 X)) 𝕜 X) (bU : Basis κ 𝕜 U)
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    IsControllable A B ↔
      (kalmanControllabilityMatrix bX bU A B).rank = Module.finrank 𝕜 X := by
  rw [isControllable_iff_finrank_range_kalmanControllabilityMap,
    ← kalmanControllabilityMatrix_rank bX bU A B]

/-- The Kalman observability matrix of `(C, A)` with respect to bases `bX` of
`X` and `bY` of `Y`. -/
noncomputable def kalmanObservabilityMatrix (bX : Basis ι 𝕜 X)
    (bY : Basis κ 𝕜 Y) (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (n : ℕ) :
    Matrix (Fin n × κ) ι 𝕜 := by
  classical
  exact LinearMap.toMatrix bX (piBasis bY n) (kalmanObservabilityMap C A n)

/-- The rank of the Kalman observability matrix is the dimension of the range of
the Kalman observability map. -/
theorem kalmanObservabilityMatrix_rank (bX : Basis ι 𝕜 X) (bY : Basis κ 𝕜 Y)
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (n : ℕ) :
    (kalmanObservabilityMatrix bX bY C A n).rank =
      Module.finrank 𝕜 (range (kalmanObservabilityMap C A n)) := by
  classical
  rw [kalmanObservabilityMatrix,
    Matrix.rank_eq_finrank_range_toLin _ (piBasis bY n) bX,
    Matrix.toLin_toMatrix]

/-- **Matrix rank criterion for observability.** `(C, A)` is observable exactly
when the Kalman observability matrix has full rank. -/
theorem isObservable_iff_kalmanObservabilityMatrix_rank [FiniteDimensional 𝕜 X]
    (bX : Basis ι 𝕜 X) (bY : Basis κ 𝕜 Y) (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    IsObservable C A ↔
      (kalmanObservabilityMatrix bX bY C A (Module.finrank 𝕜 X)).rank =
        Module.finrank 𝕜 X := by
  rw [isObservable_iff_finrank_ker_kalmanObservabilityMap,
    kalmanObservabilityMatrix_rank]
  constructor
  · intro hker
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (kalmanObservabilityMap C A (Module.finrank 𝕜 X))
    rw [hker, add_zero] at hrn
    exact hrn
  · intro hrange
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (kalmanObservabilityMap C A (Module.finrank 𝕜 X))
    rw [hrange] at hrn
    omega

end LinearMap
