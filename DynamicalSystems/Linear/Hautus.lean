/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Duality
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # The Hautus (PBH) eigenvalue criteria for linear pairs

This file proves the Popov–Belevitch–Hautus (PBH) eigenvalue criteria for the
coordinate-free algebraic pair APIs of `DynamicalSystems.Linear.Subspaces`, over
an algebraically closed field such as `ℂ`. The treatment adapts the complex
matrix proof of Gokhale and Bullo, *LeanForControl*, to the all-powers subspace
API used here. In particular the finite-boundary induction of the source is
replaced by the all-powers definitions
`LinearMap.reachableSubspace` / `LinearMap.unobservableSubspace`, and the
eigenvector extraction reuses `Module.End.exists_eigenvalue` on the invariant
unobservable subspace.

## Observability

* `LinearMap.exists_eigenvector_of_unobservableSubspace_neBot`: a nontrivial
  unobservable subspace contains a nonzero eigenvector of `A` lying in `ker C`.
* `LinearMap.isObservable_iff_hautus`: `(C, A)` is observable if and only if
  for every `μ` the Hautus observability map `(A - μ • 1).prod C` is injective,
  equivalently `A.eigenspace μ ⊓ ker C = ⊥`.

## Controllability

The controllability criterion is obtained by duality from the observability
criterion, using the accepted duality lemma
`LinearMap.isControllable_iff_isObservable_dualMap`. An annihilator calculation
relates the kernel of the dual pair's Hautus observability map to the range of
the Hautus controllability map `(A - μ • 1).coprod B`, namely
`range (A - μ • 1) ⊔ range B`.

* `LinearMap.isControllable_iff_hautus`: `(A, B)` is controllable if and only
  if for every `μ`, `range (A - μ • 1) ⊔ range B = ⊤`, equivalently the Hautus
  controllability map is surjective.

## Matrix forms

With bases of the state, input and output spaces, the coordinate-free
statements become full-rank statements for the PBH block matrices
`[A - μI; C]` and `[A - μI | B]`.

## Real matrices

The PBH criterion is stated over an algebraically closed field. For a real
matrix pair the eigenvalues of the complexification must be checked, so the
matrix form is applied after complexifying.

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Section 3.5, Theorem 3.13.
* A. Gokhale and F. Bullo, *LeanForControl*, commit
  `c5cedca904fe7b8168643c428b5cf5fd8b6ebf6d`, file
  `LeanForControl/LinearSystems/Hautus.lean` (Apache-2.0). The observability
  eigenvector argument is adapted from there; the blueprint annotations and
  custom axioms of that repository are not used.
-/

@[expose] public section

open Module

namespace LinearMap

variable {𝕜 X U Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-! ## The Hautus maps -/

/-- The **Hautus observability map** of the pair `(C, A)` at `μ`:
`x ↦ (A x - μ x, C x)`. Its kernel is `A.eigenspace μ ⊓ ker C`, so the PBH
condition that this kernel be trivial says that `μ` has no eigenvector of `A`
lying in `ker C`.

Source: Trentelman–Stoorvogel–Hautus, Section 3.5; the coordinate-free form of
the block row `[A - μI; C]`. -/
noncomputable def hautusObservabilityMap (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (μ : 𝕜) :
    X →ₗ[𝕜] X × Y :=
  (A - μ • 1).prod C

/-- The **Hautus controllability map** of the pair `(A, B)` at `μ`:
`(x, u) ↦ A x - μ x + B u`. Its range is `range (A - μ • 1) ⊔ range B`, so the
PBH condition that this map be surjective says that for every left eigenvector
`η` of `A` with eigenvalue `μ` one has `η B = 0 ⟹ η = 0`.

Source: Trentelman–Stoorvogel–Hautus, Section 3.5; the coordinate-free form of
the block column `[A - μI | B]`. -/
noncomputable def hautusControllabilityMap (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (μ : 𝕜) :
    X × U →ₗ[𝕜] X :=
  (A - μ • 1).coprod B

/-- The kernel of the Hautus observability map is
`Module.End.eigenspace A μ ⊓ ker C`. -/
theorem ker_hautusObservabilityMap (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (μ : 𝕜) :
    ker (hautusObservabilityMap C A μ) = Module.End.eigenspace A μ ⊓ ker C := by
  rw [hautusObservabilityMap, LinearMap.ker_prod, Module.End.eigenspace_def]

/-- The range of the Hautus controllability map is
`range (A - μ • 1) ⊔ range B`. -/
theorem range_hautusControllabilityMap (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (μ : 𝕜) :
    range (hautusControllabilityMap A B μ) = range (A - μ • 1) ⊔ range B := by
  rw [hautusControllabilityMap, LinearMap.range_coprod]

/-! ## Observability Hautus -/

/-- A nonzero eigenvector of `A` lying in `ker C` renders the pair `(C, A)`
non-observable: it is annihilated by every `C A ^ k`. This is the converse
direction of the PBH criterion and does not require finite dimension. -/
theorem hautus_witness_implies_not_isObservable (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (μ : 𝕜) (v : X) (hv : v ≠ 0) (hAv : A v = μ • v) (hCv : C v = 0) :
    ¬ IsObservable C A := by
  rw [isObservable_iff]
  intro hbot
  have hmem : v ∈ unobservableSubspace C A := by
    rw [mem_unobservableSubspace]
    intro k
    have hpow : (A ^ k) v = μ ^ k • v := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply, hAv, map_smul,
            ih, smul_smul]
          congr 1
          ring
    rw [hpow, map_smul, hCv, smul_zero]
  rw [hbot] at hmem
  exact hv (by simpa using hmem)

/-- **PBH failure direction for observability.** If `(C, A)` is not observable
over an algebraically closed field, then its unobservable subspace is a
nontrivial `A`-invariant subspace, and `Module.End.exists_eigenvalue` produces a
nonzero eigenvector of `A` inside it; since the unobservable subspace is
contained in `ker C`, this is a Hautus failure.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.13 (ii), first half; the
eigenvector extraction is adapted from `LeanForControl`. -/
theorem exists_eigenvector_of_unobservableSubspace_neBot [IsAlgClosed 𝕜]
    [FiniteDimensional 𝕜 X] (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (h : unobservableSubspace C A ≠ ⊥) :
    ∃ μ : 𝕜, ∃ v : X, v ≠ 0 ∧ A v = μ • v ∧ C v = 0 := by
  have : Nontrivial (unobservableSubspace C A) :=
    (Submodule.nontrivial_iff_ne_bot).mpr h
  let A_res : Module.End 𝕜 (unobservableSubspace C A) :=
    A.restrict fun _ hx => map_unobservableSubspace_le C A ⟨_, hx, rfl⟩
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A_res
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, w.val, ?_, ?_, ?_⟩
  · intro hzero
    exact hw.2 (Subtype.ext hzero)
  · have hval := congrArg Subtype.val hw.apply_eq_smul
    simpa [A_res, LinearMap.restrict_apply] using hval
  · exact C_eq_zero_of_mem_unobservableSubspace w.2

/-- **Observability Hautus criterion.** Over an algebraically closed field, a
finite-dimensional pair `(C, A)` is observable if and only if for every `μ` the
Hautus observability map `(A - μ • 1).prod C` has trivial kernel, equivalently
`A.eigenspace μ ⊓ ker C = ⊥`.

This is the coordinate-free form of "rank `[A - μI; C] = n` for every
eigenvalue" and uses the all-powers unobservable subspace.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.13 (ii). -/
theorem isObservable_iff_hautus [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 X]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    IsObservable C A ↔ ∀ μ : 𝕜, ker (hautusObservabilityMap C A μ) = ⊥ := by
  constructor
  · intro hObs μ
    rw [ker_hautusObservabilityMap, Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hAv, hCv⟩ := Submodule.mem_inf.mp hv
    by_contra hvne
    exact hautus_witness_implies_not_isObservable C A μ v hvne
      (Module.End.mem_eigenspace_iff.mp hAv) (mem_ker.mp hCv) hObs
  · intro hHautus
    by_contra hNotObs
    have hN : unobservableSubspace C A ≠ ⊥ := fun hbot => hNotObs hbot
    obtain ⟨μ, v, hv, hAv, hCv⟩ :=
      exists_eigenvector_of_unobservableSubspace_neBot C A hN
    have hmem : v ∈ ker (hautusObservabilityMap C A μ) := by
      rw [ker_hautusObservabilityMap]
      exact Submodule.mem_inf.mpr ⟨Module.End.mem_eigenspace_iff.mpr hAv, mem_ker.mpr hCv⟩
    rw [hHautus μ] at hmem
    exact hv (by simpa using hmem)

/-- Eigenspace form of the observability Hautus criterion. -/
theorem isObservable_iff_hautus_eigenspace [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 X]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    IsObservable C A ↔ ∀ μ : 𝕜, Module.End.eigenspace A μ ⊓ ker C = ⊥ := by
  rw [isObservable_iff_hautus]
  exact forall_congr' fun μ => by rw [ker_hautusObservabilityMap]

/-! ## Controllability Hautus by duality -/

/-- The dual of `A - μ • 1` is `A.dualMap - μ • 1`. -/
theorem dualMap_sub_smul_one (A : X →ₗ[𝕜] X) (μ : 𝕜) :
    (A - μ • 1).dualMap = A.dualMap - μ • (1 : Module.End 𝕜 (Module.Dual 𝕜 X)) := by
  ext g x
  simp [LinearMap.dualMap_apply]

/-- The kernel of the dual Hautus observability map is the annihilator of
`range (A - μ • 1) ⊔ range B`. -/
theorem ker_hautusObservabilityMap_dualMap (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (μ : 𝕜) :
    ker (hautusObservabilityMap B.dualMap A.dualMap μ) =
      (range (A - μ • 1) ⊔ range B).dualAnnihilator := by
  rw [hautusObservabilityMap, LinearMap.ker_prod, ← dualMap_sub_smul_one,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, ← Submodule.dualAnnihilator_sup_eq]

/-- **Controllability Hautus criterion.** Over an algebraically closed field, a
finite-dimensional pair `(A, B)` is controllable if and only if for every `μ`,
`range (A - μ • 1) ⊔ range B = ⊤`, equivalently the Hautus controllability map
`(A - μ • 1).coprod B` is surjective.

This is the dual of the observability criterion, using the accepted duality
`IsControllable A B ↔ IsObservable B.dualMap A.dualMap`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.13 (i). -/
theorem isControllable_iff_hautus [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 X]
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    IsControllable A B ↔ ∀ μ : 𝕜, range (A - μ • 1) ⊔ range B = ⊤ := by
  rw [isControllable_iff_isObservable_dualMap, isObservable_iff_hautus]
  refine forall_congr' fun μ => ?_
  rw [ker_hautusObservabilityMap_dualMap, Submodule.dualAnnihilator_eq_bot_iff]

/-- Surjectivity form of the controllability Hautus criterion. -/
theorem isControllable_iff_hautus_surjective [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 X]
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    IsControllable A B ↔
      ∀ μ : 𝕜, Function.Surjective (hautusControllabilityMap A B μ) := by
  rw [isControllable_iff_hautus]
  refine forall_congr' fun μ => ?_
  rw [← range_hautusControllabilityMap, LinearMap.range_eq_top]

/-! ## Matrix full-rank forms

With bases of the state, input and output spaces, the coordinate-free PBH
criteria become full-rank statements for the PBH block matrices `[A - μI; C]`
and `[A - μI | B]`. -/

section Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The **Hautus observability matrix** `[A - μI; C]` of `(C, A)` with respect
bases `bX` of `X` and `bY` of `Y`. Its rows are indexed by `ι ⊕ κ`. -/
noncomputable def hautusObservabilityMatrix (bX : Basis ι 𝕜 X) (bY : Basis κ 𝕜 Y)
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (μ : 𝕜) : Matrix (ι ⊕ κ) ι 𝕜 :=
  LinearMap.toMatrix bX (bX.prod bY) (hautusObservabilityMap C A μ)

/-- The **Hautus controllability matrix** `[A - μI | B]` of `(A, B)` with
respect to bases `bX` of `X` and `bU` of `U`. Its columns are indexed by
`ι ⊕ κ`. -/
noncomputable def hautusControllabilityMatrix (bX : Basis ι 𝕜 X) (bU : Basis κ 𝕜 U)
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (μ : 𝕜) : Matrix ι (ι ⊕ κ) 𝕜 :=
  LinearMap.toMatrix (bX.prod bU) bX (hautusControllabilityMap A B μ)

omit [DecidableEq κ] in
/-- The rank of the Hautus observability matrix is the dimension of the range of
the Hautus observability map. -/
theorem hautusObservabilityMatrix_rank (bX : Basis ι 𝕜 X) (bY : Basis κ 𝕜 Y)
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (μ : 𝕜) :
    (hautusObservabilityMatrix bX bY C A μ).rank =
      Module.finrank 𝕜 (range (hautusObservabilityMap C A μ)) := by
  rw [hautusObservabilityMatrix,
    Matrix.rank_eq_finrank_range_toLin _ (bX.prod bY) bX, Matrix.toLin_toMatrix]

/-- The rank of the Hautus controllability matrix is the dimension of the range
of the Hautus controllability map. -/
theorem hautusControllabilityMatrix_rank (bX : Basis ι 𝕜 X) (bU : Basis κ 𝕜 U)
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (μ : 𝕜) :
    (hautusControllabilityMatrix bX bU A B μ).rank =
      Module.finrank 𝕜 (range (hautusControllabilityMap A B μ)) := by
  rw [hautusControllabilityMatrix,
    Matrix.rank_eq_finrank_range_toLin _ bX (bX.prod bU), Matrix.toLin_toMatrix]

omit [DecidableEq κ] in
/-- **Matrix observability Hautus criterion.** Over an algebraically closed
field, `(C, A)` is observable if and only if the Hautus observability matrix
`[A - μI; C]` has full column rank for every `μ`. -/
theorem isObservable_iff_hautus_matrix_rank [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 X]
    (bX : Basis ι 𝕜 X) (bY : Basis κ 𝕜 Y) (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) :
    IsObservable C A ↔
      ∀ μ : 𝕜, (hautusObservabilityMatrix bX bY C A μ).rank = Module.finrank 𝕜 X := by
  rw [isObservable_iff_hautus]
  refine forall_congr' fun μ => ?_
  rw [hautusObservabilityMatrix_rank]
  constructor
  · intro hker
    have hrn := LinearMap.finrank_range_add_finrank_ker (hautusObservabilityMap C A μ)
    rw [hker] at hrn
    simpa using hrn
  · intro hrank
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hrn := LinearMap.finrank_range_add_finrank_ker (hautusObservabilityMap C A μ)
    rw [hrank] at hrn
    have hker0 : Module.finrank 𝕜 (ker (hautusObservabilityMap C A μ)) = 0 := by omega
    have hbot : ker (hautusObservabilityMap C A μ) = ⊥ :=
      Submodule.finrank_eq_zero.mp hker0
    rw [hbot] at hv
    simpa using hv

/-- **Matrix controllability Hautus criterion.** Over an algebraically closed
field, `(A, B)` is controllable if and only if the Hautus controllability
matrix `[A - μI | B]` has full row rank for every `μ`. -/
theorem isControllable_iff_hautus_matrix_rank [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 X]
    (bX : Basis ι 𝕜 X) (bU : Basis κ 𝕜 U) (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) :
    IsControllable A B ↔
      ∀ μ : 𝕜, (hautusControllabilityMatrix bX bU A B μ).rank = Module.finrank 𝕜 X := by
  rw [isControllable_iff_hautus]
  refine forall_congr' fun μ => ?_
  rw [← range_hautusControllabilityMap, hautusControllabilityMatrix_rank]
  constructor
  · intro htop
    rw [htop]
    simp
  · intro hrank
    exact Submodule.eq_top_of_finrank_eq hrank

end Matrix

/-! ## Real matrices and complexification

The PBH criterion is stated over an algebraically closed field, so for a real
matrix pair it must be applied after complexifying the entries. The bridges
below connect the real matrix pair, viewed through `Matrix.mulVecLin`, to its
complexification. They show that the complex unobservable subspace is trivial
exactly when the real unobservable subspace is, so the criterion is genuinely
about the real system while checking *complex* eigenvalues.

The key observation is that the complex realization of an unobservable vector
has a real or imaginary part that is real-unobservable, and conversely that the
complexification of a real-unobservable vector is complex-unobservable. -/

section RealComplexify

variable {m n p : Type*}

/-- Pointwise real part of a complex vector. -/
def reFun (v : n → ℂ) : n → ℝ := fun i => (v i).re

/-- Pointwise imaginary part of a complex vector. -/
def imFun (v : n → ℂ) : n → ℝ := fun i => (v i).im

/-- Pointwise inclusion of a real vector into complex vectors. -/
def ofRealFun (v : n → ℝ) : n → ℂ := fun i => (v i : ℂ)

@[simp]
theorem reFun_apply (v : n → ℂ) (i : n) : reFun v i = (v i).re := rfl

@[simp]
theorem imFun_apply (v : n → ℂ) (i : n) : imFun v i = (v i).im := rfl

@[simp]
theorem ofRealFun_apply (v : n → ℝ) (i : n) : ofRealFun v i = (v i : ℂ) := rfl

variable [Fintype n]

/-- The real part of a complex vector commutes with multiplication by a real
matrix, viewed through entrywise complexification. -/
theorem mulVecLin_complexify_re (A : Matrix m n ℝ) (v : n → ℂ) :
    Matrix.mulVecLin A (reFun v) =
      reFun (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)) v) := by
  ext i
  simp [Matrix.mulVec, dotProduct, reFun]

/-- The imaginary part of a complex vector commutes with multiplication by a
real matrix, viewed through entrywise complexification. -/
theorem mulVecLin_complexify_im (A : Matrix m n ℝ) (v : n → ℂ) :
    Matrix.mulVecLin A (imFun v) =
      imFun (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)) v) := by
  ext i
  simp [Matrix.mulVec, dotProduct, imFun]

/-- Entrywise complexification of a matrix commutes with entrywise inclusion of
a real vector. -/
theorem mulVecLin_complexify_ofReal (A : Matrix m n ℝ) (v : n → ℝ) :
    Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)) (ofRealFun v) =
      ofRealFun (Matrix.mulVecLin A v) := by
  ext i
  simp [Matrix.mulVec, dotProduct, ofRealFun]

/-- Powers of the complexification of a real matrix commute with taking real
parts. -/
theorem re_complex_pow (A : Matrix n n ℝ) (v : n → ℂ) (k : ℕ) :
    reFun ((Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)) ^ k) v) =
      (Matrix.mulVecLin A ^ k) (reFun v) := by
  induction k with
  | zero => ext i; simp [reFun]
  | succ k ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply,
        ← mulVecLin_complexify_re A ((Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)) ^ k) v), ih,
        pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]

/-- Powers of the complexification of a real matrix commute with taking
imaginary parts. -/
theorem im_complex_pow (A : Matrix n n ℝ) (v : n → ℂ) (k : ℕ) :
    imFun ((Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)) ^ k) v) =
      (Matrix.mulVecLin A ^ k) (imFun v) := by
  induction k with
  | zero => ext i; simp [imFun]
  | succ k ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply,
        ← mulVecLin_complexify_im A ((Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)) ^ k) v), ih,
        pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]

/-- Powers of the complexification of a real matrix commute with entrywise
inclusion of a real vector. -/
theorem ofReal_complex_pow (A : Matrix n n ℝ) (v : n → ℝ) (k : ℕ) :
    (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)) ^ k) (ofRealFun v) =
      ofRealFun ((Matrix.mulVecLin A ^ k) v) := by
  induction k with
  | zero => ext i; simp [ofRealFun]
  | succ k ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply, ih,
        pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply,
        ← mulVecLin_complexify_ofReal A ((Matrix.mulVecLin A ^ k) v)]

/-- The real part of a complex-unobservable vector is real-unobservable. -/
theorem reFun_mem_unobservableSubspace {A : Matrix n n ℝ} {C : Matrix p n ℝ} {w : n → ℂ}
    (hw : w ∈ unobservableSubspace (Matrix.mulVecLin (C.map (algebraMap ℝ ℂ)))
      (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)))) :
    reFun w ∈ unobservableSubspace (Matrix.mulVecLin C) (Matrix.mulVecLin A) := by
  rw [mem_unobservableSubspace] at hw ⊢
  intro k
  rw [← re_complex_pow A w k,
    mulVecLin_complexify_re C ((Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)) ^ k) w), hw k]
  ext i
  simp [reFun]

/-- The imaginary part of a complex-unobservable vector is real-unobservable. -/
theorem imFun_mem_unobservableSubspace {A : Matrix n n ℝ} {C : Matrix p n ℝ} {w : n → ℂ}
    (hw : w ∈ unobservableSubspace (Matrix.mulVecLin (C.map (algebraMap ℝ ℂ)))
      (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)))) :
    imFun w ∈ unobservableSubspace (Matrix.mulVecLin C) (Matrix.mulVecLin A) := by
  rw [mem_unobservableSubspace] at hw ⊢
  intro k
  rw [← im_complex_pow A w k,
    mulVecLin_complexify_im C ((Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)) ^ k) w), hw k]
  ext i
  simp [imFun]

/-- The entrywise inclusion of a real-unobservable vector is
complex-unobservable. -/
theorem ofRealFun_mem_unobservableSubspace {A : Matrix n n ℝ} {C : Matrix p n ℝ} {v : n → ℝ}
    (hv : v ∈ unobservableSubspace (Matrix.mulVecLin C) (Matrix.mulVecLin A)) :
    ofRealFun v ∈ unobservableSubspace (Matrix.mulVecLin (C.map (algebraMap ℝ ℂ)))
      (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ))) := by
  rw [mem_unobservableSubspace] at hv ⊢
  intro k
  rw [ofReal_complex_pow A v k,
    mulVecLin_complexify_ofReal C ((Matrix.mulVecLin A ^ k) v), hv k]
  ext i
  simp [ofRealFun]

/-- **Real-matrix complexification bridge for observability.** The real matrix
pair represented by `(Matrix.mulVecLin C, Matrix.mulVecLin A)` is observable if
and only if its entrywise complexification is observable over `ℂ`. Since the
complex criterion is the PBH condition over all *complex* eigenvalues, this
shows that the real criterion must be checked at complex eigenvalues.

Source: Trentelman–Stoorvogel–Hautus, Section 3.5; the complexification step
is the real-matrix bridge required when the PBH criterion is stated over an
algebraically closed field. -/
theorem isObservable_complexify_iff (C : Matrix p n ℝ) (A : Matrix n n ℝ) :
    IsObservable (Matrix.mulVecLin C) (Matrix.mulVecLin A) ↔
      IsObservable (Matrix.mulVecLin (C.map (algebraMap ℝ ℂ)))
        (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ))) := by
  constructor
  · intro h
    rw [isObservable_iff, Submodule.eq_bot_iff] at h ⊢
    intro w hw
    have hre := h (reFun w) (reFun_mem_unobservableSubspace hw)
    have him := h (imFun w) (imFun_mem_unobservableSubspace hw)
    ext i
    exact Complex.ext (by simpa using congrFun hre i) (by simpa using congrFun him i)
  · intro h
    rw [isObservable_iff, Submodule.eq_bot_iff] at h ⊢
    intro v hv
    have hof := h (ofRealFun v) (ofRealFun_mem_unobservableSubspace (A := A) (C := C) hv)
    ext i
    exact Complex.ofReal_eq_zero.mp (by simpa using congrFun hof i)

/-! ### Controllability complexification bridge -/

variable [Fintype m]

omit [Fintype n] in
/-- The real part of a finite sum of complex vectors. -/
theorem reFun_sum {ι : Type*} (s : Finset ι) (f : ι → n → ℂ) :
    reFun (s.sum f) = s.sum (fun i => reFun (f i)) := by
  ext j
  simp [reFun]

omit [Fintype n] in
/-- The imaginary part of a finite sum of complex vectors. -/
theorem imFun_sum {ι : Type*} (s : Finset ι) (f : ι → n → ℂ) :
    imFun (s.sum f) = s.sum (fun i => imFun (f i)) := by
  ext j
  simp [imFun]

omit [Fintype n] in
/-- The entrywise inclusion of a finite sum of real vectors. -/
theorem ofRealFun_sum {ι : Type*} (s : Finset ι) (f : ι → n → ℝ) :
    ofRealFun (s.sum f) = s.sum (fun i => ofRealFun (f i)) := by
  ext j
  simp [ofRealFun]

omit [Fintype n] in
/-- The real part of the entrywise inclusion of a real vector is the vector. -/
@[simp]
theorem reFun_ofRealFun (v : n → ℝ) : reFun (ofRealFun v) = v := by
  ext j
  simp [reFun, ofRealFun]

omit [Fintype n] in
/-- A complex vector is recovered from its real and imaginary parts. -/
theorem ofReal_re_add_I_smul_imFun (w : n → ℂ) :
    ofRealFun (reFun w) + Complex.I • ofRealFun (imFun w) = w := by
  ext j
  simp only [ofRealFun, reFun, imFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm Complex.I]
  exact Complex.re_add_im (w j)

/-- The real part of the complexified Kalman controllability map is the real
Kalman controllability map applied to the real parts. -/
theorem re_kalmanControllabilityMap (A : Matrix n n ℝ) (B : Matrix n m ℝ) (N : ℕ)
    (u : Fin N → m → ℂ) :
    reFun (kalmanControllabilityMap (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)))
      (Matrix.mulVecLin (B.map (algebraMap ℝ ℂ))) N u) =
    kalmanControllabilityMap (Matrix.mulVecLin A) (Matrix.mulVecLin B) N
      (fun k => reFun (u k)) := by
  rw [kalmanControllabilityMap_apply, kalmanControllabilityMap_apply, reFun_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [re_complex_pow A (Matrix.mulVecLin (B.map (algebraMap ℝ ℂ)) (u k)) (k : ℕ),
    ← mulVecLin_complexify_re B (u k)]

/-- The imaginary part of the complexified Kalman controllability map is the real
Kalman controllability map applied to the imaginary parts. -/
theorem im_kalmanControllabilityMap (A : Matrix n n ℝ) (B : Matrix n m ℝ) (N : ℕ)
    (u : Fin N → m → ℂ) :
    imFun (kalmanControllabilityMap (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)))
      (Matrix.mulVecLin (B.map (algebraMap ℝ ℂ))) N u) =
    kalmanControllabilityMap (Matrix.mulVecLin A) (Matrix.mulVecLin B) N
      (fun k => imFun (u k)) := by
  rw [kalmanControllabilityMap_apply, kalmanControllabilityMap_apply, imFun_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [im_complex_pow A (Matrix.mulVecLin (B.map (algebraMap ℝ ℂ)) (u k)) (k : ℕ),
    ← mulVecLin_complexify_im B (u k)]

/-- The complexified Kalman controllability map commutes with entrywise
inclusion of a real input sequence. -/
theorem ofReal_kalmanControllabilityMap (A : Matrix n n ℝ) (B : Matrix n m ℝ) (N : ℕ)
    (v : Fin N → m → ℝ) :
    kalmanControllabilityMap (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)))
      (Matrix.mulVecLin (B.map (algebraMap ℝ ℂ))) N (fun k => ofRealFun (v k)) =
    ofRealFun (kalmanControllabilityMap (Matrix.mulVecLin A) (Matrix.mulVecLin B) N v) := by
  rw [kalmanControllabilityMap_apply, kalmanControllabilityMap_apply, ofRealFun_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mulVecLin_complexify_ofReal B (v k),
    ofReal_complex_pow A ((Matrix.mulVecLin B) (v k)) (k : ℕ)]

/-- **Real-matrix complexification bridge for controllability.** The real matrix
pair represented by `(Matrix.mulVecLin A, Matrix.mulVecLin B)` is controllable if
and only if its entrywise complexification is controllable over `ℂ`. This is the
dual companion of `isObservable_complexify_iff` and forces the real criterion to
inspect non-real complex eigenvalues.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.13 (i). -/
theorem isControllable_complexify_iff (A : Matrix n n ℝ) (B : Matrix n m ℝ) :
    IsControllable (Matrix.mulVecLin A) (Matrix.mulVecLin B) ↔
      IsControllable (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)))
        (Matrix.mulVecLin (B.map (algebraMap ℝ ℂ))) := by
  rw [isControllable_iff_surjective_kalmanControllabilityMap,
    isControllable_iff_surjective_kalmanControllabilityMap,
    Module.finrank_fintype_fun_eq_card ℝ,
    Module.finrank_fintype_fun_eq_card ℂ]
  constructor
  · intro hsurj w
    obtain ⟨ure, hure⟩ := hsurj (reFun w)
    obtain ⟨uim, huim⟩ := hsurj (imFun w)
    refine ⟨fun k => ofRealFun (ure k) + Complex.I • ofRealFun (uim k), ?_⟩
    have hsplit : (fun k => ofRealFun (ure k) + Complex.I • ofRealFun (uim k)) =
        (fun k => ofRealFun (ure k)) + Complex.I • (fun k => ofRealFun (uim k)) := by
      ext k
      simp
    rw [hsplit, map_add, map_smul, ofReal_kalmanControllabilityMap,
      ofReal_kalmanControllabilityMap, hure, huim]
    exact ofReal_re_add_I_smul_imFun w
  · intro hsurj v
    obtain ⟨u, hu⟩ := hsurj (ofRealFun v)
    refine ⟨fun k => reFun (u k), ?_⟩
    rw [← re_kalmanControllabilityMap A B (Fintype.card n) u, hu, reFun_ofRealFun]

/-- **Real observability PBH criterion.** A real matrix pair `(C, A)` is
observable if and only if the complexified Hautus observability map has trivial
kernel at every *complex* `μ`. This combines `isObservable_complexify_iff` with
the complex PBH criterion, so non-real eigenvalues are genuinely inspected. -/
theorem isObservable_iff_hautus_complex (C : Matrix p n ℝ) (A : Matrix n n ℝ) :
    IsObservable (Matrix.mulVecLin C) (Matrix.mulVecLin A) ↔
      ∀ μ : ℂ, ker (hautusObservabilityMap
        (Matrix.mulVecLin (C.map (algebraMap ℝ ℂ)))
        (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ))) μ) = ⊥ := by
  rw [isObservable_complexify_iff, isObservable_iff_hautus]

/-- **Real controllability PBH criterion.** A real matrix pair `(A, B)` is
controllable if and only if the complexified Hautus controllability map is
surjective at every *complex* `μ`. This combines
`isControllable_complexify_iff` with the complex PBH criterion. -/
theorem isControllable_iff_hautus_complex (A : Matrix n n ℝ) (B : Matrix n m ℝ) :
    IsControllable (Matrix.mulVecLin A) (Matrix.mulVecLin B) ↔
      ∀ μ : ℂ, range (Matrix.mulVecLin (A.map (algebraMap ℝ ℂ)) - μ • 1) ⊔
        range (Matrix.mulVecLin (B.map (algebraMap ℝ ℂ))) = ⊤ := by
  rw [isControllable_complexify_iff, isControllable_iff_hautus]

end RealComplexify

end LinearMap
