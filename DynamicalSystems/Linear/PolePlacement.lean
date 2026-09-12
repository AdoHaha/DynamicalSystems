/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Duality
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.AdjoinRoot

/-! # Pole placement for finite-dimensional real linear systems

This file develops the algebraic pole-placement theorem for finite-dimensional
real controllable pairs, in the coordinate-free formulation of
Trentelman–Stoorvogel–Hautus, *Control Theory for Linear Systems*,
Theorem 3.29.

For a pair `(A, B)` with `A : X →ₗ[ℝ] X` and `B : U →ₗ[ℝ] X` and
`FiniteDimensional ℝ X`, state feedback `u = F x + v` produces the closed-loop
state map `A + B.comp F`. The characteristic polynomial of the closed loop is
`(A + B.comp F).charpoly`, and the pole-placement problem asks for a real
feedback `F` realising a prescribed monic real polynomial.

The complex conjugate poles of a real system are represented here by the real
coefficients of the target polynomial: the target `p` is an arbitrary monic
`ℝ[X]` of degree `finrank ℝ X`, so its non-real roots automatically come in
conjugate pairs. No complex feedback is introduced.

## Main results

* `LinearMap.reachableSubspace_add_comp`: the reachable subspace is invariant
  under state feedback, `reachableSubspace (A + B.comp F) B = reachableSubspace A B`.
* `LinearMap.isControllable_add_comp`: controllability is invariant under state
  feedback.
* `LinearMap.isControllable_of_forall_exists_feedback_charpoly`: the converse
  (necessity) direction of pole placement: if every monic real polynomial of
  degree `finrank ℝ X` is realised by some feedback, then `(A, B)` is
  controllable.
* `LinearMap.charpoly_eq_of_companion`: a linear map acting on a basis by the
  companion relations of a monic `p` has `charpoly = p`, proved via
  `AdjoinRoot`/`PowerBasis` without determinant expansion.
* `LinearMap.exists_feedback_charpoly_of_finrank_zero`: the zero-dimensional
  case of the sufficiency direction.
* `LinearMap.ne_zero_of_isControllable`,
  `LinearMap.isControllable_iff_bijective_kalmanControllabilityMap_single`,
  `LinearMap.linearIndependent_krylov_of_isControllable_single` and
  `LinearMap.eq_top_of_isControllable_of_map_le`: verified ingredients of the
  constructive sufficiency proof (Lemma 3.31 and Theorem 3.18 inputs).

The sufficiency direction — constructing `F` for a prescribed `p` — is the
remaining obligation; it is documented at the bottom of this file, together with
an explicit, determinant-free construction.

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Theorem 3.29 and its proof on PDF pages 72–74.
-/

@[expose] public section

open Polynomial
open Module

namespace LinearMap

variable {X U 𝕜 : Type*}

/-! ## Feedback invariance of the reachable subspace -/

section Feedback

variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]

/-- **State feedback does not change the reachable subspace.** For the pair
`(A + B.comp F, B)` the reachable subspace equals that of `(A, B)`. This is the
algebraic content of the fact that the reachable subspace contains `range B` and
is stable under both `A` and `A + B.comp F`.

Source: Trentelman–Stoorvogel–Hautus, Section 3.10, where feedback is used to
modify the dynamics without changing controllability. -/
theorem reachableSubspace_add_comp (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (F : X →ₗ[𝕜] U) :
    reachableSubspace (A + B.comp F) B = reachableSubspace A B := by
  apply le_antisymm
  · -- The reachable subspace of `(A + B F, B)` is contained in the reachable
    -- subspace of `(A, B)`: the latter contains `range B` and is stable under
    -- `A + B F`.
    apply reachableSubspace_le
    · exact range_le_reachableSubspace A B
    · intro y hy
      rw [Submodule.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [LinearMap.add_apply, LinearMap.comp_apply]
      exact Submodule.add_mem _
        (map_reachableSubspace_le A B ⟨x, hx, rfl⟩)
        (range_le_reachableSubspace A B (LinearMap.mem_range_self B (F x)))
  · -- The reachable subspace of `(A, B)` is contained in the reachable subspace
    -- of `(A + B F, B)`: the latter contains `range B` and is stable under
    -- `A = (A + B F) - B F`.
    apply reachableSubspace_le
    · exact range_le_reachableSubspace (A + B.comp F) B
    · intro y hy
      rw [Submodule.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have h1 : (A + B.comp F) x ∈ reachableSubspace (A + B.comp F) B :=
        map_reachableSubspace_le (A + B.comp F) B ⟨x, hx, rfl⟩
      have h2 : B (F x) ∈ reachableSubspace (A + B.comp F) B :=
        range_le_reachableSubspace (A + B.comp F) B (LinearMap.mem_range_self B (F x))
      have : A x = (A + B.comp F) x - B (F x) := by
        rw [LinearMap.add_apply, LinearMap.comp_apply]
        abel
      rw [this]
      exact Submodule.sub_mem _ h1 h2

/-- **Controllability is invariant under state feedback.** -/
theorem isControllable_add_comp (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (F : X →ₗ[𝕜] U) :
    IsControllable (A + B.comp F) B ↔ IsControllable A B := by
  rw [isControllable_iff, isControllable_iff, reachableSubspace_add_comp]

end Feedback

/-! ## Characteristic-polynomial obstruction for uncontrollable pairs

The converse direction of pole placement is proved by a quotient argument. If
`(A, B)` is not controllable then the reachable subspace `W` is a proper
`(A + B.comp F)`-invariant subspace containing `range B`. On the quotient
`X ⧸ W` every feedback induces the *same* endomorphism `Ā`, so the minimal
polynomial of `Ā` divides the characteristic polynomial of `A + B.comp F` for
every `F`. Choosing a monic target polynomial of degree `finrank ℝ X` that is
not divisible by `minpoly Ā` therefore produces a polynomial that no feedback
can realise.

This argument is purely real: the obstruction polynomial has real coefficients,
so non-real complex poles are handled automatically by the real-coefficient
target, exactly as required for a real system. -/

section Converse

variable [AddCommGroup X] [Module ℝ X]

/-- For an invariant subspace `W`, the `k`-th power of the induced quotient map
composed with the quotient projection is the projection of the `k`-th power. -/
theorem mapQ_pow_mkQ (A : X →ₗ[ℝ] X) (W : Submodule ℝ X)
    (hW : W ≤ W.comap A) (k : ℕ) :
    ((W.mapQ W A hW) ^ k).comp W.mkQ = W.mkQ.comp (A ^ k) := by
  induction k with
  | zero =>
      rw [pow_zero, Module.End.one_eq_id, LinearMap.id_comp, pow_zero,
        Module.End.one_eq_id, LinearMap.comp_id]
  | succ k ih =>
      rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc, Submodule.mapQ_mkQ,
        ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, ← Module.End.mul_eq_comp,
        ← pow_succ]

/-- The quotient map is compatible with polynomial evaluation: evaluating a
polynomial at the induced quotient map and then projecting equals projecting and
then evaluating at the original map. This is the algebraic step that transfers
the Cayley–Hamilton relation to the quotient. -/
theorem mapQ_aeval_mkQ (A : X →ₗ[ℝ] X) (W : Submodule ℝ X)
    (hW : W ≤ W.comap A) (p : ℝ[X]) :
    (aeval (W.mapQ W A hW) p).comp W.mkQ = W.mkQ.comp (aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      have h1 : (algebraMap ℝ (Module.End ℝ (X ⧸ W)) a * (W.mapQ W A hW) ^ n).comp
            W.mkQ = a • (((W.mapQ W A hW) ^ n).comp W.mkQ) := by
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, LinearMap.smul_comp]
      have h2 : W.mkQ.comp (algebraMap ℝ (Module.End ℝ X) a * A ^ n) =
            a • (W.mkQ.comp (A ^ n)) := by
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, LinearMap.comp_smul]
      rw [h1, h2, mapQ_pow_mkQ]

/-- **Minimal polynomial of a quotient divides the characteristic polynomial.**
For an invariant subspace `W`, the minimal polynomial of the induced quotient
map divides the characteristic polynomial of the original map, provided the
quotient is finite-dimensional. This uses Cayley–Hamilton on `X` together with
the compatibility `mapQ_aeval_mkQ`, and avoids any explicit canonical form. -/
theorem minpoly_mapQ_dvd_charpoly [FiniteDimensional ℝ X] (A : X →ₗ[ℝ] X)
    (W : Submodule ℝ X) (hW : W ≤ W.comap A) :
    minpoly ℝ (W.mapQ W A hW) ∣ A.charpoly := by
  refine minpoly.dvd ℝ (W.mapQ W A hW) ?_
  -- Push `aeval A A.charpoly = 0` through the quotient projection.
  have hzero : W.mkQ.comp (aeval A A.charpoly) = 0 := by
    rw [LinearMap.aeval_self_charpoly, LinearMap.comp_zero]
  have hcomp : (aeval (W.mapQ W A hW) A.charpoly).comp W.mkQ = 0 := by
    rw [mapQ_aeval_mkQ, hzero]
  -- The projection is surjective, so the quotient endomorphism itself vanishes.
  apply Submodule.quot_hom_ext
  intro x
  have hx := congrArg (fun f : X →ₗ[ℝ] X ⧸ W => f x) hcomp
  simpa using hx

end Converse

/-! ## The converse direction of pole placement -/

section MainConverse

variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup U] [Module ℝ U]

/-- **Necessity in the pole-placement theorem.** If every monic real polynomial
of degree `finrank ℝ X` is the characteristic polynomial of `A + B.comp F` for
some real feedback `F`, then `(A, B)` is controllable.

The proof is the real-coefficient quotient obstruction: if the reachable
subspace `W` is proper, then on the quotient `X ⧸ W` all feedbacks induce the
same endomorphism `Ā`. By `minpoly_mapQ_dvd_charpoly` the minimal polynomial
`r` of `Ā` divides every realisable characteristic polynomial, while the monic
target `X ^ (finrank ℝ X - natDegree r) * r + 1` has degree `finrank ℝ X` and
is not divisible by `r`. No complex feedback is used: both the target and the
obstruction have real coefficients.

Source: Trentelman–Stoorvogel–Hautus, proof of Theorem 3.29, PDF page 73. -/
theorem isControllable_of_forall_exists_feedback_charpoly
    [FiniteDimensional ℝ X] (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (h : ∀ p : ℝ[X], p.Monic → p.natDegree = Module.finrank ℝ X →
      ∃ F : X →ₗ[ℝ] U, (A + B.comp F).charpoly = p) :
    IsControllable A B := by
  by_contra hc
  set W : Submodule ℝ X := reachableSubspace A B with hWdef
  have hWtop : W ≠ ⊤ :=
    fun htop => hc (by rw [isControllable_iff]; exact htop)
  have hnt : Nontrivial (X ⧸ W) := (Submodule.Quotient.nontrivial_iff).mpr hWtop
  have hW : W ≤ W.comap A :=
    (Submodule.map_le_iff_le_comap).mp (map_reachableSubspace_le A B)
  set Abar : X ⧸ W →ₗ[ℝ] X ⧸ W := W.mapQ W A hW with hAbardef
  set r : ℝ[X] := minpoly ℝ Abar with hrdef
  have hAb_int : IsIntegral ℝ Abar := LinearMap.isIntegral Abar
  have hr_monic : r.Monic := by
    rw [hrdef]; exact minpoly.monic hAb_int
  have hr_ne_one : r ≠ 1 := by
    have := minpoly.ne_one (A := ℝ) (x := Abar)
    simpa [hrdef] using this
  -- Every feedback induces the same quotient map, so `r` divides every realisable charpoly.
  have hr_dvd : ∀ F : X →ₗ[ℝ] U, r ∣ (A + B.comp F).charpoly := by
    intro F
    have hF : W ≤ W.comap (A + B.comp F) := by
      intro x hx
      rw [Submodule.mem_comap, LinearMap.add_apply, LinearMap.comp_apply]
      exact Submodule.add_mem _ (map_reachableSubspace_le A B ⟨x, hx, rfl⟩)
        (range_le_reachableSubspace A B (LinearMap.mem_range_self B (F x)))
    have hq : W.mapQ W (A + B.comp F) hF = W.mapQ W A hW := by
      apply Submodule.quot_hom_ext
      intro x
      simp only [Submodule.mapQ_apply]
      change W.mkQ (A x + B (F x)) = W.mkQ (A x)
      rw [map_add]
      have hker : W.mkQ (B (F x)) = 0 := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact range_le_reachableSubspace A B (LinearMap.mem_range_self B (F x))
      rw [hker, add_zero]
    rw [hrdef, hAbardef, ← hq]
    exact minpoly_mapQ_dvd_charpoly (A + B.comp F) W hF
  -- The minimal polynomial of the quotient has degree at most `finrank ℝ X`.
  have hr_le : r.natDegree ≤ Module.finrank ℝ X := by
    have hdvd : r ∣ Abar.charpoly := by
      rw [hrdef]; exact LinearMap.minpoly_dvd_charpoly Abar
    have hle : r.natDegree ≤ Abar.charpoly.natDegree :=
      hr_monic.natDegree_le_of_dvd (LinearMap.charpoly_monic Abar).ne_zero hdvd
    rw [LinearMap.charpoly_natDegree] at hle
    have hfin : Module.finrank ℝ (X ⧸ W) ≤ Module.finrank ℝ X := by
      have hsum := Submodule.finrank_quotient_add_finrank W
      omega
    exact le_trans hle hfin
  have hr_pos : 0 < r.natDegree := minpoly.natDegree_pos hAb_int
  -- The obstruction polynomial.
  set k : ℕ := Module.finrank ℝ X - r.natDegree with hkdef
  set p : ℝ[X] := Polynomial.X ^ k * r + 1 with hpdef
  have hXk_nat : (Polynomial.X ^ k * r).natDegree = k + r.natDegree := by
    rw [Polynomial.natDegree_X_pow_mul k hr_monic.ne_zero]
    omega
  have hdeg : degree (1 : ℝ[X]) < degree (Polynomial.X ^ k * r) := by
    apply Polynomial.degree_lt_degree
    rw [hXk_nat]
    simp only [Polynomial.natDegree_one]
    omega
  have hp_monic : p.Monic := by
    rw [hpdef]
    have hX : (Polynomial.X : ℝ[X]).Monic := by
      simpa using Polynomial.monic_X_add_C (0 : ℝ)
    exact ((hX.pow k).mul hr_monic).add_of_left hdeg
  have hp_natDegree : p.natDegree = Module.finrank ℝ X := by
    rw [hpdef, Polynomial.natDegree_add_eq_left_of_degree_lt hdeg, hXk_nat, hkdef]
    omega
  obtain ⟨F, hFchar⟩ := h p hp_monic hp_natDegree
  have hdiv : r ∣ p := by
    rw [← hFchar]; exact hr_dvd F
  have hr_dvd_one : r ∣ 1 := by
    have h2 : r ∣ Polynomial.X ^ k * r := dvd_mul_left r (Polynomial.X ^ k)
    have h1 : r ∣ p - Polynomial.X ^ k * r := dvd_sub hdiv h2
    have : p - Polynomial.X ^ k * r = 1 := by rw [hpdef]; ring
    rwa [this] at h1
  exact hr_ne_one (hr_monic.eq_one_of_isUnit (isUnit_iff_dvd_one.mpr hr_dvd_one))

end MainConverse

/-! ## Companion-basis characteristic polynomial

A linear map whose matrix in a basis is the companion matrix of a monic polynomial
`p` has characteristic polynomial `p`. This is the algebraic computation at the
heart of the SISO step of pole placement. We prove it by identifying the matrix
with the matrix of multiplication by the root in `AdjoinRoot p`, whose
characteristic polynomial is `p` by `charpoly_leftMulMatrix`.

This avoids any direct determinant expansion of the companion matrix. -/

section Companion

variable [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]

/-- **Characteristic polynomial from a companion basis.** If `T` acts on the basis
`v` by the companion relations of a monic `p` (shift for all but the last index,
and the reversed-coefficient combination at the last index), then `T.charpoly = p`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.29 (SISO step). -/
theorem charpoly_eq_of_companion (p : ℝ[X]) (hp : p.Monic)
    (T : X →ₗ[ℝ] X) (v : Basis (Fin p.natDegree) ℝ X)
    (hrel : ∀ i : Fin p.natDegree,
      T (v i) = if h : (i : ℕ) + 1 < p.natDegree then v ⟨(i : ℕ) + 1, h⟩
        else -∑ j : Fin p.natDegree, p.coeff (j : ℕ) • v j) :
    T.charpoly = p := by
  classical
  let h := AdjoinRoot.powerBasis hp.ne_zero
  have hmin : h.minpolyGen = p :=
    (h.minpolyGen_eq).trans (AdjoinRoot.minpoly_powerBasis_gen_of_monic hp)
  have hmat : LinearMap.toMatrix v v T = Algebra.leftMulMatrix h.basis h.gen := by
    have hrepr : ∀ (c : Fin p.natDegree → ℝ) (i : Fin p.natDegree),
        (v.repr (∑ b, c b • v b)) i = c i := by
      intro c i
      simp only [map_sum, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul]
      simp [Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
    rw [PowerBasis.leftMulMatrix]
    ext i j
    rw [LinearMap.toMatrix_apply]
    show (v.repr (T (v j))) i =
      (if (j : ℕ) + 1 = h.dim then -h.minpolyGen.coeff (i : ℕ)
        else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0)
    rw [hmin]
    have hdim : h.dim = p.natDegree := rfl
    by_cases hj : (j : ℕ) + 1 = h.dim
    · rw [if_pos hj]
      have hnj : ¬ (j : ℕ) + 1 < p.natDegree := by omega
      rw [hrel j, dif_neg hnj, map_neg, Finsupp.neg_apply, hrepr]
    · rw [if_neg hj]
      by_cases hij : (i : ℕ) = (j : ℕ) + 1
      · rw [if_pos hij]
        have hlt : (j : ℕ) + 1 < p.natDegree := by
          have : (j : ℕ) + 1 < h.dim := by rw [← hij]; exact i.2
          omega
        rw [hrel j, dif_pos hlt, Basis.repr_self_apply, if_pos]
        exact Fin.ext hij.symm
      · rw [if_neg hij]
        by_cases hlt : (j : ℕ) + 1 < p.natDegree
        · rw [hrel j, dif_pos hlt, Basis.repr_self_apply, if_neg]
          exact fun h => hij (Fin.ext_iff.mp h).symm
        · exfalso; omega
  have h1 : T.charpoly = (Algebra.leftMulMatrix h.basis h.gen).charpoly := by
    rw [← hmat]
    exact (LinearMap.charpoly_toMatrix (f := T) v).symm
  rw [h1, charpoly_leftMulMatrix h, (h.minpolyGen_eq).symm.trans hmin]

end Companion

/-! ## Zero-dimensional sufficiency

The pole-placement construction is trivial when the state space is zero-dimensional:
the only monic polynomial of degree zero is `1`, and the zero feedback works. This
case must be isolated before the source's `B ≠ 0` argument in Lemma 3.31. -/

section ZeroDim

variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup U] [Module ℝ U]

/-- **Pole placement in dimension zero.** If `finrank ℝ X = 0`, every monic target
polynomial of degree `finrank ℝ X` (necessarily `1`) is realised by `F = 0`. -/
theorem exists_feedback_charpoly_of_finrank_zero [FiniteDimensional ℝ X]
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (hzero : Module.finrank ℝ X = 0) (p : ℝ[X]) (hp : p.Monic)
    (hpdeg : p.natDegree = Module.finrank ℝ X) :
    ∃ F : X →ₗ[ℝ] U, (A + B.comp F).charpoly = p := by
  haveI : Subsingleton X := Module.finrank_zero_iff.mp hzero
  have hp1 : p = 1 := by
    have h0 : p.natDegree = 0 := by rw [hpdeg, hzero]
    exact Polynomial.eq_one_of_monic_natDegree_zero hp h0
  refine ⟨0, ?_⟩
  rw [hp1, LinearMap.comp_zero, add_zero]
  haveI : IsEmpty (Module.Free.ChooseBasisIndex ℝ X) := by
    rw [← Fintype.card_eq_zero_iff, ← Module.finrank_eq_card_chooseBasisIndex, hzero]
  rw [LinearMap.charpoly_def]
  exact Matrix.charpoly_isEmpty

end ZeroDim

/-! ## Towards sufficiency: nonzero input and the single-input Krylov basis

The sufficiency proof of Theorem 3.29 starts from a controllable pair. We record
here two elementary but reusable facts used by the constructive part.

* `LinearMap.ne_zero_of_isControllable`: a controllable pair on a positive-
  dimensional state space has `B ≠ 0` (the source's first step in Lemma 3.31).
* `LinearMap.isControllable_iff_bijective_kalmanControllabilityMap_single` and
  `LinearMap.linearIndependent_krylov_of_isControllable_single`: for a single
  input `b : ℝ →ₗ X`, controllability is exactly bijectivity of the Kalman
  controllability map, and the Krylov vectors `b, A b, …, A^{n-1} b` are linearly
  independent. This is the basis underlying Theorem 3.18 (control canonical
  form). -/

section Krylov

variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup U] [Module ℝ U]

/-- A controllable pair on a positive-dimensional state space has a nonzero input
map. This is the first case distinction in Lemma 3.31 of
Trentelman–Stoorvogel–Hautus: if `B = 0` the reachable subspace is `⊥`. -/
theorem ne_zero_of_isControllable
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (h : IsControllable A B)
    (hn : 0 < Module.finrank ℝ X) : B ≠ 0 := by
  intro hB
  have hbot : reachableSubspace A B = ⊥ := by
    rw [reachableSubspace, hB]
    simp
  rw [isControllable_iff] at h
  have hbt : (⊥ : Submodule ℝ X) = ⊤ := by rw [← hbot]; exact h
  have h0 : (0 : ℕ) = Module.finrank ℝ X := by
    have := congrArg (fun (M : Submodule ℝ X) => Module.finrank ℝ M) hbt
    simpa using this
  omega

/-- **Single-input Kalman criterion.** For an input map `b : ℝ →ₗ X` the pair
`(A, b)` is controllable exactly when the Kalman controllability map
`(Fin n → ℝ) → X` is bijective. Surjectivity is controllability; injectivity
follows because the domain and codomain both have dimension `n`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.18 and Section 3.3. -/
theorem isControllable_iff_bijective_kalmanControllabilityMap_single
    [FiniteDimensional ℝ X] (A : X →ₗ[ℝ] X) (b : ℝ →ₗ[ℝ] X) :
    IsControllable A b ↔
      Function.Bijective (kalmanControllabilityMap A b (Module.finrank ℝ X)) := by
  rw [isControllable_iff_surjective_kalmanControllabilityMap]
  refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Module.finrank_fin_fun])).mpr h

/-- **The Krylov vectors of a controllable single-input pair are linearly
independent.** For a controllable pair `(A, b)` with `b : ℝ →ₗ X`, the family
`i ↦ A ^ i (b 1)`, `i < finrank ℝ X`, is linearly independent, hence a basis of
`X`. This constructs the basis underlying the control canonical form of
Theorem 3.18 from the bijective Kalman map.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.18. -/
theorem linearIndependent_krylov_of_isControllable_single
    [FiniteDimensional ℝ X] (A : X →ₗ[ℝ] X) (b : ℝ →ₗ[ℝ] X)
    (h : IsControllable A b) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ X) => (A ^ (i : ℕ)) (b 1)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hbid := (isControllable_iff_bijective_kalmanControllabilityMap_single A b).mp h
  have hb : ∀ k : Fin (Module.finrank ℝ X), b (c k) = c k • b 1 :=
    fun k => by rw [← map_smul]; simp
  have hmap : kalmanControllabilityMap A b (Module.finrank ℝ X) c = 0 := by
    rw [kalmanControllabilityMap_apply]
    trans ∑ k : Fin (Module.finrank ℝ X), c k • (A ^ (k : ℕ)) (b 1)
    · exact Finset.sum_congr rfl fun k _ => by rw [hb k, map_smul]
    · exact hc
  have hc0 : c = 0 := hbid.1 (by rw [hmap, map_zero])
  intro i
  rw [hc0]
  rfl

/-- **A proper `A`-invariant subspace containing `range B` cannot exist for a
controllable pair.** This is the extremal property of the reachable subspace
(`LinearMap.reachableSubspace_le`) in the form used by the controlled-chain
extension step of Lemma 3.31: if `L` is `A`-invariant and contains the image of
`B`, then `L = ⊤`.

Source: Trentelman–Stoorvogel–Hautus, Corollary 3.3 and the proof of Lemma 3.31. -/
theorem eq_top_of_isControllable_of_map_le (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (h : IsControllable A B) {L : Submodule ℝ X}
    (hA : Submodule.map A L ≤ L) (hB : range B ≤ L) : L = ⊤ := by
  have hle : reachableSubspace A B ≤ L := reachableSubspace_le A B hB hA
  rw [isControllable_iff] at h
  rw [h] at hle
  exact top_le_iff.mp hle

end Krylov

/-! ## Polynomial auxiliary for the determinant-free SISO construction

The sufficiency direction constructs the feedback through a reversed-polynomial
auxiliary. Let `p` be the monic target of degree `n` and `q = A.charpoly`. Write
`p^*` and `q^*` for the coefficient reversals (Mathlib's `Polynomial.reverse`),
set `ptilde = p^* - 1` (so `ptilde` is divisible by `X`) and

`D = q^* * ∑_{k<n} (-ptilde)^k`.

Because `p^* = 1 + ptilde` and `(1 + x) ∑_{k<n} (-x)^k = 1 - (-x)^n`, the
polynomial `p^* * D - q^*` is divisible by `X^n`. Hence the coefficients of
`p^* * D` below degree `n` are exactly those of `q^*`; this is the only
polynomial identity needed for the triangular recurrence of the construction
(`poleD_congr`). The auxiliary `D` is used through its low coefficients
`D.coeff k`, `k < n`, which are the `c_k` of the documented recurrence. -/

section PolynomialAux

/-- The finite geometric identity `(1 + x) ∑_{k<n} (-x)^k = 1 - (-x)^n`, valid
in any commutative ring. -/
theorem one_add_mul_sum_neg_pow (x : ℝ[X]) (n : ℕ) :
    (1 + x) * (∑ k ∈ Finset.range n, (-x) ^ k) = 1 - (-x) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

/-- The reversed auxiliary polynomial `D = q^* ∑_{k<n} (-(p^* - 1))^k` used by
the constructive SISO pole-placement proof. Its low coefficients `D.coeff k`,
`k < n`, play the role of the recurrence constants `c_k` of the source proof. -/
noncomputable def poleD (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  q.reverse * ∑ k ∈ Finset.range n, (-(p.reverse - 1)) ^ k

/-- Constant coefficient of a power of a polynomial. -/
theorem coeff_zero_pow (x : ℝ[X]) (k : ℕ) : (x ^ k).coeff 0 = (x.coeff 0) ^ k := by
  rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]

/-- The auxiliary polynomial has constant coefficient `1` when `p` and `q` are
monic and `n > 0`. This is the fact that the leading coefficient `D.coeff 0` of
each triangular polynomial `G_i` is `1`, so that the `G_i` are monic. -/
theorem coeff_zero_poleD {n : ℕ} (hn : 0 < n) {p q : ℝ[X]} (hp : p.Monic)
    (hq : q.Monic) : (poleD n p q).coeff 0 = 1 := by
  have hpt : (p.reverse - 1).coeff 0 = 0 := by
    rw [coeff_sub, coeff_one, coeff_zero_reverse, hp.leadingCoeff]
    simp
  have hS : (∑ k ∈ Finset.range n, (-(p.reverse - 1)) ^ k).coeff 0 = 1 := by
    rw [← lcoeff_apply, map_sum]
    simp only [lcoeff_apply]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk0
      rw [coeff_zero_pow, coeff_neg, hpt, neg_zero, zero_pow hk0]
    · intro h0
      exact absurd (Finset.mem_range.mpr hn) h0
  rw [poleD, coeff_mul, Finset.sum_eq_single (0, 0)]
  · simp only [coeff_zero_reverse, hq.leadingCoeff, hS, mul_one]
  · intro x hx hx0
    have hx' : x = (0, 0) := by
      rw [Finset.mem_antidiagonal] at hx
      ext <;> omega
    exact absurd hx' hx0
  · intro h0
    exact absurd (Finset.mem_antidiagonal.mpr (by norm_num)) h0

/-- **The reversed congruence.** If `p` and `q` are monic of degree `n` and
`n > 0`, then `p^* * D` and `q^*` agree in every degree below `n`. This is the
polynomial identity that drives the forward recurrence `c_s` of the
construction: comparing the degree-`(n-m)` coefficient turns the recurrence into
the equality `H.coeff m = q.coeff m` for `1 ≤ m ≤ n-1`. -/
theorem poleD_congr {n : ℕ} {p q : ℝ[X]} (hp : p.Monic) :
    ∀ t < n, (p.reverse * poleD n p q).coeff t = q.reverse.coeff t := by
  intro t ht
  set ptilde : ℝ[X] := p.reverse - 1 with hpt
  set S : ℝ[X] := ∑ k ∈ Finset.range n, (-ptilde) ^ k with hSdef
  have hgeom : p.reverse * S = 1 - (-ptilde) ^ n := by
    have h1 : p.reverse = 1 + ptilde := by rw [hpt]; ring
    rw [h1, one_add_mul_sum_neg_pow]
  have hpt0 : ptilde.coeff 0 = 0 := by
    rw [hpt, coeff_sub, coeff_one, coeff_zero_reverse, hp.leadingCoeff]
    simp
  have hX : X ∣ ptilde := X_dvd_iff.mpr hpt0
  have hXnp : X ^ n ∣ ptilde ^ n := pow_dvd_pow_of_dvd hX n
  have hXnm : X ^ n ∣ (-ptilde) ^ n := by
    rw [neg_pow]
    exact dvd_mul_of_dvd_right hXnp ((-1 : ℝ[X]) ^ n)
  have hD : poleD n p q = q.reverse * S := by rw [poleD, hSdef]
  have hmain : p.reverse * poleD n p q = q.reverse * (p.reverse * S) := by
    rw [hD]; ring
  have hdiff : p.reverse * poleD n p q - q.reverse = -(q.reverse * (-ptilde) ^ n) := by
    rw [hmain, hgeom]; ring
  have hdiv : X ^ n ∣ p.reverse * poleD n p q - q.reverse := by
    rw [hdiff]
    exact dvd_neg.mpr (dvd_mul_of_dvd_right hXnm q.reverse)
  have h := (X_pow_dvd_iff.mp hdiv) t ht
  rw [coeff_sub, sub_eq_zero] at h
  exact h

/-- The `i`-th triangular polynomial `G_i` of the SISO construction. It is the
reversal of the truncation of the auxiliary `D` to degree `i`, i.e.
`G_i = ∑_{k≤i} (D.coeff k) X^{i-k}`. It is monic of degree `i`, and the low
coefficients `D.coeff k` are exactly the recurrence constants. -/
noncomputable def poleG (n : ℕ) (p q : ℝ[X]) (i : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (i+1), C ((poleD n p q).coeff k) * Polynomial.X ^ (i - k)

/-- The defining recurrence of the triangular polynomials:
`G_{i+1} = X G_i + c_i` with `c_i = D.coeff (i+1)`. This is the relation that
makes `y_i = G_i(A) (b 1)` a controlled chain for the feedback to be built. -/
theorem poleG_succ (n : ℕ) (p q : ℝ[X]) (i : ℕ) :
    poleG n p q (i+1) = Polynomial.X * poleG n p q i + C ((poleD n p q).coeff (i+1)) := by
  rw [poleG, poleG, Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show i + 1 - k = (i - k) + 1 by omega, pow_succ]
    ring
  · simp

/-- Coefficients of the triangular polynomials. For `m ≤ i` the coefficient of
`X^m` is `D.coeff (i - m)`, and for `m > i` it vanishes. In particular
`G_i.coeff i = D.coeff 0 = 1` and `G_i` has degree `i`. -/
theorem poleG_coeff (n : ℕ) (p q : ℝ[X]) (i m : ℕ) :
    (poleG n p q i).coeff m =
      if m ≤ i then (poleD n p q).coeff (i - m) else 0 := by
  rw [poleG, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, coeff_C_mul, coeff_X_pow]
  by_cases hm : m ≤ i
  · rw [if_pos hm]
    rw [Finset.sum_eq_single (i - m)]
    · rw [if_pos (Nat.sub_sub_self hm).symm, mul_one]
    · intro k hk hk0
      have hne : m ≠ i - k := by
        intro h
        apply hk0
        have hk' : k ≤ i := by rw [Finset.mem_range] at hk; omega
        omega
      rw [if_neg hne, mul_zero]
    · intro h0
      exact absurd (Finset.mem_range.mpr (by omega)) h0
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    have hne : m ≠ i - k := by omega
    rw [if_neg hne, mul_zero]

/-- The polynomial `H = X G_{n-1} + ∑_{j<n} p_j G_j` whose companion form is
realised by the constructed feedback. Its coefficients in degrees `1, …, n`
agree with those of `q = A.charpoly`, so `H - q` is a constant (and `H` is monic
of degree `n`). -/
noncomputable def poleH (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  Polynomial.X * poleG n p q (n-1) +
    ∑ j ∈ Finset.range n, C (p.coeff j) * poleG n p q j

/-- Coefficient of `X * G_{n-1}` in positive degree. -/
theorem coeff_X_mul_poleG (n : ℕ) (p q : ℝ[X]) {m : ℕ} (hm : 1 ≤ m) :
    (Polynomial.X * poleG n p q (n-1)).coeff m = (poleG n p q (n-1)).coeff (m-1) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => Polynomial.X.coeff a * (poleG n p q (n-1)).coeff b) m]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro k _ hk1
    rw [coeff_X, if_neg (Ne.symm hk1), zero_mul]
  · intro h1
    exact absurd (Finset.mem_range.mpr (by omega)) h1

/-- Coefficient of the `∑ p_j G_j` part of `H`. -/
theorem coeff_sum_C_poleG (n : ℕ) (p q : ℝ[X]) (m : ℕ) :
    (∑ j ∈ Finset.range n, C (p.coeff j) * poleG n p q j).coeff m =
      ∑ j ∈ Finset.range n,
        p.coeff j * (if m ≤ j then (poleD n p q).coeff (j - m) else 0) := by
  rw [← lcoeff_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [lcoeff_apply, coeff_C_mul, poleG_coeff]

/-- **The key coefficient identity of the SISO construction.** For `1 ≤ m ≤ n`,
the coefficient of `X^m` in `H` equals the coefficient of the reversed-product
`p^* D` in degree `n - m`. Since `p^* D` agrees with `q^*` below degree `n`
(`poleD_congr`), this gives `H.coeff m = q.coeff m` in positive degrees. -/
theorem poleH_coeff_eq (n : ℕ) (p q : ℝ[X]) (hp : p.Monic) (hpn : p.natDegree = n)
    {m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    (poleH n p q).coeff m = (p.reverse * poleD n p q).coeff (n - m) := by
  rw [poleH, coeff_add, coeff_X_mul_poleG n p q hm1, coeff_sum_C_poleG]
  have hG : (poleG n p q (n-1)).coeff (m-1) = (poleD n p q).coeff (n-m) := by
    rw [poleG_coeff, if_pos (by omega : m - 1 ≤ n - 1)]
    congr 1
    omega
  rw [hG]
  have hL : ∑ j ∈ Finset.range n,
        p.coeff j * (if m ≤ j then (poleD n p q).coeff (j - m) else 0)
      = ∑ i ∈ Finset.range (n - m), p.coeff (m + i) * (poleD n p q).coeff i := by
    nth_rewrite 1 [show n = m + (n - m) by omega]
    rw [Finset.sum_range_add]
    have hzero : ∑ j ∈ Finset.range m,
        p.coeff j * (if m ≤ j then (poleD n p q).coeff (j - m) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      rw [if_neg (by omega), mul_zero]
    rw [hzero, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_pos (by omega : m ≤ m + i)]
    rw [show (m + i) - m = i by omega]
  rw [hL]
  have hR : (p.reverse * poleD n p q).coeff (n - m)
      = ∑ i ∈ Finset.range (n - m + 1), p.coeff (m + i) * (poleD n p q).coeff i := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => p.reverse.coeff a * (poleD n p q).coeff b) (n - m)]
    rw [← Finset.sum_range_reflect
      (fun k => p.reverse.coeff k * (poleD n p q).coeff ((n - m) - k)) (n - m + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show n - m + 1 - 1 - k = n - m - k by omega]
    rw [coeff_reverse, hpn, revAt_le (by omega : n - m - k ≤ n)]
    rw [show n - (n - m - k) = m + k by omega,
      show (n - m) - (n - m - k) = k by omega]
  rw [hR, Finset.sum_range_succ]
  rw [show p.coeff (m + (n - m)) = 1 by
    rw [show m + (n - m) = n by omega, ← hpn]
    exact hp.coeff_natDegree]
  ring

/-- `H` vanishes above degree `n` when `n > 0` (each `G_j` has degree `j ≤ n-1`
and `X G_{n-1}` has degree `n`). -/
theorem poleH_coeff_gt (n : ℕ) (p q : ℝ[X]) {m : ℕ} (hn : 0 < n) (hm : n < m) :
    (poleH n p q).coeff m = 0 := by
  rw [poleH, coeff_add, coeff_X_mul_poleG n p q (by omega : 1 ≤ m), coeff_sum_C_poleG]
  have hG : (poleG n p q (n-1)).coeff (m-1) = 0 := by
    rw [poleG_coeff, if_neg (by omega : ¬ (m - 1 ≤ n - 1))]
  rw [hG, zero_add]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  rw [if_neg (not_le.mpr (by omega : j < m)), mul_zero]

/-- `H` differs from `q = A.charpoly` by a constant. This is the polynomial
content of the final companion relation: choosing the last feedback value as the
negated constant makes `H` equal to `q`, whose evaluation at `b` vanishes by
Cayley–Hamilton. -/
theorem poleH_eq (n : ℕ) (p q : ℝ[X]) (hp : p.Monic) (hpn : p.natDegree = n)
    (hqn : q.natDegree = n) (hn : 0 < n) :
    poleH n p q = q + C ((poleH n p q).coeff 0 - q.coeff 0) := by
  ext m
  by_cases hm : m = 0
  · subst hm
    rw [coeff_add, coeff_C, if_pos rfl]
    ring
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    rw [coeff_add, coeff_C, if_neg hm, add_zero]
    by_cases hmn : m ≤ n
    · have h1 : (poleH n p q).coeff m = (p.reverse * poleD n p q).coeff (n-m) :=
        poleH_coeff_eq n p q hp hpn hm1 hmn
      have h2 : (p.reverse * poleD n p q).coeff (n-m) = q.reverse.coeff (n-m) :=
        poleD_congr hp (n-m) (by omega)
      have h3 : q.reverse.coeff (n-m) = q.coeff m := by
        rw [coeff_reverse, hqn, revAt_le (by omega : n - m ≤ n)]
        congr 1
        omega
      rw [h1, h2, h3]
    · have h1 : (poleH n p q).coeff m = 0 := poleH_coeff_gt n p q hn (by omega)
      have h2 : q.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by rw [hqn]; omega)
      rw [h1, h2]

/-- Each triangular polynomial `G_i` has degree at most `i`. -/
theorem poleG_natDegree_le (n : ℕ) (p q : ℝ[X]) (i : ℕ) :
    (poleG n p q i).natDegree ≤ i := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [poleG_coeff, if_neg (by omega : ¬ (N ≤ i))]

/-- **The triangular family `G_i(A) (b 1)` is linearly independent.** This is
the key structural input for the companion basis: since each `G_i` is monic of
degree `i`, the vectors `G_i(A) (b 1)` are triangular over the Krylov basis
`b, A b, …, A^{n-1} b`, whose independence is
`linearIndependent_krylov_of_isControllable_single`. -/
theorem linearIndependent_poleG [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
    (A : X →ₗ[ℝ] X) (b : ℝ →ₗ[ℝ] X)
    (h : IsControllable A b) (n : ℕ) (hnpos : 0 < n) (hnrank : n = Module.finrank ℝ X)
    (p q : ℝ[X]) (hD0 : (poleD n p q).coeff 0 = 1) :
    LinearIndependent ℝ (fun i : Fin n => aeval A (poleG n p q i) (b 1)) := by
  subst hnrank
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  obtain ⟨i1, hi1⟩ := hne
  let s : Finset (Fin (Module.finrank ℝ X)) := Finset.univ.filter (fun i => c i ≠ 0)
  have hsne : s.Nonempty := ⟨i1, by simp [s, hi1]⟩
  let i0 : Fin (Module.finrank ℝ X) := s.max' hsne
  have hi0 : c i0 ≠ 0 := by
    have := Finset.max'_mem s hsne
    simpa [s] using this
  have hmax : ∀ j : Fin (Module.finrank ℝ X), c j ≠ 0 → j ≤ i0 := by
    intro j hj
    exact Finset.le_max' s j (by simp [s, hj])
  let R : ℝ[X] := ∑ i : Fin (Module.finrank ℝ X), C (c i) * poleG (Module.finrank ℝ X) p q i
  have hRval : aeval A R (b 1) = 0 := by
    have h1 : aeval A R =
        ∑ i : Fin (Module.finrank ℝ X), c i • aeval A (poleG (Module.finrank ℝ X) p q i) := by
      dsimp only [R]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, aeval_C]
      simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc]
    rw [h1]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    exact hc
  have hRdeg : R.natDegree < Module.finrank ℝ X := by
    have hle : R.natDegree ≤ Module.finrank ℝ X - 1 := by
      dsimp only [R]
      refine le_trans (natDegree_sum_le _ _) ?_
      rw [Finset.fold_max_le]
      refine ⟨by omega, ?_⟩
      intro i _
      exact le_trans (natDegree_C_mul_le _ _)
        (le_trans (poleG_natDegree_le (Module.finrank ℝ X) p q i) (by omega))
    omega
  have hcoeff : R.coeff i0 = 0 := by
    have hk := linearIndependent_krylov_of_isControllable_single A b h
    rw [Fintype.linearIndependent_iff] at hk
    apply hk (fun k : Fin (Module.finrank ℝ X) => R.coeff k)
    rw [aeval_eq_sum_range' hRdeg A, LinearMap.sum_apply] at hRval
    simp only [LinearMap.smul_apply] at hRval
    rw [Fin.sum_univ_eq_sum_range (fun k => R.coeff k • (A ^ k) (b 1))]
    exact hRval
  have hRcoeff : R.coeff i0 = c i0 := by
    dsimp only [R]
    rw [← lcoeff_apply, map_sum]
    simp only [lcoeff_apply, coeff_C_mul]
    rw [Finset.sum_eq_single i0]
    · rw [poleG_coeff, if_pos le_rfl, Nat.sub_self, hD0, mul_one]
    · intro j _ hj
      by_cases hlt : i0 < j
      · have hcj : c j = 0 := by
          by_contra hcj
          exact absurd (hmax j hcj) (not_le.mpr hlt)
        rw [hcj, zero_mul]
      · have hji : j < i0 := by omega
        have hif : ¬ (↑i0 ≤ ↑j) := by omega
        have hzero : (poleG (Module.finrank ℝ X) p q j).coeff i0 = 0 := by
          rw [poleG_coeff]
          exact if_neg hif
        rw [hzero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i0) h
  rw [hRcoeff] at hcoeff
  exact hi0 hcoeff

end PolynomialAux

/-! ## SISO sufficiency: constructive pole placement

The constructive direction of Trentelman–Stoorvogel–Hautus Theorem 3.29 for a
single input map `b : ℝ →ₗ[ℝ] X` and a controllable pair `(A, b)`: every monic
real polynomial `p` of degree `finrank ℝ X` is the characteristic polynomial of
`A + b.comp f` for a suitable real feedback `f : X →ₗ[ℝ] ℝ`.

The proof builds the triangular Krylov family `G_i(A) (b 1)` from the
reversed-polynomial auxiliary `poleD`, uses it as a basis, chooses the feedback
on that basis from the recurrence constants and the constant shift `κ` of
`poleH` versus `A.charpoly`, and concludes with the determinant-free companion
characteristic-polynomial computation `charpoly_eq_of_companion`. No
determinant expansion, complexification, or dimension-zero edge case is left
implicit.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.29 and its proof, PDF
pages 73–74 / printed 59–60. -/

section Sufficiency

theorem exists_feedback_charpoly_single [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
    (A : X →ₗ[ℝ] X) (b : ℝ →ₗ[ℝ] X)
    (h : IsControllable A b) (p : ℝ[X]) (hp : p.Monic)
    (hpdeg : p.natDegree = Module.finrank ℝ X) :
    ∃ f : X →ₗ[ℝ] ℝ, (A + b.comp f).charpoly = p := by
  classical
  by_cases hzero : Module.finrank ℝ X = 0
  · exact exists_feedback_charpoly_of_finrank_zero A b hzero p hp hpdeg
  · have hnpos : 0 < Module.finrank ℝ X := Nat.pos_of_ne_zero hzero
    set n : ℕ := p.natDegree with hn
    have hnrank : n = Module.finrank ℝ X := by rw [hn]; exact hpdeg
    have hpn : p.natDegree = n := hn.symm
    have hnpos' : 0 < n := by rw [hnrank]; exact hnpos
    set q : ℝ[X] := A.charpoly with hq
    have hqmonic : q.Monic := by rw [hq]; exact A.charpoly_monic
    have hqdeg : q.natDegree = n := by
      rw [hq, A.charpoly_natDegree, ← hnrank]
    have hD0 : (poleD n p q).coeff 0 = 1 := coeff_zero_poleD hnpos' hp hqmonic
    have hLI : LinearIndependent ℝ (fun i : Fin n => aeval A (poleG n p q i) (b 1)) :=
      linearIndependent_poleG A b h n hnpos' hnrank p q hD0
    haveI : Nonempty (Fin n) := ⟨⟨0, hnpos'⟩⟩
    let v : Basis (Fin n) ℝ X :=
      basisOfLinearIndependentOfCardEqFinrank hLI (by rw [Fintype.card_fin]; exact hnrank)
    have hv : ∀ i : Fin n, v i = aeval A (poleG n p q i) (b 1) := by
      intro i
      change (basisOfLinearIndependentOfCardEqFinrank hLI _) i = _
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    let κ : ℝ := (poleH n p q).coeff 0 - q.coeff 0
    have hκ : poleH n p q = q + C κ := by
      rw [poleH_eq n p q hp hpn hqdeg hnpos']
    let f : X →ₗ[ℝ] ℝ := v.constr ℝ (fun i : Fin n =>
      if (i : ℕ) + 1 < n then (poleD n p q).coeff ((i : ℕ) + 1) else -κ)
    have hC : ∀ (c : ℝ) (x : X), (aeval A (C c)) x = c • x := by
      intro c x
      rw [aeval_C]
      simp [Algebra.algebraMap_eq_smul_one]
    have hb : ∀ r : ℝ, b r = r • (b 1) := fun r => by
      simpa using (b.map_smul r (1 : ℝ))
    have hlin : ∀ (i : Fin n) (c : ℝ),
        A (v i) + c • (b 1) =
          aeval A (Polynomial.X * poleG n p q (i : ℕ) + C c) (b 1) := by
      intro i c
      rw [map_add, LinearMap.add_apply, hC, map_mul, aeval_X, Module.End.mul_eq_comp,
        LinearMap.comp_apply, ← hv i]
    have hsum : (∑ j : Fin n, C (p.coeff (j : ℕ)) * poleG n p q (j : ℕ))
        = ∑ j ∈ Finset.range n, C (p.coeff j) * poleG n p q j := by
      rw [Fin.sum_univ_eq_sum_range (fun j => C (p.coeff j) * poleG n p q j)]
    have hsum_v : aeval A (∑ j : Fin n, C (p.coeff (j : ℕ)) * poleG n p q (j : ℕ)) (b 1)
        = ∑ j : Fin n, p.coeff (j : ℕ) • v j := by
      rw [map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul, aeval_C, Module.End.mul_eq_comp, LinearMap.comp_apply, ← hv j]
      simp [Algebra.algebraMap_eq_smul_one]
    have hrel : ∀ i : Fin n, (A + b.comp f) (v i) =
        if h : (i : ℕ) + 1 < n then v ⟨(i : ℕ) + 1, h⟩
          else -∑ j : Fin n, p.coeff (j : ℕ) • v j := by
      intro i
      rw [LinearMap.add_apply, LinearMap.comp_apply]
      have hfv : f (v i) =
          if (i : ℕ) + 1 < n then (poleD n p q).coeff ((i : ℕ) + 1) else -κ := by
        simp only [f, Basis.constr_basis]
      rw [hfv, hb]
      split_ifs with hlt
      · rw [hlin]
        rw [← poleG_succ n p q (i : ℕ)]
        rw [← hv ⟨(i : ℕ) + 1, hlt⟩]
      · have hi : (i : ℕ) = n - 1 := by omega
        rw [hlin]
        have hEq : Polynomial.X * poleG n p q (i : ℕ) + C (-κ)
            = q - ∑ j : Fin n, C (p.coeff (j : ℕ)) * poleG n p q (j : ℕ) := by
          have hbase : Polynomial.X * poleG n p q (i : ℕ)
              = (Polynomial.X * poleG n p q (n - 1) +
                    ∑ j : Fin n, C (p.coeff (j : ℕ)) * poleG n p q (j : ℕ))
                - ∑ j : Fin n, C (p.coeff (j : ℕ)) * poleG n p q (j : ℕ) := by
            rw [hi]
            abel
          rw [hbase]
          have hH : Polynomial.X * poleG n p q (n - 1) +
                ∑ j : Fin n, C (p.coeff (j : ℕ)) * poleG n p q (j : ℕ) = q + C κ := by
            rw [hsum]
            rw [← hκ]
            rfl
          rw [hH, map_neg]
          ring
        rw [hEq]
        rw [map_sub, LinearMap.sub_apply, hsum_v]
        have hq0 : aeval A q (b 1) = 0 := by
          rw [hq, LinearMap.aeval_self_charpoly, LinearMap.zero_apply]
        rw [hq0, zero_sub]
    have hchar := charpoly_eq_of_companion p hp (A + b.comp f) v hrel
    exact ⟨f, hchar⟩

end Sufficiency


/-! ## Multi-input assembly: the controlled chain of Lemma 3.31

The single-input constructive theorem `exists_feedback_charpoly_single` is proved
above: for a controllable pair `(A, b)` with `b : ℝ →ₗ[ℝ] X` and any monic
`p : ℝ[X]` of degree `finrank ℝ X` there is `f : X →ₗ[ℝ] ℝ` with
`(A + b.comp f).charpoly = p`.

The multi-input statement (`B : U →ₗ[ℝ] X`, gain `F : X →ₗ[ℝ] U`) is obtained by
the MIMO reduction of Trentelman–Stoorvogel–Hautus, Lemma 3.31:

1. Handle `finrank ℝ X = 0` with `exists_feedback_charpoly_of_finrank_zero`.
2. For `n = finrank ℝ X > 0`, construct an independent controlled chain
   `x₀ = 0`, `x_{k+1} = A x_k + B u_k` (`k < n`). At each step, if
   `A x_k + B u ∈ span{x₁, …, x_k}` for every `u : U`, then `A x_k ∈ L`,
   `range B ≤ L` and `L` is `A`-invariant, so
   `eq_top_of_isControllable_of_map_le` contradicts `finrank L ≤ k < n`.
3. Let `F₀` be the unique map with `F₀ x_k = u_k`, so `b = B u₀` is cyclic for
   `A + B.comp F₀` with `x_k = (A + B F₀)^{k-1} b`.
4. Apply `exists_feedback_charpoly_single` to `(A + B F₀, b)`, obtaining
   `f : X →ₗ[ℝ] ℝ`, and set `F = F₀ + u₀.comp f`; then
   `B.comp F = B.comp F₀ + b.comp f` and the characteristic polynomial is `p`.

The controlled chain is formalised below as `exists_controlled_chain`, and the
multi-input theorem as `exists_feedback_charpoly_of_isControllable`.
-/

section MIMO

variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup U] [Module ℝ U]

/-- **Controlled chain (Trentelman–Stoorvogel–Hautus, Lemma 3.31).** For a
controllable pair `(A, B)` with `n = finrank ℝ X` there are vectors
`x 0 = 0, x 1, …, x n` and inputs `u 0, …, u (n-1)` with
`x (i+1) = A (x i) + B (u i)` such that `x 1, …, x n` are linearly independent.

The proof is the source's induction: given `x 1, …, x k` with
`L = span{x 1, …, x k}`, if `A (x k) + B u ∈ L` for every `u` then `A (x k) ∈ L`,
`range B ≤ L` and `L` is `A`-invariant, so controllability forces `L = ⊤`,
contradicting `finrank L ≤ k < n`. Hence some `u k` leaves `L`, and `x (k+1)` is
independent of `x 1, …, x k`. -/
theorem exists_controlled_chain (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (h : IsControllable A B) :
    ∃ (x : Fin (Module.finrank ℝ X + 1) → X) (u : Fin (Module.finrank ℝ X) → U),
      x 0 = 0 ∧
      (∀ i : Fin (Module.finrank ℝ X), x i.succ = A (x i.castSucc) + B (u i)) ∧
      LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ X) => x i.succ) := by
  classical
  set N : ℕ := Module.finrank ℝ X with hN
  let Good : (k : ℕ) → Type _ := fun k =>
    { p : (Fin (k + 1) → X) × (Fin k → U) //
        p.1 0 = 0 ∧
        (∀ i : Fin k, p.1 i.succ = A (p.1 i.castSucc) + B (p.2 i)) ∧
        LinearIndependent ℝ (fun i : Fin k => p.1 i.succ) }
  have build : ∀ k, k ≤ N → Good k := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨(fun _ => 0, Fin.elim0), rfl, ?_, ?_⟩
        · intro i; exact Fin.elim0 i
        · exact linearIndependent_empty_type
    | succ k ih =>
        intro hk
        obtain ⟨⟨x, u⟩, hx0, hchain, hind⟩ := ih (Nat.le_of_succ_le hk)
        have hx0' : x 0 = 0 := hx0
        have hkN : k < N := Nat.lt_of_succ_le hk
        set v : Fin k → X := fun i => x i.succ with hv
        have hv_eq : ∀ i, v i = x i.succ := fun i => rfl
        set L : Submodule ℝ X := Submodule.span ℝ (Set.range v) with hL
        have hex : ∃ w : U, A (x (Fin.last k)) + B w ∉ L := by
          by_contra hc
          push_neg at hc
          have hlast : A (x (Fin.last k)) ∈ L := by
            have := hc 0
            simpa using this
          have hB : LinearMap.range B ≤ L := by
            rintro y ⟨w, rfl⟩
            have h1 := hc w
            have h2 : B w = (A (x (Fin.last k)) + B w) - A (x (Fin.last k)) := by
              abel
            rw [h2]
            exact Submodule.sub_mem _ h1 hlast
          have hA : Submodule.map A L ≤ L := by
            rw [Submodule.map_le_iff_le_comap, hL, Submodule.span_le]
            rintro y ⟨i, rfl⟩
            change A (v i) ∈ Submodule.span ℝ (Set.range v)
            rw [hv_eq i]
            by_cases hi : (i.succ : Fin (k + 1)) = Fin.last k
            · rw [hi]; exact hlast
            · obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hi
              have hch : x j.succ = A (x j.castSucc) + B (u j) := hchain j
              have hAj : A (x j.castSucc) = x j.succ - B (u j) := by
                rw [hch]; abel
              rw [← hj, hAj]
              exact Submodule.sub_mem _
                (Submodule.subset_span (show x j.succ ∈ Set.range v from ⟨j, rfl⟩))
                (hB ⟨u j, rfl⟩)
          have htop : L = ⊤ := eq_top_of_isControllable_of_map_le A B h hA hB
          have hfin : Module.finrank ℝ L = N := by
            rw [htop, finrank_top, hN]
          have hle : Module.finrank ℝ L ≤ k := by
            rw [hL]
            have := finrank_range_le_card (R := ℝ) v
            simpa only [Set.finrank, Fintype.card_fin] using this
          omega
        let w : U := Classical.choose hex
        have hw : A (x (Fin.last k)) + B w ∉ L := Classical.choose_spec hex
        have hw' : A (x (Fin.last k)) + B w ∉ Submodule.span ℝ (Set.range v) := by
          rwa [hL] at hw
        refine ⟨(Fin.snoc x (A (x (Fin.last k)) + B w), Fin.snoc u w), ?_, ?_, ?_⟩
        · dsimp only
          rw [Fin.snoc_apply_zero, hx0']
        · intro i
          dsimp only
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
            exact hchain j
          · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_last]
        · have hv' : (fun i : Fin (k + 1) =>
              (Fin.snoc x (A (x (Fin.last k)) + B w) : Fin (k + 2) → X) i.succ)
              = (Fin.snoc v (A (x (Fin.last k)) + B w) : Fin (k + 1) → X) := by
            ext i
            rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
            · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc, hv_eq j]
            · simp only [Fin.succ_last, Fin.snoc_last]
          rw [hv']
          exact LinearIndependent.finSnoc hind hw'
  obtain ⟨⟨x, u⟩, hx0, hchain, hind⟩ := build N le_rfl
  exact ⟨x, u, hx0, hchain, hind⟩

/-- **Pole placement (sufficiency), multi-input.** For a controllable pair
`(A, B)` on a finite-dimensional real state space and any monic real polynomial
`p` of degree `finrank ℝ X`, there is a real state feedback `F : X →ₗ[ℝ] U`
with `(A + B.comp F).charpoly = p`.

The proof builds the controlled chain `exists_controlled_chain`, defines `F₀` on
its basis so that `b = B u₀` is cyclic for `A + B.comp F₀`, applies the
single-input theorem `exists_feedback_charpoly_single` to `(A + B.comp F₀, b)`,
and assembles `F = F₀ + u₀.comp f`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.29, PDF pages 73–74. -/
theorem exists_feedback_charpoly_of_isControllable
    [FiniteDimensional ℝ X]
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (h : IsControllable A B) (p : ℝ[X]) (hp : p.Monic)
    (hpdeg : p.natDegree = Module.finrank ℝ X) :
    ∃ F : X →ₗ[ℝ] U, (A + B.comp F).charpoly = p := by
  classical
  by_cases hzero : Module.finrank ℝ X = 0
  · exact exists_feedback_charpoly_of_finrank_zero A B hzero p hp hpdeg
  have hNpos : 0 < Module.finrank ℝ X := Nat.pos_of_ne_zero hzero
  haveI : NeZero (Module.finrank ℝ X) := ⟨hNpos.ne'⟩
  obtain ⟨x, u, hx0, hchain, hind⟩ := exists_controlled_chain A B h
  let v : Fin (Module.finrank ℝ X) → X := fun i => x i.succ
  have hv_eq : ∀ i, v i = x i.succ := fun i => rfl
  have hv : LinearIndependent ℝ v := hind
  let vb : Basis (Fin (Module.finrank ℝ X)) ℝ X :=
    basisOfLinearIndependentOfCardEqFinrank hv (by simp)
  have hvb : ∀ i, vb i = v i := by
    intro i
    change (basisOfLinearIndependentOfCardEqFinrank hv _) i = v i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  let f₀ : Fin (Module.finrank ℝ X) → U :=
    fun i => if hi : (i : ℕ) + 1 < Module.finrank ℝ X then u ⟨(i : ℕ) + 1, hi⟩ else 0
  let F₀ : X →ₗ[ℝ] U := vb.constr ℝ f₀
  have hF₀ : ∀ i, F₀ (vb i) = f₀ i := fun i => by
    simp only [F₀, Basis.constr_basis]
  let b₀ : X := B (u 0)
  have hb₀ : vb 0 = b₀ := by
    rw [hvb 0, hv_eq 0]
    have hc0 : x ((0 : Fin (Module.finrank ℝ X)).succ)
        = A (x ((0 : Fin (Module.finrank ℝ X)).castSucc)) + B (u 0) := hchain 0
    have hx00 : x ((0 : Fin (Module.finrank ℝ X)).castSucc) = 0 := by
      simpa using hx0
    rw [hc0, hx00, map_zero, zero_add]
  let b : ℝ →ₗ[ℝ] X := LinearMap.toSpanSingleton ℝ X b₀
  have hb : b 1 = b₀ := LinearMap.toSpanSingleton_apply_one ℝ X b₀
  let T : X →ₗ[ℝ] X := A + B.comp F₀
  have hrec : ∀ (i : Fin (Module.finrank ℝ X)) (hi : (i : ℕ) + 1 < Module.finrank ℝ X),
      T (v i) = v ⟨(i : ℕ) + 1, hi⟩ := by
    intro i hi
    have hF0i : F₀ (v i) = u ⟨(i : ℕ) + 1, hi⟩ := by
      have h1 : F₀ (vb i) = f₀ i := hF₀ i
      rw [hvb i] at h1
      rw [h1]
      exact dif_pos hi
    have hT : T (v i) = A (v i) + B (u ⟨(i : ℕ) + 1, hi⟩) := by
      simp only [T, LinearMap.add_apply, LinearMap.comp_apply, hF0i]
    rw [hT, hv_eq i, hv_eq ⟨(i : ℕ) + 1, hi⟩]
    have hsucc : (i.succ : Fin (Module.finrank ℝ X + 1))
        = (⟨(i : ℕ) + 1, hi⟩ : Fin (Module.finrank ℝ X)).castSucc := Fin.ext rfl
    have hch := hchain ⟨(i : ℕ) + 1, hi⟩
    rw [hsucc]
    exact hch.symm
  have krylov : ∀ (i : ℕ) (hi : i < Module.finrank ℝ X),
      (T ^ i) b₀ = v ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
        intro hi
        rw [pow_zero, Module.End.one_eq_id, LinearMap.id_apply]
        exact (hb₀.symm).trans (hvb 0)
    | succ i ih =>
        intro hi
        rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
        rw [ih (Nat.lt_of_succ_lt hi)]
        exact hrec ⟨i, Nat.lt_of_succ_lt hi⟩ hi
  have hcont : IsControllable T b := by
    rw [isControllable_iff, eq_top_iff, ← vb.span_eq]
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    rw [hvb i]
    have hvi : v i = (T ^ (i : ℕ)) b₀ := (krylov (i : ℕ) i.isLt).symm
    rw [hvi]
    have hsym : (T ^ (i : ℕ)) b₀ = ((T ^ (i : ℕ)).comp b) 1 := by
      rw [LinearMap.comp_apply, hb]
    rw [hsym]
    exact Submodule.mem_iSup_of_mem (i : ℕ) ⟨1, rfl⟩
  obtain ⟨f, hf⟩ := exists_feedback_charpoly_single T b hcont p hp hpdeg
  let u₀ : ℝ →ₗ[ℝ] U := LinearMap.toSpanSingleton ℝ U (u 0)
  have hBu₀ : B.comp u₀ = b := by
    ext c
    simp only [LinearMap.comp_apply, u₀, b, b₀, LinearMap.toSpanSingleton_apply,
      map_smul]
  refine ⟨F₀ + u₀.comp f, ?_⟩
  have hBcomp : B.comp (F₀ + u₀.comp f) = B.comp F₀ + b.comp f := by
    rw [LinearMap.comp_add, ← LinearMap.comp_assoc, hBu₀]
  have hfinal : A + B.comp (F₀ + u₀.comp f) = (A + B.comp F₀) + b.comp f := by
    rw [hBcomp]
    abel
  rw [hfinal]
  exact hf

end MIMO

end LinearMap
