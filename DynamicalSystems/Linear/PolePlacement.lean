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

/-! ## Remaining obligation: sufficiency (construction of the feedback)

The forward direction of Theorem 3.29 is **not** proved in this file. Its exact
statement, to be added here as a theorem, is

```
theorem exists_feedback_charpoly_of_isControllable
    [FiniteDimensional ℝ X] (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (h : IsControllable A B) (p : ℝ[X]) (hp : p.Monic)
    (hpdeg : p.natDegree = Module.finrank ℝ X) :
    ∃ F : X →ₗ[ℝ] U, (A + B.comp F).charpoly = p
```

Because `p` is an arbitrary monic `ℝ[X]`, its non-real roots occur in complex
conjugate pairs, so this is the correct *real* statement; no complex feedback is
introduced.

### Source proof route (Trentelman–Stoorvogel–Hautus, PDF pages 73–74)

1. **SISO companion form.** For a controllable single-input pair `(A', b)` the
   vectors `b, A'b, …, (A')^{n-1}b` form a basis (Theorem 3.18). In that basis the
   matrix of `A'` is the companion matrix, and a row feedback `f` can set its last
   row arbitrarily. Hence every monic `p` of degree `n` is realised. This step is
   already the bulk of the work: it needs
   * the Krylov basis `(A')^k b` and a proof that it is a basis from
     controllability (equivalently `kalmanControllabilityMap A' b n` is
     bijective, `Kalman.lean`),
   * the matrix of `A'` in that basis being the companion matrix, and
   * `Matrix.charpoly` of the companion matrix. The last point is now discharged
     by `LinearMap.charpoly_eq_of_companion` above, which proves the companion
     characteristic polynomial from `PowerBasis.leftMulMatrix` on `AdjoinRoot p`
     without any determinant expansion.

2. **MIMO reduction (Lemma 3.31).** From controllability of `(A, B)` with
   `n = finrank ℝ X > 0`, construct `u₀, …, u_{n-1} : U` such that
   `x₁ = B u₀`, `x_{k+1} = A x_k + B u_k` are independent. Then the unique
   `F₀` with `F₀ x_k = u_k` makes `b = B u₀` cyclic for `A + B F₀`:
   `x_k = (A + B F₀)^{k-1} b`. Apply step 1 to the single-input pair
   `(A + B F₀, b)` to obtain `f` with the prescribed characteristic polynomial;
   the final gain is `F = F₀ + u₀.comp f` (i.e. `F x = F₀ x + f x • u₀`).

3. **Zero dimension.** `finrank ℝ X = 0` must be handled separately before the
   `B ≠ 0` argument of Lemma 3.31; then `p = 1`, `F = 0`.

### Progress added in the present pass (all proved, no placeholders)

In addition to the feedback-invariance, quotient-obstruction,
companion-characteristic-polynomial and zero-dimensional pieces, the following
ingredients of the sufficiency proof are now available:

* `LinearMap.ne_zero_of_isControllable`: controllability on a positive-
  dimensional state space forces `B ≠ 0` (first step of Lemma 3.31).
* `LinearMap.isControllable_iff_bijective_kalmanControllabilityMap_single`:
  for `b : ℝ →ₗ X`, controllability is bijectivity of the Kalman map.
* `LinearMap.linearIndependent_krylov_of_isControllable_single`: the Krylov
  vectors `b, A b, …, A^{n-1} b` are a basis (Theorem 3.18 input).
* `LinearMap.eq_top_of_isControllable_of_map_le`: a proper `A`-invariant
  subspace containing `range B` cannot exist for a controllable pair, i.e. the
  key step used to extend a controlled chain (Lemma 3.31 input).

### Remaining gap

The missing piece is the construction of the feedback *and* the MIMO chain. The
plan below is explicit and avoids the `adjugate`/determinant route entirely; it
uses only `LinearMap.charpoly_eq_of_companion` (already proved above) and
Cayley–Hamilton.

**SISO construction in the Krylov basis.** Let `(A, b)` with `b : ℝ →ₗ X` be
controllable, `n = finrank ℝ X`, `q = A.charpoly`, and let the Krylov basis be
`e_i = A^i (b 1)`, `i : Fin n` (independence is
`linearIndependent_krylov_of_isControllable_single`). Write
`q(t) = t^n + ∑_{j<n} q_j t^j` and the target
`p(t) = t^n + ∑_{j<n} p_j t^j`. Define constants `c_0, …, c_{n-2}` by the
*forward triangular recurrence*

  `c_r = (q_{n-1-r} - p_{n-1-r}) - ∑_{k<r} c_k · p_{n-r+k}`,
  `r = 0, …, n-2`.

Set `G_i(t) = t^i + ∑_{k=0}^{i-1} c_k t^{i-1-k}` (monic of degree `i`) and
`y_i = G_i(A) (b 1)`. Because `G_{i+1} = t G_i + c_i`, one has the chain
`y_{i+1} = A y_i + c_i • b 1`, and the `y_i` are triangular over `(e_i)`, hence a
basis. Define the polynomial

  `h_p(t) = t · G_{n-1}(t) + ∑_{j<n} p_j · G_j(t)`.

Expanding the coefficient of `t^m` (`1 ≤ m ≤ n-1`) in `h_p` gives exactly
`c_{n-1-m} + p_m + ∑_{k=0}^{n-2-m} c_k p_{m+1+k}`, so the recurrence says that
`h_p` and `q` have the same coefficients in degrees `1, …, n-1`. Both are monic
of degree `n`, hence `h_p = q + κ` for the constant `κ`. Cayley–Hamilton gives
`h_p(A)(b 1) = κ · b 1`, i.e. `A y_{n-1} + ∑_{j<n} p_j y_j = κ · b 1`.

Finally define `f : X →ₗ ℝ` on the basis `(y_i)` by `f (y_i) = c_i` for
`i < n-1` and `f (y_{n-1}) = -κ` (use `Basis.constr`). Then
`(A + b.comp f)(y_i) = y_{i+1}` for `i < n-1` and
`(A + b.comp f)(y_{n-1}) = -∑_{j<n} p_j y_j`, which are exactly the companion
relations of `p` in the basis `(y_i)`; `LinearMap.charpoly_eq_of_companion`
applied to `T = A + b.comp f`, `v =` the basis `(y_i)` and `p` yields
`(A + b.comp f).charpoly = p`.

**MIMO reduction (Lemma 3.31).** With `n = finrank ℝ X > 0` and `(A, B)`
controllable, build an independent chain `x_0 = 0`, `x_{k+1} = A x_k + B u_k`
(`x_1 = B u_0`) by induction: at each step, if
`A x_k + B u ∈ span{x_1, …, x_k}` for *every* `u : U`, then taking `u = 0`
gives `A x_k ∈ L`, subtracting gives `range B ≤ L`, and the chain relations make
`L` `A`-invariant; `LinearMap.eq_top_of_isControllable_of_map_le` then forces
`L = ⊤`, contradicting `finrank L = k < n`. Hence some `u_k` works and the chain
extends. Then `F₀` defined on the basis `(x_k)` by `F₀ x_k = u_k` satisfies
`(A + B F₀) x_k = x_{k+1}`, so `x_k = (A + B F₀)^{k-1} (B u₀)`, i.e.
`(A + B F₀, B u₀)` is a controllable single-input pair. Apply the SISO step to
that pair (with `b := ℝ →ₗ X, 1 ↦ B u₀`) to get `f : X →ₗ ℝ`, and put
`F = F₀ + u₀.comp f`; then `B.comp F = B.comp F₀ + b.comp f`, so
`(A + B.comp F).charpoly = p`.

**Zero dimension** is already discharged by
`exists_feedback_charpoly_of_finrank_zero`.

### Suggested next Lean steps (in order, all self-contained)

* Define `c : Fin (n-1) → ℝ` (or a `ℕ`-indexed function on `r < n-1`) by the
  forward recurrence above and prove the coefficient identity for `h_p` by
  `Finset.sum` manipulation over `Polynomial.coeff`; this is pure polynomial
  arithmetic and the only remaining non-structural work in the SISO step.
* Build the basis `(y_i)` with `Basis.mk` from the triangular independence over
  the Krylov basis and define `f` with `Basis.constr`; verify the two companion
  relations by the `G_{i+1} = t G_i + c_i` identity and `h_p = q + κ`.
* Formalise the MIMO chain by strong induction on `k ≤ n`, using `Fin.snoc`
  together with `LinearIndependent.finSnoc'` and the
  `eq_top_of_isControllable_of_map_le` lemma above; define `F₀` with
  `Basis.constr` on the chain basis.
* Combine and use `exists_feedback_charpoly_of_finrank_zero` for `n = 0`.

The result `exists_feedback_charpoly_of_isControllable` is therefore **not yet**
proved, and this file does not claim it is. The declarations proved above are
independently checkable ingredients of the Trentelman–Stoorvogel–Hautus proof.
-/

end LinearMap
