/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.TransferPoleStability
public import Mathlib.LinearAlgebra.Matrix.Polynomial

/-! # Degree bound for state-space transfer numerators

The Cramer numerator of a finite-dimensional scalar channel has degree less
than the state characteristic polynomial. Thus divisibility by that
characteristic polynomial forces the numerator to vanish, including in the
zero-dimensional case.
-/

@[expose] public section

open Polynomial
open Equiv.Perm

set_option maxHeartbeats 500000

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem natDegree_updateRow_charmatrix_det_le (A : Matrix n n ℂ) (i : n)
    (v : n → ℂ) :
    (Matrix.charmatrix A |>.updateRow i (fun j => Polynomial.C (v j))).det.natDegree
      ≤ Fintype.card n - 1 := by
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro σ
  calc
    natDegree (sign σ • ∏ j : n,
      (Matrix.charmatrix A |>.updateRow i (fun j => Polynomial.C (v j))) (σ j) j) ≤
      natDegree (∏ j : n,
      (Matrix.charmatrix A |>.updateRow i (fun j => Polynomial.C (v j))) (σ j) j) := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · rw [h, one_smul]
        · rw [h, Units.neg_smul, one_smul, natDegree_neg]
    _ ≤ ∑ j : n, natDegree
      ((Matrix.charmatrix A |>.updateRow i (fun j => Polynomial.C (v j))) (σ j) j) :=
      (natDegree_prod_le (Finset.univ : Finset n) _)
    _ ≤ Fintype.card n - 1 := by
      let j0 : n := σ.symm i
      have hσj0 : σ j0 = i := by simp [j0]
      have hmem : j0 ∈ (Finset.univ : Finset n) := Finset.mem_univ _
      have hspecial : natDegree
          ((Matrix.charmatrix A |>.updateRow i (fun j => Polynomial.C (v j)))
            (σ j0) j0) = 0 := by
        simp [Matrix.updateRow_apply, hσj0]
      have hrest : (∑ j ∈ (Finset.univ.erase j0), natDegree
          ((Matrix.charmatrix A |>.updateRow i (fun j => Polynomial.C (v j)))
            (σ j) j)) ≤ (Finset.univ.erase j0).card := by
        calc
          _ ≤ (Finset.univ.erase j0).card • 1 := by
            apply Finset.sum_le_card_nsmul
            intro j hj
            have hjne : j ≠ j0 := (Finset.mem_erase.mp hj).1
            have hji : σ j ≠ i := by
              intro h
              apply hjne
              apply σ.injective
              simpa [hσj0] using h
            simp only [Matrix.updateRow_apply, if_neg hji]
            simp only [Matrix.charmatrix]
            by_cases hdiag : σ j = j
            · simp [Matrix.diagonal, hdiag]
            · simp [Matrix.diagonal, hdiag]
          _ = (Finset.univ.erase j0).card := by simp
      have hsum : (∑ j : n, natDegree
          ((Matrix.charmatrix A |>.updateRow i (fun j => Polynomial.C (v j)))
            (σ j) j)) = natDegree
              ((Matrix.charmatrix A |>.updateRow i (fun j => Polynomial.C (v j)))
                (σ j0) j0) +
          ∑ j ∈ (Finset.univ.erase j0), natDegree
          ((Matrix.charmatrix A |>.updateRow i (fun j => Polynomial.C (v j)))
            (σ j) j) := by
        let f : n → ℕ := fun j => natDegree
          ((Matrix.charmatrix A |>.updateRow i (fun j => Polynomial.C (v j)))
            (σ j) j)
        change (Finset.univ.sum f) = f j0 + (Finset.univ.erase j0).sum f
        exact (Finset.add_sum_erase _ f hmem).symm
      rw [hsum, hspecial, zero_add]
      simpa using hrest

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The scalar Cramer numerator is strictly lower-degree than the
characteristic denominator when the state index is nonempty. -/
theorem channelTransferNumerator_natDegree_lt [Nonempty n]
    (A : Matrix n n ℂ) (c b : n → ℂ) :
    (channelTransferNumerator A c b).natDegree < A.charpoly.natDegree := by
  rw [Matrix.charpoly_natDegree_eq_dim]
  let m := Fintype.card n - 1
  have hterm (i j : n) :
      natDegree (C (c i) * (Matrix.adjugate (Matrix.charmatrix A) i j) * C (b j)) ≤ m := by
    calc
      _ ≤ natDegree (C (c i) * (Matrix.adjugate (Matrix.charmatrix A) i j)) +
          natDegree (C (b j)) := natDegree_mul_le
      _ ≤ natDegree (Matrix.adjugate (Matrix.charmatrix A) i j) := by
        calc
          _ ≤ (natDegree (C (c i)) + natDegree (Matrix.adjugate (Matrix.charmatrix A) i j)) +
              natDegree (C (b j)) := by exact Nat.add_le_add_right natDegree_mul_le _
          _ = natDegree (Matrix.adjugate (Matrix.charmatrix A) i j) := by simp
      _ ≤ m := by
        rw [Matrix.adjugate_apply]
        have hv : (Matrix.charmatrix A).updateRow j (Pi.single i (1 : Polynomial ℂ)) =
            (Matrix.charmatrix A).updateRow j
              (fun k => C ((Pi.single i (1 : ℂ) : n → ℂ) k)) := by
          ext k l
          simp [Matrix.updateRow_apply, Pi.single_apply]
        rw [hv]
        exact natDegree_updateRow_charmatrix_det_le A j (Pi.single i (1 : ℂ))
  unfold channelTransferNumerator
  have hbound : (∑ i : n, ∑ j : n,
      C (c i) * (Matrix.adjugate (Matrix.charmatrix A) i j) * C (b j)).natDegree ≤ m := by
    apply natDegree_sum_le_of_forall_le _ _
    intro i hi
    apply natDegree_sum_le_of_forall_le _ _
    intro j hj
    exact hterm i j
  have hcard : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨Classical.choice ‹Nonempty n›⟩
  exact hbound.trans_lt (by
    dsimp [m]
    exact Nat.pred_lt (Nat.ne_of_gt hcard))

/-- A scalar Cramer numerator divisible by the characteristic polynomial
must vanish; this also covers the zero-dimensional state space. -/
theorem channelTransferNumerator_eq_zero_of_charpoly_dvd
    (A : Matrix n n ℂ) (c b : n → ℂ)
    (hdiv : A.charpoly ∣ channelTransferNumerator A c b) :
    channelTransferNumerator A c b = 0 := by
  classical
  by_cases hn : Nonempty n
  · letI := hn
    by_contra hzero
    have hle := Polynomial.natDegree_le_of_dvd hdiv hzero
    exact (not_lt_of_ge hle) (channelTransferNumerator_natDegree_lt A c b)
  · haveI : IsEmpty n := not_nonempty_iff.mp hn
    simp [channelTransferNumerator]

end Matrix
