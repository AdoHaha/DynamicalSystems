/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.TransferPoleStability
public import DynamicalSystems.Linear.Hautus

/-! # Noncancellation at rank-one characteristic roots

For a controllable and observable complex matrix realization, a characteristic
root whose evaluated adjugate is nonzero is a pole of some scalar transfer-matrix
entry. This covers the corank-one case. The general higher-order root case,
where the evaluated adjugate can vanish, remains open.
-/

@[expose] public section


open Polynomial

noncomputable section

namespace RatFunc

theorem isRoot_denom_mk_of_isRoot_of_not_isRoot
    (p q : Polynomial ℂ) (z : ℂ) (hq : q ≠ 0)
    (hzq : q.IsRoot z) (hzp : ¬ p.IsRoot z) :
    (RatFunc.mk p q).denom.IsRoot z := by
  have hid : (RatFunc.mk p q).num * q = p * (RatFunc.mk p q).denom := by
    apply (RatFunc.num_mul_eq_mul_denom_iff hq).2
    exact RatFunc.mk_eq_div p q
  have heval := congrArg (Polynomial.eval z) hid
  change q.eval z = 0 at hzq
  change p.eval z ≠ 0 at hzp
  simp only [Polynomial.eval_mul, hzq, mul_zero] at heval
  change (RatFunc.mk p q).denom.eval z = 0
  exact (mul_eq_zero.mp heval.symm).resolve_left hzp

end RatFunc

namespace LinearMap

variable {X U Y : Type*}
variable [AddCommGroup X] [Module ℂ X]
variable [AddCommGroup U] [Module ℂ U]
variable [AddCommGroup Y] [Module ℂ Y]

theorem nonzero_readout_adjugate_of_pbh
    (M J : X →ₗ[ℂ] X) (B : U →ₗ[ℂ] X) (C : X →ₗ[ℂ] Y)
    (hJM : J.comp M = 0) (hMJ : M.comp J = 0)
    (hreach : LinearMap.range M ⊔ LinearMap.range B = ⊤)
    (hobs : LinearMap.ker M ⊓ LinearMap.ker C = ⊥)
    (hJ : J ≠ 0) : C.comp (J.comp B) ≠ 0 := by
  intro hzero
  apply hJ
  ext x
  have hx : x ∈ LinearMap.range M ⊔ LinearMap.range B := by
    rw [hreach]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp ha
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hb
  have hJu : J (B u) = 0 := by
    have hkerM : J (B u) ∈ LinearMap.ker M := by
      rw [LinearMap.mem_ker]
      have h := congrArg (fun T : X →ₗ[ℂ] X => T (B u)) hMJ
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
    have hkerC : J (B u) ∈ LinearMap.ker C := by
      rw [LinearMap.mem_ker]
      have h := congrArg (fun T : U →ₗ[ℂ] Y => T u) hzero
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
    have hh : J (B u) ∈ (⊥ : Submodule ℂ X) := by
      rw [← hobs]
      exact ⟨hkerM, hkerC⟩
    simpa only [Submodule.mem_bot] using hh
  rw [← hab, map_add]
  have hMv : J (M v) = 0 := by
    have h := congrArg (fun T : X →ₗ[ℂ] X => T v) hJM
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  simp [hMv, hJu]

end LinearMap

namespace Matrix

variable {n m p : Type*} [Fintype n] [DecidableEq n]
variable [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

theorem channelTransferNumerator_eval_eq_adjugate_channel
    (A : Matrix n n ℂ) (c b : n → ℂ) (z : ℂ) :
    (channelTransferNumerator A c b).eval z =
      ∑ i : n, c i * (((Matrix.scalar n z - A).adjugate) *ᵥ b) i := by
  let M : Matrix n n ℂ := Matrix.scalar n z - A
  have hM : (Polynomial.evalRingHom z).mapMatrix (Matrix.charmatrix A) = M := by
    ext i j
    change ((Matrix.charmatrix A) i j).eval z = M i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.charmatrix_apply_eq, M, Matrix.scalar_apply]
    · simp [M, Matrix.scalar_apply, hij]
  have hadjEval :
      (Polynomial.evalRingHom z).mapMatrix (Matrix.adjugate (Matrix.charmatrix A)) =
        M.adjugate := by
    rw [RingHom.map_adjugate, hM]
  have hadjEntry (i j : n) :
      (Matrix.adjugate (Matrix.charmatrix A) i j).eval z = M.adjugate i j := by
    have h := congrArg (fun N : Matrix n n ℂ => N i j) hadjEval
    simpa using h
  rw [channelTransferNumerator, Polynomial.eval_finsetSum]
  simp_rw [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, hadjEntry]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem channelTransferNumerator_eval_eq_transfer_matrix_entry
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix p n ℂ)
    (z : ℂ) (i : p) (j : m) :
    (channelTransferNumerator A (C i) (fun k => B k j)).eval z =
      (C * (Matrix.scalar n z - A).adjugate * B) i j := by
  rw [channelTransferNumerator_eval_eq_adjugate_channel, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem exists_scalar_transfer_pole_of_nonzero_cramer_numerator
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix p n ℂ)
    (z : ℂ) (hz : A.charpoly.IsRoot z)
    (i : p) (j : m)
    (hnum : ¬ (channelTransferNumerator A (C i) (fun k => B k j)).IsRoot z) :
    (channelTransferRatFunc A (C i) (fun k => B k j)).denom.IsRoot z := by
  exact RatFunc.isRoot_denom_mk_of_isRoot_of_not_isRoot
    _ _ z A.charpoly_monic.ne_zero hz hnum

theorem transfer_matrix_nonzero_of_pbh_and_adjugate_nonzero
    (M : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix p n ℂ)
    (hdet : M.det = 0)
    (hreach : LinearMap.range M.mulVecLin ⊔ LinearMap.range B.mulVecLin = ⊤)
    (hobs : LinearMap.ker M.mulVecLin ⊓ LinearMap.ker C.mulVecLin = ⊥)
    (hadj : M.adjugate ≠ 0) :
    C * M.adjugate * B ≠ 0 := by
  let ML : (n → ℂ) →ₗ[ℂ] n → ℂ := M.mulVecLin
  let J : (n → ℂ) →ₗ[ℂ] n → ℂ := M.adjugate.mulVecLin
  have hJM : J.comp ML = 0 := by
    change M.adjugate.mulVecLin.comp M.mulVecLin = 0
    rw [← Matrix.mulVecLin_mul, Matrix.adjugate_mul, hdet, zero_smul, Matrix.mulVecLin_zero]
  have hMJ : ML.comp J = 0 := by
    change M.mulVecLin.comp M.adjugate.mulVecLin = 0
    rw [← Matrix.mulVecLin_mul, Matrix.mul_adjugate, hdet, zero_smul, Matrix.mulVecLin_zero]
  have hJ : J ≠ 0 := by
    intro h
    apply hadj
    apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_apply', Matrix.mulVecLin_zero] using h
  have hmap : C.mulVecLin.comp (J.comp B.mulVecLin) ≠ 0 :=
    LinearMap.nonzero_readout_adjugate_of_pbh ML J B.mulVecLin C.mulVecLin
      hJM hMJ hreach hobs hJ
  intro hzero
  apply hmap
  change C.mulVecLin.comp (M.adjugate.mulVecLin.comp B.mulVecLin) = 0
  rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, ← Matrix.mul_assoc,
    hzero, Matrix.mulVecLin_zero]

theorem exists_scalar_transfer_pole_of_pbh_and_adjugate_nonzero
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix p n ℂ)
    (z : ℂ) (hz : A.charpoly.IsRoot z)
    (hreach : LinearMap.range (Matrix.scalar n z - A).mulVecLin ⊔
      LinearMap.range B.mulVecLin = ⊤)
    (hobs : LinearMap.ker (Matrix.scalar n z - A).mulVecLin ⊓
      LinearMap.ker C.mulVecLin = ⊥)
    (hadj : (Matrix.scalar n z - A).adjugate ≠ 0) :
    ∃ (i : p) (j : m),
      (channelTransferRatFunc A (C i) (fun k => B k j)).denom.IsRoot z := by
  have hdet : (Matrix.scalar n z - A).det = 0 := by
    change A.charpoly.eval z = 0 at hz
    rwa [Matrix.eval_charpoly] at hz
  have hprod := transfer_matrix_nonzero_of_pbh_and_adjugate_nonzero
    (Matrix.scalar n z - A) B C hdet hreach hobs hadj
  by_contra hnone
  push_neg at hnone
  apply hprod
  ext i j
  by_contra hentry
  have hnum : ¬ (channelTransferNumerator A (C i) (fun k => B k j)).IsRoot z := by
    change (channelTransferNumerator A (C i) (fun k => B k j)).eval z ≠ 0
    rw [channelTransferNumerator_eval_eq_transfer_matrix_entry]
    exact hentry
  have hpole := exists_scalar_transfer_pole_of_nonzero_cramer_numerator
    A B C z hz i j hnum
  exact hnone i j hpole

/-- For a controllable and observable realization, any characteristic root
where the evaluated adjugate is nonzero is a pole of at least one reduced
scalar transfer-matrix entry. -/
theorem exists_scalar_transfer_pole_of_minimal_rank_one_root
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix p n ℂ)
    (hctrl : LinearMap.IsControllable A.mulVecLin B.mulVecLin)
    (hobs : LinearMap.IsObservable C.mulVecLin A.mulVecLin)
    (z : ℂ) (hz : A.charpoly.IsRoot z)
    (hadj : (Matrix.scalar n z - A).adjugate ≠ 0) :
    ∃ (i : p) (j : m),
      (channelTransferRatFunc A (C i) (fun k => B k j)).denom.IsRoot z := by
  have hM : (Matrix.scalar n z - A).mulVecLin =
      -(A.mulVecLin - z • (1 : (n → ℂ) →ₗ[ℂ] n → ℂ)) := by
    ext x
    simp [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.scalar_apply,
      Pi.single_apply, smul_eq_mul]
  have hreach : LinearMap.range (Matrix.scalar n z - A).mulVecLin ⊔
      LinearMap.range B.mulVecLin = ⊤ := by
    rw [hM, LinearMap.range_neg]
    exact (LinearMap.isControllable_iff_hautus A.mulVecLin B.mulVecLin).mp hctrl z
  have hobs' : LinearMap.ker (Matrix.scalar n z - A).mulVecLin ⊓
      LinearMap.ker C.mulVecLin = ⊥ := by
    rw [hM, LinearMap.ker_neg]
    have hh := (LinearMap.isObservable_iff_hautus C.mulVecLin A.mulVecLin).mp hobs z
    simpa only [LinearMap.ker_hautusObservabilityMap, Module.End.eigenspace_def] using hh
  exact exists_scalar_transfer_pole_of_pbh_and_adjugate_nonzero
    A B C z hz hreach hobs' hadj

end Matrix
