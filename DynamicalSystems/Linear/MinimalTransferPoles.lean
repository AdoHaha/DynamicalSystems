/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.TransferDenominatorRecurrence
public import DynamicalSystems.Linear.MinimalPoleCancellation
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! # Transfer poles of a minimal realization

Every characteristic root of a finite-dimensional complex controllable and
observable realization appears as a pole of at least one reduced scalar entry
of its transfer matrix. Unlike the corank-one result, this includes repeated
roots with vanishing evaluated adjugate. The proof uses a common denominator,
the finite Markov recurrence, and controllability/observability.
-/

@[expose] public section


set_option maxHeartbeats 1000000

open Polynomial

noncomputable section

namespace LinearMap

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]

theorem isRoot_of_aeval_eq_zero (A : X →ₗ[ℂ] X) (q : Polynomial ℂ)
    (hq : aeval A q = 0) (z : ℂ) (hz : A.charpoly.IsRoot z) : q.IsRoot z := by
  have heig : Module.End.HasEigenvalue A z :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly A z).mpr hz
  have hmin : (minpoly ℂ A).IsRoot z :=
    (Module.End.hasEigenvalue_iff_isRoot).mp heig
  exact hmin.dvd (minpoly.dvd ℂ A hq)

end LinearMap

namespace Matrix

variable {n m p : Type*} [Fintype n] [DecidableEq n]
variable [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

def commonChannelDenominator (A : Matrix n n ℂ) (B : Matrix n m ℂ)
    (C : Matrix p n ℂ) : Polynomial ℂ :=
  ∏ ij : p × m,
    (channelTransferRatFunc A (C ij.1) (fun k ↦ B k ij.2)).denom

theorem channel_denom_dvd_commonChannelDenominator
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix p n ℂ)
  (i : p) (j : m) :
    (channelTransferRatFunc A (C i) (fun k ↦ B k j)).denom ∣
      commonChannelDenominator A B C := by
  let f : p × m → Polynomial ℂ :=
    fun ij ↦ (channelTransferRatFunc A (C ij.1) (fun k ↦ B k ij.2)).denom
  have hf : f (i, j) ∣ ∏ ij : p × m, f ij :=
    Finset.dvd_prod_of_mem f (Finset.mem_univ (i, j))
  exact hf

theorem exists_channel_denom_root_of_common_root
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix p n ℂ)
    (z : ℂ) (hz : (commonChannelDenominator A B C).IsRoot z) :
    ∃ (i : p) (j : m),
      (channelTransferRatFunc A (C i) (fun k ↦ B k j)).denom.IsRoot z := by
  change (commonChannelDenominator A B C).eval z = 0 at hz
  rw [commonChannelDenominator, Polynomial.eval_prod] at hz
  obtain ⟨⟨i, j⟩, _, hij⟩ := Finset.prod_eq_zero_iff.mp hz
  exact ⟨i, j, hij⟩

theorem mulVecLin_aeval (A : Matrix n n ℂ) (q : Polynomial ℂ) :
    (aeval A q).mulVecLin = aeval A.mulVecLin q := by
  exact (Polynomial.aeval_algHom_apply Matrix.toLinAlgEquiv' A q).symm

theorem matrix_markov_zero_of_channel_denoms
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix p n ℂ)
    (q : Polynomial ℂ)
    (hden : ∀ i : p, ∀ j : m,
      (channelTransferRatFunc A (C i) (fun k ↦ B k j)).denom ∣ q)
    (k : ℕ) :
    C * ((aeval A q) * (A ^ k) * B) = 0 := by
  ext i j
  have h := channel_markov_annihilation_of_denom_dvd A (C i)
    (fun l ↦ B l j) q (hden i j) k
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.mul_assoc] using h

theorem aeval_eq_zero_of_channel_denoms
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix p n ℂ)
    (hctrl : LinearMap.IsControllable A.mulVecLin B.mulVecLin)
    (hobs : LinearMap.IsObservable C.mulVecLin A.mulVecLin)
    (q : Polynomial ℂ)
    (hden : ∀ i : p, ∀ j : m,
      (channelTransferRatFunc A (C i) (fun k ↦ B k j)).denom ∣ q) :
    aeval A.mulVecLin q = 0 := by
  apply LinearMap.aeval_eq_zero_of_markov_annihilation
    A.mulVecLin B.mulVecLin C.mulVecLin hctrl hobs q
  intro k u
  have hcomm : (aeval A q) * A ^ k = A ^ k * (aeval A q) := by
    have h := congrArg (aeval A) (mul_comm q (X ^ k))
    simpa only [map_mul, map_pow, aeval_X] using h
  have hm := matrix_markov_zero_of_channel_denoms A B C q hden k
  rw [hcomm] at hm
  have hv := congrArg (fun M : Matrix p m ℂ ↦ M *ᵥ u) hm
  rw [← mulVecLin_aeval A q]
  change C.toLin' ((A.toLin' ^ k) (((aeval A q).toLin') (B.toLin' u))) = 0
  rw [← Matrix.toLin'_pow]
  change C *ᵥ ((A ^ k) *ᵥ ((aeval A q) *ᵥ (B *ᵥ u))) = 0
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.zero_mulVec] using hv

/-- Every characteristic root of a controllable and observable realization
survives pole cancellation in at least one scalar transfer-matrix entry. -/
theorem exists_scalar_transfer_pole_of_minimal
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix p n ℂ)
    (hctrl : LinearMap.IsControllable A.mulVecLin B.mulVecLin)
    (hobs : LinearMap.IsObservable C.mulVecLin A.mulVecLin)
    (z : ℂ) (hz : A.charpoly.IsRoot z) :
    ∃ (i : p) (j : m),
      (channelTransferRatFunc A (C i) (fun k ↦ B k j)).denom.IsRoot z := by
  let q := commonChannelDenominator A B C
  have hden (i : p) (j : m) :
      (channelTransferRatFunc A (C i) (fun k ↦ B k j)).denom ∣ q :=
    channel_denom_dvd_commonChannelDenominator A B C i j
  have hq : aeval A.mulVecLin q = 0 :=
    aeval_eq_zero_of_channel_denoms A B C hctrl hobs q hden
  have hzlin : A.mulVecLin.charpoly.IsRoot z := by simpa using hz
  have hzq : q.IsRoot z := LinearMap.isRoot_of_aeval_eq_zero A.mulVecLin q hq z hzlin
  exact exists_channel_denom_root_of_common_root A B C z hzq

/-- For a controllable and observable complex realization, all scalar transfer
entries have left-half-plane poles exactly when the state spectrum is Hurwitz. -/
theorem all_channels_pole_stable_iff_charpoly_hurwitz_of_minimal
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix p n ℂ)
    (hctrl : LinearMap.IsControllable A.mulVecLin B.mulVecLin)
    (hobs : LinearMap.IsObservable C.mulVecLin A.mulVecLin) :
    (∀ (i : p) (j : m),
      RatFunc.IsPoleStable (channelTransferRatFunc A (C i) (fun k ↦ B k j))) ↔
      ∀ z : ℂ, A.charpoly.IsRoot z → z.re < 0 := by
  constructor
  · intro h z hz
    obtain ⟨i, j, hpole⟩ := exists_scalar_transfer_pole_of_minimal A B C
      hctrl hobs z hz
    exact h i j z hpole
  · intro h i j
    exact channelTransferRatFunc_isPoleStable A (C i) (fun k ↦ B k j) h

/-- For a controllable and observable real matrix realization, all entries of
the complexified rational transfer matrix are pole-stable exactly when the
complex roots of the real state characteristic polynomial lie in the open
left half-plane. -/
theorem real_all_channels_pole_stable_iff_charpoly_hurwitz_of_minimal
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix p n ℝ)
    (hctrl : LinearMap.IsControllable A.mulVecLin B.mulVecLin)
    (hobs : LinearMap.IsObservable C.mulVecLin A.mulVecLin) :
    (∀ (i : p) (j : m),
      RatFunc.IsPoleStable
        (channelTransferRatFunc (A.map (algebraMap ℝ ℂ))
          ((C.map (algebraMap ℝ ℂ)) i)
          (fun k ↦ (B.map (algebraMap ℝ ℂ)) k j))) ↔
      ∀ z : ℂ, (A.charpoly.map (algebraMap ℝ ℂ)).IsRoot z → z.re < 0 := by
  have hcctrl := (LinearMap.isControllable_complexify_iff A B).mp hctrl
  have hcobs := (LinearMap.isObservable_complexify_iff C A).mp hobs
  have h := all_channels_pole_stable_iff_charpoly_hurwitz_of_minimal
    (A.map (algebraMap ℝ ℂ)) (B.map (algebraMap ℝ ℂ))
    (C.map (algebraMap ℝ ℂ)) hcctrl hcobs
  simpa only [Matrix.charpoly_map] using h

end Matrix
