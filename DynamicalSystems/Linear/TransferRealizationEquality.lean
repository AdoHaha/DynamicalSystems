/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.TransferDenominatorRecurrence
public import DynamicalSystems.Linear.TransferPoleDomains

/-! # Transfer functions preserved by minimal realization

Matching all Markov parameters determines a scalar rational state-space
channel, even when the realizations have different state dimensions. Applying
this fact to the controllable-observable realization makes its transfer
function equal to the original channel before pole cancellation.

The proof uses the adjugate numerator recurrence. When the Markov parameters
match, the cross-multiplied numerator at the next power of the state map is
`X` times the previous one. Its degree is uniformly bounded, so this numerator
must vanish. No series expansion or analytic assumption is needed.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

private theorem channelTransferNumerator_natDegree_le_card
    (A : Matrix n n ℂ) (c b : n → ℂ) :
    (channelTransferNumerator A c b).natDegree ≤ Fintype.card n := by
  by_cases hn : Nonempty n
  · let hnonempty := hn
    exact (channelTransferNumerator_natDegree_lt A c b).le.trans
      (le_of_eq (charpoly_natDegree_eq_dim A))
  · have hempty : IsEmpty n := not_nonempty_iff.mp hn
    simp [channelTransferNumerator]

/-- Realizations with the same scalar Markov parameters have the same rational
transfer channel. Their state dimensions may differ, including dimension zero. -/
theorem channelTransferRatFunc_eq_of_markov_eq
    (A : Matrix n n ℂ) (c b : n → ℂ)
    (A' : Matrix m m ℂ) (c' b' : m → ℂ)
    (hmarkov : ∀ k : ℕ,
      ∑ i : n, c i * (((A ^ k) *ᵥ b) i) =
        ∑ i : m, c' i * (((A' ^ k) *ᵥ b') i)) :
    channelTransferRatFunc A c b = channelTransferRatFunc A' c' b' := by
  let P : ℕ → Polynomial ℂ := fun k ↦
    channelTransferNumerator A c ((A ^ k) *ᵥ b) * A'.charpoly -
      channelTransferNumerator A' c' ((A' ^ k) *ᵥ b') * A.charpoly
  have hrec (k : ℕ) : P (k + 1) = X * P k := by
    dsimp only [P]
    simp only [pow_succ', ← mulVec_mulVec]
    rw [channelTransferNumerator_mulVec_recurrence,
      channelTransferNumerator_mulVec_recurrence]
    have hc := congrArg (C : ℂ →+* Polynomial ℂ) (hmarkov k)
    simp only [map_sum] at hc
    rw [hc]
    ring
  have hpow (k : ℕ) : P k = X ^ k * P 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [hrec, ih, pow_succ']; ring
  have hbound (k : ℕ) : (P k).natDegree ≤ Fintype.card n + Fintype.card m := by
    dsimp only [P]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by
        rw [charpoly_natDegree_eq_dim]
        exact Nat.add_le_add_right (channelTransferNumerator_natDegree_le_card A c _) _)
    · exact natDegree_mul_le.trans (by
        rw [charpoly_natDegree_eq_dim, Nat.add_comm (Fintype.card n)]
        exact Nat.add_le_add_right (channelTransferNumerator_natDegree_le_card A' c' _) _)
  have hzero : P 0 = 0 := by
    by_contra hne
    have hb := hbound (Fintype.card n + Fintype.card m + 1)
    rw [hpow, natDegree_mul (pow_ne_zero _ X_ne_zero) hne, natDegree_X_pow] at hb
    omega
  have hcross : channelTransferNumerator A c b * A'.charpoly =
      channelTransferNumerator A' c' b' * A.charpoly := by
    simpa only [P, pow_zero, one_mulVec, sub_eq_zero] using hzero
  rw [channelTransferRatFunc, channelTransferRatFunc, RatFunc.mk_eq_div,
    RatFunc.mk_eq_div]
  apply (div_eq_div_iff
    (RatFunc.algebraMap_ne_zero A.charpoly_monic.ne_zero)
    (RatFunc.algebraMap_ne_zero A'.charpoly_monic.ne_zero)).mpr
  simpa only [map_mul] using
    congrArg (algebraMap (Polynomial ℂ) (RatFunc ℂ)) hcross

end Matrix

namespace LinearMap

variable {X U Y : Type*}
variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]
variable {n m ι κ : Type*}
variable [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable [Fintype ι] [DecidableEq ι] [Finite κ]

/-- Passing to the controllable-observable realization preserves each rational
transfer entry. The original and reduced state bases can be chosen independently;
the input and output bases are shared. -/
theorem controllableObservableRealization_channelTransferRatFunc_eq
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (C : X →ₗ[ℝ] Y)
    (bX : Module.Basis n ℝ X) (bU : Module.Basis ι ℝ U) (bY : Module.Basis κ ℝ Y)
    (bS : Module.Basis m ℝ
      ((reachableSubspace A B) ⧸ reachableIntersection A B C)) (i : κ) (j : ι) :
    let M := controllableObservableRealization A B C 0
    Matrix.channelTransferRatFunc
      ((toMatrix bS bS M.A).map (algebraMap ℝ ℂ))
      (fun k ↦ ((toMatrix bS bY M.C) i k : ℂ))
      (fun k ↦ ((toMatrix bU bS M.B) k j : ℂ)) =
    Matrix.channelTransferRatFunc
      ((toMatrix bX bX A).map (algebraMap ℝ ℂ))
      (fun k ↦ ((toMatrix bX bY C) i k : ℂ))
      (fun k ↦ ((toMatrix bU bX B) k j : ℂ)) := by
  dsimp only
  apply Matrix.channelTransferRatFunc_eq_of_markov_eq
  intro k
  have hmat := congrArg (toMatrix bU bY)
    (controllableObservableRealization_markov A B C 0 k)
  rw [toMatrix_comp bU bS bY, toMatrix_comp bU bS bS,
    toMatrix_comp bU bX bY, toMatrix_comp bU bX bX,
    ← toMatrix_pow bS, ← toMatrix_pow bX] at hmat
  have hcomplex := congrArg
    (fun T : Matrix κ ι ℝ ↦ T.map (algebraMap ℝ ℂ)) hmat
  simp only [Matrix.map_mul, Matrix.map_pow] at hcomplex
  simpa only [Matrix.mul_apply, Matrix.map_apply, Matrix.mulVec, dotProduct,
    Complex.coe_algebraMap] using
    congrFun (congrFun hcomplex i) j

end LinearMap

namespace LinearSystem

variable {X D Z n : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [Fintype n] [DecidableEq n]

/-- The minimal-realization pole predicate is exactly pole inclusion for the
original transfer matrix, expressed in any finite state basis and the canonical
input and output bases. Cancellation is handled by each rational entry. -/
theorem minimalRealizationAllChannelsPolesIn_iff_original_channels
    (Cg : Set ℂ) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (bX : Module.Basis n ℝ X) :
    MinimalRealizationAllChannelsPolesIn Cg A E H ↔
      ∀ (i : Fin (Module.finrank ℝ Z)) (j : Fin (Module.finrank ℝ D)),
        RatFunc.HasPolesIn Cg (Matrix.channelTransferRatFunc
          ((LinearMap.toMatrix bX bX A).map (algebraMap ℝ ℂ))
          (fun k ↦ ((LinearMap.toMatrix bX (Module.finBasis ℝ Z) H) i k : ℂ))
          (fun k ↦ ((LinearMap.toMatrix (Module.finBasis ℝ D) bX E) k j : ℂ))) := by
  unfold MinimalRealizationAllChannelsPolesIn
  simp only [LinearMap.controllableObservableRealization_channelTransferRatFunc_eq
    A E H bX (Module.finBasis ℝ D) (Module.finBasis ℝ Z)]

end LinearSystem
