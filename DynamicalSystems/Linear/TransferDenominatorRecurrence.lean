/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.TransferNumeratorDegree

/-! # Finite transfer-denominator recurrence

A common polynomial multiple of a scalar transfer channel's reduced
denominator annihilates the corresponding Markov sequence after evaluation
at the state matrix. The proof uses the adjugate recurrence and Cramer
numerator degree bound, not a formal Laurent-series expansion.
-/

@[expose] public section


set_option maxHeartbeats 1000000

open Polynomial

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem charmatrix_mulVec_C (A : Matrix n n ℂ) (b : n → ℂ) :
    (charmatrix A) *ᵥ (fun j ↦ C (b j)) =
      (fun i ↦ X * C (b i) - C ((A *ᵥ b) i)) := by
  funext i
  change ((Matrix.scalar n X - (C : ℂ →+* Polynomial ℂ).mapMatrix A) *ᵥ
      (fun j ↦ C (b j))) i = _
  rw [sub_mulVec]
  simp only [Pi.sub_apply]
  have hmap : ((C : ℂ →+* Polynomial ℂ).mapMatrix A *ᵥ
      (fun j ↦ C (b j))) i = C ((A *ᵥ b) i) := by
    simpa [Function.comp_def] using
      (RingHom.map_mulVec (C : ℂ →+* Polynomial ℂ) A b i).symm
  rw [hmap]
  simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem adjugate_charmatrix_mulVec_recurrence
    (A : Matrix n n ℂ) (b : n → ℂ) (i : n) :
    (∑ j : n, (adjugate (charmatrix A) i j) * C ((A *ᵥ b) j)) =
      X * (∑ j : n, (adjugate (charmatrix A) i j) * C (b j)) -
        A.charpoly * C (b i) := by
  let v : n → Polynomial ℂ := fun j ↦ C (b j)
  have h := congrArg (fun M : Matrix n n (Polynomial ℂ) ↦ M *ᵥ v)
    (adjugate_mul (charmatrix A))
  rw [← mulVec_mulVec, charmatrix_mulVec_C] at h
  have hi := congrFun h i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply,
    Pi.smul_apply, smul_eq_mul, one_mulVec] at hi
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    v] at hi
  simp_rw [mul_sub] at hi
  rw [Finset.sum_sub_distrib] at hi
  simp [Finset.sum_ite_eq', Matrix.mulVec, dotProduct, Matrix.charpoly] at hi ⊢
  simp_rw [← mul_assoc] at hi
  rw [← Finset.sum_mul] at hi
  rw [mul_comm (∑ x, A.charmatrix.adjugate i x * C (b x)) X] at hi
  linear_combination -hi

theorem channelTransferNumerator_mulVec_recurrence
    (A : Matrix n n ℂ) (c b : n → ℂ) :
    channelTransferNumerator A c (A *ᵥ b) =
      X * channelTransferNumerator A c b -
        A.charpoly * (∑ i : n, C (c i * b i)) := by
  unfold channelTransferNumerator
  simp_rw [mul_assoc]
  simp_rw [← Finset.mul_sum]
  simp_rw [adjugate_charmatrix_mulVec_recurrence]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
    map_sum, map_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    ring

theorem channelTransferNumerator_add (A : Matrix n n ℂ) (c b₁ b₂ : n → ℂ) :
    channelTransferNumerator A c (b₁ + b₂) =
      channelTransferNumerator A c b₁ + channelTransferNumerator A c b₂ := by
  simp [channelTransferNumerator, Pi.add_apply, map_add, mul_add,
    Finset.sum_add_distrib]

theorem channelTransferNumerator_smul (A : Matrix n n ℂ) (c b : n → ℂ) (a : ℂ) :
    channelTransferNumerator A c (a • b) =
      C a * channelTransferNumerator A c b := by
  simp [channelTransferNumerator, Pi.smul_apply, smul_eq_mul, map_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem charpoly_dvd_polynomial_mul_numerator_sub_aeval
    (A : Matrix n n ℂ) (c b : n → ℂ) (q : Polynomial ℂ) :
    A.charpoly ∣ q * channelTransferNumerator A c b -
      channelTransferNumerator A c ((aeval A q) *ᵥ b) := by
  induction q using Polynomial.induction_on with
  | C a =>
      simp [Algebra.algebraMap_eq_smul_one, channelTransferNumerator_smul,
        smul_mulVec]
  | add p q hp hq =>
      simp only [map_add, add_mul, add_mulVec, channelTransferNumerator_add]
      convert dvd_add hp hq using 1 <;> ring
  | monomial k a ih =>
      have hstep : C a * X ^ (k + 1) = X * (C a * X ^ k) := by ring
      rw [hstep]
      simp only [map_mul, aeval_X, ← mulVec_mulVec,
        channelTransferNumerator_mulVec_recurrence]
      simp only [map_mul, ← mulVec_mulVec] at ih
      rcases ih with ⟨t, ht⟩
      let v : n → ℂ := (aeval A (Polynomial.C a)) *ᵥ
        ((aeval A ((X : Polynomial ℂ) ^ k)) *ᵥ b)
      refine ⟨X * t + ∑ x : n, Polynomial.C (c x) * Polynomial.C (v x), ?_⟩
      dsimp only [v]
      linear_combination X * ht

theorem charpoly_dvd_polynomial_mul_numerator_of_denom_dvd
    (A : Matrix n n ℂ) (c b : n → ℂ) (q : Polynomial ℂ)
    (hden : (channelTransferRatFunc A c b).denom ∣ q) :
    A.charpoly ∣ q * channelTransferNumerator A c b := by
  obtain ⟨p, hp⟩ :=
    RatFunc.exists_polynomial_mul_eq_of_denom_dvd (channelTransferRatFunc A c b) q hden
  have hχ : (A.charpoly : RatFunc ℂ) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (A.charpoly_monic.ne_zero)
  have hfract : (q : RatFunc ℂ) *
      ((channelTransferNumerator A c b : RatFunc ℂ) / (A.charpoly : RatFunc ℂ)) = p := by
    simpa [channelTransferRatFunc, RatFunc.mk_eq_div] using hp
  have hcross : (q : RatFunc ℂ) * (channelTransferNumerator A c b : RatFunc ℂ) =
      (A.charpoly : RatFunc ℂ) * (p : RatFunc ℂ) := by
    rw [← mul_div_assoc] at hfract
    exact (div_eq_iff hχ).mp hfract |>.trans (mul_comm _ _)
  have hpoly : q * channelTransferNumerator A c b = A.charpoly * p := by
    apply RatFunc.algebraMap_injective ℂ
    simp only [map_mul]
    change (q : RatFunc ℂ) * (channelTransferNumerator A c b : RatFunc ℂ) =
      (A.charpoly : RatFunc ℂ) * (p : RatFunc ℂ)
    exact hcross
  exact ⟨p, hpoly⟩

theorem channelTransferNumerator_aeval_eq_zero_of_denom_dvd
    (A : Matrix n n ℂ) (c b : n → ℂ) (q : Polynomial ℂ)
    (hden : (channelTransferRatFunc A c b).denom ∣ q) :
    channelTransferNumerator A c ((aeval A q) *ᵥ b) = 0 := by
  have hmul := charpoly_dvd_polynomial_mul_numerator_of_denom_dvd A c b q hden
  have hmod := charpoly_dvd_polynomial_mul_numerator_sub_aeval A c b q
  have hdiv : A.charpoly ∣ channelTransferNumerator A c ((aeval A q) *ᵥ b) := by
    have h := dvd_sub hmul hmod
    convert h using 1 <;> ring
  exact channelTransferNumerator_eq_zero_of_charpoly_dvd A c _ hdiv

theorem channel_dot_eq_zero_of_two_numerators_zero
    (A : Matrix n n ℂ) (c b : n → ℂ)
    (h0 : channelTransferNumerator A c b = 0)
    (h1 : channelTransferNumerator A c (A *ᵥ b) = 0) :
    ∑ i : n, c i * b i = 0 := by
  have hχ : A.charpoly ≠ 0 := A.charpoly_monic.ne_zero
  have h := channelTransferNumerator_mulVec_recurrence A c b
  rw [h0, h1] at h
  simp only [mul_zero, zero_sub, zero_eq_neg] at h
  have hs : ∑ i : n, C (c i * b i) = 0 :=
    (mul_eq_zero.mp h).resolve_left hχ
  have he := congrArg (Polynomial.eval (0 : ℂ)) hs
  simpa only [Polynomial.eval_finsetSum, Polynomial.eval_C, Polynomial.eval_zero] using he

theorem charpoly_dvd_polynomial_mul_numerator_mulVec
    (A : Matrix n n ℂ) (c b : n → ℂ) (q : Polynomial ℂ)
    (hdiv : A.charpoly ∣ q * channelTransferNumerator A c b) :
    A.charpoly ∣ q * channelTransferNumerator A c (A *ᵥ b) := by
  obtain ⟨r, hr⟩ := hdiv
  refine ⟨X * r - q * (∑ i : n, C (c i * b i)), ?_⟩
  rw [channelTransferNumerator_mulVec_recurrence]
  linear_combination X * hr

theorem charpoly_dvd_polynomial_mul_numerator_pow_mulVec
    (A : Matrix n n ℂ) (c b : n → ℂ) (q : Polynomial ℂ)
    (hdiv : A.charpoly ∣ q * channelTransferNumerator A c b) (k : ℕ) :
    A.charpoly ∣ q * channelTransferNumerator A c ((A ^ k) *ᵥ b) := by
  induction k with
  | zero => simpa using hdiv
  | succ k ih =>
      simpa only [pow_succ', ← mulVec_mulVec] using
        charpoly_dvd_polynomial_mul_numerator_mulVec A c ((A ^ k) *ᵥ b) q ih

theorem channelTransferNumerator_aeval_pow_mulVec_eq_zero_of_denom_dvd
    (A : Matrix n n ℂ) (c b : n → ℂ) (q : Polynomial ℂ)
    (hden : (channelTransferRatFunc A c b).denom ∣ q) (k : ℕ) :
    channelTransferNumerator A c ((aeval A q) *ᵥ ((A ^ k) *ᵥ b)) = 0 := by
  have hbase := charpoly_dvd_polynomial_mul_numerator_of_denom_dvd A c b q hden
  have hmul := charpoly_dvd_polynomial_mul_numerator_pow_mulVec A c b q hbase k
  have hmod := charpoly_dvd_polynomial_mul_numerator_sub_aeval A c
    ((A ^ k) *ᵥ b) q
  have hdiv : A.charpoly ∣
      channelTransferNumerator A c ((aeval A q) *ᵥ ((A ^ k) *ᵥ b)) := by
    have h := dvd_sub hmul hmod
    convert h using 1 <;> ring
  exact channelTransferNumerator_eq_zero_of_charpoly_dvd A c _ hdiv

/-- A polynomial multiple of the reduced transfer denominator annihilates
every Markov parameter of that scalar input-output channel after evaluation
at the state matrix. -/
theorem channel_markov_annihilation_of_denom_dvd
    (A : Matrix n n ℂ) (c b : n → ℂ) (q : Polynomial ℂ)
    (hden : (channelTransferRatFunc A c b).denom ∣ q) (k : ℕ) :
    ∑ i : n, c i * (((aeval A q) *ᵥ ((A ^ k) *ᵥ b)) i) = 0 := by
  let v : n → ℂ := (aeval A q) *ᵥ ((A ^ k) *ᵥ b)
  have h0 : channelTransferNumerator A c v = 0 :=
    channelTransferNumerator_aeval_pow_mulVec_eq_zero_of_denom_dvd A c b q hden k
  have hcomm : A * aeval A q = aeval A q * A := by
    have h := congrArg (aeval A) (mul_comm (X : Polynomial ℂ) q)
    simpa only [map_mul, aeval_X] using h
  have hv : A *ᵥ v = (aeval A q) *ᵥ ((A ^ (k + 1)) *ᵥ b) := by
    dsimp only [v]
    rw [mulVec_mulVec, hcomm, ← mulVec_mulVec,
      mulVec_mulVec b A (A ^ k), ← pow_succ']
  have h1 : channelTransferNumerator A c (A *ᵥ v) = 0 := by
    rw [hv]
    exact channelTransferNumerator_aeval_pow_mulVec_eq_zero_of_denom_dvd A c b q hden
      (k + 1)
  exact channel_dot_eq_zero_of_two_numerators_zero A c v h0 h1

end Matrix
