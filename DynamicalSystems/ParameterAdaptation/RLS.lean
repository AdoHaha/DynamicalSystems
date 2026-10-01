/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.ParameterAdaptation.Basic

/-! # The recursive least squares parameter adaptation algorithm

This file formalizes the recursive least squares (RLS) parameter adaptation
algorithm (PAA) of I. D. Landau, R. Lozano, M'Saad and A. Karimi, *Adaptive
Control: Algorithms, Analysis and Applications*, 2nd ed., Springer 2011,
Chapter 3, eqs. 3.49–3.54.

The regressor is `φ : Fin n → ℝ`, the estimate is `θ̂`, the adaptation gain is
the matrix `F : Matrix (Fin n) (Fin n) ℝ`, and `d = φᵀFφ` is the scalar that
normalizes the algorithm.

## Main definitions

* `rlsGainUpdate F φ`: the rank-one RLS gain update
  `F⁺ = F − (F φ φᵀ F)/(1 + φᵀFφ)` (eq. 3.53).
* `rlsStep F φ eps0 θ̂`: one RLS step `θ̂⁺ = θ̂ + F φ ε⁰/(1 + φᵀFφ)`
  (eq. 3.49).

## Main results

* `aposterioriError_rlsStep`: the unconditional algebraic identity
  `ε = ε⁰ − ε⁰·φᵀFφ/(1 + φᵀFφ)` relating the a posteriori error of an RLS step
  to `ε⁰` (the general rearrangement underlying eq. 3.54).
* `rls_normalization`: eq. 3.54, the a posteriori–a priori error relation
  `ε = ε⁰/(1 + φᵀFφ)`.

## Note on the normalization lemma

The book's eq. 3.54 is stated for the a priori prediction error
`ε⁰ = y − θ̂ᵀφ` computed from the *same* measurement `y` that defines the a
posteriori error. The statement here therefore carries the explicit
compatibility hypothesis `eps0 = aprioriError y thetaHat phi` together with the
non-degeneracy hypothesis `1 + φᵀFφ ≠ 0` needed to clear the inverse
(`1 + φᵀFφ = 0` is excluded in the book by `F > 0`). Without them the literal
statement is false because `y` and `eps0` are independent and because the
identity genuinely fails at `1 + φᵀFφ = 0`; `aposterioriError_rlsStep` records
the unconditional algebraic form. -/

@[expose] public section

/-- The rank-one RLS gain update (eq. 3.53):
`F⁺ = F − (F φ φᵀ F)/(1 + φᵀFφ)`. The outer product `φ φᵀ` is
`Matrix.vecMulVec phi phi` and the scalar factor is `Ring.inverse`. -/
noncomputable def rlsGainUpdate {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  F - (1 + phi ⬝ᵥ (F.mulVec phi))⁻¹ • (F * Matrix.vecMulVec phi phi * F)

/-- One RLS step (eq. 3.49): `θ̂⁺ = θ̂ + F·φ·ε⁰/(1 + φᵀFφ)`. -/
noncomputable def rlsStep {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) (eps0 : ℝ)
    (thetaHat : Fin n → ℝ) : Fin n → ℝ :=
  paaStep F phi (eps0 * (1 + phi ⬝ᵥ (F.mulVec phi))⁻¹) thetaHat

/-- The unconditional algebraic identity underlying eq. 3.54: the a posteriori
error of an RLS step equals the a priori error minus
`ε⁰·(φᵀFφ)/(1 + φᵀFφ)`. -/
theorem aposterioriError_rlsStep {n : ℕ} (y eps0 : ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (phi thetaHat : Fin n → ℝ) :
    aposterioriError y (rlsStep F phi eps0 thetaHat) phi =
      aprioriError y thetaHat phi -
        eps0 * (1 + phi ⬝ᵥ (F.mulVec phi))⁻¹ * (phi ⬝ᵥ (F.mulVec phi)) := by
  rw [aposterioriError_eq_aprioriError_sub, rlsStep, paaStep, add_sub_cancel_left,
    Matrix.mulVec_smul, smul_dotProduct, dotProduct_comm (F.mulVec phi) phi]
  ring

/-- The a posteriori–a priori error relation for RLS (eq. 3.54):
`ε = ε⁰/(1 + φᵀFφ)`.

Here `eps0` is the a priori prediction error of the measurement `y`,
`eps0 = y − θ̂ᵀφ`; the hypothesis `heps` records that compatibility, and `hden`
records `1 + φᵀFφ ≠ 0` (automatic when `F` is positive definite). -/
theorem rls_normalization {n : ℕ} (y eps0 : ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (phi thetaHat : Fin n → ℝ) (heps : eps0 = aprioriError y thetaHat phi)
    (hden : 1 + phi ⬝ᵥ (F.mulVec phi) ≠ 0) :
    aposterioriError y (rlsStep F phi eps0 thetaHat) phi =
      eps0 * (1 + phi ⬝ᵥ (F.mulVec phi))⁻¹ := by
  rw [aposterioriError_rlsStep, ← heps]
  set d := phi ⬝ᵥ (F.mulVec phi) with hd
  set t := 1 + d with ht
  have hdt : d = t - 1 := by rw [ht]; ring
  have htne : t ≠ 0 := by rw [ht]; exact hden
  rw [hdt]
  have hexpand : eps0 * t⁻¹ * (t - 1) = eps0 * (1 - t⁻¹) := by
    rw [mul_sub, mul_one, mul_assoc, inv_mul_cancel₀ htne, mul_one]
    ring
  rw [hexpand]
  ring

/-- Eq. 3.54 in applied form, with the a priori error substituted directly:
for a nonzero `1 + φᵀFφ`, the a posteriori error of the RLS step driven by the
a priori error `ε⁰ = y − θ̂ᵀφ` is `ε⁰/(1 + φᵀFφ)`. -/
theorem rls_normalization_apriori {n : ℕ} (y : ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (phi thetaHat : Fin n → ℝ) (hden : 1 + phi ⬝ᵥ (F.mulVec phi) ≠ 0) :
    aposterioriError y (rlsStep F phi (aprioriError y thetaHat phi) thetaHat) phi =
      aprioriError y thetaHat phi * (1 + phi ⬝ᵥ (F.mulVec phi))⁻¹ :=
  rls_normalization y (aprioriError y thetaHat phi) F phi thetaHat rfl hden
