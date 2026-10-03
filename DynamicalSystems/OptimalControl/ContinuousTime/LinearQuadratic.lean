/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.LinearAlgebra.Matrix.Invertible
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Instances.Matrix
public import DynamicalSystems.Mathlib.LinearAlgebra.Matrix.Calculus

/-! # Continuous-time Linear Quadratic Regulator (LQR) and Riccati Equations

This file formalizes the continuous-time linear quadratic regulator (LQR), the finite-horizon
matrix Riccati differential equation (RDE), the continuous algebraic Riccati equation (CARE),
the optimal state-feedback gain, and the fundamental completion-of-squares cost identities.

The development follows Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional
Systems*, 2nd ed., 1998:
* Chapter 8 §8.2 (printed pp. 363–371), particularly Theorem 37 and Lemma 8.2.1 for the
  finite-horizon problem, the Riccati ODE, and the completion of squares;
* Chapter 8 §8.4 (printed pp. 380–390), particularly Lemma 8.4.1 and equations (8.53)–(8.56)
  for the continuous algebraic Riccati equation (CARE), optimal gain, and infinite-horizon cost.

## Conventions

1. **Riccati ODE (backward in time):** In finite-horizon optimal control with horizon `T` and
   terminal penalty `Qf`, the optimal cost-to-go matrix `P(t)` satisfies the backward Riccati ODE
   `-Ṗ(t) = Aᵀ P(t) + P(t) A + Q - P(t) B R⁻¹ Bᵀ P(t)` with terminal condition `P(T) = Qf`.
   In forward-time derivative formulation, `HasDerivAt P (-(Aᵀ P + P A + Q - P B R⁻¹ Bᵀ P)) t`.

2. **CARE:** The continuous algebraic Riccati equation is the steady-state equation
   `Aᵀ P + P A - P B R⁻¹ Bᵀ P + Q = 0`.

3. **Optimal Gain:** The continuous-time LQR optimal feedback gain is `K = R⁻¹ Bᵀ P`, with
   optimal control `u(t) = -K x(t)`.

4. **Completion of Squares:** For any trajectory `ẋ = A x + B u`, the time derivative of the
   quadratic value function along the flow satisfies:
   `d/dt (xᵀ P x) + xᵀ Q x + uᵀ R u = (u + K x)ᵀ R (u + K x)`.
   When `u = -K x`, the right-hand side vanishes, giving the integrated identity:
   `x₀ᵀ P(0) x₀ = ∫₀ᵀ (xᵀ Q x + uᵀ R u) dt + x(T)ᵀ P(T) x(T)`.

## Main definitions

* `riccatiODE`: the finite-horizon matrix Riccati differential equation backward in time.
* `care`: the continuous algebraic Riccati equation.
* `continuousLQRGain`: the continuous LQR optimal state-feedback gain `K = R⁻¹ Bᵀ P`.

## Main results

* `care_lyapunov`: CARE implies the closed-loop Lyapunov matrix equality
  `(A - B K)ᵀ P + P (A - B K) = -(Q + Kᵀ R K)`.
* `quadForm_closed_loop_deriv_algebraic`: pointwise derivative of the quadratic value form
  along the optimal closed loop, in algebraic form (before substituting CARE).
* `quadForm_control_cost_algebraic`: the optimal control cost equality
  `uᵀ R u = xᵀ (P B R⁻¹ Bᵀ P) x`.
* `quadForm_closed_loop_deriv_care`: pointwise derivative of the quadratic value form along
  the optimal closed loop under CARE, i.e. `d/dt (xᵀ P x) = -(xᵀ Q x + uᵀ R u)`.
* `completion_of_squares_algebraic`: pointwise algebraic completion-of-squares expansion.
* `lqrContinuous_completionOfSquares`: integrated cost identity for the Riccati ODE.
* `lqrContinuous_completionOfSquares_care`: integrated cost identity for CARE.
* `lqrContinuous_completionOfSquares_infinite`: infinite-horizon limit of the LQR cost.
-/

@[expose] public section

open Matrix MeasureTheory

variable {n m : ℕ}
variable (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
variable (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
variable (P : Matrix (Fin n) (Fin n) ℝ)

/-! ### Definitions: Riccati ODE, CARE, and Optimal Gain -/

/-- The ODE part of the backward Riccati differential equation (RDE) for the finite-horizon
matrix Riccati equation: the matrix function `P` satisfies the differential relation
`-Ṗ = Aᵀ P + P A + Q - P B R⁻¹ Bᵀ P`, expressed in forward time as the pointwise derivative
`HasDerivAt P (-(Aᵀ * P t + P t * A + Q - P t * B * R⁻¹ * Bᵀ * P t)) t` for every `t`.
The terminal condition `P T = Qf` is not currently formalized. The ODE is stated on the whole
real line (a global horizon) rather than on a fixed interval `[σ, τ]`.
Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.2, Theorem 37, printed p. 364. -/
def riccatiODE (P : ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ t, HasDerivAt P (-(Aᵀ * P t + P t * A + Q - P t * B * R⁻¹ * Bᵀ * P t)) t

/-- The continuous algebraic Riccati equation (CARE).
Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.4, Lemma 8.4.1, printed p. 381. -/
def care : Prop :=
  Aᵀ * P + P * A - P * B * R⁻¹ * Bᵀ * P + Q = 0

/-- The continuous-time LQR optimal state-feedback gain `K = R⁻¹ Bᵀ P`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.2, eq. (8.27), printed p. 364;
§8.4, printed p. 382). -/
noncomputable def continuousLQRGain (B : Matrix (Fin n) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) [Invertible R] (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  ⅟R * Bᵀ * P

variable [Invertible R]

/-- Alternative form of `continuousLQRGain` using matrix inverse `R⁻¹`. -/
lemma continuousLQRGain_eq_inv :
    continuousLQRGain B R P = R⁻¹ * Bᵀ * P := by
  unfold continuousLQRGain
  rw [invOf_eq_nonsing_inv]

/-! ### Quadratic Form and Matrix Calculus Helpers -/

/-- Symmetry of bilinear pairing against a symmetric matrix. -/
theorem quadForm_dotProduct_symm {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : Mᵀ = M)
    (x y : Fin k → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  calc x ⬝ᵥ (M *ᵥ y)
    _ = x ᵥ* M ⬝ᵥ y := by rw [dotProduct_mulVec]
    _ = y ⬝ᵥ (x ᵥ* M) := by rw [dotProduct_comm]
    _ = y ⬝ᵥ (Mᵀ *ᵥ x) := by rw [mulVec_transpose]
    _ = y ⬝ᵥ (M *ᵥ x) := by rw [hM]

/-- Adjoint movement for matrix vector multiplication under dot product. -/
theorem dotProduct_mulVec_comp {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℝ)
    (x : Fin k → ℝ) (y : Fin l → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (Mᵀ *ᵥ x) := by
  calc x ⬝ᵥ (M *ᵥ y)
    _ = x ᵥ* M ⬝ᵥ y := by rw [dotProduct_mulVec]
    _ = y ⬝ᵥ (x ᵥ* M) := by rw [dotProduct_comm]
    _ = y ⬝ᵥ (Mᵀ *ᵥ x) := by rw [mulVec_transpose]

/-- Derivative of a quadratic form with a constant matrix along a trajectory. -/
theorem hasDerivAt_quadForm_const
    {t : ℝ} (P : Matrix (Fin n) (Fin n) ℝ)
    {x : ℝ → Fin n → ℝ} {x' : Fin n → ℝ}
    (hx : ∀ j, HasDerivAt (fun s ↦ x s j) (x' j) t) :
    HasDerivAt (fun s ↦ x s ⬝ᵥ (P *ᵥ x s))
      (x' ⬝ᵥ (P *ᵥ x t) + x t ⬝ᵥ (P *ᵥ x')) t := by
  have hmul : ∀ i, HasDerivAt (fun s ↦ (P *ᵥ x s) i) ((P *ᵥ x') i) t :=
    fun i ↦ hasDerivAt_mulVec P hx i
  exact hasDerivAt_dotProduct hx hmul

/-- Derivative of a quadratic form with a time-varying matrix along a trajectory. -/
theorem hasDerivAt_quadForm_timeVarying
    {t : ℝ} {P : ℝ → Matrix (Fin n) (Fin n) ℝ} {P' : Matrix (Fin n) (Fin n) ℝ}
    {x : ℝ → Fin n → ℝ} {x' : Fin n → ℝ}
    (hP : ∀ i j, HasDerivAt (fun s ↦ P s i j) (P' i j) t)
    (hx : ∀ j, HasDerivAt (fun s ↦ x s j) (x' j) t) :
    HasDerivAt (fun s ↦ x s ⬝ᵥ (P s *ᵥ x s))
      (x' ⬝ᵥ (P t *ᵥ x t) + x t ⬝ᵥ (P' *ᵥ x t) + x t ⬝ᵥ (P t *ᵥ x')) t := by
  have hmul : ∀ i, HasDerivAt (fun s ↦ (P s *ᵥ x s) i) ((P' *ᵥ x t + P t *ᵥ x') i) t := by
    intro i
    change HasDerivAt (fun s ↦ ∑ j, P s i j * x s j) ((P' *ᵥ x t + P t *ᵥ x') i) t
    have hpi : (fun s ↦ ∑ j, P s i j * x s j) = (∑ j, (fun s ↦ P s i j * x s j)) := by
      funext s
      simp only [Finset.sum_apply]
    rw [hpi]
    have h := HasDerivAt.sum (u := Finset.univ) (fun j _ ↦ (hP i j).mul (hx j))
    have heq : (∑ j : Fin n, (P' i j * x t j + P t i j * x' j)) = (P' *ᵥ x t + P t *ᵥ x') i := by
      rw [Finset.sum_add_distrib]
      rfl
    rwa [heq] at h
  have hdot := hasDerivAt_dotProduct hx hmul
  rw [dotProduct_add] at hdot
  rw [add_assoc]
  exact hdot

/-! ### Closed-Loop Algebraic Identities and Completion of Squares -/

/-- CARE implies the closed-loop Lyapunov matrix equality:
`(A - B * K)ᵀ * P + P * (A - B * K) = -(Q + Kᵀ * R * K)`
where `K = continuousLQRGain B R P`.
Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.4 (printed pp. 380–383). -/
theorem care_lyapunov
    (hCARE : care A B Q R P)
    (hP_symm : Pᵀ = P)
    (hR_symm : Rᵀ = R) :
    let K := continuousLQRGain B R P
    (A - B * K)ᵀ * P + P * (A - B * K) = -(Q + Kᵀ * R * K) := by
  intro K
  have hinv_symm : (⅟R : Matrix (Fin m) (Fin m) ℝ)ᵀ = ⅟R := by
    rw [invOf_eq_nonsing_inv, transpose_nonsing_inv, hR_symm, ← invOf_eq_nonsing_inv]
  have hK_eq : K = ⅟R * Bᵀ * P := rfl
  have hKt : Kᵀ = P * B * ⅟R := by
    rw [hK_eq]
    simp only [transpose_mul, transpose_transpose, hP_symm, hinv_symm]
    simp only [Matrix.mul_assoc]
  have hKTRK : Kᵀ * R * K = P * B * ⅟R * Bᵀ * P := by
    calc Kᵀ * R * K
      _ = (P * B * ⅟R) * R * (⅟R * Bᵀ * P) := by rw [hKt, hK_eq]
      _ = (P * B * (⅟R * R)) * (⅟R * Bᵀ * P) := by simp only [Matrix.mul_assoc]
      _ = (P * B * (1 : Matrix (Fin m) (Fin m) ℝ)) * (⅟R * Bᵀ * P) := by rw [invOf_mul_self R]
      _ = P * B * ⅟R * Bᵀ * P := by
        rw [Matrix.mul_one]
        simp only [Matrix.mul_assoc]
  have hcl : (A - B * K)ᵀ * P + P * (A - B * K) =
      Aᵀ * P + P * A - (P * B * ⅟R * Bᵀ * P + P * B * ⅟R * Bᵀ * P) := by
    simp only [transpose_sub, transpose_mul, sub_mul, Matrix.mul_sub]
    rw [hKt, hK_eq]
    simp only [Matrix.mul_assoc]
    abel
  rw [hcl, hKTRK]
  have hCARE_sub : Aᵀ * P + P * A = P * B * ⅟R * Bᵀ * P - Q := by
    have hcare_eq : Aᵀ * P + P * A - P * B * R⁻¹ * Bᵀ * P + Q = 0 := hCARE
    rw [← invOf_eq_nonsing_inv] at hcare_eq
    have h1 : Aᵀ * P + P * A - P * B * ⅟R * Bᵀ * P = -Q := by
      exact add_eq_zero_iff_eq_neg.mp hcare_eq
    have h2 : Aᵀ * P + P * A = -Q + P * B * ⅟R * Bᵀ * P := by
      exact sub_eq_iff_eq_add.mp h1
    rw [h2]
    abel
  rw [hCARE_sub]
  abel

/-- Cross terms in the derivative of `x ⬝ᵥ (P *ᵥ x)` along the closed loop. -/
theorem quadForm_closed_loop_deriv_algebraic
    (hP_symm : Pᵀ = P) (hR_symm : Rᵀ = R)
    (x : Fin n → ℝ) (u : Fin m → ℝ)
    (hu : u = -(continuousLQRGain B R P) *ᵥ x) :
    (A *ᵥ x + B *ᵥ u) ⬝ᵥ (P *ᵥ x) + x ⬝ᵥ (P *ᵥ (A *ᵥ x + B *ᵥ u)) =
      x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) - 2 * (x ⬝ᵥ ((P * B * ⅟R * Bᵀ * P) *ᵥ x)) := by
  have hK_eq : continuousLQRGain B R P = ⅟R * Bᵀ * P := rfl
  have hinv_symm : (⅟R : Matrix (Fin m) (Fin m) ℝ)ᵀ = ⅟R := by
    rw [invOf_eq_nonsing_inv, transpose_nonsing_inv, hR_symm, ← invOf_eq_nonsing_inv]
  have h1 : (A *ᵥ x + B *ᵥ u) ⬝ᵥ (P *ᵥ x) = (A *ᵥ x) ⬝ᵥ (P *ᵥ x) + (B *ᵥ u) ⬝ᵥ (P *ᵥ x) := by
    rw [add_dotProduct]
  have h2 : x ⬝ᵥ (P *ᵥ (A *ᵥ x + B *ᵥ u)) = x ⬝ᵥ (P *ᵥ (A *ᵥ x)) + x ⬝ᵥ (P *ᵥ (B *ᵥ u)) := by
    rw [Matrix.mulVec_add, dotProduct_add]
  have hP_symm2 : x ⬝ᵥ (P *ᵥ (B *ᵥ u)) = (B *ᵥ u) ⬝ᵥ (P *ᵥ x) :=
    quadForm_dotProduct_symm P hP_symm x (B *ᵥ u)
  have hA : (A *ᵥ x) ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ ((Aᵀ * P) *ᵥ x) := by
    rw [dotProduct_comm (A *ᵥ x) (P *ᵥ x), dotProduct_mulVec_comp A (P *ᵥ x) x,
      Matrix.mulVec_mulVec]
  have hPA : x ⬝ᵥ (P *ᵥ (A *ᵥ x)) = x ⬝ᵥ ((P * A) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec]
  have hB : (B *ᵥ u) ⬝ᵥ (P *ᵥ x) = u ⬝ᵥ ((Bᵀ * P) *ᵥ x) := by
    rw [dotProduct_comm (B *ᵥ u) (P *ᵥ x), dotProduct_mulVec_comp B (P *ᵥ x) u,
      Matrix.mulVec_mulVec]
  have hu_sub : u ⬝ᵥ ((Bᵀ * P) *ᵥ x) = -(x ⬝ᵥ ((P * B * ⅟R * Bᵀ * P) *ᵥ x)) := by
    rw [hu, hK_eq]
    rw [Matrix.neg_mulVec, neg_dotProduct]
    congr 1
    calc ((⅟R * Bᵀ * P) *ᵥ x) ⬝ᵥ ((Bᵀ * P) *ᵥ x)
      _ = ((Bᵀ * P) *ᵥ x) ⬝ᵥ ((⅟R * Bᵀ * P) *ᵥ x) := by rw [dotProduct_comm]
      _ = x ⬝ᵥ ((⅟R * Bᵀ * P)ᵀ *ᵥ ((Bᵀ * P) *ᵥ x)) := by
        rw [dotProduct_mulVec_comp (⅟R * Bᵀ * P) ((Bᵀ * P) *ᵥ x) x]
      _ = x ⬝ᵥ ((P * B * ⅟R) *ᵥ ((Bᵀ * P) *ᵥ x)) := by
        have htrans : (⅟R * Bᵀ * P)ᵀ = P * B * ⅟R := by
          simp only [transpose_mul, transpose_transpose, hP_symm, hinv_symm]
          simp only [Matrix.mul_assoc]
        rw [htrans]
      _ = x ⬝ᵥ ((P * B * ⅟R * (Bᵀ * P)) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ ((P * B * ⅟R * Bᵀ * P) *ᵥ x) := by
        simp only [Matrix.mul_assoc]
  rw [h1, h2, hP_symm2, hA, hPA, hB, hu_sub]
  have hAPA : x ⬝ᵥ ((Aᵀ * P) *ᵥ x) + x ⬝ᵥ ((P * A) *ᵥ x) = x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x) := by
    rw [← dotProduct_add, ← Matrix.add_mulVec]
  linarith

/-- Optimal control cost equality: `uᵀ R u = xᵀ (P B R⁻¹ Bᵀ P) x`. -/
theorem quadForm_control_cost_algebraic
    (hP_symm : Pᵀ = P) (hR_symm : Rᵀ = R)
    (x : Fin n → ℝ) (u : Fin m → ℝ)
    (hu : u = -(continuousLQRGain B R P) *ᵥ x) :
    u ⬝ᵥ (R *ᵥ u) = x ⬝ᵥ ((P * B * ⅟R * Bᵀ * P) *ᵥ x) := by
  have hK_eq : continuousLQRGain B R P = ⅟R * Bᵀ * P := rfl
  have hinv_symm : (⅟R : Matrix (Fin m) (Fin m) ℝ)ᵀ = ⅟R := by
    rw [invOf_eq_nonsing_inv, transpose_nonsing_inv, hR_symm, ← invOf_eq_nonsing_inv]
  rw [hu, hK_eq]
  rw [Matrix.neg_mulVec, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  have hRK : R * (⅟R * Bᵀ * P) = (Bᵀ * P) := by
    calc R * (⅟R * Bᵀ * P)
      _ = (R * ⅟R) * (Bᵀ * P) := by simp only [Matrix.mul_assoc]
      _ = (1 : Matrix (Fin m) (Fin m) ℝ) * (Bᵀ * P) := by rw [mul_invOf_self R]
      _ = Bᵀ * P := by rw [Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, hRK]
  calc ((⅟R * Bᵀ * P) *ᵥ x) ⬝ᵥ ((Bᵀ * P) *ᵥ x)
    _ = ((Bᵀ * P) *ᵥ x) ⬝ᵥ ((⅟R * Bᵀ * P) *ᵥ x) := by rw [dotProduct_comm]
    _ = x ⬝ᵥ ((⅟R * Bᵀ * P)ᵀ *ᵥ ((Bᵀ * P) *ᵥ x)) := by
      rw [dotProduct_mulVec_comp (⅟R * Bᵀ * P) ((Bᵀ * P) *ᵥ x) x]
    _ = x ⬝ᵥ ((P * B * ⅟R) *ᵥ ((Bᵀ * P) *ᵥ x)) := by
      have htrans : (⅟R * Bᵀ * P)ᵀ = P * B * ⅟R := by
        simp only [transpose_mul, transpose_transpose, hP_symm, hinv_symm]
        simp only [Matrix.mul_assoc]
      rw [htrans]
    _ = x ⬝ᵥ ((P * B * ⅟R * (Bᵀ * P)) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ ((P * B * ⅟R * Bᵀ * P) *ᵥ x) := by
      simp only [Matrix.mul_assoc]

/-- Pointwise time derivative of `x(t)ᵀ P x(t)` under CARE along the optimal closed loop:
`d/dt (xᵀ P x) = -(xᵀ Q x + uᵀ R u)`.
Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.4, printed p. 383. -/
theorem quadForm_closed_loop_deriv_care
    (hCARE : care A B Q R P) (hP_symm : Pᵀ = P) (hR_symm : Rᵀ = R)
    (x : Fin n → ℝ) (u : Fin m → ℝ)
    (hu : u = -(continuousLQRGain B R P) *ᵥ x) :
    (A *ᵥ x + B *ᵥ u) ⬝ᵥ (P *ᵥ x) + x ⬝ᵥ (P *ᵥ (A *ᵥ x + B *ᵥ u)) =
      -(x ⬝ᵥ (Q *ᵥ x) + u ⬝ᵥ (R *ᵥ u)) := by
  have h1 := quadForm_closed_loop_deriv_algebraic A B R P hP_symm hR_symm x u hu
  have h2 := quadForm_control_cost_algebraic B R P hP_symm hR_symm x u hu
  have hcare_eq : Aᵀ * P + P * A - P * B * R⁻¹ * Bᵀ * P + Q = 0 := hCARE
  rw [← invOf_eq_nonsing_inv] at hcare_eq
  have hCARE_sub : Aᵀ * P + P * A = P * B * ⅟R * Bᵀ * P - Q := by
    have h_neg : Aᵀ * P + P * A - P * B * ⅟R * Bᵀ * P = -Q := add_eq_zero_iff_eq_neg.mp hcare_eq
    have h3 : Aᵀ * P + P * A = -Q + P * B * ⅟R * Bᵀ * P := sub_eq_iff_eq_add.mp h_neg
    rw [h3]
    abel
  have hsub : (P * B * ⅟R * Bᵀ * P - Q) *ᵥ x =
      (P * B * ⅟R * Bᵀ * P) *ᵥ x - Q *ᵥ x := by
    rw [Matrix.sub_mulVec]
  rw [h1, h2, hCARE_sub, hsub, dotProduct_sub]
  linarith

/-- Pointwise algebraic completion of squares for continuous-time LQR with arbitrary input `w`:
`(w + K x)ᵀ R (w + K x) = wᵀ R w + 2 (B w)ᵀ P x + xᵀ (P B R⁻¹ Bᵀ P) x`.
Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.2, Lemma 8.2.1, printed p. 365. -/
theorem completion_of_squares_algebraic
    (hP_symm : Pᵀ = P) (hR_symm : Rᵀ = R)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    let K := continuousLQRGain B R P
    (w + K *ᵥ x) ⬝ᵥ (R *ᵥ (w + K *ᵥ x)) =
      w ⬝ᵥ (R *ᵥ w) + 2 * (w ⬝ᵥ ((Bᵀ * P) *ᵥ x)) +
      x ⬝ᵥ ((P * B * ⅟R * Bᵀ * P) *ᵥ x) := by
  intro K
  have hK_eq : K = ⅟R * Bᵀ * P := rfl
  have hinv_symm : (⅟R : Matrix (Fin m) (Fin m) ℝ)ᵀ = ⅟R := by
    rw [invOf_eq_nonsing_inv, transpose_nonsing_inv, hR_symm, ← invOf_eq_nonsing_inv]
  have h1 : (w + K *ᵥ x) ⬝ᵥ (R *ᵥ (w + K *ᵥ x)) =
      w ⬝ᵥ (R *ᵥ w) + w ⬝ᵥ (R *ᵥ (K *ᵥ x)) + (K *ᵥ x) ⬝ᵥ (R *ᵥ w) +
      (K *ᵥ x) ⬝ᵥ (R *ᵥ (K *ᵥ x)) := by
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
    ring
  have hRK : R * K = Bᵀ * P := by
    rw [hK_eq]
    calc R * (⅟R * Bᵀ * P)
      _ = (R * ⅟R) * (Bᵀ * P) := by simp only [Matrix.mul_assoc]
      _ = (1 : Matrix (Fin m) (Fin m) ℝ) * (Bᵀ * P) := by rw [mul_invOf_self R]
      _ = Bᵀ * P := by rw [Matrix.one_mul]
  have hRKx : R *ᵥ (K *ᵥ x) = (Bᵀ * P) *ᵥ x := by
    rw [mulVec_mulVec, hRK]
  have hsymm : (K *ᵥ x) ⬝ᵥ (R *ᵥ w) = w ⬝ᵥ ((Bᵀ * P) *ᵥ x) := by
    rw [quadForm_dotProduct_symm R hR_symm (K *ᵥ x) w, hRKx]
  have hKxRKx : (K *ᵥ x) ⬝ᵥ (R *ᵥ (K *ᵥ x)) = x ⬝ᵥ ((P * B * ⅟R * Bᵀ * P) *ᵥ x) := by
    rw [hRKx, hK_eq]
    calc ((⅟R * Bᵀ * P) *ᵥ x) ⬝ᵥ ((Bᵀ * P) *ᵥ x)
      _ = ((Bᵀ * P) *ᵥ x) ⬝ᵥ ((⅟R * Bᵀ * P) *ᵥ x) := by rw [dotProduct_comm]
      _ = x ⬝ᵥ ((⅟R * Bᵀ * P)ᵀ *ᵥ ((Bᵀ * P) *ᵥ x)) := by
        rw [dotProduct_mulVec_comp (⅟R * Bᵀ * P) ((Bᵀ * P) *ᵥ x) x]
      _ = x ⬝ᵥ ((P * B * ⅟R) *ᵥ ((Bᵀ * P) *ᵥ x)) := by
        have htrans : (⅟R * Bᵀ * P)ᵀ = P * B * ⅟R := by
          simp only [transpose_mul, transpose_transpose, hP_symm, hinv_symm]
          simp only [Matrix.mul_assoc]
        rw [htrans]
      _ = x ⬝ᵥ ((P * B * ⅟R * (Bᵀ * P)) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ ((P * B * ⅟R * Bᵀ * P) *ᵥ x) := by
        simp only [Matrix.mul_assoc]
  rw [h1, hsymm, hKxRKx, hRKx]
  ring

/-! ### Integrated Completion of Squares Identities -/

/-- The completion-of-squares identity for continuous-time finite-horizon LQR under CARE:
along the closed-loop optimal trajectory `x₀ᵀ P x₀ = ∫₀ᵀ (xᵀ Q x + uᵀ R u) dt + x(T)ᵀ P x(T)`.
Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.4, Lemma 8.4.1,
printed pp. 381–383. -/
theorem lqrContinuous_completionOfSquares_care
    {T : ℝ} (hT : 0 ≤ T)
    (hP_symm : Pᵀ = P) (hR_symm : Rᵀ = R)
    (hCARE : care A B Q R P)
    (x : ℝ → Fin n → ℝ) (u : ℝ → Fin m → ℝ)
    (hx_traj : ∀ t ∈ Set.Icc 0 T, ∀ j, HasDerivAt (fun s ↦ x s j) ((A *ᵥ x t + B *ᵥ u t) j) t)
    (hu : ∀ t ∈ Set.Icc 0 T, u t = -(continuousLQRGain B R P) *ᵥ x t)
    (h_int : IntervalIntegrable (fun t ↦ x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t)) volume 0 T) :
    x 0 ⬝ᵥ (P *ᵥ x 0) =
      (∫ t in 0..T, (x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t))) + x T ⬝ᵥ (P *ᵥ x T) := by
  have hderiv : ∀ t ∈ Set.uIcc 0 T,
      HasDerivAt (fun s ↦ x s ⬝ᵥ (P *ᵥ x s))
        (-(x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t))) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have hd := hasDerivAt_quadForm_const P (hx_traj t ht)
    have halg := quadForm_closed_loop_deriv_care A B Q R P hCARE hP_symm hR_symm
      (x t) (u t) (hu t ht)
    rwa [halg] at hd
  have h_int_neg : IntervalIntegrable
      (fun t ↦ -(x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t))) volume 0 T :=
    h_int.neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv h_int_neg
  rw [intervalIntegral.integral_neg] at hFTC
  linarith

/-- The completion-of-squares identity for continuous-time finite-horizon LQR under the
matrix Riccati ODE: the cost along the closed-loop optimal trajectory satisfies
`x₀ᵀ P(0) x₀ = ∫₀ᵀ (xᵀ Q x + uᵀ R u) dt + x(T)ᵀ P(T) x(T)`.
Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.2, Lemma 8.2.1 and
Theorem 37, printed pp. 364–366. -/
theorem lqrContinuous_completionOfSquares
    (P : ℝ → Matrix (Fin n) (Fin n) ℝ)
    {T : ℝ} (hT : 0 ≤ T)
    (hP_symm : ∀ t, (P t)ᵀ = P t) (hR_symm : Rᵀ = R)
    (hODE : riccatiODE A B Q R P)
    (x : ℝ → Fin n → ℝ) (u : ℝ → Fin m → ℝ)
    (hx_traj : ∀ t ∈ Set.Icc 0 T, ∀ j, HasDerivAt (fun s ↦ x s j) ((A *ᵥ x t + B *ᵥ u t) j) t)
    (hu : ∀ t ∈ Set.Icc 0 T, u t = -(continuousLQRGain B R (P t)) *ᵥ x t)
    (h_int : IntervalIntegrable (fun t ↦ x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t)) volume 0 T) :
    x 0 ⬝ᵥ (P 0 *ᵥ x 0) =
      (∫ t in 0..T, (x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t))) + x T ⬝ᵥ (P T *ᵥ x T) := by
  have hderiv : ∀ t ∈ Set.uIcc 0 T,
      HasDerivAt (fun s ↦ x s ⬝ᵥ (P s *ᵥ x s))
        (-(x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t))) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have hODE_t := hODE t
    have hP_entries : ∀ i j, HasDerivAt (fun s ↦ P s i j)
        ((-(Aᵀ * P t + P t * A + Q - P t * B * R⁻¹ * Bᵀ * P t)) i j) t := by
      intro i j
      have h1 : HasDerivAt (fun s i ↦ P s i)
          (-(Aᵀ * P t + P t * A + Q - P t * B * R⁻¹ * Bᵀ * P t)) t := hODE_t
      have h2 := hasDerivAt_pi.mp h1 i
      exact hasDerivAt_pi.mp h2 j
    have hd := hasDerivAt_quadForm_timeVarying hP_entries (hx_traj t ht)
    have halg1 := quadForm_closed_loop_deriv_algebraic A B R (P t) (hP_symm t) hR_symm
      (x t) (u t) (hu t ht)
    have halg2 := quadForm_control_cost_algebraic B R (P t) (hP_symm t) hR_symm
      (x t) (u t) (hu t ht)
    have hsum : (A *ᵥ x t + B *ᵥ u t) ⬝ᵥ (P t *ᵥ x t) +
        x t ⬝ᵥ ((-(Aᵀ * P t + P t * A + Q - P t * B * R⁻¹ * Bᵀ * P t)) *ᵥ x t) +
        x t ⬝ᵥ (P t *ᵥ (A *ᵥ x t + B *ᵥ u t)) =
        -(x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t)) := by
      rw [← invOf_eq_nonsing_inv]
      have hneg_mat : (-(Aᵀ * P t + P t * A + Q - P t * B * ⅟R * Bᵀ * P t)) *ᵥ x t =
          - ((Aᵀ * P t + P t * A + Q - P t * B * ⅟R * Bᵀ * P t) *ᵥ x t) := by
        rw [Matrix.neg_mulVec]
      rw [hneg_mat, dotProduct_neg]
      have hdecomp : (Aᵀ * P t + P t * A + Q - P t * B * ⅟R * Bᵀ * P t) *ᵥ x t =
          ((Aᵀ * P t + P t * A) *ᵥ x t + Q *ᵥ x t) - (P t * B * ⅟R * Bᵀ * P t) *ᵥ x t := by
        rw [Matrix.sub_mulVec, Matrix.add_mulVec]
      rw [hdecomp, dotProduct_sub, dotProduct_add]
      have hsplit : (A *ᵥ x t + B *ᵥ u t) ⬝ᵥ (P t *ᵥ x t) +
          -(x t ⬝ᵥ (Aᵀ * P t + P t * A) *ᵥ x t + x t ⬝ᵥ Q *ᵥ x t -
            x t ⬝ᵥ (P t * B * ⅟R * Bᵀ * P t) *ᵥ x t) +
          x t ⬝ᵥ (P t *ᵥ (A *ᵥ x t + B *ᵥ u t)) =
          ((A *ᵥ x t + B *ᵥ u t) ⬝ᵥ (P t *ᵥ x t) + x t ⬝ᵥ (P t *ᵥ (A *ᵥ x t + B *ᵥ u t))) -
          x t ⬝ᵥ (Aᵀ * P t + P t * A) *ᵥ x t - x t ⬝ᵥ Q *ᵥ x t +
          x t ⬝ᵥ (P t * B * ⅟R * Bᵀ * P t) *ᵥ x t := by ring
      rw [hsplit, halg1, halg2]
      ring
    rwa [hsum] at hd
  have h_int_neg : IntervalIntegrable
      (fun t ↦ -(x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t))) volume 0 T :=
    h_int.neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv h_int_neg
  rw [intervalIntegral.integral_neg] at hFTC
  linarith

/-- The infinite-horizon LQR cost identity under CARE: if the closed-loop state converges
to zero in the quadratic form `x(t)ᵀ P x(t) → 0` as `t → ∞`, the running cost integral
`∫₀^T (xᵀ Q x + uᵀ R u) dt` tends to the initial value `x₀ᵀ P x₀` as `T → ∞`.
Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.4, eq. (8.53)–(8.56),
printed pp. 380–383. -/
theorem lqrContinuous_completionOfSquares_infinite
    (hP_symm : Pᵀ = P) (hR_symm : Rᵀ = R)
    (hCARE : care A B Q R P)
    (x : ℝ → Fin n → ℝ) (u : ℝ → Fin m → ℝ)
    (hx_traj : ∀ t ≥ 0, ∀ j, HasDerivAt (fun s ↦ x s j) ((A *ᵥ x t + B *ᵥ u t) j) t)
    (hu : ∀ t ≥ 0, u t = -(continuousLQRGain B R P) *ᵥ x t)
    (h_int : ∀ T ≥ 0, IntervalIntegrable (fun t ↦ x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t)) volume 0 T)
    (h_conv : Filter.Tendsto (fun T ↦ x T ⬝ᵥ (P *ᵥ x T)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun T ↦ ∫ t in 0..T, (x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t)))
      Filter.atTop (nhds (x 0 ⬝ᵥ (P *ᵥ x 0))) := by
  have heq : ∀ᶠ T in Filter.atTop,
      (∫ t in 0..T, (x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t))) =
        x 0 ⬝ᵥ (P *ᵥ x 0) - x T ⬝ᵥ (P *ᵥ x T) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
    have hcs := lqrContinuous_completionOfSquares_care A B Q R P hT hP_symm hR_symm hCARE x u
      (fun t ht ↦ hx_traj t ht.1)
      (fun t ht ↦ hu t ht.1)
      (h_int T hT)
    linarith
  have hlim : Filter.Tendsto (fun T ↦ x 0 ⬝ᵥ (P *ᵥ x 0) - x T ⬝ᵥ (P *ᵥ x T))
      Filter.atTop (nhds (x 0 ⬝ᵥ (P *ᵥ x 0) - 0)) :=
    tendsto_const_nhds.sub h_conv
  rw [sub_zero] at hlim
  exact Filter.Tendsto.congr' (Filter.Eventually.mono heq fun _ h ↦ h.symm) hlim
