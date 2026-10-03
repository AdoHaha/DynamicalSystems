/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.DiscreteTime.MatrixLyapunov
public import Mathlib.LinearAlgebra.Matrix.Invertible
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Discrete-time Linear Quadratic Regulator (LQR) and the DARE

This file formalizes the infinite-horizon discrete-time linear quadratic regulator (LQR),
the discrete algebraic Riccati equation (DARE), and the Lyapunov / Bellman identity for
the DARE state-feedback gain.

The treatment follows Rawlings, Mayne and Diehl, *Model Predictive Control: Theory, Computation,
and Design*, 2nd ed., 2019, Ch. 1 §1.3.6, eq. (1.18), printed p. 25, for the discrete algebraic
Riccati equation (DARE), the DARE state-feedback gain, the closed-loop Lyapunov matrix equation,
and the one-step (Bellman-form) identity.

The book states the cost with a leading factor (1/2), `V = (1/2)xᵀ Π x`, whereas this file uses
`V = xᵀ P x`. This is a uniform rescaling: it leaves the DARE and the gain unchanged in form
(the book's `(Bᵀ P B + R)` equals this file's `(R + Bᵀ P B)` by commutativity of addition).

## Main definitions

* `dare`: the discrete algebraic Riccati equation
  `P = Aᵀ P A - Aᵀ P B (R + Bᵀ P B)⁻¹ Bᵀ P A + Q`.
* `lqrOptimalGain`: the DARE state-feedback gain
  `K = -⅟(R + Bᵀ P B) Bᵀ P A`.

## Main results

* `lqr_lyapunov_decrease`: the DARE implies the closed-loop Lyapunov equation
  `P = (A + B K)ᵀ P (A + B K) + Q + Kᵀ R K`.
* `lqr_bellman`: the quadratic value function `V(x) = quadForm P x` satisfies the Bellman
  one-step identity `V(x) = quadForm Q x + quadForm R (K x) + V((A + B K) x)`.
-/

@[expose] public section

open Matrix

variable {n m : ℕ}
variable (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
variable (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
variable (P : Matrix (Fin n) (Fin n) ℝ)

/-- The discrete algebraic Riccati equation (DARE).
Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 1 §1.3.6, eq. (1.18), printed p. 25. -/
def dare : Prop :=
  P = Aᵀ * P * A - Aᵀ * P * B * (R + Bᵀ * P * B)⁻¹ * (Bᵀ * P * A) + Q

/-- The DARE state-feedback gain for the discrete LQR.
Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 1 §1.3.6, eq. (1.18), printed p. 25. -/
noncomputable def lqrOptimalGain [Invertible (R + Bᵀ * P * B)] : Matrix (Fin m) (Fin n) ℝ :=
  -⅟(R + Bᵀ * P * B) * (Bᵀ * P * A)

variable [Invertible (R + Bᵀ * P * B)]

private lemma mul_gain :
    (R + Bᵀ * P * B) * (-⅟(R + Bᵀ * P * B) * (Bᵀ * P * A)) = -(Bᵀ * P * A) := by
  rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_invOf_cancel_left]

/-- DARE implies the closed-loop Lyapunov matrix equation.
This is the algebraic Lyapunov equation; no stability/decrease is asserted (that requires
Q + KᵀRK ⪰ 0).
Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 1 §1.3.6 (printed p. 24). -/
theorem lqr_lyapunov_decrease (hD : dare A B Q R P) :
    P = (A + B * lqrOptimalGain A B R P)ᵀ * P * (A + B * lqrOptimalGain A B R P) + Q +
      (lqrOptimalGain A B R P)ᵀ * R * (lqrOptimalGain A B R P) := by
  have hexp := expand_closed_loop (lqrOptimalGain A B R P)
  rw [hexp]
  unfold lqrOptimalGain
  rw [mul_gain]
  have hzero : Bᵀ * P * A + -(Bᵀ * P * A) = 0 := by abel
  rw [hzero, Matrix.mul_zero, add_zero]
  rw [Matrix.neg_mul, Matrix.mul_neg, ← sub_eq_add_neg, invOf_eq_nonsing_inv, ← Matrix.mul_assoc]
  exact hD
where
  expand_closed_loop (K : Matrix (Fin m) (Fin n) ℝ) :
      (A + B * K)ᵀ * P * (A + B * K) + Q + Kᵀ * R * K =
        Aᵀ * P * A + Aᵀ * P * B * K + Q + Kᵀ * (Bᵀ * P * A + (R + Bᵀ * P * B) * K) := by
    simp only [transpose_add, transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel

private lemma quadForm_mulVec_rect {k l : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (N : Matrix (Fin k) (Fin l) ℝ) (x : Fin l → ℝ) :
    quadForm M (N *ᵥ x) = quadForm (Nᵀ * M * N) x := by
  simp only [quadForm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_mulVec, Matrix.vecMul_transpose]

/-- The one-step (Bellman-form) identity for the DARE gain.
Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 1 §1.3.6 (printed p. 24). -/
theorem lqr_bellman (hD : dare A B Q R P) (x : Fin n → ℝ) :
    quadForm P x = quadForm Q x + quadForm R (lqrOptimalGain A B R P *ᵥ x) +
      quadForm P ((A + B * lqrOptimalGain A B R P) *ᵥ x) := by
  have hdec := lqr_lyapunov_decrease A B Q R P hD
  conv_lhs => rw [hdec]
  rw [quadForm_add, quadForm_add]
  rw [← quadForm_mulVec, ← quadForm_mulVec_rect]
  ring
