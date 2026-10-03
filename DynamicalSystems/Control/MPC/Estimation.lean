/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.LQR

/-! # Moving-horizon estimation and offset-free steady-state targets

This file formalizes two estimation results of Rawlings, Mayne and Diehl,
*Model Predictive Control: Theory, Computation, and Design*, 2nd ed., Nob Hill
Publishing, 2019.

## Estimation Riccati equation and duality (Ch. 4 §4.2.2, printed pp. 281–283)

The moving-horizon estimation (MHE) problem for the linear system
`x⁺ = A x + w`, `y = C x + v` is governed by the *estimator* Riccati equation.
Writing `W` for the process-noise weight and `V` for the measurement-noise weight,
the dual (estimator) Riccati equation is
`Π = A Π Aᵀ − A Π Cᵀ (V + C Π Cᵀ)⁻¹ (C Π Aᵀ) + W`.

The formal content of the estimation/regulation duality of §4.2.2 and Theorem 4.1
is that this equation is *exactly* the discrete algebraic Riccati equation (DARE)
of the dual LQR problem — the regulation problem with state-transition matrix `Aᵀ`,
input matrix `Cᵀ`, state weight `W` and input weight `V`. This is recorded in
`mhe_dual_lqr`; it is proved by unfolding both equations and cancelling the double
transposes, so the identification is definitional.

## Offset-free steady-state targets (Ch. 5 §5.5, printed p. 353)

For the tracking problem with setpoint `ysp`, an offset-free steady-state target is
a pair `(xs, us)` that is simultaneously a fixed point of the dynamics and an output
match for the setpoint: `xs = A xs + B us` and `C xs = ysp`. The predicate
`offsetFree_steadyTarget` packages these two conditions, and
`offsetFree_steadyTarget.zero_offset` records the consequent absence of offset.

## Scope

This file contains only the algebraic Riccati equation, its LQR duality, and the
steady-state target predicate. The full finite-horizon MHE *problem* (the estimation
cost functional over a moving window and the associated optimality conditions) and
its stability theory are separate future work; no stability statement is made here.

## Main definitions

* `mheRiccati`: the estimator (moving-horizon/full-information) Riccati equation.
* `offsetFree_steadyTarget`: the steady-state target predicate for a setpoint.

## Main results

* `mhe_dual_lqr`: the estimator Riccati equation is the DARE of the dual LQR problem.
* `offsetFree_steadyTarget.zero_offset`: a steady-state target has zero offset.
-/

@[expose] public section

open Matrix

variable {n m p : ℕ}

/-- The (dual) estimator Riccati equation of moving-horizon / full-information
estimation for the linear system `x⁺ = A x + w`, `y = C x + v`, with process-noise
weight `W` and measurement-noise weight `V`:
`Π = A Π Aᵀ − A Π Cᵀ (V + C Π Cᵀ)⁻¹ (C Π Aᵀ) + W`.

This is the estimation Riccati equation of Rawlings–Mayne–Diehl 2019, 2nd ed.,
Ch. 4 §4.2.2, eq. (4.13)-style, printed pp. 281–283. The inverse is the matrix
(involution) inverse `⁻¹ = Matrix.nonsing_inv`, matching `dare` in
`DynamicalSystems.OptimalControl.LQR`; no extra invertibility hypothesis is needed
for the equation itself. The full finite-horizon MHE cost and its stability are
not formalized here. -/
def mheRiccati (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin p) (Fin p) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P = A * P * Aᵀ - A * P * Cᵀ * (V + C * P * Cᵀ)⁻¹ * (C * P * Aᵀ) + W

/-- **Duality of linear estimation and regulation.**
The estimator Riccati equation `mheRiccati A C W V P` holds if and only if the
discrete algebraic Riccati equation of the dual LQR problem — state transition
`Aᵀ`, input matrix `Cᵀ`, state weight `W`, input weight `V` — holds.

This is the formal content of Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 4 §4.2.2
and Theorem 4.1 (duality of linear estimation and regulation), printed pp. 281–283.
The two equations are the same up to cancelling the double transposes `(Aᵀ)ᵀ = A`
and `(Cᵀ)ᵀ = C`, so the proof is definitional. -/
theorem mhe_dual_lqr (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin p) (Fin p) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) :
    mheRiccati A C W V P ↔ dare Aᵀ Cᵀ W V P := by
  unfold mheRiccati dare
  simp only [transpose_transpose]

/-- An offset-free steady-state target pair `(xs, us)` for the setpoint `ysp`:
the state `xs` is a fixed point of the dynamics under the input `us`,
`xs = A xs + B us`, and the output of the plant at `xs` matches the setpoint,
`C xs = ysp`.

This is the steady-state target condition of Rawlings–Mayne–Diehl 2019, 2nd ed.,
Ch. 5 §5.5 (printed p. 353). Only the two target equalities are packaged here; the
target-calculator QP that selects a particular target and the surrounding
offset-free tracking controller are separate future work. -/
-- The underscore in `offsetFree_steadyTarget` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def offsetFree_steadyTarget (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (ysp : Fin p → ℝ)
    (xs : Fin n → ℝ) (us : Fin m → ℝ) : Prop :=
  xs = A *ᵥ xs + B *ᵥ us ∧ C *ᵥ xs = ysp

/-- A steady-state target tracks its setpoint with zero offset: the deviation
`ysp − C xs` of the setpoint from the target output vanishes.

Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 5 §5.5, printed p. 353. -/
theorem offsetFree_steadyTarget.zero_offset {A : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} {C : Matrix (Fin p) (Fin n) ℝ} {ysp : Fin p → ℝ}
    {xs : Fin n → ℝ} {us : Fin m → ℝ} (h : offsetFree_steadyTarget A B C ysp xs us) :
    ysp - C *ᵥ xs = 0 := by
  rw [← h.2, sub_self]
