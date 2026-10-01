/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-! # Parameter adaptation algorithms: abstract regressor and algebraic core

This file sets up the abstract regressor and the algebraic skeleton of the
parameter adaptation algorithms (PAA) of I. D. Landau, R. Lozano, M'Saad and
A. Karimi, *Adaptive Control: Algorithms, Analysis and Applications*, 2nd ed.,
Springer 2011, Chapter 3 (deterministic environment, eqs. 3.7–3.15 and
3.50–3.54).

The regressor is kept abstract: `φ : Fin n → ℝ`. The plant parameter is `θ`, its
estimate is `θ̂`, and `F` is the adaptation gain matrix. The predicted output is
the matrix-vector dot product `θ̂ᵀφ`, the adaptation (prediction) errors are the
differences between the measured output and the predicted outputs, and the
parameter error is `θ̃ = θ − θ̂`.

## Main definitions

* `predictedOutput thetaHat phi`: the predicted output `θ̂ᵀφ`.
* `aprioriError y thetaHat phi`: the a priori prediction error `ε⁰ = y − θ̂ᵀφ`
  (eq. 3.13).
* `aposterioriError y thetaHat phi`: the a posteriori prediction error
  `ε = y − θ̂ᵀφ` (eq. 3.8), evaluated at the updated estimate.
* `paramError theta thetaHat`: the parameter error `θ̃ = θ − θ̂` (eq. 3.16).
* `paaStep F phi eps thetaHat`: one PAA step `θ̂⁺ = θ̂ + F·(φ ε)` (eqs. 3.15 /
  3.51).

## Main results

* `aposterioriError_eq_aprioriError_sub`: `ε = ε⁰ − (θ̂⁺ − θ̂)ᵀφ`, the
  rearrangement underlying eq. 3.50.
* `paramError_paaStep`: the parameter-error recursion `θ̃⁺ = θ̃ − F·(φ ε)` of a
  PAA step.
-/

@[expose] public section

/-- The predicted output `θ̂ᵀφ`. -/
def predictedOutput {n : ℕ} (thetaHat phi : Fin n → ℝ) : ℝ := thetaHat ⬝ᵥ phi

/-- A priori prediction error `ε⁰ = y − θ̂ᵀφ` (eq. 3.13). -/
def aprioriError {n : ℕ} (y : ℝ) (thetaHat phi : Fin n → ℝ) : ℝ :=
  y - predictedOutput thetaHat phi

/-- A posteriori prediction error `ε = y − (θ̂⁺)ᵀφ` (eq. 3.8). -/
def aposterioriError {n : ℕ} (y : ℝ) (thetaHat phi : Fin n → ℝ) : ℝ :=
  y - predictedOutput thetaHat phi

/-- Parameter error `θ̃ = θ − θ̂`. -/
def paramError {n : ℕ} (theta thetaHat : Fin n → ℝ) : Fin n → ℝ := theta - thetaHat

/-- One PAA step `θ̂⁺ = θ̂ + F·(φ ε)` (eqs. 3.15 / 3.51). -/
def paaStep {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) (eps : ℝ)
    (thetaHat : Fin n → ℝ) : Fin n → ℝ :=
  thetaHat + F.mulVec (eps • phi)

/-- Split the a posteriori error into the a priori error and the regressor
projection of the parameter update (book eq. 3.50, rearrangement). -/
theorem aposterioriError_eq_aprioriError_sub {n : ℕ} (y : ℝ)
    (thetaHat thetaHat' phi : Fin n → ℝ) :
    aposterioriError y thetaHat' phi =
      aprioriError y thetaHat phi - (thetaHat' - thetaHat) ⬝ᵥ phi := by
  simp only [aposterioriError, aprioriError, predictedOutput, sub_dotProduct]
  ring

/-- The parameter-error recursion of a PAA step. -/
theorem paramError_paaStep {n : ℕ} (theta thetaHat : Fin n → ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) (eps : ℝ) :
    paramError theta (paaStep F phi eps thetaHat) =
      paramError theta thetaHat - F.mulVec (eps • phi) := by
  simp only [paramError, paaStep]
  abel
