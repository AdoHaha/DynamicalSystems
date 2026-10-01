/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.ParameterAdaptation.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.FieldSimp

/-! # PAA Lyapunov algebra: the RLS quadratic-form difference identity

This file formalizes the quadratic Lyapunov function of the parameter adaptation
algorithms (PAA) of I. D. Landau, R. Lozano, M'Saad and A. Karimi, *Adaptive
Control: Algorithms, Analysis and Applications*, 2nd ed., Springer 2011,
Chapter 3 (deterministic environment, eq. 3.124 and the equivalent feedback
analysis of Sect. 3.3).

The inverse adaptation gain is `P = F⁻¹`, and the Lyapunov function is the
quadratic form `V(θ̃) = θ̃ᵀ P θ̃`. For the recursive least squares update
`θ̃⁺ = θ̃ − F·(νφ)` with `ν = (θ̃ᵀφ)/(1 + φᵀFφ)` and `P⁺ = P + φφᵀ`, the exact
difference identity is

`V⁺ − V = −(1 + φᵀFφ)·ν²`,

the discrete dissipation inequality that drives the adaptation-error convergence
of Theorem 3.2.

## Main definitions

* `paaV P θ̃`: the PAA Lyapunov function `θ̃ᵀ P θ̃` (`P = F⁻¹`).

## Main results

* `paaV_add_vecMulVec`: the rank-one identity
  `(P + φφᵀ)`-form value `V(P + φφᵀ, x) = V(P, x) + (xᵀφ)²`.
* `paaV_sub_of_transpose_eq`: the polarisation identity
  `V(P, x − v) = V(P, x) − 2·xᵀPv + vᵀPv` for symmetric `P`.
* `paaV_rls_step`: the exact RLS quadratic-form difference identity
  `V⁺ − V = −(1 + φᵀFφ)·ν²` (eq. 3.124, noiseless direct case `H = 1`).
-/

@[expose] public section

open scoped Matrix

/-- PAA Lyapunov function `θ̃ᵀ P θ̃` (`P = F⁻¹`). -/
def paaV {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (thetaTilde : Fin n → ℝ) : ℝ :=
  thetaTilde ⬝ᵥ (P.mulVec thetaTilde)

/-- The rank-one Lyapunov identity: adjoining the rank-one matrix `φφᵀ` to `P`
adds the square of the projection `xᵀφ` to the quadratic form. -/
lemma paaV_add_vecMulVec {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (x phi : Fin n → ℝ) :
    paaV (P + Matrix.vecMulVec phi phi) x = paaV P x + (x ⬝ᵥ phi) ^ 2 := by
  simp only [paaV, Matrix.add_mulVec, dotProduct_add, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMulVec, smul_dotProduct, dotProduct_comm phi x, smul_eq_mul]
  ring

/-- Polarisation identity for a symmetric matrix `P`: expanding the quadratic
form of the difference `x − v`. -/
lemma paaV_sub_of_transpose_eq {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P)
    (x v : Fin n → ℝ) :
    paaV P (x - v) = paaV P x - 2 * (x ⬝ᵥ P.mulVec v) + v ⬝ᵥ P.mulVec v := by
  have hcomm : v ⬝ᵥ P.mulVec x = x ⬝ᵥ P.mulVec v := by
    simpa only [hP] using Matrix.dotProduct_transpose_mulVec P v x
  simp only [paaV, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hcomm]
  ring

/-- Exact RLS quadratic-form difference identity (noiseless direct case): with
`F * P = 1`, `Fᵀ = F`, a posteriori error `ν = (θ̃ᵀφ)/(1+φᵀFφ)`, update
`θ̃⁺ = θ̃ − F·(νφ)` and `P⁺ = P + φφᵀ`, then `V⁺ − V = −(1 + φᵀFφ)·ν²`.

The non-degeneracy hypothesis `1 + φᵀFφ ≠ 0` is required: the inverse
`(1 + φᵀFφ)⁻¹` is `0` at `1 + φᵀFφ = 0` (this is Lean's total inverse), and in
that degenerate case the identity fails for indefinite `F` (e.g. `n = 1`,
`F = P = -1`, `φ = 1`, `θ̃ = 1`). In the book `F > 0` guarantees
`1 + φᵀFφ ≥ 1`, so the hypothesis never binds there. -/
theorem paaV_rls_step {n : ℕ} (F P : Matrix (Fin n) (Fin n) ℝ) (hFP : F * P = 1)
    (hFsym : Fᵀ = F) (thetaTilde phi : Fin n → ℝ)
    (hden : 1 + phi ⬝ᵥ (F.mulVec phi) ≠ 0) :
    let b := phi ⬝ᵥ (F.mulVec phi)
    let ν := (thetaTilde ⬝ᵥ phi) * (1 + b)⁻¹
    paaV (P + Matrix.vecMulVec phi phi) (thetaTilde - F.mulVec (ν • phi)) - paaV P thetaTilde
      = -(1 + b) * ν ^ 2 := by
  dsimp only
  set b : ℝ := phi ⬝ᵥ (F.mulVec phi) with hb
  set c : ℝ := thetaTilde ⬝ᵥ phi with hc
  set ν : ℝ := c * (1 + b)⁻¹ with hν
  have hden' : 1 + b ≠ 0 := hden
  -- `F` and `P` are inverse, symmetric matrices
  have htr : Pᵀ * F = 1 := by
    have h := congrArg Matrix.transpose hFP
    rwa [Matrix.transpose_mul, hFsym, Matrix.transpose_one] at h
  have hPsym : Pᵀ = P := by
    have h := congrArg (fun M ↦ M * P) htr
    simpa [Matrix.mul_assoc, hFP] using h
  have hPF : P * F = 1 := by rwa [hPsym] at htr
  have hPu : P.mulVec (F.mulVec phi) = phi := by
    rw [Matrix.mulVec_mulVec, hPF, Matrix.one_mulVec]
  have hbu : (F.mulVec phi) ⬝ᵥ phi = b := by rw [dotProduct_comm, ← hb]
  -- rewrite the outer-product update and expand the quadratic form
  have hFu : F.mulVec (ν • phi) = ν • (F.mulVec phi) := by rw [Matrix.mulVec_smul]
  have hPv : P.mulVec (ν • (F.mulVec phi)) = ν • phi := by
    rw [Matrix.mulVec_smul, hPu]
  have hxv : thetaTilde ⬝ᵥ P.mulVec (ν • (F.mulVec phi)) = ν * c := by
    rw [hPv, dotProduct_smul, smul_eq_mul, ← hc]
  have hvv : (ν • (F.mulVec phi)) ⬝ᵥ P.mulVec (ν • (F.mulVec phi)) = ν ^ 2 * b := by
    rw [hPv, smul_dotProduct, dotProduct_smul, smul_eq_mul, hbu]
    ring
  have hphi : (thetaTilde - ν • (F.mulVec phi)) ⬝ᵥ phi = c - ν * b := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hbu, ← hc]
  rw [hFu, paaV_add_vecMulVec, paaV_sub_of_transpose_eq P hPsym, hxv, hvv, hphi, hν]
  field_simp [hden']
  ring
