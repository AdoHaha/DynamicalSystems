/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.DiscreteTime.ExpectedLyapunov
public import DynamicalSystems.DiscreteTime.MatrixLyapunov
public import DynamicalSystems.OptimalControl.LQR
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Stochastic Model Predictive Control (mean-square stability)

This file formalizes the algebraic core of stochastic model predictive control (MPC)
for a discrete-time linear system subject to Bernoulli packet drops, following
Rawlings, Mayne, and Diehl, *Model Predictive Control: Theory, Computation, and Design*,
2nd ed., Nob Hill Publishing, 2019, Chapter 3, §3.7 (printed pp. 246–256), in particular
§3.7.2 (stabilizing conditions, printed pp. 248–256).

Consider a switched linear system under a Bernoulli packet-loss communication channel:
with probability `ᾱ ∈ [0, 1]`, the control packet is delivered and the closed-loop
matrix is `A₁ = A + B * K`, where `K = lqrOptimalGain A B R P` is the optimal state-feedback
gain for the discrete algebraic Riccati equation (DARE). With probability `1 - ᾱ`, the
packet is dropped (or measurement held) and the autonomous matrix is `A₀ = A`.
The state value function is the quadratic form `V(x) = quadForm P x`.

## Main results

* `mpc_meanSquare_decrease`: The one-step expected quadratic form strictly decreases:
  `ᾱ * quadForm P (A₁ *ᵥ x) + (1 - ᾱ) * quadForm P (A₀ *ᵥ x) < quadForm P x` for all `x ≠ 0`,
  provided that the expected Lyapunov matrix operator satisfies the positive-definiteness
  condition `(P - expectedLyapunovOperator ᾱ A A₁ P).PosDef`. This instantiates the general
  result `meanSquare_decrease_of_bernoulli` from
  `DynamicalSystems.DiscreteTime.ExpectedLyapunov` at the LQR closed-loop mode.

* `mpc_meanSquare_geometric_decay`: If both the delivered mode `A₁` and the dropped mode `A₀`
  contract the quadratic form with a common rate `c ≥ 0`, then the expected quadratic form
  along the two-mode Bernoulli trajectory decays geometrically with factor `c ^ k`:
  `ᾱ * quadForm P ((A₁ ^ k) *ᵥ x) + (1 - ᾱ) * quadForm P ((A₀ ^ k) *ᵥ x) ≤ c ^ k * quadForm P x`.
  This establishes mean-square geometric convergence at rate `c`.

## Scope and boundary

This file formalizes the algebraic one-step expected decrease and the mean-square geometric
decay bound. Full trajectory-level martingale analysis, almost-sure sample-path convergence,
and probability-space formulations are outside the scope of this module.
-/

@[expose] public section

open Matrix

/-- One-step expected mean-square decrease for stochastic MPC under Bernoulli packet loss.

If the expected Lyapunov operator satisfies the strict positive-definiteness condition
`(P - expectedLyapunovOperator ᾱ A (A + B * lqrOptimalGain A B R P) P).PosDef`,
then the one-step expected quadratic form strictly decreases on every non-zero state:
`ᾱ * quadForm P (A₁ *ᵥ x) + (1 - ᾱ) * quadForm P (A₀ *ᵥ x) < quadForm P x`,
where `A₁ = A + B * lqrOptimalGain A B R P` is the delivered-mode closed loop and `A₀ = A`
is the dropped-mode matrix.

Rawlings, Mayne, and Diehl (2019, 2nd ed., Ch. 3 §3.7.2, printed pp. 248–256). -/
theorem mpc_meanSquare_decrease {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (ᾱ : ℝ) [Invertible (R + Bᵀ * P * B)]
    (hE : (P - expectedLyapunovOperator ᾱ A (A + B * lqrOptimalGain A B R P) P).PosDef)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    ᾱ * quadForm P ((A + B * lqrOptimalGain A B R P) *ᵥ x) + (1 - ᾱ) * quadForm P (A *ᵥ x) <
      quadForm P x :=
  meanSquare_decrease_of_bernoulli ᾱ hE hx

/-- Mean-square geometric decay for stochastic MPC under Bernoulli packet loss.

If both the delivered closed loop `A₁ = A + B * lqrOptimalGain A B R P` and the dropped
system `A₀ = A` contract the quadratic form `P` with factor `c ≥ 0`, then for any step `k : ℕ`
and state `x : Fin n → ℝ`, the expected quadratic form of the two-mode Bernoulli trajectory
satisfies the geometric decay bound
`ᾱ * quadForm P ((A₁ ^ k) *ᵥ x) + (1 - ᾱ) * quadForm P ((A₀ ^ k) *ᵥ x) ≤ c ^ k * quadForm P x`,
demonstrating mean-square convergence at rate `c`.

Rawlings, Mayne, and Diehl (2019, 2nd ed., Ch. 3 §3.7.2, printed pp. 248–256). -/
theorem mpc_meanSquare_geometric_decay {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (ᾱ : ℝ) [Invertible (R + Bᵀ * P * B)]
    (hᾱ0 : 0 ≤ ᾱ) (hᾱ1 : ᾱ ≤ 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hA₁ : ∀ x, quadForm P ((A + B * lqrOptimalGain A B R P) *ᵥ x) ≤ c * quadForm P x)
    (hA₀ : ∀ x, quadForm P (A *ᵥ x) ≤ c * quadForm P x)
    (k : ℕ) (x : Fin n → ℝ) :
    (ᾱ * quadForm P (((A + B * lqrOptimalGain A B R P) ^ k) *ᵥ x) +
      (1 - ᾱ) * quadForm P ((A ^ k) *ᵥ x)) ≤ c ^ k * quadForm P x := by
  have h1 : quadForm P (((A + B * lqrOptimalGain A B R P) ^ k) *ᵥ x) ≤ c ^ k * quadForm P x :=
    quadForm_pow_mulVec_le hc0 hA₁ k x
  have h0 : quadForm P ((A ^ k) *ᵥ x) ≤ c ^ k * quadForm P x :=
    quadForm_pow_mulVec_le hc0 hA₀ k x
  have h1' : ᾱ * quadForm P (((A + B * lqrOptimalGain A B R P) ^ k) *ᵥ x) ≤
      ᾱ * (c ^ k * quadForm P x) :=
    mul_le_mul_of_nonneg_left h1 hᾱ0
  have h0' : (1 - ᾱ) * quadForm P ((A ^ k) *ᵥ x) ≤
      (1 - ᾱ) * (c ^ k * quadForm P x) :=
    mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hᾱ1)
  linarith

end
