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

This file formalizes the algebraic expected-decrease certificate used in stochastic model
predictive control (MPC) for a discrete-time linear system subject to Bernoulli packet
drops.

## Provenance

The Bernoulli expected-Lyapunov operator and its one-step decrease are due to
A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding Mode
Control: Theory and Applications*, CRC Press 2018, eqs. (4.2) and (4.12), printed
pp. 72 and 75. Rawlings, Mayne and Diehl, *Model Predictive Control: Theory,
Computation, and Design*, 2nd ed., Nob Hill Publishing, 2019, Ch. 3 §3.7.2 (printed
pp. 248–256) is cited only as the general stochastic-MPC expected-decrease context:
the book states a stochastic Lyapunov condition with an `η`-margin and a general
disturbance, whereas this module is the `η = 0`, two-mode Bernoulli restriction.

## Model

Consider a switched linear system under a Bernoulli packet-loss communication channel.
The control packet is delivered with probability parameter `ᾱ` (the probabilistic
reading `0 ≤ ᾱ ≤ 1` is needed only for the weighting step of the geometric-decay
corollary; the one-step decrease is a purely algebraic inequality valid for every real
`ᾱ`). When delivered, the closed-loop matrix is `A₁ = A + B * K`, where
`K = lqrOptimalGain A B R P` is the state-feedback gain associated with the discrete
algebraic Riccati equation (DARE); when dropped (or the measurement is held), the
autonomous matrix is `A₀ = A`. The quadratic form `V(x) = quadForm P x` is used as a
candidate certificate, so the one-step quantity is the convex combination
`ᾱ * V(A₁ x) + (1 - ᾱ) * V(A₀ x)`. The matrix `P` need not be positive (semi)definite
for the algebraic bounds below; only the assumed matrix inequalities are used.

## Main results

* `mpc_meanSquare_decrease`: The one-step convex combination strictly decreases:
  `ᾱ * quadForm P (A₁ *ᵥ x) + (1 - ᾱ) * quadForm P (A₀ *ᵥ x) < quadForm P x` for all `x ≠ 0`,
  provided that the expected Lyapunov matrix operator satisfies the positive-definiteness
  condition `(P - expectedLyapunovOperator ᾱ A A₁ P).PosDef`. This instantiates the general
  result `meanSquare_decrease_of_bernoulli` from
  `DynamicalSystems.DiscreteTime.ExpectedLyapunov` at the LQR closed-loop mode.

* `mpc_meanSquare_geometric_decay`: If both the delivered mode `A₁` and the dropped mode `A₀`
  contract the quadratic form with a common factor `c ≥ 0`, then the convex combination of
  the two pure-mode endpoint values — the always-delivered endpoint
  `quadForm P ((A₁ ^ k) *ᵥ x)` and the always-dropped endpoint `quadForm P ((A₀ ^ k) *ᵥ x)`,
  weighted by `ᾱ` and `1 - ᾱ` — obeys the geometric bound
  `ᾱ * quadForm P ((A₁ ^ k) *ᵥ x) + (1 - ᾱ) * quadForm P ((A₀ ^ k) *ᵥ x) ≤ c ^ k * quadForm P x`.
  The proved object is this convex combination of two deterministic endpoint values, *not* a
  measure-theoretic expectation over the infinite product space of mode sequences, so the bound
  is not by itself a mean-square convergence statement at rate `c`.

## Scope and boundary

The stabilizing LMI `P - E_P ≻ 0` and the contraction factors `hA₁`/`hA₀` are hypotheses in
this file; deriving a rate `c ∈ [0, 1)` from `exists_factor` and the DARE is out of scope for
this slice. Full trajectory-level martingale analysis, almost-sure sample-path convergence,
and probability-space formulations are likewise outside the scope of this module.
-/

@[expose] public section

open Matrix

/-- One-step expected mean-square decrease for stochastic MPC under Bernoulli packet loss.

This is the algebraic one-step expected-Lyapunov certificate of A. Argha, S. W. Su,
L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory and
Applications*, CRC Press 2018, eqs. (4.2)/(4.12), instantiated at the LQR closed loop.
Rawlings, Mayne and Diehl (2019, 2nd ed., Ch. 3 §3.7.2, printed pp. 248–256) supplies
only the general stochastic-MPC expected-decrease context; here the margin is `η = 0`
and the channel has two modes.

If the expected Lyapunov operator satisfies the strict positive-definiteness condition
`(P - expectedLyapunovOperator ᾱ A (A + B * lqrOptimalGain A B R P) P).PosDef`,
then the one-step expected quadratic form strictly decreases on every non-zero state:
`ᾱ * quadForm P (A₁ *ᵥ x) + (1 - ᾱ) * quadForm P (A₀ *ᵥ x) < quadForm P x`,
where `A₁ = A + B * lqrOptimalGain A B R P` is the delivered-mode closed loop and `A₀ = A`
is the dropped-mode matrix. The matrix inequality is a hypothesis of this theorem, and no
probabilistic range condition on `ᾱ` is assumed: the identity holds for every real `ᾱ` and
any `P`, so it is purely algebraic. Deriving the LMI from the DARE/`exists_factor` is out of
scope for this slice. -/
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
and state `x : Fin n → ℝ`, the convex combination of the two pure-mode endpoint values —
the always-delivered endpoint `(A₁ ^ k) *ᵥ x` and the always-dropped endpoint `(A₀ ^ k) *ᵥ x`,
weighted by `ᾱ` and `1 - ᾱ` — satisfies the geometric bound
`ᾱ * quadForm P ((A₁ ^ k) *ᵥ x) + (1 - ᾱ) * quadForm P ((A₀ ^ k) *ᵥ x) ≤ c ^ k * quadForm P x`.

The proved object is this convex combination of two deterministic endpoint values; it is *not*
a measure-theoretic expectation over the infinite product space of mode sequences, and the
bound should not be read as a mean-square convergence theorem at rate `c`. The contraction
hypotheses `hA₁`/`hA₀` are assumptions here; deriving them, and a rate `c ∈ [0, 1)`, from
`exists_factor` and the DARE is out of scope for this slice. The matrix `P` need not be positive
(semi)definite for the algebraic bound. -/
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
