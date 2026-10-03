/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import DynamicalSystems.DiscreteTime.MatrixLyapunov

/-! # The expected discrete-Lyapunov operator

This file collects the generic one-step algebraic facts about the *expected*
discrete-Lyapunov operator of a Bernoulli-parameterised switched linear system.
For a real square matrix `P`, two mode matrices `A₀`, `A₁` and a real weight `ᾱ`
the operator is

`E_P(A₀, A₁, ᾱ) = ᾱ • A₁ᵀ P A₁ + (1 - ᾱ) • A₀ᵀ P A₀`.

Its defining property is that the quadratic form of `E_P` is the one-step
expected quadratic form `ᾱ * quadForm P (A₁ x) + (1 - ᾱ) * quadForm P (A₀ x)`
(`expectedLyapunovOperator_quadForm`). This is the algebraic core of the `∆V`
computation (4.12), printed p. 75, and of the mean-square notion of Definition
4.1 / Lemma 4.1, printed p. 73, of A. Argha, S. W. Su, L. Li and H. T. Nguyen,
*Advances in Discrete-Time Sliding Mode Control: Theory and Applications*, CRC
Press 2018.

The operator is generic rather than networked-control-specific: besides the
Bernoulli packet-loss channel of discrete-time sliding-mode control
(`DynamicalSystems.Control.SlidingMode.PacketLoss`, which consumes this module),
it is the one-step expected-Lyapunov decrease used by stochastic MPC. The generic
home serves stochastic MPC (Rawlings, Mayne and Diehl, *Model Predictive Control:
Theory, Computation, and Design*, 2nd ed., Nob Hill 2019, Ch. 3 §3.7, printed
pp. 246–257), which must not depend on the sliding-mode package.

## Main definitions

* `expectedLyapunovOperator`: the expected Lyapunov operator
  `E_P(A₀, A₁, ᾱ) = ᾱ A₁ᵀ P A₁ + (1 - ᾱ) A₀ᵀ P A₀`.

## Main results

* `expectedLyapunovOperator_quadForm`: the quadratic form of the operator is the
  one-step expected quadratic form.
* `meanSquare_decrease_of_lmi`: if `P - E_P ≻ 0` then the convex combination of
  the two one-step quadratic forms is strictly below `quadForm P x` for `x ≠ 0`.
* `meanSquare_decrease_of_bernoulli`: the same strict decrease phrased for the
  Bernoulli-weighted expected quadratic form.
* `meanSquare_nonneg_of_bernoulli`: for `ᾱ ∈ [0, 1]` and `P ⪰ 0` the expected
  one-step quadratic form is nonnegative.

## Implementation notes

The matrix quadratic-form toolkit (`quadForm`, `quadForm_add`, `quadForm_smul_left`,
`quadForm_mulVec`, `quadForm_pos`, `quadForm_sub`, `quadForm_nonneg`) is reused from
`DynamicalSystems.DiscreteTime.MatrixLyapunov`. The operator is kept generic — no
trajectory, no martingale and no probability space — so that the networked-control
and the stochastic-MPC uses share a single definition.

## Honest boundary

Only the **one-step** expected-Lyapunov decrease is formalized here: if the
algebraic matrix inequality `P - E_P ≻ 0` holds then the expected quadratic form
strictly decreases in one step. The trajectory-level martingale argument, the
exponential mean-square rate, the full block LMI and the almost-sure convergence
rest on this algebraic condition but are not formalized here. Feasibility of the
LMI is never claimed.
-/

@[expose] public section

open Matrix

variable {n : ℕ}

/-- The **expected discrete-Lyapunov operator** of the Bernoulli packet-loss
channel of A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time
Sliding Mode Control: Theory and Applications*, CRC Press 2018, eq. (4.2),
printed p. 72, and eq. (4.12), printed p. 75:

`expectedLyapunovOperator ᾱ A₀ A₁ P =
   ᾱ • (A₁ᵀ P A₁) + (1 - ᾱ) • (A₀ᵀ P A₀)`

Here `A₁` is the delivered-mode closed-loop matrix and `A₀` the dropped-mode
(held-measurement) matrix, and `ᾱ` is the delivery probability. Its defining
property is that the quadratic form of the operator is the one-step expected
quadratic form, `expectedLyapunovOperator_quadForm` below. The definition
makes sense for every real `ᾱ`; the probabilistic interpretation of `ᾱ` as
a probability requires `0 ≤ ᾱ ≤ 1` and is used in the Bernoulli-measure
statement `meanSquare_decrease_of_bernoulli`. The generic placement additionally
serves stochastic MPC (Rawlings, Mayne and Diehl 2019, Ch. 3 §3.7). -/
noncomputable def expectedLyapunovOperator (ᾱ : ℝ)
    (A₀ A₁ P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ᾱ • (A₁ᵀ * P * A₁) + (1 - ᾱ) • (A₀ᵀ * P * A₀)

/-- **The quadratic form of the expected Lyapunov operator is the one-step
expected quadratic form.** This is the algebraic identity that turns the matrix
inequality hypothesis of `meanSquare_decrease_of_bernoulli` into a statement
about the expectation

`ᾱ * quadForm P (A₁ *ᵥ x) + (1 - ᾱ) * quadForm P (A₀ *ᵥ x)`,

using the substitution identity `quadForm_mulVec` of
`DynamicalSystems.DiscreteTime.MatrixLyapunov`. It is the scalar content of the
expectation computation (4.12), printed p. 75, of A. Argha, S. W. Su, L. Li and
H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory and
Applications*, CRC Press 2018. -/
theorem expectedLyapunovOperator_quadForm (ᾱ : ℝ)
    (A₀ A₁ P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadForm (expectedLyapunovOperator ᾱ A₀ A₁ P) x =
      ᾱ * quadForm P (A₁ *ᵥ x) + (1 - ᾱ) * quadForm P (A₀ *ᵥ x) := by
  simp only [expectedLyapunovOperator, quadForm_add, quadForm_smul_left, quadForm_mulVec]

/-- **Purely algebraic form of the one-step strict decrease.** The convex combination
of the two one-step quadratic forms is strictly dominated by `quadForm P x` whenever
`P - expectedLyapunovOperator ᾱ A₀ A₁ P` is positive definite, without requiring
positivity or bounds on `ᾱ`. -/
theorem meanSquare_decrease_of_lmi (ᾱ : ℝ)
    {A₀ A₁ P : Matrix (Fin n) (Fin n) ℝ}
    (hLMI : (P - expectedLyapunovOperator ᾱ A₀ A₁ P).PosDef)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    ᾱ * quadForm P (A₁ *ᵥ x) + (1 - ᾱ) * quadForm P (A₀ *ᵥ x) < quadForm P x := by
  have h := quadForm_pos hLMI hx
  rw [quadForm_sub, expectedLyapunovOperator_quadForm] at h
  linarith

/-- **One-step expected mean-square decrease under Bernoulli packet loss.** If
the expected Lyapunov operator `expectedLyapunovOperator ᾱ A₀ A₁ P` satisfies
the strict matrix inequality `P - expectedLyapunovOperator ᾱ A₀ A₁ P ≻ 0`,
then the one-step expected quadratic form strictly decreases on every non-zero
state:

`ᾱ * quadForm P (A₁ *ᵥ x) + (1 - ᾱ) * quadForm P (A₀ *ᵥ x) < quadForm P x`.

This is the `η = 0` strict-decrease instance of the algebraic one-step
expected-Lyapunov condition behind the disturbance-free part of Theorem 4.1
(eqs. (4.11)–(4.12), printed p. 75) and of the exponential mean-square definition
of Definition 4.1, printed p. 73, of A. Argha, S. W. Su, L. Li and H. T. Nguyen,
*Advances in Discrete-Time Sliding Mode Control: Theory and Applications*, CRC
Press 2018. It is *not* the uniform `∆V ≤ -η‖x‖²` margin: the strict margin with
`η > 0` requires the additional compactness step, which is not formalized here.
The statement does not require `P` to be positive definite or `ᾱ` to lie in
`[0, 1]`; it is a purely algebraic inequality valid for every real `ᾱ` and any
`P`. It is derived from the library's strict discrete decrease
`quadForm_mulVec_lt` (`DynamicalSystems.DiscreteTime.MatrixLyapunov`) via the
expectation identity `expectedLyapunovOperator_quadForm`: in the degenerate
case `ᾱ = 1` the condition is exactly `(P - A₁ᵀ P A₁) ≻ 0`, i.e.
`quadForm_mulVec_lt` with `M = A₁`. This declaration is retained as a naming-continuity
synonym of `meanSquare_decrease_of_lmi`, preserving the Argha et al. (2018) /
`PacketLoss.lean` vocabulary for downstream consumers. -/
theorem meanSquare_decrease_of_bernoulli (ᾱ : ℝ)
    {A₀ A₁ P : Matrix (Fin n) (Fin n) ℝ}
    (hLMI : (P - expectedLyapunovOperator ᾱ A₀ A₁ P).PosDef)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    ᾱ * quadForm P (A₁ *ᵥ x) + (1 - ᾱ) * quadForm P (A₀ *ᵥ x) < quadForm P x :=
  meanSquare_decrease_of_lmi ᾱ hLMI hx

/-- **Mean-square nonnegativity.** For any valid Bernoulli delivery probability `ᾱ ∈ [0, 1]`
and positive semidefinite matrix `P`, the expected one-step quadratic form is nonnegative. -/
theorem meanSquare_nonneg_of_bernoulli (ᾱ : ℝ) (hᾱ0 : 0 ≤ ᾱ) (hᾱ1 : ᾱ ≤ 1)
    {A₀ A₁ P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef) (x : Fin n → ℝ) :
    0 ≤ ᾱ * quadForm P (A₁ *ᵥ x) + (1 - ᾱ) * quadForm P (A₀ *ᵥ x) := by
  have : 0 ≤ quadForm P (A₁ *ᵥ x) := quadForm_nonneg hP _
  have : 0 ≤ quadForm P (A₀ *ᵥ x) := quadForm_nonneg hP _
  have : 0 ≤ 1 - ᾱ := sub_nonneg.mpr hᾱ1
  positivity
