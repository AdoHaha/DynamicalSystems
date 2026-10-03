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

## Estimation Riccati equation and duality (Ch. 4 §4.2.2, printed pp. 280–283)

The moving-horizon estimation (MHE) problem for the linear system
`x⁺ = A x + w`, `y = C x + v` is governed by the *estimator* Riccati equation.
Writing `W` for the process-noise weight and `V` for the measurement-noise weight,
the dual (estimator) Riccati equation is
`Π = A Π Aᵀ − A Π Cᵀ (V + C Π Cᵀ)⁻¹ (C Π Aᵀ) + W`.

The formal content of the estimation/regulation duality of §4.2.2 and
Table 4.2 / Lemma 4.11 / Theorem 4.12 is that this equation is *exactly* the
discrete algebraic Riccati equation (DARE) of the dual LQR problem — the regulation
problem with state-transition matrix `Aᵀ`, input matrix `Cᵀ`, state weight `W` and
input weight `V`. This is recorded in `mhe_dual_lqr`; it is proved by unfolding both
equations and cancelling the double transposes, so the identification is definitional.
The corresponding estimator gain is `mheOptimalGain`, and `mhe_dual_gain` records its
gain duality with `lqrOptimalGain`.

## Offset-free steady-state targets (Ch. 5 §5.5, printed p. 353)

For the tracking problem with setpoint `ysp`, an offset-free steady-state target is
a pair `(xs, us)` that is simultaneously a fixed point of the dynamics and an output
match for the setpoint: `xs = A xs + B us` and `C xs = ysp`. The predicate
`offsetFree_steadyTarget` packages these two conditions. It is the *nominal*
(disturbance-free, `d̂ = 0`) target; the disturbance-augmented target of Rawlings
eq. (1.45b), §5.5.2 is `offsetFree_augmentedTarget`. The trajectory-level
`offsetFree_steadyTarget.zero_offset` shows that a trajectory initialized at a target
and driven by the constant target input keeps zero steady-state error.

## Scope

This file contains only the algebraic Riccati equation, its LQR duality, the estimator
gain and its duality, and the steady-state target predicates. The full finite-horizon
MHE *problem* (the estimation cost functional over a moving window and the associated
optimality conditions) and its stability theory are separate future work; no stability
statement is made here.

## Main definitions

* `mheRiccati`: the estimator (moving-horizon/full-information) Riccati equation.
* `mheOptimalGain`: the estimator gain of §4.2.2.
* `offsetFree_steadyTarget`: the nominal steady-state target predicate for a setpoint.
* `offsetFree_augmentedTarget`: the disturbance-augmented offset-free target.

## Main results

* `mhe_dual_lqr`: the estimator Riccati equation is the DARE of the dual LQR problem.
* `mhe_dual_gain`: the estimator gain is the negative transpose of the dual LQR gain.
* `offsetFree_steadyTarget.zero_offset`: a trajectory at a target keeps zero offset.
-/

@[expose] public section

open Matrix

variable {n m p : ℕ}

/-- The (dual) estimator Riccati equation of moving-horizon / full-information
estimation for the linear system `x⁺ = A x + w`, `y = C x + v`, with process-noise
weight `W` and measurement-noise weight `V`:
`Π = A Π Aᵀ − A Π Cᵀ (V + C Π Cᵀ)⁻¹ (C Π Aᵀ) + W`.

This is the estimation Riccati equation of Rawlings–Mayne–Diehl 2019, 2nd ed.,
Ch. 4 §4.2.2, eq. (4.21) (estimator Riccati), printed p. 280; steady-state p. 283.
The inverse is the matrix (involution) inverse `⁻¹ = Matrix.nonsing_inv`, matching
`dare` in `DynamicalSystems.OptimalControl.LQR`; no extra invertibility hypothesis is
needed for the equation itself. Note that `Matrix.nonsing_inv`/`⁻¹` is `0` when the
matrix `V + C Π Cᵀ` is singular, in which case this equation degenerates to the
uncorrected `Π = A Π Aᵀ + W`; a well-posedness predicate `[Invertible (V + C Π Cᵀ)]`
is therefore needed when connecting the equation to error dynamics. The full
finite-horizon MHE cost and its stability are not formalized here. -/
def mheRiccati (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin p) (Fin p) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P = A * P * Aᵀ - A * P * Cᵀ * (V + C * P * Cᵀ)⁻¹ * (C * P * Aᵀ) + W

/-- **Duality of linear estimation and regulation.**
The estimator Riccati equation `mheRiccati A C W V P` holds if and only if the
discrete algebraic Riccati equation of the dual LQR problem — state transition
`Aᵀ`, input matrix `Cᵀ`, state weight `W`, input weight `V` — holds.

This is the formal content of Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 4 §4.2.2
and Table 4.2 / Lemma 4.11 / Theorem 4.12 (duality of linear estimation and
regulation), printed pp. 281–283. The two equations are the same up to cancelling
the double transposes `(Aᵀ)ᵀ = A` and `(Cᵀ)ᵀ = C`, so the proof is definitional. -/
theorem mhe_dual_lqr (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin p) (Fin p) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) :
    mheRiccati A C W V P ↔ dare Aᵀ Cᵀ W V P := by
  unfold mheRiccati dare
  simp only [transpose_transpose]

/-- The moving-horizon estimator gain of §4.2.2, Table 4.2:
`Le = A P Cᵀ (V + C P Cᵀ)⁻¹`, sending the output innovation to a state correction.
This is the gain associated with the estimator Riccati solution `P` (`mheRiccati`).
The inverse `⅟ = Matrix.invOf` requires the well-posedness instance
`[Invertible (V + C P Cᵀ)]`.

Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 4 §4.2.2, Table 4.2. -/
noncomputable def mheOptimalGain {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (V : Matrix (Fin p) (Fin p) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) [Invertible (V + C * P * Cᵀ)] :
    Matrix (Fin n) (Fin p) ℝ :=
  A * P * Cᵀ * ⅟(V + C * P * Cᵀ)

/-- **Gain duality of estimation and regulation.**
The estimator gain `mheOptimalGain A C V P` is the negative transpose of the LQR gain
of the dual regulation problem with state transition `Aᵀ`, input matrix `Cᵀ`, state
weight `V` and input weight `P`: `Le = −Kᵀ`, i.e. `Leᵀ = −K` where
`K = lqrOptimalGain Aᵀ Cᵀ V P`.

Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 4 §4.2.2, Table 4.2 / Lemma 4.11 /
Theorem 4.12. The symmetry hypotheses `Pᵀ = P` and `Vᵀ = V` make `V + C P Cᵀ`
symmetric, hence its inverse symmetric, so the transpose of the inverse commutes. -/
theorem mhe_dual_gain {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (V : Matrix (Fin p) (Fin p) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) [inst : Invertible (V + C * P * Cᵀ)]
    (hP : Pᵀ = P) (hV : Vᵀ = V) :
    (mheOptimalGain A C V P)ᵀ = -@lqrOptimalGain n p Aᵀ Cᵀ V P inst := by
  have hM : (V + C * P * Cᵀ)ᵀ = V + C * P * Cᵀ := by
    simp only [transpose_add, transpose_mul, transpose_transpose, hP, hV]
    rw [← Matrix.mul_assoc C P Cᵀ]
  have hinv : (⅟(V + C * P * Cᵀ))ᵀ = ⅟(V + C * P * Cᵀ) := by
    simp only [transpose_invOf, hM]
  have hinst : @Invertible.invOf (Matrix (Fin p) (Fin p) ℝ) _ _ (V + Cᵀᵀ * P * Cᵀ) inst
      = ⅟(V + C * P * Cᵀ) := rfl
  unfold mheOptimalGain lqrOptimalGain
  simp only [transpose_mul, transpose_transpose, hP]
  rw [hinv, hinst, Matrix.neg_mul, neg_neg]
  rw [Matrix.mul_assoc C P Aᵀ]

/-- An offset-free steady-state target pair `(xs, us)` for the setpoint `ysp`:
the state `xs` is a fixed point of the dynamics under the input `us`,
`xs = A xs + B us`, and the output of the plant at `xs` matches the setpoint,
`C xs = ysp`.

This is the *nominal* steady-state target condition of Rawlings–Mayne–Diehl 2019,
2nd ed., Ch. 5 §5.5 (printed p. 353): it is disturbance-free, i.e. `d̂ = 0`. The
disturbance-augmented target is `offsetFree_augmentedTarget`. Only the two target
equalities are packaged here; the target-calculator QP that selects a particular
target and the surrounding offset-free tracking controller are separate future work. -/
-- The underscore in `offsetFree_steadyTarget` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def offsetFree_steadyTarget (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (ysp : Fin p → ℝ)
    (xs : Fin n → ℝ) (us : Fin m → ℝ) : Prop :=
  xs = A *ᵥ xs + B *ᵥ us ∧ C *ᵥ xs = ysp

/-- A steady-state target drives every trajectory initialized at it, under the
constant target input `us`, to zero offset: if `x 0 = xs` and
`∀ k, x (k + 1) = A *ᵥ x k + B *ᵥ us`, then `ysp - C *ᵥ (x k) = 0` for all `k`.

This uses both halves of the target condition: `h.1` (`xs = A xs + B us`) makes `xs`
a fixed point, so by induction `x k = xs` for all `k`, and `h.2` (`C xs = ysp`) then
gives the zero steady-state error.

Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 5 §5.5, printed p. 353. -/
theorem offsetFree_steadyTarget.zero_offset {A : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} {C : Matrix (Fin p) (Fin n) ℝ} {ysp : Fin p → ℝ}
    {xs : Fin n → ℝ} {us : Fin m → ℝ} (h : offsetFree_steadyTarget A B C ysp xs us)
    (x : ℕ → Fin n → ℝ) (hx0 : x 0 = xs) (hx : ∀ k, x (k + 1) = A *ᵥ x k + B *ᵥ us) :
    ∀ k, ysp - C *ᵥ (x k) = 0 := by
  have hfix : ∀ k, x k = xs := by
    intro k
    induction k with
    | zero => exact hx0
    | succ k ih =>
      rw [hx k, ih]
      exact h.1.symm
  intro k
  rw [hfix k, h.2]
  exact sub_self ysp

/-- The disturbance-augmented offset-free steady-state target pair `(xs, us)` for the
setpoint `ysp` with disturbance estimate `d̂`: the state `xs` is a fixed point of the
disturbance-augmented dynamics, `xs = A xs + B us + Bd d̂`, and the augmented output
matches the setpoint, `C xs + Cd d̂ = ysp`. Taking `d̂ = 0` recovers the nominal
`offsetFree_steadyTarget`.

This is the offset-free target condition of Rawlings–Mayne–Diehl 2019, 2nd ed.,
Ch. 5 §5.5.2, Rawlings eq. (1.45b). -/
-- The underscore in `offsetFree_augmentedTarget` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def offsetFree_augmentedTarget {n m nd p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Bd : Matrix (Fin n) (Fin nd) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (Cd : Matrix (Fin p) (Fin nd) ℝ) (ysp : Fin p → ℝ)
    (dhat : Fin nd → ℝ) (xs : Fin n → ℝ) (us : Fin m → ℝ) : Prop :=
  xs = A *ᵥ xs + B *ᵥ us + Bd *ᵥ dhat ∧ C *ᵥ xs + Cd *ᵥ dhat = ysp
