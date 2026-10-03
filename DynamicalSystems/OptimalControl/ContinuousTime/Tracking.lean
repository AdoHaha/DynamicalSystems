/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.LinearQuadratic

/-! # Continuous-time tracking and deterministic (minimum-energy) estimation

This file formalizes the two §8.3 themes of Sontag, *Mathematical Control Theory:
Deterministic Finite Dimensional Systems*, 2nd ed., 1998, printed pp. 371–380
(PDF pp. 383–392): output/state tracking under a reference signal, and the
deterministic (minimum-energy) Kalman filtering problem together with its
linear-quadratic duality. The supporting estimation reference is Crassidis &
Junkins, *Optimal Estimation of Dynamic Systems*.

## Tracking (Sontag §8.3, Theorem 38, printed pp. 373–374)

For the LQR plant `ẋ = A x + B u` with constant setpoint `r`, weights `Q`, `R`,
and a solution `P` of the continuous algebraic Riccati equation (`care`) and a
feedforward vector `β` satisfying the (steady-state form of the) affine
feedforward/adjoint equation `(A + B F)ᵀ β = Q r`, `F = -R⁻¹BᵀP`, the affine law

`u = F x - R⁻¹Bᵀ β = -R⁻¹Bᵀ (P x + β)`

is optimal for the tracking cost `∫ {uᵀRu + (x - r)ᵀQ(x - r)} dt + x(T)ᵀSx(T)`
(Sontag eq. (8.41)). The optimality is established by the completion-of-squares
identity for the affine (quadratic-plus-linear) value function
`W(x) = xᵀPx + 2 xᵀ β + α`, which is the algebraic content of Sontag
eqs. (8.37)–(8.41). Writing `S` for the square, the pointwise identity is

`dW/dt + {uᵀRu + (x - r)ᵀQ(x - r)} = S + (rᵀQr - βᵀ B R⁻¹ Bᵀ β)`,

so the optimal law makes `S = 0` and the accumulated cost is exactly the
boundary term. The full finite-horizon problem (a `sInf` over admissible
trajectories, cf. `ContinuousOCP`) is not formalized here; this file states the
completion-of-squares identity at the pointwise algebraic / state-space level,
which is the standard optimality certificate.

## Deterministic estimation and duality (Sontag §8.3, printed pp. 375–378)

For the plant `ẋ = A x + B u`, `y = C x`, the minimum-energy estimator minimises
the noise energy `∫ vᵀV v + wᵀW w` subject to `ẋ̂ = A x̂ + B u + v` and
`y = C x̂ + w`. The estimation Riccati equation, the observer gain and the
linear-quadratic duality are

* `estimationRiccati A C V W P` — the dual continuous algebraic Riccati equation
  `A P + P Aᵀ - P Cᵀ W⁻¹ C P + V = 0`;
* `observerGain C W P` — the observer gain `P Cᵀ W⁻¹` (Sontag's filtering gain
  `L = -ΠCᵀQ`, printed p. 378);
* `estimation_dual_lqr` — the estimation Riccati equation is *exactly* the LQR
  `care` of the dual system `(Aᵀ, Cᵀ)` with weights `(V, W)`.

The duality is definitional, mirroring `mhe_dual_lqr` in
`DynamicalSystems.Control.MPC.Estimation` (which is deliberately not imported:
the continuous theory lives in `OptimalControl/ContinuousTime`, per the P5
layering rule).

## Main definitions

* `trackingProblem`: the standing data and algebraic hypotheses of the affine
  continuous-time tracking problem.
* `trackingOptimalControl`: the affine feedback-plus-feedforward law (8.41).
* `estimationRiccati`: the dual continuous algebraic Riccati equation.
* `observerGain`: the deterministic (Kalman) observer gain `P Cᵀ W⁻¹`.

## Main results

* `tracking_completion_of_squares`: the pointwise completion-of-squares identity.
* `trackingOptimalControl_optimal`: at the affine law the square vanishes, giving
  the optimal tracking cost identity.
* `estimation_dual_lqr`: estimation/regulation duality of the Riccati equations.
-/

@[expose] public section

open Matrix

variable {n m p : ℕ}

/-! ## Tracking -/

/-- The standing data and algebraic hypotheses of the affine continuous-time
tracking problem for a constant setpoint `r`: `P` is a symmetric solution of the
continuous algebraic Riccati equation, `Q` and `R` are symmetric, and `β`
satisfies the steady-state affine feedforward/adjoint equation
`(A - B R⁻¹BᵀP)ᵀ β = Q r` (Sontag, *Mathematical Control Theory*, 2nd ed., 1998,
Ch. 8 §8.3, eq. (8.38), printed p. 373; the `ϕ ≡ 0`, time-invariant case).

The pair `(P, β)` determines the affine value function `xᵀPx + 2 xᵀβ + α` and the
optimal tracking law `u = -R⁻¹Bᵀ(P x + β)`. -/
def trackingProblem (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) [Invertible R]
    (r : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (β : Fin n → ℝ) : Prop :=
  care A B Q R P ∧ Pᵀ = P ∧ Qᵀ = Q ∧ Rᵀ = R ∧
    (A - B * continuousLQRGain A B R P)ᵀ *ᵥ β = Q *ᵥ r

/-- The continuous-time optimal tracking law (Sontag, *Mathematical Control
Theory*, 2nd ed., 1998, Ch. 8 §8.3, eq. (8.41), printed p. 374):
`u = -R⁻¹Bᵀ(P x + β)`, the affine feedback-plus-feedforward law built from the
Riccati solution `P` and the feedforward vector `β` of `trackingProblem`.
Writing `g = -β`, this is the form `u = -R⁻¹Bᵀ(P x - g)` of the task statement. -/
noncomputable def trackingOptimalControl (B : Matrix (Fin n) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) [Invertible R] (P : Matrix (Fin n) (Fin n) ℝ)
    (β : Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  -((⅟R * Bᵀ) *ᵥ (P *ᵥ x + β))

/-- Pointwise completion of squares for the continuous-time affine tracking
problem. With `K := R⁻¹BᵀP` and `β` satisfying `(A - B K)ᵀ β = Q r`, and with the
affine value function `W(x) = xᵀPx + 2 xᵀβ`,

`ẋᵀ(Px) + xᵀPẋ + 2 ẋᵀβ + {uᵀRu + (x - r)ᵀQ(x - r)}
   = (u + K x + R⁻¹Bᵀβ)ᵀ R (u + K x + R⁻¹Bᵀβ) + (rᵀQr - βᵀ B R⁻¹ Bᵀ β)`,

where `ẋ = A x + B u`. Equivalently, the derivative of `W` along the plant plus
the tracking running cost equals a perfect square plus a constant. This is the
algebraic content of Sontag, *Mathematical Control Theory*, 2nd ed., 1998,
Ch. 8 §8.3, eqs. (8.37)–(8.39), printed pp. 373–374. -/
theorem tracking_completion_of_squares
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) [Invertible R]
    (P : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (β : Fin n → ℝ)
    (hcare : care A B Q R P) (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hR : Rᵀ = R)
    (hβ : (A - B * continuousLQRGain A B R P)ᵀ *ᵥ β = Q *ᵥ r)
    (x : Fin n → ℝ) (u : Fin m → ℝ) :
    (A *ᵥ x + B *ᵥ u) ⬝ᵥ (P *ᵥ x) + x ⬝ᵥ (P *ᵥ (A *ᵥ x + B *ᵥ u)) +
        2 * ((A *ᵥ x + B *ᵥ u) ⬝ᵥ β) + u ⬝ᵥ (R *ᵥ u) +
        (x - r) ⬝ᵥ (Q *ᵥ (x - r)) =
      (u + (⅟R * Bᵀ) *ᵥ (P *ᵥ x + β)) ⬝ᵥ
          (R *ᵥ (u + (⅟R * Bᵀ) *ᵥ (P *ᵥ x + β))) +
        (r ⬝ᵥ (Q *ᵥ r) - β ⬝ᵥ ((B * ⅟R * Bᵀ) *ᵥ β)) := by
  -- transpose of the inverse weight is itself
  have hRt : (⅟R : Matrix (Fin m) (Fin m) ℝ)ᵀ = ⅟R := by
    rw [invOf_eq_nonsing_inv, transpose_nonsing_inv, hR, ← invOf_eq_nonsing_inv]
  -- transpose of the LQR gain
  have hKt : (continuousLQRGain A B R P)ᵀ = P * B * ⅟R := by
    unfold continuousLQRGain
    rw [transpose_mul, transpose_mul, transpose_transpose, hP, hRt]
    simp only [Matrix.mul_assoc]
  -- CARE, rearranged
  have hcare_sub : Aᵀ * P + P * A = P * B * ⅟R * Bᵀ * P - Q := by
    have h : Aᵀ * P + P * A - P * B * R⁻¹ * Bᵀ * P + Q = 0 := hcare
    rw [← invOf_eq_nonsing_inv] at h
    have h_neg : Aᵀ * P + P * A - P * B * ⅟R * Bᵀ * P = -Q :=
      add_eq_zero_iff_eq_neg.mp h
    have h3 : Aᵀ * P + P * A = -Q + P * B * ⅟R * Bᵀ * P := sub_eq_iff_eq_add.mp h_neg
    rw [h3]; abel
  -- feedforward equation, rearranged
  have hβ' : Aᵀ *ᵥ β = (P * B * ⅟R * Bᵀ) *ᵥ β + Q *ᵥ r := by
    have h := hβ
    rw [transpose_sub, transpose_mul, hKt] at h
    rw [Matrix.sub_mulVec] at h
    rw [sub_eq_iff_eq_add] at h
    rw [add_comm] at h
    exact h
  -- elementary dot-product movement identities
  have hAP : (A *ᵥ x) ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ ((Aᵀ * P) *ᵥ x) := by
    rw [dotProduct_comm, dotProduct_mulVec_comp A (P *ᵥ x) x, Matrix.mulVec_mulVec]
  have hBP : (B *ᵥ u) ⬝ᵥ (P *ᵥ x) = u ⬝ᵥ ((Bᵀ * P) *ᵥ x) := by
    rw [dotProduct_comm, dotProduct_mulVec_comp B (P *ᵥ x) u, Matrix.mulVec_mulVec]
  have hPA : x ⬝ᵥ (P *ᵥ (A *ᵥ x)) = x ⬝ᵥ ((P * A) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec]
  have hPB : x ⬝ᵥ (P *ᵥ (B *ᵥ u)) = u ⬝ᵥ ((Bᵀ * P) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, dotProduct_mulVec_comp (P * B) x u]
    congr 1
    rw [transpose_mul, hP]
  have hAb : (A *ᵥ x) ⬝ᵥ β = x ⬝ᵥ (Aᵀ *ᵥ β) := by
    rw [dotProduct_comm, dotProduct_mulVec_comp A β x]
  have hBb : (B *ᵥ u) ⬝ᵥ β = u ⬝ᵥ (Bᵀ *ᵥ β) := by
    rw [dotProduct_comm, dotProduct_mulVec_comp B β u]
  -- combination of the `A` terms
  have hxAPA : x ⬝ᵥ ((Aᵀ * P) *ᵥ x) + x ⬝ᵥ ((P * A) *ᵥ x) =
      x ⬝ᵥ ((P * B * ⅟R * Bᵀ * P) *ᵥ x) - x ⬝ᵥ (Q *ᵥ x) := by
    rw [← dotProduct_add, ← Matrix.add_mulVec, hcare_sub, Matrix.sub_mulVec, dotProduct_sub]
  -- quadratic expansion of the shifted state
  have hQexp : (x - r) ⬝ᵥ (Q *ᵥ (x - r)) =
      x ⬝ᵥ (Q *ᵥ x) - 2 * (x ⬝ᵥ (Q *ᵥ r)) + r ⬝ᵥ (Q *ᵥ r) := by
    have hsym : r ⬝ᵥ (Q *ᵥ x) = x ⬝ᵥ (Q *ᵥ r) := quadForm_dotProduct_symm Q hQ r x
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hsym]
    ring
  -- the first three (differential) terms of the left-hand side
  have hT123 : (A *ᵥ x + B *ᵥ u) ⬝ᵥ (P *ᵥ x) +
        x ⬝ᵥ (P *ᵥ (A *ᵥ x + B *ᵥ u)) + 2 * ((A *ᵥ x + B *ᵥ u) ⬝ᵥ β) =
      x ⬝ᵥ ((Aᵀ * P) *ᵥ x) + x ⬝ᵥ ((P * A) *ᵥ x) +
        2 * (u ⬝ᵥ ((Bᵀ * P) *ᵥ x)) + 2 * (x ⬝ᵥ (Aᵀ *ᵥ β)) +
        2 * (u ⬝ᵥ (Bᵀ *ᵥ β)) := by
    rw [add_dotProduct, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
      hAP, hPA, hBP, hPB, hAb, hBb]
    ring
  -- the square of the optimal control direction
  have hq : u + (⅟R * Bᵀ) *ᵥ (P *ᵥ x + β) =
      (u + (⅟R * Bᵀ) *ᵥ β) + continuousLQRGain A B R P *ᵥ x := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
    unfold continuousLQRGain
    abel
  have hsquare : (u + (⅟R * Bᵀ) *ᵥ (P *ᵥ x + β)) ⬝ᵥ
        (R *ᵥ (u + (⅟R * Bᵀ) *ᵥ (P *ᵥ x + β))) =
      (u + (⅟R * Bᵀ) *ᵥ β) ⬝ᵥ (R *ᵥ (u + (⅟R * Bᵀ) *ᵥ β)) +
        2 * ((u + (⅟R * Bᵀ) *ᵥ β) ⬝ᵥ ((Bᵀ * P) *ᵥ x)) +
        x ⬝ᵥ ((P * B * ⅟R * Bᵀ * P) *ᵥ x) := by
    rw [hq]
    exact completion_of_squares_algebraic A B R P hP hR x (u + (⅟R * Bᵀ) *ᵥ β)
  -- reduction of the square by expanding the feedforward vector
  have hRc : R *ᵥ ((⅟R * Bᵀ) *ᵥ β) = Bᵀ *ᵥ β := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  have hcRc : ((⅟R * Bᵀ) *ᵥ β) ⬝ᵥ (R *ᵥ ((⅟R * Bᵀ) *ᵥ β)) =
      β ⬝ᵥ ((B * ⅟R * Bᵀ) *ᵥ β) := by
    rw [hRc, dotProduct_comm, dotProduct_mulVec_comp (⅟R * Bᵀ) (Bᵀ *ᵥ β) β]
    congr 1
    rw [transpose_mul, transpose_transpose, hRt, Matrix.mulVec_mulVec]
  have hwRw : (u + (⅟R * Bᵀ) *ᵥ β) ⬝ᵥ (R *ᵥ (u + (⅟R * Bᵀ) *ᵥ β)) =
      u ⬝ᵥ (R *ᵥ u) + 2 * (u ⬝ᵥ (Bᵀ *ᵥ β)) + β ⬝ᵥ ((B * ⅟R * Bᵀ) *ᵥ β) := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
    rw [quadForm_dotProduct_symm R hR ((⅟R * Bᵀ) *ᵥ β) u, hcRc, hRc]
    ring
  have hcP : ((⅟R * Bᵀ) *ᵥ β) ⬝ᵥ ((Bᵀ * P) *ᵥ x) =
      β ⬝ᵥ ((B * ⅟R * Bᵀ * P) *ᵥ x) := by
    rw [dotProduct_comm, dotProduct_mulVec_comp (⅟R * Bᵀ) ((Bᵀ * P) *ᵥ x) β]
    congr 1
    rw [transpose_mul, transpose_transpose, hRt, Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]
  have hwP : (u + (⅟R * Bᵀ) *ᵥ β) ⬝ᵥ ((Bᵀ * P) *ᵥ x) =
      u ⬝ᵥ ((Bᵀ * P) *ᵥ x) + β ⬝ᵥ ((B * ⅟R * Bᵀ * P) *ᵥ x) := by
    rw [add_dotProduct, hcP]
  -- the feedforward term in the `A`-transpose expression
  have hM : (B * ⅟R * Bᵀ * P)ᵀ = P * B * ⅟R * Bᵀ := by
    rw [transpose_mul, transpose_mul, transpose_mul, transpose_transpose, hP, hRt]
    simp only [Matrix.mul_assoc]
  have hv : x ⬝ᵥ ((P * B * ⅟R * Bᵀ) *ᵥ β) = β ⬝ᵥ ((B * ⅟R * Bᵀ * P) *ᵥ x) := by
    rw [← hM]
    exact (dotProduct_mulVec_comp (B * ⅟R * Bᵀ * P) β x).symm
  -- assemble
  rw [hsquare, hT123, hQexp, hwRw, hwP, hxAPA, hβ', dotProduct_add, hv]
  ring

/-- **Optimality of the affine continuous-time tracking law.** At
`u = trackingOptimalControl B R P β x` the completion-of-squares square vanishes,
so the derivative of the affine value function plus the tracking running cost is
the constant `rᵀQr - βᵀ B R⁻¹ Bᵀ β`; along the resulting trajectory the tracking
cost equals the boundary value of `xᵀPx + 2xᵀβ` up to that constant, which is the
completion-of-squares optimality certificate of Sontag, *Mathematical Control
Theory*, 2nd ed., 1998, Ch. 8 §8.3, Theorem 38, printed p. 374. -/
theorem trackingOptimalControl_optimal
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) [Invertible R]
    (P : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (β : Fin n → ℝ)
    (hcare : care A B Q R P) (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hR : Rᵀ = R)
    (hβ : (A - B * continuousLQRGain A B R P)ᵀ *ᵥ β = Q *ᵥ r)
    (x : Fin n → ℝ) :
    (A *ᵥ x + B *ᵥ (trackingOptimalControl B R P β x)) ⬝ᵥ (P *ᵥ x) +
        x ⬝ᵥ (P *ᵥ (A *ᵥ x + B *ᵥ (trackingOptimalControl B R P β x))) +
        2 * ((A *ᵥ x + B *ᵥ (trackingOptimalControl B R P β x)) ⬝ᵥ β) +
        (trackingOptimalControl B R P β x) ⬝ᵥ
          (R *ᵥ (trackingOptimalControl B R P β x)) +
        (x - r) ⬝ᵥ (Q *ᵥ (x - r)) =
      r ⬝ᵥ (Q *ᵥ r) - β ⬝ᵥ ((B * ⅟R * Bᵀ) *ᵥ β) := by
  have hcs := tracking_completion_of_squares A B Q R P r β hcare hP hQ hR hβ x
    (trackingOptimalControl B R P β x)
  have hq0 : trackingOptimalControl B R P β x + (⅟R * Bᵀ) *ᵥ (P *ᵥ x + β) = 0 := by
    unfold trackingOptimalControl
    rw [neg_add_cancel]
  rw [hcs, hq0]
  simp

/-! ## Deterministic estimation and duality -/

/-- The dual continuous algebraic Riccati equation of deterministic
(minimum-energy) estimation, for the plant `ẋ = A x + B u` with output
`y = C x`, process-noise weight `V` and dual input (measurement) weight `W`:
`A P + P Aᵀ - P Cᵀ W⁻¹ C P + V = 0`. It is the continuous-time counterpart of
`mheRiccati` and is *definitionally* the LQR `care` of the dual system
`(Aᵀ, Cᵀ)` with weights `(V, W)` (`estimation_dual_lqr`).

Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.3, eq. (FRDE)
(printed p. 378) and Theorem 40; Crassidis & Junkins, *Optimal Estimation of
Dynamic Systems*, Ch. 3. -/
noncomputable def estimationRiccati (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (V : Matrix (Fin n) (Fin n) ℝ)
    (W : Matrix (Fin p) (Fin p) ℝ) [Invertible W] (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A * P + P * Aᵀ - P * Cᵀ * ⅟W * C * P + V = 0

/-- **Duality of continuous-time estimation and regulation.**
The estimation Riccati equation `estimationRiccati A C V W P` holds if and only if
the continuous algebraic Riccati equation `care` of the *dual* linear-quadratic
problem — state matrix `Aᵀ`, input matrix `Cᵀ`, state weight `V`, input weight
`W` — holds. The two equations are the same after cancelling the double
transposes and identifying the `Invertible` inverse `⅟W` with the matrix inverse
`W⁻¹` of `care`.

This is the continuous-time counterpart of `mhe_dual_lqr` in
`DynamicalSystems.Control.MPC.Estimation`, restated here for the continuous
`care` (Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.3,
printed pp. 375–378; the estimation/regulation duality of Table 4.2 of
Rawlings–Mayne–Diehl is the discrete analogue). -/
theorem estimation_dual_lqr (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (V : Matrix (Fin n) (Fin n) ℝ)
    (W : Matrix (Fin p) (Fin p) ℝ) [Invertible W] (P : Matrix (Fin n) (Fin n) ℝ) :
    estimationRiccati A C V W P ↔ care Aᵀ Cᵀ V W P := by
  unfold estimationRiccati care
  simp only [transpose_transpose, invOf_eq_nonsing_inv]

/-- The deterministic (Kalman) observer gain `K = P Cᵀ W⁻¹` of Sontag,
*Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.3 (the filtering gain
`L = -ΠCᵀQ` of the summary on printed p. 378, with `W` the measurement weight and
`P` the solution of `estimationRiccati`). The inverse `W⁻¹` is the dual input
weight, matching the `⅟W` that appears in `estimationRiccati`. -/
noncomputable def observerGain (C : Matrix (Fin p) (Fin n) ℝ)
    (W : Matrix (Fin p) (Fin p) ℝ) [Invertible W] (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin p) ℝ :=
  P * Cᵀ * ⅟W

/-- The transpose of the deterministic observer gain `P Cᵀ W⁻¹` is `(W⁻¹)ᵀ C Pᵀ`. -/
theorem observerGain_transpose (C : Matrix (Fin p) (Fin n) ℝ)
    (W : Matrix (Fin p) (Fin p) ℝ) [Invertible W] (P : Matrix (Fin n) (Fin n) ℝ) :
    (observerGain C W P)ᵀ = (⅟W)ᵀ * C * Pᵀ := by
  unfold observerGain
  rw [transpose_mul, transpose_mul, transpose_transpose]
  simp only [Matrix.mul_assoc]

/-- **Duality of the observer gain and the dual LQR gain.** For a symmetric
measurement weight `W` (`Wᵀ = W`) and a symmetric Riccati solution `P`
(`Pᵀ = P`), the transpose of the deterministic observer gain is exactly the
continuous LQR gain of the dual system `(Aᵀ, Cᵀ)`:
`(P Cᵀ W⁻¹)ᵀ = ⅟W C P = continuousLQRGain Aᵀ Cᵀ W P`. The observer gain
`P Cᵀ W⁻¹` is thus the transpose of the dual regulation gain, mirroring the
filtering gain `L = -ΠCᵀQ` of Sontag, *Mathematical Control Theory*, 2nd ed.,
1998, Ch. 8 §8.3 (printed pp. 377–378) and the estimation Riccati equation
`estimationRiccati A C V W P`. -/
theorem observerGain_dual_lqr (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (W : Matrix (Fin p) (Fin p) ℝ) [Invertible W]
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (hW : Wᵀ = W) :
    (observerGain C W P)ᵀ = continuousLQRGain Aᵀ Cᵀ W P := by
  have hWt : (⅟W : Matrix (Fin p) (Fin p) ℝ)ᵀ = ⅟W := by
    rw [invOf_eq_nonsing_inv, transpose_nonsing_inv, hW, ← invOf_eq_nonsing_inv]
  unfold observerGain continuousLQRGain
  simp only [transpose_mul, transpose_transpose, hP, hWt, Matrix.mul_assoc]
