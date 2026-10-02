/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.Discrete
public import DynamicalSystems.DiscreteTime.MatrixLyapunov
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Matrix/vector regular-form discrete-time sliding-mode control

This file formalizes the algebraic core of the *regular form*-based and
*equivalent-control* design of discrete-time sliding-mode control (DSMC) for the
multi-input linear time-invariant plant

`x(k + 1) = A x(k) + B u(k) + d(k)`,

with `A : Matrix (Fin n) (Fin n) ℝ`, `B : Matrix (Fin n) (Fin m) ℝ`, state
`x(k) : Fin n → ℝ` and input `u(k) : Fin m → ℝ`, of A. Argha, S. W. Su, L. Li
and H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory and
Applications*, CRC Press 2018. The relevant printed pages are Chapter 1, §1.2
"Regular form-based DSMC", eqs. (1.19), (1.24), (1.38) (printed pp. 20–22), and
Chapter 2, §2.2–2.4, eqs. (2.1)–(2.16) (printed pp. 29–35).

The *sliding variable* is the linear function `s(k) = C x(k)` of the state
(Chapter 2, eq. (2.6), printed p. 31; equivalently eq. (1.24), printed p. 21),
where the book writes the surface matrix as `S` and we write it `C`. The discrete
*equivalent control* is the input that annihilates the one-step propagation of
the sliding variable,

`u_eq(k) = -(C * B)⁻¹ (C A x(k))`,

the `Φ = 0` instance of the direct control law (1.38), printed p. 22 (linear part
of (2.12), printed p. 31). It is unique as soon as `C * B` is invertible. Closing
the loop by `u = u_eq` yields the equivalent closed-loop matrix
`A - B (C B)⁻¹ C A` (cf. `Â = B (SB)⁻¹ S A` and eq. (2.22), printed p. 34), for
which the sliding variable vanishes identically — the surface `{s = 0}` is
invariant.

The final pair of declarations records the one-step disturbance estimate

`d̂(k) = x(k + 1) - A x(k) - B u(k)`,

computed from the measured state and input. It is the state-space counterpart of
the disturbance observer `f̂(k) = (SB)⁻¹ S[x(k) - A x(k-1) - B u(k-1)]` (eq.
(2.16), printed p. 33), from which an exact estimate of the matched disturbance is
recovered when the plant model holds.

The scalar (single-channel) reaching law, the quasi-sliding band and their
invariance/contraction properties are deliberately *not* repeated here: they
live in `DynamicalSystems.Control.SlidingMode.Discrete` (Gao's reaching law and
its forward invariance of the quasi-sliding band), and the continuous-time
equivalent control in `DynamicalSystems.Control.SlidingMode.Basic`. Likewise the
discrete matrix-Lyapunov quadratic-form toolkit is reused from
`DynamicalSystems.DiscreteTime.MatrixLyapunov`. The matrix/vector statements
below are the new regular-form content of this slice.

## Main definitions

* `dsmcSlidingVariable`: the vector sliding variable `s = C x`.
* `dsmcEquivalentControl`: the discrete equivalent control `u_eq`.
* `dsmcEquivalentClosedLoop`: the equivalent closed-loop matrix.
* `dsmcDisturbanceEstimate`: the one-step state-space disturbance estimate.

## Main results

* `dsmcEquivalentControl_spec`: the equivalent control drives `s` to `0` in one step.
* `dsmcEquivalentControl_unique`: it is the unique input with that property.
* `dsmcEquivalentClosedLoop_slidingVariable`: the surface `{s = 0}` is invariant.
* `dsmcDisturbanceEstimate_spec`: the estimate recovers the exact disturbance.

## Implementation notes

The task statement describes the input history of `dsmcDisturbanceEstimate` as
`ℕ → Fin n → ℝ`; here it is typed `ℕ → Fin m → ℝ`, which is the dimension
consistent with the plant input `u(k) : Fin m → ℝ` and with `B : Matrix (Fin n)
(Fin m) ℝ`. Similarly `dsmcDisturbanceEstimate_spec` is stated for an input
history in `Fin m`.
-/

@[expose] public section

open Matrix

variable {n m : ℕ}

/-- The vector sliding variable `s(k) = C x(k)` of A. Argha, S. W. Su, L. Li and
H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory and
Applications*, CRC Press 2018, eq. (2.6), printed p. 31 (equivalently eq. (1.24),
printed p. 21); the book's surface matrix `S` is written `C` here. -/
def dsmcSlidingVariable (C : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  C *ᵥ x

/-- The `i`-th entry of the sliding variable is the `i`-th row of `C` dotted with
the state: `(C x) i = ∑ j, C i j * x j`. This is the componentwise unfolding of
eq. (2.6), printed p. 31. -/
@[simp] theorem dsmcSlidingVariable_apply (C : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin m) : dsmcSlidingVariable C x i = C.row i ⬝ᵥ x := by
  simp only [dsmcSlidingVariable, Matrix.mulVec_apply]

/-- The discrete *equivalent control* `u_eq(k) = -(C * B)⁻¹ (C A x(k))`, the input
that sets the one-step propagation `s(k+1) = C (A x(k) + B u(k))` of the sliding
variable to zero. It is the `Φ = 0` instance of the direct control law (1.38),
printed p. 22, and the linear part of the control law (2.12), printed p. 31, of
A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding
Mode Control: Theory and Applications*, CRC Press 2018. -/
noncomputable def dsmcEquivalentControl (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  -((C * B)⁻¹ *ᵥ (C *ᵥ (A *ᵥ x)))

/-- The equivalent control places the sliding variable exactly on the surface in
one step: `s(k+1) = C (A x + B u_eq) = 0`, which is the ideal-sliding condition
`σ_x(k + 1) = σ_x(k) = 0` of eq. (2.7), printed p. 31, and the discrete
counterpart of the equivalent-control identity of
`DynamicalSystems.Control.SlidingMode.Basic`. The hypothesis `IsUnit (C * B).det`
says that `C * B` is invertible, i.e. the product `S B` of eq. (1.38) is
nonsingular (printed p. 22). -/
theorem dsmcEquivalentControl_spec (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) (hb : IsUnit (C * B).det) (x : Fin n → ℝ) :
    dsmcSlidingVariable C (A *ᵥ x + B *ᵥ dsmcEquivalentControl A B C x) = 0 := by
  unfold dsmcSlidingVariable dsmcEquivalentControl
  rw [Matrix.mulVec_add]
  rw [Matrix.mulVec_mulVec _ C B]
  rw [Matrix.mulVec_neg]
  rw [Matrix.mulVec_mulVec _ (C * B) (C * B)⁻¹]
  rw [Matrix.mul_nonsing_inv _ hb, Matrix.one_mulVec]
  abel

/-- The equivalent control is the *unique* input driving the sliding variable to
zero in one step: if `s(k+1) = C (A x + B u) = 0` then `u = u_eq`. This is the
well-posedness of the ideal-sliding input `u_eq(k) = -(SB)⁻¹ SA x(k)` of eq.
(2.12), printed p. 31, under the invertibility of `C * B` (= `S B`). -/
theorem dsmcEquivalentControl_unique (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) (hb : IsUnit (C * B).det) (x : Fin n → ℝ) {u : Fin m → ℝ}
    (hu : dsmcSlidingVariable C (A *ᵥ x + B *ᵥ u) = 0) :
    u = dsmcEquivalentControl A B C x := by
  have h1 : (C * B) *ᵥ u = -(C *ᵥ (A *ᵥ x)) := by
    have h2 := hu
    rw [dsmcSlidingVariable, Matrix.mulVec_add] at h2
    rw [Matrix.mulVec_mulVec u C B] at h2
    exact eq_neg_of_add_eq_zero_right h2
  calc u = (C * B)⁻¹ *ᵥ ((C * B) *ᵥ u) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hb, Matrix.one_mulVec]
    _ = (C * B)⁻¹ *ᵥ (-(C *ᵥ (A *ᵥ x))) := by rw [h1]
    _ = -((C * B)⁻¹ *ᵥ (C *ᵥ (A *ᵥ x))) := by rw [Matrix.mulVec_neg]
    _ = dsmcEquivalentControl A B C x := rfl

/-- The *equivalent closed-loop matrix* `A - B (C B)⁻¹ C A` obtained by applying
the equivalent control `u_eq` to the disturbance-free plant,
`x(k+1) = (A - B (C B)⁻¹ C A) x(k)`. This is the state-space form of eq. (2.22),
printed p. 34, with `Â = B (SB)⁻¹ S A` and `A - Â` in the book's notation
(`S = C`). -/
noncomputable def dsmcEquivalentClosedLoop (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A - B * (C * B)⁻¹ * C * A

/-- With the equivalent control the sliding surface is invariant: the
disturbance-free equivalent closed loop maps the surface `{x | C x = 0}` into
itself, `C ((A - B (C B)⁻¹ C A) x) = 0`. This is the ideal-sliding invariance
`σ_x(k + 1) = 0` on `σ_x(k) = 0` behind eqs. (2.7) and (2.23) (printed pp. 31
and 34). -/
theorem dsmcEquivalentClosedLoop_slidingVariable (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) (hb : IsUnit (C * B).det)
    (x : Fin n → ℝ) :
    dsmcSlidingVariable C (dsmcEquivalentClosedLoop A B C *ᵥ x) = 0 := by
  have hCX : C * (B * (C * B)⁻¹ * C * A) = C * A := by
    have h1 : C * (B * (C * B)⁻¹ * C * A) = (C * B) * (C * B)⁻¹ * (C * A) := by
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_nonsing_inv _ hb, Matrix.one_mul]
  have hCM : C * dsmcEquivalentClosedLoop A B C = 0 := by
    rw [dsmcEquivalentClosedLoop, Matrix.mul_sub, hCX, sub_self]
  unfold dsmcSlidingVariable
  rw [Matrix.mulVec_mulVec _ C (dsmcEquivalentClosedLoop A B C), hCM, Matrix.zero_mulVec]

/-- The one-step disturbance estimate `d̂(k) = x(k + 1) - A x(k) - B u(k)` from the
measured successor state and the applied input. It is the state-space counterpart
of the disturbance observer `f̂(k) = (SB)⁻¹ S[x(k) - A x(k-1) - B u(k-1)]` of
A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding
Mode Control: Theory and Applications*, CRC Press 2018, eq. (2.16), printed p. 33
(§2.3.1.1, the disturbance-estimator used in §2.4). -/
noncomputable def dsmcDisturbanceEstimate (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (x : ℕ → Fin n → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) : Fin n → ℝ :=
  x (k + 1) - A *ᵥ x k - B *ᵥ u k

/-- For an exact model `x(k + 1) = A x(k) + B u(k) + d(k)`, the one-step estimate
recovers the disturbance exactly: `d̂(k) = d(k)`. This records the algebraic
identity underlying the disturbance observer (2.15)–(2.16), printed p. 33. -/
theorem dsmcDisturbanceEstimate_spec (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (x d : ℕ → Fin n → ℝ) (u : ℕ → Fin m → ℝ)
    (h : ∀ k, x (k + 1) = A *ᵥ x k + B *ᵥ u k + d k) (k : ℕ) :
    dsmcDisturbanceEstimate A B x u k = d k := by
  unfold dsmcDisturbanceEstimate
  rw [h k]
  abel
