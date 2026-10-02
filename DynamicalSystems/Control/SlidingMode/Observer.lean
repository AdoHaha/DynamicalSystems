/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.Differentiator

/-! # Higher-order sliding-mode observer

This file records the high-order sliding-mode **observer** of L. Fridman, A. Levant and
J. Davila, *Observation and Identification Via High-Order Sliding Modes*, Chapter 14 of
G. Bartolini, L. Fridman, A. Pisano and E. Usai (eds.), *Modern Sliding Mode Control
Theory: New Perspectives and Applications*, LNCIS 375, Springer 2008, printed pp. 293–305
(PDF pp. 309–321).

For the canonical observable double-integrator system `ẋ₀ = x₁`, `ẋ₁ = 0` with measured
output `y = x₀`, the super-twisting differentiator of
`DynamicalSystems.Control.SlidingMode.Differentiator` driven by `y` is an observer for the
full state `(x₀, x₁)`: in the estimate `z = (z₀, z₁)` the field is the super-twisting
differentiator field `superTwistingDifferentiatorField k₁ k₂ y`, and the observation error
`z - x` is exactly the differentiator error `(z₀ - y, z₁ - y')`.  When the observation
error vanishes the estimate coincides with the state, i.e. the reconstruction is exact.

## Main definitions

* `observationError`: the observation error `z - x` between estimate and state.
* `superTwistingObserverField`: the super-twisting observer field, driven by the output
  `y`, which is the differentiator field of the measured signal.

## Main statements

* `observationError_eq_differentiatorError`: the observation error is the differentiator
  error of the measured output.
* `state_reconstruction_exact`: a vanishing observation error gives exact state
  reconstruction.

## Scope

Only the canonical observable double integrator is formalised here.  The full
Chapter 14 LTISUI matrix-pencil theory, noise-corrupted exactness and classical
differentiation through `e₀ = 0` are deliberately out of scope. -/

@[expose] public section

/-! ## Canonical observable system -/

/-- The **observation error** `z - x` between the observer estimate `z` and the state `x`
of the canonical observable double integrator `(x₀, x₁)`. -/
noncomputable def observationError (z x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  z - x

/-- The **super-twisting observer field** driven by the measured output `y`: on the
estimate `z` of `(x₀, x₁)` it is the super-twisting differentiator field of the signal
with current measured value `y`.  Its first channel corrects `z₀` towards `y` while the
second channel estimates `ẏ = x₁`. -/
noncomputable def superTwistingObserverField (k₁ k₂ : ℝ) (y : ℝ) (z : Fin 2 → ℝ) :
    Fin 2 → ℝ :=
  superTwistingDifferentiatorField k₁ k₂ y z

/-- The observation error of the canonical observable system is exactly the
differentiator error of the measured output `(x 0, x 1)`: both are `(z₀ - y, z₁ - y')`. -/
theorem observationError_eq_differentiatorError (z x : Fin 2 → ℝ) :
    observationError z x = differentiatorError (x 0) (x 1) z := by
  funext i
  fin_cases i <;>
    simp only [observationError, differentiatorError, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.reduceFinMk]

/-- **Closed-loop observation-error identity for the canonical observable system.**
Subtracting the state drift `![x 1, 0]` from the observer field and reading the result in
the observation-error coordinates is exactly slice S7's super-twisting vector field:
`ż - ![x₁, 0] = superTwistingVectorField k₁ k₂ (z - x)`. -/
theorem superTwistingObserver_error_eq_superTwistingVectorField
    (k₁ k₂ : ℝ) (x z : Fin 2 → ℝ) :
    superTwistingObserverField k₁ k₂ (x 0) z - ![x 1, 0] =
      superTwistingVectorField k₁ k₂ (observationError z x) := by
  rw [superTwistingObserverField,
    superTwistingDifferentiator_error_eq_superTwistingVectorField,
    observationError_eq_differentiatorError]

/-- **Exact state reconstruction for the canonical observable system.** If the observation
error vanishes then the estimate coincides with the state, so both components are
reconstructed exactly: `z₀ = x₀` and `z₁ = x₁`. -/
theorem state_reconstruction_exact (z x : Fin 2 → ℝ) (h : observationError z x = 0) :
    z 0 = x 0 ∧ z 1 = x 1 := by
  have hz : z = x := sub_eq_zero.mp (by simpa only [observationError] using h)
  subst hz
  exact ⟨rfl, rfl⟩
