/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Gramian
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The finite-horizon Lyapunov integral

For a real finite-dimensional linear time-invariant system `x' = A x` and a
continuous endomorphism `Q` of the state space we define the finite-horizon
Lyapunov integral

```
P(T) = ∫₀ᵀ exp(s A)* Q exp(s A) ds,
```

as a continuous linear endomorphism of the state space, obtained by integrating
the continuous operator-valued integrand `s ↦ exp(s A)* Q exp(s A)`. The main
results are the energy identity

```
⟪x, P(T) x⟫ = ∫₀ᵀ ⟪exp(s A) x, Q (exp(s A) x)⟫ ds
```

and the positive semidefiniteness of `P(T)` on a nonnegative horizon whenever
`Q` is positive semidefinite. These are the building blocks for the infinite
horizon limit and the algebraic Lyapunov equation `A* P + P A = -Q`, which are
treated in a later slice.

## Main definitions

* `lyapunovIntegral`

## Main results

* `inner_lyapunovIntegral`
* `lyapunovIntegral_nonneg`

## References

* J. Kabziński, P. Mosiołek, *Projektowanie nieliniowych układów sterowania*,
  Komitet Automatyki i Robotyki PAN, Monografie tom 22, Chapter 2, equation
  (2.40).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Interval InnerProduct

variable {X : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

/-! ### Definition -/

/-- The finite-horizon Lyapunov integral
`P(T) = ∫₀ᵀ exp(s A)* Q exp(s A) ds`, as a continuous endomorphism of the state
space. Source: Kabziński–Mosiołek, equation (2.40). -/
noncomputable def lyapunovIntegral (A Q : X →L[ℝ] X) (T : ℝ) : X →L[ℝ] X :=
  ∫ s in (0 : ℝ)..T,
    (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
      (Q.comp (NormedSpace.exp (s • A)))

/-! ### Continuity of the integrand -/

/-- The Lyapunov integral integrand `s ↦ exp(s A)* Q exp(s A)` is continuous in
time. -/
theorem continuous_lyapunovIntegrand (A Q : X →L[ℝ] X) :
    Continuous (fun s : ℝ =>
      (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
        (Q.comp (NormedSpace.exp (s • A)))) := by
  have hE : Continuous (fun s : ℝ => NormedSpace.exp (s • A)) :=
    (differentiable_exp_smul_const ℝ A).continuous
  have hEa : Continuous (fun s : ℝ =>
      (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A)))) :=
    ContinuousLinearMap.adjoint.continuous.comp hE
  exact hEa.clm_comp (continuous_const.clm_comp hE)

/-! ### Energy identity -/

/-- The Lyapunov energy identity: the quadratic form of `P(T)` is the integral of
`⟪exp(s A) x, Q (exp(s A) x)⟫`. No squared norm appears because `Q` is not
factored as `C* C`. -/
theorem inner_lyapunovIntegral (A Q : X →L[ℝ] X) (T : ℝ) (x : X) :
    inner ℝ x (lyapunovIntegral A Q T x) =
      ∫ s in (0 : ℝ)..T,
        inner ℝ (NormedSpace.exp (s • A) x) (Q (NormedSpace.exp (s • A) x)) := by
  let L : ℝ → X →L[ℝ] X := fun s =>
    (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
      (Q.comp (NormedSpace.exp (s • A)))
  have hcontL : Continuous L := continuous_lyapunovIntegrand A Q
  have hIntL : IntervalIntegrable L volume (0 : ℝ) T := hcontL.intervalIntegrable _ _
  have happly : lyapunovIntegral A Q T x = ∫ s in (0 : ℝ)..T, L s x := by
    rw [lyapunovIntegral]
    exact ContinuousLinearMap.intervalIntegral_apply hIntL x
  have hcontLx : Continuous (fun s : ℝ => L s x) := hcontL.clm_apply continuous_const
  have hIntLx : IntervalIntegrable (fun s : ℝ => L s x) volume (0 : ℝ) T :=
    hcontLx.intervalIntegrable _ _
  rw [happly]
  rw [show inner ℝ x (∫ s in (0 : ℝ)..T, L s x) =
      (innerSL ℝ x) (∫ s in (0 : ℝ)..T, L s x) from rfl]
  rw [← (innerSL ℝ x).intervalIntegral_comp_comm hIntLx]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [L, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [ContinuousLinearMap.adjoint_inner_right (NormedSpace.exp (s • A)) x
    (Q (NormedSpace.exp (s • A) x))]

/-! ### Positive semidefiniteness -/

/-- The Lyapunov integral is positive semidefinite on a nonnegative horizon when
`Q` is positive semidefinite. -/
theorem lyapunovIntegral_nonneg (A Q : X →L[ℝ] X)
    (hQ : ∀ x, 0 ≤ inner ℝ x (Q x)) {T : ℝ} (hT : 0 ≤ T) (x : X) :
    0 ≤ inner ℝ x (lyapunovIntegral A Q T x) := by
  rw [inner_lyapunovIntegral]
  exact intervalIntegral.integral_nonneg hT fun s _ => hQ _
