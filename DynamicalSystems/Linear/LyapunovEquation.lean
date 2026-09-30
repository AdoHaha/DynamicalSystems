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

/-! ### The finite-horizon Lyapunov equation -/

/-- Derivative of the operator-valued Lyapunov integrand
`g s = exp(s A)* Q exp(s A)`: its derivative at `t` is
`A* g t + g t A`. -/
private lemma hasDerivAt_lyapunovIntegrand (A Q : X →L[ℝ] X) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦
      (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
        (Q.comp (NormedSpace.exp (s • A))))
      ((ContinuousLinearMap.adjoint A).comp
          ((ContinuousLinearMap.adjoint (NormedSpace.exp (t • A))).comp
            (Q.comp (NormedSpace.exp (t • A))))
        + ((ContinuousLinearMap.adjoint (NormedSpace.exp (t • A))).comp
            (Q.comp (NormedSpace.exp (t • A)))).comp A) t := by
  let E : ℝ → X →L[ℝ] X := fun s ↦ NormedSpace.exp (s • A)
  let g : ℝ → X →L[ℝ] X := fun s ↦
    (ContinuousLinearMap.adjoint (E s)).comp (Q.comp (E s))
  have hE : HasDerivAt E ((E t).comp A) t := by
    have h := hasDerivAt_exp_smul_const A t
    rw [ContinuousLinearMap.mul_def] at h
    simpa only [E] using h
  have hEa : HasDerivAt (fun s ↦ ContinuousLinearMap.adjoint (E s))
      (ContinuousLinearMap.adjoint ((E t).comp A)) t := by
    have h := (ContinuousLinearMap.adjoint.toContinuousLinearEquiv.hasFDerivAt).comp_hasDerivAt t hE
    exact h
  have hQ : HasDerivAt (fun s ↦ Q.comp (E s)) (Q.comp ((E t).comp A)) t := by
    have h := ((ContinuousLinearMap.compL ℝ X X X Q).hasFDerivAt).comp_hasDerivAt t hE
    simpa only [Function.comp_def, ContinuousLinearMap.compL_apply] using h
  have h := hEa.clm_comp hQ
  have hg : (fun s ↦ ContinuousLinearMap.adjoint (E s) ∘SL Q ∘SL E s) = g := by
    funext s; rfl
  rw [hg] at h
  have hgoal : (ContinuousLinearMap.adjoint ((E t).comp A)).comp (Q.comp (E t))
      + (ContinuousLinearMap.adjoint (E t)).comp (Q.comp ((E t).comp A))
      = (ContinuousLinearMap.adjoint A).comp (g t) + (g t).comp A := by
    simp only [g, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
  rwa [hgoal] at h

/-- The finite-horizon Lyapunov equation: the finite-horizon Lyapunov integral
`P(T) = ∫₀ᵀ exp(s A)* Q exp(s A) ds` satisfies
`A* P(T) + P(T) A = exp(TA)* Q exp(TA) - Q`,
so it solves the algebraic Lyapunov equation up to the boundary term
`exp(TA)* Q exp(TA)`. Source: Kabziński–Mosiołek, equation (2.40). -/
theorem lyapunovIntegral_equation (A Q : X →L[ℝ] X) (T : ℝ) :
    (ContinuousLinearMap.adjoint A).comp (lyapunovIntegral A Q T)
      + (lyapunovIntegral A Q T).comp A
    = (ContinuousLinearMap.adjoint (NormedSpace.exp (T • A))).comp
        (Q.comp (NormedSpace.exp (T • A))) - Q := by
  let E : ℝ → X →L[ℝ] X := fun s ↦ NormedSpace.exp (s • A)
  let g : ℝ → X →L[ℝ] X := fun s ↦
    (ContinuousLinearMap.adjoint (E s)).comp (Q.comp (E s))
  have hg_eq : lyapunovIntegral A Q T = ∫ s in (0 : ℝ)..T, g s := by
    rw [lyapunovIntegral]
  have hcontg : Continuous g := by
    simpa only [g, E] using continuous_lyapunovIntegrand A Q
  have hIntg : IntervalIntegrable g volume (0 : ℝ) T := hcontg.intervalIntegrable _ _
  have hderiv : ∀ t, HasDerivAt g
      ((ContinuousLinearMap.adjoint A).comp (g t) + (g t).comp A) t := by
    intro t
    simpa only [g, E] using hasDerivAt_lyapunovIntegrand A Q t
  have hcontA_g : Continuous (fun s ↦ (ContinuousLinearMap.adjoint A).comp (g s)) :=
    continuous_const.clm_comp hcontg
  have hcont_g_A : Continuous (fun s ↦ (g s).comp A) :=
    hcontg.clm_comp continuous_const
  have hInt_A_g : IntervalIntegrable
      (fun s ↦ (ContinuousLinearMap.adjoint A).comp (g s)) volume (0 : ℝ) T :=
    hcontA_g.intervalIntegrable _ _
  have hInt_g_A : IntervalIntegrable (fun s ↦ (g s).comp A) volume (0 : ℝ) T :=
    hcont_g_A.intervalIntegrable _ _
  have hcontg' : Continuous
      (fun s ↦ (ContinuousLinearMap.adjoint A).comp (g s) + (g s).comp A) :=
    hcontA_g.add hcont_g_A
  have hIntg' : IntervalIntegrable
      (fun s ↦ (ContinuousLinearMap.adjoint A).comp (g s) + (g s).comp A)
      volume (0 : ℝ) T :=
    hcontg'.intervalIntegrable _ _
  have hFTC : ∫ s in (0 : ℝ)..T,
      ((ContinuousLinearMap.adjoint A).comp (g s) + (g s).comp A) = g T - g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t) hIntg'
  have hcomm1 : (ContinuousLinearMap.adjoint A).comp (∫ s in (0 : ℝ)..T, g s)
      = ∫ s in (0 : ℝ)..T, (ContinuousLinearMap.adjoint A).comp (g s) := by
    have h := ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousLinearMap.compL ℝ X X X (ContinuousLinearMap.adjoint A)) hIntg
    simpa only [ContinuousLinearMap.compL_apply] using h.symm
  have hcomm2 : (∫ s in (0 : ℝ)..T, g s).comp A
      = ∫ s in (0 : ℝ)..T, (g s).comp A := by
    have h := ContinuousLinearMap.intervalIntegral_comp_comm
      ((ContinuousLinearMap.compL ℝ X X X).flip A) hIntg
    simpa only [ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply] using h.symm
  have hg0 : g 0 = Q := by
    ext x
    simp only [g, E, zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.adjoint_one,
      ContinuousLinearMap.comp_apply, one_apply_eq_self]
  have hKey : (ContinuousLinearMap.adjoint A).comp (lyapunovIntegral A Q T)
      + (lyapunovIntegral A Q T).comp A
      = ∫ s in (0 : ℝ)..T,
          ((ContinuousLinearMap.adjoint A).comp (g s) + (g s).comp A) := by
    rw [hg_eq, hcomm1, hcomm2, ← intervalIntegral.integral_add hInt_A_g hInt_g_A]
  rw [hKey, hFTC, hg0]
