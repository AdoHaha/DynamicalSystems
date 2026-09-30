/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Gramian
public import DynamicalSystems.Linear.Stabilization
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.ExpDecay

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

/-! ### The infinite-horizon Lyapunov integral

When `A` is Hurwitz the finite-horizon Lyapunov integral has a limit as the
horizon tends to `+∞`: the exponential decay `‖exp (s A)‖ ≤ C exp (-γ s)` makes
the integrand `exp (s A)* Q exp (s A)` dominated by the integrable function
`C ^ 2 * ‖Q‖ * exp (-(2 γ) s)` on `(0, ∞)`. The limit is the improper Bochner
integral `P = ∫₀^∞ exp (s A)* Q exp (s A) ds`, the candidate solution of the
algebraic Lyapunov equation `A* P + P A = -Q` from equation (2.40). -/

/-- For a Hurwitz generator `A`, the operator-valued Lyapunov integrand
`s ↦ exp (s A)* Q exp (s A)` is Bochner integrable on the half-line `(0, ∞)`.
The domination uses the quantitative Hurwitz bound
`‖exp (s A)‖ ≤ C exp (-γ s)` for `s ≥ 0`. Source: Kabziński–Mosiołek, equation
(2.40), where the improper integral defining `P` is shown to converge. -/
theorem integrableOn_Ioi_lyapunovIntegrand (A Q : X →L[ℝ] X)
    (hA : LinearMap.IsHurwitz A.toLinearMap) :
    IntegrableOn (fun s =>
      (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
        (Q.comp (NormedSpace.exp (s • A)))) (Ioi (0 : ℝ)) := by
  obtain ⟨C, hCpos, γ, hγpos, hC⟩ :=
    LinearMap.exists_exponential_norm_bound_of_isHurwitz A.toLinearMap hA
  have hC' : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • A)‖ ≤ C * Real.exp (-γ * t) := by
    intro t ht
    have h := hC t ht
    rwa [show A.toLinearMap.toContinuousLinearMap = A from rfl] at h
  set f : ℝ → X →L[ℝ] X := fun s =>
    (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
      (Q.comp (NormedSpace.exp (s • A))) with hf
  have hfcont : Continuous f := continuous_lyapunovIntegrand A Q
  have hg : IntegrableOn
      (fun s : ℝ => (C ^ 2 * ‖Q‖) * Real.exp (-(2 * γ) * s)) (Ioi 0) := by
    have h : IntegrableOn (fun s : ℝ => Real.exp (-(2 * γ) * s)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 (by positivity)
    exact h.const_mul (C ^ 2 * ‖Q‖)
  refine Integrable.mono' hg ?_ ?_
  · exact (hfcont.aestronglyMeasurable).mono_measure Measure.restrict_le_self
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    have hbound := hC' s hs0
    have hadj : ‖ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))‖ =
        ‖NormedSpace.exp (s • A)‖ := ContinuousLinearMap.adjoint.norm_map _
    calc ‖f s‖
        = ‖(ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
            (Q.comp (NormedSpace.exp (s • A)))‖ := rfl
      _ ≤ ‖ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))‖ *
            ‖Q.comp (NormedSpace.exp (s • A))‖ := by
          simpa only [ContinuousLinearMap.mul_def] using norm_mul_le
            (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A)))
            (Q.comp (NormedSpace.exp (s • A)))
      _ ≤ ‖NormedSpace.exp (s • A)‖ * (‖Q‖ * ‖NormedSpace.exp (s • A)‖) := by
          rw [hadj]
          gcongr
          simpa only [ContinuousLinearMap.mul_def] using
            norm_mul_le Q (NormedSpace.exp (s • A))
      _ ≤ (C * Real.exp (-γ * s)) * (‖Q‖ * (C * Real.exp (-γ * s))) := by
          gcongr
      _ = (C ^ 2 * ‖Q‖) * Real.exp (-(2 * γ) * s) := by
          rw [show -(2 * γ) * s = -γ * s + -γ * s by ring, Real.exp_add]
          ring

/-- The infinite-horizon Lyapunov integral `P = ∫₀^∞ exp (s A)* Q exp (s A) ds`,
as a continuous endomorphism of the state space. This is the improper Bochner
integral over `(0, ∞)` of the operator-valued integrand; when `A` is Hurwitz it
is the limit of the finite-horizon integrals `lyapunovIntegral A Q T`. Source:
Kabziński–Mosiołek, equation (2.40). -/
-- The underscore in `lyapunovIntegral_limit` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
noncomputable def lyapunovIntegral_limit (A Q : X →L[ℝ] X) : X →L[ℝ] X :=
  ∫ s in Ioi (0 : ℝ),
    (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
      (Q.comp (NormedSpace.exp (s • A)))

/-- **Existence of the infinite-horizon Lyapunov integral.** For a Hurwitz
generator `A` the finite-horizon Lyapunov integrals `P(T) = lyapunovIntegral A Q T`
converge, as `T → +∞`, to the improper integral `lyapunovIntegral_limit A Q`. This
is the convergence of the improper integral of equation (2.40). -/
theorem tendsto_lyapunovIntegral_limit (A Q : X →L[ℝ] X)
    (hA : LinearMap.IsHurwitz A.toLinearMap) :
    Tendsto (fun T => lyapunovIntegral A Q T) atTop
      (nhds (lyapunovIntegral_limit A Q)) := by
  have hInt := integrableOn_Ioi_lyapunovIntegrand A Q hA
  exact intervalIntegral_tendsto_integral_Ioi (μ := volume) (a := (0 : ℝ))
    (f := fun s =>
      (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
        (Q.comp (NormedSpace.exp (s • A)))) hInt tendsto_id

/-- **Existence of a limit of the finite-horizon Lyapunov integrals.** For a
Hurwitz generator `A` the family `T ↦ lyapunovIntegral A Q T` converges to some
continuous endomorphism as `T → +∞`; the witness is the infinite-horizon
integral `lyapunovIntegral_limit A Q`. Source: Kabziński–Mosiołek, equation
(2.40). -/
theorem hasLyapunovIntegralLimit (A Q : X →L[ℝ] X)
    (hA : LinearMap.IsHurwitz A.toLinearMap) :
    ∃ P : X →L[ℝ] X, Tendsto (fun T => lyapunovIntegral A Q T) atTop (nhds P) :=
  ⟨lyapunovIntegral_limit A Q, tendsto_lyapunovIntegral_limit A Q hA⟩
