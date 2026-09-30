/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Gramian
public import DynamicalSystems.Linear.Stabilization
public import Mathlib.Analysis.CStarAlgebra.Matrix
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

/-- Pointwise operator-norm bound for the Lyapunov integrand
`exp (T A)* Q exp (T A)`, assuming the quantitative decay bound
`‖exp (t A)‖ ≤ C exp (-γ t)` for all `t ≥ 0`. The conclusion is
`‖exp (T A)* Q exp (T A)‖ ≤ ‖Q‖ C² exp (-(2 γ) T)`. -/
theorem norm_exp_adjoint_comp_comp_exp_le (A Q : X →L[ℝ] X) (C γ : ℝ)
    (hC : ∀ t, 0 ≤ t → ‖NormedSpace.exp (t • A)‖ ≤ C * Real.exp (-γ * t))
    {T : ℝ} (hT : 0 ≤ T) :
    ‖(ContinuousLinearMap.adjoint (NormedSpace.exp (T • A))).comp
        (Q.comp (NormedSpace.exp (T • A)))‖ ≤
      ‖Q‖ * C ^ 2 * Real.exp (-(2 * γ) * T) := by
  have hET := hC T hT
  have hadj : ‖ContinuousLinearMap.adjoint (NormedSpace.exp (T • A))‖ =
      ‖NormedSpace.exp (T • A)‖ := ContinuousLinearMap.adjoint.norm_map _
  calc ‖(ContinuousLinearMap.adjoint (NormedSpace.exp (T • A))).comp
          (Q.comp (NormedSpace.exp (T • A)))‖
      ≤ ‖ContinuousLinearMap.adjoint (NormedSpace.exp (T • A))‖ *
          ‖Q.comp (NormedSpace.exp (T • A))‖ := by
        simpa only [ContinuousLinearMap.mul_def] using norm_mul_le
          (ContinuousLinearMap.adjoint (NormedSpace.exp (T • A)))
          (Q.comp (NormedSpace.exp (T • A)))
    _ = ‖NormedSpace.exp (T • A)‖ * ‖Q.comp (NormedSpace.exp (T • A))‖ := by
        rw [hadj]
    _ ≤ ‖NormedSpace.exp (T • A)‖ * (‖Q‖ * ‖NormedSpace.exp (T • A)‖) := by
        gcongr
        simpa only [ContinuousLinearMap.mul_def] using
          norm_mul_le Q (NormedSpace.exp (T • A))
    _ ≤ (C * Real.exp (-γ * T)) * (‖Q‖ * (C * Real.exp (-γ * T))) := by
        have hCnonneg : 0 ≤ C * Real.exp (-γ * T) := le_trans (norm_nonneg _) hET
        have hQnonneg : 0 ≤ ‖Q‖ := norm_nonneg _
        exact mul_le_mul hET (mul_le_mul_of_nonneg_left hET hQnonneg)
          (mul_nonneg hQnonneg (norm_nonneg _)) hCnonneg
    _ = ‖Q‖ * C ^ 2 * Real.exp (-(2 * γ) * T) := by
        rw [show -(2 * γ) * T = -γ * T + -γ * T by ring, Real.exp_add]
        ring

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
    have hb := norm_exp_adjoint_comp_comp_exp_le A Q C γ hC' (le_of_lt hs)
    calc ‖f s‖
        = ‖(ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
            (Q.comp (NormedSpace.exp (s • A)))‖ := rfl
      _ ≤ ‖Q‖ * C ^ 2 * Real.exp (-(2 * γ) * s) := hb
      _ = (C ^ 2 * ‖Q‖) * Real.exp (-(2 * γ) * s) := by ring

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

/-! ### The boundary term vanishes at infinity

For a Hurwitz generator `A` the finite-horizon boundary term
`g T = exp(T A)* Q exp(T A)` of `lyapunovIntegral_equation` tends to `0` as
`T → +∞`: the quantitative Hurwitz bound makes it dominated by
`‖Q‖ C ^ 2 exp (-(2 γ) T)`, which is squeezed to zero. This is what turns the
finite-horizon equation into the algebraic Lyapunov equation in the limit. -/

/-- For a Hurwitz generator `A`, the finite-horizon boundary term
`T ↦ exp(T A)* Q exp(T A)` of the Lyapunov equation tends to `0` as `T → +∞`.
Source: Kabziński–Mosiołek, equations (2.39)–(2.40), where the boundary term of
the integrated equation disappears in the infinite-horizon limit. -/
theorem tendsto_exp_adjoint_comp_comp_exp_zero (A Q : X →L[ℝ] X)
    (hA : LinearMap.IsHurwitz A.toLinearMap) :
    Tendsto (fun T : ℝ =>
      (ContinuousLinearMap.adjoint (NormedSpace.exp (T • A))).comp
        (Q.comp (NormedSpace.exp (T • A)))) atTop (nhds 0) := by
  obtain ⟨C, _hCpos, γ, hγpos, hC⟩ :=
    LinearMap.exists_exponential_norm_bound_of_isHurwitz A.toLinearMap hA
  have hC' : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • A)‖ ≤ C * Real.exp (-γ * t) := by
    intro t ht
    have h := hC t ht
    rwa [show A.toLinearMap.toContinuousLinearMap = A from rfl] at h
  have hbound : ∀ T : ℝ, 0 ≤ T →
      ‖(ContinuousLinearMap.adjoint (NormedSpace.exp (T • A))).comp
        (Q.comp (NormedSpace.exp (T • A)))‖ ≤
      ‖Q‖ * C ^ 2 * Real.exp (-(2 * γ) * T) :=
    fun T hT => norm_exp_adjoint_comp_comp_exp_le A Q C γ hC' hT
  have hexp : Tendsto (fun T : ℝ => Real.exp (-(2 * γ) * T)) atTop (nhds 0) := by
    have hgamma : -(2 * γ) < 0 := by linarith
    have h1 : Tendsto (fun T : ℝ => T * (-(2 * γ))) atTop atBot :=
      tendsto_id.atTop_mul_const_of_neg hgamma
    have h2 : Tendsto (fun T : ℝ => Real.exp (T * (-(2 * γ)))) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h1
    refine h2.congr' ?_
    filter_upwards with T
    rw [mul_comm]
  have hg : Tendsto (fun T : ℝ => ‖Q‖ * C ^ 2 * Real.exp (-(2 * γ) * T))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hexp.const_mul (‖Q‖ * C ^ 2)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _)
    (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT; exact hbound T hT) hg

/-! ### The algebraic Lyapunov equation

Passing to the limit `T → +∞` in the finite-horizon Lyapunov equation. The left
side is continuous in `P(T)`, hence converges to `A* P + P A` along the limit of
the finite-horizon integrals, while the right side converges to `-Q` because the
boundary term `exp(T A)* Q exp(T A)` vanishes. Uniqueness of limits then yields
the algebraic Lyapunov equation. -/

/-- **Algebraic Lyapunov equation from a limit of finite-horizon integrals.** If
the finite-horizon Lyapunov integrals `lyapunovIntegral A Q T` converge to `P` as
`T → +∞`, then `P` solves the algebraic Lyapunov equation `A* P + P A = -Q`.
Source: Kabziński–Mosiołek, equation (2.39). -/
theorem lyapunov_equation_of_tendsto (A Q P : X →L[ℝ] X)
    (hA : LinearMap.IsHurwitz A.toLinearMap)
    (hP : Tendsto (fun T => lyapunovIntegral A Q T) atTop (nhds P)) :
    (ContinuousLinearMap.adjoint A).comp P + P.comp A = -Q := by
  have hcont : Continuous (fun R : X →L[ℝ] X =>
      (ContinuousLinearMap.adjoint A).comp R + R.comp A) :=
    (ContinuousLinearMap.compL ℝ X X X (ContinuousLinearMap.adjoint A)).continuous.add
      (((ContinuousLinearMap.compL ℝ X X X).flip A).continuous)
  have hLHS : Tendsto (fun T : ℝ =>
      (ContinuousLinearMap.adjoint A).comp (lyapunovIntegral A Q T)
        + (lyapunovIntegral A Q T).comp A) atTop
      (nhds ((ContinuousLinearMap.adjoint A).comp P + P.comp A)) :=
    (hcont.tendsto P).comp hP
  have hRHS : Tendsto (fun T : ℝ =>
      (ContinuousLinearMap.adjoint A).comp (lyapunovIntegral A Q T)
        + (lyapunovIntegral A Q T).comp A) atTop (nhds (-Q)) := by
    have h := (tendsto_exp_adjoint_comp_comp_exp_zero A Q hA).sub
      (tendsto_const_nhds (x := Q))
    rw [zero_sub] at h
    refine h.congr' ?_
    filter_upwards with T
    exact (lyapunovIntegral_equation A Q T).symm
  exact tendsto_nhds_unique hLHS hRHS

/-- **The infinite-horizon Lyapunov equation.** For a Hurwitz generator `A`,
the infinite-horizon Lyapunov integral `P = lyapunovIntegral_limit A Q` solves the
algebraic Lyapunov equation `A* P + P A = -Q`. Source: Kabziński–Mosiołek,
equation (2.39) with the integral representation (2.40). -/
theorem lyapunovIntegral_limit_equation (A Q : X →L[ℝ] X)
    (hA : LinearMap.IsHurwitz A.toLinearMap) :
    (ContinuousLinearMap.adjoint A).comp (lyapunovIntegral_limit A Q)
      + (lyapunovIntegral_limit A Q).comp A = -Q :=
  lyapunov_equation_of_tendsto A Q (lyapunovIntegral_limit A Q) hA
    (tendsto_lyapunovIntegral_limit A Q hA)

/-- **Pointwise form of the infinite-horizon Lyapunov equation.** Applying the
operator equation `A* P + P A = -Q` to a state `x` gives
`A* (P x) + P (A x) = -Q x`. This is the identity used downstream to compute
the system derivative `V̇(x) = ⟪x, (A* P + P A) x⟫ = -⟪x, Q x⟫` of the quadratic
Lyapunov function `V(x) = ⟪x, P x⟫`. Source: Kabziński–Mosiołek, equations
(2.36)–(2.39). -/
theorem lyapunovIntegral_limit_equation_apply (A Q : X →L[ℝ] X)
    (hA : LinearMap.IsHurwitz A.toLinearMap) (x : X) :
    ContinuousLinearMap.adjoint A (lyapunovIntegral_limit A Q x)
      + lyapunovIntegral_limit A Q (A x) = -Q x := by
  have h := lyapunovIntegral_limit_equation A Q hA
  simpa only [add_apply, ContinuousLinearMap.comp_apply, neg_apply]
    using congrArg (fun L : X →L[ℝ] X => L x) h

/-! ### Positive definiteness, self-adjointness and the assembled solution

With the algebraic Lyapunov equation in hand, this section records that the
solution `P = ∫₀^∞ exp (s A)* Q exp (s A) ds` is positive definite whenever `Q`
is, that `P` is self-adjoint whenever `Q` is, and assembles the existence
theorem of Kabziński–Mosiołek, Theorem 2.16. -/

/-- The finite-horizon Lyapunov integral at horizon `T = 1` is strictly positive
on every nonzero state when `Q` is positive definite: the quadratic form
`⟪x, P(1) x⟫ = ∫₀¹ ⟪e^{s A} x, Q (e^{s A} x)⟫ ds` integrates a continuous
nonnegative integrand that is positive at `s = 0`. Source: Kabziński–Mosiołek,
Theorem 2.16 and equation (2.40). -/
theorem inner_lyapunovIntegral_one_pos (A Q : X →L[ℝ] X)
    (hQ : LinearSystem.IsPositiveDefinite Q) {x : X} (hx : x ≠ 0) :
    0 < inner ℝ x (lyapunovIntegral A Q 1 x) := by
  have hQnonneg : ∀ y : X, 0 ≤ inner ℝ y (Q y) := by
    intro y
    by_cases hy : y = 0
    · subst hy
      simp
    · exact le_of_lt (hQ y hy)
  have hcont : Continuous (fun s : ℝ =>
      inner ℝ (NormedSpace.exp (s • A) x) (Q (NormedSpace.exp (s • A) x))) := by
    have hE : Continuous (fun s : ℝ => NormedSpace.exp (s • A) x) :=
      (differentiable_exp_smul_const ℝ A).continuous.clm_apply continuous_const
    exact hE.inner (Q.continuous.comp hE)
  rw [inner_lyapunovIntegral]
  refine intervalIntegral.integral_pos (by norm_num) hcont.continuousOn
    (fun s _ => hQnonneg _) ⟨0, ⟨le_refl 0, by norm_num⟩, ?_⟩
  simpa only [zero_smul, NormedSpace.exp_zero, one_apply_eq_self]
    using hQ x hx

/-- The infinite-horizon Lyapunov integral is positive definite when `Q` is. For
`x ≠ 0` the quadratic form is estimated from below by its value at horizon
`1`, which is positive, and the estimate passes to the limit because the
finite-horizon quadratic forms are eventually bounded below by this value and
converge to the quadratic form of `lyapunovIntegral_limit`. Source:
Kabziński–Mosiołek, Theorem 2.16 and equation (2.40). -/
theorem isPositiveDefinite_lyapunovIntegral_limit (A Q : X →L[ℝ] X)
    (hA : LinearMap.IsHurwitz A.toLinearMap) (hQ : LinearSystem.IsPositiveDefinite Q) :
    LinearSystem.IsPositiveDefinite (lyapunovIntegral_limit A Q) := by
  intro x hx
  have hQnonneg : ∀ y : X, 0 ≤ inner ℝ y (Q y) := by
    intro y
    by_cases hy : y = 0
    · subst hy
      simp
    · exact le_of_lt (hQ y hy)
  have hcont : Continuous (fun s : ℝ =>
      inner ℝ (NormedSpace.exp (s • A) x) (Q (NormedSpace.exp (s • A) x))) := by
    have hE : Continuous (fun s : ℝ => NormedSpace.exp (s • A) x) :=
      (differentiable_exp_smul_const ℝ A).continuous.clm_apply continuous_const
    exact hE.inner (Q.continuous.comp hE)
  have htend : Tendsto (fun T : ℝ => inner ℝ x (lyapunovIntegral A Q T x)) atTop
      (nhds (inner ℝ x (lyapunovIntegral_limit A Q x))) := by
    have heval : Continuous (fun L : X →L[ℝ] X => inner ℝ x (L x)) :=
      continuous_const.inner (ContinuousLinearMap.apply ℝ X x).continuous
    exact (heval.tendsto (lyapunovIntegral_limit A Q)).comp
      (tendsto_lyapunovIntegral_limit A Q hA)
  have hmono : ∀ᶠ T in atTop,
      inner ℝ x (lyapunovIntegral A Q 1 x) ≤ inner ℝ x (lyapunovIntegral A Q T x) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    simp only [inner_lyapunovIntegral]
    exact intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) zero_le_one hT
      (Eventually.of_forall fun s : ℝ => hQnonneg _) (hcont.intervalIntegrable _ _)
  exact lt_of_lt_of_le (inner_lyapunovIntegral_one_pos A Q hQ hx)
    (ge_of_tendsto htend hmono)

/-- The infinite-horizon Lyapunov integral is self-adjoint when `Q` is. The
integrand `exp (s A)* Q exp (s A)` is self-adjoint at every time `s` when
`adjoint Q = Q`, and `adjoint` commutes with the Bochner integral. Source:
Kabziński–Mosiołek, equation (2.40). -/
theorem adjoint_lyapunovIntegral_limit (A Q : X →L[ℝ] X)
    (hA : LinearMap.IsHurwitz A.toLinearMap)
    (hQ : ContinuousLinearMap.adjoint Q = Q) :
    ContinuousLinearMap.adjoint (lyapunovIntegral_limit A Q) =
      lyapunovIntegral_limit A Q := by
  have hg : ∀ s : ℝ,
      ContinuousLinearMap.adjoint
        ((ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
          (Q.comp (NormedSpace.exp (s • A))))
        = (ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
            (Q.comp (NormedSpace.exp (s • A))) := by
    intro s
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_assoc, hQ]
  have hcomm : ContinuousLinearMap.adjoint (lyapunovIntegral_limit A Q)
      = ∫ s in Ioi (0 : ℝ),
          ContinuousLinearMap.adjoint
            ((ContinuousLinearMap.adjoint (NormedSpace.exp (s • A))).comp
              (Q.comp (NormedSpace.exp (s • A)))) := by
    rw [lyapunovIntegral_limit]
    exact (ContinuousLinearMap.integral_comp_commSL
      (σ := starRingEnd ℝ) (by intro r x; simp)
      ((ContinuousLinearMap.adjoint (E := X) (F := X)).toLinearIsometry.toContinuousLinearMap)
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (integrableOn_Ioi_lyapunovIntegrand A Q hA)).symm
  rw [hcomm, lyapunovIntegral_limit]
  exact setIntegral_congr_fun measurableSet_Ioi (fun s _ => hg s)

/-- **Existence of a positive definite self-adjoint solution of the Lyapunov
equation** (Kabziński–Mosiołek, Theorem 2.16, equation (2.40)): for a Hurwitz
generator `A` and a positive definite self-adjoint `Q` there is a positive
definite self-adjoint `P` with `A* P + P A = -Q`. The solution is the
infinite-horizon Lyapunov integral `P = ∫₀^∞ exp (s A)* Q exp (s A) ds`. -/
theorem lyapunov_equation_solution (A Q : X →L[ℝ] X)
    (hA : LinearMap.IsHurwitz A.toLinearMap)
    (hQ_pd : LinearSystem.IsPositiveDefinite Q)
    (hQ_adj : ContinuousLinearMap.adjoint Q = Q) :
    ∃ P : X →L[ℝ] X,
      LinearSystem.IsPositiveDefinite P ∧
      ContinuousLinearMap.adjoint P = P ∧
      (ContinuousLinearMap.adjoint A).comp P + P.comp A = -Q :=
  ⟨lyapunovIntegral_limit A Q,
   isPositiveDefinite_lyapunovIntegral_limit A Q hA hQ_pd,
   adjoint_lyapunovIntegral_limit A Q hA hQ_adj,
   lyapunovIntegral_limit_equation A Q hA⟩

/-! ### The matrix Lyapunov equation for MRAC

This final section records the matrix form of the existence theorem used by the
model reference adaptive control construction. The bridge between matrices and
operators is the star algebra equivalence `Matrix.toEuclideanCLM`, which sends a
real `n × n` matrix to the continuous endomorphism of the Euclidean space
`EuclideanSpace ℝ (Fin n)` it represents in the standard orthonormal basis. It
has the following properties:

* the endomorphism `Matrix.toEuclideanCLM A` has the same characteristic
  polynomial as `Matrix.toLin' A`, so it is Hurwitz exactly when `A` is;
* it intertwines the matrix transpose with the Hilbert adjoint, whence
  `Aᵀ P + P A` is carried to `A† P + P A`;
* `Matrix.inner_toEuclideanCLM` turns the operator quadratic form into the
  matrix quadratic form `x ⬝ᵥ A *ᵥ x`, which lets `Matrix.PosDef` be read as
  `LinearSystem.IsPositiveDefinite` and back.

Applying the operator theorem `lyapunov_equation_solution` and pulling the
solution back along this equivalence yields the matrix statement.
Source: Kabziński–Mosiołek, Section 2.5, Definition 2.10 and Theorem 2.16,
equations (2.36)–(2.40). -/

namespace Matrix

/-- A square real matrix is Hurwitz when the linear endomorphism `Matrix.toLin'`
it induces on `Fin n → ℝ` is Hurwitz, i.e. when all complex eigenvalues of `A`
have negative real part. Source: Kabziński–Mosiołek, Section 2.5 and
Theorem 2.16. -/
def IsHurwitz {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  LinearMap.IsHurwitz (Matrix.toLin' A)

end Matrix

open scoped Matrix

/-- **The matrix Lyapunov equation** (Kabziński–Mosiołek, Theorem 2.16): for a
Hurwitz real square matrix `A` and a positive definite matrix `Q` there is a
positive definite matrix `P` solving `Aᵀ * P + P * A = -Q`. -/
theorem matrix_lyapunov_equation_solution {n : Nat} (A Q : Matrix (Fin n) (Fin n) ℝ)
    (hA : Matrix.IsHurwitz A) (hQ : Q.PosDef) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, P.PosDef ∧ Aᵀ * P + P * A = -Q := by
  classical
  set e : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) with he
  have hAe : LinearMap.IsHurwitz (e A).toLinearMap := by
    have hchar : (e A).toLinearMap.charpoly = (Matrix.toLin' A).charpoly := by
      rw [he, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin A,
        Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.charpoly_toLin,
        Matrix.charpoly_toLin']
    intro z hz
    exact hA z (by rwa [hchar] at hz)
  have hQe : LinearSystem.IsPositiveDefinite (e Q) := by
    intro x hx
    rw [he, Matrix.inner_toEuclideanCLM]
    have hx' : x.ofLp ≠ 0 := fun h => hx (WithLp.ofLp_injective 2 h)
    simpa using (Matrix.posDef_iff_dotProduct_mulVec.mp hQ).2 hx'
  have hQadj : ContinuousLinearMap.adjoint (e Q) = e Q := by
    have hstar : star Q = Q := hQ.1.star_eq
    have hmap : e Q = star (e Q) := by
      rw [← map_star (f := e) Q, hstar]
    rw [ContinuousLinearMap.star_eq_adjoint] at hmap
    exact hmap.symm
  obtain ⟨Pe, hPe_pd, hPe_adj, hPe_eq⟩ :=
    lyapunov_equation_solution (e A) (e Q) hAe hQe hQadj
  set P : Matrix (Fin n) (Fin n) ℝ := e.symm Pe with hP
  have heP : e P = Pe := by rw [hP]; exact e.apply_symm_apply Pe
  refine ⟨P, ?_, ?_⟩
  · rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · change Pᴴ = P
      rw [← Matrix.star_eq_conjTranspose]
      have h := map_star (f := e.symm) Pe
      have hstar_adj : star Pe = Pe := by
        rw [ContinuousLinearMap.star_eq_adjoint, hPe_adj]
      rw [hstar_adj] at h
      rw [← hP] at h
      exact h.symm
    · intro x hx
      have hx' : WithLp.toLp 2 x ≠ 0 := by
        intro h0
        apply hx
        have := congrArg WithLp.ofLp h0
        simpa using this
      have hpos := hPe_pd (WithLp.toLp 2 x) hx'
      have hinner : inner ℝ (WithLp.toLp 2 x) (Pe (WithLp.toLp 2 x)) =
          star x ⬝ᵥ P *ᵥ x := by
        rw [← heP, he, Matrix.inner_toEuclideanCLM]
        simp
      rwa [← hinner]
  · have hPe_eq' : ContinuousLinearMap.adjoint (e A) * Pe + Pe * e A = -e Q := by
      simpa only [← ContinuousLinearMap.mul_def] using hPe_eq
    have h := congrArg e.symm hPe_eq'
    simp only [map_add, map_mul, map_neg, StarAlgEquiv.symm_apply_apply] at h
    rw [← hP] at h
    have hsymm_adj : e.symm (ContinuousLinearMap.adjoint (e A)) = Aᵀ := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star (f := e) A,
        e.symm_apply_apply]
      exact (Matrix.star_eq_conjTranspose A).trans
        (Matrix.conjTranspose_eq_transpose_of_trivial A)
    rw [hsymm_adj] at h
    exact h
