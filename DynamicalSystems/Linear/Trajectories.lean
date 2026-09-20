/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Trajectory
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Vector-valued fundamental theorem of calculus

This file supplies the vector-valued fundamental theorem of calculus that identifies an
absolutely continuous primitive with the Bochner interval integral of its almost-everywhere
derivative, together with the specialization to the shifted exponential flow
`s ↦ exp ((t - s) • A) (g s)` used by the finite Bohl variation-of-constants bridge.

The pinned Mathlib proves the corresponding statement only for real-valued curves:
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` is stated for `f : ℝ → ℝ`, and
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` (the primitive
absolute-continuity template) is also real-valued.  The vector-valued primitive is already
available as `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector` in
`DynamicalSystems.Linear.Trajectory`; combining it with the vector-valued
`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero` gives the theorem
`intervalIntegral.integral_eq_sub_of_ae_hasDerivAt` below.  This is the vector-valued form of
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`.

The declarations are:

* `intervalIntegral.integral_eq_sub_of_ae_hasDerivAt` — vector-valued FTC for an absolutely
  continuous curve whose derivative `f'` exists almost everywhere and is interval integrable.
* `intervalIntegral.sub_eq_integral_of_hasDerivAt` — endpoint-difference form for a curve with a
  continuous derivative, obtained from Mathlib's generic
  `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
* `hasDerivAt_exp_sub_smul_apply` — the product rule for the shifted exponential flow
  `s ↦ exp ((t - s) • A) (g s)`.
* `integral_exp_sub_smul_apply_deriv` — the resulting FTC identity on the shifted exponential
  flow, the form consumed by the finite Bohl / Bochner variation-of-constants identification.

## References

The vector-valued form follows the scalar template in
`Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun`
(Yizheng Zhu, Apache-2.0), replacing the scalar absolute value by the Bochner norm.

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Section 2.6.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Interval

namespace intervalIntegral

/-- **Vector-valued fundamental theorem of calculus.** If `f` is absolutely continuous on
`uIcc a b`, has derivative `f'` almost everywhere on `uIcc a b`, and `f'` is interval integrable,
then the interval integral of `f'` equals the endpoint difference `f b - f a`.

This is the vector-valued form of `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`; the
latter is stated for `f : ℝ → ℝ`.  The proof subtracts the vector-valued primitive of `f'`, whose
absolute continuity is `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector`,
and applies `AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`. -/
theorem integral_eq_sub_of_ae_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a := by
  set g : ℝ → E := f - fun x ↦ ∫ t in a..x, f' t with hg_def
  have hg_ac : AbsolutelyContinuousOnInterval g a b := by
    have hprim : AbsolutelyContinuousOnInterval (fun x ↦ ∫ t in a..x, f' t) a b :=
      hint.absolutelyContinuousOnInterval_intervalIntegral_vector (c := a) (by simp)
    exact hf.sub hprim
  have hg_ae : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt g 0 x := by
    filter_upwards [hderiv, hint.ae_hasDerivAt_integral] with x hx hxint
    intro hxmem
    have hsub := (hx hxmem).sub (hxint hxmem a (by simp))
    simpa only [hg_def, sub_self] using hsub
  obtain ⟨C, hC⟩ := AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero hg_ac hg_ae
  have ha : f a = C := by simpa [hg_def] using hC a (by simp)
  have hb : f b - ∫ x in a..b, f' x = C := by simpa [hg_def] using hC b (by simp)
  have hthis : f b - ∫ x in a..b, f' x = f a := by rw [ha]; exact hb
  exact eq_sub_iff_add_eq.mpr (by rw [add_comm, sub_eq_iff_eq_add.mp hthis])

/-- **Vector-valued fundamental theorem of calculus, endpoint-difference form.** If `f` has
derivative `f'` everywhere and `f'` is continuous, then `f t - f t₀ = ∫ s in t₀..t, f' s`.

This is the form used for smooth primitives; it is a direct corollary of Mathlib's generic
`intervalIntegral.integral_eq_sub_of_hasDerivAt`. -/
theorem sub_eq_integral_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') (t₀ t : ℝ) :
    f t - f t₀ = ∫ s in t₀..t, f' s := by
  have h := integral_eq_sub_of_hasDerivAt (a := t₀) (b := t)
    (fun x _ ↦ hderiv x) (hf'.intervalIntegrable t₀ t)
  exact h.symm

end intervalIntegral

/-! ### The shifted exponential flow

For a continuous linear map `A` on a real Banach space the curve `s ↦ exp ((t - s) • A) (g s)`
differentiates by the product rule; integrating the derivative with
`intervalIntegral.sub_eq_integral_of_hasDerivAt` recovers the endpoint difference.  These are the
real-scalar statements; the complex-generator form used by the Bohl API is obtained in
`DynamicalSystems.Linear.DynamicFeedback` from the product rule proved there. -/

/-- **Product rule for the shifted exponential flow.** The curve
`s ↦ exp ((t - s) • A) (g s)` has derivative
`exp ((t - s) • A) (-(A (g s)) + g')` at `s`. -/
theorem hasDerivAt_exp_sub_smul_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) {g : ℝ → E} {g' : E} (t s : ℝ) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun r : ℝ ↦ NormedSpace.exp ((t - r) • A) (g r))
      (NormedSpace.exp ((t - s) • A) (-(A (g s)) + g')) s := by
  have hE : HasDerivAt (fun r : ℝ ↦ NormedSpace.exp ((t - r) • A))
      (NormedSpace.exp ((t - s) • A) * (-A)) s := by
    have h1 : HasDerivAt (fun u : ℝ ↦ NormedSpace.exp (u • A))
        (NormedSpace.exp ((t - s) • A) * A) (t - s) :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) A (t - s)
    have h2 : HasDerivAt (fun r : ℝ ↦ t - r) (-1 : ℝ) s :=
      (hasDerivAt_id s).const_sub t
    have h3 := h1.scomp s h2
    have heq : (-1 : ℝ) • (NormedSpace.exp ((t - s) • A) * A) =
        NormedSpace.exp ((t - s) • A) * (-A) := by
      rw [neg_one_smul, mul_neg]
    simpa [Function.comp_def, heq] using h3
  have h := hE.clm_apply hg
  have hderiv : (NormedSpace.exp ((t - s) • A) * (-A)) (g s) +
      NormedSpace.exp ((t - s) • A) g' =
      NormedSpace.exp ((t - s) • A) (-(A (g s)) + g') := by
    rw [mul_apply_eq_comp, neg_apply, map_add]
  rwa [hderiv] at h

/-- **Vector FTC on the shifted exponential flow.** If `g` has derivative `g'` everywhere and `g'`
is continuous, then the interval integral of the derivative of `s ↦ exp ((t - s) • A) (g s)` is
the endpoint difference `g t - exp ((t - t₀) • A) (g t₀)`. -/
theorem integral_exp_sub_smul_apply_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) {g g' : ℝ → E}
    (hg : ∀ r, HasDerivAt g (g' r) r) (hg' : Continuous g') (t t₀ : ℝ) :
    ∫ r in t₀..t, NormedSpace.exp ((t - r) • A) (-(A (g r)) + g' r) =
      g t - NormedSpace.exp ((t - t₀) • A) (g t₀) := by
  have hg_cont : Continuous g := continuous_iff_continuousAt.mpr fun r ↦ (hg r).continuousAt
  have hderiv : ∀ r, HasDerivAt (fun r : ℝ ↦ NormedSpace.exp ((t - r) • A) (g r))
      (NormedSpace.exp ((t - r) • A) (-(A (g r)) + g' r)) r :=
    fun r ↦ hasDerivAt_exp_sub_smul_apply A t r (hg r)
  have hflow : Continuous (fun r : ℝ ↦ NormedSpace.exp ((t - r) • A)) :=
    ((differentiable_exp_smul_const (𝕂 := ℝ) A).comp (by fun_prop)).continuous
  have hcont : Continuous
      (fun r : ℝ ↦ NormedSpace.exp ((t - r) • A) (-(A (g r)) + g' r)) :=
    hflow.clm_apply (((A.continuous.comp hg_cont).neg).add hg')
  have h := intervalIntegral.sub_eq_integral_of_hasDerivAt hderiv hcont t₀ t
  have ht : NormedSpace.exp ((t - t) • A) (g t) = g t := by simp
  rw [ht] at h
  exact h.symm
