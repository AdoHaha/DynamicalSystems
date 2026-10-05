/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.FiniteSpatialVariations
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFinitePiecewiseVariations

/-!
# Nonautonomous spatial corner conditions from actual ambient minima

Time-offset subarc costs preserve the original physical time. Actual spatial
variations derive interior Euler–Lagrange and momentum matching at every corner
represented by a finite surrounding context.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace KirkMedhin.FinitePiecewise

open TimeReparametrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translating the physical time origin preserves joint C1 regularity. -/
theorem contDiff_timeShift (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L)) (t0 : ℝ) :
    ContDiff ℝ 1 (K3.uncurryLagrangian (fun t ↦ L (t0 + t))) := by
  exact hL.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)

/-- Genuine time-dependent finite-piecewise minimality implies the interior
Euler–Lagrange equation on the selected C1 arc at its actual physical time. -/
theorem interior_EL_of_timeAction_min
    (L : ℝ → E → E → ℝ) (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L)) (t0 : ℝ)
    {T : ℝ} (hT : 0 < T) {x : ℝ → E} (hx : ContDiff ℝ 1 x)
    (hmin : IsMinOn (timeAction L t0 T)
      (fixedEndpointFinitePiecewiseC1Curves T (x 0) (x T)) x) :
    ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s ↦ fderiv ℝ (L (t0 + s) (x s)) (deriv x s))
        (fderiv ℝ (fun y ↦ L (t0 + t) y (deriv x t)) (x t)) t := by
  apply WeakCoV.eulerLagrange_hasDerivAt_of_fixedEndpoint_min
    (fun t ↦ L (t0 + t)) (fun _ ↦ 0) T x (contDiff_timeShift L hL t0)
    contDiff_const hx hT
  intro y hy
  have hf : y ∈ fixedEndpointFinitePiecewiseC1Curves T (x 0) (x T) :=
    ⟨hy.2.1, hy.2.2, .of_contDiff hT hy.1⟩
  have hh : timeAction L t0 T x ≤ timeAction L t0 T y := hmin hf
  change cvFunctional (fun t ↦ L (t0 + t)) (fun _ ↦ 0) T x ≤
    cvFunctional (fun t ↦ L (t0 + t)) (fun _ ↦ 0) T y
  simpa only [cvFunctional, timeAction, add_zero] using hh

/-- Every C1 arc in a timed finite context satisfies the derived momentum ODE. -/
theorem interior_EL_in_timeSpliceContext
    (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L))
    {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v)
    {start d : ℝ} (hd : 0 < d) {t0 T : ℝ} {A B : E}
    {F : (ℝ → E) → ℝ → E}
    (ctx : TimeSpliceContext start d (x 0) (x d) t0 T A B F)
    (hmin : IsMinOn (cvFunctional (fun t ↦ L (t0 + t)) K T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) (F x)) :
    ∀ t ∈ Ioo 0 d, HasDerivAt (fun s ↦ fderiv ℝ (L (start + s) (x s)) (v s))
      (fderiv ℝ (fun y ↦ L (start + t) y (v t)) (x t)) t := by
  have href : x ∈ fixedEndpointFinitePiecewiseC1Curves d (x 0) (x d) :=
    ⟨rfl, rfl, .smooth hd hx hv⟩
  have hm := ctx.timeAction_min L hL.continuous href
    (timeAction_min_of_cvFunctional_min L K t0 (ctx.feasible href).2.1 hmin)
  have he := interior_EL_of_timeAction_min L hL start hd
    (contDiff_of_hasDerivAt_continuous hx hv) hm
  simpa only [funext fun t ↦ (hx t).deriv] using he

/-- A true join displacement gives the sum of the time-offset first variations.
Physical time is retained in both integrals. -/
theorem twoArc_firstVariation_zero_of_timeAction_min
    (L : ℝ → E → E → ℝ) (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L)) (t0 : ℝ)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {x₁ x₂ : ℝ → E} (hx₁ : ContDiff ℝ 1 x₁) (hx₂ : ContDiff ℝ 1 x₂)
    (hjoin : x₁ d₁ = x₂ 0)
    (hmin : IsMinOn (timeAction L t0 (d₁ + d₂))
      (fixedEndpointFinitePiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂))
      (concatenate d₁ x₁ x₂))
    (η₁ η₂ : ℝ → E) (hη₁ : ContDiff ℝ 1 η₁) (hη₂ : ContDiff ℝ 1 η₂)
    (hη₀ : η₁ 0 = 0) (hηT : η₂ d₂ = 0) (hηjoin : η₁ d₁ = η₂ 0) :
    firstVariation (fun t ↦ L (t0 + t)) (fun _ ↦ 0) d₁ x₁ η₁ +
      firstVariation (fun t ↦ L ((t0 + d₁) + t)) (fun _ ↦ 0) d₂ x₂ η₂ = 0 := by
  let f := fun ε : ℝ ↦
    timeAction L t0 d₁ (fun t ↦ x₁ t + ε • η₁ t) +
      timeAction L (t0 + d₁) d₂ (fun t ↦ x₂ t + ε • η₂ t)
  have h₁ := WeakCoV.hasDerivAt_cvFunctional_affine
    (fun t ↦ L (t0 + t)) (fun _ ↦ 0) d₁ x₁ η₁ (contDiff_timeShift L hL t0)
    contDiff_const hx₁ hη₁ hd₁.le
  have h₂ := WeakCoV.hasDerivAt_cvFunctional_affine
    (fun t ↦ L ((t0 + d₁) + t)) (fun _ ↦ 0) d₂ x₂ η₂
    (contDiff_timeShift L hL (t0 + d₁)) contDiff_const hx₂ hη₂ hd₂.le
  have hf : HasDerivAt f
      (firstVariation (fun t ↦ L (t0 + t)) (fun _ ↦ 0) d₁ x₁ η₁ +
        firstVariation (fun t ↦ L ((t0 + d₁) + t)) (fun _ ↦ 0) d₂ x₂ η₂) 0 := by
    convert h₁.add h₂ using 1
    funext ε
    simp [f, timeAction, cvFunctional]
  have hm : IsLocalMin f 0 := by
    filter_upwards [] with ε
    have hp₁ : ContDiff ℝ 1 (fun t ↦ x₁ t + ε • η₁ t) :=
      hx₁.add (contDiff_const.smul hη₁)
    have hp₂ : ContDiff ℝ 1 (fun t ↦ x₂ t + ε • η₂ t) :=
      hx₂.add (contDiff_const.smul hη₂)
    have hpj : x₁ d₁ + ε • η₁ d₁ = x₂ 0 + ε • η₂ 0 := by rw [hjoin, hηjoin]
    have hc := concatenate_mem_fixedEndpointFinitePiecewiseC1Curves
      (.of_contDiff hd₁ hp₁) (.of_contDiff hd₂ hp₂) hpj
    simp only [hη₀, hηT, smul_zero, add_zero] at hc
    have hh := hmin hc
    change timeAction L t0 (d₁ + d₂) (concatenate d₁ x₁ x₂) ≤
      timeAction L t0 (d₁ + d₂) (concatenate d₁
        (fun t ↦ x₁ t + ε • η₁ t) (fun t ↦ x₂ t + ε • η₂ t)) at hh
    rw [timeAction_concatenate L hL.continuous t0
        (.of_contDiff hd₁ hx₁) (.of_contDiff hd₂ hx₂),
      timeAction_concatenate L hL.continuous t0 (.of_contDiff hd₁ hp₁) (.of_contDiff hd₂ hp₂)] at hh
    simpa only [f, zero_smul, add_zero] using hh
  exact hm.hasDerivAt_eq_zero hf

/-- Nonautonomous momentum matching from the actual finite-piecewise minimum,
with only C1 state arcs and no acceleration or Euler–Lagrange premise. -/
theorem corner_momentum_eq_of_timeAction_min
    (L : ℝ → E → E → ℝ) (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L)) (t0 : ℝ)
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hjoin : x₁ d₁ = x₂ 0)
    (hmin : IsMinOn (timeAction L t0 (d₁ + d₂))
      (fixedEndpointFinitePiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂))
      (concatenate d₁ x₁ x₂)) :
    fderiv ℝ (L (t0 + d₁) (x₁ d₁)) (v₁ d₁) =
      fderiv ℝ (L (t0 + d₁) (x₂ 0)) (v₂ 0) := by
  have hc₁ := contDiff_of_hasDerivAt_continuous hx₁ hv₁
  have hc₂ := contDiff_of_hasDerivAt_continuous hx₂ hv₂
  have h₁ : IsFinitePiecewiseC1 d₁ x₁ := .smooth hd₁ hx₁ hv₁
  have h₂ : IsFinitePiecewiseC1 d₂ x₂ := .smooth hd₂ hx₂ hv₂
  have he₁ := interior_EL_of_timeAction_min L hL t0 hd₁ hc₁
    (timeAction_min_left L hL.continuous t0 h₁ h₂ hjoin hmin)
  have he₂ := interior_EL_of_timeAction_min L hL (t0 + d₁) hd₂ hc₂
    (timeAction_min_right L hL.continuous t0 h₁ h₂ hjoin hmin)
  ext z
  let η₁ : ℝ → E := fun t ↦ (t / d₁) • z
  let η₂ : ℝ → E := fun t ↦ (1 - t / d₂) • z
  have hη₁ : ContDiff ℝ 1 η₁ := (contDiff_id.div_const d₁).smul contDiff_const
  have hη₂ : ContDiff ℝ 1 η₂ :=
    (contDiff_const.sub (contDiff_id.div_const d₂)).smul contDiff_const
  have hη₀ : η₁ 0 = 0 := by simp [η₁]
  have hηT : η₂ d₂ = 0 := by simp [η₂, ne_of_gt hd₂]
  have hηj : η₁ d₁ = η₂ 0 := by simp [η₁, η₂, ne_of_gt hd₁]
  have hz := twoArc_firstVariation_zero_of_timeAction_min L hL t0 hd₁ hd₂ hc₁ hc₂ hjoin
    hmin η₁ η₂ hη₁ hη₂ hη₀ hηT hηj
  rw [firstVariation_eq_boundary_of_interior_EL (fun t ↦ L (t0 + t)) hd₁.le
      (contDiff_timeShift L hL t0) hc₁ hη₁ he₁,
    firstVariation_eq_boundary_of_interior_EL (fun t ↦ L ((t0 + d₁) + t)) hd₂.le
      (contDiff_timeShift L hL (t0 + d₁)) hc₂ hη₂ he₂] at hz
  simpa [η₁, η₂, ne_of_gt hd₁, ne_of_gt hd₂, (hx₁ d₁).deriv,
    (hx₂ 0).deriv, add_neg_eq_zero] using hz

/-- Nonautonomous momentum matching in any actual finite surrounding context. -/
theorem corner_momentum_eq_in_timeSpliceContext
    (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L))
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {start d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hjoin : x₁ d₁ = x₂ 0)
    {t0 T : ℝ} {A B : E} {F : (ℝ → E) → ℝ → E}
    (ctx : TimeSpliceContext start (d₁ + d₂) (x₁ 0) (x₂ d₂) t0 T A B F)
    (hmin : IsMinOn (cvFunctional (fun t ↦ L (t0 + t)) K T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) (F (concatenate d₁ x₁ x₂))) :
    fderiv ℝ (L (start + d₁) (x₁ d₁)) (v₁ d₁) =
      fderiv ℝ (L (start + d₁) (x₂ 0)) (v₂ 0) := by
  have href := concatenate_mem_fixedEndpointFinitePiecewiseC1Curves
    (.smooth hd₁ hx₁ hv₁) (.smooth hd₂ hx₂ hv₂) hjoin
  have hm := ctx.timeAction_min L hL.continuous href
    (timeAction_min_of_cvFunctional_min L K t0 (ctx.feasible href).2.1 hmin)
  exact corner_momentum_eq_of_timeAction_min L hL start hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hjoin hm

end KirkMedhin.FinitePiecewise
