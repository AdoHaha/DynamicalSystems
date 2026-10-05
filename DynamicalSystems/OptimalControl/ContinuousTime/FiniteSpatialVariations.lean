/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.WeakCornerConditions
import DynamicalSystems.OptimalControl.ContinuousTime.WeakEulerLagrangeMinimum

/-!
# Actual spatial variations in the finite-piecewise ambient class

A smooth reference arc inherits actual fixed-endpoint minimality from any finite
surrounding context. The resulting Euler–Lagrange law is derived from primitive
C1 data. Actual join-moving variations then imply momentum matching.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace FinitePiecewise

open TimeReparametrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A differentiable curve with continuous velocity is C1; no acceleration is needed. -/
theorem contDiff_of_hasDerivAt_continuous {x v : ℝ → E}
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v) : ContDiff ℝ 1 x := by
  exact contDiff_one_iff_deriv.mpr
    ⟨fun t ↦ (hx t).differentiableAt, (funext fun t ↦ (hx t).deriv) ▸ hv⟩

/-- An autonomous C1 Lagrangian is jointly C1 after adjoining the time variable. -/
theorem contDiff_autonomous_lagrangian (L : E → E → ℝ)
    (hL : ContDiff ℝ 1 L.uncurry) : ContDiff ℝ 1 (uncurryLagrangian (fun _ ↦ L)) :=
  hL.comp contDiff_snd

/-- Integration of the derived interior Euler–Lagrange law gives the true boundary
first variation, including endpoint directions which need not vanish. -/
theorem firstVariation_eq_boundary_of_interior_EL
    (L : ℝ → E → E → ℝ) {T : ℝ} {x η : ℝ → E}
    (hT : 0 ≤ T) (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 1 η)
    (hEL : ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s ↦ fderiv ℝ (fun v ↦ L s (x s) v) (deriv x s))
        (fderiv ℝ (fun y ↦ L t y (deriv x t)) (x t)) t) :
    firstVariation L (fun _ ↦ 0) T x η =
      (fderiv ℝ (fun v ↦ L T (x T) v) (deriv x T)) (η T) -
      (fderiv ℝ (fun v ↦ L 0 (x 0) v) (deriv x 0)) (η 0) := by
  have hp := continuous_momentumCovector L x hL hx
  have hq := continuous_stateCovector L x hL hx
  have hc := (hq.clm_apply hη.continuous).add (hp.clm_apply hη.continuous_deriv_one)
  have hd : ∀ t ∈ Ioo 0 T, HasDerivAt
      (fun s ↦ (fderiv ℝ (fun v ↦ L s (x s) v) (deriv x s)) (η s))
      ((fderiv ℝ (fun y ↦ L t y (deriv x t)) (x t)) (η t) +
        (fderiv ℝ (fun v ↦ L t (x t) v) (deriv x t)) (deriv η t)) t := by
    intro t ht
    exact (hEL t ht).clm_apply (hη.differentiable one_ne_zero t).hasDerivAt
  simpa [firstVariation] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
      (hp.clm_apply hη.continuous).continuousOn hd (hc.intervalIntegrable 0 T)

/-- Every globally C1 arc belongs to the finite-piecewise class on a positive horizon. -/
theorem IsFinitePiecewiseC1.of_contDiff {T : ℝ} (hT : 0 < T)
    {x : ℝ → E} (hx : ContDiff ℝ 1 x) : IsFinitePiecewiseC1 T x :=
  .smooth hT (fun t ↦ (hx.differentiable one_ne_zero t).hasDerivAt)
    hx.continuous_deriv_one

/-- Actual finite-piecewise ambient optimality makes each C1 endpoint-zero spatial
variation stationary. Every perturbed curve is proved admissible. -/
theorem firstVariation_zero_of_finite_min
    (L : E → E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {T : ℝ} (hT : 0 < T) {x : ℝ → E} (hx : ContDiff ℝ 1 x)
    (hmin : IsMinOn (action L T)
      (fixedEndpointFinitePiecewiseC1Curves T (x 0) (x T)) x)
    (η : ℝ → E) (hη : ContDiff ℝ 1 η) (hη₀ : η 0 = 0) (hηT : η T = 0) :
    firstVariation (fun _ ↦ L) (fun _ ↦ 0) T x η = 0 := by
  have hd := hasDerivAt_cvFunctional_affine
    (fun _ ↦ L) (fun _ ↦ 0) T x η (contDiff_autonomous_lagrangian L hL)
    contDiff_const hx hη hT.le
  have hm : IsLocalMin
      (fun ε : ℝ ↦ cvFunctional (fun _ ↦ L) (fun _ ↦ 0) T (fun t ↦ x t + ε • η t)) 0 := by
    filter_upwards [] with ε
    have hp : ContDiff ℝ 1 (fun t ↦ x t + ε • η t) :=
      hx.add (contDiff_const.smul hη)
    have hf : (fun t ↦ x t + ε • η t) ∈
        fixedEndpointFinitePiecewiseC1Curves T (x 0) (x T) := by
      refine ⟨?_, ?_, .of_contDiff hT hp⟩
      · simp only [hη₀, smul_zero, add_zero]
      · simp only [hηT, smul_zero, add_zero]
    have hh : action L T x ≤ action L T (fun t ↦ x t + ε • η t) := hmin hf
    simpa only [cvFunctional, action, zero_smul, add_zero] using hh
  exact hm.hasDerivAt_eq_zero hd

/-- Interior Euler–Lagrange follows from the genuine finite-piecewise minimum.
Momentum differentiability is a conclusion, without differentiating velocity. -/
theorem interior_EL_of_finite_min
    (L : E → E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {T : ℝ} (hT : 0 < T) {x : ℝ → E} (hx : ContDiff ℝ 1 x)
    (hmin : IsMinOn (action L T)
      (fixedEndpointFinitePiecewiseC1Curves T (x 0) (x T)) x) :
    ∀ t ∈ Ioo 0 T, HasDerivAt (fun s ↦ fderiv ℝ (L (x s)) (deriv x s))
      (fderiv ℝ (fun y ↦ L y (deriv x t)) (x t)) t := by
  exact WeakEulerLagrange.eulerLagrange_hasDerivAt_of_firstVariation_zero hT
    (contDiff_autonomous_lagrangian L hL) hx
    (firstVariation_zero_of_finite_min L hL hT hx hmin)

/-- The original minimum in any finite surrounding context implies the actual
Euler–Lagrange differential equation on the interior of each C1 subarc. -/
theorem interior_EL_in_finite_context
    (L : E → E → ℝ) (K : E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v)
    {d : ℝ} (hd : 0 < d) {T : ℝ} {A B : E} {F : (ℝ → E) → ℝ → E}
    (ctx : SpliceContext d (x 0) (x d) T A B F)
    (hmin : IsMinOn (cvFunctional (fun _ ↦ L) K T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) (F x)) :
    ∀ t ∈ Ioo 0 d, HasDerivAt (fun s ↦ fderiv ℝ (L (x s)) (v s))
      (fderiv ℝ (fun y ↦ L y (v t)) (x t)) t := by
  have href : x ∈ fixedEndpointFinitePiecewiseC1Curves d (x 0) (x d) :=
    ⟨rfl, rfl, .smooth hd hx hv⟩
  have hm := ctx.action_min L hL.continuous href
    (action_min_of_cvFunctional_min L K (ctx.feasible href).2.1 hmin)
  have he := interior_EL_of_finite_min L hL hd (contDiff_of_hasDerivAt_continuous hx hv) hm
  simpa only [funext fun t ↦ (hx t).deriv] using he

/-- A genuine spatial displacement of the join gives the sum of the two actual
first variations equal to zero. No stationarity identity is assumed. -/
theorem twoArc_firstVariation_zero_of_action_min
    (L : E → E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {x₁ x₂ : ℝ → E} (hx₁ : ContDiff ℝ 1 x₁) (hx₂ : ContDiff ℝ 1 x₂)
    (hjoin : x₁ d₁ = x₂ 0)
    (hmin : IsMinOn (action L (d₁ + d₂))
      (fixedEndpointFinitePiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂))
      (concatenate d₁ x₁ x₂))
    (η₁ η₂ : ℝ → E) (hη₁ : ContDiff ℝ 1 η₁) (hη₂ : ContDiff ℝ 1 η₂)
    (hη₀ : η₁ 0 = 0) (hηT : η₂ d₂ = 0) (hηjoin : η₁ d₁ = η₂ 0) :
    firstVariation (fun _ ↦ L) (fun _ ↦ 0) d₁ x₁ η₁ +
      firstVariation (fun _ ↦ L) (fun _ ↦ 0) d₂ x₂ η₂ = 0 := by
  let f := fun ε : ℝ ↦
    action L d₁ (fun t ↦ x₁ t + ε • η₁ t) + action L d₂ (fun t ↦ x₂ t + ε • η₂ t)
  have h₁ := hasDerivAt_cvFunctional_affine
    (fun _ ↦ L) (fun _ ↦ 0) d₁ x₁ η₁ (contDiff_autonomous_lagrangian L hL)
    contDiff_const hx₁ hη₁ hd₁.le
  have h₂ := hasDerivAt_cvFunctional_affine
    (fun _ ↦ L) (fun _ ↦ 0) d₂ x₂ η₂ (contDiff_autonomous_lagrangian L hL)
    contDiff_const hx₂ hη₂ hd₂.le
  have hf : HasDerivAt f
      (firstVariation (fun _ ↦ L) (fun _ ↦ 0) d₁ x₁ η₁ +
        firstVariation (fun _ ↦ L) (fun _ ↦ 0) d₂ x₂ η₂) 0 := by
    convert h₁.add h₂ using 1
    funext ε
    simp [f, action, cvFunctional]
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
    change action L (d₁ + d₂) (concatenate d₁ x₁ x₂) ≤
      action L (d₁ + d₂) (concatenate d₁
        (fun t ↦ x₁ t + ε • η₁ t) (fun t ↦ x₂ t + ε • η₂ t)) at hh
    rw [action_concatenate L hL.continuous (.of_contDiff hd₁ hx₁) (.of_contDiff hd₂ hx₂),
      action_concatenate L hL.continuous (.of_contDiff hd₁ hp₁) (.of_contDiff hd₂ hp₂)] at hh
    simpa only [f, zero_smul, add_zero] using hh
  exact hm.hasDerivAt_eq_zero hf

/-- Actual ambient optimality forces the two one-sided momentum covectors to agree.
Interior Euler–Lagrange and join-displacement stationarity are both derived here. -/
theorem corner_momentum_eq_of_cvFunctional_min_weak
    (L : E → E → ℝ) (K : E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hjoin : x₁ d₁ = x₂ 0)
    (hmin : IsMinOn (cvFunctional (fun _ ↦ L) K (d₁ + d₂))
      (fixedEndpointFinitePiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂))
      (concatenate d₁ x₁ x₂)) :
    fderiv ℝ (L (x₁ d₁)) (v₁ d₁) = fderiv ℝ (L (x₂ 0)) (v₂ 0) := by
  have hc₁ := contDiff_of_hasDerivAt_continuous hx₁ hv₁
  have hc₂ := contDiff_of_hasDerivAt_continuous hx₂ hv₂
  have h₁ : IsFinitePiecewiseC1 d₁ x₁ := .smooth hd₁ hx₁ hv₁
  have h₂ : IsFinitePiecewiseC1 d₂ x₂ := .smooth hd₂ hx₂ hv₂
  have href := concatenate_mem_fixedEndpointFinitePiecewiseC1Curves h₁ h₂ hjoin
  have hm := action_min_of_cvFunctional_min L K href.2.1 hmin
  have he₁ := interior_EL_of_finite_min L hL hd₁ hc₁
    (action_min_left L hL.continuous h₁ h₂ hjoin hm)
  have he₂ := interior_EL_of_finite_min L hL hd₂ hc₂
    (action_min_right L hL.continuous h₁ h₂ hjoin hm)
  ext z
  let η₁ : ℝ → E := fun t ↦ (t / d₁) • z
  let η₂ : ℝ → E := fun t ↦ (1 - t / d₂) • z
  have hη₁ : ContDiff ℝ 1 η₁ := (contDiff_id.div_const d₁).smul contDiff_const
  have hη₂ : ContDiff ℝ 1 η₂ :=
    (contDiff_const.sub (contDiff_id.div_const d₂)).smul contDiff_const
  have hη₀ : η₁ 0 = 0 := by simp [η₁]
  have hηT : η₂ d₂ = 0 := by simp [η₂, ne_of_gt hd₂]
  have hηj : η₁ d₁ = η₂ 0 := by simp [η₁, η₂, ne_of_gt hd₁]
  have hz := twoArc_firstVariation_zero_of_action_min L hL hd₁ hd₂ hc₁ hc₂ hjoin hm
    η₁ η₂ hη₁ hη₂ hη₀ hηT hηj
  rw [firstVariation_eq_boundary_of_interior_EL (fun _ ↦ L) hd₁.le
      (contDiff_autonomous_lagrangian L hL) hc₁ hη₁ he₁,
    firstVariation_eq_boundary_of_interior_EL (fun _ ↦ L) hd₂.le
      (contDiff_autonomous_lagrangian L hL) hc₂ hη₂ he₂] at hz
  simpa [η₁, η₂, ne_of_gt hd₁, ne_of_gt hd₂, (hx₁ d₁).deriv,
    (hx₂ 0).deriv, add_neg_eq_zero] using hz

/-- Momentum matching at every corner embedded in arbitrary finite surrounding arcs. -/
theorem corner_momentum_eq_in_finite_context
    (L : E → E → ℝ) (K : E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hjoin : x₁ d₁ = x₂ 0)
    {T : ℝ} {A B : E} {F : (ℝ → E) → ℝ → E}
    (ctx : SpliceContext (d₁ + d₂) (x₁ 0) (x₂ d₂) T A B F)
    (hmin : IsMinOn (cvFunctional (fun _ ↦ L) K T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) (F (concatenate d₁ x₁ x₂))) :
    fderiv ℝ (L (x₁ d₁)) (v₁ d₁) = fderiv ℝ (L (x₂ 0)) (v₂ 0) := by
  have href := concatenate_mem_fixedEndpointFinitePiecewiseC1Curves
    (.smooth hd₁ hx₁ hv₁) (.smooth hd₂ hx₂ hv₂) hjoin
  have hamb := ctx.feasible href
  have hm := ctx.action_min L hL.continuous href
    (action_min_of_cvFunctional_min L K hamb.2.1 hmin)
  exact corner_momentum_eq_of_cvFunctional_min_weak L (fun _ ↦ 0) hL hx₁ hv₁ hx₂ hv₂
    hd₁ hd₂ hjoin (cvFunctional_min_of_action_min L _ href.2.1 hm)

/-- Both Weierstrass–Erdmann corner conditions follow from the original finite-piecewise
ambient optimum under C1 Lagrangian and arc data, at every finite-context corner. -/
theorem weierstrassErdmann_of_cvFunctional_min_weak
    (L : E → E → ℝ) (K : E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hjoin : x₁ d₁ = x₂ 0)
    {T : ℝ} {A B : E} {F : (ℝ → E) → ℝ → E}
    (ctx : SpliceContext (d₁ + d₂) (x₁ 0) (x₂ d₂) T A B F)
    (hmin : IsMinOn (cvFunctional (fun _ ↦ L) K T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) (F (concatenate d₁ x₁ x₂))) :
    fderiv ℝ (L (x₁ d₁)) (v₁ d₁) = fderiv ℝ (L (x₂ 0)) (v₂ 0) ∧
      energyCurve L x₁ v₁ d₁ = energyCurve L x₂ v₂ 0 :=
  ⟨corner_momentum_eq_in_finite_context L K hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hjoin ctx hmin,
    corner_energy_eq_in_finite_context L K hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hjoin ctx hmin⟩

end FinitePiecewise
