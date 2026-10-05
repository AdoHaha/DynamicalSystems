/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.K3IsoperimetricEulerLagrange

/-!
# Continuity of the actual first-variation covectors

Joint `C¹` regularity of a Lagrangian and `C¹` regularity of a curve imply
continuity of its state and velocity partial derivatives along the curve.
These are the actual Fréchet derivatives, with no independently supplied
covector regularity assumptions. The first-variation integrand is consequently
continuous for every `C¹` direction.

The final two lemmas give `C¹` regularity of the same covectors from primitive
`C²` data, so classical momentum derivatives exist at horizon endpoints as well.
-/

@[expose] public section

namespace KirkMedhin.K3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The state partial derivative is the joint derivative composed with the
constant injection of a state direction. -/
theorem fderiv_lagrangian_state_eq (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (t : ℝ) (a b : E) :
    fderiv ℝ (fun y : E ↦ L t y b) a =
      (fderiv ℝ (uncurryLagrangian L) (t, a, b)).comp
        ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.inl ℝ E E)) := by
  have hι : HasFDerivAt (fun y : E ↦ (t, y, b))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.inl ℝ E E)) a :=
    (hasFDerivAt_const t a).prodMk
      ((hasFDerivAt_id a).prodMk (hasFDerivAt_const b a))
  exact ((hL.differentiable one_ne_zero (t, a, b)).hasFDerivAt.comp a hι).fderiv

/-- The velocity partial derivative is the joint derivative composed with the
constant injection of a velocity direction. -/
theorem fderiv_lagrangian_velocity_eq (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (t : ℝ) (a b : E) :
    fderiv ℝ (fun v : E ↦ L t a v) b =
      (fderiv ℝ (uncurryLagrangian L) (t, a, b)).comp
        ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.inr ℝ E E)) := by
  have hι : HasFDerivAt (fun v : E ↦ (t, a, v))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.inr ℝ E E)) b :=
    (hasFDerivAt_const t b).prodMk
      ((hasFDerivAt_const a b).prodMk (hasFDerivAt_id b))
  exact ((hL.differentiable one_ne_zero (t, a, b)).hasFDerivAt.comp b hι).fderiv

/-- Continuity of the actual state covector along a `C¹` curve. -/
theorem continuous_stateCovector (L : ℝ → E → E → ℝ) (x : ℝ → E)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (hx : ContDiff ℝ 1 x) :
    Continuous (fun t ↦ fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t)) := by
  have hpath : Continuous (fun t ↦ (t, x t, deriv x t)) :=
    continuous_id.prodMk (hx.continuous.prodMk hx.continuous_deriv_one)
  have hjoint := (hL.continuous_fderiv one_ne_zero).comp hpath
  have hcomp := hjoint.clm_comp
    (continuous_const (y := (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.inl ℝ E E)))
  simpa only [fderiv_lagrangian_state_eq L hL, Function.comp_apply] using hcomp

/-- Continuity of the actual momentum covector along a `C¹` curve. -/
theorem continuous_momentumCovector (L : ℝ → E → E → ℝ) (x : ℝ → E)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (hx : ContDiff ℝ 1 x) :
    Continuous (fun t ↦ fderiv ℝ (fun v : E ↦ L t (x t) v) (deriv x t)) := by
  have hpath : Continuous (fun t ↦ (t, x t, deriv x t)) :=
    continuous_id.prodMk (hx.continuous.prodMk hx.continuous_deriv_one)
  have hjoint := (hL.continuous_fderiv one_ne_zero).comp hpath
  have hcomp := hjoint.clm_comp
    (continuous_const (y := (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.inr ℝ E E)))
  simpa only [fderiv_lagrangian_velocity_eq L hL, Function.comp_apply] using hcomp

/-- The actual first-variation integrand is continuous under primitive `C¹`
assumptions on the Lagrangian, reference curve, and direction. -/
theorem continuous_firstVariationIntegrand (L : ℝ → E → E → ℝ) (x η : ℝ → E)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 1 η) :
    Continuous (firstVariationIntegrand L x η) := by
  exact ((continuous_stateCovector L x hL hx).clm_apply hη.continuous).add
    ((continuous_momentumCovector L x hL hx).clm_apply hη.continuous_deriv_one)

/-- Joint `C²` Lagrangian data and a `C²` curve give `C¹` regularity of the
actual state covector, including at the endpoints of any chosen horizon. -/
theorem contDiff_stateCovector_of_contDiff_two (L : ℝ → E → E → ℝ) (x : ℝ → E)
    (hL : ContDiff ℝ 2 (uncurryLagrangian L)) (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (fun t ↦ fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t)) := by
  have hLone : ContDiff ℝ 1 (uncurryLagrangian L) := hL.of_le (by norm_num)
  have hxone : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hxderiv : ContDiff ℝ 1 (deriv x) := hx.deriv'
  have hpath : ContDiff ℝ 1 (fun t ↦ (t, x t, deriv x t)) :=
    contDiff_id.prodMk (hxone.prodMk hxderiv)
  have hjoint := (hL.fderiv_right (m := 1) (by norm_num)).comp hpath
  have hcomp := hjoint.clm_comp
    (contDiff_const (c := (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.inl ℝ E E)))
  simpa only [fderiv_lagrangian_state_eq L hLone, Function.comp_apply] using hcomp

/-- Joint `C²` Lagrangian data and a `C²` curve give `C¹` regularity of the
actual momentum covector, including at the endpoints of any chosen horizon. -/
theorem contDiff_momentumCovector_of_contDiff_two (L : ℝ → E → E → ℝ) (x : ℝ → E)
    (hL : ContDiff ℝ 2 (uncurryLagrangian L)) (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (fun t ↦ fderiv ℝ (fun v : E ↦ L t (x t) v) (deriv x t)) := by
  have hLone : ContDiff ℝ 1 (uncurryLagrangian L) := hL.of_le (by norm_num)
  have hxone : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hxderiv : ContDiff ℝ 1 (deriv x) := hx.deriv'
  have hpath : ContDiff ℝ 1 (fun t ↦ (t, x t, deriv x t)) :=
    contDiff_id.prodMk (hxone.prodMk hxderiv)
  have hjoint := (hL.fderiv_right (m := 1) (by norm_num)).comp hpath
  have hcomp := hjoint.clm_comp
    (contDiff_const (c := (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.inr ℝ E E)))
  simpa only [fderiv_lagrangian_velocity_eq L hLone, Function.comp_apply] using hcomp

end KirkMedhin.K3
