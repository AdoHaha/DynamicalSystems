/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteSpatialVariations
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousDuBoisReymond

/-!
# Nonautonomous energy and corner laws for finite-piecewise minima

Actual spliced subarc minima imply the compensated du Bois–Reymond law without
an acceleration assumption. Actual duration exchanges then match the corner
energies, while the spatial variations supply momentum matching.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace KirkMedhin.FinitePiecewise

open TimeReparametrization DuBoisReymond NonautonomousTimeReparametrization
open NonautonomousDuBoisReymond

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Nonautonomous weak du Bois–Reymond follows from the original minimum among
finite-piecewise competitors; all inner time variations are constructed. -/
theorem weak_duBoisReymond_of_finite_cvFunctional_min
    (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L))
    {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v)
    {T : ℝ} (hT : 0 < T)
    (hmin : IsMinOn (cvFunctional L K T)
      (fixedEndpointFinitePiecewiseC1Curves T (x 0) (x T)) x) :
    (∀ t ∈ Icc 0 T, energyCurve L x v t + (∫ s in 0..t, timePartialCurve L x v s) =
      energyCurve L x v 0) ∧
    (∀ t ∈ Ioo 0 T, HasDerivAt (energyCurve L x v) (-timePartialCurve L x v t) t) := by
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t ↦ (hx t).continuousAt
  apply weak_duBoisReymond_of_all_duration_exchange_min L hL hxc hv hT
  intro a ha
  have hd : 0 < T - a := sub_pos.mpr ha.2
  have hsum : a + (T - a) = T := by ring
  have hvshift : Continuous (fun s ↦ v (a + s)) :=
    hv.comp (continuous_const.add continuous_id)
  have hjoin : x a = (fun s ↦ x (a + s)) 0 := by simp
  apply fixedParameterCost_isLocalMin_of_ambient_min L K hL.continuous hx hv
    (hasDerivAt_shifted hx a) hvshift ha.1 hd
    (fixedEndpointFinitePiecewiseC1Curves (a + (T - a)) (x 0) (x (a + (T - a))))
  · intro ε hε
    exact durationExchange_mem_fixedEndpointFinitePiecewiseC1Curves
      hx hv (hasDerivAt_shifted hx a) hvshift ha.1 hd hjoin hε
  · simpa only [hsum, concatenate_shifted] using hmin

/-- Every represented C1 subarc of the genuine finite-piecewise optimum satisfies
both the integrated energy law and the interior nonautonomous energy ODE. -/
theorem weak_duBoisReymond_in_timeSpliceContext
    (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L))
    {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v)
    {start d : ℝ} (hd : 0 < d) {t0 T : ℝ} {A B : E}
    {F : (ℝ → E) → ℝ → E}
    (ctx : TimeSpliceContext start d (x 0) (x d) t0 T A B F)
    (hmin : IsMinOn (cvFunctional (fun t ↦ L (t0 + t)) K T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) (F x)) :
    (∀ t ∈ Icc 0 d,
      energyCurve (fun s ↦ L (start + s)) x v t +
        (∫ s in 0..t, timePartialCurve (fun r ↦ L (start + r)) x v s) =
      energyCurve (fun s ↦ L (start + s)) x v 0) ∧
    (∀ t ∈ Ioo 0 d,
      HasDerivAt (energyCurve (fun s ↦ L (start + s)) x v)
        (-timePartialCurve (fun s ↦ L (start + s)) x v t) t) := by
  have href : x ∈ fixedEndpointFinitePiecewiseC1Curves d (x 0) (x d) :=
    ⟨rfl, rfl, .smooth hd hx hv⟩
  have hm := ctx.timeAction_min L hL.continuous href
    (timeAction_min_of_cvFunctional_min L K t0 (ctx.feasible href).2.1 hmin)
  exact weak_duBoisReymond_of_finite_cvFunctional_min
    (fun t ↦ L (start + t)) (fun _ ↦ 0) (contDiff_timeShift L hL start) hx hv hd
    (cvFunctional_min_of_timeAction_min L _ start rfl hm)

/-- A nonautonomous actual finite-piecewise minimum implies corner-energy matching.
The interior energy derivatives and scalar duration minimum are derived in the proof. -/
theorem corner_energy_eq_of_timeAction_min_weak
    (L : ℝ → E → E → ℝ) (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L)) (t0 : ℝ)
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hjoin : x₁ d₁ = x₂ 0)
    (hmin : IsMinOn (timeAction L t0 (d₁ + d₂))
      (fixedEndpointFinitePiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂))
      (concatenate d₁ x₁ x₂)) :
    fderiv ℝ (L (t0 + d₁) (x₁ d₁)) (v₁ d₁) (v₁ d₁) -
        L (t0 + d₁) (x₁ d₁) (v₁ d₁) =
      fderiv ℝ (L (t0 + d₁) (x₂ 0)) (v₂ 0) (v₂ 0) -
        L (t0 + d₁) (x₂ 0) (v₂ 0) := by
  have h₁ : IsFinitePiecewiseC1 d₁ x₁ := .smooth hd₁ hx₁ hv₁
  have h₂ : IsFinitePiecewiseC1 d₂ x₂ := .smooth hd₂ hx₂ hv₂
  have href := concatenate_mem_fixedEndpointFinitePiecewiseC1Curves h₁ h₂ hjoin
  have hm₁ := timeAction_min_left L hL.continuous t0 h₁ h₂ hjoin hmin
  have hm₂ := timeAction_min_right L hL.continuous t0 h₁ h₂ hjoin hmin
  have hE₁ := (weak_duBoisReymond_of_finite_cvFunctional_min
    (fun t ↦ L (t0 + t)) (fun _ ↦ 0) (contDiff_timeShift L hL t0) hx₁ hv₁ hd₁
    (cvFunctional_min_of_timeAction_min L _ t0 rfl hm₁)).2
  have hE₂ := (weak_duBoisReymond_of_finite_cvFunctional_min
    (fun t ↦ L ((t0 + d₁) + t)) (fun _ ↦ 0) (contDiff_timeShift L hL (t0 + d₁))
    hx₂ hv₂ hd₂ (cvFunctional_min_of_timeAction_min L _ (t0 + d₁) rfl hm₂)).2
  have hxc₁ : Continuous x₁ := continuous_iff_continuousAt.mpr fun t ↦ (hx₁ t).continuousAt
  have hxc₂ : Continuous x₂ := continuous_iff_continuousAt.mpr fun t ↦ (hx₂ t).continuousAt
  have hscalar : IsLocalMin
      (fixedParameterCost (fun t ↦ L (t0 + t)) x₁ v₁ x₂ v₂ d₁ d₂) 0 := by
    apply fixedParameterCost_isLocalMin_of_ambient_min (fun t ↦ L (t0 + t)) (fun _ ↦ 0)
      (contDiff_timeShift L hL t0).continuous hx₁ hv₁ hx₂ hv₂ hd₁ hd₂
      (fixedEndpointFinitePiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂))
    · intro ε hε
      exact durationExchange_mem_fixedEndpointFinitePiecewiseC1Curves
        hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hjoin hε
    · exact cvFunctional_min_of_timeAction_min L _ t0 href.2.1 hmin
  have he := corner_energy_eq_of_weak_dbr_min (fun t ↦ L (t0 + t))
    (contDiff_timeShift L hL t0) hxc₁ hv₁ hxc₂ hv₂ hd₁ hd₂ hE₁
    (by simpa only [add_assoc] using hE₂) hscalar
  simpa only [NonautonomousDuBoisReymond.energyCurve, _root_.energyCurve, add_zero] using he

/-- Nonautonomous energy matching at any corner in a finite surrounding context. -/
theorem corner_energy_eq_in_timeSpliceContext
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
    fderiv ℝ (L (start + d₁) (x₁ d₁)) (v₁ d₁) (v₁ d₁) -
        L (start + d₁) (x₁ d₁) (v₁ d₁) =
      fderiv ℝ (L (start + d₁) (x₂ 0)) (v₂ 0) (v₂ 0) -
        L (start + d₁) (x₂ 0) (v₂ 0) := by
  have href := concatenate_mem_fixedEndpointFinitePiecewiseC1Curves
    (.smooth hd₁ hx₁ hv₁) (.smooth hd₂ hx₂ hv₂) hjoin
  have hm := ctx.timeAction_min L hL.continuous href
    (timeAction_min_of_cvFunctional_min L K t0 (ctx.feasible href).2.1 hmin)
  exact corner_energy_eq_of_timeAction_min_weak L hL start hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hjoin hm

/-- Both nonautonomous Weierstrass–Erdmann conditions follow from the actual global
minimum at every finite-context corner, with continuous velocities and no acceleration. -/
theorem weierstrassErdmann_in_timeSpliceContext
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
        fderiv ℝ (L (start + d₁) (x₂ 0)) (v₂ 0) ∧
      fderiv ℝ (L (start + d₁) (x₁ d₁)) (v₁ d₁) (v₁ d₁) -
          L (start + d₁) (x₁ d₁) (v₁ d₁) =
        fderiv ℝ (L (start + d₁) (x₂ 0)) (v₂ 0) (v₂ 0) -
          L (start + d₁) (x₂ 0) (v₂ 0) :=
  ⟨corner_momentum_eq_in_timeSpliceContext L K hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hjoin ctx hmin,
    corner_energy_eq_in_timeSpliceContext L K hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hjoin ctx hmin⟩

end KirkMedhin.FinitePiecewise
