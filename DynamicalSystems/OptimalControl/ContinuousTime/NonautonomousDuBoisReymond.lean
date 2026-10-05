/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.DuBoisReymond
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousTimeReparametrization
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousTimeReparametrizationFamily
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Nonautonomous weak du Bois–Reymond from the actual functional minimum

The actual duration-exchange competitors preserve both endpoints. Their exact
cost identity and the chain-rule derivative of the rescaled density yield the
hat-weight identity. The scalar weak argument then derives the interior energy
equation and its integrated form using only continuous velocity.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace KirkMedhin.NonautonomousDuBoisReymond

open KirkMedhin.K3 KirkMedhin.TimeReparametrization
open KirkMedhin.NonautonomousTimeReparametrization KirkMedhin.DuBoisReymond

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluate the project's existing energy at the current time slice of a
time-dependent Lagrangian. This is an adapter of the original energy model. -/
noncomputable def energyCurve (L : ℝ → E → E → ℝ) (x v : ℝ → E) (t : ℝ) : ℝ :=
  _root_.energyCurve (L t) x v t

/-- The genuine partial time derivative evaluated along the reference state and velocity. -/
noncomputable def timePartialCurve (L : ℝ → E → E → ℝ) (x v : ℝ → E) (t : ℝ) : ℝ :=
  deriv (fun s => L s (x t) (v t)) t

theorem continuous_timePartialCurve (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) {x v : ℝ → E}
    (hx : Continuous x) (hv : Continuous v) : Continuous (timePartialCurve L x v) := by
  have h := ((hL.continuous_fderiv one_ne_zero).comp
    (continuous_id.prodMk (hx.prodMk hv))).clm_apply
      (continuous_const : Continuous (fun _ : ℝ => ((1 : ℝ), (0 : E), (0 : E))))
  have heq : timePartialCurve L x v = fun t =>
      fderiv ℝ (uncurryLagrangian L) (t, x t, v t) (1, 0, 0) := by
    funext t
    exact time_deriv_eq L hL t (x t) (v t)
  rw [heq]
  exact h

theorem continuous_energyCurve (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) {x v : ℝ → E}
    (hx : Continuous x) (hv : Continuous v) : Continuous (energyCurve L x v) := by
  have hp : Continuous (fun t => (t, x t, v t)) :=
    continuous_id.prodMk (hx.prodMk hv)
  have hw : Continuous (fun t => ((0 : ℝ), (0 : E), v t)) :=
    continuous_const.prodMk (continuous_const.prodMk hv)
  have h := (((hL.continuous_fderiv one_ne_zero).comp hp).clm_apply
    hw).sub (hL.continuous.comp hp)
  have heq : energyCurve L x v = fun t =>
      fderiv ℝ (uncurryLagrangian L) (t, x t, v t) (0, 0, v t) - L t (x t) (v t) := by
    funext t
    exact congrArg (fun z => z - L t (x t) (v t))
      (velocity_fderiv_eq L hL t (x t) (v t) (v t))
  rw [heq]
  exact h

/-- The fixed-parameter cost is exactly the sum of the two moving-density integrals. -/
theorem fixedParameterCost_eq_movingArcCost (L : ℝ → E → E → ℝ)
    (x₁ v₁ x₂ v₂ : ℝ → E) (d₁ : ℝ) {d₂ : ℝ} (hd₂ : d₂ ≠ 0) (ε : ℝ) :
    fixedParameterCost L x₁ v₁ x₂ v₂ d₁ d₂ ε =
      movingArcCost L id id x₁ v₁ d₁ (1 + ε / d₁) +
      movingArcCost L (fun t => d₁ + t) (fun t => t - d₂)
        x₂ v₂ d₂ (1 - ε / d₂) := by
  unfold fixedParameterCost movingArcCost movingDensity
  congr 1
  · apply intervalIntegral.integral_congr
    intro t _
    have ht : (1 + ε / d₁) * t = t + (1 + ε / d₁ - 1) * t := by ring
    simp only [id_eq, ht]
  · apply intervalIntegral.integral_congr
    intro t _
    have ht : d₁ + ε + (1 - ε / d₂) * t =
        d₁ + t + (1 - ε / d₂ - 1) * (t - d₂) := by
      field_simp
      ring
    dsimp only
    rw [ht]

/-- Differentiate the actual fixed-parameter cost, including the shifted origin
of the right arc. The state and velocity need only be continuous. -/
theorem hasDerivAt_fixedParameterCost (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : Continuous x₁) (hv₁ : Continuous v₁)
    (hx₂ : Continuous x₂) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    HasDerivAt (fixedParameterCost L x₁ v₁ x₂ v₂ d₁ d₂)
      ((∫ t in 0..d₁, t * deriv (fun s => L s (x₁ t) (v₁ t)) t -
          (fderiv ℝ (L t (x₁ t)) (v₁ t) (v₁ t) - L t (x₁ t) (v₁ t))) / d₁ -
       (∫ t in 0..d₂, (t - d₂) * deriv (fun s => L s (x₂ t) (v₂ t)) (d₁ + t) -
          (fderiv ℝ (L (d₁ + t) (x₂ t)) (v₂ t) (v₂ t) -
            L (d₁ + t) (x₂ t) (v₂ t))) / d₂) 0 := by
  have hleft : HasDerivAt (fun ε : ℝ => 1 + ε / d₁) (1 / d₁) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const d₁).const_add 1
  have hright : HasDerivAt (fun ε : ℝ => 1 - ε / d₂) (-(1 / d₂)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const d₂).const_sub 1
  have h₁base := hasDerivAt_movingArcCost L hL continuous_id continuous_id hx₁ hv₁ hd₁.le
  have h₁ := h₁base.comp_of_eq 0 hleft (by simp)
  simp only [id_eq] at h₁
  have h₂base := hasDerivAt_movingArcCost L hL
    (θ := fun t => d₁ + t) (α := fun t => t - d₂)
    (continuous_const.add continuous_id) (continuous_id.sub continuous_const) hx₂ hv₂ hd₂.le
  have h₂ := h₂base.comp_of_eq 0 hright (by simp)
  have hfun : fixedParameterCost L x₁ v₁ x₂ v₂ d₁ d₂ = fun ε =>
      movingArcCost L id id x₁ v₁ d₁ (1 + ε / d₁) +
      movingArcCost L (fun t => d₁ + t) (fun t => t - d₂)
        x₂ v₂ d₂ (1 - ε / d₂) := by
    funext ε
    exact fixedParameterCost_eq_movingArcCost L x₁ v₁ x₂ v₂ d₁ hd₂.ne' ε
  rw [hfun]
  convert h₁.add h₂ using 1
  · rfl
  · ring

/-- The exact cost derivative at an interior cut is the hat-weight identity
needed by the scalar weak du Bois–Reymond argument. -/
theorem hat_integral_eq_of_duration_exchange_min (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) {x v : ℝ → E}
    (hx : Continuous x) (hv : Continuous v) {T a : ℝ} (ha : a ∈ Ioo 0 T)
    (hmin : IsLocalMin (fixedParameterCost L x v (fun s => x (a + s))
      (fun s => v (a + s)) a (T - a)) 0) :
    (∫ t in a..T, energyCurve L x v t) / (T - a) -
      (∫ t in 0..a, energyCurve L x v t) / a +
      (∫ t in 0..a, t * timePartialCurve L x v t) / a +
      (∫ t in a..T, (T - t) * timePartialCurve L x v t) / (T - a) = 0 := by
  let f := energyCurve L x v
  let g := timePartialCurve L x v
  have hf : Continuous f := continuous_energyCurve L hL hx hv
  have hg : Continuous g := continuous_timePartialCurve L hL hx hv
  have hD := hasDerivAt_fixedParameterCost L hL hx hv
    (x₂ := fun s => x (a + s)) (v₂ := fun s => v (a + s))
    (hx.comp (continuous_const.add continuous_id))
    (hv.comp (continuous_const.add continuous_id)) ha.1 (sub_pos.mpr ha.2)
  have hz := hmin.hasDerivAt_eq_zero hD
  change (∫ t in 0..a, t * g t - f t) / a -
    (∫ t in 0..T - a, (t - (T - a)) * g (a + t) - f (a + t)) / (T - a) = 0 at hz
  have hleft : (∫ t in 0..a, t * g t - f t) =
      (∫ t in 0..a, t * g t) - (∫ t in 0..a, f t) :=
    intervalIntegral.integral_sub ((continuous_id.mul hg).intervalIntegrable 0 a)
      (hf.intervalIntegrable 0 a)
  have hright : (∫ t in 0..T - a, (t - (T - a)) * g (a + t) - f (a + t)) =
      -(∫ t in a..T, (T - t) * g t) - (∫ t in a..T, f t) := by
    calc
      (∫ t in 0..T - a, (t - (T - a)) * g (a + t) - f (a + t)) =
          ∫ t in 0..T - a, ((a + t) - T) * g (a + t) - f (a + t) := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = ∫ t in a..T, (t - T) * g t - f t := by
        simpa only [add_zero, add_sub_cancel] using
          (intervalIntegral.integral_comp_add_left (fun t => (t - T) * g t - f t)
            (a := 0) (b := T - a) a)
      _ = ∫ t in a..T, -((T - t) * g t) - f t := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        have hw : Continuous (fun t => (T - t) * g t) :=
          (continuous_const.sub continuous_id).mul hg
        simpa only [Pi.neg_apply, intervalIntegral.integral_neg] using
          (intervalIntegral.integral_sub (μ := volume) (hw.neg.intervalIntegrable a T)
            (hf.intervalIntegrable a T))
  rw [hleft, hright] at hz
  change (∫ t in a..T, f t) / (T - a) - (∫ t in 0..a, f t) / a +
    (∫ t in 0..a, t * g t) / a + (∫ t in a..T, (T - t) * g t) / (T - a) = 0
  convert hz using 1
  ring

/-- Every actual duration-exchange minimum yields both forms of the weak energy
law. This interface permits the ambient finite-piecewise construction to supply
its already-derived local minima. -/
theorem weak_duBoisReymond_of_all_duration_exchange_min (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) {x v : ℝ → E}
    (hx : Continuous x) (hv : Continuous v) {T : ℝ} (hT : 0 < T)
    (hmin : ∀ a ∈ Ioo 0 T, IsLocalMin
      (fixedParameterCost L x v (fun s => x (a + s)) (fun s => v (a + s)) a (T - a)) 0) :
    (∀ t ∈ Icc 0 T, energyCurve L x v t + (∫ s in 0..t, timePartialCurve L x v s) =
      energyCurve L x v 0) ∧
    (∀ t ∈ Ioo 0 T, HasDerivAt (energyCurve L x v) (-timePartialCurve L x v t) t) := by
  have he := continuous_energyCurve L hL hx hv
  have ht := continuous_timePartialCurve L hL hx hv
  have hhat := fun a ha => hat_integral_eq_of_duration_exchange_min L hL hx hv ha (hmin a ha)
  exact ⟨compensated_eq_of_hat_integral_eq he ht hT hhat,
    hasDerivAt_neg_of_hat_integral_eq he ht hT hhat⟩

/-- Nonautonomous weak du Bois–Reymond from the actual ambient functional minimum.
The feasible time competitors, their cost derivatives, and the weak energy law
are all derived. No energy or Euler–Lagrange equation is a hypothesis. -/
theorem weak_duBoisReymond_of_cvFunctional_min (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) {x v : ℝ → E}
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v) {T : ℝ} (hT : 0 < T)
    (hmin : IsMinOn (cvFunctional L K T)
      (fixedEndpointPiecewiseC1Curves T (x 0) (x T)) x) :
    (∀ t ∈ Icc 0 T, energyCurve L x v t + (∫ s in 0..t, timePartialCurve L x v s) =
      energyCurve L x v 0) ∧
    (∀ t ∈ Ioo 0 T, HasDerivAt (energyCurve L x v) (-timePartialCurve L x v t) t) := by
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t => (hx t).continuousAt
  apply weak_duBoisReymond_of_all_duration_exchange_min L hL hxc hv hT
  intro a ha
  have hsum : a + (T - a) = T := by ring
  apply fixedParameterCost_isLocalMin_of_cvFunctional_min L K hL.continuous hx hv
    (hasDerivAt_shifted hx a) (hv.comp (continuous_const.add continuous_id))
    ha.1 (sub_pos.mpr ha.2) (by simp)
  simpa only [hsum, concatenate_shifted] using hmin

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A shift of the physical clock preserves the actual time partial. -/
theorem timePartialCurve_shift (L : ℝ → E → E → ℝ) (a : ℝ) (x v : ℝ → E) (t : ℝ) :
    timePartialCurve (fun s => L (a + s)) x v t =
      deriv (fun s => L s (x t) (v t)) (a + t) :=
  deriv_comp_const_add (fun s => L s (x t) (v t)) a t

/-- Integrating the weak energy equation with an affine weight gives its exact
boundary terms. Only interior energy derivatives are needed. -/
theorem integral_weighted_energy_eq {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {d : ℝ} (hd : 0 ≤ d) (b : ℝ)
    (hD : ∀ t ∈ Ioo 0 d, HasDerivAt f (-g t) t) :
    (∫ t in 0..d, (t - b) * g t - f t) = -(d - b) * f d - b * f 0 := by
  have hder : ∀ t ∈ Ioo 0 d, HasDerivAt (fun s => -(s - b) * f s)
      ((t - b) * g t - f t) t := by
    intro t ht
    have h := (((hasDerivAt_id t).sub_const b).neg).mul (hD t ht)
    convert h using 1
    · rfl
    · simp only [Pi.neg_apply, id_eq]
      ring
  have hcont : Continuous (fun s => -(s - b) * f s) :=
    (continuous_id.sub continuous_const).neg.mul hf
  have hdc : Continuous (fun t => (t - b) * g t - f t) :=
    ((continuous_id.sub continuous_const).mul hg).sub hf
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hd hcont.continuousOn
    hder (hdc.intervalIntegrable 0 d)
  convert h using 1
  ring

/-- The genuine duration-exchange minimum matches the two corner energies once
the weak interior equations have been derived on the two arcs. The finite
ambient wrapper derives these equations from its actual subarc minima. -/
theorem corner_energy_eq_of_weak_dbr_min (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : Continuous x₁) (hv₁ : Continuous v₁)
    (hx₂ : Continuous x₂) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hE₁ : ∀ t ∈ Ioo 0 d₁,
      HasDerivAt (energyCurve L x₁ v₁) (-timePartialCurve L x₁ v₁ t) t)
    (hE₂ : ∀ t ∈ Ioo 0 d₂,
      HasDerivAt (energyCurve (fun s => L (d₁ + s)) x₂ v₂)
        (-timePartialCurve (fun s => L (d₁ + s)) x₂ v₂ t) t)
    (hmin : IsLocalMin (fixedParameterCost L x₁ v₁ x₂ v₂ d₁ d₂) 0) :
    energyCurve L x₁ v₁ d₁ = energyCurve (fun s => L (d₁ + s)) x₂ v₂ 0 := by
  let L₂ : ℝ → E → E → ℝ := fun s => L (d₁ + s)
  have hL₂ : ContDiff ℝ 1 (uncurryLagrangian L₂) := by
    exact hL.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)
  have hl := integral_weighted_energy_eq (continuous_energyCurve L hL hx₁ hv₁)
    (continuous_timePartialCurve L hL hx₁ hv₁) hd₁.le 0 hE₁
  have hr := integral_weighted_energy_eq (continuous_energyCurve L₂ hL₂ hx₂ hv₂)
    (continuous_timePartialCurve L₂ hL₂ hx₂ hv₂) hd₂.le d₂ hE₂
  have hleft : (∫ t in 0..d₁,
      t * timePartialCurve L x₁ v₁ t - energyCurve L x₁ v₁ t) / d₁ =
      -energyCurve L x₁ v₁ d₁ := by
    simp only [sub_zero, zero_mul, sub_zero] at hl
    rw [hl]
    field_simp
  have hright : (∫ t in 0..d₂,
      (t - d₂) * timePartialCurve L₂ x₂ v₂ t - energyCurve L₂ x₂ v₂ t) / d₂ =
      -energyCurve L₂ x₂ v₂ 0 := by
    rw [hr]
    simp only [sub_self, neg_zero, zero_mul, zero_sub]
    field_simp
  have hz := hmin.hasDerivAt_eq_zero
    (hasDerivAt_fixedParameterCost L hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂)
  simp_rw [← timePartialCurve_shift L d₁ x₂ v₂] at hz
  change (∫ t in 0..d₁,
      t * timePartialCurve L x₁ v₁ t - energyCurve L x₁ v₁ t) / d₁ -
    (∫ t in 0..d₂,
      (t - d₂) * timePartialCurve L₂ x₂ v₂ t - energyCurve L₂ x₂ v₂ t) / d₂ = 0 at hz
  rw [hleft, hright] at hz
  linarith

end KirkMedhin.NonautonomousDuBoisReymond

#print axioms KirkMedhin.NonautonomousDuBoisReymond.weak_duBoisReymond_of_cvFunctional_min
#print axioms KirkMedhin.NonautonomousDuBoisReymond.corner_energy_eq_of_weak_dbr_min
