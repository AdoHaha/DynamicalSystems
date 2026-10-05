/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.TimeReparametrizationFamily

/-!
# Weak autonomous du Bois–Reymond from actual inner time variations

Every interior cut of a continuously differentiable arc gives an actual
duration-exchange competitor. Its cost derivative equates the average energies
on the two sides. The fundamental theorem of calculus then makes the energy
constant, without differentiating the velocity or assuming Euler–Lagrange.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace KirkMedhin.DuBoisReymond

open KirkMedhin.TimeReparametrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous states and velocities give continuous energy for a C1 Lagrangian. -/
theorem continuous_energyCurve (L : E → E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x v : ℝ → E} (hx : Continuous x) (hv : Continuous v) :
    Continuous (energyCurve L x v) := by
  have hD : Continuous (fun t => (fderiv ℝ L.uncurry (x t, v t)) (0, v t)) :=
    ((hL.continuous_fderiv one_ne_zero).comp (hx.prodMk hv)).clm_apply
      ((continuous_const : Continuous (fun _ : ℝ => (0 : E))).prodMk hv)
  have heq : energyCurve L x v = fun t =>
      (fderiv ℝ L.uncurry (x t, v t)) (0, v t) - L (x t) (v t) := by
    funext t
    exact congrArg (fun z => z - L (x t) (v t))
      (velocity_fderiv_apply L (x t) (v t) (v t) (hL.differentiable one_ne_zero _))
  rw [heq]
  exact hD.sub (hL.continuous.comp (hx.prodMk hv))

/-- Translate the parameter of an actual differentiable arc. -/
theorem hasDerivAt_shifted {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t)
    (a t : ℝ) : HasDerivAt (fun s => x (a + s)) (v (a + t)) t := by
  simpa only [Function.comp_def, zero_add, one_smul] using
    (hx (a + t)).scomp t ((hasDerivAt_const t a).add (hasDerivAt_id t))

/-- Stationarity of the actual duration exchange at an interior cut equates the
two average energies. The derivative comes from the genuine curve costs. -/
theorem average_energy_eq_of_duration_exchange_min
    (L : E → E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v)
    {T a : ℝ} (ha : a ∈ Ioo 0 T)
    (hmin : IsLocalMin (actualCornerCost L x (fun s => x (a + s)) a (T - a)) 0) :
    (∫ t in a..T, energyCurve L x v t) / (T - a) =
      (∫ t in 0..a, energyCurve L x v t) / a := by
  have hD := hasDerivAt_actualCornerCost L hL hx hv
    (hasDerivAt_shifted hx a) (hv.comp (continuous_const.add continuous_id))
    ha.1.le (sub_nonneg.mpr ha.2.le)
  have hz := hmin.hasDerivAt_eq_zero hD
  have hshift : (∫ t in 0..T - a,
      energyCurve L (fun s => x (a + s)) (fun s => v (a + s)) t) =
      ∫ t in a..T, energyCurve L x v t := by
    simpa only [energyCurve, add_zero, add_sub_cancel] using
      (intervalIntegral.integral_comp_add_left (energyCurve L x v)
        (a := 0) (b := T - a) a)
  rw [hshift] at hz
  exact sub_eq_zero.mp hz

/-- A continuous scalar function whose averages agree across every interior cut
is constant, including at both endpoints. -/
theorem eq_of_average_integral_eq {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ}
    (hT : 0 < T)
    (haverage : ∀ a ∈ Ioo 0 T,
      (∫ t in a..T, f t) / (T - a) = (∫ t in 0..a, f t) / a) :
    ∀ t ∈ Icc 0 T, f t = f 0 := by
  let c := (∫ t in 0..T, f t) / T
  have hprimitive : ∀ a ∈ Ioo 0 T, (∫ t in 0..a, f t) = a * c := by
    intro a ha
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a T)
    have hcross := (div_eq_div_iff (sub_ne_zero.mpr (ne_of_gt ha.2))
      (ne_of_gt ha.1)).mp (haverage a ha)
    dsimp [c]
    rw [← mul_div_assoc]
    apply (eq_div_iff (ne_of_gt hT)).mpr
    rw [← hsplit]
    nlinarith
  have hinterior : EqOn f (fun _ => c) (Ioo 0 T) := by
    intro a ha
    have hF := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 a)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
    have hlinear : HasDerivAt (fun t : ℝ => t * c) c a := by
      simpa using (hasDerivAt_id a).mul_const c
    apply hF.unique
    apply hlinear.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ha.1 ha.2] with b hb
    exact hprimitive b hb
  have hclosed : EqOn f (fun _ => c) (Icc 0 T) := by
    simpa only [closure_Ioo hT.ne] using hinterior.closure hf continuous_const
  intro t ht
  exact (hclosed ht).trans (hclosed ⟨le_rfl, hT.le⟩).symm

/-- The scalar weak du Bois–Reymond implication for time-dependent Lagrangians.
The identity tested here is the derivative of an actual two-piece affine time
variation: `f` is the energy and `g` is the partial time derivative of the
Lagrangian. Continuous data suffice to make the compensated energy constant. -/
theorem compensated_eq_of_hat_integral_eq {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {T : ℝ} (hT : 0 < T)
    (hhat : ∀ a ∈ Ioo 0 T,
      (∫ t in a..T, f t) / (T - a) - (∫ t in 0..a, f t) / a +
        (∫ t in 0..a, t * g t) / a +
        (∫ t in a..T, (T - t) * g t) / (T - a) = 0) :
    ∀ t ∈ Icc 0 T, f t + (∫ s in 0..t, g s) = f 0 := by
  let Q : ℝ → ℝ := fun a => ∫ t in 0..a, g t
  let R : ℝ → ℝ := fun a => ∫ t in 0..a, t * g t
  let c := ((∫ t in 0..T, f t) + T * Q T - R T) / T
  have htgc : Continuous (fun t => t * g t) := continuous_id.mul hg
  have hQ (a : ℝ) : HasDerivAt Q (g a) a :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 a)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hR (a : ℝ) : HasDerivAt R (a * g a) a :=
    intervalIntegral.integral_hasDerivAt_right (htgc.intervalIntegrable 0 a)
      htgc.aestronglyMeasurable.stronglyMeasurableAtFilter htgc.continuousAt
  have hprimitive : ∀ a ∈ Ioo 0 T,
      (∫ t in 0..a, f t) = a * c + R a - a * Q a := by
    intro a ha
    have htail (k : ℝ → ℝ) (hk : Continuous k) :
        (∫ t in a..T, k t) = (∫ t in 0..T, k t) - (∫ t in 0..a, k t) := by
      have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hk.intervalIntegrable 0 a) (hk.intervalIntegrable a T)
      linarith
    have hweighted : (∫ t in a..T, (T - t) * g t) =
        T * (Q T - Q a) - (R T - R a) := by
      have hTgc : Continuous (fun t => T * g t) := continuous_const.mul hg
      calc
        (∫ t in a..T, (T - t) * g t) = ∫ t in a..T, T * g t - t * g t := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
        _ = T * (∫ t in a..T, g t) - (∫ t in a..T, t * g t) := by
          rw [intervalIntegral.integral_sub (hTgc.intervalIntegrable a T)
            (htgc.intervalIntegrable a T), intervalIntegral.integral_const_mul]
        _ = _ := by rw [htail g hg, htail _ htgc]
    have hh := hhat a ha
    rw [hweighted, htail f hf] at hh
    change ((∫ t in 0..T, f t) - (∫ t in 0..a, f t)) / (T - a) -
      (∫ t in 0..a, f t) / a + R a / a +
      (T * (Q T - Q a) - (R T - R a)) / (T - a) = 0 at hh
    field_simp [ne_of_gt ha.1, sub_ne_zero.mpr (ne_of_gt ha.2)] at hh
    have hc : T * c = (∫ t in 0..T, f t) + T * Q T - R T := by
      dsimp [c]
      field_simp
    have hmul := congrArg (fun z : ℝ => a * z) hc
    apply (mul_right_inj' (ne_of_gt hT)).mp
    nlinarith only [hh, hmul]
  have hinterior : EqOn (fun t => f t + Q t) (fun _ => c) (Ioo 0 T) := by
    intro a ha
    have hF := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 a)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
    have hmodel := (((hasDerivAt_id a).mul_const c).add (hR a)).sub
      ((hasDerivAt_id a).mul (hQ a))
    simp only [one_mul, id_eq] at hmodel
    have heq : f a = c + a * g a - (Q a + a * g a) := by
      apply hF.unique
      apply hmodel.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds ha.1 ha.2] with b hb
      exact hprimitive b hb
    linarith
  have hQc : Continuous Q := continuous_iff_continuousAt.mpr fun t => (hQ t).continuousAt
  have hclosed : EqOn (fun t => f t + Q t) (fun _ => c) (Icc 0 T) := by
    simpa only [closure_Ioo hT.ne] using hinterior.closure (hf.add hQc) continuous_const
  intro t ht
  have hzero : f 0 = c := by
    simpa only [Q, intervalIntegral.integral_same, add_zero]
      using (hclosed ⟨le_rfl, hT.le⟩)
  exact (hclosed ht).trans hzero.symm

/-- The weak hat-integral identity gives the actual interior derivative of
energy; its differentiability is a conclusion, not a regularity assumption. -/
theorem hasDerivAt_neg_of_hat_integral_eq {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {T : ℝ} (hT : 0 < T)
    (hhat : ∀ a ∈ Ioo 0 T,
      (∫ t in a..T, f t) / (T - a) - (∫ t in 0..a, f t) / a +
        (∫ t in 0..a, t * g t) / a +
        (∫ t in a..T, (T - t) * g t) / (T - a) = 0) :
    ∀ t ∈ Ioo 0 T, HasDerivAt f (-g t) t := by
  intro t ht
  have he := compensated_eq_of_hat_integral_eq hf hg hT hhat
  have hQ := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  apply hQ.const_sub (f 0) |>.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  have h := he s ⟨hs.1.le, hs.2.le⟩
  linarith

/-- Weak autonomous du Bois–Reymond using actual duration exchanges at every cut.
The conclusion needs only a continuous velocity, with no velocity derivative. -/
theorem energy_eq_of_all_duration_exchange_min
    (L : E → E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v)
    {T : ℝ} (hT : 0 < T)
    (hmin : ∀ a ∈ Ioo 0 T,
      IsLocalMin (actualCornerCost L x (fun s => x (a + s)) a (T - a)) 0) :
    ∀ t ∈ Icc 0 T, energyCurve L x v t = energyCurve L x v 0 := by
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t => (hx t).continuousAt
  exact eq_of_average_integral_eq (continuous_energyCurve L hL hxc hv) hT
    (fun a ha => average_energy_eq_of_duration_exchange_min L hL hx hv ha (hmin a ha))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Splitting and translating a single reference arc preserves its actual curve. -/
theorem concatenate_shifted (x : ℝ → E) (a : ℝ) :
    concatenate a x (fun s => x (a + s)) = x := by
  funext t
  unfold concatenate
  split_ifs
  · rfl
  · exact congrArg x (by ring)

/-- An actual ambient fixed-endpoint minimum yields the weak autonomous
du Bois–Reymond condition. Every tested time variation is constructed and proved
to belong to the ambient piecewise-C1 curve class. Neither Euler–Lagrange nor
differentiability of the velocity is assumed. -/
theorem energy_eq_of_cvFunctional_min
    (L : E → E → ℝ) (K : E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v)
    {T : ℝ} (hT : 0 < T)
    (hmin : IsMinOn (cvFunctional (fun _ => L) K T)
      (fixedEndpointPiecewiseC1Curves T (x 0) (x T)) x) :
    ∀ t ∈ Icc 0 T, energyCurve L x v t = energyCurve L x v 0 := by
  apply energy_eq_of_all_duration_exchange_min L hL hx hv hT
  intro a ha
  have hd : 0 < T - a := sub_pos.mpr ha.2
  have hsum : a + (T - a) = T := by ring
  have hvshift : Continuous (fun s => v (a + s)) :=
    hv.comp (continuous_const.add continuous_id)
  have hjoin : x a = (fun s => x (a + s)) 0 := by simp
  apply actualCornerCost_isLocalMin_of_ambient_min L K hL.continuous hx hv
    (hasDerivAt_shifted hx a) hvshift ha.1 hd
    (fixedEndpointPiecewiseC1Curves (a + (T - a)) (x 0) (x (a + (T - a))))
  · intro ε hε
    exact durationExchange_mem_fixedEndpointPiecewiseC1Curves
      hx hv (hasDerivAt_shifted hx a) hvshift ha.1 hd hjoin hε
  · simpa only [hsum, concatenate_shifted] using hmin

end KirkMedhin.DuBoisReymond

#print axioms KirkMedhin.DuBoisReymond.energy_eq_of_all_duration_exchange_min
#print axioms KirkMedhin.DuBoisReymond.energy_eq_of_cvFunctional_min
#print axioms KirkMedhin.DuBoisReymond.compensated_eq_of_hat_integral_eq
#print axioms KirkMedhin.DuBoisReymond.hasDerivAt_neg_of_hat_integral_eq
