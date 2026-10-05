/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.K3IsoperimetricEulerLagrange
import DynamicalSystems.OptimalControl.ContinuousTime.TimeReparametrizationFamily

/-!
# Actual costs of nonautonomous duration-exchange competitors

The existing concatenation and duration-exchange curves are reused. Their actual
time-dependent `cvFunctional` is identified with integrals over the fixed reference
intervals, retaining both the rescaled time and the shifted origin of the right arc.
-/

open MeasureTheory Set Filter
open scoped Topology Interval
open TimeReparametrization

namespace NonautonomousTimeReparametrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Split the actual nonautonomous cost at the concatenation corner. The right
arc's Lagrangian is evaluated at physical time `s + t`. -/
theorem cvFunctional_concatenate (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (hL : Continuous (uncurryLagrangian L))
    {s T : ℝ} (hs : 0 < s) (hT : s < T) {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂) :
    cvFunctional L K T (concatenate s x₁ x₂) =
      (∫ t in 0..s, L t (x₁ t) (deriv x₁ t)) +
      (∫ t in 0..T - s, L (s + t) (x₂ t) (deriv x₂ t)) + K (x₂ (T - s)) := by
  let F : ℝ → ℝ := fun t ↦ L t (concatenate s x₁ x₂ t)
    (deriv (concatenate s x₁ x₂) t)
  let F₁ : ℝ → ℝ := fun t ↦ L t (x₁ t) (v₁ t)
  let F₂ : ℝ → ℝ := fun t ↦ L t (x₂ (t - s)) (v₂ (t - s))
  have hxc₁ : Continuous x₁ := continuous_iff_continuousAt.mpr fun t ↦ (hx₁ t).continuousAt
  have hxc₂ : Continuous x₂ := continuous_iff_continuousAt.mpr fun t ↦ (hx₂ t).continuousAt
  have hFc₁ : Continuous F₁ := hL.comp (continuous_id.prodMk (hxc₁.prodMk hv₁))
  have hFc₂ : Continuous F₂ := hL.comp (continuous_id.prodMk
    ((hxc₂.comp (continuous_id.sub continuous_const)).prodMk
      (hv₂.comp (continuous_id.sub continuous_const))))
  have hEq₁ : EqOn F F₁ (Ioo 0 s) := by
    intro t ht
    change L t (concatenate s x₁ x₂ t) (deriv (concatenate s x₁ x₂) t) = _
    rw [(hasDerivAt_concatenate_left hx₁ ht.2).deriv]
    simp only [concatenate, show (t ≤ s) = True from eq_true ht.2.le, ite_true]
    rfl
  have hEq₂ : EqOn F F₂ (Ioo s T) := by
    intro t ht
    change L t (concatenate s x₁ x₂ t) (deriv (concatenate s x₁ x₂) t) = _
    rw [(hasDerivAt_concatenate_right hx₂ ht.1).deriv]
    simp only [concatenate, show (t ≤ s) = False from eq_false (not_le_of_gt ht.1),
      ite_false]
    rfl
  have hi₁ : IntervalIntegrable F volume 0 s :=
    (hFc₁.intervalIntegrable 0 s).congr_uIoo (by simpa only [uIoo_of_le hs.le] using hEq₁.symm)
  have hi₂ : IntervalIntegrable F volume s T :=
    (hFc₂.intervalIntegrable s T).congr_uIoo (by simpa only [uIoo_of_le hT.le] using hEq₂.symm)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  have he₁ := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hs.le hEq₁
  have he₂ := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hT.le hEq₂
  have hshift := intervalIntegral.integral_comp_sub_right
    (fun t ↦ L (s + t) (x₂ t) (v₂ t)) (a := s) (b := T) s
  have hdx₁ : ∀ t, deriv x₁ t = v₁ t := fun t ↦ (hx₁ t).deriv
  have hdx₂ : ∀ t, deriv x₂ t = v₂ t := fun t ↦ (hx₂ t).deriv
  simp_rw [hdx₁, hdx₂]
  change (∫ t in 0..T, F t) + K (concatenate s x₁ x₂ T) = _
  rw [← hsplit, he₁, he₂]
  simp only [concatenate, show (T ≤ s) = False from eq_false (not_le_of_gt hT), ite_false]
  have hr : (∫ t in s..T, F₂ t) = ∫ t in 0..T - s, L (s + t) (x₂ t) (v₂ t) := by
    simpa only [F₂, ← add_sub_assoc, add_sub_cancel_left, sub_self] using hshift
  rw [hr]

/-- The two actual arc costs expressed on their fixed original parameter intervals. -/
noncomputable def fixedParameterCost (L : ℝ → E → E → ℝ)
    (x₁ v₁ x₂ v₂ : ℝ → E) (d₁ d₂ ε : ℝ) : ℝ :=
  (∫ t in 0..d₁, (1 + ε / d₁) *
    L ((1 + ε / d₁) * t) (x₁ t) ((1 + ε / d₁)⁻¹ • v₁ t)) +
  (∫ t in 0..d₂, (1 - ε / d₂) *
    L (d₁ + ε + (1 - ε / d₂) * t) (x₂ t) ((1 - ε / d₂)⁻¹ • v₂ t))

/-- A change of variables retains the physical time argument of a rescaled arc. -/
theorem fixedParameterArcCost_eq_actual (L : ℝ → E → E → ℝ)
    {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t)
    (s d : ℝ) {r : ℝ} (hr : r ≠ 0) :
    (∫ t in 0..d, r * L (s + r * t) (x t) (r⁻¹ • v t)) =
      ∫ t in 0..r * d, L (s + t) (x (t / r))
        (deriv (fun q : ℝ ↦ x (q / r)) t) := by
  have hd : ∀ t, deriv (fun q : ℝ ↦ x (q / r)) t = r⁻¹ • v (t / r) :=
    fun t ↦ (hasDerivAt_rescaledArc hx r t).deriv
  simp_rw [hd]
  rw [intervalIntegral.integral_const_mul]
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ ↦ L (s + t) (x (t / r)) (r⁻¹ • v (t / r)))
    (a := 0) (b := d) r
  simpa only [mul_div_cancel_left₀ _ hr, mul_zero, smul_eq_mul] using hsub

/-- Exact ambient cost of the actual duration-exchange competitor, including its
fixed terminal penalty, expressed on the original reference intervals. -/
theorem cvFunctional_durationExchange (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (hL : Continuous (uncurryLagrangian L)) {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ ε : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hε : ε ∈ Ioo (-d₁) d₂) :
    cvFunctional L K (d₁ + d₂) (durationExchange x₁ x₂ d₁ d₂ ε) =
      fixedParameterCost L x₁ v₁ x₂ v₂ d₁ d₂ ε + K (x₂ d₂) := by
  have hs : 0 < d₁ + ε := by linarith [hε.1]
  have hT : d₁ + ε < d₁ + d₂ := by linarith [hε.2]
  have hv₁r : Continuous (fun t ↦ (1 + ε / d₁)⁻¹ • v₁ (t / (1 + ε / d₁))) :=
    continuous_const.smul (hv₁.comp (continuous_id.div_const _))
  have hv₂r : Continuous (fun t ↦ (1 - ε / d₂)⁻¹ • v₂ (t / (1 - ε / d₂))) :=
    continuous_const.smul (hv₂.comp (continuous_id.div_const _))
  have h := cvFunctional_concatenate L K hL hs hT
    (hasDerivAt_rescaledArc hx₁ (1 + ε / d₁)) hv₁r
    (hasDerivAt_rescaledArc hx₂ (1 - ε / d₂)) hv₂r
  have hdurs := exchanged_durations (ne_of_gt hd₁) (ne_of_gt hd₂) ε
  have heq : d₁ + d₂ - (d₁ + ε) = (1 - ε / d₂) * d₂ := by linarith [hdurs.2.1]
  have hrs := rescaling_factors_pos hd₁ hd₂ hε
  change cvFunctional L K (d₁ + d₂)
    (concatenate (d₁ + ε) (fun t ↦ x₁ (t / (1 + ε / d₁)))
      (fun t ↦ x₂ (t / (1 - ε / d₂)))) = _
  rw [h, heq]
  simp only [mul_div_cancel_left₀ d₂ (ne_of_gt hrs.2)]
  have ha := fixedParameterArcCost_eq_actual L hx₁ 0 d₁ (ne_of_gt hrs.1)
  have hb := fixedParameterArcCost_eq_actual L hx₂ (d₁ + ε) d₂ (ne_of_gt hrs.2)
  simp only [zero_add] at ha
  rw [hdurs.1] at ha
  rw [← ha, ← hb]
  rfl

/-- Ambient optimality implies a local minimum of the genuine fixed-parameter cost
when the actual duration-exchange curves belong to the chosen feasible set. -/
theorem fixedParameterCost_isLocalMin_of_ambient_min (L : ℝ → E → E → ℝ)
    (K : E → ℝ) (hL : Continuous (uncurryLagrangian L))
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (feasible : Set (ℝ → E))
    (hfeasible : ∀ ε ∈ Ioo (-d₁) d₂, durationExchange x₁ x₂ d₁ d₂ ε ∈ feasible)
    (hmin : IsMinOn (cvFunctional L K (d₁ + d₂)) feasible (concatenate d₁ x₁ x₂)) :
    IsLocalMin (fixedParameterCost L x₁ v₁ x₂ v₂ d₁ d₂) 0 := by
  filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hd₁) hd₂] with ε hε
  have hzero : (0 : ℝ) ∈ Ioo (-d₁) d₂ := ⟨neg_neg_of_pos hd₁, hd₂⟩
  have hn := cvFunctional_durationExchange L K hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hzero
  rw [durationExchange_zero] at hn
  apply (add_le_add_iff_right (K (x₂ d₂))).mp
  rw [← hn, ← cvFunctional_durationExchange L K hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hε]
  exact hmin (hfeasible ε hε)

/-- Actual fixed-endpoint piecewise-C1 optimality supplies the feasible family
automatically; no scalar minimum or cost identity is assumed. -/
theorem fixedParameterCost_isLocalMin_of_cvFunctional_min (L : ℝ → E → E → ℝ)
    (K : E → ℝ) (hL : Continuous (uncurryLagrangian L))
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hjoin : x₁ d₁ = x₂ 0)
    (hmin : IsMinOn (cvFunctional L K (d₁ + d₂))
      (fixedEndpointPiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂))
      (concatenate d₁ x₁ x₂)) :
    IsLocalMin (fixedParameterCost L x₁ v₁ x₂ v₂ d₁ d₂) 0 := by
  exact fixedParameterCost_isLocalMin_of_ambient_min L K hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ _
    (fun ε hε ↦ durationExchange_mem_fixedEndpointPiecewiseC1Curves
      hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hjoin hε) hmin

end NonautonomousTimeReparametrization
