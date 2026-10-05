import DynamicalSystems.OptimalControl.ContinuousTime.TimeReparametrization
import Mathlib.Topology.Piecewise

/-!
# Concatenated time-rescaling competitors for the two-arc corner condition

This module represents the duration-exchange variations as actual continuous,
piecewise C1 curves. It identifies their `cvFunctional` with the actual sum of
arc costs and transports ambient-family optimality to the scalar local minimum.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace TimeReparametrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Join a left arc to a translated right arc at the specified switch time. -/
noncomputable def concatenate (s : ℝ) (x₁ x₂ : ℝ → E) (t : ℝ) : E :=
  if t ≤ s then x₁ t else x₂ (t - s)

theorem hasDerivAt_concatenate_left {s t : ℝ} {x₁ v₁ x₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (ht : t < s) :
    HasDerivAt (concatenate s x₁ x₂) (v₁ t) t := by
  apply (hx₁ t).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht] with q hq
  have hqs : q < s := hq
  simp [concatenate, hqs.le]

theorem hasDerivAt_concatenate_right {s t : ℝ} {x₁ x₂ v₂ : ℝ → E}
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (ht : s < t) :
    HasDerivAt (concatenate s x₁ x₂) (v₂ (t - s)) t := by
  have h : HasDerivAt (fun q : ℝ ↦ x₂ (q - s)) (v₂ (t - s)) t := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (hx₂ (t - s)).scomp t ((hasDerivAt_id t).sub_const s)
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with q hq
  have hqs : s < q := hq
  simp [concatenate, not_le_of_gt hqs]

omit [NormedSpace ℝ E] in
theorem concatenate_continuous {s : ℝ} {x₁ x₂ : ℝ → E}
    (hx₁ : Continuous x₁) (hx₂ : Continuous x₂) (hjoin : x₁ s = x₂ 0) :
    Continuous (concatenate s x₁ x₂) := by
  change Continuous ((Iic s).piecewise x₁ (fun t ↦ x₂ (t - s)))
  apply Continuous.piecewise _ hx₁ (hx₂.comp (continuous_id.sub continuous_const))
  intro t ht
  have heq : t = s := by simpa only [frontier_Iic, mem_singleton_iff] using ht
  subst t
  simpa using hjoin

/-- The concatenated curve satisfies the project's actual piecewise-C1 predicate. -/
theorem concatenate_isPiecewiseC1 {s T : ℝ} (hs : 0 < s) (hT : s < T)
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t)
    (hjoin : x₁ s = x₂ 0) :
    IsPiecewiseC₁On (concatenate s x₁ x₂) v₁ (fun t ↦ v₂ (t - s)) T s := by
  have hxc₁ : Continuous x₁ := continuous_iff_continuousAt.mpr fun t ↦ (hx₁ t).continuousAt
  have hxc₂ : Continuous x₂ := continuous_iff_continuousAt.mpr fun t ↦ (hx₂ t).continuousAt
  refine ⟨hs, hT, (concatenate_continuous hxc₁ hxc₂ hjoin).continuousOn, ?_, ?_⟩
  · intro t ht
    apply (hx₁ t).hasDerivWithinAt.congr_of_mem (s := Iic s) _ ht.2
    intro q hq
    have hqs : q ≤ s := hq
    simp [concatenate, hqs]
  · intro t ht
    have h : HasDerivAt (fun q : ℝ ↦ x₂ (q - s)) (v₂ (t - s)) t := by
      simpa only [Function.comp_def, id_eq, one_smul] using
        (hx₂ (t - s)).scomp t ((hasDerivAt_id t).sub_const s)
    apply h.hasDerivWithinAt.congr_of_mem (s := Ici s) _ ht.1
    intro q hq
    by_cases hqs : q ≤ s
    · have heq : q = s := le_antisymm hqs hq
      subst q
      simpa [concatenate] using hjoin
    · simp [concatenate, hqs]

/-- Split the genuine `cvFunctional` of the concatenated curve. The single corner
can change the classical derivative at that point, which has no effect on the integral. -/
theorem cvFunctional_concatenate (L : E → E → ℝ) (K : E → ℝ)
    (hL : Continuous L.uncurry) {s T : ℝ} (hs : 0 < s) (hT : s < T)
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂) :
    cvFunctional (fun _ ↦ L) K T (concatenate s x₁ x₂) =
      (∫ t in 0..s, L (x₁ t) (deriv x₁ t)) +
      (∫ t in 0..T - s, L (x₂ t) (deriv x₂ t)) + K (x₂ (T - s)) := by
  let F : ℝ → ℝ := fun t ↦ L (concatenate s x₁ x₂ t) (deriv (concatenate s x₁ x₂) t)
  let F₁ : ℝ → ℝ := fun t ↦ L (x₁ t) (v₁ t)
  let F₂ : ℝ → ℝ := fun t ↦ L (x₂ (t - s)) (v₂ (t - s))
  have hxc₁ : Continuous x₁ := continuous_iff_continuousAt.mpr fun t ↦ (hx₁ t).continuousAt
  have hxc₂ : Continuous x₂ := continuous_iff_continuousAt.mpr fun t ↦ (hx₂ t).continuousAt
  have hFc₁ : Continuous F₁ := hL.comp (hxc₁.prodMk hv₁)
  have hFc₂ : Continuous F₂ :=
    (hL.comp (hxc₂.prodMk hv₂)).comp (continuous_id.sub continuous_const)
  have hEq₁ : EqOn F F₁ (Ioo 0 s) := by
    intro t ht
    change L (concatenate s x₁ x₂ t) (deriv (concatenate s x₁ x₂) t) = _
    rw [(hasDerivAt_concatenate_left hx₁ ht.2).deriv]
    simp only [concatenate, show (t ≤ s) = True from eq_true ht.2.le, ite_true]
    rfl
  have hEq₂ : EqOn F F₂ (Ioo s T) := by
    intro t ht
    change L (concatenate s x₁ x₂ t) (deriv (concatenate s x₁ x₂) t) = _
    rw [(hasDerivAt_concatenate_right hx₂ ht.1).deriv]
    simp only [concatenate, show (t ≤ s) = False from eq_false (not_le_of_gt ht.1), ite_false]
    rfl
  have hi₁ : IntervalIntegrable F volume 0 s :=
    (hFc₁.intervalIntegrable 0 s).congr_uIoo (by simpa only [uIoo_of_le hs.le] using hEq₁.symm)
  have hi₂ : IntervalIntegrable F volume s T :=
    (hFc₂.intervalIntegrable s T).congr_uIoo (by simpa only [uIoo_of_le hT.le] using hEq₂.symm)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  have he₁ := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hs.le hEq₁
  have he₂ := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hT.le hEq₂
  have hshift := intervalIntegral.integral_comp_sub_right
    (fun t ↦ L (x₂ t) (v₂ t)) (a := s) (b := T) s
  have hdx₁ : ∀ t, deriv x₁ t = v₁ t := fun t ↦ (hx₁ t).deriv
  have hdx₂ : ∀ t, deriv x₂ t = v₂ t := fun t ↦ (hx₂ t).deriv
  simp_rw [hdx₁, hdx₂]
  change (∫ t in 0..T, F t) + K (concatenate s x₁ x₂ T) = _
  rw [← hsplit, he₁, he₂]
  simp only [concatenate, show (T ≤ s) = False from eq_false (not_le_of_gt hT), ite_false]
  have hr : (∫ t in s..T, F₂ t) = ∫ t in 0..T - s, L (x₂ t) (v₂ t) := by
    simpa only [sub_self] using hshift
  rw [hr]

/-- Rescale two arcs while shifting their join and preserving total duration. -/
noncomputable def durationExchange (x₁ x₂ : ℝ → E) (d₁ d₂ ε : ℝ) : ℝ → E :=
  concatenate (d₁ + ε) (fun t ↦ x₁ (t / (1 + ε / d₁)))
    (fun t ↦ x₂ (t / (1 - ε / d₂)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem durationExchange_zero (x₁ x₂ : ℝ → E) (d₁ d₂ : ℝ) :
    durationExchange x₁ x₂ d₁ d₂ 0 = concatenate d₁ x₁ x₂ := by
  funext t
  simp [durationExchange, concatenate]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem durationExchange_endpoints (x₁ x₂ : ℝ → E) {d₁ d₂ ε : ℝ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hε : ε ∈ Ioo (-d₁) d₂) :
    durationExchange x₁ x₂ d₁ d₂ ε 0 = x₁ 0 ∧
    durationExchange x₁ x₂ d₁ d₂ ε (d₁ + d₂) = x₂ d₂ := by
  have hs : 0 < d₁ + ε := by linarith [hε.1]
  have hT : d₁ + ε < d₁ + d₂ := by linarith [hε.2]
  have hdurs := exchanged_durations (ne_of_gt hd₁) (ne_of_gt hd₂) ε
  have hr₂ := (rescaling_factors_pos hd₁ hd₂ hε).2
  constructor
  · simp [durationExchange, concatenate, hs.le]
  · have heq : d₁ + d₂ - (d₁ + ε) = (1 - ε / d₂) * d₂ := by linarith [hdurs.2.1]
    simp [durationExchange, concatenate, not_le_of_gt hT, heq,
      mul_div_cancel_left₀ d₂ (ne_of_gt hr₂)]

theorem durationExchange_isPiecewiseC1 {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t)
    {d₁ d₂ ε : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hε : ε ∈ Ioo (-d₁) d₂)
    (hjoin : x₁ d₁ = x₂ 0) :
    IsPiecewiseC₁On (durationExchange x₁ x₂ d₁ d₂ ε)
      (fun t ↦ (1 + ε / d₁)⁻¹ • v₁ (t / (1 + ε / d₁)))
      (fun t ↦ (1 - ε / d₂)⁻¹ • v₂ ((t - (d₁ + ε)) / (1 - ε / d₂)))
      (d₁ + d₂) (d₁ + ε) := by
  have hs : 0 < d₁ + ε := by linarith [hε.1]
  have hT : d₁ + ε < d₁ + d₂ := by linarith [hε.2]
  apply concatenate_isPiecewiseC1 hs hT (hasDerivAt_rescaledArc hx₁ (1 + ε / d₁))
    (hasDerivAt_rescaledArc hx₂ (1 - ε / d₂))
  have hdurs := exchanged_durations (ne_of_gt hd₁) (ne_of_gt hd₂) ε
  have hr₁ := (rescaling_factors_pos hd₁ hd₂ hε).1
  rw [← hdurs.1]
  simpa only [mul_div_cancel_left₀ d₁ (ne_of_gt hr₁), zero_div] using hjoin

/-- Exact equality between the ambient cost of the concatenated competitor and the
actual duration-exchange cost, including its fixed terminal penalty. -/
theorem cvFunctional_durationExchange (L : E → E → ℝ) (K : E → ℝ)
    (hL : Continuous L.uncurry) {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ ε : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hε : ε ∈ Ioo (-d₁) d₂) :
    cvFunctional (fun _ ↦ L) K (d₁ + d₂) (durationExchange x₁ x₂ d₁ d₂ ε) =
      actualCornerCost L x₁ x₂ d₁ d₂ ε + K (x₂ d₂) := by
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
  have hr₂ := (rescaling_factors_pos hd₁ hd₂ hε).2
  change cvFunctional (fun _ ↦ L) K (d₁ + d₂)
    (concatenate (d₁ + ε) (fun t ↦ x₁ (t / (1 + ε / d₁)))
      (fun t ↦ x₂ (t / (1 - ε / d₂)))) = _
  rw [h, heq]
  rw [show (d₁ + ε) = (1 + ε / d₁) * d₁ from hdurs.1.symm]
  simp only [mul_div_cancel_left₀ d₂ (ne_of_gt hr₂)]
  rfl

/-- Ambient optimality transfers to the scalar parameter only after the actual
competitors and their actual `cvFunctional` costs have been identified. -/
theorem actualCornerCost_isLocalMin_of_ambient_min (L : E → E → ℝ) (K : E → ℝ)
    (hL : Continuous L.uncurry) {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (feasible : Set (ℝ → E))
    (hfeasible : ∀ ε ∈ Ioo (-d₁) d₂, durationExchange x₁ x₂ d₁ d₂ ε ∈ feasible)
    (hmin : IsMinOn (cvFunctional (fun _ ↦ L) K (d₁ + d₂)) feasible
      (concatenate d₁ x₁ x₂)) :
    IsLocalMin (actualCornerCost L x₁ x₂ d₁ d₂) 0 := by
  apply actualCornerCost_isLocalMin_of_optimal_duration L K x₁ x₂ hd₁ hd₂
  intro ε hε
  have hzero : (0 : ℝ) ∈ Ioo (-d₁) d₂ := ⟨neg_neg_of_pos hd₁, hd₂⟩
  have hn := cvFunctional_durationExchange L K hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hzero
  rw [durationExchange_zero] at hn
  rw [← hn, ← cvFunctional_durationExchange L K hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hε]
  exact hmin (hfeasible ε hε)

/-- Actual fixed-endpoint curves with one interior corner and continuous one-sided
velocity extensions. No cost or variation identity is included in membership. -/
def fixedEndpointPiecewiseC1Curves (T : ℝ) (a b : E) : Set (ℝ → E) :=
  {y | y 0 = a ∧ y T = b ∧ ∃ s w₁ w₂,
    IsPiecewiseC₁On y w₁ w₂ T s ∧ Continuous w₁ ∧ Continuous w₂}

/-- Every valid duration exchange is an actual member of the fixed-endpoint
piecewise-C1 competitor class. -/
theorem durationExchange_mem_fixedEndpointPiecewiseC1Curves
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ ε : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hjoin : x₁ d₁ = x₂ 0)
    (hε : ε ∈ Ioo (-d₁) d₂) :
    durationExchange x₁ x₂ d₁ d₂ ε ∈
      fixedEndpointPiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂) := by
  have he := durationExchange_endpoints x₁ x₂ hd₁ hd₂ hε
  refine ⟨he.1, he.2, d₁ + ε, _, _,
    durationExchange_isPiecewiseC1 hx₁ hx₂ hd₁ hd₂ hε hjoin, ?_, ?_⟩
  · exact continuous_const.smul (hv₁.comp (continuous_id.div_const _))
  · exact continuous_const.smul
      (hv₂.comp ((continuous_id.sub continuous_const).div_const _))

/-- The reference concatenation itself belongs to the ambient competitor class. -/
theorem concatenate_mem_fixedEndpointPiecewiseC1Curves
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hjoin : x₁ d₁ = x₂ 0) :
    concatenate d₁ x₁ x₂ ∈ fixedEndpointPiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂) := by
  have h := durationExchange_mem_fixedEndpointPiecewiseC1Curves
    hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hjoin (show (0 : ℝ) ∈ Ioo (-d₁) d₂ from
      ⟨neg_neg_of_pos hd₁, hd₂⟩)
  simpa only [durationExchange_zero] using h

/-- Restricted two-smooth-arc energy condition from optimality of the original
`cvFunctional` over actual fixed-endpoint piecewise-C1 curves. The feasible
family, scalar cost derivative, and local-minimum transfer are all derived. -/
theorem corner_energy_eq_of_cvFunctional_min (L : E → E → ℝ) (K : E → ℝ)
    (hL : ContDiff ℝ 1 L.uncurry) {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hjoin : x₁ d₁ = x₂ 0)
    (hvd₁ : ∀ t ∈ Ico 0 d₁, DifferentiableAt ℝ v₁ t)
    (hvd₂ : ∀ t ∈ Ico 0 d₂, DifferentiableAt ℝ v₂ t)
    (hEL₁ : ∀ t ∈ Ico 0 d₁, HasDerivAt (fun s ↦ fderiv ℝ (L (x₁ s)) (v₁ s))
      (fderiv ℝ (fun y ↦ L y (v₁ t)) (x₁ t)) t)
    (hEL₂ : ∀ t ∈ Ico 0 d₂, HasDerivAt (fun s ↦ fderiv ℝ (L (x₂ s)) (v₂ s))
      (fderiv ℝ (fun y ↦ L y (v₂ t)) (x₂ t)) t)
    (hmin : IsMinOn (cvFunctional (fun _ ↦ L) K (d₁ + d₂))
      (fixedEndpointPiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂)) (concatenate d₁ x₁ x₂)) :
    energyCurve L x₁ v₁ d₁ = energyCurve L x₂ v₂ 0 := by
  apply corner_energy_eq_of_eulerLagrange_min L hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hvd₁ hvd₂ hEL₁ hEL₂
  exact actualCornerCost_isLocalMin_of_ambient_min L K hL.continuous hx₁ hv₁ hx₂ hv₂ hd₁ hd₂
    _ (fun ε hε ↦ durationExchange_mem_fixedEndpointPiecewiseC1Curves
      hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hjoin hε) hmin

end TimeReparametrization
