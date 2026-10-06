/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.OccupationIntegral
public import DynamicalSystems.OptimalControl.ContinuousTime.ControlHorizon
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Joint continuity of the Volterra slice integral

For a parameter-dependent continuous field `F p : [0,T] × U → E` the slice integral
`(p, ρ, t) ↦ ∫_{(0,t] × U} F p dρ` is jointly continuous in the parameter, the relaxed
control (weak topology) and the time `t`.  Continuity in `(p, ρ)` for fixed `t` is
`RelaxedControl.continuous_setIntegral_param`; continuity in `t`, uniformly in `ρ`, comes from
the fixed Lebesgue time marginal (`‖∫_{(r,s]×U} F dρ‖ ≤ M (s − r)/T`).  Consequently the Volterra
residual energy `∫ ‖x(t) − x₀ − T ∫_{(0,t]×U} f dρ‖² dt/T` of Berkovitz & Medhin (11.3.6) is a
continuous function of `(x, ρ)`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.6).
Names are concept names; the citation lives in docstrings.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

namespace OptimalControl.RelaxedControl

variable {T : ℝ} {U E : Type*}
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [CompactSpace U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [BorelSpace U] [CompactSpace U] [FiniteDimensional ℝ E] in
/-- **Lipschitz estimate in time, uniform in the control**: the integral of a bounded field over
the slab `(r, s] × U` has norm at most `M (s − r) / T` because the time marginal is normalised
Lebesgue measure. -/
theorem norm_setIntegral_slab_le {hT : 0 < T}
    (ρ : RelaxedControl (ControlTime T) U (horizonProbability T hT))
    (F : (ControlTime T × U) →ᵇ E) {M : ℝ} (hM : ‖F‖ ≤ M) {r s : ControlTime T} (hrs : r ≤ s) :
    ‖∫ z in Ioc r s ×ˢ (univ : Set U), F z ∂ρ.measure‖ ≤ M * (((s : ℝ) - r) / T) := by
  have hn : ‖∫ z in Ioc r s ×ˢ (univ : Set U), F z ∂ρ.measure‖ ≤
      M * ρ.measure.real (Ioc r s ×ˢ univ) :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
      (fun z _ => (F.norm_coe_le_norm z).trans hM)
  have hm : ρ.measure.real (Ioc r s ×ˢ univ) = ((s : ℝ) - r) / T := by
    rw [measureReal_def, ρ.measure_prod_univ measurableSet_Ioc,
      eq_div_iff hT.ne', mul_comm]
    exact scale_horizonProbability_real_Ioc T hT r s hrs
  rwa [hm] at hn

omit [FiniteDimensional ℝ E] in
/-- The difference of two initial slices `(0, s]` and `(0, r]` is the slab integral over
`(r, s]`. -/
theorem setIntegral_slice_sub {hT : 0 < T}
    (ρ : RelaxedControl (ControlTime T) U (horizonProbability T hT))
    (F : (ControlTime T × U) →ᵇ E) {r s : ControlTime T} (hrs : r ≤ s) :
    (∫ z in Ioc (timeZero T hT.le) s ×ˢ (univ : Set U), F z ∂ρ.measure) -
      ∫ z in Ioc (timeZero T hT.le) r ×ˢ (univ : Set U), F z ∂ρ.measure =
    ∫ z in Ioc r s ×ˢ (univ : Set U), F z ∂ρ.measure := by
  set a := timeZero T hT.le
  have har : a ≤ r := r.2.1
  have hdiff : (Ioc a s ×ˢ (univ : Set U)) \ (Ioc a r ×ˢ univ) = Ioc r s ×ˢ univ := by
    ext z
    simp only [Set.mem_sdiff, mem_prod, mem_Ioc, mem_univ, and_true]
    constructor
    · rintro ⟨⟨haz, hzs⟩, hn⟩
      exact ⟨lt_of_not_ge (fun hzr => hn ⟨haz, hzr⟩), hzs⟩
    · rintro ⟨hrz, hzs⟩
      exact ⟨⟨har.trans_lt hrz, hzs⟩, fun h => (not_le_of_gt hrz) h.2⟩
  have hsub : Ioc a r ×ˢ (univ : Set U) ⊆ Ioc a s ×ˢ univ :=
    Set.prod_mono (Ioc_subset_Ioc_right hrs) Subset.rfl
  have heq := setIntegral_sdiff (measurableSet_Ioc.prod MeasurableSet.univ)
    (F.continuous.integrable_of_hasCompactSupport (μ := ρ.measure)
      (HasCompactSupport.of_compactSpace _)).integrableOn hsub
  rw [hdiff] at heq
  rw [← heq]

omit [FiniteDimensional ℝ E] in
/-- The slice integral is `M/T`-Lipschitz in time for a field of sup norm at most `M`. -/
theorem norm_setIntegral_slice_sub_le {hT : 0 < T}
    (ρ : RelaxedControl (ControlTime T) U (horizonProbability T hT))
    (F : (ControlTime T × U) →ᵇ E) {M : ℝ} (hM : ‖F‖ ≤ M) (r s : ControlTime T) :
    ‖(∫ z in Ioc (timeZero T hT.le) s ×ˢ (univ : Set U), F z ∂ρ.measure) -
      ∫ z in Ioc (timeZero T hT.le) r ×ˢ (univ : Set U), F z ∂ρ.measure‖ ≤
      M * (dist s r / T) := by
  rcases le_total r s with hrs | hsr
  · have hd : dist s r = (s : ℝ) - (r : ℝ) := by
      rw [Subtype.dist_eq, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.2 (show (r : ℝ) ≤ s from hrs))]
    rw [setIntegral_slice_sub ρ F hrs, hd]
    exact norm_setIntegral_slab_le ρ F hM hrs
  · have hd : dist s r = (r : ℝ) - (s : ℝ) := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.2 (show (s : ℝ) ≤ r from hsr))]
    rw [norm_sub_rev, setIntegral_slice_sub ρ F hsr, hd]
    exact norm_setIntegral_slab_le ρ F hM hsr

/-- **Joint continuity of the Volterra slice integral** in the parameter, the weak relaxed control
and the time `t`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6). -/
theorem continuous_sliceIntegral_joint {hT : 0 < T} {Q : Type*} [TopologicalSpace Q]
    (F : Q → ControlTime T × U → E) (hF : Continuous (Function.uncurry F)) :
    Continuous (fun q : (Q × RelaxedControl (ControlTime T) U (horizonProbability T hT)) ×
        ControlTime T =>
      ∫ z in Ioc (timeZero T hT.le) q.2 ×ˢ (univ : Set U), F q.1.1 z ∂q.1.2.measure) := by
  let Fc : Q → C(ControlTime T × U, E) := fun p =>
    ⟨F p, hF.comp (continuous_const.prodMk continuous_id)⟩
  have hFc : Continuous Fc := ContinuousMap.continuous_of_continuous_uncurry Fc hF
  let Fb : Q → ((ControlTime T × U) →ᵇ E) := fun p => BoundedContinuousFunction.mkOfCompact (Fc p)
  have hFb : Continuous Fb :=
    (ContinuousMap.isometryEquivBoundedOfCompact (ControlTime T × U) E).continuous.comp hFc
  have hFbF : ∀ p z, Fb p z = F p z := fun _ _ => rfl
  simp only [← hFbF]
  rw [continuous_iff_continuousAt]
  rintro ⟨⟨p₀, ρ₀⟩, t₀⟩
  set g : (Q × RelaxedControl (ControlTime T) U (horizonProbability T hT)) × ControlTime T → E :=
    fun q => ∫ z in Ioc (timeZero T hT.le) q.2 ×ˢ (univ : Set U), Fb q.1.1 z ∂q.1.2.measure
    with hg
  set g' : (Q × RelaxedControl (ControlTime T) U (horizonProbability T hT)) × ControlTime T → E :=
    fun q => ∫ z in Ioc (timeZero T hT.le) t₀ ×ˢ (univ : Set U), Fb q.1.1 z ∂q.1.2.measure
    with hg'
  have h2 : Tendsto g' (𝓝 ((p₀, ρ₀), t₀)) (𝓝 (g ((p₀, ρ₀), t₀))) := by
    have hc := (continuous_setIntegral_param (ν := horizonProbability T hT) (E := E)
      (fun p z => Fb p z) (by
        have : Function.uncurry (fun p z => Fb p z) = Function.uncurry F := rfl
        rw [this]; exact hF) (s := Ioc (timeZero T hT.le) t₀) measurableSet_Ioc)
    exact (hc.comp continuous_fst).tendsto _
  have hM : ∀ᶠ q in 𝓝 ((p₀, ρ₀), t₀), ‖Fb q.1.1‖ ≤ ‖Fb p₀‖ + 1 := by
    have hcont : ContinuousAt (fun q : (Q × RelaxedControl (ControlTime T) U
        (horizonProbability T hT)) × ControlTime T => ‖Fb q.1.1‖) ((p₀, ρ₀), t₀) :=
      (hFb.comp (continuous_fst.comp continuous_fst)).norm.continuousAt
    exact hcont.eventually (eventually_le_nhds (lt_add_one _) |>.mono fun _ h => h)
  have h1 : Tendsto (fun q => g q - g' q) (𝓝 ((p₀, ρ₀), t₀)) (𝓝 0) := by
    have hdist : Tendsto (fun q : (Q × RelaxedControl (ControlTime T) U
        (horizonProbability T hT)) × ControlTime T => (‖Fb p₀‖ + 1) * (dist q.2 t₀ / T))
        (𝓝 ((p₀, ρ₀), t₀)) (𝓝 0) := by
      have : Continuous fun q : (Q × RelaxedControl (ControlTime T) U
          (horizonProbability T hT)) × ControlTime T => (‖Fb p₀‖ + 1) * (dist q.2 t₀ / T) :=
        continuous_const.mul ((continuous_snd.dist continuous_const).div_const _)
      simpa using this.tendsto ((p₀, ρ₀), t₀)
    refine squeeze_zero_norm' ?_ hdist
    filter_upwards [hM] with q hq
    exact norm_setIntegral_slice_sub_le q.1.2 (Fb q.1.1) hq t₀ q.2
  have := h1.add h2
  simp only [zero_add, sub_add_cancel] at this
  exact this

/-- The integral of a jointly continuous family over a compact probability space is continuous
in the parameter. -/
theorem continuous_integral_of_jointly_continuous {α X : Type*} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [TopologicalSpace X]
    (μ : Measure α) [IsProbabilityMeasure μ] (H : X → α → ℝ)
    (hH : Continuous (Function.uncurry H)) :
    Continuous fun x => ∫ a, H x a ∂μ := by
  let Hc : X → C(α, ℝ) := fun x => ⟨H x, hH.comp (continuous_const.prodMk continuous_id)⟩
  have hHc : Continuous Hc := ContinuousMap.continuous_of_continuous_uncurry Hc hH
  let Hb : X → (α →ᵇ ℝ) := fun x => BoundedContinuousFunction.mkOfCompact (Hc x)
  have hHb : Continuous Hb :=
    (ContinuousMap.isometryEquivBoundedOfCompact α ℝ).continuous.comp hHc
  have hlip : LipschitzWith 1 (fun f : α →ᵇ ℝ => ∫ a, f a ∂μ) := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    rw [Real.dist_eq, ← integral_sub (f.integrable μ) (g.integrable μ)]
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun a => f a - g a) (C := dist f g)
      (Eventually.of_forall fun a => by
        rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist a)
    simpa using this
  exact hlip.continuous.comp hHb

end OptimalControl.RelaxedControl
