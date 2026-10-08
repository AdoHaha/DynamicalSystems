/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.StateMultiplierStieltjes
public import DynamicalSystems.OptimalControl.ContinuousTime.EpsilonLevelBridge
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Integral complementarity from constancy on slack intervals

The interval constancy and terminal collar delivered by the necessary conditions
of Berkovitz & Medhin Theorem 11.6.3 imply that the multiplier measure is carried
by the contact set. Consequently its integral against the reference constraint
is zero, providing the complementarity input of Theorem 11.8.4.

State-constraint integrability follows from joint measurability, bounds on bounded
state sets, and continuity of the trajectory. The full costate/sufficiency bridge
is separate: the present sufficiency API also requires a primitive with no time
derivative of the constraint, which does not follow for a time-dependent constraint.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace OptimalControl.BoundedState

section Complementarity

variable {T : ℝ} {lam g : ℝ → ℝ}

/-- A zero terminal collar removes the terminal mass. The collar is provided
by the endpoint-slackness part of Theorem 11.6.3. -/
theorem multiplierMeasure_Ioi_eq_zero_of_terminal_collar
    (hT : 0 < T) (hanti : AntitoneOn lam (Icc (0 : ℝ) T))
    (δ : ℝ) (hδ : 0 < δ) (hδT : δ < T)
    (hcollar : ∀ t ∈ Icc (T - δ) T, lam t = 0) :
    multiplierMeasure hT.le hanti (Ioi (T - δ / 2)) = 0 := by
  have hlamT : lam T = 0 := hcollar T ⟨by linarith, le_rfl⟩
  have hr : T - δ / 2 ∈ Ico (T - δ) T := ⟨by linarith, by linarith⟩
  have hsub : Icc (T - δ) T ⊆ Icc (0 : ℝ) T := by
    intro t ht
    exact ⟨(by linarith [ht.1]), ht.2⟩
  have hrl : rightMultiplier T lam (T - δ / 2) = 0 := by
    rw [rightMultiplier_eq_of_const hsub
      (fun t ht ↦ (hcollar t ht).trans (hcollar (T - δ) ⟨le_rfl, by linarith⟩).symm) hr]
    exact hcollar (T - δ) ⟨le_rfl, by linarith⟩
  have hIoc : multiplierMeasure hT.le hanti (Ioc (T - δ / 2) T) = 0 := by
    rw [multiplierMeasure_Ioc_horizon hT.le hanti hlamT, hrl]
    simp
  have hIoi := multiplierMeasure_Ioi_horizon hT.le hanti hlamT
  rw [show Ioi (T - δ / 2) = Ioc (T - δ / 2) T ∪ Ioi T from by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      rcases le_or_gt t T with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · linarith]
  exact measure_union_null hIoc hIoi

/-- The interval complementarity supplied by the necessary conditions implies
contact-set concentration of the Stieltjes measure, and hence integral
complementarity. The terminal collar handles the atom at the terminal time. -/
theorem ae_constraint_eq_zero_of_const_on_slack
    (hT : 0 < T) (hanti : AntitoneOn lam (Icc (0 : ℝ) T))
    (hg : ContinuousOn g (Icc (0 : ℝ) T)) (hgn : ∀ t ∈ Icc (0 : ℝ) T, g t ≤ 0)
    (hslack : ∀ α β, α ∈ Icc (0 : ℝ) T → β ∈ Icc (0 : ℝ) T →
      (∀ r ∈ Icc α β, g r < 0) → ∀ t ∈ Icc α β, lam t = lam α)
    (δ : ℝ) (hδ : 0 < δ) (hδT : δ < T)
    (hcollar : ∀ t ∈ Icc (T - δ) T, lam t = 0) :
    ∀ᵐ t ∂(multiplierMeasure hT.le hanti).restrict (Ioc 0 T), g t = 0 := by
  let μ := multiplierMeasure hT.le hanti
  have hsupport : ∀ᵐ t ∂μ.restrict (Ioc 0 T), t ∈ μ.support := by
    have hs : ∀ᵐ t ∂μ, t ∈ μ.support := Measure.support_mem_ae
    exact hs.filter_mono (ae_mono Measure.restrict_le_self)
  have hterminal : μ (Ioi (T - δ / 2)) = 0 :=
    multiplierMeasure_Ioi_eq_zero_of_terminal_collar hT hanti δ hδ hδT hcollar
  filter_upwards [hsupport, ae_restrict_mem measurableSet_Ioc] with t ht htI
  apply le_antisymm (hgn t ⟨htI.1.le, htI.2⟩)
  by_contra h
  have hgt : g t < 0 := lt_of_not_ge h
  have htT : t < T := by
    rcases lt_or_eq_of_le htI.2 with hlt | heq
    · exact hlt
    · have hpos := (Measure.mem_support_iff_forall t).mp ht (Ioi (T - δ / 2))
        (Ioi_mem_nhds (by rw [heq]; linarith))
      rw [hterminal] at hpos
      exact (lt_irrefl _ hpos).elim
  have hcont : ContinuousAt g t :=
    (hg t ⟨htI.1.le, htI.2⟩).continuousAt (Icc_mem_nhds htI.1 htT)
  obtain ⟨ε, hε, hεg⟩ := Metric.eventually_nhds_iff.mp
    (hcont.tendsto.eventually (Iio_mem_nhds hgt))
  let r := min (ε / 2) (min (t / 2) ((T - t) / 2))
  have hr : 0 < r := lt_min (by linarith) (lt_min (by linarith [htI.1]) (by linarith))
  have hre : r < ε := (min_le_left _ _).trans_lt (by linarith)
  have hrt : r ≤ t / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrT : r ≤ (T - t) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hα : t - r ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have hβ : t + r ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have hneg : ∀ s ∈ Icc (t - r) (t + r), g s < 0 := by
    intro s hs
    apply hεg
    rw [Real.dist_eq]
    exact (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩).trans_lt hre
  have hzero : μ (Ioo (t - r) (t + r)) = 0 :=
    multiplierMeasure_Ioo_eq_zero_of_const hT.le hanti (by linarith)
      (Icc_subset_Icc hα.1 hβ.2) (hslack _ _ hα hβ hneg)
  have hpos := (Measure.mem_support_iff_forall t).mp ht (Ioo (t - r) (t + r))
    (Ioo_mem_nhds (by linarith) (by linarith))
  rw [hzero] at hpos
  exact (lt_irrefl _ hpos).elim

/-- The integral complementarity input of Theorem 11.8.4 follows from the
interval constancy and terminal collar in Theorem 11.6.3. -/
theorem integral_constraint_eq_zero_of_const_on_slack
    (hT : 0 < T) (hanti : AntitoneOn lam (Icc (0 : ℝ) T))
    (hg : ContinuousOn g (Icc (0 : ℝ) T)) (hgn : ∀ t ∈ Icc (0 : ℝ) T, g t ≤ 0)
    (hslack : ∀ α β, α ∈ Icc (0 : ℝ) T → β ∈ Icc (0 : ℝ) T →
      (∀ r ∈ Icc α β, g r < 0) → ∀ t ∈ Icc α β, lam t = lam α)
    (δ : ℝ) (hδ : 0 < δ) (hδT : δ < T)
    (hcollar : ∀ t ∈ Icc (T - δ) T, lam t = 0) :
    (∫ t in Ioc 0 T, g t ∂multiplierMeasure hT.le hanti) = 0 := by
  have h := ae_constraint_eq_zero_of_const_on_slack hT hanti hg hgn hslack δ hδ hδT hcollar
  rw [integral_congr_ae h, integral_zero]

end Complementarity

section Integrability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}

/-- Regularity of the constraint discharges its Stieltjes integrability along
a continuous trajectory, even though the constraint need only be measurable in time. -/
theorem integrableOn_stateConstraint_of_regularity
    (hreg : StateConstraintRegularity G Gx) (x : ℝ → E) (a b : ℝ)
    (hx : ContinuousOn x (Icc a b)) (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    IntegrableOn (fun t ↦ G t (x t)) (Icc a b) μ := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  obtain ⟨C, _, hC⟩ := hreg.bounded R
  have hm := hreg.measurable_G.comp_aemeasurable
    (aemeasurable_id.prodMk (hx.aemeasurable measurableSet_Icc))
  refine IntegrableOn.of_bound isCompact_Icc.measure_lt_top hm.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simpa only [Real.norm_eq_abs] using (hC t (x t) (hR t ht)).1

variable {V W : Type*} [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

/-- The state-gradient/velocity pairing is interval integrable under
`StateConstraintRegularity`; no separate integrability hypothesis is needed. -/
theorem intervalIntegrable_stateGradient_velocity_of_regularity
    (hreg : StateConstraintRegularity G Gx) (γ : VelocityTrajectory P) :
    IntervalIntegrable (fun t ↦ Gx t (γ.value t) (γ.velocity t)) volume 0 P.horizon := by
  have hb : ∀ R : ℝ, ∃ C : ℝ, ∀ t y, ‖y‖ ≤ R → ‖Gx t y‖ ≤ C := by
    intro R
    obtain ⟨C, _, hC⟩ := hreg.bounded R
    exact ⟨C, fun t y hy ↦ (hC t y hy).2⟩
  have hgint := intervalIntegrable_comp_value γ hreg.measurable_Gx hb
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn γ.continuousOn_value
  obtain ⟨C, _, hC⟩ := hreg.bounded R
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le P.horizon_pos.le]
  have hgmeas := ((intervalIntegrable_iff_integrableOn_Ioc_of_le P.horizon_pos.le).mp
    hgint).aestronglyMeasurable
  have hv := (intervalIntegrable_iff_integrableOn_Ioc_of_le P.horizon_pos.le).mp
    γ.velocity_intervalIntegrable
  have hmeas : AEStronglyMeasurable (fun t ↦ Gx t (γ.value t) (γ.velocity t))
      (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hgmeas.prodMk hv.aestronglyMeasurable)
  refine (hv.norm.const_mul C).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (Gx t (γ.value t)).le_opNorm (γ.velocity t) |>.trans
    (mul_le_mul_of_nonneg_right ((hC t _ (hR t ⟨ht.1.le, ht.2⟩)).2) (norm_nonneg _))

/-- Multiplication by a nonincreasing multiplier preserves integrability of
the state-gradient/velocity pairing. Monotonicity supplies both measurability and a bound. -/
theorem intervalIntegrable_multiplier_stateGradient_velocity_of_regularity
    (hreg : StateConstraintRegularity G Gx) (γ : VelocityTrajectory P)
    (lam : ℝ → ℝ) (hanti : AntitoneOn lam (Icc (0 : ℝ) P.horizon)) :
    IntervalIntegrable (fun t ↦ lam t * Gx t (γ.value t) (γ.velocity t))
      volume 0 P.horizon := by
  have hk := (intervalIntegrable_iff_integrableOn_Ioc_of_le P.horizon_pos.le).mp
    (intervalIntegrable_stateGradient_velocity_of_regularity hreg γ)
  have hm : AEStronglyMeasurable lam (volume.restrict (Ioc (0 : ℝ) P.horizon)) := by
    have hm := ((monotone_multiplierExtension P.horizon_pos.le hanti).measurable.neg)
      .aestronglyMeasurable
    apply hm.restrict.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [multiplierExtension_of_mem ⟨ht.1.le, ht.2⟩, neg_neg]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le P.horizon_pos.le]
  refine hk.bdd_mul hm (C := |lam 0| + |lam P.horizon|) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_le]
  have hI : t ∈ Icc (0 : ℝ) P.horizon := ⟨ht.1.le, ht.2⟩
  have h0 := hanti ⟨le_rfl, P.horizon_pos.le⟩ hI ht.1.le
  have hT := hanti hI ⟨P.horizon_pos.le, le_rfl⟩ ht.2
  constructor <;> linarith [neg_abs_le (lam P.horizon), le_abs_self (lam 0),
    abs_nonneg (lam 0), abs_nonneg (lam P.horizon)]

end Integrability

end OptimalControl.BoundedState
