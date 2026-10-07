/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-!
# Integrable vector-valued measure tails

Open tails use `(a,b]` increments. Bounded variation is derived from integrability,
without absolute continuity or a supplied bounded-variation certificate.
-/
@[expose] public section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
/-- A vector tail excluding the atom at its argument. -/
noncomputable def openIntegralTail (μ : Measure ℝ) (w : ℝ → E) (t : ℝ) : E :=
  ∫ s in Ioi t, w s ∂μ
/-- A vector tail including the atom at its argument. -/
noncomputable def closedIntegralTail (μ : Measure ℝ) (w : ℝ → E) (t : ℝ) : E :=
  ∫ s in Ici t, w s ∂μ
variable {μ : Measure ℝ} {w : ℝ → E}
omit [CompleteSpace E] in
theorem openIntegralTail_sub (hw : Integrable w μ) {a b : ℝ} (hab : a ≤ b) :
    openIntegralTail μ w a - openIntegralTail μ w b = ∫ s in Ioc a b, w s ∂μ := by
  have hu : Ioc a b ∪ Ioi b = Ioi a := by
    ext s
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (hs | hs)
      · exact hs.1
      · exact lt_of_le_of_lt hab hs
    · intro hs
      exact (le_or_gt s b).elim (fun h ↦ Or.inl ⟨hs, h⟩) Or.inr
  have hd : Disjoint (Ioc a b) (Ioi b) := disjoint_left.mpr
    (fun _ hs ht ↦ (not_lt_of_ge hs.2) ht)
  have he := setIntegral_union hd measurableSet_Ioi hw.integrableOn hw.integrableOn
  rw [hu] at he
  exact sub_eq_iff_eq_add.mpr (by simpa [openIntegralTail, add_comm] using he)
theorem closedIntegralTail_sub_openIntegralTail (hw : Integrable w μ) (t : ℝ) :
    closedIntegralTail μ w t - openIntegralTail μ w t = μ.real {t} • w t := by
  have hu : ({t} : Set ℝ) ∪ Ioi t = Ici t := by
    ext s
    simp only [mem_union, mem_singleton_iff, mem_Ioi, mem_Ici]
    constructor
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.le
    · intro h
      exact (eq_or_lt_of_le h).imp Eq.symm id
  have hd : Disjoint ({t} : Set ℝ) (Ioi t) := by
    apply disjoint_left.mpr
    intro s hs ht
    simp only [mem_singleton_iff] at hs
    subst s
    exact lt_irrefl _ ht
  have he := setIntegral_union hd measurableSet_Ioi hw.integrableOn hw.integrableOn
  rw [hu, integral_singleton] at he
  exact sub_eq_iff_eq_add.mpr (by simpa [closedIntegralTail, openIntegralTail, add_comm] using he)
omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem normIntegralTail_bounds (hw : Integrable w μ) (t : ℝ) :
    0 ≤ openIntegralTail μ (fun s ↦ ‖w s‖) t ∧
      openIntegralTail μ (fun s ↦ ‖w s‖) t ≤ ∫ s, ‖w s‖ ∂μ := by
  constructor
  · exact integral_nonneg (fun _ ↦ norm_nonneg _)
  · exact setIntegral_le_integral hw.norm (Eventually.of_forall (fun _ ↦ norm_nonneg _))
omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem antitone_normIntegralTail (hw : Integrable w μ) :
    Antitone (openIntegralTail μ (fun s ↦ ‖w s‖)) := by
  intro a b hab
  have he := openIntegralTail_sub hw.norm hab
  have hn : 0 ≤ ∫ s in Ioc a b, ‖w s‖ ∂μ := integral_nonneg (fun _ ↦ norm_nonneg _)
  linarith
omit [CompleteSpace E] in
theorem dist_openIntegralTail_le (hw : Integrable w μ) {a b : ℝ} (hab : a ≤ b) :
    dist (openIntegralTail μ w a) (openIntegralTail μ w b) ≤
      dist (openIntegralTail μ (fun s ↦ ‖w s‖) a)
        (openIntegralTail μ (fun s ↦ ‖w s‖) b) := by
  rw [dist_eq_norm, openIntegralTail_sub hw hab, Real.dist_eq,
    openIntegralTail_sub hw.norm hab, abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
  exact norm_integral_le_integral_norm _
omit [CompleteSpace E] in
/-- Vector-tail BV follows from an integrable norm, including for singular measures. -/
theorem boundedVariationOn_openIntegralTail (hw : Integrable w μ) :
    BoundedVariationOn (openIntegralTail μ w) univ := by
  let q := openIntegralTail μ (fun s ↦ ‖w s‖)
  have hm : Monotone (fun t ↦ -q t) := fun _ _ hab ↦
    neg_le_neg (antitone_normIntegralTail hw hab)
  have hq : BoundedVariationOn q univ := by
    have hv := (hm.monotoneOn univ).boundedVariationOn
      (C := ∫ s, ‖w s‖ ∂μ) (fun t _ ↦ by
        rw [abs_neg, abs_of_nonneg (normIntegralTail_bounds hw t).1]
        exact (normIntegralTail_bounds hw t).2)
    simpa only [Function.comp_def, neg_neg] using
      (isometry_neg (G := ℝ)).lipschitzWith.comp_boundedVariationOn hv
  have he : eVariationOn (openIntegralTail μ w) univ ≤ eVariationOn q univ := by
    unfold eVariationOn
    apply iSup_le
    intro p
    apply le_iSup_of_le p
    apply Finset.sum_le_sum
    intro i hi
    rw [edist_dist, edist_dist]
    apply ENNReal.ofReal_le_ofReal
    simpa only [dist_comm] using dist_openIntegralTail_le hw (p.2.2.1 (Nat.le_succ i))
  exact ne_top_of_le_ne_top hq he
omit [CompleteSpace E] in
/-- The constructed open tail is right-continuous, even at atoms. -/
theorem continuousWithinAt_openIntegralTail (hw : Integrable w μ) (t : ℝ) :
    ContinuousWithinAt (openIntegralTail μ w) (Ici t) t := by
  have hm : ∀ᶠ r in 𝓝[Ici t] t, AEStronglyMeasurable ((Ioi r).indicator w) μ :=
    Eventually.of_forall (fun r ↦ hw.aestronglyMeasurable.indicator measurableSet_Ioi)
  have hb : ∀ᶠ r in 𝓝[Ici t] t, ∀ᵐ s ∂μ, ‖(Ioi r).indicator w s‖ ≤ ‖w s‖ := by
    apply Eventually.of_forall
    intro r
    apply Eventually.of_forall
    intro s
    by_cases h : s ∈ Ioi r <;> simp [h, norm_nonneg]
  have hl : ∀ᵐ s ∂μ, Tendsto (fun r ↦ (Ioi r).indicator w s)
      (𝓝[Ici t] t) (𝓝 ((Ioi t).indicator w s)) := by
    apply Eventually.of_forall
    intro s
    by_cases h : t < s
    · have he : ∀ᶠ r in 𝓝[Ici t] t, r < s :=
        (eventually_lt_nhds h).filter_mono nhdsWithin_le_nhds
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with r hr
      simp [h, hr]
    · have he : ∀ᶠ r in 𝓝[Ici t] t, t ≤ r := self_mem_nhdsWithin
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with r hr
      have hs : ¬ r < s := not_lt.mpr ((not_lt.mp h).trans hr)
      simp [h, hs]
  have hi := tendsto_integral_filter_of_dominated_convergence (fun s ↦ ‖w s‖) hm hb
    hw.norm hl
  change Tendsto (fun r ↦ ∫ s in Ioi r, w s ∂μ) _ (𝓝 (∫ s in Ioi t, w s ∂μ))
  simpa only [integral_indicator measurableSet_Ioi] using hi

omit [CompleteSpace E] in
/-- The left trace of the open tail is the closed tail. -/
theorem tendsto_openIntegralTail_left (hw : Integrable w μ) (t : ℝ) :
    Tendsto (openIntegralTail μ w) (𝓝[<] t) (𝓝 (closedIntegralTail μ w t)) := by
  have hm : ∀ᶠ r in 𝓝[<] t, AEStronglyMeasurable ((Ioi r).indicator w) μ :=
    Eventually.of_forall (fun r ↦ hw.aestronglyMeasurable.indicator measurableSet_Ioi)
  have hb : ∀ᶠ r in 𝓝[<] t, ∀ᵐ s ∂μ, ‖(Ioi r).indicator w s‖ ≤ ‖w s‖ := by
    apply Eventually.of_forall
    intro r
    apply Eventually.of_forall
    intro s
    by_cases h : s ∈ Ioi r <;> simp [h, norm_nonneg]
  have hl : ∀ᵐ s ∂μ, Tendsto (fun r ↦ (Ioi r).indicator w s)
      (𝓝[<] t) (𝓝 ((Ici t).indicator w s)) := by
    apply Eventually.of_forall
    intro s
    by_cases h : t ≤ s
    · have he : ∀ᶠ r in 𝓝[<] t, r < t := self_mem_nhdsWithin
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with r hr
      have hs := hr.trans_le h
      simp [h, hs]
    · have he : ∀ᶠ r in 𝓝[<] t, s < r :=
        (eventually_gt_nhds (not_le.mp h)).filter_mono nhdsWithin_le_nhds
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with r hr
      have hs : ¬ r < s := not_lt.mpr hr.le
      simp [h, hs]
  have hi := tendsto_integral_filter_of_dominated_convergence (fun s ↦ ‖w s‖) hm hb
    hw.norm hl
  change Tendsto (fun r ↦ ∫ s in Ioi r, w s ∂μ) _ (𝓝 (∫ s in Ici t, w s ∂μ))
  simpa only [integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ici] using hi

omit [CompleteSpace E] in
/-- Restriction to a terminal half-line produces exactly the finite-horizon open tail. -/
theorem openIntegralTail_restrict_Iic (μ : Measure ℝ) (w : ℝ → E) (T t : ℝ) :
    openIntegralTail (μ.restrict (Iic T)) w t = ∫ s in Ioc t T, w s ∂μ := by
  unfold openIntegralTail
  rw [Measure.restrict_restrict measurableSet_Ioi]
  rfl

omit [CompleteSpace E] in
/-- The open finite-horizon tail is zero at the terminal time, including terminal atoms. -/
theorem openIntegralTail_terminal (μ : Measure ℝ) (w : ℝ → E) (T : ℝ) :
    openIntegralTail (μ.restrict (Iic T)) w T = 0 := by
  rw [openIntegralTail_restrict_Iic]
  simp

end MeasureTheory
