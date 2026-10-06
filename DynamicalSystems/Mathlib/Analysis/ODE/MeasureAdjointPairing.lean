/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.MeasureAdjoint

/-!
# Measure adjoint pairing with indexed state constraints

The multiplier measure may live on time times a finite constraint index. Fubini
uses the time projection, preserving all atoms and avoiding a supplied pairing identity.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology

namespace MeasureAdjoint

variable {Ω τ X : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [LinearOrder τ] [TopologicalSpace τ] [OrderTopology τ] [SecondCountableTopology τ]
  [MeasurableSpace τ] [BorelSpace τ]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {μ : Measure Ω} {ν : Measure τ} [SFinite μ] [SFinite ν]

/-- Indexed measures pair with actual integral variations through their time projection. -/
theorem integral_indexed_tail_pairing (κ : Ω → τ) (hκ : Continuous κ)
    {w : Ω → X →L[ℝ] ℝ} (hw : Integrable w μ) {v : τ → X} (hv : Integrable v ν) :
    (∫ q, w q (∫ t in Iio (κ q), v t ∂ν) ∂μ) =
      ∫ t, (∫ q in {q | t < κ q}, w q ∂μ) (v t) ∂ν := by
  classical
  have hp : Integrable (fun z : Ω × τ ↦ w z.1 (v z.2)) (μ.prod ν) := by
    apply hw.op_fst_snd _ _ hv
    · exact continuous_fst.clm_apply continuous_snd
    · exact ⟨1, fun f x ↦ by simpa using f.le_opNorm x⟩
  have hs : MeasurableSet {z : Ω × τ | z.2 < κ z.1} :=
    (isOpen_lt continuous_snd (hκ.comp continuous_fst)).measurableSet
  have ht : Integrable (fun z : Ω × τ ↦ if z.2 < κ z.1 then w z.1 (v z.2) else 0)
      (μ.prod ν) := by
    apply (hp.indicator hs).congr
    exact Eventually.of_forall (fun _ ↦ by simp [Set.indicator])
  have he := integral_integral_swap (f := fun q t ↦
    if t < κ q then w q (v t) else 0) ht
  have hl (q : Ω) : w q (∫ t in Iio (κ q), v t ∂ν) =
      ∫ t, (if t < κ q then w q (v t) else 0) ∂ν := by
    rw [← (w q).integral_comp_comm hv.integrableOn, ← integral_indicator measurableSet_Iio]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ ↦ by simp [Set.indicator])
  have hr (t : τ) : (∫ q in {q | t < κ q}, w q ∂μ) (v t) =
      ∫ q, (if t < κ q then w q (v t) else 0) ∂μ := by
    have hs' : MeasurableSet {q | t < κ q} :=
      (isOpen_lt continuous_const hκ).measurableSet
    rw [ContinuousLinearMap.integral_apply hw.integrableOn, ← integral_indicator hs']
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ ↦ by simp [Set.indicator])
  simp_rw [hl, hr]
  exact he

omit [CompleteSpace X] in
/-- Product integrability derives integrability of the indexed adjoint-control pairing. -/
theorem integrable_indexed_tail_apply (κ : Ω → τ) (hκ : Continuous κ)
    {w : Ω → X →L[ℝ] ℝ} (hw : Integrable w μ) {v : τ → X} (hv : Integrable v ν) :
    Integrable (fun t ↦ (∫ q in {q | t < κ q}, w q ∂μ) (v t)) ν := by
  have hp : Integrable (fun z : Ω × τ ↦ w z.1 (v z.2)) (μ.prod ν) := by
    apply hw.op_fst_snd _ _ hv
    · exact continuous_fst.clm_apply continuous_snd
    · exact ⟨1, fun f x ↦ by simpa using f.le_opNorm x⟩
  have hs : MeasurableSet {z : Ω × τ | z.2 < κ z.1} :=
    (isOpen_lt continuous_snd (hκ.comp continuous_fst)).measurableSet
  have hi := (hp.indicator hs).integral_prod_right
  apply hi.congr
  apply Eventually.of_forall
  intro t
  dsimp only
  have hs' : MeasurableSet {q | t < κ q} :=
    (isOpen_lt continuous_const hκ).measurableSet
  rw [ContinuousLinearMap.integral_apply hw.integrableOn, ← integral_indicator hs']
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ ↦ by simp [Set.indicator])

/-- Terminal, running and indexed state-constraint variations assemble into one adjoint
pairing. Each tail is constructed, and the identity follows from Fubini. -/
theorem integral_firstVariation_pairing (κ : Ω → τ) (hκ : Continuous κ)
    (lambda : X →L[ℝ] ℝ) {ell : τ → X →L[ℝ] ℝ} (hell : Integrable ell ν)
    {normal : Ω → X →L[ℝ] ℝ} (hnormal : Integrable normal μ)
    {v : τ → X} (hv : Integrable v ν) :
    lambda (∫ t, v t ∂ν) + (∫ s, ell s (∫ t in Iio s, v t ∂ν) ∂ν) +
      (∫ q, normal q (∫ t in Iio (κ q), v t ∂ν) ∂μ) =
      ∫ t, (lambda + (∫ s in Ioi t, ell s ∂ν) +
        ∫ q in {q | t < κ q}, normal q ∂μ) (v t) ∂ν := by
  have hi := lambda.integrable_comp hv
  have hl := integrable_order_tail_apply hell hv
  have hn := integrable_indexed_tail_apply κ hκ hnormal hv
  simp only [add_apply]
  have ha := integral_add (hi.add hl) hn
  have hb := integral_add hi hl
  simp only [Pi.add_apply] at ha hb
  rw [ha, hb, lambda.integral_comp_comm hv, integral_order_tail_pairing hell hv,
    integral_indexed_tail_pairing κ hκ hnormal hv]

section IndexedTails

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [SFinite μ] [SFinite ν]
  [SecondCountableTopology τ] [MeasurableSpace τ] [BorelSpace τ] in
/-- Exact indexed measure increments use the time projection and the interval `(a,b]`. -/
theorem indexed_tail_sub (κ : Ω → τ) (hκ : Continuous κ)
    {w : Ω → F} (hw : Integrable w μ) {a b : τ} (hab : a ≤ b) :
    (∫ q in {q | a < κ q}, w q ∂μ) - (∫ q in {q | b < κ q}, w q ∂μ) =
      ∫ q in {q | a < κ q ∧ κ q ≤ b}, w q ∂μ := by
  have hu : {q | a < κ q ∧ κ q ≤ b} ∪ {q | b < κ q} = {q | a < κ q} := by
    ext q
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hab.trans_lt h
    · intro h
      exact (le_or_gt (κ q) b).elim (fun hb ↦ Or.inl ⟨h, hb⟩) Or.inr
  have hd : Disjoint {q | a < κ q ∧ κ q ≤ b} {q | b < κ q} :=
    disjoint_left.mpr (fun _ hs ht ↦ (not_lt_of_ge hs.2) ht)
  have hs : MeasurableSet {q | b < κ q} :=
    (isOpen_lt continuous_const hκ).measurableSet
  have he := setIntegral_union hd hs hw.integrableOn hw.integrableOn
  rw [hu] at he
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [SFinite μ] [SFinite ν]
  [SecondCountableTopology τ] [MeasurableSpace τ] [BorelSpace τ] in
/-- Integrability derives BV for vector-valued indexed tails; no density or AC is required. -/
theorem boundedVariation_indexed_tail (κ : Ω → τ) (hκ : Continuous κ)
    {w : Ω → F} (hw : Integrable w μ) :
    BoundedVariationOn (fun t ↦ ∫ q in {q | t < κ q}, w q ∂μ) univ := by
  let f : τ → ℝ := fun t ↦ ∫ q in {q | t < κ q}, ‖w q‖ ∂μ
  have hbound (t : τ) : 0 ≤ f t ∧ f t ≤ ∫ q, ‖w q‖ ∂μ :=
    ⟨integral_nonneg (fun _ ↦ norm_nonneg _),
      setIntegral_le_integral hw.norm (Eventually.of_forall (fun _ ↦ norm_nonneg _))⟩
  have hm : Monotone (fun t ↦ -f t) := by
    intro a b hab
    have he := indexed_tail_sub κ hκ hw.norm hab
    have hn : 0 ≤ ∫ q in {q | a < κ q ∧ κ q ≤ b}, ‖w q‖ ∂μ :=
      integral_nonneg (fun _ ↦ norm_nonneg _)
    change -(∫ q in {q | a < κ q}, ‖w q‖ ∂μ) ≤
      -(∫ q in {q | b < κ q}, ‖w q‖ ∂μ)
    linarith
  have hf : BoundedVariationOn f univ := by
    have hv := (hm.monotoneOn univ).boundedVariationOn
      (C := ∫ q, ‖w q‖ ∂μ) (fun t _ ↦ by
        rw [abs_neg, abs_of_nonneg (hbound t).1]
        exact (hbound t).2)
    simpa only [Function.comp_def, neg_neg] using
      (isometry_neg (G := ℝ)).lipschitzWith.comp_boundedVariationOn hv
  have hd {a b : τ} (hab : a ≤ b) :
      dist (∫ q in {q | a < κ q}, w q ∂μ) (∫ q in {q | b < κ q}, w q ∂μ) ≤
        dist (f a) (f b) := by
    rw [dist_eq_norm, indexed_tail_sub κ hκ hw hab]
    change ‖∫ q in {q | a < κ q ∧ κ q ≤ b}, w q ∂μ‖ ≤
      |(∫ q in {q | a < κ q}, ‖w q‖ ∂μ) - (∫ q in {q | b < κ q}, ‖w q‖ ∂μ)|
    rw [indexed_tail_sub κ hκ hw.norm hab,
      abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
    exact norm_integral_le_integral_norm _
  have he : eVariationOn (fun t ↦ ∫ q in {q | t < κ q}, w q ∂μ) univ ≤
      eVariationOn f univ := by
    unfold eVariationOn
    apply iSup_le
    intro p
    apply le_iSup_of_le p
    apply Finset.sum_le_sum
    intro i hi
    rw [edist_dist, edist_dist]
    apply ENNReal.ofReal_le_ofReal
    simpa only [dist_comm] using hd (p.2.2.1 (Nat.le_succ i))
  exact ne_top_of_le_ne_top hf he

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [SFinite μ] [SFinite ν]
  [SecondCountableTopology τ] [MeasurableSpace τ] [BorelSpace τ] in
/-- Indexed open tails are right-continuous, including at atoms. -/
theorem continuousWithinAt_indexed_tail [FirstCountableTopology τ] (κ : Ω → τ) (hκ : Continuous κ)
    {w : Ω → F} (hw : Integrable w μ) (t : τ) :
    ContinuousWithinAt (fun r ↦ ∫ q in {q | r < κ q}, w q ∂μ) (Ici t) t := by
  have hopen (r : τ) : MeasurableSet {q | r < κ q} :=
    (isOpen_lt continuous_const hκ).measurableSet
  have hm : ∀ᶠ r in 𝓝[Ici t] t, AEStronglyMeasurable (({q | r < κ q}).indicator w) μ :=
    Eventually.of_forall (fun r ↦ hw.aestronglyMeasurable.indicator (hopen r))
  have hb : ∀ᶠ r in 𝓝[Ici t] t, ∀ᵐ s ∂μ, ‖({q | r < κ q}).indicator w s‖ ≤ ‖w s‖ := by
    apply Eventually.of_forall
    intro r
    apply Eventually.of_forall
    intro s
    by_cases h : r < κ s <;> simp [Set.indicator, h, norm_nonneg]
  have hl : ∀ᵐ s ∂μ, Tendsto (fun r ↦ ({q | r < κ q}).indicator w s)
      (𝓝[Ici t] t) (𝓝 (({q | t < κ q}).indicator w s)) := by
    apply Eventually.of_forall
    intro s
    by_cases h : t < κ s
    · have he : ∀ᶠ r in 𝓝[Ici t] t, r < κ s :=
        (eventually_lt_nhds h).filter_mono nhdsWithin_le_nhds
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with r hr
      simp [Set.indicator, h, hr]
    · have he : ∀ᶠ r in 𝓝[Ici t] t, t ≤ r := self_mem_nhdsWithin
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with r hr
      have hs : ¬ r < κ s := not_lt.mpr ((not_lt.mp h).trans hr)
      simp [Set.indicator, h, hs]
  have hi := tendsto_integral_filter_of_dominated_convergence (fun s ↦ ‖w s‖) hm hb
    hw.norm hl
  change Tendsto (fun r ↦ ∫ s in {q | r < κ q}, w s ∂μ) _ (𝓝 (∫ s in {q | t < κ q}, w s ∂μ))
  simpa only [integral_indicator (hopen _)] using hi


omit [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [SFinite μ] [SFinite ν]
  [SecondCountableTopology τ] [MeasurableSpace τ] [BorelSpace τ] in
/-- The indexed left trace retains the full time fiber, including all constraint atoms. -/
theorem tendsto_indexed_tail_left [FirstCountableTopology τ] (κ : Ω → τ) (hκ : Continuous κ)
    {w : Ω → F} (hw : Integrable w μ) (t : τ) :
    Tendsto (fun r ↦ ∫ q in {q | r < κ q}, w q ∂μ) (𝓝[<] t)
      (𝓝 (∫ q in {q | t ≤ κ q}, w q ∂μ)) := by
  have hopen (r : τ) : MeasurableSet {q | r < κ q} :=
    (isOpen_lt continuous_const hκ).measurableSet
  have hclosed (r : τ) : MeasurableSet {q | r ≤ κ q} :=
    (isClosed_le continuous_const hκ).measurableSet
  have hm : ∀ᶠ r in 𝓝[<] t, AEStronglyMeasurable (({q | r < κ q}).indicator w) μ :=
    Eventually.of_forall (fun r ↦ hw.aestronglyMeasurable.indicator (hopen r))
  have hb : ∀ᶠ r in 𝓝[<] t, ∀ᵐ s ∂μ, ‖({q | r < κ q}).indicator w s‖ ≤ ‖w s‖ := by
    apply Eventually.of_forall
    intro r
    apply Eventually.of_forall
    intro s
    by_cases h : r < κ s <;> simp [Set.indicator, h, norm_nonneg]
  have hl : ∀ᵐ s ∂μ, Tendsto (fun r ↦ ({q | r < κ q}).indicator w s)
      (𝓝[<] t) (𝓝 (({q | t ≤ κ q}).indicator w s)) := by
    apply Eventually.of_forall
    intro s
    by_cases h : t ≤ κ s
    · have he : ∀ᶠ r in 𝓝[<] t, r < t := self_mem_nhdsWithin
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with r hr
      have hs := hr.trans_le h
      simp [Set.indicator, h, hs]
    · have he : ∀ᶠ r in 𝓝[<] t, κ s < r :=
        (eventually_gt_nhds (not_le.mp h)).filter_mono nhdsWithin_le_nhds
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with r hr
      have hs : ¬ r < κ s := not_lt.mpr hr.le
      simp [Set.indicator, h, hs]
  have hi := tendsto_integral_filter_of_dominated_convergence (fun s ↦ ‖w s‖) hm hb
    hw.norm hl
  change Tendsto (fun r ↦ ∫ s in {q | r < κ q}, w s ∂μ) _ (𝓝 (∫ s in {q | t ≤ κ q}, w s ∂μ))
  simpa only [integral_indicator (hopen _), integral_indicator (hclosed _)] using hi


omit [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [SFinite μ] [SFinite ν]
  [SecondCountableTopology τ] [MeasurableSpace τ] [BorelSpace τ] in
/-- The left and right representatives differ by the entire time-fiber measure. -/
theorem indexed_closed_tail_sub_open (κ : Ω → τ) (hκ : Continuous κ)
    {w : Ω → F} (hw : Integrable w μ) (t : τ) :
    (∫ q in {q | t ≤ κ q}, w q ∂μ) - (∫ q in {q | t < κ q}, w q ∂μ) =
      ∫ q in {q | κ q = t}, w q ∂μ := by
  have hu : {q | κ q = t} ∪ {q | t < κ q} = {q | t ≤ κ q} := by
    ext q
    constructor
    · rintro (h | h)
      · exact h.symm.le
      · exact h.le
    · intro h
      exact (eq_or_lt_of_le h).imp Eq.symm id
  have hd : Disjoint {q | κ q = t} {q | t < κ q} :=
    disjoint_left.mpr (fun q hs ht ↦ by
      change κ q = t at hs
      change t < κ q at ht
      rw [hs] at ht
      exact lt_irrefl _ ht)
  have hs : MeasurableSet {q | t < κ q} :=
    (isOpen_lt continuous_const hκ).measurableSet
  have he := setIntegral_union hd hs hw.integrableOn hw.integrableOn
  rw [hu] at he
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [SFinite ν] in
/-- A finite time marginal makes every integrable indexed vector tail integrable in time. -/
theorem integrable_indexed_tail [IsFiniteMeasure ν] (κ : Ω → τ) (hκ : Continuous κ)
    {w : Ω → F} (hw : Integrable w μ) :
    Integrable (fun t ↦ ∫ q in {q | t < κ q}, w q ∂μ) ν := by
  classical
  have hs : MeasurableSet {z : Ω × τ | z.2 < κ z.1} :=
    (isOpen_lt continuous_snd (hκ.comp continuous_fst)).measurableSet
  have hi := ((hw.comp_fst ν).indicator hs).integral_prod_right
  apply hi.congr
  apply Eventually.of_forall
  intro t
  dsimp only
  have hs' : MeasurableSet {q | t < κ q} :=
    (isOpen_lt continuous_const hκ).measurableSet
  rw [← integral_indicator hs']
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ ↦ by simp [Set.indicator])

end IndexedTails
end MeasureAdjoint
