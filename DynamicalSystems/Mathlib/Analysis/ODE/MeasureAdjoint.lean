/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module
public import DynamicalSystems.Mathlib.MeasureTheory.VectorMeasureTail
public import DynamicalSystems.Mathlib.Analysis.ODE.StateTransition
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-!
# Constructed measure adjoints and their Fubini pairing

A terminal covector plus a covector-valued measure tail is a BV adjoint for an
integrator. Its interval law, right continuity and atom jumps are conclusions.
The Fubini lemma derives its pairing against actual integral state variations.
-/
@[expose] public section
open Set MeasureTheory Filter Function
open scoped Topology
namespace MeasureAdjoint
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
/-- Construct the adjoint from a terminal covector and an integrable measure density. -/
noncomputable def costate (μ : Measure ℝ) (w : ℝ → X →L[ℝ] ℝ)
    (lambda : X →L[ℝ] ℝ) (t : ℝ) : X →L[ℝ] ℝ :=
  lambda + openIntegralTail μ w t
variable {μ : Measure ℝ} {w : ℝ → X →L[ℝ] ℝ} (lambda : X →L[ℝ] ℝ)
omit [CompleteSpace X] in
theorem increment (hw : Integrable w μ) {a b : ℝ} (hab : a ≤ b) :
    costate μ w lambda b - costate μ w lambda a = -∫ s in Ioc a b, w s ∂μ := by
  simpa [costate, neg_sub] using congrArg Neg.neg (openIntegralTail_sub hw hab)
omit [CompleteSpace X] in
theorem boundedVariation (hw : Integrable w μ) :
    BoundedVariationOn (costate μ w lambda) univ := by
  have hi : Isometry (fun q : X →L[ℝ] ℝ ↦ lambda + q) :=
    Isometry.of_dist_eq (fun _ _ ↦ dist_add_left _ _ _)
  exact hi.lipschitzWith.comp_boundedVariationOn (boundedVariationOn_openIntegralTail hw)
omit [CompleteSpace X] in
theorem right_continuous (hw : Integrable w μ) (t : ℝ) :
    ContinuousWithinAt (costate μ w lambda) (Ici t) t :=
  continuousWithinAt_const.add (continuousWithinAt_openIntegralTail hw t)
omit [CompleteSpace X] in
theorem left_trace (hw : Integrable w μ) (t : ℝ) :
    Function.leftLim (costate μ w lambda) t = lambda + closedIntegralTail μ w t := by
  apply leftLim_eq_of_tendsto
  exact tendsto_const_nhds.add (tendsto_openIntegralTail_left hw t)
omit [CompleteSpace X] in
/-- The exact jump is the negative atom, including at a terminal time. -/
theorem jump (hw : Integrable w μ) (t : ℝ) :
    costate μ w lambda t - Function.leftLim (costate μ w lambda) t =
      -(μ.real {t} • w t) := by
  rw [left_trace lambda hw t]
  simpa [costate, neg_sub] using
    congrArg Neg.neg (closedIntegralTail_sub_openIntegralTail hw t)

/-- Fubini derives the measure-tail pairing against the actual integral variation.
The measures may be singular; the variation is integrated with respect to `ν`. -/
theorem integral_order_tail_pairing {τ : Type*} [LinearOrder τ] [TopologicalSpace τ]
    [OrderTopology τ] [SecondCountableTopology τ] [MeasurableSpace τ] [BorelSpace τ]
    {μ ν : Measure τ} [SFinite μ] [SFinite ν]
    {w : τ → X →L[ℝ] ℝ} (hw : Integrable w μ) {v : τ → X} (hv : Integrable v ν) :
    (∫ s, w s (∫ t in Iio s, v t ∂ν) ∂μ) =
      ∫ t, (∫ s in Ioi t, w s ∂μ) (v t) ∂ν := by
  classical
  have hprod : Integrable (fun z : τ × τ ↦ w z.1 (v z.2)) (μ.prod ν) := by
    apply hw.op_fst_snd _ _ hv
    · exact continuous_fst.clm_apply continuous_snd
    · exact ⟨1, fun f x ↦ by simpa using f.le_opNorm x⟩
  have hset : MeasurableSet {z : τ × τ | z.2 < z.1} :=
    isOpen_lt continuous_snd continuous_fst |>.measurableSet
  have htriangle : Integrable (fun z ↦ if z.2 < z.1 then w z.1 (v z.2) else 0)
      (μ.prod ν) := by
    apply (hprod.indicator hset).congr
    exact Eventually.of_forall (fun _ ↦ by simp [Set.indicator])
  have hswap := integral_integral_swap (f := fun s t ↦
    if t < s then w s (v t) else 0) htriangle
  have hl (s : τ) : w s (∫ t in Iio s, v t ∂ν) =
      ∫ t, (if t < s then w s (v t) else 0) ∂ν := by
    rw [← (w s).integral_comp_comm hv.integrableOn, ← integral_indicator measurableSet_Iio]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ ↦ by simp [Set.indicator])
  have hr (t : τ) : (∫ s in Ioi t, w s ∂μ) (v t) =
      ∫ s, (if t < s then w s (v t) else 0) ∂μ := by
    rw [ContinuousLinearMap.integral_apply hw.integrableOn,
      ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ ↦ by simp [Set.indicator])
  simp_rw [hl, hr]
  exact hswap

theorem integral_tail_pairing {ν : Measure ℝ} [SFinite μ] [SFinite ν]
    (hw : Integrable w μ) {v : ℝ → X} (hv : Integrable v ν) :
    (∫ s, w s (∫ t in Iio s, v t ∂ν) ∂μ) =
      ∫ t, openIntegralTail μ w t (v t) ∂ν := by
  change (∫ s, w s (∫ t in Iio s, v t ∂ν) ∂μ) =
    ∫ t, (∫ s in Ioi t, w s ∂μ) (v t) ∂ν
  exact integral_order_tail_pairing hw hv

omit [CompleteSpace X] in
/-- The tail paired with any integrable control is integrable, by the product estimate. -/
theorem integrable_order_tail_apply {τ : Type*} [LinearOrder τ] [TopologicalSpace τ]
    [OrderTopology τ] [SecondCountableTopology τ] [MeasurableSpace τ] [BorelSpace τ]
    {μ ν : Measure τ} [SFinite μ] [SFinite ν]
    {w : τ → X →L[ℝ] ℝ} (hw : Integrable w μ) {v : τ → X} (hv : Integrable v ν) :
    Integrable (fun t ↦ (∫ s in Ioi t, w s ∂μ) (v t)) ν := by
  have hprod : Integrable (fun z : τ × τ ↦ w z.1 (v z.2)) (μ.prod ν) := by
    apply hw.op_fst_snd _ _ hv
    · exact continuous_fst.clm_apply continuous_snd
    · exact ⟨1, fun f x ↦ by simpa using f.le_opNorm x⟩
  have hset : MeasurableSet {z : τ × τ | z.2 < z.1} :=
    (isOpen_lt continuous_snd continuous_fst).measurableSet
  have hp := (hprod.indicator hset).integral_prod_right
  apply hp.congr
  apply Eventually.of_forall
  intro t
  dsimp only
  rw [ContinuousLinearMap.integral_apply hw.integrableOn,
    ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun s ↦ by simp [Set.indicator])

/-- The strict prefix paired with any integrable control is integrable, by the product estimate. -/
theorem integrable_order_prefix_apply {τ : Type*} [LinearOrder τ] [TopologicalSpace τ]
    [OrderTopology τ] [SecondCountableTopology τ] [MeasurableSpace τ] [BorelSpace τ]
    {μ ν : Measure τ} [SFinite μ] [SFinite ν]
    {w : τ → X →L[ℝ] ℝ} (hw : Integrable w μ) {v : τ → X} (hv : Integrable v ν) :
    Integrable (fun s ↦ w s (∫ t in Iio s, v t ∂ν)) μ := by
  have hprod : Integrable (fun z : τ × τ ↦ w z.1 (v z.2)) (μ.prod ν) := by
    apply hw.op_fst_snd _ _ hv
    · exact continuous_fst.clm_apply continuous_snd
    · exact ⟨1, fun f x ↦ by simpa using f.le_opNorm x⟩
  have hset : MeasurableSet {z : τ × τ | z.2 < z.1} :=
    (isOpen_lt continuous_snd continuous_fst).measurableSet
  have hp := (hprod.indicator hset).integral_prod_left
  apply hp.congr
  apply Eventually.of_forall
  intro s
  dsimp only
  rw [← (w s).integral_comp_comm hv.integrableOn,
    ← integral_indicator measurableSet_Iio]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t ↦ by simp [Set.indicator])

/-- Ordered vector tails have exact `(a,b]` interval increments. -/
theorem order_tail_sub {τ F : Type*} [LinearOrder τ] [TopologicalSpace τ]
    [OrderTopology τ] [MeasurableSpace τ] [BorelSpace τ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure τ} {w : τ → F} (hw : Integrable w μ) {a b : τ} (hab : a ≤ b) :
    (∫ s in Ioi a, w s ∂μ) - (∫ s in Ioi b, w s ∂μ) = ∫ s in Ioc a b, w s ∂μ := by
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
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he)

/-- The closed-minus-open order-tail convention differs by exactly the actual atom. -/
theorem order_closed_tail_sub_open {τ F : Type*} [LinearOrder τ] [TopologicalSpace τ]
    [OrderTopology τ] [MeasurableSpace τ] [BorelSpace τ] [MeasurableSingletonClass τ]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure τ} {w : τ → F} (hw : Integrable w μ) (t : τ) :
    (∫ s in Ici t, w s ∂μ) - (∫ s in Ioi t, w s ∂μ) = μ.real {t} • w t := by
  have hu : ({t} : Set τ) ∪ Ioi t = Ici t := by
    ext s
    simp only [mem_union, mem_singleton_iff, mem_Ioi, mem_Ici]
    constructor
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.le
    · intro h
      exact (eq_or_lt_of_le h).imp Eq.symm id
  have hd : Disjoint ({t} : Set τ) (Ioi t) := by
    apply disjoint_left.mpr
    intro s hs ht
    simp only [mem_singleton_iff] at hs
    subst s
    exact lt_irrefl _ ht
  have he := setIntegral_union hd measurableSet_Ioi hw.integrableOn hw.integrableOn
  rw [hu, integral_singleton] at he
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he)

/-- BV on a compact horizon subtype is derived directly from an integrable measure density. -/
theorem boundedVariation_order_tail {τ F : Type*} [LinearOrder τ] [TopologicalSpace τ]
    [OrderTopology τ] [MeasurableSpace τ] [BorelSpace τ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure τ} {w : τ → F} (hw : Integrable w μ) :
    BoundedVariationOn (fun t ↦ ∫ s in Ioi t, w s ∂μ) univ := by
  let q : τ → ℝ := fun t ↦ ∫ s in Ioi t, ‖w s‖ ∂μ
  have hbound (t : τ) : 0 ≤ q t ∧ q t ≤ ∫ s, ‖w s‖ ∂μ :=
    ⟨integral_nonneg (fun _ ↦ norm_nonneg _),
      setIntegral_le_integral hw.norm (Eventually.of_forall (fun _ ↦ norm_nonneg _))⟩
  have hm : Monotone (fun t ↦ -q t) := by
    intro a b hab
    have he := order_tail_sub hw.norm hab
    have hn : 0 ≤ ∫ s in Ioc a b, ‖w s‖ ∂μ := integral_nonneg (fun _ ↦ norm_nonneg _)
    change -(∫ s in Ioi a, ‖w s‖ ∂μ) ≤ -(∫ s in Ioi b, ‖w s‖ ∂μ)
    linarith
  have hq : BoundedVariationOn q univ := by
    have hv := (hm.monotoneOn univ).boundedVariationOn
      (C := ∫ s, ‖w s‖ ∂μ) (fun t _ ↦ by
        rw [abs_neg, abs_of_nonneg (hbound t).1]
        exact (hbound t).2)
    simpa only [Function.comp_def, neg_neg] using
      (isometry_neg (G := ℝ)).lipschitzWith.comp_boundedVariationOn hv
  have hd {a b : τ} (hab : a ≤ b) :
      dist (∫ s in Ioi a, w s ∂μ) (∫ s in Ioi b, w s ∂μ) ≤ dist (q a) (q b) := by
    rw [dist_eq_norm, order_tail_sub hw hab]
    change ‖∫ s in Ioc a b, w s ∂μ‖ ≤ |(∫ s in Ioi a, ‖w s‖ ∂μ) -
      (∫ s in Ioi b, ‖w s‖ ∂μ)|
    rw [order_tail_sub hw.norm hab, abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
    exact norm_integral_le_integral_norm _
  have he : eVariationOn (fun t ↦ ∫ s in Ioi t, w s ∂μ) univ ≤ eVariationOn q univ := by
    unfold eVariationOn
    apply iSup_le
    intro p
    apply le_iSup_of_le p
    apply Finset.sum_le_sum
    intro i hi
    rw [edist_dist, edist_dist]
    apply ENNReal.ofReal_le_ofReal
    simpa only [dist_comm] using hd (p.2.2.1 (Nat.le_succ i))
  exact ne_top_of_le_ne_top hq he

/-- The constructed open tail is right-continuous, even at atoms. -/
theorem continuousWithinAt_order_tail {τ F : Type*} [LinearOrder τ] [TopologicalSpace τ]
    [OrderTopology τ] [FirstCountableTopology τ] [MeasurableSpace τ] [BorelSpace τ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure τ} {w : τ → F} (hw : Integrable w μ) (t : τ) :
    ContinuousWithinAt (fun t ↦ ∫ s in Ioi t, w s ∂μ) (Ici t) t := by
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

/-- The left trace of the open tail is the closed tail. -/
theorem tendsto_order_tail_left {τ F : Type*} [LinearOrder τ] [TopologicalSpace τ]
    [OrderTopology τ] [FirstCountableTopology τ] [MeasurableSpace τ] [BorelSpace τ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure τ} {w : τ → F} (hw : Integrable w μ) (t : τ) :
    Tendsto (fun t ↦ ∫ s in Ioi t, w s ∂μ) (𝓝[<] t) (𝓝 (∫ s in Ici t, w s ∂μ)) := by
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

/-- An order tail of an integrable density is itself integrable for any finite time measure. -/
theorem integrable_order_tail {τ F : Type*} [LinearOrder τ] [TopologicalSpace τ]
    [OrderTopology τ] [SecondCountableTopology τ] [MeasurableSpace τ] [BorelSpace τ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ ν : Measure τ} [SFinite μ] [IsFiniteMeasure ν]
    {w : τ → F} (hw : Integrable w μ) :
    Integrable (fun t ↦ ∫ s in Ioi t, w s ∂μ) ν := by
  classical
  have hset : MeasurableSet {z : τ × τ | z.2 < z.1} :=
    (isOpen_lt continuous_snd continuous_fst).measurableSet
  have hp := ((hw.comp_fst ν).indicator hset).integral_prod_right
  apply hp.congr
  apply Eventually.of_forall
  intro t
  dsimp only
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun s ↦ by simp [Set.indicator])

omit [CompleteSpace X] in
/-- The terminal value excludes a terminal atom. -/
theorem terminal_value (μ : Measure ℝ) (w : ℝ → X →L[ℝ] ℝ) (T : ℝ) :
    costate (μ.restrict (Iic T)) w lambda T = lambda := by
  simp [costate, openIntegralTail_terminal]

omit [CompleteSpace X] in
/-- The left terminal trace retains the terminal atom. -/
theorem terminal_left_trace (T : ℝ) (hw : Integrable w (μ.restrict (Iic T))) :
    Function.leftLim (costate (μ.restrict (Iic T)) w lambda) T =
      lambda + μ.real {T} • w T := by
  have hj := jump lambda hw T
  rw [terminal_value lambda] at hj
  have he : (μ.restrict (Iic T)).real {T} = μ.real {T} := by
    unfold Measure.real
    rw [Measure.restrict_apply (measurableSet_singleton T)]
    simp
  rw [he] at hj
  exact eq_add_of_sub_eq' (by simpa using congrArg Neg.neg hj)
/-- Propagate a terminal covector and transformed measure density through the actual transition.
`w s` is the density in the fixed reference frame, such as `n s ∘ Phi s 0`. -/
noncomputable def propagatedCostate (Phi : ℝ → ℝ → X →L[ℝ] X)
    (μ : Measure ℝ) (w : ℝ → X →L[ℝ] ℝ) (lambda : X →L[ℝ] ℝ) (t : ℝ) :
    X →L[ℝ] ℝ := (costate μ w lambda t).comp (Phi 0 t)

omit [CompleteSpace X] in
/-- Continuous coefficients make the backward propagator BV on each compact interval. -/
theorem transition_boundedVariation {A : ℝ → X →L[ℝ] X}
    {Phi : ℝ → ℝ → X →L[ℝ] X} (hPhi : IsStateTransition A Phi)
    (hA : Continuous A) (a b : ℝ) :
    BoundedVariationOn (fun t ↦ Phi 0 t) (Icc a b) := by
  have hp : Continuous (fun t ↦ Phi 0 t) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_id)
  have hd : Continuous (fun t ↦ -((Phi 0 t).comp (A t))) := (hp.clm_comp hA).neg
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hd.continuousOn
  have hl : LipschitzOnWith (max C 0).toNNReal (fun t ↦ Phi 0 t) (Icc a b) := by
    apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht ↦ (hPhi.backward 0 t).hasDerivWithinAt)
    intro t ht
    apply NNReal.coe_le_coe.mp
    change ‖-((Phi 0 t).comp (A t))‖ ≤ ↑((max C 0).toNNReal)
    rw [Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hC t ht).trans (le_max_left _ _)
  simpa only [Function.comp_def, id_eq] using
    hl.comp_boundedVariationOn (fun _ ht ↦ ht) (BoundedVariationOn.id_Icc a b)

omit [CompleteSpace X] in
/-- BV of a propagated costate is derived from integrability and continuous coefficients. -/
theorem propagated_boundedVariation {A : ℝ → X →L[ℝ] X}
    {Phi : ℝ → ℝ → X →L[ℝ] X} (hPhi : IsStateTransition A Phi)
    (hA : Continuous A) (hw : Integrable w μ) (a b : ℝ) :
    BoundedVariationOn (propagatedCostate Phi μ w lambda) (Icc a b) := by
  exact ((boundedVariation lambda hw).mono (subset_univ _)).bilinear_comp
    (transition_boundedVariation hPhi hA a b) (ContinuousLinearMap.compL ℝ X X ℝ)
omit [CompleteSpace X] in
/-- The constructed propagated costate has the exact mild adjoint balance. -/
theorem propagated_balance {A : ℝ → X →L[ℝ] X}
    {Phi : ℝ → ℝ → X →L[ℝ] X} (hPhi : IsStateTransition A Phi)
    (hw : Integrable w μ) {a b : ℝ} (hab : a ≤ b) :
    propagatedCostate Phi μ w lambda a =
      (propagatedCostate Phi μ w lambda b).comp (Phi b a) +
        (∫ s in Ioc a b, w s ∂μ).comp (Phi 0 a) := by
  have he : costate μ w lambda a =
      costate μ w lambda b + ∫ s in Ioc a b, w s ∂μ := by
    have hs := sub_eq_iff_eq_add.mp (openIntegralTail_sub hw hab)
    simp only [costate]
    rw [hs]
    abel
  unfold propagatedCostate
  rw [he, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc, hPhi.cocycle]

omit [CompleteSpace X] in
/-- Propagation preserves the right-continuous atom convention. -/
theorem propagated_right_continuous {A : ℝ → X →L[ℝ] X}
    {Phi : ℝ → ℝ → X →L[ℝ] X} (hPhi : IsStateTransition A Phi)
    (hw : Integrable w μ) (t : ℝ) :
    ContinuousWithinAt (propagatedCostate Phi μ w lambda) (Ici t) t :=
  (right_continuous lambda hw t).clm_comp (hPhi.backward 0 t).continuousAt.continuousWithinAt

omit [CompleteSpace X] in
/-- The propagated left trace retains the measure atom. -/
theorem propagated_left_trace {A : ℝ → X →L[ℝ] X}
    {Phi : ℝ → ℝ → X →L[ℝ] X} (hPhi : IsStateTransition A Phi)
    (hw : Integrable w μ) (t : ℝ) :
    Function.leftLim (propagatedCostate Phi μ w lambda) t =
      (lambda + closedIntegralTail μ w t).comp (Phi 0 t) := by
  apply leftLim_eq_of_tendsto
  have hl := (tendsto_const_nhds (x := lambda)).add (tendsto_openIntegralTail_left hw t)
  have hp := (hPhi.backward 0 t).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Iio t))
  exact ((continuous_fst.clm_comp continuous_snd).tendsto _).comp (hl.prodMk_nhds hp)

omit [CompleteSpace X] in
/-- The propagated jump is the correctly propagated negative atom. -/
theorem propagated_jump {A : ℝ → X →L[ℝ] X}
    {Phi : ℝ → ℝ → X →L[ℝ] X} (hPhi : IsStateTransition A Phi)
    (hw : Integrable w μ) (t : ℝ) :
    propagatedCostate Phi μ w lambda t -
      Function.leftLim (propagatedCostate Phi μ w lambda) t =
        -(μ.real {t} • (w t).comp (Phi 0 t)) := by
  rw [propagated_left_trace lambda hPhi hw t, propagatedCostate,
    ← ContinuousLinearMap.sub_comp]
  have he := closedIntegralTail_sub_openIntegralTail hw t
  have hz : lambda + openIntegralTail μ w t - (lambda + closedIntegralTail μ w t) =
      -(μ.real {t} • w t) := by
    simpa [neg_sub] using congrArg Neg.neg he
  change ((lambda + openIntegralTail μ w t - (lambda + closedIntegralTail μ w t)).comp
    (Phi 0 t)) = _
  rw [hz]
  simp
omit [CompleteSpace X] in
/-- The reference-frame construction is exactly the transition-weighted measure formula. -/
theorem propagated_formula {A : ℝ → X →L[ℝ] X}
    {Phi : ℝ → ℝ → X →L[ℝ] X} (hPhi : IsStateTransition A Phi)
    (n : ℝ → X →L[ℝ] ℝ) (hw : Integrable (fun s ↦ (n s).comp (Phi s 0)) μ)
    (terminal : X →L[ℝ] ℝ) (T t : ℝ) :
    propagatedCostate Phi μ (fun s ↦ (n s).comp (Phi s 0))
      (terminal.comp (Phi T 0)) t =
        terminal.comp (Phi T t) + ∫ s in Ioi t, (n s).comp (Phi s t) ∂μ := by
  unfold propagatedCostate costate openIntegralTail
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc, hPhi.cocycle]
  congr 1
  have hi := ((ContinuousLinearMap.compL ℝ X X ℝ).flip (Phi 0 t)).integral_comp_comm
    (hw.integrableOn (s := Ioi t))
  change (∫ s in Ioi t, ((n s).comp (Phi s 0)).comp (Phi 0 t) ∂μ) =
    (∫ s in Ioi t, (n s).comp (Phi s 0) ∂μ).comp (Phi 0 t) at hi
  rw [← hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro s
  change ((n s).comp (Phi s 0)).comp (Phi 0 t) = (n s).comp (Phi s t)
  rw [ContinuousLinearMap.comp_assoc, hPhi.cocycle]
end MeasureAdjoint
