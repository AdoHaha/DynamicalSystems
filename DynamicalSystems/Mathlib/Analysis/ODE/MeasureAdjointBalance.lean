/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.MeasureAdjoint
public import DynamicalSystems.Mathlib.Analysis.ODE.MeasureAdjointPairing
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Additive interval balances for constructed measure adjoints

The propagated costate is a smooth backward transition multiplied by an actual measure tail.
A local Fubini and fundamental-theorem argument derives its additive adjoint law, retaining
atoms and singular continuous measure parts without assuming a costate derivative or BV
certificate.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology

namespace MeasureAdjoint

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The strict prefix of a continuous derivative restricted to a compact interval. -/
theorem integral_prefix_deriv (v v' : ℝ → X) (hv' : Continuous v')
    (hd : ∀ t, HasDerivAt v (v' t) t) {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    (∫ t in Iio s, v' t ∂volume.restrict (Ioc a b)) =
      if s ≤ a then 0 else if s ≤ b then v s - v a else v b - v a := by
  rw [Measure.restrict_restrict measurableSet_Iio]
  by_cases hsa : s ≤ a
  · have he : Iio s ∩ Ioc a b = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_empty_iff_false, iff_false]
      rintro ⟨hts, hat, _⟩
      exact (not_lt_of_ge (hsa.trans hat.le)) hts
    rw [he]
    simp [hsa]
  · have has : a < s := lt_of_not_ge hsa
    by_cases hsb : s ≤ b
    · have he : Iio s ∩ Ioc a b = Ioo a s := by
        ext t
        simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
        constructor
        · rintro ⟨hts, hat, _⟩
          exact ⟨hat, hts⟩
        · rintro ⟨hat, hts⟩
          exact ⟨hts, hat, hts.le.trans hsb⟩
      rw [he, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le has.le]
      simp only [hsa, hsb, ite_false, ite_true]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
        (hv'.intervalIntegrable _ _)
    · have hbs : b < s := lt_of_not_ge hsb
      have he : Iio s ∩ Ioc a b = Ioc a b :=
        inter_eq_right.mpr (fun t ht ↦ ht.2.trans_lt hbs)
      rw [he, ← intervalIntegral.integral_of_le hab]
      simp only [hsa, hsb, ite_false]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
        (hv'.intervalIntegrable _ _)

/-- Local smooth variation pairs with an integrable measure tail by genuine Fubini. -/
theorem integral_tail_deriv_pairing {μ : Measure ℝ} [SFinite μ]
    {w : ℝ → X →L[ℝ] ℝ} (hw : Integrable w μ)
    (v v' : ℝ → X) (hv' : Continuous v') (hd : ∀ t, HasDerivAt v (v' t) t)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, openIntegralTail μ w t (v' t)) =
      (∫ s in Ioc a b, w s (v s - v a) ∂μ) +
        openIntegralTail μ w b (v b - v a) := by
  let ν := volume.restrict (Ioc a b)
  have hvi : Integrable v' ν := hv'.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hF := integral_order_tail_pairing hw hvi
  have hpi := integrable_order_prefix_apply hw hvi
  have hp (s : ℝ) := integral_prefix_deriv v v' hv' hd hab s
  have hi : IntegrableOn (fun s ↦ w s (v s - v a)) (Ioc a b) μ := by
    apply hpi.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    dsimp only [ν]
    rw [hp]
    simp [not_le.mpr hs.1, hs.2]
  have hconst : Integrable (fun s ↦ w s (v b - v a)) μ :=
    (ContinuousLinearMap.apply ℝ ℝ (v b - v a)).integrable_comp hw
  have he (s : ℝ) : w s (∫ t in Iio s, v' t ∂ν) =
      (Ioc a b).indicator (fun s ↦ w s (v s - v a)) s +
        (Ioi b).indicator (fun s ↦ w s (v b - v a)) s := by
    dsimp only [ν]
    rw [hp]
    by_cases hsa : s ≤ a
    · have hsb : s ≤ b := hsa.trans hab
      simp [hsa, hsb, not_lt.mpr hsa, not_lt.mpr hsb, Set.indicator]
    · by_cases hsb : s ≤ b
      · simp [hsa, hsb, lt_of_not_ge hsa, not_lt.mpr hsb, Set.indicator]
      · simp [hsa, hsb, lt_of_not_ge hsa, lt_of_not_ge hsb, Set.indicator]
  rw [intervalIntegral.integral_of_le hab]
  change (∫ t, (∫ s in Ioi t, w s ∂μ) (v' t) ∂ν) = _
  rw [← hF]
  simp_rw [he]
  rw [integral_add (hi.integrable_indicator measurableSet_Ioc)
    (hconst.integrableOn.integrable_indicator measurableSet_Ioi),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioi,
    ← ContinuousLinearMap.integral_apply hw.integrableOn]
  rfl

omit [CompleteSpace X] in
/-- An integrable covector density paired with a continuous vector path is locally integrable. -/
theorem integrableOn_density_apply {μ : Measure ℝ} {w : ℝ → X →L[ℝ] ℝ}
    (hw : Integrable w μ) {v : ℝ → X} (hv : Continuous v) (a b : ℝ) :
    IntegrableOn (fun s ↦ w s (v s)) (Ioc a b) μ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hv.continuousOn
  apply (hw.integrableOn.norm.mul_const C).mono'
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hw.integrableOn.aestronglyMeasurable.prodMk hv.aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (w s).le_opNorm (v s) |>.trans
      (mul_le_mul_of_nonneg_left (hC s (Ioc_subset_Icc_self hs)) (norm_nonneg _))

/-- Exact product-tail integration by parts derived locally from Fubini and the smooth FTC. -/
theorem costate_pairing_increment {μ : Measure ℝ} [SFinite μ]
    {w : ℝ → X →L[ℝ] ℝ} (hw : Integrable w μ) (lambda : X →L[ℝ] ℝ)
    (v v' : ℝ → X) (hv' : Continuous v') (hd : ∀ t, HasDerivAt v (v' t) t)
    {a b : ℝ} (hab : a ≤ b) :
    costate μ w lambda b (v b) - costate μ w lambda a (v a) =
      (∫ t in a..b, costate μ w lambda t (v' t)) -
        ∫ s in Ioc a b, w s (v s) ∂μ := by
  have hv : Continuous v :=
    (show Differentiable ℝ v from fun t ↦ (hd t).differentiableAt).continuous
  have hvi : Integrable v' (volume.restrict (Ioc a b)) :=
    hv'.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hti := integrable_order_tail_apply hw hvi
  have hli := lambda.integrable_comp hvi
  have hwi := integrableOn_density_apply hw hv a b
  have hc : Integrable (fun s ↦ w s (v a)) μ :=
    (ContinuousLinearMap.apply ℝ ℝ (v a)).integrable_comp hw
  have htail := integral_tail_deriv_pairing hw v v' hv' hd hab
  have hdiff : (∫ s in Ioc a b, w s (v s - v a) ∂μ) =
      (∫ s in Ioc a b, w s (v s) ∂μ) -
        (openIntegralTail μ w a - openIntegralTail μ w b) (v a) := by
    simp_rw [map_sub]
    rw [integral_sub hwi hc.integrableOn, openIntegralTail_sub hw hab,
      ContinuousLinearMap.integral_apply hw.integrableOn]
  have hl : (∫ t in a..b, lambda (v' t)) = lambda (v b - v a) := by
    rw [lambda.intervalIntegral_comp_comm (hv'.intervalIntegrable _ _)]
    congr 1
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
      (hv'.intervalIntegrable _ _)
  have hsplit : (∫ t in a..b, costate μ w lambda t (v' t)) =
      (∫ t in a..b, lambda (v' t)) +
        ∫ t in a..b, openIntegralTail μ w t (v' t) := by
    simp only [costate, add_apply]
    apply intervalIntegral.integral_add
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hli
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hti
  rw [hsplit, hl, htail, hdiff]
  simp only [costate, add_apply, map_sub, sub_apply]
  ring


omit [CompleteSpace X] in
/-- Composition with a continuous operator preserves local integrability of covectors. -/
theorem integrableOn_covector_comp {μ : Measure ℝ} {w : ℝ → X →L[ℝ] ℝ}
    (hw : Integrable w μ) {g : ℝ → X →L[ℝ] X} (hg : Continuous g) (a b : ℝ) :
    IntegrableOn (fun s ↦ (w s).comp (g s)) (Ioc a b) μ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  apply (hw.integrableOn.norm.mul_const C).mono'
  · exact (continuous_fst.clm_comp continuous_snd).comp_aestronglyMeasurable
      (hw.integrableOn.aestronglyMeasurable.prodMk hg.aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact ContinuousLinearMap.opNorm_comp_le (w s) (g s) |>.trans
      (mul_le_mul_of_nonneg_left (hC s (Ioc_subset_Icc_self hs)) (norm_nonneg _))

/-- Exact additive measure-adjoint balance for the constructed propagated costate.
The density `w` is expressed in the fixed reference frame; its physical density at `s`
is `w s ∘ Phi 0 s`. The open-tail convention retains every atom in `(a,b]`. -/
theorem propagated_increment {μ : Measure ℝ} [SFinite μ]
    {w : ℝ → X →L[ℝ] ℝ} (hw : Integrable w μ) (lambda : X →L[ℝ] ℝ)
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (hA : Continuous A) {a b : ℝ} (hab : a ≤ b) :
    propagatedCostate Phi μ w lambda b - propagatedCostate Phi μ w lambda a =
      -(∫ t in a..b, (propagatedCostate Phi μ w lambda t).comp (A t)) -
        ∫ s in Ioc a b, (w s).comp (Phi 0 s) ∂μ := by
  have hp : Continuous (fun t ↦ Phi 0 t) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_id)
  have hq : Integrable (costate μ w lambda) (volume.restrict (Ioc a b)) := by
    exact (integrable_const lambda).add (integrable_order_tail hw)
  have hi := integrableOn_covector_comp hq (hp.clm_comp hA) a b
  have hi' : IntegrableOn (fun t ↦ (propagatedCostate Phi μ w lambda t).comp (A t))
      (Ioc a b) volume := by
    simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc, inter_self,
      propagatedCostate, ContinuousLinearMap.comp_assoc] using hi
  have hn := integrableOn_covector_comp hw hp a b
  ext x
  have hd : ∀ t, HasDerivAt (fun s ↦ Phi 0 s x) (-((Phi 0 t).comp (A t)) x) t := by
    intro t
    simpa using (hPhi.backward 0 t).clm_apply (hasDerivAt_const t x)
  have he := costate_pairing_increment hw lambda (fun t ↦ Phi 0 t x)
    (fun t ↦ -((Phi 0 t).comp (A t)) x)
    ((hp.clm_comp hA).neg.clm_apply continuous_const) hd hab
  rw [intervalIntegral.integral_of_le hab] at he ⊢
  simp only [sub_apply, neg_apply]
  rw [ContinuousLinearMap.integral_apply hi', ContinuousLinearMap.integral_apply hn]
  simpa only [propagatedCostate, ContinuousLinearMap.comp_apply,
    neg_apply, map_neg, integral_neg] using he

/-- In physical coordinates the additive balance contains precisely the original normal
measure. No transition factor remains in the singular term. -/
theorem propagated_normal_increment {μ : Measure ℝ} [SFinite μ]
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (hA : Continuous A)
    (n : ℝ → X →L[ℝ] ℝ) (hw : Integrable (fun s ↦ (n s).comp (Phi s 0)) μ)
    (terminal : X →L[ℝ] ℝ) (T : ℝ) {a b : ℝ} (hab : a ≤ b) :
    let p := propagatedCostate Phi μ (fun s ↦ (n s).comp (Phi s 0))
      (terminal.comp (Phi T 0))
    p b - p a = -(∫ t in a..b, (p t).comp (A t)) - ∫ s in Ioc a b, n s ∂μ := by
  dsimp only
  convert propagated_increment hw (terminal.comp (Phi T 0)) hPhi hA hab using 1
  simp only [ContinuousLinearMap.comp_assoc, hPhi.cocycle, hPhi.diag,
    ContinuousLinearMap.comp_id]

/-- A running covector density and a constraint measure are constructed independently and
then added. This definition keeps the singular measure separate from Lebesgue density. -/
noncomputable def fullPropagatedCostate (Phi : ℝ → ℝ → X →L[ℝ] X)
    (μ : Measure ℝ) (n ell : ℝ → X →L[ℝ] ℝ) (terminal : X →L[ℝ] ℝ)
    (T : ℝ) (t : ℝ) : X →L[ℝ] ℝ :=
  propagatedCostate Phi μ (fun s ↦ (n s).comp (Phi s 0))
    (terminal.comp (Phi T 0)) t +
  propagatedCostate Phi (volume.restrict (Icc 0 T))
    (fun s ↦ (ell s).comp (Phi s 0)) 0 t

/-- Exact additive adjoint equation including both running density and singular constraints.
The horizon restriction appears only in the Lebesgue measure, while constraint atoms at
both interior points and the terminal point retain the `(a,b]` convention. -/
theorem fullPropagatedCostate_increment {μ : Measure ℝ} [SFinite μ]
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (hA : Continuous A)
    (n ell : ℝ → X →L[ℝ] ℝ)
    (hn : Integrable (fun s ↦ (n s).comp (Phi s 0)) μ)
    (terminal : X →L[ℝ] ℝ) (T : ℝ)
    (hell : Integrable (fun s ↦ (ell s).comp (Phi s 0)) (volume.restrict (Icc 0 T)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    let p := fullPropagatedCostate Phi μ n ell terminal T
    p b - p a = -(∫ t in a..b, (p t).comp (A t) + ell t) -
      ∫ s in Ioc a b, n s ∂μ := by
  let q := propagatedCostate Phi μ (fun s ↦ (n s).comp (Phi s 0))
    (terminal.comp (Phi T 0))
  let r := propagatedCostate Phi (volume.restrict (Icc 0 T))
    (fun s ↦ (ell s).comp (Phi s 0)) 0
  have hq := propagated_normal_increment hPhi hA n hn terminal T hab
  have hr := propagated_normal_increment hPhi hA ell hell 0 T hab
  have hr' : r b - r a = -(∫ t in a..b, (r t).comp (A t)) -
      ∫ s in a..b, ell s := by
    have hm : (∫ s in Ioc a b, ell s ∂volume.restrict (Icc 0 T)) =
        ∫ s in a..b, ell s := by
      rw [intervalIntegral.integral_of_le hab]
      congr 1
      rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr]
      exact fun s hs ↦ ⟨ha.trans hs.1.le, hs.2.trans hb⟩
    simpa only [r, ContinuousLinearMap.zero_comp, hm] using hr
  have hp : Continuous (fun t ↦ Phi 0 t) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_id)
  have hiq : IntegrableOn (fun t ↦ (q t).comp (A t)) (Ioc a b) volume := by
    have hc : Integrable (costate μ (fun s ↦ (n s).comp (Phi s 0))
        (terminal.comp (Phi T 0))) (volume.restrict (Ioc a b)) :=
      (integrable_const _).add (integrable_order_tail hn)
    simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc, inter_self,
      q, propagatedCostate, ContinuousLinearMap.comp_assoc] using
      integrableOn_covector_comp hc (hp.clm_comp hA) a b
  have hir : IntegrableOn (fun t ↦ (r t).comp (A t)) (Ioc a b) volume := by
    have hc : Integrable (costate (volume.restrict (Icc 0 T))
        (fun s ↦ (ell s).comp (Phi s 0)) 0) (volume.restrict (Ioc a b)) :=
      (integrable_const _).add (integrable_order_tail hell)
    simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc, inter_self,
      r, propagatedCostate, ContinuousLinearMap.comp_assoc] using
      integrableOn_covector_comp hc (hp.clm_comp hA) a b
  have hie : IntegrableOn ell (Ioc a b) volume := by
    have hi := integrableOn_covector_comp hell hp a b
    have he : (fun s ↦ ((ell s).comp (Phi s 0)).comp (Phi 0 s)) = ell := by
      funext s
      simp only [ContinuousLinearMap.comp_assoc, hPhi.cocycle, hPhi.diag,
        ContinuousLinearMap.comp_id]
    rw [he] at hi
    simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (show Ioc a b ⊆ Icc 0 T from
        fun s hs ↦ ⟨ha.trans hs.1.le, hs.2.trans hb⟩)] using hi
  dsimp only
  change (q b + r b) - (q a + r a) = _
  have hs : (∫ t in a..b,
      ((q t + r t).comp (A t)) + ell t) =
      (∫ t in a..b, (q t).comp (A t)) +
        (∫ t in a..b, (r t).comp (A t)) + ∫ t in a..b, ell t := by
    simp only [ContinuousLinearMap.add_comp]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add]
    all_goals first
      | exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hiq
      | exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hir
      | exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hie
      | exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hiq).add
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hir)
  change (q b + r b) - (q a + r a) =
    -(∫ t in a..b, ((q t + r t).comp (A t)) + ell t) - _
  rw [hs]
  have he : (q b + r b) - (q a + r a) = (q b - q a) + (r b - r a) := by abel
  rw [he, hq, hr']
  abel

omit [CompleteSpace X] in
/-- The constructed full costate uses the right-continuous representative at atoms. -/
theorem fullPropagatedCostate_right_continuous {μ : Measure ℝ} [IsFiniteMeasure μ]
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (n ell : ℝ → X →L[ℝ] ℝ)
    (hn : Integrable (fun s ↦ (n s).comp (Phi s 0)) μ)
    (terminal : X →L[ℝ] ℝ) (T : ℝ)
    (hell : Integrable (fun s ↦ (ell s).comp (Phi s 0)) (volume.restrict (Icc 0 T)))
    (t : ℝ) : ContinuousWithinAt (fullPropagatedCostate Phi μ n ell terminal T)
      (Ici t) t := by
  exact (propagated_right_continuous (terminal.comp (Phi T 0)) hPhi hn t).add
    (propagated_right_continuous 0 hPhi hell t)

section Indexed

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] {μ : Measure Ω} [SFinite μ]

omit [CompleteSpace X] [SFinite μ] in
/-- Continuous paths on the compact multiplier domain pair integrably with covectors. -/
theorem integrable_compact_density_apply {w : Ω → X →L[ℝ] ℝ} (hw : Integrable w μ)
    {v : Ω → X} (hv : Continuous v) : Integrable (fun q ↦ w q (v q)) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  apply (hw.norm.mul_const C).mono'
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hw.aestronglyMeasurable.prodMk hv.aestronglyMeasurable)
  · exact Eventually.of_forall fun q ↦ (w q).le_opNorm (v q) |>.trans
      (mul_le_mul_of_nonneg_left (hC q (mem_univ q)) (norm_nonneg _))

/-- The indexed tail paired with a smooth path has the exact local product balance. -/
theorem indexed_costate_pairing_increment (κ : Ω → ℝ) (hκ : Continuous κ)
    {w : Ω → X →L[ℝ] ℝ} (hw : Integrable w μ) (lambda : X →L[ℝ] ℝ)
    (v v' : ℝ → X) (hv' : Continuous v') (hd : ∀ t, HasDerivAt v (v' t) t)
    {a b : ℝ} (hab : a ≤ b) :
    let q := fun t ↦ lambda + ∫ q in {q | t < κ q}, w q ∂μ
    q b (v b) - q a (v a) = (∫ t in a..b, q t (v' t)) -
      ∫ q in {q | a < κ q ∧ κ q ≤ b}, w q (v (κ q)) ∂μ := by
  let tail := fun t ↦ ∫ q in {q | t < κ q}, w q ∂μ
  have hv : Continuous v :=
    (show Differentiable ℝ v from fun t ↦ (hd t).differentiableAt).continuous
  have hvi : Integrable v' (volume.restrict (Ioc a b)) :=
    hv'.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hti := integrable_indexed_tail_apply κ hκ hw hvi
  have hi : Integrable (fun q ↦ w q (v (κ q))) μ :=
    integrable_compact_density_apply hw (hv.comp hκ)
  have hid : Integrable (fun q ↦ w q (v (κ q) - v a)) μ := by
    apply (hi.sub ((ContinuousLinearMap.apply ℝ ℝ (v a)).integrable_comp hw)).congr
    exact Eventually.of_forall (fun q ↦ by simp)
  have hc : Integrable (fun q ↦ w q (v a)) μ :=
    (ContinuousLinearMap.apply ℝ ℝ (v a)).integrable_comp hw
  have hm : MeasurableSet {q | a < κ q ∧ κ q ≤ b} :=
    (isOpen_lt continuous_const hκ).measurableSet.inter
      (isClosed_le hκ continuous_const).measurableSet
  have hbset : MeasurableSet {q | b < κ q} :=
    (isOpen_lt continuous_const hκ).measurableSet
  have ht : (∫ t in a..b, tail t (v' t)) =
      (∫ q in {q | a < κ q ∧ κ q ≤ b}, w q (v (κ q) - v a) ∂μ) +
        tail b (v b - v a) := by
    rw [intervalIntegral.integral_of_le hab,
      ← integral_indexed_tail_pairing κ hκ hw hvi]
    have he (q : Ω) : w q (∫ t in Iio (κ q), v' t ∂volume.restrict (Ioc a b)) =
        {q | a < κ q ∧ κ q ≤ b}.indicator (fun q ↦ w q (v (κ q) - v a)) q +
        {q | b < κ q}.indicator (fun q ↦ w q (v b - v a)) q := by
      rw [integral_prefix_deriv v v' hv' hd hab]
      by_cases ha : κ q ≤ a
      · have hb : κ q ≤ b := ha.trans hab
        simp [ha, hb, indicator, not_lt.mpr ha, not_lt.mpr hb]
      · by_cases hb : κ q ≤ b
        · simp [ha, hb, indicator, lt_of_not_ge ha, not_lt.mpr hb]
        · simp [ha, hb, indicator, lt_of_not_ge ha, lt_of_not_ge hb]
    simp_rw [he]
    have hib : Integrable (fun q ↦ w q (v b - v a)) μ :=
      (ContinuousLinearMap.apply ℝ ℝ (v b - v a)).integrable_comp hw
    rw [integral_add (hid.indicator hm) (hib.indicator hbset),
      integral_indicator hm, integral_indicator hbset,
      ContinuousLinearMap.integral_apply hw.integrableOn]
  have hs : (∫ q in {q | a < κ q ∧ κ q ≤ b}, w q (v (κ q) - v a) ∂μ) =
      (∫ q in {q | a < κ q ∧ κ q ≤ b}, w q (v (κ q)) ∂μ) -
        (tail a - tail b) (v a) := by
    simp_rw [map_sub]
    rw [integral_sub hi.integrableOn hc.integrableOn,
      indexed_tail_sub κ hκ hw hab, ContinuousLinearMap.integral_apply hw.integrableOn]
  have hl : (∫ t in a..b, lambda (v' t)) = lambda (v b - v a) := by
    rw [lambda.intervalIntegral_comp_comm (hv'.intervalIntegrable _ _)]
    congr 1
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
      (hv'.intervalIntegrable _ _)
  dsimp only
  change (lambda + tail b) (v b) - (lambda + tail a) (v a) =
    (∫ t in a..b, (lambda + tail t) (v' t)) - _
  simp only [add_apply]
  rw [intervalIntegral.integral_add
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 (lambda.integrable_comp hvi))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hti), hl, ht, hs]
  simp only [map_sub, sub_apply]
  ring

/-- An indexed multiplier constructs a propagated costate using its actual time projection. -/
noncomputable def indexedPropagatedCostate (κ : Ω → ℝ)
    (Phi : ℝ → ℝ → X →L[ℝ] X) (μ : Measure Ω) (w : Ω → X →L[ℝ] ℝ)
    (lambda : X →L[ℝ] ℝ) (t : ℝ) : X →L[ℝ] ℝ :=
  (lambda + ∫ q in {q | t < κ q}, w q ∂μ).comp (Phi 0 t)

omit [CompleteSpace X] [CompactSpace Ω] [SecondCountableTopology Ω] in
/-- The constructed indexed costate times a continuous coefficient is locally integrable. -/
theorem indexed_propagated_integrableOn_comp (κ : Ω → ℝ) (hκ : Continuous κ)
    {w : Ω → X →L[ℝ] ℝ} (hw : Integrable w μ) (lambda : X →L[ℝ] ℝ)
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (hA : Continuous A) (a b : ℝ) :
    IntegrableOn (fun t ↦ (indexedPropagatedCostate κ Phi μ w lambda t).comp (A t))
      (Ioc a b) volume := by
  have hp : Continuous (fun t ↦ Phi 0 t) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_id)
  have hq : Integrable (fun t ↦ lambda + ∫ q in {q | t < κ q}, w q ∂μ)
      (volume.restrict (Ioc a b)) :=
    (integrable_const lambda).add (integrable_indexed_tail κ hκ hw)
  simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc, inter_self,
    indexedPropagatedCostate, ContinuousLinearMap.comp_assoc] using
    integrableOn_covector_comp hq (hp.clm_comp hA) a b

/-- The indexed propagated costate satisfies the exact additive adjoint increment,
including the complete constraint fiber over each atom of the time projection. -/
theorem indexed_propagated_increment (κ : Ω → ℝ) (hκ : Continuous κ)
    {w : Ω → X →L[ℝ] ℝ} (hw : Integrable w μ) (lambda : X →L[ℝ] ℝ)
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (hA : Continuous A) {a b : ℝ} (hab : a ≤ b) :
    let p := indexedPropagatedCostate κ Phi μ w lambda
    p b - p a = -(∫ t in a..b, (p t).comp (A t)) -
      ∫ q in {q | a < κ q ∧ κ q ≤ b}, (w q).comp (Phi 0 (κ q)) ∂μ := by
  have hp : Continuous (fun t ↦ Phi 0 t) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_id)
  have hq : Integrable (fun t ↦ lambda + ∫ q in {q | t < κ q}, w q ∂μ)
      (volume.restrict (Ioc a b)) :=
    (integrable_const lambda).add (integrable_indexed_tail κ hκ hw)
  have hi := integrableOn_covector_comp hq (hp.clm_comp hA) a b
  have hi' : IntegrableOn (fun t ↦
      (indexedPropagatedCostate κ Phi μ w lambda t).comp (A t)) (Ioc a b) volume := by
    simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc, inter_self,
      indexedPropagatedCostate, ContinuousLinearMap.comp_assoc] using hi
  have hn : Integrable (fun q ↦ (w q).comp (Phi 0 (κ q))) μ := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (hp.comp hκ).continuousOn
    apply (hw.norm.mul_const C).mono'
    · exact (continuous_fst.clm_comp continuous_snd).comp_aestronglyMeasurable
        (hw.aestronglyMeasurable.prodMk (hp.comp hκ).aestronglyMeasurable)
    · exact Eventually.of_forall fun q ↦ (w q).opNorm_comp_le (Phi 0 (κ q)) |>.trans
        (mul_le_mul_of_nonneg_left (hC q (mem_univ q)) (norm_nonneg _))
  dsimp only
  ext x
  have hd : ∀ t, HasDerivAt (fun s ↦ Phi 0 s x) (-((Phi 0 t).comp (A t)) x) t := by
    intro t
    simpa using (hPhi.backward 0 t).clm_apply (hasDerivAt_const t x)
  have he := indexed_costate_pairing_increment κ hκ hw lambda (fun t ↦ Phi 0 t x)
    (fun t ↦ -((Phi 0 t).comp (A t)) x)
    ((hp.clm_comp hA).neg.clm_apply continuous_const) hd hab
  dsimp only at he
  rw [intervalIntegral.integral_of_le hab] at he ⊢
  simp only [sub_apply, neg_apply]
  rw [ContinuousLinearMap.integral_apply hi', ContinuousLinearMap.integral_apply hn.integrableOn]
  simpa only [indexedPropagatedCostate, ContinuousLinearMap.comp_apply,
    neg_apply, map_neg, integral_neg] using he

omit [CompleteSpace X] [CompactSpace Ω] [SecondCountableTopology Ω] [SFinite μ] in
/-- BV is derived for the indexed propagated costate, including singular time fibers. -/
theorem indexed_propagated_boundedVariation (κ : Ω → ℝ) (hκ : Continuous κ)
    {w : Ω → X →L[ℝ] ℝ} (hw : Integrable w μ) (lambda : X →L[ℝ] ℝ)
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (hA : Continuous A) (a b : ℝ) :
    BoundedVariationOn (indexedPropagatedCostate κ Phi μ w lambda) (Icc a b) := by
  have ht := ((isometry_add_left lambda).lipschitzWith.comp_boundedVariationOn
    (boundedVariation_indexed_tail κ hκ hw)).mono (subset_univ (Icc a b))
  exact ht.bilinear_comp (transition_boundedVariation hPhi hA a b)
    (ContinuousLinearMap.compL ℝ X X ℝ)

omit [CompleteSpace X] [CompactSpace Ω] [SecondCountableTopology Ω] [SFinite μ] in
/-- Indexed propagated costates retain the right-continuous open-tail representative. -/
theorem indexed_propagated_right_continuous (κ : Ω → ℝ) (hκ : Continuous κ)
    {w : Ω → X →L[ℝ] ℝ} (hw : Integrable w μ) (lambda : X →L[ℝ] ℝ)
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (t : ℝ) :
    ContinuousWithinAt (indexedPropagatedCostate κ Phi μ w lambda) (Ici t) t := by
  exact (continuousWithinAt_const.add (continuousWithinAt_indexed_tail κ hκ hw t)).clm_comp
    (hPhi.backward 0 t).continuousAt.continuousWithinAt

omit [CompleteSpace X] [CompactSpace Ω] [SecondCountableTopology Ω] [SFinite μ] in
/-- The left trace of an indexed propagated costate includes the entire active time fiber. -/
theorem indexed_propagated_left_trace (κ : Ω → ℝ) (hκ : Continuous κ)
    {w : Ω → X →L[ℝ] ℝ} (hw : Integrable w μ) (lambda : X →L[ℝ] ℝ)
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (t : ℝ) :
    Function.leftLim (indexedPropagatedCostate κ Phi μ w lambda) t =
      (lambda + ∫ q in {q | t ≤ κ q}, w q ∂μ).comp (Phi 0 t) := by
  apply leftLim_eq_of_tendsto
  have hl := (tendsto_const_nhds (x := lambda)).add (tendsto_indexed_tail_left κ hκ hw t)
  have hp := (hPhi.backward 0 t).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[<] t ≤ 𝓝 t)
  exact ((continuous_fst.clm_comp continuous_snd).tendsto _).comp (hl.prodMk_nhds hp)

omit [CompleteSpace X] [CompactSpace Ω] [SecondCountableTopology Ω] [SFinite μ] in
/-- The jump is the negative multiplier normal on the full time fiber. -/
theorem indexed_propagated_jump (κ : Ω → ℝ) (hκ : Continuous κ)
    {w : Ω → X →L[ℝ] ℝ} (hw : Integrable w μ) (lambda : X →L[ℝ] ℝ)
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (t : ℝ) :
    indexedPropagatedCostate κ Phi μ w lambda t -
      Function.leftLim (indexedPropagatedCostate κ Phi μ w lambda) t =
        -(∫ q in {q | κ q = t}, w q ∂μ).comp (Phi 0 t) := by
  rw [indexed_propagated_left_trace κ hκ hw lambda hPhi t, indexedPropagatedCostate,
    ← ContinuousLinearMap.sub_comp]
  have he : (lambda + ∫ q in {q | t < κ q}, w q ∂μ) -
      (lambda + ∫ q in {q | t ≤ κ q}, w q ∂μ) =
        -(∫ q in {q | κ q = t}, w q ∂μ) := by
    have ht := indexed_closed_tail_sub_open κ hκ hw t
    abel_nf
    rw [← ht]
    abel
  rw [he, ContinuousLinearMap.neg_comp]

end Indexed

end MeasureAdjoint
