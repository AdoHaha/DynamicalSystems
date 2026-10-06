/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module
public import DynamicalSystems.Mathlib.Analysis.ODE.StateTransitionExistence
public import DynamicalSystems.Mathlib.Analysis.ODE.MeasureAdjoint
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # Actual affine integral responses to measurable forcing

The response is constructed by integrating the actual forcing through the state transition.
Integrability follows from compact-interval operator bounds, and response differences are exact.
-/
@[expose] public section
open Set MeasureTheory Filter
open scoped Interval Topology NNReal
namespace AffineIntegralResponse
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Continuous operators preserve integrability of L1 forcing on a finite interval. -/
theorem intervalIntegrable_clm_apply {U : ℝ → F →L[ℝ] E} (hU : Continuous U)
    {g : ℝ → F} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t ↦ U t (g t)) volume a b := by
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hU.continuousOn
  apply (hg.norm.const_mul C).mono_fun'
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      hU.aestronglyMeasurable hg.def'.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    exact ((U t).le_opNorm (g t)).trans
      (mul_le_mul_of_nonneg_right (hC t (uIoc_subset_uIcc ht)) (norm_nonneg _))

/-- The triangular Fubini pairing with a Banach-valued output. -/
theorem integral_order_pairing {τ : Type*} [LinearOrder τ] [TopologicalSpace τ]
    [OrderTopology τ] [SecondCountableTopology τ] [MeasurableSpace τ] [BorelSpace τ]
    {μ ν : Measure τ} [SFinite μ] [SFinite ν]
    {w : τ → F →L[ℝ] E} (hw : Integrable w μ) {v : τ → F} (hv : Integrable v ν) :
    (∫ s, w s (∫ t in Iio s, v t ∂ν) ∂μ) =
      ∫ t, (∫ s in Ioi t, w s ∂μ) (v t) ∂ν := by
  classical
  have hprod : Integrable (fun z : τ × τ ↦ w z.1 (v z.2)) (μ.prod ν) := by
    apply hw.op_fst_snd _ _ hv
    · exact continuous_fst.clm_apply continuous_snd
    · exact ⟨1, fun f x ↦ by simpa using f.le_opNorm x⟩
  have hset : MeasurableSet {z : τ × τ | z.2 < z.1} :=
    (isOpen_lt continuous_snd continuous_fst).measurableSet
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
    rw [ContinuousLinearMap.integral_apply hw.integrableOn, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ ↦ by simp [Set.indicator])
  simp_rw [hl, hr]
  exact hswap

omit [CompleteSpace F] in
/-- Strict prefixes of the restricted Lebesgue marginal are the actual interval integrals. -/
theorem prefix_restrict_Ioc (g : ℝ → F) {a b t : ℝ} (ht : t ∈ Icc a b) :
    (∫ s in Iio t, g s ∂volume.restrict (Ioc a b)) = ∫ s in a..t, g s := by
  rw [Measure.restrict_restrict measurableSet_Iio]
  have hs : Iio t ∩ Ioc a b = Ioo a t := by
    ext s
    simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨hst, has, hsb⟩
      exact ⟨has, hst⟩
    · rintro ⟨has, hst⟩
      exact ⟨hst, has, hst.le.trans ht.2⟩
  rw [hs, ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le ht.1]

omit [CompleteSpace F] in
/-- Open tails of the restricted Lebesgue marginal are the remaining interval integrals. -/
theorem tail_restrict_Ioc (g : ℝ → F) {a b t : ℝ} (ht : t ∈ Icc a b) :
    (∫ s in Ioi t, g s ∂volume.restrict (Ioc a b)) = ∫ s in t..b, g s := by
  rw [Measure.restrict_restrict measurableSet_Ioi]
  have hs : Ioi t ∩ Ioc a b = Ioc t b := by
    ext s
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨hst, has, hsb⟩
      exact ⟨hst, hsb⟩
    · rintro ⟨hst, hsb⟩
      exact ⟨hst, ht.1.trans_lt hst, hsb⟩
  rw [hs, intervalIntegral.integral_of_le ht.2]

/-- C1 operator / L1 primitive integration identity, derived by actual triangular Fubini. -/
theorem integral_operator_primitive {U U' : ℝ → F →L[ℝ] E}
    (hU' : Continuous U') (hderiv : ∀ t, HasDerivAt U (U' t) t)
    {g : ℝ → F} {a b : ℝ} (hab : a ≤ b) (hg : IntervalIntegrable g volume a b) :
    (∫ s in a..b, U' s (∫ r in a..s, g r)) =
      ∫ s in a..b, (U b - U s) (g s) := by
  let μ := volume.restrict (Ioc a b)
  have hwi : Integrable U' μ := hU'.intervalIntegrable a b |>.1
  have hgi : Integrable g μ := hg.1
  have hi := integral_order_pairing hwi hgi
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  calc
    _ = ∫ s, U' s (∫ r in Iio s, g r ∂μ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [prefix_restrict_Ioc g ⟨hs.1.le, hs.2⟩]
    _ = ∫ s, (∫ r in Ioi s, U' r ∂μ) (g s) ∂μ := hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [tail_restrict_Ioc U' ⟨hs.1.le, hs.2⟩]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht ↦ hderiv t) (hU'.intervalIntegrable s b)]

/-- The actual Duhamel response; no trajectory or first-variation certificate is supplied. -/
noncomputable def response (Phi : ℝ → ℝ → E →L[ℝ] E)
    (a : ℝ) (x₀ : E) (g : ℝ → E) (t : ℝ) : E :=
  Phi t a x₀ + ∫ s in a..t, Phi t s (g s)

variable {A : ℝ → E →L[ℝ] E} {Phi : ℝ → ℝ → E →L[ℝ] E}

omit [CompleteSpace E] in
/-- The response has the prescribed initial value by diagonal normalization. -/
theorem initial (hPhi : IsStateTransition A Phi) (a : ℝ) (x₀ : E) (g : ℝ → E) :
    response Phi a x₀ g a = x₀ := by
  simp [response, hPhi.diag]

omit [CompleteSpace E] in
/-- Exact response difference, including discontinuous measurable forcings. -/
theorem sub_response (hPhi : IsStateTransition A Phi) (a t : ℝ) (x₀ : E)
    {g h : ℝ → E} (hg : IntervalIntegrable g volume a t)
    (hh : IntervalIntegrable h volume a t) :
    response Phi a x₀ g t - response Phi a x₀ h t =
      ∫ s in a..t, Phi t s (g s - h s) := by
  have hp : Continuous (fun s ↦ Phi t s) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_id)
  have hgi := intervalIntegrable_clm_apply hp hg
  have hhi := intervalIntegrable_clm_apply hp hh
  simp only [response, add_sub_add_left_eq_sub, map_sub]
  exact (intervalIntegral.integral_sub hgi hhi).symm

omit [CompleteSpace E] in
/-- Exact affine mixture response, with no differentiation or trajectory certificate. -/
theorem response_affine_mixture (hPhi : IsStateTransition A Phi) (a t : ℝ) (x₀ : E)
    {g h : ℝ → E} (hg : IntervalIntegrable g volume a t)
    (hh : IntervalIntegrable h volume a t) {c d : ℝ} (hcd : c + d = 1) :
    response Phi a x₀ (fun s ↦ c • g s + d • h s) t =
      c • response Phi a x₀ g t + d • response Phi a x₀ h t := by
  have hp : Continuous (fun s ↦ Phi t s) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_id)
  have hgi := intervalIntegrable_clm_apply hp hg
  have hhi := intervalIntegrable_clm_apply hp hh
  simp only [response, map_add, map_smul]
  have hgc : IntervalIntegrable (fun s ↦ c • Phi t s (g s)) volume a t := by
    convert hgi.smul c using 1
  have hhd : IntervalIntegrable (fun s ↦ d • Phi t s (h s)) volume a t := by
    convert hhi.smul d using 1
  rw [intervalIntegral.integral_add hgc hhd,
    intervalIntegral.integral_smul, intervalIntegral.integral_smul]
  have hc : c • Phi t a x₀ + d • Phi t a x₀ = Phi t a x₀ := by
    rw [← add_smul, hcd, one_smul]
  simp only [smul_add]
  calc
    _ = (c • Phi t a x₀ + d • Phi t a x₀) +
        (c • (∫ s in a..t, Phi t s (g s)) + d • (∫ s in a..t, Phi t s (h s))) := by
      rw [hc]
    _ = _ := by abel

/-- Factor through the initial reference frame to avoid differentiating a two-time kernel. -/
theorem response_eq_reference (hPhi : IsStateTransition A Phi) (a t : ℝ) (x₀ : E)
    {g : ℝ → E} (hg : IntervalIntegrable g volume a t) :
    response Phi a x₀ g t = Phi t a (x₀ + ∫ s in a..t, Phi a s (g s)) := by
  have hp : Continuous (fun s ↦ Phi a s) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_id)
  rw [response, map_add, ← (Phi t a).intervalIntegral_comp_comm
    (intervalIntegrable_clm_apply hp hg)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  exact congrArg (fun M : E →L[ℝ] E ↦ M (g s)) (hPhi.cocycle t a s).symm
/-- The constructed response is continuous for genuinely L1, potentially discontinuous forcing. -/
theorem continuousOn_response (hPhi : IsStateTransition A Phi) {a b : ℝ}
    (x₀ : E) {g : ℝ → E} (hg : IntervalIntegrable g volume a b) :
    ContinuousOn (response Phi a x₀ g) (uIcc a b) := by
  have hp : Continuous (fun s ↦ Phi a s) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_id)
  have hi := intervalIntegrable_clm_apply hp hg
  have hprim := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have hf : Continuous (fun t ↦ Phi t a) :=
    hPhi.continuous.comp (continuous_id.prodMk continuous_const)
  have hc := hf.continuousOn.clm_apply ((continuousOn_const (c := x₀)).add hprim)
  apply hc.congr
  intro t ht
  exact (response_eq_reference hPhi a t x₀
    (hg.mono_set (uIcc_subset_uIcc_left ht)))

/-- The actual Duhamel response satisfies the Volterra integral dynamics for L1 forcing. -/
theorem response_integral_eq (hPhi : IsStateTransition A Phi) (hA : Continuous A)
    {a b : ℝ} (hab : a ≤ b) (x₀ : E) {g : ℝ → E}
    (hg : IntervalIntegrable g volume a b) :
    response Phi a x₀ g b = x₀ +
      ∫ s in a..b, A s (response Phi a x₀ g s) + g s := by
  let U : ℝ → E →L[ℝ] E := fun s ↦ Phi s a
  let U' : ℝ → E →L[ℝ] E := fun s ↦ (A s).comp (Phi s a)
  let h : ℝ → E := fun s ↦ Phi a s (g s)
  have hU : Continuous U := hPhi.continuous.comp (continuous_id.prodMk continuous_const)
  have hU' : Continuous U' := hA.clm_comp hU
  have hderiv : ∀ s, HasDerivAt U (U' s) s := fun s ↦ hPhi.forward a s
  have hp : Continuous (fun s ↦ Phi a s) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_id)
  have hh : IntervalIntegrable h volume a b := intervalIntegrable_clm_apply hp hg
  have hprim := intervalIntegral.continuousOn_primitive_interval' hh left_mem_uIcc
  have hpre : IntervalIntegrable (fun s ↦ U' s (∫ r in a..s, h r)) volume a b :=
    (hU'.continuousOn.clm_apply hprim).intervalIntegrable
  have hcon : IntervalIntegrable (fun s ↦ U' s x₀) volume a b :=
    (hU'.clm_apply continuous_const).intervalIntegrable a b
  have hdiff : IntervalIntegrable (fun s ↦ (U b - U s) (h s)) volume a b :=
    intervalIntegrable_clm_apply (continuous_const.sub hU) hh
  have hforce : IntervalIntegrable (fun s ↦ U s (h s)) volume a b :=
    intervalIntegrable_clm_apply hU hh
  have hhom : (∫ s in a..b, U' s x₀) = U b x₀ - x₀ := by
    have hd : ∀ s, HasDerivAt (fun s ↦ U s x₀) (U' s x₀) s :=
      fun s ↦ by simpa using (hderiv s).clm_apply (hasDerivAt_const s x₀)
    simpa [U, hPhi.diag] using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs ↦ hd s) hcon
  have hprod := integral_operator_primitive hU' hderiv hab hh
  have hcancel (s : ℝ) : U s (h s) = g s := by
    have he := congrArg (fun M : E →L[ℝ] E ↦ M (g s)) (hPhi.cocycle s a s)
    simpa [U, h, hPhi.diag] using he
  have heq : (∫ s in a..b, A s (response Phi a x₀ g s) + g s) =
      (∫ s in a..b, U' s x₀) + (∫ s in a..b, U' s (∫ r in a..s, h r)) +
        ∫ s in a..b, U s (h s) := by
    calc
      _ = ∫ s in a..b, (U' s x₀ + U' s (∫ r in a..s, h r)) + U s (h s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [response_eq_reference hPhi a s x₀ (hg.mono_set (uIcc_subset_uIcc_left hs))]
        simp only [U', U, h, ContinuousLinearMap.comp_apply, map_add, hcancel]
      _ = _ := by
        rw [intervalIntegral.integral_add (hcon.add hpre) hforce,
          intervalIntegral.integral_add hcon hpre]
  rw [heq, hhom, hprod]
  have hc : (∫ s in a..b, (U b - U s) (h s)) + (∫ s in a..b, U s (h s)) =
      U b (∫ s in a..b, h s) := by
    rw [← intervalIntegral.integral_add hdiff hforce, ← (U b).intervalIntegral_comp_comm hh]
    apply intervalIntegral.integral_congr
    intro s hs
    simp
  rw [add_assoc, hc, response_eq_reference hPhi a b x₀ hg]
  simp only [map_add, U]
  abel

/-- Every positive finite interval has an actual continuous Volterra response to L1 forcing.
The transition is constructed from the primitive coefficient data. -/
theorem exists_response_on_Icc [FiniteDimensional ℝ E]
    {A : ℝ → E →L[ℝ] E} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (x₀ : E) {g : ℝ → E}
    (hg : IntervalIntegrable g volume a b) :
    ∃ (Aext : ℝ → E →L[ℝ] E) (Phi : ℝ → ℝ → E →L[ℝ] E) (x : ℝ → E),
      Continuous Aext ∧ EqOn Aext A (Icc a b) ∧ IsStateTransition Aext Phi ∧
      x a = x₀ ∧ ContinuousOn x (Icc a b) ∧
      (∀ t ∈ Icc a b, x t = x₀ + ∫ s in a..t, A s (x s) + g s) ∧
      (∀ t ∈ Icc a b, x t = Phi t a x₀ + ∫ s in a..t, Phi t s (g s)) := by
  let Aext : ℝ → E →L[ℝ] E := fun t ↦ A (projIcc a b hab t)
  have hAe : Continuous Aext := hA.domRestrict.comp continuous_projIcc
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hb : ∀ t, ‖Aext t‖ ≤ (K : ℝ) := fun t ↦
    (hC _ (projIcc a b hab t).2).trans (le_max_left _ _)
  obtain ⟨Phi, hPhi⟩ := exists_stateTransition_of_continuous_bounded hAe hb
  have heq : EqOn Aext A (Icc a b) := by
    intro t ht
    simp only [Aext, projIcc_of_mem hab ht]
  refine ⟨Aext, Phi, response Phi a x₀ g, hAe, heq, hPhi,
    initial hPhi a x₀ g, ?_, ?_, fun _ _ ↦ rfl⟩
  · simpa only [uIcc_of_le hab] using continuousOn_response hPhi x₀ hg
  · intro t ht
    rw [response_integral_eq hPhi hAe ht.1 x₀
      (hg.mono_set (uIcc_subset_uIcc_left (by simpa [uIcc_of_le hab] using ht)))]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    have hsab : s ∈ Icc a b := by
      rw [uIcc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    rw [heq hsab]

/-- Continuous homogeneous Volterra solutions are unique, derived from the backward transition. -/
theorem homogeneous_eq_zero (hPhi : IsStateTransition A Phi) (hA : Continuous A)
    {a b : ℝ} (hab : a ≤ b) {z : ℝ → E} (hz : ContinuousOn z (Icc a b))
    (heq : ∀ t ∈ Icc a b, z t = ∫ s in a..t, A s (z s)) :
    ∀ t ∈ Icc a b, z t = 0 := by
  by_cases hab' : a < b
  · let zext : ℝ → E := fun t ↦ z (projIcc a b hab t)
    have hze : Continuous zext := hz.domRestrict.comp continuous_projIcc
    have hQ : Continuous (fun s ↦ A s (zext s)) := hA.clm_apply hze
    have hext : ∀ t ∈ Icc a b, z t = ∫ s in a..t, A s (zext s) := by
      intro t ht
      rw [heq t ht]
      apply intervalIntegral.integral_congr
      intro s hs
      have hsa : s ∈ Icc a b := by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      simp only [zext, projIcc_of_mem hab hsa]
    have hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt z (A t (z t)) (Icc a b) t := by
      intro t ht
      have hd : HasDerivWithinAt (fun t ↦ ∫ s in a..t, A s (zext s))
          (A t (zext t)) (Icc a b) t :=
        (hQ.integral_hasStrictDerivAt a t).hasDerivAt.hasDerivWithinAt
      have hd' := hd.congr_of_mem hext ht
      simpa only [zext, projIcc_of_mem hab ht] using hd'
    have hzero : ∀ t ∈ Icc a b,
        HasDerivWithinAt (fun t ↦ Phi a t (z t)) 0 (Icc a b) t := by
      intro t ht
      convert (hPhi.backward a t).hasDerivWithinAt.clm_apply (hderiv t ht) using 1
      simp
    have hconst : ∀ t ∈ Icc a b, Phi a t (z t) = Phi a a (z a) := by
      intro t ht
      exact (convex_Icc a b).is_const_of_fderivWithin_eq_zero
        (fun t ht ↦ (hzero t ht).differentiableWithinAt)
        (fun t ht ↦ by simpa using
          (hzero t ht).hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Icc hab' t ht)) ht ⟨le_rfl, hab⟩
    intro t ht
    have ha : z a = 0 := by simpa using heq a ⟨le_rfl, hab⟩
    have he := hconst t ht
    have hp : Phi a t (z t) = 0 := by simpa [ha] using he
    have hc := congrArg (fun v ↦ Phi t a v) hp
    have hcoc := congrArg (fun M : E →L[ℝ] E ↦ M (z t)) (hPhi.cocycle t a t)
    simpa [← ContinuousLinearMap.comp_apply, hcoc, hPhi.diag] using hc
  · have habeq : a = b := le_antisymm hab (not_lt.mp hab')
    intro t ht
    have hta : t = a := le_antisymm (ht.2.trans habeq.ge) ht.1
    subst t
    simpa using heq a ⟨le_rfl, hab⟩

/-- Actual continuous integral trajectories coincide with the constructed response. -/
theorem eq_response_of_integral_eq (hPhi : IsStateTransition A Phi) (hA : Continuous A)
    {a b : ℝ} (hab : a ≤ b) (x₀ : E) {g x : ℝ → E}
    (hg : IntervalIntegrable g volume a b) (hx : ContinuousOn x (Icc a b))
    (heq : ∀ t ∈ Icc a b, x t = x₀ + ∫ s in a..t, A s (x s) + g s) :
    ∀ t ∈ Icc a b, x t = response Phi a x₀ g t := by
  have hr : ContinuousOn (response Phi a x₀ g) (Icc a b) := by
    simpa only [uIcc_of_le hab] using continuousOn_response hPhi x₀ hg
  have hd : ∀ t ∈ Icc a b, x t - response Phi a x₀ g t =
      ∫ s in a..t, A s (x s - response Phi a x₀ g s) := by
    intro t ht
    have hgt := hg.mono_set (uIcc_subset_uIcc_left (by simpa [uIcc_of_le hab] using ht))
    have hxi : IntervalIntegrable (fun s ↦ A s (x s)) volume a t :=
      (show ContinuousOn (fun s ↦ A s (x s)) (uIcc a b) by
        simpa only [uIcc_of_le hab] using hA.continuousOn.clm_apply hx).intervalIntegrable.mono_set
        (uIcc_subset_uIcc_left (by simpa [uIcc_of_le hab] using ht))
    have hri : IntervalIntegrable (fun s ↦ A s (response Phi a x₀ g s)) volume a t :=
      (show ContinuousOn (fun s ↦ A s (response Phi a x₀ g s)) (uIcc a b) by
        simpa only [uIcc_of_le hab] using hA.continuousOn.clm_apply hr).intervalIntegrable.mono_set
        (uIcc_subset_uIcc_left (by simpa [uIcc_of_le hab] using ht))
    rw [heq t ht, response_integral_eq hPhi hA ht.1 x₀ hgt,
      add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub (hxi.add hgt) (hri.add hgt)]
    apply intervalIntegral.integral_congr
    intro s hs
    simp
  intro t ht
  exact sub_eq_zero.mp (homogeneous_eq_zero hPhi hA hab (hx.sub hr) hd t ht)

end AffineIntegralResponse
