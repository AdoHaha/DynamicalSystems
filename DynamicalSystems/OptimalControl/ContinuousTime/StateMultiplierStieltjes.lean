/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.MeasureAdjoint
public import DynamicalSystems.OptimalControl.ContinuousTime.StateMultiplierLimit
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# The Stieltjes-measure rendering of the limit multiplier `λ`

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Theorem 11.4.4 / 11.6.3: the
limit multiplier `λ` is a nonincreasing function of bounded variation, `λ ≥ 0`, `λ(t₁⁻) = 0`, and
the term `λ∇G` of the costate equation is the Stieltjes integral `∫ ∇G dλ`.

`StateMultiplierLimit.lean` delivers the limit `λ` as a nonincreasing function and the costate
equation in the measure-free form (11.6.11).  This file renders the same data as a finite positive
measure:

* `multiplierMeasure`: the Lebesgue–Stieltjes measure of `−λ`; `multiplierMeasure_Ioc_horizon`:
  `μ(t, T] = λ(t⁺)`; `rightMultiplier` is the right limit `λ(t⁺)`, equal to `λ` off a countable set
  (`rightMultiplier_ae_eq`).  The measure is finite, with total mass `λ(0)`; the part on `(−∞,0]`
  is the initial atom `λ(0) − λ(0⁺)` of Remark 11.4.2.
* `integral_Ioc_multiplierMeasure_smul`: the **Stieltjes integration by parts**
  `∫_{(t,T]} g dμ = λ(t⁺) g(t) + ∫_t^T λ g'` for an absolutely continuous covector function `g`.
* `exists_multiplierMeasure_costate`: for the conclusion `PenalisedMultiplierLimit`, the momentum
  `∂ᵥL(γL,γL')` equals, a.e., the **library's measure-tail form**
  `MeasureAdjoint.costate μ (−∇G(·,γL)) (−∂₂Φ₁) + (Lebesgue tail of −∂ₓL)`, i.e.
  `p(t) = −∂₂Φ₁ − ∫_t^T ∂ₓL − ∫_{(t,T]} ∇G dμ`.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter ACEulerLagrange
open scoped Topology Interval ENNReal

namespace OptimalControl.BoundedState

section Measure

variable {T : ℝ} {lam : ℝ → ℝ}

/-- The monotone extension `t ↦ −λ(clamp t)` of the negated multiplier to the real line, constant
outside `[0,T]`. -/
noncomputable def multiplierExtension (T : ℝ) (lam : ℝ → ℝ) (t : ℝ) : ℝ :=
  -lam (max 0 (min t T))

theorem multiplierExtension_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    multiplierExtension T lam t = -lam t := by
  have h1 : min t T = t := min_eq_left ht.2
  have h2 : max 0 t = t := max_eq_right ht.1
  simp [multiplierExtension, h1, h2]

theorem multiplierExtension_of_horizon_le {t : ℝ} (ht : T ≤ t) (hT : 0 ≤ T) :
    multiplierExtension T lam t = -lam T := by
  simp [multiplierExtension, min_eq_right ht, max_eq_right hT]

theorem multiplierExtension_of_nonpos {t : ℝ} (ht : t ≤ 0) (hT : 0 ≤ T) :
    multiplierExtension T lam t = -lam 0 := by
  have : min t T = t := min_eq_left (ht.trans hT)
  simp [multiplierExtension, this, max_eq_left ht]

/-- The extension of a nonincreasing multiplier is monotone. -/
theorem monotone_multiplierExtension (hT : 0 ≤ T) (hanti : AntitoneOn lam (Icc (0 : ℝ) T)) :
    Monotone (multiplierExtension T lam) := by
  intro a b hab
  have hmem : ∀ t : ℝ, max 0 (min t T) ∈ Icc (0 : ℝ) T := fun t =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hle : max 0 (min a T) ≤ max 0 (min b T) :=
    max_le_max le_rfl (min_le_min hab le_rfl)
  simpa [multiplierExtension] using hanti (hmem a) (hmem b) hle

/-- The right limit `λ(t⁺)` of the multiplier (`λ(T⁺) = λ(T)`, and the value at `t < 0` is `λ(0)`
by the extension). -/
noncomputable def rightMultiplier (T : ℝ) (lam : ℝ → ℝ) (t : ℝ) : ℝ :=
  -Function.rightLim (multiplierExtension T lam) t

/-- The Lebesgue–Stieltjes measure of the nonincreasing multiplier: `μ(a,b] = λ(a⁺) − λ(b⁺)`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Theorem 11.4.4: the book's `λ`
as a function of bounded variation corresponds to this finite positive measure. -/
noncomputable def multiplierMeasure (hT : 0 ≤ T) (hanti : AntitoneOn lam (Icc (0 : ℝ) T)) :
    Measure ℝ :=
  (monotone_multiplierExtension hT hanti).stieltjesFunction.measure

variable (hT : 0 ≤ T) (hanti : AntitoneOn lam (Icc (0 : ℝ) T))

include hT hanti in
theorem multiplierMeasure_Ioc (a b : ℝ) :
    multiplierMeasure hT hanti (Ioc a b) = ENNReal.ofReal (rightMultiplier T lam a
      - rightMultiplier T lam b) := by
  unfold multiplierMeasure
  rw [StieltjesFunction.measure_Ioc]
  simp only [Monotone.stieltjesFunction_eq, rightMultiplier]
  congr 1
  ring

include hT in
theorem rightMultiplier_of_horizon_le (hlamT : lam T = 0) {t : ℝ} (ht : T ≤ t) :
    rightMultiplier T lam t = 0 := by
  have hev : multiplierExtension T lam =ᶠ[𝓝[>] t] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [multiplierExtension_of_horizon_le (ht.trans hs.le) hT, hlamT, neg_zero]
  have hlim : Tendsto (multiplierExtension T lam) (𝓝[>] t) (𝓝 0) :=
    tendsto_const_nhds.congr' hev.symm
  simp [rightMultiplier, rightLim_eq_of_tendsto hlim]

include hT in
theorem rightMultiplier_of_nonpos {t : ℝ} (ht : t < 0) :
    rightMultiplier T lam t = lam 0 := by
  have hev : multiplierExtension T lam =ᶠ[𝓝[>] t] fun _ => -lam 0 := by
    have : Iio (0 : ℝ) ∈ 𝓝[>] t := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)
    filter_upwards [this] with s hs
    rw [multiplierExtension_of_nonpos (le_of_lt hs) hT]
  have hlim : Tendsto (multiplierExtension T lam) (𝓝[>] t) (𝓝 (-lam 0)) :=
    tendsto_const_nhds.congr' hev.symm
  simp [rightMultiplier, rightLim_eq_of_tendsto hlim]

include hT hanti in
/-- `λ(t⁺)` is nonincreasing. -/
theorem antitone_rightMultiplier : Antitone (rightMultiplier T lam) := by
  intro a b hab
  have := (monotone_multiplierExtension hT hanti).rightLim hab
  simpa [rightMultiplier] using this

include hT hanti in
theorem rightMultiplier_le_of_mem {M : ℝ} (hbd : ∀ t ∈ Icc (0 : ℝ) T, lam t ≤ M)
    (t : ℝ) : rightMultiplier T lam t ≤ max M (lam 0) := by
  have hmono := monotone_multiplierExtension hT hanti
  have h1 : multiplierExtension T lam t ≤ Function.rightLim (multiplierExtension T lam) t :=
    hmono.le_rightLim le_rfl
  have h2 : multiplierExtension T lam t = -lam (max 0 (min t T)) := rfl
  have hmem : max 0 (min t T) ∈ Icc (0 : ℝ) T :=
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have h3 := hbd _ hmem
  simp only [rightMultiplier]
  have : lam (max 0 (min t T)) ≤ max M (lam 0) := h3.trans (le_max_left _ _)
  linarith

include hT hanti in
theorem rightMultiplier_nonneg (hlam : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ lam t)
    (t : ℝ) : 0 ≤ rightMultiplier T lam t := by
  have hmono := monotone_multiplierExtension hT hanti
  have hle : Function.rightLim (multiplierExtension T lam) t ≤ 0 := by
    have := hmono.rightLim_le (x := t) (y := max t T + 1) (by
      have := le_max_left t T; linarith)
    refine this.trans ?_
    have hm : max 0 (min (max t T + 1) T) ∈ Icc (0 : ℝ) T :=
      ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
    have := hlam _ hm
    simp only [multiplierExtension]
    linarith
  simp only [rightMultiplier]
  linarith

include hT hanti in
/-- `λ(t⁺) = λ(t)` off a countable set, for `t ∈ [0,T]`. -/
theorem rightMultiplier_ae_eq :
    ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) T → rightMultiplier T lam t = lam t := by
  have hmono := monotone_multiplierExtension hT hanti
  have hc := hmono.countable_not_continuousAt
  filter_upwards [hc.ae_notMem volume] with t ht htI
  have hcont : ContinuousAt (multiplierExtension T lam) t := not_not.1 ht
  have hlr := (hmono.continuousAt_iff_leftLim_eq_rightLim).1 hcont
  have hval : Function.rightLim (multiplierExtension T lam) t = multiplierExtension T lam t := by
    have h1 := hmono.leftLim_le (le_refl t)
    have h2 := hmono.le_rightLim (le_refl t)
    have h3 := hmono.le_rightLim (le_refl t)
    have h4 : Function.leftLim (multiplierExtension T lam) t ≤ multiplierExtension T lam t := h1
    have h5 : multiplierExtension T lam t ≤ Function.rightLim (multiplierExtension T lam) t := h2
    linarith
  rw [rightMultiplier, hval, multiplierExtension_of_mem htI, neg_neg]

include hT hanti in
theorem multiplierMeasure_Ioc_horizon (hlamT : lam T = 0) (t : ℝ) :
    multiplierMeasure hT hanti (Ioc t T) = ENNReal.ofReal (rightMultiplier T lam t) := by
  rw [multiplierMeasure_Ioc hT hanti, rightMultiplier_of_horizon_le hT hlamT le_rfl]
  simp

include hT hanti in
theorem multiplierMeasure_Ioi_horizon (hlamT : lam T = 0) :
    multiplierMeasure hT hanti (Ioi T) = 0 := by
  have hanti' := hanti
  have hmono := monotone_multiplierExtension hT hanti
  unfold multiplierMeasure
  have hfin : Tendsto (fun x => (hmono.stieltjesFunction) x) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop T] with x hx
    have := rightMultiplier_of_horizon_le hT hlamT hx
    simp only [rightMultiplier] at this
    rw [Monotone.stieltjesFunction_eq]
    linarith
  rw [(hmono.stieltjesFunction).measure_Ioi hfin T]
  have : hmono.stieltjesFunction T = 0 := by
    have := rightMultiplier_of_horizon_le hT hlamT (le_refl T)
    simp only [rightMultiplier] at this
    simpa [Monotone.stieltjesFunction_eq] using this
  simp [this]

include hT hanti in
/-- The multiplier measure is finite, of total mass `λ(0)`. -/
theorem multiplierMeasure_univ (hlamT : lam T = 0) :
    multiplierMeasure hT hanti univ = ENNReal.ofReal (lam 0) := by
  have hmono := monotone_multiplierExtension hT hanti
  unfold multiplierMeasure
  have hl : Tendsto (fun x => (hmono.stieltjesFunction) x) atBot (𝓝 (-lam 0)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    have := rightMultiplier_of_nonpos hT (lam := lam) hx
    simp only [rightMultiplier] at this
    simp [Monotone.stieltjesFunction_eq]
    linarith
  have hu : Tendsto (fun x => (hmono.stieltjesFunction) x) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop T] with x hx
    have := rightMultiplier_of_horizon_le hT hlamT hx
    simp only [rightMultiplier] at this
    rw [Monotone.stieltjesFunction_eq]
    linarith
  rw [StieltjesFunction.measure_univ _ hl hu]
  simp

include hT hanti in
/-- The multiplier measure does not charge `(−∞,0)`: it lives on `[0,T]`. -/
theorem multiplierMeasure_Iio_zero :
    multiplierMeasure hT hanti (Iio 0) = 0 := by
  have hmono := monotone_multiplierExtension hT hanti
  unfold multiplierMeasure
  have hl : Tendsto (fun x => (hmono.stieltjesFunction) x) atBot (𝓝 (-lam 0)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    have := rightMultiplier_of_nonpos hT (lam := lam) hx
    simp only [rightMultiplier] at this
    simp [Monotone.stieltjesFunction_eq]
    linarith
  rw [(hmono.stieltjesFunction).measure_Iio hl 0]
  have hleft : Function.leftLim (hmono.stieltjesFunction) 0 = -lam 0 := by
    refine leftLim_eq_of_tendsto ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have := rightMultiplier_of_nonpos hT (lam := lam) (show x < 0 from hx)
    simp only [rightMultiplier] at this
    simp [Monotone.stieltjesFunction_eq]
    linarith
  simp [hleft]

include hT hanti in
/-- The multiplier measure is carried by `[0,T]`. -/
theorem multiplierMeasure_compl_Icc (hlamT : lam T = 0) :
    multiplierMeasure hT hanti (Icc (0 : ℝ) T)ᶜ = 0 := by
  have : (Icc (0 : ℝ) T)ᶜ = Iio 0 ∪ Ioi T := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi]
    constructor
    · intro h
      by_contra hc
      simp only [not_or, not_lt] at hc
      exact h ⟨hc.1, hc.2⟩
    · rintro (h | h) ⟨h1, h2⟩ <;> linarith
  rw [this]
  exact measure_union_null (multiplierMeasure_Iio_zero hT hanti)
    (multiplierMeasure_Ioi_horizon hT hanti hlamT)

instance (hT : 0 ≤ T) (hanti : AntitoneOn lam (Icc (0 : ℝ) T)) :
    IsLocallyFiniteMeasure (multiplierMeasure hT hanti) :=
  inferInstanceAs (IsLocallyFiniteMeasure
    (monotone_multiplierExtension hT hanti).stieltjesFunction.measure)

/-- If `λ` is constant on `[α,β] ⊆ [0,T]` (`α < β`), its right limit at `s ∈ [α,β)` is that
constant. -/
theorem rightMultiplier_eq_of_const {α β : ℝ} (hsub : Icc α β ⊆ Icc (0 : ℝ) T)
    (hconst : ∀ t ∈ Icc α β, lam t = lam α) {s : ℝ} (hs : s ∈ Ico α β) :
    rightMultiplier T lam s = lam α := by
  have hF : ∀ t ∈ Icc α β, multiplierExtension T lam t = -lam α := fun t ht => by
    rw [multiplierExtension_of_mem (hsub ht), hconst t ht]
  have : Function.rightLim (multiplierExtension T lam) s = -lam α := by
    refine rightLim_eq_of_tendsto ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hs.2] with x hx
    exact (hF x ⟨hs.1.trans hx.1.le, hx.2.le⟩).symm
  simp [rightMultiplier, this]

include hT hanti in
/-- **Complementarity in measure form**: if `λ` is constant on `[α,β] ⊆ [0,T]`, the multiplier
measure does not charge `(α,β)`.  For the limit multiplier this is the statement that the
constraint measure `dμ` is carried by the contact set (Berkovitz & Medhin, Lemma 11.3.9). -/
theorem multiplierMeasure_Ioo_eq_zero_of_const {α β : ℝ} (hαβ : α < β)
    (hsub : Icc α β ⊆ Icc (0 : ℝ) T) (hconst : ∀ t ∈ Icc α β, lam t = lam α) :
    multiplierMeasure hT hanti (Ioo α β) = 0 := by
  have hmono := monotone_multiplierExtension hT hanti
  have hF : ∀ t ∈ Icc α β, multiplierExtension T lam t = -lam α := fun t ht => by
    rw [multiplierExtension_of_mem (hsub ht), hconst t ht]
  have hrl : ∀ s ∈ Ico α β, Function.rightLim (multiplierExtension T lam) s = -lam α := by
    intro s hs
    refine rightLim_eq_of_tendsto ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hs.2] with x hx
    exact (hF x ⟨hs.1.trans hx.1.le, hx.2.le⟩).symm
  unfold multiplierMeasure
  rw [StieltjesFunction.measure_Ioo]
  have h1 : (hmono.stieltjesFunction) α = -lam α := hrl α ⟨le_rfl, hαβ⟩
  have h2 : Function.leftLim (hmono.stieltjesFunction) β = -lam α := by
    refine leftLim_eq_of_tendsto ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hαβ] with x hx
    exact (hrl x ⟨hx.1.le, hx.2⟩).symm
  rw [h1, h2]
  simp

include hT hanti in
/-- The mass of `(−∞,0]` is the initial atom `λ(0) − λ(0⁺)` (Remark 11.4.2). -/
theorem multiplierMeasure_Iic_zero :
    multiplierMeasure hT hanti (Iic 0) = ENNReal.ofReal (lam 0 - rightMultiplier T lam 0) := by
  have hmono := monotone_multiplierExtension hT hanti
  unfold multiplierMeasure
  have hl : Tendsto (fun x => (hmono.stieltjesFunction) x) atBot (𝓝 (-lam 0)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    have := rightMultiplier_of_nonpos hT (lam := lam) hx
    simp only [rightMultiplier] at this
    simp [Monotone.stieltjesFunction_eq]
    linarith
  rw [(hmono.stieltjesFunction).measure_Iic hl 0]
  simp only [Monotone.stieltjesFunction_eq, rightMultiplier]
  congr 1
  ring

end Measure

section ByParts

/-- **Scalar Stieltjes integration by parts** (Fubini on the triangle `a < r < s ≤ T`):
`∫_{(a,T]} (c + ∫_a^s k) dμ(s) = c μ(a,T] + ∫_a^T μ(r,T] k(r) dr`. -/
theorem integral_Ioc_primitive_stieltjes {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {a T c : ℝ}
    (haT : a ≤ T) {k : ℝ → ℝ} (hk : IntervalIntegrable k volume a T) :
    ∫ s in Ioc a T, (c + ∫ r in a..s, k r) ∂μ
      = c * μ.real (Ioc a T) + ∫ r in a..T, μ.real (Ioc r T) * k r := by
  classical
  have hfin : IsFiniteMeasure (μ.restrict (Ioc a T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hkI : IntegrableOn k (Ioc a T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le haT).1 hk
  have hcont : ContinuousOn (fun s => ∫ r in a..s, k r) (Icc a T) := by
    have := intervalIntegral.continuousOn_primitive_interval' (a := a) hk
      (by simp [uIcc, haT] : a ∈ [[a, T]])
    rwa [uIcc_of_le haT] at this
  have hint2 : Integrable (fun s => ∫ r in a..s, k r) (μ.restrict (Ioc a T)) :=
    (hcont.integrableOn_Icc (μ := μ)).mono_set Ioc_subset_Icc_self
  rw [integral_add (integrable_const c) hint2, integral_const, smul_eq_mul,
    Measure.real, Measure.restrict_apply_univ]
  have hpair := MeasureAdjoint.integral_order_tail_pairing (X := ℝ)
    (μ := μ.restrict (Ioc a T)) (ν := volume.restrict (Ioc a T))
    (w := fun _ => ContinuousLinearMap.id ℝ ℝ) (integrable_const _) (v := k) hkI
  have hl : ∫ s in Ioc a T, (∫ r in a..s, k r) ∂μ =
      ∫ s, (ContinuousLinearMap.id ℝ ℝ) (∫ r in Iio s, k r ∂(volume.restrict (Ioc a T)))
        ∂(μ.restrict (Ioc a T)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    simp only [ContinuousLinearMap.id_apply]
    rw [Measure.restrict_restrict measurableSet_Iio, intervalIntegral.integral_of_le hs.1.le]
    have : Iio s ∩ Ioc a T = Ioo a s := by
      ext r; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.le.trans hs.2⟩
    rw [this]
    exact setIntegral_congr_set Ioo_ae_eq_Ioc.symm
  rw [hl, hpair, ← intervalIntegral.integral_of_le haT]
  rw [mul_comm]
  congr 1
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le haT] at hx
  rw [setIntegral_const, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, Measure.real, Measure.restrict_apply measurableSet_Ioi]
  have : Ioi x ∩ Ioc a T = Ioc x T := by
    ext r; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, hx.1.trans_lt h1, h3⟩
  rw [this]
  rfl

/-- The tail mass `r ↦ μ(r,T]` is nonincreasing. -/
theorem antitone_real_Ioc_tail (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] (T : ℝ) :
    Antitone fun r : ℝ => μ.real (Ioc r T) := fun _ _ h =>
  measureReal_mono (Ioc_subset_Ioc_left h) measure_Ioc_lt_top.ne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The tail mass times an interval integrable covector function is interval integrable. -/
theorem intervalIntegrable_real_Ioc_tail_smul (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    {a T : ℝ} (haT : a ≤ T) {gd : ℝ → E →L[ℝ] ℝ} (hgd : IntervalIntegrable gd volume a T) :
    IntervalIntegrable (fun r => μ.real (Ioc r T) • gd r) volume a T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le haT] at hgd ⊢
  have hmeas : AEStronglyMeasurable (fun r : ℝ => μ.real (Ioc r T)) (volume.restrict (Ioc a T)) :=
    (antitone_real_Ioc_tail μ T).measurable.aestronglyMeasurable
  refine Integrable.bdd_smul (φ := fun r : ℝ => μ.real (Ioc r T)) hgd (μ.real (Ioc a T)) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact antitone_real_Ioc_tail μ T hr.1.le

/-- **Stieltjes integration by parts for an absolutely continuous covector function**:
`∫_{(a,T]} g dμ = μ(a,T] g(a) + ∫_a^T μ(r,T] g'(r) dr` when `g = g(a) + ∫_a^· g'`. -/
theorem integral_Ioc_primitive_stieltjes_covector {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {a T : ℝ} (haT : a ≤ T) {g gd : ℝ → E →L[ℝ] ℝ} (hgd : IntervalIntegrable gd volume a T)
    (hg : ∀ s ∈ Icc a T, g s = g a + ∫ r in a..s, gd r) :
    ∫ s in Ioc a T, g s ∂μ
      = μ.real (Ioc a T) • g a + ∫ r in a..T, μ.real (Ioc r T) • gd r := by
  classical
  have hfin : IsFiniteMeasure (μ.restrict (Ioc a T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hcont : ContinuousOn (fun s => ∫ r in a..s, gd r) (Icc a T) := by
    have := intervalIntegral.continuousOn_primitive_interval' (a := a) hgd
      (by simp [uIcc, haT] : a ∈ [[a, T]])
    rwa [uIcc_of_le haT] at this
  have hgcont : ContinuousOn g (Icc a T) :=
    (continuousOn_const.add hcont).congr hg
  have hgint : Integrable g (μ.restrict (Ioc a T)) :=
    (hgcont.integrableOn_Icc (μ := μ)).mono_set Ioc_subset_Icc_self
  have hrint := intervalIntegrable_real_Ioc_tail_smul μ haT hgd
  refine ContinuousLinearMap.ext fun e => ?_
  rw [ContinuousLinearMap.integral_apply hgint, add_apply,
    smul_apply, ContinuousLinearMap.intervalIntegral_apply hrint]
  have hk : IntervalIntegrable (fun r => gd r e) volume a T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le haT] at hgd ⊢
    exact (ContinuousLinearMap.apply ℝ ℝ e).integrable_comp hgd
  have hscalar := integral_Ioc_primitive_stieltjes (μ := μ) (c := g a e) haT hk
  have hlhs : ∫ s in Ioc a T, g s e ∂μ = ∫ s in Ioc a T, (g a e + ∫ r in a..s, gd r e) ∂μ := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs' : s ∈ Icc a T := ⟨hs.1.le, hs.2⟩
    have hgs : IntervalIntegrable gd volume a s := hgd.mono_set (by
      rw [uIcc_of_le haT, uIcc_of_le hs.1.le]; exact Icc_subset_Icc le_rfl hs.2)
    rw [hg s hs', add_apply, ContinuousLinearMap.intervalIntegral_apply hgs]
  rw [hlhs, hscalar]
  simp only [smul_apply, smul_eq_mul]
  rw [mul_comm]

end ByParts

section Wiring

variable {T : ℝ} {lam : ℝ → ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (hT : 0 ≤ T) (hanti : AntitoneOn lam (Icc (0 : ℝ) T))

include hT hanti in
/-- On `[0,T]` the real tail mass of the multiplier measure is `λ(t⁺)`. -/
theorem real_Ioc_multiplierMeasure (hlam : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ lam t) (hlamT : lam T = 0)
    (t : ℝ) :
    (multiplierMeasure hT hanti).real (Ioc t T) = rightMultiplier T lam t := by
  rw [Measure.real, multiplierMeasure_Ioc_horizon hT hanti hlamT t,
    ENNReal.toReal_ofReal (rightMultiplier_nonneg hT hanti hlam t)]

include hT hanti in
/-- **The momentum in the Stieltjes measure-tail form** (Berkovitz & Medhin, Theorem 11.4.4 (ii)).

Let `Φ = limitStateCostate c λ ∇G(0) ∂ₓL (d∇G/dt)` be the limit costate (11.6.11) with
`Φ(T) = −q`, and suppose the momentum `p` satisfies `p = Φ − λ ∇G` a.e.  Then, with `μ` the
Stieltjes measure of the nonincreasing multiplier `λ`, for a.e. `t ∈ (0,T)`
`p(t) = −q − ∫_t^T ∂ₓL − ∫_{(t,T]} ∇G dμ`:
the `λ∇G` term of the costate equation is the tail Stieltjes integral `∫ ∇G dλ` (the measure-free
costate equation and the measure form are equivalent by Stieltjes integration by parts). -/
theorem momentum_eq_stieltjesTail (hlam : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ lam t) (hlamT : lam T = 0)
    {c q : E →L[ℝ] ℝ} {a gd g p : ℝ → E →L[ℝ] ℝ}
    (ha : IntervalIntegrable a volume 0 T) (hgd : IntervalIntegrable gd volume 0 T)
    (hg : ∀ s ∈ Icc (0 : ℝ) T, g s = g 0 + ∫ r in (0 : ℝ)..s, gd r)
    (hΦT : limitStateCostate c lam (g 0) a gd T = -q)
    (hmom : ∀ᵐ t ∂(timeMeasure T), p t = limitStateCostate c lam (g 0) a gd t - lam t • g t) :
    ∀ᵐ t ∂(timeMeasure T), p t = -q - (∫ r in t..T, a r)
      - ∫ s in Ioc t T, g s ∂(multiplierMeasure hT hanti) := by
  classical
  set μ := multiplierMeasure hT hanti with hμ
  have hrm := rightMultiplier_ae_eq hT hanti
  have hrm' : ∀ᵐ t ∂(timeMeasure T), t ∈ Icc (0 : ℝ) T → rightMultiplier T lam t = lam t :=
    ae_restrict_of_ae hrm
  have hreal : ∀ r ∈ Icc (0 : ℝ) T, μ.real (Ioc r T) = rightMultiplier T lam r :=
    fun r _ => real_Ioc_multiplierMeasure hT hanti hlam hlamT r
  have hrmgd : IntervalIntegrable (fun r => rightMultiplier T lam r • gd r) volume 0 T := by
    have h1 := intervalIntegrable_real_Ioc_tail_smul μ hT hgd
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at h1 ⊢
    refine h1.congr_fun (fun r hr => ?_) measurableSet_Ioc
    simp only
    rw [hreal r ⟨hr.1.le, hr.2⟩]
  have hlamgd : IntervalIntegrable (fun r => lam r • gd r) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at hrmgd ⊢
    refine hrmgd.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae hrm, ae_restrict_mem measurableSet_Ioc] with r h1 h2
    rw [h1 ⟨h2.1.le, h2.2⟩]
  have hFint : IntervalIntegrable (fun r => a r + lam r • gd r) volume 0 T := ha.add hlamgd
  filter_upwards [hmom, hrm', ae_restrict_mem measurableSet_Ioc] with t h1 h2 h3
  have ht : t ∈ Icc (0 : ℝ) T := ⟨h3.1.le, h3.2⟩
  have htT : t ≤ T := ht.2
  have hI : ∀ {u v : ℝ}, u ∈ Icc (0 : ℝ) T → v ∈ Icc (0 : ℝ) T →
      IntervalIntegrable gd volume u v := fun hu hv =>
    intervalIntegrable_of_mem_Icc_Icc hgd hT hu hv
  have hg_t : ∀ s ∈ Icc t T, g s = g t + ∫ r in t..s, gd r := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) T := ⟨h3.1.le.trans hs.1, hs.2⟩
    rw [hg s hs', hg t ht, add_assoc, intervalIntegral.integral_add_adjacent_intervals
      (hI ⟨le_rfl, hT⟩ ht) (hI ht hs')]
  have hibp := integral_Ioc_primitive_stieltjes_covector (μ := μ) htT (hI ht ⟨hT, le_rfl⟩) hg_t
  have hcongr : ∫ r in t..T, μ.real (Ioc r T) • gd r = ∫ r in t..T, lam r • gd r := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hrm] with r hr hrI
    rw [uIoc_of_le htT] at hrI
    have hrI' : r ∈ Icc (0 : ℝ) T := ⟨h3.1.le.trans hrI.1.le, hrI.2⟩
    rw [hreal r hrI', hr hrI']
  have hlamgd_t : IntervalIntegrable (fun r => lam r • gd r) volume t T :=
    intervalIntegrable_of_mem_Icc_Icc hlamgd hT ht ⟨hT, le_rfl⟩
  have ha_t : IntervalIntegrable a volume t T :=
    intervalIntegrable_of_mem_Icc_Icc ha hT ht ⟨hT, le_rfl⟩
  have hF0t : IntervalIntegrable (fun r => a r + lam r • gd r) volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc hFint hT ⟨le_rfl, hT⟩ ht
  have hFtT : IntervalIntegrable (fun r => a r + lam r • gd r) volume t T :=
    intervalIntegrable_of_mem_Icc_Icc hFint hT ht ⟨hT, le_rfl⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hF0t hFtT
  rw [hibp, hreal t ht, h2 ht, hcongr, h1]
  have hFsplit := intervalIntegral.integral_add ha_t hlamgd_t
  have hΦT' := hΦT
  simp only [limitStateCostate] at hΦT' ⊢
  rw [← hsplit, hFsplit] at hΦT'
  linear_combination (norm := abel_nf) hΦT'

include hT hanti in
/-- A nonincreasing nonnegative multiplier times an interval integrable covector function is
interval integrable. -/
theorem intervalIntegrable_lam_smul (hlam : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ lam t) (hlamT : lam T = 0)
    {gd : ℝ → E →L[ℝ] ℝ} (hgd : IntervalIntegrable gd volume 0 T) :
    IntervalIntegrable (fun r => lam r • gd r) volume 0 T := by
  set μ := multiplierMeasure hT hanti with hμ
  have hrm := rightMultiplier_ae_eq hT hanti
  have hreal : ∀ r ∈ Icc (0 : ℝ) T, μ.real (Ioc r T) = rightMultiplier T lam r :=
    fun r _ => real_Ioc_multiplierMeasure hT hanti hlam hlamT r
  have hrmgd : IntervalIntegrable (fun r => rightMultiplier T lam r • gd r) volume 0 T := by
    have h1 := intervalIntegrable_real_Ioc_tail_smul μ hT hgd
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at h1 ⊢
    refine h1.congr_fun (fun r hr => ?_) measurableSet_Ioc
    simp only
    rw [hreal r ⟨hr.1.le, hr.2⟩]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at hrmgd ⊢
  refine hrmgd.congr_fun_ae ?_
  filter_upwards [ae_restrict_of_ae hrm, ae_restrict_mem measurableSet_Ioc] with r h1 h2
  rw [h1 ⟨h2.1.le, h2.2⟩]

end Wiring

section CostateForm

variable {T : ℝ} {lam : ℝ → ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (hT : 0 ≤ T) (hanti : AntitoneOn lam (Icc (0 : ℝ) T))

include hT hanti in
/-- A function continuous on `[0,T]` is integrable for the multiplier measure (carried by
`[0,T]`). -/
theorem integrable_multiplierMeasure_of_continuousOn (hlamT : lam T = 0) {w : ℝ → E →L[ℝ] ℝ}
    (hw : ContinuousOn w (Icc (0 : ℝ) T)) : Integrable w (multiplierMeasure hT hanti) := by
  have hrestrict : (multiplierMeasure hT hanti).restrict (Icc (0 : ℝ) T)
      = multiplierMeasure hT hanti :=
    Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1
      (multiplierMeasure_compl_Icc hT hanti hlamT) |>.mono fun x hx => not_not.1 hx)
  rw [← hrestrict]
  exact hw.integrableOn_Icc

include hT hanti in
/-- **The library's measure-tail costate of the multiplier measure** equals
`−q − ∫_{(t,T]} g dμ` on `[0,T]`: `MeasureAdjoint.costate μ (−g) (−q)`. -/
theorem costate_multiplierMeasure_eq (hlamT : lam T = 0)
    {g : ℝ → E →L[ℝ] ℝ} (hg : ContinuousOn g (Icc (0 : ℝ) T)) (q : E →L[ℝ] ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    MeasureAdjoint.costate (multiplierMeasure hT hanti) (fun s => -g s) (-q) t
      = -q - ∫ s in Ioc t T, g s ∂(multiplierMeasure hT hanti) := by
  set μ := multiplierMeasure hT hanti with hμ
  have hint : Integrable g μ := integrable_multiplierMeasure_of_continuousOn hT hanti hlamT hg
  have hu : Ioi t = Ioc t T ∪ Ioi T := by
    ext x; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro h; by_cases hx : x ≤ T
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (not_le.1 hx)
    · rintro (h | h)
      · exact h.1
      · exact lt_of_le_of_lt ht.2 h
  have hz : μ.restrict (Ioi T) = 0 := Measure.restrict_eq_zero.2
    (multiplierMeasure_Ioi_horizon hT hanti hlamT)
  have hcongr : ∫ s in Ioi t, -g s ∂μ = ∫ s in Ioc t T, -g s ∂μ := by
    have hdisj : Disjoint (Ioc t T) (Ioi T) :=
      Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx')
    have hU := Measure.restrict_union (μ := μ) hdisj measurableSet_Ioi
    rw [hu, hU, hz, add_zero]
  simp only [MeasureAdjoint.costate, openIntegralTail]
  rw [hcongr, integral_neg]
  abel

end CostateForm

section Final

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

/-- **The Stieltjes-measure form of the limit costate equation.**  For a nonincreasing multiplier
`lam` on `[0,T]`, with `μ = multiplierMeasure lam`: `μ` is a finite positive measure carried by
`[0,T]` with tail masses `μ(t,T] = λ(t⁺)`; the limit momentum `∂ᵥL(γL,γL')` equals, a.e., the
library measure-tail costate `MeasureAdjoint.costate μ (−∇G(·,γL)) (−∂₂Φ₁)` minus the Lebesgue tail
of `∂ₓL`, i.e. `−∂₂Φ₁ − ∫_t^T ∂ₓL − ∫_{(t,T]} ∇G dμ`; `μ` is carried by the contact set; and under
Assumption 11.4.1 it has no mass near the endpoints.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Theorem 11.4.4 (ii)-(iv). -/
def StieltjesCostateForm (Lx Lv : ℝ → E → E → E →L[ℝ] ℝ) (G : ℝ → E → ℝ)
    (Gx : ℝ → E → E →L[ℝ] ℝ) (Φ₁ : E × E → ℝ) (γL : VelocityTrajectory P) (lam : ℝ → ℝ)
    (hanti : AntitoneOn lam (Icc (0 : ℝ) P.horizon)) : Prop :=
  multiplierMeasure P.horizon_pos.le hanti univ = ENNReal.ofReal (lam 0) ∧
  multiplierMeasure P.horizon_pos.le hanti (Icc (0 : ℝ) P.horizon)ᶜ = 0 ∧
  (∀ t ∈ Icc (0 : ℝ) P.horizon, multiplierMeasure P.horizon_pos.le hanti (Ioc t P.horizon)
    = ENNReal.ofReal (rightMultiplier P.horizon lam t)) ∧
  (∀ᵐ t ∂(timeMeasure P.horizon), Lv t (γL.value t) (γL.velocity t)
    = MeasureAdjoint.costate (multiplierMeasure P.horizon_pos.le hanti)
        (fun s => -Gx s (γL.value s))
        (-((fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp (ContinuousLinearMap.inr ℝ E E))) t
      - ∫ r in t..P.horizon, Lx r (γL.value r) (γL.velocity r)) ∧
  (∀ α β : ℝ, α ∈ Icc (0 : ℝ) P.horizon → β ∈ Icc (0 : ℝ) P.horizon → α < β →
    (∀ r ∈ Icc α β, G r (γL.value r) < 0) →
      multiplierMeasure P.horizon_pos.le hanti (Ioo α β) = 0) ∧
  ((∃ δ : ℝ, 0 < δ ∧ δ < P.horizon ∧ ∀ t ∈ Icc (0 : ℝ) P.horizon,
      (t < δ ∨ P.horizon - δ < t) → G t (γL.value t) < 0) →
    ∃ δ : ℝ, 0 < δ ∧ multiplierMeasure P.horizon_pos.le hanti (Iio δ) = 0 ∧
      multiplierMeasure P.horizon_pos.le hanti (Ioi (P.horizon - δ)) = 0)

/-- **Item 3 (Stieltjes rendering of the limit `λ`).**  The limit of the penalised multipliers
(`PenalisedMultiplierLimit`) is a nonincreasing `λ` whose Lebesgue–Stieltjes measure `μ` makes the
limit costate equation hold in the library's measure-tail form (`StieltjesCostateForm`).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Theorem 11.4.4. -/
theorem PenalisedMultiplierLimit.exists_stieltjesCostateForm
    {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}
    (hD : IsCaratheodoryC1 P.horizon L Lx Lv) {ω ω' : ℝ → ℝ}
    {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)} (hGx : StateGradientRegularity Gx Gxd)
    {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ} {seq : PenalisedMinimiserSequence P L G ω Φ₀ Φ₁}
    {γL : VelocityTrajectory P} {M : ℝ}
    (hlim : PenalisedMultiplierLimit Lx Lv ω' G Gx Gxd seq γL M) :
    ∃ (lam : ℝ → ℝ) (hanti : AntitoneOn lam (Icc (0 : ℝ) P.horizon)),
      (∀ t ∈ Icc (0 : ℝ) P.horizon, 0 ≤ lam t ∧ lam t ≤ M) ∧ lam P.horizon = 0 ∧
      StieltjesCostateForm Lx Lv G Gx Φ₁ γL lam hanti := by
  classical
  obtain ⟨φ, lam, hφ, htend, hanti, hbd, hlamT, hder, h0, hTT, hmom, hcompl, hend⟩ := hlim
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  refine ⟨lam, hanti, hbd, hlamT, ?_⟩
  have hlam : ∀ t ∈ Icc (0 : ℝ) P.horizon, 0 ≤ lam t := fun t ht => (hbd t ht).1
  obtain ⟨hgint, hgprim⟩ := γL.gradientAlongPath_eq_primitive hGx
  have haL : IntervalIntegrable (fun r => Lx r (γL.value r) (γL.velocity r)) volume 0 P.horizon :=
    intervalIntegrable_of_memLp hT (memLp_stateGradient hD hT γL.memLp_velocity γL.initial)
  have hgcont : ContinuousOn (fun t => Gx t (γL.value t)) (Icc (0 : ℝ) P.horizon) := by
    have hprim : ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, Gxd r (γL.value r) (1, γL.velocity r))
        (Icc (0 : ℝ) P.horizon) := by
      have := intervalIntegral.continuousOn_primitive_interval' (a := (0 : ℝ)) hgint
        (by simp [uIcc, hT] : (0 : ℝ) ∈ [[0, P.horizon]])
      rwa [uIcc_of_le hT] at this
    exact (continuousOn_const.add hprim).congr hgprim
  have htail := momentum_eq_stieltjesTail hT hanti hlam hlamT haL hgint hgprim hTT hmom
  refine ⟨multiplierMeasure_univ hT hanti hlamT, multiplierMeasure_compl_Icc hT hanti hlamT,
    fun t ht => multiplierMeasure_Ioc_horizon hT hanti hlamT t, ?_, ?_, ?_⟩
  · filter_upwards [htail, ae_restrict_mem measurableSet_Ioc] with t h1 h2
    have ht : t ∈ Icc (0 : ℝ) P.horizon := ⟨h2.1.le, h2.2⟩
    rw [costate_multiplierMeasure_eq hT hanti hlamT hgcont _ ht, h1]
    abel
  · intro α β hα hβ hαβ hslack
    exact multiplierMeasure_Ioo_eq_zero_of_const hT hanti hαβ
      (fun r hr => ⟨hα.1.trans hr.1, hr.2.trans hβ.2⟩) (hcompl α β hα hβ hslack)
  · intro hslack
    obtain ⟨δ, hδ, hδT, hsl⟩ := hslack
    obtain ⟨hconst0, hconstT⟩ := hend δ hδ hδT hsl
    have hTpos := P.horizon_pos
    set δ₂ := min (δ / 2) (P.horizon / 2) with hδ₂
    have hδ₂pos : 0 < δ₂ := lt_min (by linarith) (by linarith)
    have hδ₂1 : δ₂ ≤ δ / 2 := min_le_left _ _
    have hδ₂2 : δ₂ ≤ P.horizon / 2 := min_le_right _ _
    refine ⟨δ₂, hδ₂pos, ?_, ?_⟩
    · have hsub : Icc (0 : ℝ) δ₂ ⊆ Icc (0 : ℝ) P.horizon := fun r hr =>
        ⟨hr.1, hr.2.trans (by linarith)⟩
      have hc : ∀ t ∈ Icc (0 : ℝ) δ₂, lam t = lam 0 := fun t ht =>
        hconst0 t ⟨ht.1, ht.2.trans hδ₂1⟩
      have hrm0 := rightMultiplier_eq_of_const hsub hc (s := 0) ⟨le_rfl, hδ₂pos⟩
      have hIic := multiplierMeasure_Iic_zero hT hanti
      rw [hrm0, sub_self, ENNReal.ofReal_zero] at hIic
      have hIoo := multiplierMeasure_Ioo_eq_zero_of_const hT hanti hδ₂pos hsub hc
      have hU : Iio δ₂ = Iic 0 ∪ Ioo 0 δ₂ := by
        ext x; simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
        constructor
        · intro h; by_cases hx : x ≤ 0
          · exact Or.inl hx
          · exact Or.inr ⟨not_le.1 hx, h⟩
        · rintro (h | h)
          · linarith
          · exact h.2
      rw [hU]
      exact measure_union_null hIic hIoo
    · have hα : P.horizon - δ₂ ∈ Icc (0 : ℝ) P.horizon := ⟨by linarith, by linarith⟩
      have hsub : Icc (P.horizon - δ₂) P.horizon ⊆ Icc (0 : ℝ) P.horizon := fun r hr =>
        ⟨hα.1.trans hr.1, hr.2⟩
      have hc : ∀ t ∈ Icc (P.horizon - δ₂) P.horizon, lam t = lam (P.horizon - δ₂) := fun t ht => by
        rw [hconstT t ⟨by linarith [ht.1], ht.2⟩,
          hconstT (P.horizon - δ₂) ⟨by linarith, by linarith⟩]
      have hrm := rightMultiplier_eq_of_const hsub hc (s := P.horizon - δ₂)
        ⟨le_rfl, by linarith⟩
      have hIoc := multiplierMeasure_Ioc_horizon hT hanti hlamT (P.horizon - δ₂)
      have hlz : lam (P.horizon - δ₂) = 0 := hconstT _ ⟨by linarith, by linarith⟩
      rw [hrm, hlz, ENNReal.ofReal_zero] at hIoc
      have hU : Ioi (P.horizon - δ₂) = Ioc (P.horizon - δ₂) P.horizon ∪ Ioi P.horizon := by
        ext x; simp only [mem_Ioi, mem_union, mem_Ioc]
        constructor
        · intro h; by_cases hx : x ≤ P.horizon
          · exact Or.inl ⟨h, hx⟩
          · exact Or.inr (not_le.1 hx)
        · rintro (h | h)
          · exact h.1
          · linarith
      rw [hU]
      exact measure_union_null hIoc (multiplierMeasure_Ioi_horizon hT hanti hlamT)

end Final

end OptimalControl.BoundedState
