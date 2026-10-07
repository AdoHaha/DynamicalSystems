/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.StateMultiplierLimit

/-!
# The convergence data of Lemma 11.3.5 for the `j → ∞` limit

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5, §11.4.

`StateMultiplierLimit.lean` takes the convergence data of Lemma 11.3.5 as hypotheses
(`hpath`, `hLx`, `hGd`, `hLv`).  This file derives them from the primitive output of the lemma:
**uniform convergence of the paths and strong `L²` convergence of the velocities** of the
penalised minimisers, together with continuity of the first-order data in `(y,w)`.

* `tendsto_integral_of_L1_dominated`: a Pratt-type dominated convergence theorem with
  `L¹`-convergent dominators (dominated convergence applied to `min(u_n, |H|)`).
* `tendsto_integral_norm_sub_nemytskii`: the Nemytskii operator `(y,w) ↦ N(t,y(t),w(t))` of a
  Carathéodory integrand with linear growth in `w` is `L¹`-continuous along uniformly convergent
  paths and `L¹`-convergent velocities.
* `PenalisedMinimiserSequence.comp`: reindexing along a subsequence.
* `PenalisedMinimiserSequence.exists_convergenceData`: the subsequence along which
  `hpath`, `hLx`, `hGd` and `hLv` hold.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter ACEulerLagrange
open scoped Topology Interval ENNReal

namespace OptimalControl.BoundedState

section Pratt

variable {ν : Measure ℝ}

/-- **Dominated convergence with `L¹`-convergent dominators.**  If `0 ≤ u_n ≤ H_n`,
`u_n → 0` a.e. and `H_n → H` in `L¹`, then `∫ u_n → 0`.

The proof applies ordinary dominated convergence to `min(u_n, |H|)` and uses
`u_n ≤ min(u_n,|H|) + |H_n − H|`. -/
theorem tendsto_integral_of_L1_dominated {u H' : ℕ → ℝ → ℝ} {H : ℝ → ℝ}
    (hu0 : ∀ n, ∀ᵐ t ∂ν, 0 ≤ u n t) (hum : ∀ n, AEStronglyMeasurable (u n) ν)
    (hHn : ∀ n, Integrable (H' n) ν) (hH : Integrable H ν)
    (hdom : ∀ n, ∀ᵐ t ∂ν, u n t ≤ H' n t)
    (hlim : ∀ᵐ t ∂ν, Tendsto (fun n => u n t) atTop (𝓝 0))
    (hL1 : Tendsto (fun n => ∫ t, ‖H' n t - H t‖ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, u n t ∂ν) atTop (𝓝 0) := by
  have hmin : Tendsto (fun n => ∫ t, min (u n t) |H t| ∂ν) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun n t => min (u n t) |H t|) (f := fun _ => (0 : ℝ)) (bound := fun t => |H t|)
      (fun n => ((hum n).aemeasurable.min hH.abs.aemeasurable).aestronglyMeasurable) hH.abs
      (fun n => by
        filter_upwards [hu0 n] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min ht (abs_nonneg _))]
        exact min_le_right _ _)
      (by
        filter_upwards [hlim] with t ht
        have : Tendsto (fun n => min (u n t) |H t|) atTop (𝓝 (min 0 |H t|)) :=
          ht.min tendsto_const_nhds
        simpa [min_eq_left (abs_nonneg (H t))] using this)
    simpa using this
  have hsum : Tendsto (fun n => (∫ t, min (u n t) |H t| ∂ν) + ∫ t, ‖H' n t - H t‖ ∂ν) atTop
      (𝓝 0) := by simpa using hmin.add hL1
  refine squeeze_zero' (Eventually.of_forall fun n => integral_nonneg_of_ae (hu0 n)) ?_ hsum
  refine Eventually.of_forall fun n => ?_
  have hint1 : Integrable (fun t => min (u n t) |H t|) ν :=
    hH.abs.mono' ((hum n).aemeasurable.min hH.abs.aemeasurable).aestronglyMeasurable
      (by filter_upwards [hu0 n] with t ht
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min ht (abs_nonneg _))]
          exact min_le_right _ _)
  have hint2 : Integrable (fun t => ‖H' n t - H t‖) ν := ((hHn n).sub hH).norm
  have hint0 : Integrable (u n) ν := by
    refine (hHn n).mono' (hum n) ?_
    filter_upwards [hu0 n, hdom n] with t h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    exact h2
  rw [← integral_add hint1 hint2]
  refine integral_mono_ae hint0 (hint1.add hint2) ?_
  filter_upwards [hu0 n, hdom n] with t h1 h2
  change u n t ≤ min (u n t) |H t| + ‖H' n t - H t‖
  rw [Real.norm_eq_abs]
  rcases le_total (u n t) |H t| with h | h
  · rw [min_eq_left h]; exact le_add_of_nonneg_right (abs_nonneg _)
  · rw [min_eq_right h]
    have : H' n t ≤ H t + |H' n t - H t| := by
      have := le_abs_self (H' n t - H t); linarith
    have := le_abs_self (H t)
    linarith

end Pratt

section Nemytskii

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- `L¹` convergence implies convergence in measure (for integrable functions). -/
theorem tendstoInMeasure_of_tendsto_integral_norm {ν : Measure ℝ} {f : ℕ → ℝ → E} {g : ℝ → E}
    (hf : ∀ n, Integrable (f n) ν) (hg : Integrable g ν)
    (h : Tendsto (fun n => ∫ t, ‖f n t - g t‖ ∂ν) atTop (𝓝 0)) :
    TendstoInMeasure ν f atTop g := by
  refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero ?_
  have heq : ∀ n, eLpNorm (f n - g) 1 ν = ENNReal.ofReal (∫ t, ‖f n t - g t‖ ∂ν) := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm ((hf n).sub hg).aestronglyMeasurable]
    exact (ofReal_integral_norm_eq_lintegral_enorm ((hf n).sub hg)).symm
  simp_rw [heq]
  simpa using ENNReal.tendsto_ofReal h

omit [SecondCountableTopology E] in
/-- **`L¹`-continuity of the Nemytskii operator** of a Carathéodory integrand `N(t,y,w)` with
linear growth in `w`: along paths converging pointwise (and bounded) and velocities converging in
`L¹`, `∫₀ᵀ ‖N(t,y_n,w_n) − N(t,y,w)‖ → 0`.

This is the engine that turns the strong `L²` convergence of Lemma 11.3.5 into the `L¹`
convergence `hLx`, `hGd` of `StateMultiplierLimit.lean`. -/
theorem tendsto_integral_norm_sub_nemytskii {T : ℝ} (hT : 0 ≤ T) {N : ℝ → E → E → F}
    (hmeas : Measurable fun p : ℝ × E × E => N p.1 p.2.1 p.2.2)
    (hcont : ∀ t, Continuous fun q : E × E => N t q.1 q.2) {a : ℝ → ℝ} {C R : ℝ} (hC : 0 ≤ C)
    (ha : IntervalIntegrable a volume 0 T)
    (hgrowth : ∀ t y w, ‖y‖ ≤ R → ‖N t y w‖ ≤ a t + C * ‖w‖)
    {y : ℕ → ℝ → E} {y' : ℝ → E} {w : ℕ → ℝ → E} {w' : ℝ → E}
    (hym : ∀ n, ContinuousOn (y n) (Icc 0 T)) (hy'm : ContinuousOn y' (Icc 0 T))
    (hwm : ∀ n, IntervalIntegrable (w n) volume 0 T) (hw'm : IntervalIntegrable w' volume 0 T)
    (hybd : ∀ n, ∀ t ∈ Icc (0 : ℝ) T, ‖y n t‖ ≤ R) (hy'bd : ∀ t ∈ Icc (0 : ℝ) T, ‖y' t‖ ≤ R)
    (hyconv : ∀ t ∈ Icc (0 : ℝ) T, Tendsto (fun n => y n t) atTop (𝓝 (y' t)))
    (hwconv : Tendsto (fun n => ∫ r in (0 : ℝ)..T, ‖w n r - w' r‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ r in (0 : ℝ)..T, ‖N r (y n r) (w n r) - N r (y' r) (w' r)‖)
      atTop (𝓝 0) := by
  classical
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T) with hν
  have hint : ∀ {f : ℝ → ℝ}, IntervalIntegrable f volume 0 T → Integrable f ν := fun hf =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hf
  have hintE : ∀ {f : ℝ → E}, IntervalIntegrable f volume 0 T → Integrable f ν := fun hf =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hf
  have hmem : ∀ᵐ t ∂ν, t ∈ Icc (0 : ℝ) T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ⟨ht.1.le, ht.2⟩
  have hconvert : ∀ f : ℝ → ℝ, ∫ r in (0 : ℝ)..T, f r = ∫ r, f r ∂ν := fun f =>
    intervalIntegral.integral_of_le hT
  simp_rw [hconvert]
  have haν : Integrable a ν := hint ha
  have hyaem : ∀ n, AEMeasurable (y n) ν := fun n =>
    ((hym n).mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have hy'aem : AEMeasurable y' ν := (hy'm.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have hNm : ∀ n, AEMeasurable (fun t => N t (y n t) (w n t)) ν := fun n =>
    hmeas.comp_aemeasurable (aemeasurable_id.prodMk ((hyaem n).prodMk
      (hwm n).1.aestronglyMeasurable.aemeasurable))
  have hN'm : AEMeasurable (fun t => N t (y' t) (w' t)) ν :=
    hmeas.comp_aemeasurable (aemeasurable_id.prodMk (hy'aem.prodMk
      hw'm.1.aestronglyMeasurable.aemeasurable))
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hwL1 : Tendsto (fun n => ∫ t, ‖w (ns n) t - w' t‖ ∂ν) atTop (𝓝 0) := by
    have := hwconv.comp hns
    simpa only [Function.comp_def, hconvert] using this
  have hmeasure := tendstoInMeasure_of_tendsto_integral_norm (f := fun n => w (ns n))
    (fun n => hintE (hwm (ns n))) (hintE hw'm) hwL1
  obtain ⟨ms, hms, hae⟩ := hmeasure.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  -- the dominated-convergence data along `ns ∘ ms`
  set k : ℕ → ℕ := fun j => ns (ms j) with hk
  have hkt : Tendsto k atTop atTop := hns.comp hms.tendsto_atTop
  refine tendsto_integral_of_L1_dominated (ν := ν)
    (u := fun j t => ‖N t (y (k j) t) (w (k j) t) - N t (y' t) (w' t)‖)
    (H' := fun j t => (a t + C * ‖w (k j) t‖) + (a t + C * ‖w' t‖))
    (H := fun t => (a t + C * ‖w' t‖) + (a t + C * ‖w' t‖)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun j => Eventually.of_forall fun t => norm_nonneg _
  · exact fun j => ((hNm (k j)).sub hN'm).norm.aestronglyMeasurable
  · exact fun j => (haν.add ((hintE (hwm (k j))).norm.const_mul C)).add
      (haν.add ((hintE hw'm).norm.const_mul C))
  · exact (haν.add ((hintE hw'm).norm.const_mul C)).add (haν.add ((hintE hw'm).norm.const_mul C))
  · intro j
    filter_upwards [hmem] with t ht
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact hgrowth t _ _ (hybd _ t ht)
    · exact hgrowth t _ _ (hy'bd t ht)
  · filter_upwards [hmem, hae] with t ht htw
    have h1 : Tendsto (fun j => (y (k j) t, w (k j) t)) atTop (𝓝 (y' t, w' t)) :=
      ((hyconv t ht).comp hkt).prodMk_nhds htw
    have h2 := ((hcont t).tendsto (y' t, w' t)).comp h1
    exact tendsto_iff_norm_sub_tendsto_zero.1 h2
  · have hb : Tendsto (fun j => C * ∫ t, ‖w (k j) t - w' t‖ ∂ν) atTop (𝓝 0) := by
      have := (hwL1.comp hms.tendsto_atTop).const_mul C
      rw [mul_zero] at this
      exact this
    refine squeeze_zero (fun j => integral_nonneg fun t => norm_nonneg _) (fun j => ?_) hb
    rw [← integral_const_mul]
    refine integral_mono ?_ ?_ ?_
    · have h1 := ((haν.add ((hintE (hwm (k j))).norm.const_mul C)).add
        (haν.add ((hintE hw'm).norm.const_mul C)))
      have h2 := ((haν.add ((hintE hw'm).norm.const_mul C)).add
        (haν.add ((hintE hw'm).norm.const_mul C)))
      exact (h1.sub h2).norm
    · exact (((hintE (hwm (k j))).sub (hintE hw'm)).norm).const_mul C
    · intro t
      beta_reduce
      have : (a t + C * ‖w (k j) t‖ + (a t + C * ‖w' t‖)) - (a t + C * ‖w' t‖ + (a t + C * ‖w' t‖))
          = C * (‖w (k j) t‖ - ‖w' t‖) := by ring
      rw [this, norm_mul, Real.norm_of_nonneg hC]
      exact mul_le_mul_of_nonneg_left (by
        simpa using abs_norm_sub_norm_le (w (k j) t) (w' t)) hC

end Nemytskii

section L2toL1

variable {E : Type*} [NormedAddCommGroup E]

/-- Strong `L²` convergence to zero implies `L¹` convergence to zero on `[0,T]`
(`‖x‖ ≤ ‖x‖²/(2δ) + δ/2`). -/
theorem tendsto_integral_norm_of_sq {T : ℝ} (hT : 0 < T) {f : ℕ → ℝ → E}
    (h1 : ∀ n, IntervalIntegrable (fun r => ‖f n r‖) volume 0 T)
    (h2 : ∀ n, IntervalIntegrable (fun r => ‖f n r‖ ^ 2) volume 0 T)
    (h : Tendsto (fun n => ∫ r in (0 : ℝ)..T, ‖f n r‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ r in (0 : ℝ)..T, ‖f n r‖) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha
    (intervalIntegral.integral_nonneg hT.le fun r _ => norm_nonneg _), fun b hb => ?_⟩
  have hb2 : 0 < b ^ 2 / T := by positivity
  filter_upwards [(tendsto_order.1 h).2 _ hb2] with n hn
  have hpt : ∀ r ∈ Icc (0 : ℝ) T, ‖f n r‖ ≤ ‖f n r‖ ^ 2 / (2 * (b / T)) + (b / T) / 2 := by
    intro r _
    have hδ : 0 < b / T := by positivity
    rw [← sub_nonneg]
    have : ‖f n r‖ ^ 2 / (2 * (b / T)) + (b / T) / 2 - ‖f n r‖
        = (‖f n r‖ - b / T) ^ 2 / (2 * (b / T)) := by
      field_simp; ring
    rw [this]; positivity
  have hint : IntervalIntegrable (fun r => ‖f n r‖ ^ 2 / (2 * (b / T)) + (b / T) / 2) volume 0 T :=
    ((h2 n).div_const _).add intervalIntegrable_const
  calc ∫ r in (0 : ℝ)..T, ‖f n r‖
      ≤ ∫ r in (0 : ℝ)..T, (‖f n r‖ ^ 2 / (2 * (b / T)) + (b / T) / 2) :=
        intervalIntegral.integral_mono_on hT.le (h1 n) hint hpt
    _ = (∫ r in (0 : ℝ)..T, ‖f n r‖ ^ 2) / (2 * (b / T)) + T * ((b / T) / 2) := by
        rw [intervalIntegral.integral_add ((h2 n).div_const _) intervalIntegrable_const,
          intervalIntegral.integral_div]
        simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    _ < b := by
        have hδ : 0 < b / T := by positivity
        have : (∫ r in (0 : ℝ)..T, ‖f n r‖ ^ 2) / (2 * (b / T)) < b / 2 := by
          rw [div_lt_iff₀ (by positivity)]
          have : b ^ 2 / T * T = b ^ 2 := by field_simp
          nlinarith [hn, mul_pos hb hT, show (b / T) * T = b by field_simp]
        have e : T * ((b / T) / 2) = b / 2 := by field_simp
        linarith

end L2toL1

section Data

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

/-- Reindex a sequence of penalised minimisers along a subsequence. -/
def PenalisedMinimiserSequence.comp {L : ℝ → E → E → ℝ} {G : ℝ → E → ℝ} {ω : ℝ → ℝ}
    {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ} (seq : PenalisedMinimiserSequence P L G ω Φ₀ Φ₁)
    (φ : ℕ → ℕ) : PenalisedMinimiserSequence P L G ω Φ₀ Φ₁ where
  path n := seq.path (φ n)
  penalty n := seq.penalty (φ n)
  penalty_nonneg n := seq.penalty_nonneg (φ n)
  functional n := seq.functional (φ n)
  competitors n := seq.competitors (φ n)
  functional_eq n := seq.functional_eq (φ n)
  isMinOn n := seq.isMinOn (φ n)
  interior n := seq.interior (φ n)
  integrable n := seq.integrable (φ n)
  differentiable₀ n := seq.differentiable₀ (φ n)
  differentiable₁ n := seq.differentiable₁ (φ n)

/-- **The `L¹` and a.e. convergence data of Lemma 11.3.5 from uniform convergence of the paths and
strong `L²` convergence of the velocities.**

For continuous first-order data `∂ₓL, ∂ᵥL, ∇²G(·)(1,·)` (continuity in `(y,w)`), uniform
convergence of the paths `γ_n → γL` and `‖γ_n' − γL'‖_{L²} → 0` give

* `∂ₓL(γ_n,γ_n') → ∂ₓL(γL,γL')` and `∇²G(γ_n)(1,γ_n') → ∇²G(γL)(1,γL')` in `L¹`
  (the hypotheses `hLx`, `hGd` of `exists_stateMultiplier_limit_of_penalisedMinimisers`);
* along a subsequence, `∂ᵥL(γ_n,γ_n') → ∂ᵥL(γL,γL')` a.e. (`hLv`).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5, (11.3.24). -/
theorem PenalisedMinimiserSequence.convergenceData
    {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}
    (hD : IsCaratheodoryC1 P.horizon L Lx Lv)
    (hLxc : ∀ t, Continuous fun q : E × E => Lx t q.1 q.2)
    (hLvc : ∀ t, Continuous fun q : E × E => Lv t q.1 q.2)
    {Gx : ℝ → E → E →L[ℝ] ℝ} {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)}
    (hGx : StateGradientRegularity Gx Gxd)
    (hGdc : ∀ t, Continuous fun q : E × E => Gxd t q.1 (1, q.2))
    {G : ℝ → E → ℝ} {ω : ℝ → ℝ} {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ}
    (seq : PenalisedMinimiserSequence P L G ω Φ₀ Φ₁) (γL : VelocityTrajectory P)
    (hpath : ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) P.horizon,
      dist ((seq.path n).value t) (γL.value t) < ε)
    (hvel : Tendsto (fun n => ∫ r in (0 : ℝ)..P.horizon,
      ‖(seq.path n).velocity r - γL.velocity r‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ r in (0 : ℝ)..P.horizon,
      ‖Lx r ((seq.path n).value r) ((seq.path n).velocity r)
        - Lx r (γL.value r) (γL.velocity r)‖) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ r in (0 : ℝ)..P.horizon,
      ‖Gxd r ((seq.path n).value r) (1, (seq.path n).velocity r)
        - Gxd r (γL.value r) (1, γL.velocity r)‖) atTop (𝓝 0) ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ t ∂(timeMeasure P.horizon), Tendsto
      (fun n => Lv t ((seq.path (φ n)).value t) ((seq.path (φ n)).velocity t)) atTop
      (𝓝 (Lv t (γL.value t) (γL.velocity t))) := by
  classical
  have hTpos := P.horizon_pos
  have hT : 0 ≤ P.horizon := hTpos.le
  -- boundedness of the paths
  obtain ⟨R₀, hR₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P.horizon)).exists_bound_of_continuousOn
    γL.continuousOn_value
  obtain ⟨N₀, hN₀⟩ := (hpath 1 one_pos).exists_forall_of_atTop
  set R : ℝ := R₀ + 1 with hR
  have hybd : ∀ n, ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖(seq.path (n + N₀)).value t‖ ≤ R := by
    intro n t ht
    have h1 := hN₀ (n + N₀) (Nat.le_add_left _ _) t ht
    have h2 := hR₀ t ht
    have := norm_le_of_mem_closedBall (le_of_lt h1)
    calc ‖(seq.path (n + N₀)).value t‖
        = ‖(seq.path (n + N₀)).value t - γL.value t + γL.value t‖ := by rw [sub_add_cancel]
      _ ≤ ‖(seq.path (n + N₀)).value t - γL.value t‖ + ‖γL.value t‖ := norm_add_le _ _
      _ ≤ R := by
          have : ‖(seq.path (n + N₀)).value t - γL.value t‖ < 1 := by
            simpa [dist_eq_norm] using h1
          linarith
  have hy'bd : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖γL.value t‖ ≤ R := fun t ht => by
    have := hR₀ t ht; linarith
  have hpt : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      Tendsto (fun n => (seq.path n).value t) atTop (𝓝 (γL.value t)) := fun t ht =>
    Metric.tendsto_nhds.2 fun ε hε => (hpath ε hε).mono fun n hn => hn t ht
  have hptS : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      Tendsto (fun n => (seq.path (n + N₀)).value t) atTop (𝓝 (γL.value t)) := fun t ht =>
    (hpt t ht).comp (tendsto_add_atTop_nat N₀)
  -- `L¹` convergence of the velocities
  have hvmem : ∀ n, MemLp (fun r => (seq.path n).velocity r - γL.velocity r) 2
      (timeMeasure P.horizon) := fun n =>
    (seq.path n).memLp_velocity.sub γL.memLp_velocity
  have hw1 : Tendsto (fun n => ∫ r in (0 : ℝ)..P.horizon,
      ‖(seq.path n).velocity r - γL.velocity r‖) atTop (𝓝 0) := by
    refine tendsto_integral_norm_of_sq hTpos (f := fun n r =>
      (seq.path n).velocity r - γL.velocity r) (fun n => ?_) (fun n => ?_) hvel
    · exact (intervalIntegrable_of_memLp hT (hvmem n)).norm
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 (hvmem n).norm.integrable_sq
  have hw1S : Tendsto (fun n => ∫ r in (0 : ℝ)..P.horizon,
      ‖(seq.path (n + N₀)).velocity r - γL.velocity r‖) atTop (𝓝 0) :=
    hw1.comp (tendsto_add_atTop_nat N₀)
  have hyS : ∀ n, ContinuousOn (seq.path (n + N₀)).value (Icc 0 P.horizon) := fun n =>
    (seq.path (n + N₀)).continuousOn_value
  have hwS : ∀ n, IntervalIntegrable (seq.path (n + N₀)).velocity volume 0 P.horizon := fun n =>
    (seq.path (n + N₀)).velocity_intervalIntegrable
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, C, haL, hC, hgr⟩ := hD.growth R
    have := tendsto_integral_norm_sub_nemytskii hT (N := Lx) hD.measurable_Lx hLxc hC
      (intervalIntegrable_of_memLp hT haL) (fun t y w hy => (hgr t y w hy).1) hyS
      γL.continuousOn_value hwS γL.velocity_intervalIntegrable hybd hy'bd hptS hw1S
    exact (tendsto_add_atTop_iff_nat N₀).1 this
  · obtain ⟨C₁, hC₁, hC₁b⟩ := hGx.bounded R
    have hev : Measurable (fun p : ((ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)) × (ℝ × E) => p.1 p.2) :=
      (continuous_fst.clm_apply continuous_snd).measurable
    have hmeasG : Measurable fun p : ℝ × E × E => Gxd p.1 p.2.1 (1, p.2.2) :=
      hev.comp ((hGx.measurable.comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
          (measurable_const.prodMk (measurable_snd.comp measurable_snd)))
    have hgr : ∀ t (y w : E), ‖y‖ ≤ R → ‖Gxd t y (1, w)‖ ≤ C₁ + C₁ * ‖w‖ := by
      intro t y w hy
      calc ‖Gxd t y (1, w)‖ ≤ ‖Gxd t y‖ * ‖((1 : ℝ), w)‖ := (Gxd t y).le_opNorm _
        _ ≤ C₁ * (1 + ‖w‖) := by
            refine mul_le_mul (hC₁b t y hy) ?_ (norm_nonneg _) hC₁
            rw [Prod.norm_def, norm_one]
            exact max_le (by linarith [norm_nonneg w]) (by linarith)
        _ = C₁ + C₁ * ‖w‖ := by ring
    have := tendsto_integral_norm_sub_nemytskii hT (N := fun t y w => Gxd t y (1, w)) hmeasG
      hGdc hC₁ (a := fun _ => C₁) intervalIntegrable_const hgr hyS γL.continuousOn_value hwS
      γL.velocity_intervalIntegrable hybd hy'bd hptS hw1S
    exact (tendsto_add_atTop_iff_nat N₀).1 this
  · -- a.e. convergent subsequence of the velocities
    have hν1 : ∀ n, Integrable (fun r => (seq.path n).velocity r) (timeMeasure P.horizon) :=
      fun n => (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
        (seq.path n).velocity_intervalIntegrable
    have hν2 : Integrable γL.velocity (timeMeasure P.horizon) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 γL.velocity_intervalIntegrable
    have hconv : ∀ f : ℝ → ℝ, ∫ r in (0 : ℝ)..P.horizon, f r
        = ∫ r, f r ∂(timeMeasure P.horizon) := fun f => intervalIntegral.integral_of_le hT
    have hw1ν : Tendsto (fun n => ∫ r, ‖(seq.path n).velocity r - γL.velocity r‖
        ∂(timeMeasure P.horizon)) atTop (𝓝 0) := by simpa only [hconv] using hw1
    obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_integral_norm
      (f := fun n => (seq.path n).velocity) hν1 hν2 hw1ν).exists_seq_tendsto_ae
    refine ⟨φ, hφ, ?_⟩
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with t h1 h2
    have ht : t ∈ Icc (0 : ℝ) P.horizon := ⟨h2.1.le, h2.2⟩
    have hq : Tendsto (fun n => ((seq.path (φ n)).value t, (seq.path (φ n)).velocity t)) atTop
        (𝓝 (γL.value t, γL.velocity t)) :=
      ((hpt t ht).comp hφ.tendsto_atTop).prodMk_nhds h1
    exact ((hLvc t).tendsto _).comp hq

end Data

end OptimalControl.BoundedState
