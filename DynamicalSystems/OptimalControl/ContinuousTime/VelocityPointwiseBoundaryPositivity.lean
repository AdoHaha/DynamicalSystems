/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwisePenaltyMinimizer
public import DynamicalSystems.Mathlib.Topology.ClusterPointLimit

/-!
# Boundary positivity and the strict-interior minimiser for the pointwise-defect penalty

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.3 and
Remark 11.6.6, rendered for the **pointwise velocity defect** `φ′(t) − f(φ(t),ν_t,t)` of §11.6
(the `K`-defect of `F_K` used by `VelocityPointwisePenaltyMinimizer.lean`).

The Volterra-residual versions live in `PenaltyBoundaryPositivity.lean`.  Two ingredients are
added here:

* a lower-semicontinuous form of the cluster-point zero lemma (the pointwise defect energy is only
  lower semicontinuous, unlike the continuous Volterra residual);
* the bridge between the conditional-law average `realizedVelocity` and the occupation integral
  `∫_{(0,t]×Ω} f dρ`, which identifies the pointwise defect on the *admissible graph* with the
  Volterra residual.

## Initial-condition anchor

The pointwise defect `φ′ − f(φ,ν_t,t)` does **not** reference the initial state `P.initial`,
whereas the Volterra residual `φ(t) − φ(0) − T∫f` does.  On the fixed-initial admissible set
`IsRelaxedAdmissible` (which requires `φ(0) = P.initial`) the two agree, because the bridge
identity turns `φ(t) = φ(0) + ∫₀ᵗ φ′` into `φ(0) = P.initial` plus the pointwise ODE.  Boundary
positivity over the fixed-initial optimal set therefore needs the initial mismatch to be part of
the `K`-weighted defect; the penalty carrying it is `lpPenaltyPointwiseAnchored` below, and the
main theorems are stated for it.  The book's §11.6 problem has a *free* initial state (the
initial value is only constrained through `T`), so the unanchored pointwise penalty matches the
book; the fixed-initial rendering of `Problem.IsRelaxedMinimum` used throughout this development
requires the anchor.  See `R1_PWSTRICT_REPORT.md` for the precise statement, the counterexample
for the unanchored functional, and the free-initial alternative.

Book citations appear only in docstrings; all names are concept names.
-/

@[expose] public section

open Set MeasureTheory Filter Metric
open scoped Topology Interval BoundedContinuousFunction ENNReal

namespace DynamicalSystems

/-- **Lower-semicontinuous cluster-point zero lemma.**  If `f` is lower semicontinuous and
nonnegative and `f (u n) ≤ g n` with `g → 0`, then every cluster point `a` of `u` satisfies
`f a = 0`.

This is the lower-semicontinuous form of
`eq_zero_of_mapClusterPt_of_continuous_of_nonneg_of_tendsto_zero` (the pointwise defect energy is
only lower semicontinuous).  It follows from `le_of_mapClusterPt_of_lowerSemicontinuous` by a
contradiction: a positive value `f a > 0` is witnessed on a neighbourhood of `a`, while `g n < f a`
eventually.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.3 (the limit is admissible). -/
theorem eq_zero_of_mapClusterPt_of_lowerSemicontinuous_of_nonneg_of_tendsto_zero
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : LowerSemicontinuous f)
    (hnonneg : ∀ x, 0 ≤ f x) {u : ℕ → X} {a : X} {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 0)) (ha : MapClusterPt a atTop u)
    (h : ∀ n, f (u n) ≤ g n) : f a = 0 := by
  have hfa : f a ≤ 0 := by
    by_contra hle
    push Not at hle
    obtain ⟨d, h0d, hda⟩ := exists_between hle
    have hnhds : ∀ᶠ x in 𝓝 a, d < f x := hf a d hda
    have hev : ∀ᶠ n : ℕ in atTop, g n < d := hg (Iio_mem_nhds h0d)
    obtain ⟨n, hn1, hn2⟩ := ((ha.frequently hnhds).and_eventually hev).exists
    linarith [h n]
  exact le_antisymm hfa (hnonneg a)

end DynamicalSystems

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

namespace Problem

/-! ## The conditional average and the occupation integral -/

omit [CompleteSpace E] in
/-- The control-averaged field `realizedVelocityOnLine` is interval-integrable on the horizon. -/
theorem intervalIntegrable_realizedVelocityOnLine (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) : IntervalIntegrable (realizedVelocityOnLine P x ρ) volume 0 P.horizon := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le P.horizon_pos.le]
  exact (realizedVelocityOnLine_memLp P x ρ).integrable (by norm_num)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- **Bridge between the conditional-law average and the occupation integral.**  The unnormalised
(`T`-weighted) occupation integral of the dynamics over `(0,t] × Ω` is the interval integral of
the control-averaged field `realizedVelocity` read on the real line.

This is the identity that makes the pointwise velocity defect integrate to the Volterra residual:
`f(φ(t),ν_t,t)` is `realizedVelocity`, and its primitive is `T ∫ f dρ`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.6.2) with the conditional law `ν_t = ρ.kernel t`. -/
theorem horizon_smul_setIntegral_eq_intervalIntegral_realizedVelocityOnLine
    (P : Problem E V W) (x : P.Trajectory) (ρ : P.Relaxed) (t : P.Time) :
    P.horizon •
        (∫ z in (Ioc (timeZero P.horizon P.horizon_pos.le) t) ×ˢ (univ : Set P.Control),
          P.dynamics z.1 (x z.1) (z.2 : V) ∂ρ.measure) =
      ∫ s in (0 : ℝ)..(t : ℝ), realizedVelocityOnLine P x ρ s := by
  have hT := P.horizon_pos
  have hcont : Continuous fun z : P.Time × P.Control =>
      P.dynamics z.1 (x z.1) (z.2 : V) := continuous_dynamics_trajectory P x
  have hint : IntegrableOn (fun z : P.Time × P.Control =>
      P.dynamics z.1 (x z.1) (z.2 : V))
      ((Ioc (timeZero P.horizon hT.le) t) ×ˢ (univ : Set P.Control)) ρ.measure :=
    (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).integrableOn
  rw [← OptimalControl.RelaxedControl.setIntegral_kernel ρ measurableSet_Ioc hint]
  exact OptimalControl.integral_horizon_prefix hT (fun s => realizedVelocity P x ρ s) t

/-- The primitive of the `L²` class of the control-averaged field is the interval integral of the
control-averaged field read on the real line. -/
theorem primitiveValue_realizedVelocityLp (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) (t : P.Time) :
    primitiveValue P.horizon (t : ℝ) (realizedVelocityLp P x ρ) =
      ∫ s in (0 : ℝ)..(t : ℝ), realizedVelocityOnLine P x ρ s := by
  have h1 : primitiveValue P.horizon (t : ℝ) (realizedVelocityLp P x ρ) =
      ∫ s in Ioc (0 : ℝ) (t : ℝ), realizedVelocityLp P x ρ s
        ∂(horizonMeasure P.horizon) := by
    rw [primitiveValue, setIntegralCLM_apply]
  rw [h1, integral_congr_ae (ae_restrict_of_ae (realizedVelocityLp_coeFn P x ρ)), horizonMeasure,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr (Ioc_subset_Ioc_right t.2.2),
    intervalIntegral.integral_of_le t.2.1]

/-- **The pointwise defect vanishes on the admissible graph.**  If `(toBoundedPath γ, ρ)` is an
admissible relaxed pair, then the raw velocity `γ.velocity` agrees almost everywhere with the
control-averaged dynamics `realizedVelocity`; equivalently the pointwise velocity defect is zero
a.e.  This is the pointwise counterpart of the fact that the Volterra residual vanishes on the
admissible graph.

The proof differentiates the Volterra identity `φ(t) = φ(0) + T∫f` using the bridge
`T∫f = ∫₀ᵗ realizedVelocity` and the fundamental theorem of calculus for interval integrals.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.6.2) and §11.6 (the pointwise and Volterra defects agree on admissible pairs). -/
theorem velocity_ae_eq_realizedVelocityOnLine_of_isRelaxedAdmissible
    (P : Problem E V W) (γ : VelocityTrajectory P) (ρ : P.Relaxed)
    (hadm : P.IsRelaxedAdmissible (toBoundedPath γ) ρ) :
    γ.velocity =ᵐ[horizonMeasure P.horizon]
      realizedVelocityOnLine P (toBoundedPath γ) ρ := by
  obtain ⟨htrail, -, -⟩ := hadm
  have hinit : γ.initial = P.initial := by
    have h := IsRelaxedTrajectory.initial htrail
    rw [toBoundedPath_apply] at h
    simp only [timeZero] at h
    simpa [VelocityTrajectory.value_zero] using h
  have hprim (t : P.Time) :
      ∫ s in (0 : ℝ)..(t : ℝ), γ.velocity s =
        ∫ s in (0 : ℝ)..(t : ℝ), realizedVelocityOnLine P (toBoundedPath γ) ρ s := by
    have ht := htrail t
    rw [toBoundedPath_apply, VelocityTrajectory.value] at ht
    simp only [Problem.relaxedDynamics] at ht
    rw [horizon_smul_setIntegral_eq_intervalIntegral_realizedVelocityOnLine P
      (toBoundedPath γ) ρ t, hinit] at ht
    exact add_left_cancel ht
  set h : ℝ → E := fun s =>
    γ.velocity s - realizedVelocityOnLine P (toBoundedPath γ) ρ s with hh
  have hzero (t : P.Time) : ∫ s in (0 : ℝ)..(t : ℝ), h s = 0 := by
    have hvel : IntervalIntegrable γ.velocity volume 0 (t : ℝ) :=
      γ.velocity_intervalIntegrable.mono_set (by
        simp only [uIcc_of_le t.2.1, uIcc_of_le P.horizon_pos.le]
        exact Icc_subset_Icc le_rfl t.2.2)
    have hreal : IntervalIntegrable (realizedVelocityOnLine P (toBoundedPath γ) ρ) volume 0
        (t : ℝ) :=
      (intervalIntegrable_realizedVelocityOnLine P (toBoundedPath γ) ρ).mono_set (by
        simp only [uIcc_of_le t.2.1, uIcc_of_le P.horizon_pos.le]
        exact Icc_subset_Icc le_rfl t.2.2)
    rw [hh, intervalIntegral.integral_sub hvel hreal, hprim t, sub_self]
  have hint : IntervalIntegrable h volume 0 P.horizon := by
    rw [hh]
    exact γ.velocity_intervalIntegrable.sub
      (intervalIntegrable_realizedVelocityOnLine P (toBoundedPath γ) ρ)
  have hderiv := hint.ae_hasDerivAt_integral
  rw [uIcc_of_le P.horizon_pos.le] at hderiv
  have haeIoo : h =ᵐ[volume.restrict (Ioo (0 : ℝ) P.horizon)] 0 := by
    change ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) P.horizon)), h x = 0
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hderiv] with x hd hx
    have hxIcc : x ∈ Icc (0 : ℝ) P.horizon := ⟨hx.1.le, hx.2.le⟩
    have hF0 : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, h s) 0 x := by
      have hev : (fun y : ℝ => ∫ s in (0 : ℝ)..y, h s) =ᶠ[𝓝 x] (fun _ => (0 : E)) :=
        Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) fun y hy =>
          hzero ⟨y, hy.1.le, hy.2.le⟩
      exact hev.hasDerivAt_iff.mpr (hasDerivAt_const x (0 : E))
    exact (hd hxIcc 0 ⟨le_rfl, P.horizon_pos.le⟩).unique hF0
  have hae : h =ᵐ[horizonMeasure P.horizon] 0 := by
    rw [horizonMeasure, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact haeIoo
  filter_upwards [hae] with s hs
  rw [hh] at hs
  exact sub_eq_zero.mp hs

/-- The pointwise defect energy vanishes at an admissible pair. -/
theorem pointwiseDefectEnergy_eq_zero_of_isRelaxedAdmissible
    (P : Problem E V W) (γ : VelocityTrajectory P) (ρ : P.Relaxed)
    (hadm : P.IsRelaxedAdmissible (toBoundedPath γ) ρ) :
    pointwiseDefectEnergy P γ ρ = 0 := by
  have hae := velocity_ae_eq_realizedVelocityOnLine_of_isRelaxedAdmissible P γ ρ hadm
  have hLp : γ.toLp = realizedVelocityLp P (toBoundedPath γ) ρ := by
    rw [VelocityTrajectory.toLp, realizedVelocityLp]
    exact MemLp.toLp_congr _ _ hae
  rw [pointwiseDefectEnergy, hLp, sub_self, norm_zero, sq]
  norm_num

/-! ## The anchored pointwise-defect penalty

The pointwise defect `φ′ − f(φ,ν_t,t)` does not reference `φ(0)`; the Volterra residual does.  On
the fixed-initial admissible graph the two agree (previous section), but a boundary sequence of
the pointwise penalty can drift in the initial state without paying the `K`-weighted defect.  The
anchored defect below adds the initial mismatch `|φ(0) − P.initial|²` to the `K`-weighted terms,
which is exactly the information the Volterra residual carries automatically. -/

/-- The `K`-weighted admissibility defect of the anchored pointwise penalty: the initial-state
mismatch, the endpoint constraint and the pointwise velocity defect.  Its vanishing characterises
admissibility of a product-domain datum for the fixed initial state `P.initial`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.6.2)–(11.6.5), §11.6 dynamics defect. -/
noncomputable def lpPointwiseAdmissibilityDefect (P : Problem E V W)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) : ℝ :=
  dist d.1 P.initial ^ 2
    + ‖P.endpointConstraint (lpPath P d (timeZero P.horizon P.horizon_pos.le))
        (lpPath P d (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2
    + lpPointwiseDefectEnergy P d

/-- The anchored pointwise penalty: the pointwise-defect penalty plus the `K`-weighted initial
anchor.  This is the fixed-initial rendition of the book's §11.6 `F_K`; the book's problem leaves
`φ(0)` free and constrains it only through `T`, so the anchor is redundant in the book but is what
`Problem.IsRelaxedMinimum` needs.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6) and §11.6. -/
noncomputable def lpPenaltyPointwiseAnchored (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) : ℝ :=
  lpPenaltyPointwise P K ε γ₀ ρ₀ d + K * dist d.1 P.initial ^ 2

/-- The anchored pointwise penalty on the velocity carrier. -/
noncomputable def velocityPenalizedPointwiseAnchored (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (γ : VelocityTrajectory P) (ρ : P.Relaxed) : ℝ :=
  velocityPenalizedPointwise P K ε γ₀ ρ₀ γ ρ + K * dist γ.initial P.initial ^ 2

/-- The product-domain pointwise defect energy is nonnegative. -/
theorem lpPointwiseDefectEnergy_nonneg (P : Problem E V W)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :
    0 ≤ lpPointwiseDefectEnergy P d := by
  rw [lpPointwiseDefectEnergy]
  exact sq_nonneg _

/-- The anchored admissibility defect is nonnegative. -/
theorem lpPointwiseAdmissibilityDefect_nonneg (P : Problem E V W)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :
    0 ≤ lpPointwiseAdmissibilityDefect P d := by
  simp only [lpPointwiseAdmissibilityDefect]
  exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
    (lpPointwiseDefectEnergy_nonneg P d)

/-- The anchored penalty splits into the scale-free part and `K` times the anchored defect. -/
theorem lpPenaltyPointwiseAnchored_eq_base_add_scale_mul_defect (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :
    lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d
      = lpPenaltyPointwise P 0 ε γ₀ ρ₀ d + K * lpPointwiseAdmissibilityDefect P d := by
  simp only [lpPenaltyPointwiseAnchored, lpPointwiseAdmissibilityDefect, lpPenaltyPointwise]
  ring

/-- The anchored admissibility defect is lower semicontinuous on the weakly bounded parameter set:
the initial term is continuous, the endpoint term is continuous and the pointwise defect energy is
lower semicontinuous.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 and §11.6. -/
theorem lowerSemicontinuousOn_lpPointwiseAdmissibilityDefect (P : Problem E V W)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint)) (R : ℝ) :
    LowerSemicontinuousOn (lpPointwiseAdmissibilityDefect P)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) := by
  set A : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    (univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
      (univ : Set P.Relaxed) with hA
  have hinit : LowerSemicontinuousOn (fun d : E ×
      WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed => dist d.1 P.initial ^ 2) A :=
    (continuous_fst.dist continuous_const).pow 2 |>.continuousOn.lowerSemicontinuousOn
  have hsum := (hinit.add (continuousOn_lpEndpointSq P hEnd R).lowerSemicontinuousOn).add
    (lowerSemicontinuousOn_lpPointwiseDefectEnergy P R)
  convert hsum using 1
  funext d
  simp only [lpPointwiseAdmissibilityDefect]

/-- The anchored pointwise penalty is lower semicontinuous on the weakly bounded parameter set.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 and §11.6. -/
theorem lowerSemicontinuousOn_lpPenaltyPointwiseAnchored (P : Problem E V W) (K ε : ℝ)
    (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed) (R : ℝ) :
    LowerSemicontinuousOn (lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) := by
  set A : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    (univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
      (univ : Set P.Relaxed) with hA
  have hanchor : LowerSemicontinuousOn (fun d : E ×
      WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
        K * dist d.1 P.initial ^ 2) A :=
    (((continuous_fst.dist continuous_const).pow 2).const_mul K).continuousOn.lowerSemicontinuousOn
  have hsum := (lowerSemicontinuousOn_lpPenaltyPointwise P K ε hK hε hEnd γ₀ ρ₀ R).add hanchor
  convert hsum using 1
  funext d
  simp only [lpPenaltyPointwiseAnchored]

/-- The anchored pointwise penalty on the velocity carrier is the product-domain anchored penalty
at the carrier data. -/
theorem velocityPenalizedPointwiseAnchored_eq_lpPenaltyPointwiseAnchored (P : Problem E V W)
    (K ε : ℝ) (γ₀ γ : VelocityTrajectory P) (ρ₀ ρ : P.Relaxed) :
    velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ ρ =
      lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀
        (γ.initial, toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) γ.toLp, ρ) := by
  have h := velocityPenalizedPointwise_eq_lpPenaltyPointwise P K ε γ₀ γ ρ₀ ρ
  unfold velocityPenalizedPointwiseAnchored lpPenaltyPointwiseAnchored
  rw [h]

/-- **Boundary positivity of the anchored pointwise penalty** (Berkovitz & Medhin, Lemma 11.3.3
for the §11.6 pointwise velocity defect): on the boundary of the velocity-control tube `B(ε)` the
anchored penalty `F_{K(ε)}` strictly exceeds the reference cost, for a sufficiently large scale
`K(ε)`.

The proof is the book's contradiction argument, re-run with the lower-semicontinuous pointwise
defect.  The anchored defect at the cluster point forces `φ(0) = P.initial` and `φ′ = f(φ,ν,t)`
a.e., i.e. admissibility, contradicting the strict running-cost gap.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2), (11.3.6) and Lemma 11.3.3. -/
theorem exists_penalty_scale_of_pointwise_boundary_positivity (P : Problem E V W) (ε : ℝ)
    (hε : 0 < ε) (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ d :
        E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed,
      lpTubeBoundary P ε γ₀ ρ₀ d →
        P.relaxedCost (toBoundedPath γ₀) ρ₀ < lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d := by
  classical
  set J₀ : ℝ := P.relaxedCost (toBoundedPath γ₀) ρ₀ with hJ₀
  by_contra hcon
  rw [not_exists] at hcon
  have hbad : ∀ n : ℕ, ∃ d,
      lpTubeBoundary P ε γ₀ ρ₀ d ∧
        lpPenaltyPointwiseAnchored P ((n : ℝ) + 1) ε γ₀ ρ₀ d ≤ J₀ := by
    intro n
    have h1 : ¬ (∀ d, lpTubeBoundary P ε γ₀ ρ₀ d →
        J₀ < lpPenaltyPointwiseAnchored P ((n : ℝ) + 1) ε γ₀ ρ₀ d) :=
      fun hP => hcon ((n : ℝ) + 1) ⟨by positivity, hP⟩
    simp only [not_forall, not_lt] at h1
    simpa only [exists_prop] using h1
  let x : ℕ → E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed :=
    fun n => Classical.choose (hbad n)
  have hxbnd : ∀ n : ℕ, lpTubeBoundary P ε γ₀ ρ₀ (x n) :=
    fun n => (Classical.choose_spec (hbad n)).1
  have hxle : ∀ n : ℕ, lpPenaltyPointwiseAnchored P ((n : ℝ) + 1) ε γ₀ ρ₀ (x n) ≤ J₀ :=
    fun n => (Classical.choose_spec (hbad n)).2
  have hxmem : ∀ n : ℕ, x n ∈ lpTube P ε γ₀ ρ₀ := fun n => (hxbnd n).1
  set R : ℝ := ‖γ₀.toLp‖ + ε with hR
  set S₀ : Set (Lp E 2 (horizonMeasure P.horizon)) := {v | ‖v‖ ≤ R} with hS₀
  set A : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    (univ : Set E) ×ˢ (toWeakSpace ℝ _ '' S₀) ×ˢ (univ : Set P.Relaxed) with hA
  have hSsub : lpTube P ε γ₀ ρ₀ ⊆ A := by
    rintro d ⟨⟨-, ⟨v, hv, hvd⟩, -⟩, -⟩
    refine ⟨mem_univ _, ⟨v, ?_, hvd⟩, mem_univ _⟩
    have h1 : ‖v - γ₀.toLp‖ ^ 2 ≤ ε ^ 2 := by
      rw [← integral_norm_sub_sq_eq_norm_sq]; exact hv
    have h2 : ‖v - γ₀.toLp‖ ≤ ε :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1 h1
    have h3 : ‖v‖ ≤ ‖v - γ₀.toLp‖ + ‖γ₀.toLp‖ := by
      simpa using norm_add_le (v - γ₀.toLp) γ₀.toLp
    change ‖v‖ ≤ R
    rw [hR]; linarith
  have hne : (lpTube P ε γ₀ ρ₀).Nonempty := ⟨x 0, hxmem 0⟩
  obtain ⟨dmin, hdminmem, hdmin⟩ :=
    ((lowerSemicontinuousOn_lpPenaltyPointwise P 0 ε (le_refl 0) hε.le hEnd γ₀ ρ₀ R).mono
      hSsub).exists_isMinOn hne (isCompact_lpTube P ε γ₀ ρ₀)
  have hdefect_bound : ∀ n : ℕ, lpPointwiseAdmissibilityDefect P (x n) ≤
      (J₀ - lpPenaltyPointwise P 0 ε γ₀ ρ₀ dmin) / ((n : ℝ) + 1) := by
    intro n
    have hdec := lpPenaltyPointwiseAnchored_eq_base_add_scale_mul_defect P ((n : ℝ) + 1) ε
      γ₀ ρ₀ (x n)
    have hmin : lpPenaltyPointwise P 0 ε γ₀ ρ₀ dmin ≤ lpPenaltyPointwise P 0 ε γ₀ ρ₀ (x n) :=
      hdmin (hxmem n)
    have hle := hxle n
    rw [hdec] at hle
    have hpos : 0 < ((n : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hpos, mul_comm]
    linarith
  have hgap : ∀ n : ℕ, P.relaxedCost (lpPath P (x n)) (x n).2.2 ≤ J₀ - ε ^ 2 := by
    intro n
    have hb := (hxbnd n).2
    have hle := hxle n
    have hdec := lpPenaltyPointwiseAnchored_eq_base_add_scale_mul_defect P ((n : ℝ) + 1) ε
      γ₀ ρ₀ (x n)
    have hbase : lpPenaltyPointwise P 0 ε γ₀ ρ₀ (x n)
        = P.relaxedCost (lpPath P (x n)) (x n).2.2
          + ‖(toWeakSpace ℝ _).symm (x n).2.1 - γ₀.toLp‖ ^ 2
          + dist (x n).1 γ₀.initial ^ 2
          + ε * relaxedControlDistance P (x n).2.2 ρ₀ := by
      simp only [lpPenaltyPointwise]
      ring
    have hKnn : 0 ≤ ((n : ℝ) + 1) := by positivity
    have hdefnn : 0 ≤ lpPointwiseAdmissibilityDefect P (x n) :=
      lpPointwiseAdmissibilityDefect_nonneg P (x n)
    have hinit : 0 ≤ dist (x n).1 γ₀.initial ^ 2 := sq_nonneg _
    have hctrl : 0 ≤ ε * relaxedControlDistance P (x n).2.2 ρ₀ :=
      mul_nonneg hε.le (relaxedControlDistance_nonneg P _ _)
    rw [hdec, hbase] at hle
    rcases hb with hvel | hinit' | hctrl'
    · rw [hvel] at hle
      nlinarith [hle, hinit, hctrl, mul_nonneg hKnn hdefnn]
    · rw [hinit'] at hle
      nlinarith [hle, hinit, hctrl, mul_nonneg hKnn hdefnn]
    · rw [hctrl'] at hle
      nlinarith [hle, hinit, hctrl, mul_nonneg hKnn hdefnn]
  set S : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    lpTube P ε γ₀ ρ₀ with hS
  have hScomp : IsCompact S := isCompact_lpTube P ε γ₀ ρ₀
  let y : ℕ → ↥S := fun n => ⟨x n, hxmem n⟩
  have hcount : IsCountablyCompact (univ : Set ↥S) :=
    isCountablyCompact_iff_isCountablyCompact_univ.mp hScomp.isCountablyCompact
  obtain ⟨a, -, hacl⟩ :=
    hcount.seq_clusterPt y (Eventually.of_forall fun _ => mem_univ _)
  have hJcontS : ContinuousOn (fun d => P.relaxedCost (lpPath P d) d.2.2)
      (lpTube P ε γ₀ ρ₀) := (continuousOn_lpRelaxedCost P R).mono hSsub
  have hJsub : Continuous (fun q : ↥S => P.relaxedCost (lpPath P q.1) q.1.2.2) :=
    hJcontS.domRestrict
  have hJlim : P.relaxedCost (lpPath P a.1) a.1.2.2 ≤ J₀ - ε ^ 2 :=
    DynamicalSystems.le_of_mapClusterPt_of_lowerSemicontinuous
      hJsub.lowerSemicontinuous hacl (fun n => hgap n)
  have hK : Tendsto (fun a : ℝ => a + 1) atTop atTop :=
    le_of_eq (Filter.map_add_atTop_eq (1 : ℝ))
  have hzero : Tendsto
      (fun n : ℕ => (J₀ - lpPenaltyPointwise P 0 ε γ₀ ρ₀ dmin) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    (hK.comp tendsto_natCast_atTop_atTop).const_div_atTop _
  have hdefectlim : lpPointwiseAdmissibilityDefect P a.1 = 0 :=
    DynamicalSystems.eq_zero_of_mapClusterPt_of_lowerSemicontinuous_of_nonneg_of_tendsto_zero
      (lowerSemicontinuous_restrict_iff.mpr
        ((lowerSemicontinuousOn_lpPointwiseAdmissibilityDefect P hEnd R).mono hSsub))
      (fun q => lpPointwiseAdmissibilityDefect_nonneg P q.1) hzero hacl (fun n => hdefect_bound n)
  have hinit0 : dist a.1.1 P.initial ^ 2 = 0 := by
    have h1 : 0 ≤ dist a.1.1 P.initial ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ‖P.endpointConstraint (lpPath P a.1 (timeZero P.horizon P.horizon_pos.le))
        (lpPath P a.1 (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 := sq_nonneg _
    have h3 : 0 ≤ lpPointwiseDefectEnergy P a.1 := lpPointwiseDefectEnergy_nonneg P a.1
    simp only [lpPointwiseAdmissibilityDefect] at hdefectlim
    linarith
  have hend0 : ‖P.endpointConstraint (lpPath P a.1 (timeZero P.horizon P.horizon_pos.le))
      (lpPath P a.1 (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 = 0 := by
    have h1 : 0 ≤ dist a.1.1 P.initial ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ‖P.endpointConstraint (lpPath P a.1 (timeZero P.horizon P.horizon_pos.le))
        (lpPath P a.1 (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 := sq_nonneg _
    have h3 : 0 ≤ lpPointwiseDefectEnergy P a.1 := lpPointwiseDefectEnergy_nonneg P a.1
    simp only [lpPointwiseAdmissibilityDefect] at hdefectlim
    linarith
  have hdef0 : lpPointwiseDefectEnergy P a.1 = 0 := by
    have h1 : 0 ≤ dist a.1.1 P.initial ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ‖P.endpointConstraint (lpPath P a.1 (timeZero P.horizon P.horizon_pos.le))
        (lpPath P a.1 (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 := sq_nonneg _
    simp only [lpPointwiseAdmissibilityDefect] at hdefectlim
    linarith
  have ha1 : a.1.1 = P.initial := dist_eq_zero.mp (sq_eq_zero_iff.mp hinit0)
  have hend_eq : P.endpointConstraint (lpPath P a.1 (timeZero P.horizon P.horizon_pos.le))
      (lpPath P a.1 (timeEnd P.horizon P.horizon_pos.le)) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hend0)
  have hv_eq : (toWeakSpace ℝ _).symm a.1.2.1 = realizedVelocityLp P (lpPath P a.1) a.1.2.2 :=
    sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdef0))
  have hadm : P.IsRelaxedAdmissible (lpPath P a.1) a.1.2.2 := by
    refine ⟨?_, hend_eq, a.2.2⟩
    intro t
    have hL : lpPath P a.1 t = P.initial +
        ∫ s in (0 : ℝ)..(t : ℝ), realizedVelocityOnLine P (lpPath P a.1) a.1.2.2 s := by
      conv_lhs => rw [lpPath, primitiveBoundedPath_apply]
      rw [ha1, hv_eq, primitiveValue_realizedVelocityLp]
    rw [hL]
    simp only [Problem.relaxedDynamics]
    rw [horizon_smul_setIntegral_eq_intervalIntegral_realizedVelocityOnLine]
  have hopt_a : J₀ ≤ P.relaxedCost (lpPath P a.1) a.1.2.2 :=
    hopt.2 (lpPath P a.1) a.1.2.2 hadm
  nlinarith [hJlim, hopt_a, sq_pos_of_pos hε]

/-- At an admissible reference the anchored pointwise penalty takes the reference cost value. -/
theorem velocityPenalizedPointwiseAnchored_self (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) :
    velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ₀ ρ₀ =
      P.relaxedCost (toBoundedPath γ₀) ρ₀ := by
  have hinit : dist γ₀.initial P.initial = 0 := by
    have h := IsRelaxedTrajectory.initial hopt.1.1
    rw [toBoundedPath_apply] at h
    simp only [timeZero] at h
    rw [VelocityTrajectory.value_zero] at h
    rw [h, dist_self]
  have hend : P.endpointConstraint (γ₀.value (timeZero P.horizon P.horizon_pos.le))
      (γ₀.value (timeEnd P.horizon P.horizon_pos.le)) = 0 := by
    simpa [toBoundedPath_apply] using hopt.1.2.1
  have hdef : pointwiseDefectEnergy P γ₀ ρ₀ = 0 :=
    pointwiseDefectEnergy_eq_zero_of_isRelaxedAdmissible P γ₀ ρ₀ hopt.1
  simp only [velocityPenalizedPointwiseAnchored, velocityPenalizedPointwise,
    velocityPenaltyRemainderPointwise, hinit, hdef, hend, relaxedControlDistance_self, dist_self]
  simp

/-- **Existence of a minimiser of the anchored pointwise penalty** (the analogue of Berkovitz &
Medhin, Lemma 11.3.4 for the anchored §11.6 pointwise defect).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4, (11.3.2) and §11.6. -/
theorem exists_isMinOn_velocityPenalizedPointwiseAnchored (P : Problem E V W) (K ε : ℝ)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hstate : ∀ t : P.Time, P.stateConstraint t (γ₀.value t) ≤ 0) :
    ∃ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      InVelocityControlTube P γ₀ ρ₀ ε γ ρ ∧
      ∀ (γ' : VelocityTrajectory P) (ρ' : P.Relaxed),
        InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
          velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ ρ ≤
            velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ' ρ' := by
  have hne : (lpTube P ε γ₀ ρ₀).Nonempty :=
    ⟨_, (mem_lpTube_iff P hε γ₀ γ₀ ρ₀ ρ₀).1 (self_mem_InVelocityControlTube P hε hstate)⟩
  have hsub : lpTube P ε γ₀ ρ₀ ⊆ (univ : Set E) ×ˢ
      (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ''
        {v | ‖v‖ ≤ ‖γ₀.toLp‖ + ε}) ×ˢ (univ : Set P.Relaxed) := by
    rintro d ⟨⟨-, ⟨v, hv, hvd⟩, -⟩, -⟩
    refine ⟨mem_univ _, ⟨v, ?_, hvd⟩, mem_univ _⟩
    have h1 : ‖v - γ₀.toLp‖ ^ 2 ≤ ε ^ 2 := by
      rw [← integral_norm_sub_sq_eq_norm_sq]; exact hv
    have h2 : ‖v - γ₀.toLp‖ ≤ ε :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) hε two_ne_zero).1 h1
    have h3 : ‖v‖ ≤ ‖v - γ₀.toLp‖ + ‖γ₀.toLp‖ := by
      simpa using norm_add_le (v - γ₀.toLp) γ₀.toLp
    change ‖v‖ ≤ ‖γ₀.toLp‖ + ε
    linarith
  obtain ⟨d, hd, hmin⟩ := (lowerSemicontinuousOn_lpPenaltyPointwiseAnchored P K ε hK hε hEnd
    γ₀ ρ₀ (‖γ₀.toLp‖ + ε)).mono hsub |>.exists_isMinOn hne (isCompact_lpTube P ε γ₀ ρ₀)
  set γ := VelocityTrajectory.ofLp P d.1 ((toWeakSpace ℝ _).symm d.2.1) with hγ
  have hdγ : (γ.initial, toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) γ.toLp, d.2.2) = d := by
    have hl : γ.toLp = (toWeakSpace ℝ _).symm d.2.1 := VelocityTrajectory.toLp_ofLp _ _
    have hi : γ.initial = d.1 := rfl
    rw [hl, hi]
    simp
  have hmem : InVelocityControlTube P γ₀ ρ₀ ε γ d.2.2 :=
    (mem_lpTube_iff P hε γ₀ γ ρ₀ d.2.2).2 (by rw [hdγ]; exact hd)
  refine ⟨γ, d.2.2, hmem, fun γ' ρ' hγ' => ?_⟩
  rw [velocityPenalizedPointwiseAnchored_eq_lpPenaltyPointwiseAnchored,
    velocityPenalizedPointwiseAnchored_eq_lpPenaltyPointwiseAnchored, hdγ]
  exact hmin ((mem_lpTube_iff P hε γ₀ γ' ρ₀ ρ').1 hγ')

/-- **Boundary positivity on the velocity carrier for the anchored pointwise penalty.**

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2), (11.3.6) and Lemma 11.3.3. -/
theorem exists_penalty_scale_of_velocity_pointwise_boundary_positivity (P : Problem E V W) (ε : ℝ)
    (hε : 0 < ε) (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ γ ρ,
      InVelocityControlTubeBoundary P γ₀ ρ₀ ε γ ρ →
        P.relaxedCost (toBoundedPath γ₀) ρ₀ <
          velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ ρ := by
  obtain ⟨K, hKpos, hK⟩ :=
    exists_penalty_scale_of_pointwise_boundary_positivity P ε hε hEnd γ₀ ρ₀ hopt
  refine ⟨K, hKpos, fun γ ρ hb => ?_⟩
  have hmem : (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ) ∈ lpTube P ε γ₀ ρ₀ :=
    (mem_lpTube_iff P hε.le γ₀ γ ρ₀ ρ).1 hb.1
  have hbd : lpTubeBoundary P ε γ₀ ρ₀ (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ) := by
    refine ⟨hmem, ?_⟩
    rcases hb.2 with hv | hi | hc
    · left
      simp only [LinearEquiv.symm_apply_apply]
      have hv' : ‖γ.toLp - γ₀.toLp‖ ^ 2 = ε ^ 2 := by
        rw [Lp_two_norm_sq_eq_integral_norm_sq]
        rw [integral_sq_velocity_sub_eq (P := P) γ₀ γ] at hv
        exact hv
      exact hv'
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hc)
  rw [velocityPenalizedPointwiseAnchored_eq_lpPenaltyPointwiseAnchored]
  exact hK _ hbd

/-- **Strict-interior minimiser of the anchored pointwise penalty** (Berkovitz & Medhin,
Lemma 11.3.4, strict-interior part, and Remark 11.6.6, for the §11.6 pointwise velocity defect):
for `0 < ε` there is a scale `K(ε) > 0` and a pair with all tube inequalities strict, satisfying
the state constraint, and minimising the anchored pointwise penalty over the closed tube `B(ε)`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 (strict-interior part) and Remark 11.6.6. -/
theorem exists_strict_interior_velocityPointwisePenalized_minimizer (P : Problem E V W) (ε : ℝ)
    (hε : 0 < ε) (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ γ ρ,
      (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) < ε ^ 2 ∧
      dist γ.initial γ₀.initial < ε ∧
      relaxedControlDistance P ρ ρ₀ < ε ∧
      (∀ t : P.Time, P.stateConstraint t (γ.value t) ≤ 0) ∧
      ∀ γ' ρ', InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
        velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ ρ ≤
          velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ' ρ' := by
  obtain ⟨K, hKpos, hK⟩ :=
    exists_penalty_scale_of_velocity_pointwise_boundary_positivity P ε hε hEnd γ₀ ρ₀ hopt
  have hstate : ∀ t : P.Time, P.stateConstraint t (γ₀.value t) ≤ 0 :=
    fun t => by simpa using hopt.1.2.2 t
  obtain ⟨γ, ρ, hmem, hmin⟩ :=
    exists_isMinOn_velocityPenalizedPointwiseAnchored P K ε hKpos.le hε.le hEnd γ₀ ρ₀ hstate
  have hself := self_mem_InVelocityControlTube (P := P) (γ₀ := γ₀) (ρ₀ := ρ₀) hε.le hstate
  have hle₀ : velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ ρ ≤
      P.relaxedCost (toBoundedPath γ₀) ρ₀ := by
    rw [← velocityPenalizedPointwiseAnchored_self P K ε γ₀ ρ₀ hopt]
    exact hmin γ₀ ρ₀ hself
  refine ⟨K, hKpos, γ, ρ, ?_, ?_, ?_, hmem.1.2.2.2, fun γ' ρ' hγ' => hmin γ' ρ' hγ'⟩
  · by_contra hle
    rw [not_lt] at hle
    have heq : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) = ε ^ 2 :=
      le_antisymm hmem.1.2.1 hle
    exact absurd (hK γ ρ ⟨hmem, Or.inl heq⟩) (not_lt.mpr hle₀)
  · by_contra hle
    rw [not_lt] at hle
    have heq : dist γ.initial γ₀.initial = ε := le_antisymm hmem.1.2.2.1 hle
    exact absurd (hK γ ρ ⟨hmem, Or.inr (Or.inl heq)⟩) (not_lt.mpr hle₀)
  · by_contra hle
    rw [not_lt] at hle
    have heq : relaxedControlDistance P ρ ρ₀ = ε := le_antisymm hmem.2 hle
    exact absurd (hK γ ρ ⟨hmem, Or.inr (Or.inr heq)⟩) (not_lt.mpr hle₀)

end Problem

end OptimalControl.BoundedState
