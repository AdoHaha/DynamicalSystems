/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.BoundedVariation.HellySelection
public import DynamicalSystems.OptimalControl.ContinuousTime.StateMultiplierCostate

/-!
# The limit `j → ∞` of the penalised multipliers and costates

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5, §11.6.  The
`ω`-penalised functionals `H^j` of `StatePenalisedVelocityFunctional.lean` have minimisers `γ_j`
whose costates `Φ_j = p_j + λ_j ∇G` satisfy the measure-free equation (11.6.11)
(`VelocityTrajectory.statePenalised_costateEquation`).  This file passes to the limit `j → ∞`
along a subsequence, given the convergence data produced by Lemma 11.3.5:

* `exists_stateMultiplier_limit`: **Helly's selection** applied to the nonincreasing multipliers
  `λ_j` (uniformly bounded by the total mass, itself bounded via
  `integral_density_eq_boundary`) gives a subsequence converging **everywhere** on `[0,T]` to a
  nonincreasing `λ` with `0 ≤ λ ≤ M`, `λ(T) = 0`; the costates `Φ_j` converge pointwise to
  `Φ(t) = c + λ(0) ∇G(0) + ∫₀ᵗ (∂ₓL + λ d(∇G)/dt)`: the limit costate equation (11.6.11) with the
  initial condition (11.6.6).  No measure is needed: only the `L¹` convergence of `∂ₓL(γ_j, γ_j')`
  and `d(∇G)/dt (γ_j)` and the uniform convergence of `∇G(·,γ_j)`.
* `stateMultiplier_limit_eq_of_eventually_density_eq_zero`: complementarity survives the limit:
  `λ` is constant on every interval on which the densities eventually vanish; on every interval
  where the *limit* path is strictly slack this holds
  (`eventually_nonpos_of_uniformConvergence`), so the limit constraint measure is supported on the
  contact set;
* `exists_stateMultiplier_limit_of_penalisedMinimisers`: the assembled limit theorem on the velocity
  carrier for a `PenalisedMinimiserSequence` (conclusion `PenalisedMultiplierLimit`): the limit
  costate `limitStateCostate` solves (11.6.11) with (11.6.6) and (11.6.16), `∂ᵥL = Φ - λ∇G`
  a.e., `λ` is complementary, and with Assumption 11.4.1 (`EndpointInterior`) the multiplier is
  constant near both endpoints (`λ(0⁺) = λ(0)`, `λ = 0` near `T`).

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter ACEulerLagrange
open scoped Topology Interval ENNReal

namespace OptimalControl.BoundedState

section Limit

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {T : ℝ}

omit [CompleteSpace F] in
/-- Convergence in `L¹(0,T)` gives convergence of the primitives at every `t ∈ [0,T]`. -/
theorem tendsto_intervalIntegral_of_L1 (hT : 0 ≤ T) {f : ℕ → ℝ → F} {fInf : ℝ → F}
    (hf : ∀ n, IntervalIntegrable (f n) volume 0 T) (hfInf : IntervalIntegrable fInf volume 0 T)
    (hL : Tendsto (fun n => ∫ r in (0 : ℝ)..T, ‖f n r - fInf r‖) atTop (𝓝 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    Tendsto (fun n => ∫ r in (0 : ℝ)..t, f n r) atTop (𝓝 (∫ r in (0 : ℝ)..t, fInf r)) := by
  have hT' : (⟨hT, le_rfl⟩ : T ∈ Icc (0 : ℝ) T) = ⟨hT, le_rfl⟩ := rfl
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hL
  have h1 : IntervalIntegrable (f n) volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc (hf n) hT ⟨le_rfl, hT⟩ ht
  have h2 : IntervalIntegrable fInf volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc hfInf hT ⟨le_rfl, hT⟩ ht
  rw [← intervalIntegral.integral_sub h1 h2]
  have hdiff : IntervalIntegrable (fun r => ‖f n r - fInf r‖) volume 0 T := ((hf n).sub hfInf).norm
  have hdt : IntervalIntegrable (fun r => ‖f n r - fInf r‖) volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc hdiff hT ⟨le_rfl, hT⟩ ht
  have htT : IntervalIntegrable (fun r => ‖f n r - fInf r‖) volume t T :=
    intervalIntegrable_of_mem_Icc_Icc hdiff hT ht ⟨hT, le_rfl⟩
  have hsum := intervalIntegral.integral_add_adjacent_intervals hdt htT
  have hnn : 0 ≤ ∫ r in t..T, ‖f n r - fInf r‖ :=
    intervalIntegral.integral_nonneg ht.2 fun _ _ => norm_nonneg _
  calc ‖∫ r in (0 : ℝ)..t, (f n r - fInf r)‖ ≤ ∫ r in (0 : ℝ)..t, ‖f n r - fInf r‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
    _ ≤ ∫ r in (0 : ℝ)..T, ‖f n r - fInf r‖ := by linarith

omit [CompleteSpace F] in
/-- Weighted `L¹` limit: if `w n → w` pointwise on `[0,T]` with `0 ≤ w n ≤ M` continuous and
`k n → k∞` in `L¹(0,T)`, then `∫₀ᵗ w n • k n → ∫₀ᵗ w • k∞`. -/
theorem tendsto_intervalIntegral_smul_of_L1 (hT : 0 ≤ T) {w : ℕ → ℝ → ℝ} {wInf : ℝ → ℝ} {M : ℝ}
    (hwc : ∀ n, ContinuousOn (w n) (Icc (0 : ℝ) T))
    (hw0 : ∀ n, ∀ r ∈ Icc (0 : ℝ) T, 0 ≤ w n r) (hwM : ∀ n, ∀ r ∈ Icc (0 : ℝ) T, w n r ≤ M)
    (hwlim : ∀ r ∈ Icc (0 : ℝ) T, Tendsto (fun n => w n r) atTop (𝓝 (wInf r)))
    {k : ℕ → ℝ → F} {kInf : ℝ → F}
    (hk : ∀ n, IntervalIntegrable (k n) volume 0 T) (hkInf : IntervalIntegrable kInf volume 0 T)
    (hL : Tendsto (fun n => ∫ r in (0 : ℝ)..T, ‖k n r - kInf r‖) atTop (𝓝 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    Tendsto (fun n => ∫ r in (0 : ℝ)..t, w n r • k n r) atTop
      (𝓝 (∫ r in (0 : ℝ)..t, wInf r • kInf r)) := by
  have hM0 : 0 ≤ M := (hw0 0 0 ⟨le_rfl, hT⟩).trans (hwM 0 0 ⟨le_rfl, hT⟩)
  have hsub : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hkt : ∀ n, IntervalIntegrable (k n) volume 0 t := fun n =>
    intervalIntegrable_of_mem_Icc_Icc (hk n) hT ⟨le_rfl, hT⟩ ht
  have hkInft : IntervalIntegrable kInf volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc hkInf hT ⟨le_rfl, hT⟩ ht
  have hwt : ∀ n, ContinuousOn (w n) (uIcc (0 : ℝ) t) := fun n => by
    rw [uIcc_of_le ht.1]; exact (hwc n).mono hsub
  -- split `w n • k n = w n • (k n - kInf) + w n • kInf`
  have hsplit : ∀ n, ∫ r in (0 : ℝ)..t, w n r • k n r
      = (∫ r in (0 : ℝ)..t, w n r • (k n r - kInf r)) + ∫ r in (0 : ℝ)..t, w n r • kInf r := by
    intro n
    rw [← intervalIntegral.integral_add ((hkt n).sub hkInft |>.continuousOn_smul (hwt n))
      (hkInft.continuousOn_smul (hwt n))]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp [smul_sub]
  -- part A: the error term tends to zero
  have hA : Tendsto (fun n => ∫ r in (0 : ℝ)..t, w n r • (k n r - kInf r)) atTop (𝓝 0) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    simp only [sub_zero]
    have hMt : Tendsto (fun n => M * ∫ r in (0 : ℝ)..T, ‖k n r - kInf r‖) atTop (𝓝 0) := by
      simpa using hL.const_mul M
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hMt
    have hd : IntervalIntegrable (fun r => ‖k n r - kInf r‖) volume 0 T := ((hk n).sub hkInf).norm
    have hdt : IntervalIntegrable (fun r => ‖k n r - kInf r‖) volume 0 t :=
      intervalIntegrable_of_mem_Icc_Icc hd hT ⟨le_rfl, hT⟩ ht
    have htT : IntervalIntegrable (fun r => ‖k n r - kInf r‖) volume t T :=
      intervalIntegrable_of_mem_Icc_Icc hd hT ht ⟨hT, le_rfl⟩
    have hsum := intervalIntegral.integral_add_adjacent_intervals hdt htT
    have hnn : 0 ≤ ∫ r in t..T, ‖k n r - kInf r‖ :=
      intervalIntegral.integral_nonneg ht.2 fun _ _ => norm_nonneg _
    have hint : IntervalIntegrable (fun r => w n r • (k n r - kInf r)) volume 0 t :=
      ((hkt n).sub hkInft).continuousOn_smul (hwt n)
    calc ‖∫ r in (0 : ℝ)..t, w n r • (k n r - kInf r)‖
        ≤ ∫ r in (0 : ℝ)..t, ‖w n r • (k n r - kInf r)‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ r in (0 : ℝ)..t, M * ‖k n r - kInf r‖ := by
          refine intervalIntegral.integral_mono_on ht.1 hint.norm (hdt.const_mul M) fun r hr => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 n r (hsub r hr))]
          exact mul_le_mul_of_nonneg_right (hwM n r (hsub r hr)) (norm_nonneg _)
      _ = M * ∫ r in (0 : ℝ)..t, ‖k n r - kInf r‖ := intervalIntegral.integral_const_mul _ _
      _ ≤ M * ∫ r in (0 : ℝ)..T, ‖k n r - kInf r‖ :=
          mul_le_mul_of_nonneg_left (by linarith) hM0
  -- part B: dominated convergence for `w n • kInf`
  have hB : Tendsto (fun n => ∫ r in (0 : ℝ)..t, w n r • kInf r) atTop
      (𝓝 (∫ r in (0 : ℝ)..t, wInf r • kInf r)) := by
    simp only [intervalIntegral.integral_of_le ht.1]
    have hkInfm : AEStronglyMeasurable kInf (volume.restrict (Ioc (0 : ℝ) t)) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1 hkInft).aestronglyMeasurable
    have hwm : ∀ n, AEStronglyMeasurable (w n) (volume.restrict (Ioc (0 : ℝ) t)) := fun n =>
      ((hwc n).mono hsub |>.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    refine tendsto_integral_of_dominated_convergence (fun r => M * ‖kInf r‖) (fun n =>
      (hwm n).smul hkInfm) ?_ ?_ ?_
    · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1 hkInft).norm.const_mul M
    · intro n
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun r hr => ?_
      have hr' : r ∈ Icc (0 : ℝ) T := hsub r ⟨hr.1.le, hr.2⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 n r hr')]
      exact mul_le_mul_of_nonneg_right (hwM n r hr') (norm_nonneg _)
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun r hr => ?_
      exact (hwlim r (hsub r ⟨hr.1.le, hr.2⟩)).smul_const (kInf r)
  have := hA.add hB
  rw [zero_add] at this
  exact this.congr fun n => (hsplit n).symm

end Limit

section LimitCovector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ}

/-- **Helly-compactness of the penalised multipliers (Lemma 11.3.5).**  Let `m n` be nonnegative,
interval integrable multiplier densities on `[0,T]` with total masses bounded by `M`, and let
`c n`, `a n`, `g n` be the constant, the state covector `∂ₓL` and the gradient path at level `n`,
with `g n` the primitive of `g' n` and `a n`, `g' n` interval integrable.  Suppose that, as `n → ∞`,
`c n → c∞`, `g n 0 → g∞ 0`, `a n → a∞` and `g' n → g'∞` in `L¹(0,T)`.  Then along a subsequence

* the multipliers `λ_n = ∫_t^T m n` converge **everywhere** on `[0,T]` to a nonincreasing `λ` with
  `0 ≤ λ ≤ M` and `λ(T) = 0`;
* the costates `Φ_n = c n + ∫₀ᵗ (a n + m n g n) + λ_n g n` converge everywhere on `[0,T]` to
  `c∞ + λ(0) g∞(0) + ∫₀ᵗ (a∞ + λ g'∞)`, the solution of the limit costate equation
  `Φ' = a∞ + λ g'∞` with the initial condition `Φ(0) = c∞ + λ(0) g∞(0)`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5, (11.6.6) and
(11.6.11). -/
theorem exists_stateMultiplier_limit (hT : 0 ≤ T) {m : ℕ → ℝ → ℝ}
    (hm : ∀ n, IntervalIntegrable (m n) volume 0 T)
    (hm0 : ∀ n, ∀ r ∈ Icc (0 : ℝ) T, 0 ≤ m n r) {M : ℝ}
    (hM : ∀ n, ∫ r in (0 : ℝ)..T, m n r ≤ M)
    {c : ℕ → E →L[ℝ] ℝ} {cInf : E →L[ℝ] ℝ} {a g' g : ℕ → ℝ → E →L[ℝ] ℝ}
    {aInf gdInf : ℝ → E →L[ℝ] ℝ} {gInf0 : E →L[ℝ] ℝ}
    (ha : ∀ n, IntervalIntegrable (a n) volume 0 T)
    (hg' : ∀ n, IntervalIntegrable (g' n) volume 0 T)
    (hg : ∀ n, ∀ t ∈ Icc (0 : ℝ) T, g n t = g n 0 + ∫ r in (0 : ℝ)..t, g' n r)
    (haInf : IntervalIntegrable aInf volume 0 T) (hgdInf : IntervalIntegrable gdInf volume 0 T)
    (hc : Tendsto c atTop (𝓝 cInf)) (hg0 : Tendsto (fun n => g n 0) atTop (𝓝 gInf0))
    (haL : Tendsto (fun n => ∫ r in (0 : ℝ)..T, ‖a n r - aInf r‖) atTop (𝓝 0))
    (hgL : Tendsto (fun n => ∫ r in (0 : ℝ)..T, ‖g' n r - gdInf r‖) atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (lam : ℝ → ℝ), StrictMono φ ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        Tendsto (fun n => stateMultiplier T (m (φ n)) t) atTop (𝓝 (lam t))) ∧
      AntitoneOn lam (Icc (0 : ℝ) T) ∧ (∀ t ∈ Icc (0 : ℝ) T, 0 ≤ lam t ∧ lam t ≤ M) ∧
      lam T = 0 ∧ IntervalIntegrable (fun r => lam r • gdInf r) volume 0 T ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        Tendsto (fun n => stateCostate T (m (φ n)) (c (φ n)) (a (φ n)) (g (φ n)) t) atTop
          (𝓝 ((cInf + lam 0 • gInf0) + ∫ r in (0 : ℝ)..t, (aInf r + lam r • gdInf r))) := by
  have hT0 : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hanti : ∀ n, AntitoneOn (stateMultiplier T (m n)) (Icc (0 : ℝ) T) := fun n =>
    stateMultiplier_antitoneOn hT (hm n) (hm0 n)
  have hnonneg : ∀ n, ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ stateMultiplier T (m n) t := fun n t ht =>
    stateMultiplier_nonneg (hm0 n) ht
  have hle : ∀ n, ∀ t ∈ Icc (0 : ℝ) T, stateMultiplier T (m n) t ≤ M := fun n t ht =>
    ((hanti n) h00 ht ht.1).trans (hM n)
  have hcont : ∀ n, ContinuousOn (stateMultiplier T (m n)) (Icc (0 : ℝ) T) := fun n =>
    stateMultiplier_continuousOn hT (hm n)
  -- Helly selection for the nondecreasing functions `-λ_n`
  obtain ⟨φ, gl, hφ, -, -, hlim⟩ := DynamicalSystems.Helly.helly_selection_real
    (fun n x => -stateMultiplier T (m n) x) hT (x₀ := T) hT0 (B := 0)
    (fun n => by simp) (C := ENNReal.ofReal M) ENNReal.ofReal_ne_top (fun n => by
      have hmono : MonotoneOn (fun x => -stateMultiplier T (m n) x) (Icc (0 : ℝ) T) :=
        fun x hx y hy hxy => neg_le_neg ((hanti n) hx hy hxy)
      have := (hmono.eVariationOn_eq h00 hT0).le
      rw [inter_self] at this
      refine this.trans (ENNReal.ofReal_le_ofReal ?_)
      simp only [stateMultiplier_horizon, neg_zero, zero_sub, neg_neg]
      exact hM n)
  set lam : ℝ → ℝ := fun x => -gl x with hlam
  have htend : ∀ t ∈ Icc (0 : ℝ) T,
      Tendsto (fun n => stateMultiplier T (m (φ n)) t) atTop (𝓝 (lam t)) := fun t ht => by
    simpa using (hlim t ht).neg
  have hanti' : AntitoneOn lam (Icc (0 : ℝ) T) := fun s hs t ht hst =>
    le_of_tendsto_of_tendsto' (htend t ht) (htend s hs) fun n => (hanti (φ n)) hs ht hst
  have hbd : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ lam t ∧ lam t ≤ M := fun t ht =>
    ⟨ge_of_tendsto (htend t ht) (Filter.Eventually.of_forall fun n => hnonneg (φ n) t ht),
      le_of_tendsto (htend t ht) (Filter.Eventually.of_forall fun n => hle (φ n) t ht)⟩
  have hlamT : lam T = 0 :=
    tendsto_nhds_unique (htend T hT0) (by simp [stateMultiplier_horizon])
  have hφt := hφ.tendsto_atTop
  have hsubT : ∀ t ∈ Icc (0 : ℝ) T, ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun t ht r hr =>
    ⟨hr.1, hr.2.trans ht.2⟩
  have hlamint : IntervalIntegrable (fun r => lam r • gdInf r) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    have hgm : AEStronglyMeasurable gdInf (volume.restrict (Ioc (0 : ℝ) T)) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hgdInf).aestronglyMeasurable
    have hlm : AEStronglyMeasurable lam (volume.restrict (Ioc (0 : ℝ) T)) := by
      refine aestronglyMeasurable_of_tendsto_ae atTop
        (f := fun n => stateMultiplier T (m (φ n))) (fun n => ?_) ?_
      · exact ((hcont (φ n)).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
      · rw [ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall fun r hr => htend r ⟨hr.1.le, hr.2⟩
    refine Integrable.mono' (g := fun r => M * ‖gdInf r‖)
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hgdInf).norm.const_mul M)
      (hlm.smul hgm) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun r hr => ?_
    have hr' := hbd r ⟨hr.1.le, hr.2⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr'.1]
    exact mul_le_mul_of_nonneg_right hr'.2 (norm_nonneg _)
  refine ⟨φ, lam, hφ, htend, hanti', hbd, hlamT, hlamint, fun t ht => ?_⟩
  have hsub : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := hsubT t ht
  have hI1 := tendsto_intervalIntegral_of_L1 hT (f := fun n => a (φ n)) (fInf := aInf)
    (fun n => ha (φ n)) haInf (haL.comp hφt) ht
  have hI2 := tendsto_intervalIntegral_smul_of_L1 hT (w := fun n => stateMultiplier T (m (φ n)))
    (wInf := lam) (M := M) (fun n => hcont (φ n)) (fun n => hnonneg (φ n)) (fun n => hle (φ n))
    htend (k := fun n => g' (φ n)) (kInf := gdInf) (fun n => hg' (φ n)) hgdInf (hgL.comp hφt) ht
  have hlamintt : IntervalIntegrable (fun r => lam r • gdInf r) volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc hlamint hT h00 ht
  have hat : ∀ n, IntervalIntegrable (a (φ n)) volume 0 t := fun n =>
    intervalIntegrable_of_mem_Icc_Icc (ha (φ n)) hT h00 ht
  have hatInf : IntervalIntegrable aInf volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc haInf hT h00 ht
  have hcost : ∀ n, stateCostate T (m (φ n)) (c (φ n)) (a (φ n)) (g (φ n)) t
      = (c (φ n) + stateMultiplier T (m (φ n)) 0 • g (φ n) 0)
        + ((∫ r in (0 : ℝ)..t, a (φ n) r)
          + ∫ r in (0 : ℝ)..t, stateMultiplier T (m (φ n)) r • g' (φ n) r) := by
    intro n
    have hw : ContinuousOn (stateMultiplier T (m (φ n))) (uIcc (0 : ℝ) t) := by
      rw [uIcc_of_le ht.1]
      exact (hcont (φ n)).mono hsub
    have h := stateCostate_eq_primitive hT (hm (φ n)) (c (φ n)) (ha (φ n)) (hg' (φ n))
      (hg (φ n)) ht
    have hg'n : IntervalIntegrable (g' (φ n)) volume 0 t :=
      intervalIntegrable_of_mem_Icc_Icc (hg' (φ n)) hT h00 ht
    rw [intervalIntegral.integral_add (hat n) (hg'n.continuousOn_smul hw)] at h
    exact h
  have htot := ((hc.comp hφt).add ((htend 0 h00).smul (hg0.comp hφt))).add (hI1.add hI2)
  rw [intervalIntegral.integral_add hatInf hlamintt]
  exact htot.congr fun n => (hcost n).symm

/-- **Complementarity survives the limit.**  If the multiplier densities of the subsequence
eventually vanish on `[α,β]`, the limit multiplier is constant on `[α,β]`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.9. -/
theorem stateMultiplier_limit_eq_of_eventually_density_eq_zero (hT : 0 ≤ T) {m : ℕ → ℝ → ℝ}
    (hm : ∀ n, IntervalIntegrable (m n) volume 0 T) {φ : ℕ → ℕ} {lam : ℝ → ℝ}
    (htend : ∀ t ∈ Icc (0 : ℝ) T,
      Tendsto (fun n => stateMultiplier T (m (φ n)) t) atTop (𝓝 (lam t)))
    {α β : ℝ} (hα : α ∈ Icc (0 : ℝ) T) (hβ : β ∈ Icc (0 : ℝ) T)
    (hzero : ∀ᶠ n in atTop, ∀ r ∈ Icc α β, m (φ n) r = 0) :
    ∀ t ∈ Icc α β, lam t = lam α := by
  intro t ht
  have htI : t ∈ Icc (0 : ℝ) T := ⟨hα.1.trans ht.1, ht.2.trans hβ.2⟩
  refine tendsto_nhds_unique (htend t htI) ((htend α hα).congr' ?_)
  filter_upwards [hzero] with n hn
  exact (stateMultiplier_eq_of_density_eq_zero hT (hm (φ n)) hα hβ hn t ht).symm

end LimitCovector

section Slack

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A strictly slack path stays strictly slack in a uniform tube.**  If `G` is continuous,
`y` is continuous on a compact set `A` of times and `G(r, y r) < 0` for `r ∈ A`, then there is
`η > 0` such that `G(r, z) < 0` whenever `r ∈ A` and `dist z (y r) < η`. -/
theorem exists_slack_radius {G : ℝ → E → ℝ} (hG : Continuous (fun p : ℝ × E => G p.1 p.2))
    {A : Set ℝ} (hA : IsCompact A) {yInf : ℝ → E} (hyInf : ContinuousOn yInf A)
    (hslack : ∀ r ∈ A, G r (yInf r) < 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ r ∈ A, ∀ z : E, dist z (yInf r) < η → G r z < 0 := by
  rcases Set.eq_empty_or_nonempty A with hempty | hne
  · exact ⟨1, one_pos, fun r hr => by simp [hempty] at hr⟩
  -- the maximum of `r ↦ G r (yInf r)` over `A` is negative
  have hcomp : ContinuousOn (fun r => G r (yInf r)) A :=
    hG.comp_continuousOn (continuousOn_id.prodMk hyInf)
  obtain ⟨r₀, hr₀, hmax⟩ := hA.exists_isMaxOn hne hcomp
  set δ : ℝ := -G r₀ (yInf r₀) with hδ
  have hδpos : 0 < δ := by have := hslack r₀ hr₀; linarith
  -- uniform continuity of `G` on a compact tube around the graph of `yInf`
  have hK : IsCompact ((fun q : ℝ × E => (q.1, yInf q.1 + q.2)) ''
      (A ×ˢ Metric.closedBall (0 : E) 1)) := by
    refine (hA.prod (isCompact_closedBall 0 1)).image_of_continuousOn ?_
    exact (continuousOn_fst.prodMk ((hyInf.comp continuousOn_fst (fun q hq => hq.1)).add
      continuousOn_snd))
  have hunifcont := hK.uniformContinuousOn_of_continuous hG.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hunifcont
  obtain ⟨η, hη, hηG⟩ := hunifcont (δ / 2) (by positivity)
  refine ⟨min η 1, lt_min hη one_pos, fun r hr z hz => ?_⟩
  have hd1 : dist z (yInf r) < 1 := hz.trans_le (min_le_right _ _)
  have hdη : dist z (yInf r) < η := hz.trans_le (min_le_left _ _)
  have hmem1 : (r, yInf r) ∈ (fun q : ℝ × E => (q.1, yInf q.1 + q.2)) ''
      (A ×ˢ Metric.closedBall (0 : E) 1) := ⟨(r, 0), ⟨hr, by simp⟩, by simp⟩
  have hmem2 : (r, z) ∈ (fun q : ℝ × E => (q.1, yInf q.1 + q.2)) ''
      (A ×ˢ Metric.closedBall (0 : E) 1) :=
    ⟨(r, z - yInf r), ⟨hr, by simpa [dist_eq_norm] using hd1.le⟩, by simp⟩
  have hclose := hηG (r, z) hmem2 (r, yInf r) hmem1 (by
    rw [Prod.dist_eq]
    simpa using hdη)
  rw [Real.dist_eq] at hclose
  have h1 := (abs_lt.1 hclose).2
  have h2 : G r (yInf r) ≤ G r₀ (yInf r₀) := hmax hr
  linarith

/-- **A strictly slack limit path is eventually slack along a uniformly convergent sequence.**
If `G` is continuous, `y n → y` uniformly on `[α,β]` and `G(r, y r) < 0` on `[α,β]`, then
eventually `G(r, y n r) ≤ 0` on all of `[α,β]`. -/
theorem eventually_nonpos_of_uniformConvergence {G : ℝ → E → ℝ}
    (hG : Continuous (fun p : ℝ × E => G p.1 p.2)) {y : ℕ → ℝ → E} {yInf : ℝ → E} {α β : ℝ}
    (hyInf : ContinuousOn yInf (Icc α β))
    (hunif : ∀ ε > 0, ∀ᶠ n in atTop, ∀ r ∈ Icc α β, dist (y n r) (yInf r) < ε)
    (hslack : ∀ r ∈ Icc α β, G r (yInf r) < 0) :
    ∀ᶠ n in atTop, ∀ r ∈ Icc α β, G r (y n r) ≤ 0 := by
  obtain ⟨η, hη, hηG⟩ := exists_slack_radius hG isCompact_Icc hyInf hslack
  filter_upwards [hunif η hη] with n hn r hr
  exact (hηG r hr _ (hn r hr)).le

end Slack


section Assembly

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

/-- A sequence of minimisers of the `ω`-penalised functionals `H^{j_n}` on the velocity carrier:
`path n` minimises `functional n = ∫₀ᵀ (L + j_n ω(G)) + Φ₀(γ 0) + Φ₁(γ 0, γ T)` over the set
`competitors n`, which contains all scalar-profile perturbations of `path n` for small parameter
(the
strict interior of the tube `B(ε)`).  This is the output of Lemma 11.3.4 for the functionals
`H^j_{K(ε)}` of (11.3.8) at the levels `j = j_n → ∞`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.8), Lemma 11.3.4. -/
structure PenalisedMinimiserSequence (P : Problem E V W) (L : ℝ → E → E → ℝ)
    (G : ℝ → E → ℝ) (ω : ℝ → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) where
  /-- The `n`-th minimiser `γ_n`. -/
  path : ℕ → VelocityTrajectory P
  /-- The penalty weights `j_n`. -/
  penalty : ℕ → ℝ
  /-- The weights are nonnegative. -/
  penalty_nonneg : ∀ n, 0 ≤ penalty n
  /-- The `n`-th penalised functional `H^{j_n}`. -/
  functional : ℕ → VelocityTrajectory P → ℝ
  /-- The competitor set of the `n`-th problem (the tube `B(ε)`). -/
  competitors : ℕ → Set (VelocityTrajectory P)
  /-- The functionals are the `ω`-penalised actions. -/
  functional_eq : ∀ n (γ' : VelocityTrajectory P),
    functional n γ' = actionFunctional (statePenalisedLagrangian L G ω (penalty n)) Φ₀ Φ₁
      P.horizon γ'.initial γ'.velocity
  /-- Each `path n` minimises `functional n` on `competitors n`. -/
  isMinOn : ∀ n, IsMinOn (functional n) (competitors n) (path n)
  /-- Every scalar-profile perturbation of `path n` is a competitor for small parameter. -/
  interior : ∀ n (e : E) (α : ℝ) (s : ℝ → ℝ) (hs : MemLp s 2 (timeMeasure P.horizon)),
    ∀ᶠ θ in 𝓝 (0 : ℝ), (path n).perturbProfile e α s hs θ ∈ competitors n
  /-- The penalised Lagrangian is integrable along each minimiser. -/
  integrable : ∀ n, IntervalIntegrable
    (fun t => statePenalisedLagrangian L G ω (penalty n) t ((path n).value t)
      ((path n).velocity t)) volume 0 P.horizon
  /-- The initial penalty is differentiable at each initial value. -/
  differentiable₀ : ∀ n, DifferentiableAt ℝ Φ₀ ((path n).value 0)
  /-- The endpoint penalty is differentiable at each pair of endpoint values. -/
  differentiable₁ : ∀ n, DifferentiableAt ℝ Φ₁ ((path n).value 0, (path n).value P.horizon)

/-- The limit costate `Φ(t) = c + λ(0) g(0) + ∫₀ᵗ (a + λ g')` of the penalised costate equations:
the solution of `Φ' = a + λ g'` (with `a = ∂ₓL` and `g' = d(∇G)/dt` along the limit path) with the
initial value `c + λ(0) ∇G(0)` of (11.6.6).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.6) and (11.6.11). -/
noncomputable def limitStateCostate (c : E →L[ℝ] ℝ) (lam : ℝ → ℝ) (g0 : E →L[ℝ] ℝ)
    (a gd : ℝ → E →L[ℝ] ℝ) (t : ℝ) : E →L[ℝ] ℝ :=
  (c + lam 0 • g0) + ∫ r in (0 : ℝ)..t, (a r + lam r • gd r)

/-- The conclusion of the `j → ∞` limit theorem: there is a subsequence and a nonincreasing
multiplier `lam` with values in `[0,M]` and `lam T = 0`, to which the penalised multipliers converge
everywhere, such that the limit costate (`limitStateCostate`) satisfies the costate equation
(11.6.11) a.e., the initial condition (11.6.6), the terminal condition (11.6.16), the momentum
identity `∂ᵥL = Φ - λ ∇G`, complementarity, and the endpoint behaviour forced by Assumption 11.4.1.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.6), (11.6.11),
(11.6.15)-(11.6.16), Assumption 11.4.1. -/
def PenalisedMultiplierLimit {L : ℝ → E → E → ℝ} (Lx Lv : ℝ → E → E → E →L[ℝ] ℝ) (ω' : ℝ → ℝ)
    (G : ℝ → E → ℝ) (Gx : ℝ → E → E →L[ℝ] ℝ)
    (Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)) {ω : ℝ → ℝ} {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ}
    (seq : PenalisedMinimiserSequence P L G ω Φ₀ Φ₁) (γL : VelocityTrajectory P) (M : ℝ) :
    Prop :=
  ∃ (φ : ℕ → ℕ) (lam : ℝ → ℝ), StrictMono φ ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon,
        Tendsto (fun n => stateMultiplier P.horizon (statePenaltyDensity ω' G (seq.penalty (φ n))
          (seq.path (φ n))) t) atTop (𝓝 (lam t))) ∧
      AntitoneOn lam (Icc (0 : ℝ) P.horizon) ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, 0 ≤ lam t ∧ lam t ≤ M) ∧ lam P.horizon = 0 ∧
      (∀ᵐ t ∂(timeMeasure P.horizon), HasDerivAt
        (limitStateCostate
          (fderiv ℝ Φ₀ (γL.value 0) + (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp
            (ContinuousLinearMap.inl ℝ E E)) lam (Gx 0 (γL.value 0))
          (fun r => Lx r (γL.value r) (γL.velocity r))
          (fun r => Gxd r (γL.value r) (1, γL.velocity r)))
        (Lx t (γL.value t) (γL.velocity t) + lam t • Gxd t (γL.value t) (1, γL.velocity t)) t) ∧
      limitStateCostate
          (fderiv ℝ Φ₀ (γL.value 0) + (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp
            (ContinuousLinearMap.inl ℝ E E)) lam (Gx 0 (γL.value 0))
          (fun r => Lx r (γL.value r) (γL.velocity r))
          (fun r => Gxd r (γL.value r) (1, γL.velocity r)) 0
        = fderiv ℝ Φ₀ (γL.value 0) + (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp
            (ContinuousLinearMap.inl ℝ E E) + lam 0 • Gx 0 (γL.value 0) ∧
      limitStateCostate
          (fderiv ℝ Φ₀ (γL.value 0) + (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp
            (ContinuousLinearMap.inl ℝ E E)) lam (Gx 0 (γL.value 0))
          (fun r => Lx r (γL.value r) (γL.velocity r))
          (fun r => Gxd r (γL.value r) (1, γL.velocity r)) P.horizon
        = -((fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp
            (ContinuousLinearMap.inr ℝ E E)) ∧
      (∀ᵐ t ∂(timeMeasure P.horizon), Lv t (γL.value t) (γL.velocity t)
        = limitStateCostate
          (fderiv ℝ Φ₀ (γL.value 0) + (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp
            (ContinuousLinearMap.inl ℝ E E)) lam (Gx 0 (γL.value 0))
          (fun r => Lx r (γL.value r) (γL.velocity r))
          (fun r => Gxd r (γL.value r) (1, γL.velocity r)) t - lam t • Gx t (γL.value t)) ∧
      (∀ α β : ℝ, α ∈ Icc (0 : ℝ) P.horizon → β ∈ Icc (0 : ℝ) P.horizon →
        (∀ r ∈ Icc α β, G r (γL.value r) < 0) → ∀ t ∈ Icc α β, lam t = lam α) ∧
      (∀ δ : ℝ, 0 < δ → δ < P.horizon → (∀ t ∈ Icc (0 : ℝ) P.horizon,
          (t < δ ∨ P.horizon - δ < t) → G t (γL.value t) < 0) →
        (∀ t ∈ Icc (0 : ℝ) (δ / 2), lam t = lam 0) ∧
          ∀ t ∈ Icc (P.horizon - δ / 2) P.horizon, lam t = 0)

/-- **The `j → ∞` limit of the penalised costate equations for an active state constraint
(the missing `∇G` multiplier of Berkovitz & Medhin Theorem 11.6.3).**

Let `γ n` minimise the `ω`-penalised functional `H^{j_n}` (`j_n ≥ 0`) on a set `S n` containing
its scalar-profile perturbations, and let `γL` be the limit furnished by Lemma 11.3.5: the paths
converge uniformly on `[0,T]`, `∂ₓL(γ_n,γ_n') → ∂ₓL(γL,γL')` and
`∇²G(γ_n)(1,γ_n') → ∇²G(γL)(1,γL')` in `L¹`, `∂ᵥL(γ_n,γ_n') → ∂ᵥL(γL,γL')` a.e., the endpoint
penalties are `C¹` at the limit endpoint data, and the multiplier masses `∫₀ᵀ j_n ω'(G(γ_n))` are
bounded (`integral_density_eq_boundary` with `h = ∇G/|∇G|²`).  Then along a subsequence there is a
nonincreasing multiplier `λ : [0,T] → [0,M]`, `λ(T) = 0`, such that the costate
`Φ = limitStateCostate` (`Φ(t) = c∞ + λ(0) ∇G(0,γL 0) + ∫₀ᵗ (∂ₓL + λ d(∇G)/dt)`) satisfies

* `Φ(T) = -∂₂Φ₁(γL 0, γL T)`  — (11.6.16), and `Φ(0) = ∂Φ₀ + ∂₁Φ₁ + λ(0) ∇G(0, γL 0)`
  — (11.6.6), with `d(∇G)/dt = ∇²G (1, γL')` and no measure in the equation (11.6.11);
* `∂ᵥL(γL, γL') = Φ - λ ∇G(·, γL)` a.e.;
* **complementarity:** `λ` is constant on every interval `[α,β]` on which `G(·,γL) < 0`;
* **Assumption 11.4.1** (`G(t, γL t) < 0` for `t < δ` and `t > T - δ`): `λ` is constant on
  `[0, δ/2]` and vanishes on `[T - δ/2, T]`, so the limit multiplier measure has no atom at the
  endpoints.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5, Assumption 11.4.1,
(11.6.6), (11.6.11), (11.6.15)-(11.6.16). -/
theorem exists_stateMultiplier_limit_of_penalisedMinimisers
    {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}
    (hD : IsCaratheodoryC1 P.horizon L Lx Lv) {ω ω' : ℝ → ℝ}
    (hω : StatePenaltyProfile ω ω') {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    (hG : StateConstraintRegularity G Gx) (hGc : Continuous (fun p : ℝ × E => G p.1 p.2))
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)} (hGx : StateGradientRegularity Gx Gxd)
    {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ} (seq : PenalisedMinimiserSequence P L G ω Φ₀ Φ₁)
    (γL : VelocityTrajectory P)
    (hpath : ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) P.horizon,
      dist ((seq.path n).value t) (γL.value t) < ε)
    (hLx : Tendsto (fun n => ∫ r in (0 : ℝ)..P.horizon,
      ‖Lx r ((seq.path n).value r) ((seq.path n).velocity r) - Lx r (γL.value r) (γL.velocity r)‖)
      atTop (𝓝 0))
    (hGd : Tendsto (fun n => ∫ r in (0 : ℝ)..P.horizon,
      ‖Gxd r ((seq.path n).value r) (1, (seq.path n).velocity r)
        - Gxd r (γL.value r) (1, γL.velocity r)‖) atTop (𝓝 0))
    (hLv : ∀ᵐ t ∂(timeMeasure P.horizon), Tendsto
      (fun n => Lv t ((seq.path n).value t) ((seq.path n).velocity t)) atTop
      (𝓝 (Lv t (γL.value t) (γL.velocity t))))
    (hΦ₀c : ContinuousAt (fderiv ℝ Φ₀) (γL.value 0))
    (hΦ₁c : ContinuousAt (fderiv ℝ Φ₁) (γL.value 0, γL.value P.horizon))
    {M : ℝ} (hM : ∀ n, ∫ r in (0 : ℝ)..P.horizon,
      statePenaltyDensity ω' G (seq.penalty n) (seq.path n) r ≤ M) :
    PenalisedMultiplierLimit Lx Lv ω' G Gx Gxd seq γL M := by
  classical
  unfold PenalisedMultiplierLimit
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  have hT0 : P.horizon ∈ Icc (0 : ℝ) P.horizon := ⟨hT, le_rfl⟩
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) P.horizon := ⟨le_rfl, hT⟩
  choose c hEL h0 hTT using fun n => (seq.path n).statePenalised_weakEulerLagrange (seq.functional
      n) (seq.competitors n) hD hω hG
    (seq.penalty n) (seq.functional_eq n) (seq.isMinOn n) (seq.interior n) (seq.integrable n)
        (seq.differentiable₀ n) (seq.differentiable₁ n)
  have hgrad := fun n => (seq.path n).gradientAlongPath_eq_primitive hGx
  have hgradL := γL.gradientAlongPath_eq_primitive hGx
  have hmint : ∀ n, IntervalIntegrable (statePenaltyDensity ω' G (seq.penalty n) (seq.path n))
      volume 0
      P.horizon := fun n => intervalIntegrable_statePenaltyDensity hω hG (seq.penalty n) (seq.path
          n)
  have hm0 : ∀ n, ∀ r ∈ Icc (0 : ℝ) P.horizon, 0 ≤ statePenaltyDensity ω' G (seq.penalty n)
      (seq.path n) r :=
    fun n r _ => statePenaltyDensity_nonneg hω G (seq.penalty_nonneg n) (seq.path n) r
  have haint : ∀ n, IntervalIntegrable (fun r => Lx r ((seq.path n).value r) ((seq.path n).velocity
      r))
      volume 0 P.horizon := fun n =>
    intervalIntegrable_of_memLp hT (memLp_stateGradient hD hT (seq.path n).memLp_velocity (seq.path
        n).initial)
  have haintL : IntervalIntegrable (fun r => Lx r (γL.value r) (γL.velocity r)) volume 0
      P.horizon :=
    intervalIntegrable_of_memLp hT (memLp_stateGradient hD hT γL.memLp_velocity γL.initial)
  -- convergence of the endpoint data
  have hpt : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      Tendsto (fun n => (seq.path n).value t) atTop (𝓝 (γL.value t)) := fun t ht =>
    Metric.tendsto_nhds.2 fun ε hε => (hpath ε hε).mono fun n hn => hn t ht
  have hend : Tendsto (fun n => ((seq.path n).value 0, (seq.path n).value P.horizon)) atTop
      (𝓝 (γL.value 0, γL.value P.horizon)) := (hpt 0 h00).prodMk_nhds (hpt _ hT0)
  have hF1 : Tendsto (fun n => fderiv ℝ Φ₁ ((seq.path n).value 0, (seq.path n).value P.horizon))
      atTop
      (𝓝 (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon))) := hΦ₁c.tendsto.comp hend
  have hF0 : Tendsto (fun n => fderiv ℝ Φ₀ ((seq.path n).value 0)) atTop
      (𝓝 (fderiv ℝ Φ₀ (γL.value 0))) := hΦ₀c.tendsto.comp (hpt 0 h00)
  have hF1l : Tendsto (fun n => (fderiv ℝ Φ₁ ((seq.path n).value 0, (seq.path n).value
      P.horizon)).comp
      (ContinuousLinearMap.inl ℝ E E)) atTop
      (𝓝 ((fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp
        (ContinuousLinearMap.inl ℝ E E))) :=
    ((continuous_id.clm_comp_const (ContinuousLinearMap.inl ℝ E E)).tendsto _).comp hF1
  have hcn : Tendsto c atTop (𝓝 (fderiv ℝ Φ₀ (γL.value 0)
      + (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp (ContinuousLinearMap.inl ℝ E E))) :=
    (hF0.add (hF1l)).congr fun n => (h0 n).symm
  have hqn : Tendsto (fun n => (fderiv ℝ Φ₁ ((seq.path n).value 0, (seq.path n).value
      P.horizon)).comp
      (ContinuousLinearMap.inr ℝ E E)) atTop
      (𝓝 ((fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp
        (ContinuousLinearMap.inr ℝ E E))) :=
    ((continuous_id.clm_comp_const (ContinuousLinearMap.inr ℝ E E)).tendsto _).comp hF1
  have hg0 : Tendsto (fun n => Gx 0 ((seq.path n).value 0)) atTop (𝓝 (Gx 0 (γL.value 0))) :=
    (hGx.hasFDerivAt 0 (γL.value 0)).continuousAt.tendsto.comp
      (tendsto_const_nhds.prodMk_nhds (hpt 0 h00))
  obtain ⟨φ, lam, hφ, htend, hanti, hbd, hlamT, hlamint, hcost⟩ := exists_stateMultiplier_limit hT
    (m := fun n => statePenaltyDensity ω' G (seq.penalty n) (seq.path n)) hmint hm0 hM (c := c)
    (cInf := fderiv ℝ Φ₀ (γL.value 0)
      + (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp (ContinuousLinearMap.inl ℝ E E))
    (a := fun n r => Lx r ((seq.path n).value r) ((seq.path n).velocity r))
    (g' := fun n r => Gxd r ((seq.path n).value r) (1, (seq.path n).velocity r))
    (g := fun n r => Gx r ((seq.path n).value r))
    (aInf := fun r => Lx r (γL.value r) (γL.velocity r))
    (gdInf := fun r => Gxd r (γL.value r) (1, γL.velocity r)) (gInf0 := Gx 0 (γL.value 0))
    haint (fun n => (hgrad n).1) (fun n => (hgrad n).2) haintL hgradL.1 hcn hg0 hLx hGd
  have hφt := hφ.tendsto_atTop
  -- complementarity of the limit
  have hcompl : ∀ α β : ℝ, α ∈ Icc (0 : ℝ) P.horizon → β ∈ Icc (0 : ℝ) P.horizon →
      (∀ r ∈ Icc α β, G r (γL.value r) < 0) → ∀ t ∈ Icc α β, lam t = lam α := by
    intro α β hα hβ hslack
    refine stateMultiplier_limit_eq_of_eventually_density_eq_zero hT
      (m := fun n => statePenaltyDensity ω' G (seq.penalty n) (seq.path n)) hmint htend hα hβ ?_
    have hsubαβ : Icc α β ⊆ Icc (0 : ℝ) P.horizon := fun r hr =>
      ⟨hα.1.trans hr.1, hr.2.trans hβ.2⟩
    have hev := eventually_nonpos_of_uniformConvergence hGc
      (y := fun n => (seq.path (φ n)).value) (yInf := γL.value) (α := α) (β := β)
      (γL.continuousOn_value.mono hsubαβ)
      (fun ε hε => (hφt.eventually (hpath ε hε)).mono fun n hn r hr => hn r (hsubαβ hr))
      hslack
    filter_upwards [hev] with n hn r hr
    exact statePenaltyDensity_eq_zero_of_nonpos hω G (seq.penalty (φ n)) (seq.path (φ n)) (hn r hr)
  -- terminal condition
  have hterm : ∀ n, stateCostate P.horizon (statePenaltyDensity ω' G (seq.penalty n) (seq.path n))
      (c n)
      (fun r => Lx r ((seq.path n).value r) ((seq.path n).velocity r)) (fun r => Gx r ((seq.path
          n).value r))
      P.horizon = -((fderiv ℝ Φ₁ ((seq.path n).value 0, (seq.path n).value P.horizon)).comp
        (ContinuousLinearMap.inr ℝ E E)) := by
    intro n
    simp only [stateCostate, stateMultiplier_horizon, zero_smul, add_zero]
    exact hTT n
  have hterminal := tendsto_nhds_unique (hcost P.horizon hT0)
    ((hqn.comp hφt).neg.congr fun n => (hterm (φ n)).symm)
  -- the momentum identity in the limit
  have hmom : ∀ᵐ t ∂(timeMeasure P.horizon), Lv t (γL.value t) (γL.velocity t)
      = limitStateCostate
        (fderiv ℝ Φ₀ (γL.value 0) + (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp
          (ContinuousLinearMap.inl ℝ E E)) lam (Gx 0 (γL.value 0))
        (fun r => Lx r (γL.value r) (γL.velocity r))
        (fun r => Gxd r (γL.value r) (1, γL.velocity r)) t - lam t • Gx t (γL.value t) := by
    have hall : ∀ᵐ t ∂(timeMeasure P.horizon), ∀ n, Lv t ((seq.path n).value t) ((seq.path
        n).velocity t)
        = c n + ∫ r in (0 : ℝ)..t, (Lx r ((seq.path n).value r) ((seq.path n).velocity r)
          + (seq.penalty n * ω' (G r ((seq.path n).value r))) • Gx r ((seq.path n).value r)) :=
      ae_all_iff.2 hEL
    filter_upwards [hall, hLv, ae_restrict_mem measurableSet_Ioc] with t ht1 ht2 htm
    have htI : t ∈ Icc (0 : ℝ) P.horizon := ⟨htm.1.le, htm.2⟩
    have hgt : Tendsto (fun n => Gx t ((seq.path (φ n)).value t)) atTop (𝓝 (Gx t (γL.value t))) :=
      (hGx.hasFDerivAt t (γL.value t)).continuousAt.tendsto.comp
        (tendsto_const_nhds.prodMk_nhds ((hpt t htI).comp hφt))
    have hrhs := (hcost t htI).sub ((htend t htI).smul hgt)
    refine tendsto_nhds_unique (ht2.comp hφt) (hrhs.congr fun n => ?_)
    change _ = Lv t ((seq.path (φ n)).value t) ((seq.path (φ n)).velocity t)
    rw [ht1 (φ n)]
    simp [stateCostate, statePenaltyDensity]
  have hprim : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      limitStateCostate (fderiv ℝ Φ₀ (γL.value 0)
          + (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp (ContinuousLinearMap.inl ℝ E E))
        lam (Gx 0 (γL.value 0)) (fun r => Lx r (γL.value r) (γL.velocity r))
        (fun r => Gxd r (γL.value r) (1, γL.velocity r)) t
      = limitStateCostate (fderiv ℝ Φ₀ (γL.value 0)
          + (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp (ContinuousLinearMap.inl ℝ E E))
        lam (Gx 0 (γL.value 0)) (fun r => Lx r (γL.value r) (γL.velocity r))
        (fun r => Gxd r (γL.value r) (1, γL.velocity r)) 0
        + ∫ r in (0 : ℝ)..t, (Lx r (γL.value r) (γL.velocity r)
          + lam r • Gxd r (γL.value r) (1, γL.velocity r)) := by
    intro t _
    simp [limitStateCostate]
  refine ⟨φ, lam, hφ, htend, hanti, hbd, hlamT, ?_, ?_, ?_, hmom, hcompl, ?_⟩
  · exact ae_hasDerivAt_of_eq_primitive hT (haintL.add hlamint) hprim
  · simp [limitStateCostate]
  · exact hterminal
  · intro δ hδ hδT hslack
    refine ⟨?_, ?_⟩
    · intro t ht
      exact hcompl 0 (δ / 2) h00 ⟨by linarith, by linarith⟩ (fun r hr => hslack r
        ⟨hr.1, by linarith [hr.2]⟩ (Or.inl (by linarith [hr.2]))) t ht
    · intro t ht
      have hα : P.horizon - δ / 2 ∈ Icc (0 : ℝ) P.horizon := ⟨by linarith, by linarith⟩
      have hc := hcompl (P.horizon - δ / 2) P.horizon hα hT0 (fun r hr =>
        hslack r ⟨by linarith [hr.1], hr.2⟩ (Or.inr (by linarith [hr.1])))
      rw [hc t ht, ← hc P.horizon ⟨by linarith, le_rfl⟩]
      exact hlamT

end Assembly

end OptimalControl.BoundedState
