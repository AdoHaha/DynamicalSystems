/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.EpsilonHamiltonianBridge
public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwiseMinimizerEndpointConditions

/-!
# `L¹` convergence of the normalised penalty covectors

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.38), §11.4.

The Hamiltonian of the `ε`-level inequality uses the penalty covector
`Θ_k = 2K_kT⟨γ_k' − f̄_k, ·⟩`.  By the momentum identity `ψ_k = Φ_k − λ_k∇G`, i.e.
`2K_k⟨γ_k' − f̄_k,·⟩ = Φ_k − λ_k∇G − 2⟨γ_k' − φ₀',·⟩` a.e., the normalised covectors satisfy
`Θ_k/M_k = T((Φ_k − λ_k ∇G)/M_k − defect_k/M_k)` and therefore converge in `L¹` to
`T(Φ − λ∇G₀)` when the normalised costates converge pointwise and boundedly, the
multipliers converge pointwise and `φ_k' → φ₀'` in `L¹`.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]

namespace Problem

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- On the line, the time measure `volume|(0,T]` is the push-forward of horizon volume. -/
theorem timeMeasure_eq_map_horizonVolume (T : ℝ) :
    ACEulerLagrange.timeMeasure T = (horizonVolume T).map ((↑) : ControlTime T → ℝ) := by
  rw [map_horizonVolume]
  exact Measure.restrict_congr_set Ioc_ae_eq_Icc

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- A normalised horizon integral of a line function is `T⁻¹` times its `(0,T]` integral. -/
theorem integral_horizonProbability_coe (P : Problem E V W) (f : ℝ → ℝ) :
    ∫ t : P.Time, f t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure
      = P.horizon⁻¹ * ∫ t, f t ∂(ACEulerLagrange.timeMeasure P.horizon) := by
  rw [timeMeasure_eq_map_horizonVolume,
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).integral_map]
  change ∫ t, f t ∂((ENNReal.ofReal P.horizon)⁻¹ • horizonVolume P.horizon) = _
  rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal P.horizon_pos.le]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- A line function integrable on `(0,T]` restricts to a function integrable for the normalised
horizon marginal. -/
theorem integrable_horizonProbability_coe (P : Problem E V W) {f : ℝ → ℝ}
    (hf : Integrable f (ACEulerLagrange.timeMeasure P.horizon)) :
    Integrable (fun t : P.Time => f t) (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  rw [timeMeasure_eq_map_horizonVolume] at hf
  have h2 := (MeasurableEmbedding.subtype_coe measurableSet_Icc).integrable_map_iff.1 hf
  change Integrable _ ((ENNReal.ofReal P.horizon)⁻¹ • horizonVolume P.horizon)
  exact h2.smul_measure (by simp [P.horizon_pos])

/-- **`L¹` convergence of the normalised penalty covectors.** -/
theorem tendsto_integral_norm_penaltyCovector_sub (P : Problem E V W)
    {K : ℕ → ℝ} {γ₀ : VelocityTrajectory P} {γ : ℕ → VelocityTrajectory P}
    {ρe : ℕ → P.Relaxed} {Gx : ℝ → E → E →L[ℝ] ℝ} {Φ : ℕ → ℝ → E →L[ℝ] ℝ}
    {lam : ℕ → ℝ → ℝ} {M : ℕ → ℝ} (hM : ∀ k, 1 ≤ M k)
    {Ψ g₀ : ℝ → E →L[ℝ] ℝ} {Λ : ℝ → ℝ} {B C : ℝ}
    (hmom : ∀ k, ∀ᵐ t ∂(ACEulerLagrange.timeMeasure P.horizon),
      (2 * K k) • innerSL ℝ ((γ k).velocity t - P.averagedDynamics (ρe k) t ((γ k).value t))
        = Φ k t - lam k t • Gx t ((γ k).value t)
          - (2 : ℝ) • innerSL ℝ ((γ k).velocity t - γ₀.velocity t))
    (hΦc : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      Tendsto (fun k => (1 / M k) • Φ k t) atTop (nhds (Ψ t)))
    (hΛc : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      Tendsto (fun k => (1 / M k) * lam k t) atTop (nhds (Λ t)))
    (hglim : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      Tendsto (fun k => Gx t ((γ k).value t)) atTop (nhds (g₀ t)))
    (hΦb : ∀ k, ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖(1 / M k) • Φ k t‖ ≤ B)
    (hgb : ∀ k, ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖Gx t ((γ k).value t)‖ ≤ C)
    (hlam : ∀ k, ∀ t ∈ Icc (0 : ℝ) P.horizon, 0 ≤ lam k t ∧ (1 / M k) * lam k t ≤ 1)
    (hΨm : AEStronglyMeasurable Ψ (volume.restrict (Ioc (0 : ℝ) P.horizon)))
    (hΛm : AEStronglyMeasurable Λ (volume.restrict (Ioc (0 : ℝ) P.horizon)))
    (hg₀m : AEStronglyMeasurable g₀ (volume.restrict (Ioc (0 : ℝ) P.horizon)))
    (hvlim : Tendsto (fun k => ∫ r in (0 : ℝ)..P.horizon,
      ‖(γ k).velocity r - γ₀.velocity r‖) atTop (nhds 0)) :
    (∀ k, Integrable (fun t : P.Time => ‖(1 / M k) • penaltyCovector P (K k) (γ k) (ρe k) t
        - P.horizon • (Ψ t - Λ t • g₀ t)‖)
      (horizonProbability P.horizon P.horizon_pos).toMeasure) ∧
    Tendsto (fun k => ∫ t : P.Time, ‖(1 / M k) • penaltyCovector P (K k) (γ k) (ρe k) t
        - P.horizon • (Ψ t - Λ t • g₀ t)‖
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure) atTop (nhds 0) := by
  classical
  have hT := P.horizon_pos
  have hMpos : ∀ k, 0 < M k := fun k => lt_of_lt_of_le one_pos (hM k)
  -- the integrand, read on the line
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ → ℝ, ∀ k t, F k t = ‖(1 / M k) • ((2 * K k * P.horizon) •
      innerSL ℝ ((γ k).velocity t - P.averagedDynamics (ρe k) t ((γ k).value t)))
        - P.horizon • (Ψ t - Λ t • g₀ t)‖ := ⟨_, fun _ _ => rfl⟩
  have hFeq : ∀ k (t : P.Time), ‖(1 / M k) • penaltyCovector P (K k) (γ k) (ρe k) t
      - P.horizon • (Ψ t - Λ t • g₀ t)‖ = F k t := by
    intro k t
    rw [hF]
    simp only [penaltyCovector, realizedVelocity_eq_averagedDynamics, toBoundedPath_apply]
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ → ℝ, ∀ k t, v k t = ‖(γ k).velocity t - γ₀.velocity t‖ :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ → ℝ, ∀ k t, a k t = ‖(1 / M k) • Φ k t - Ψ t‖
      + ‖((1 / M k) * lam k t) • Gx t ((γ k).value t) - Λ t • g₀ t‖ := ⟨_, fun _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ → ℝ, ∀ k t, G k t = max (F k t - 2 * P.horizon * v k t) 0 :=
    ⟨_, fun _ _ => rfl⟩
  set μ := ACEulerLagrange.timeMeasure P.horizon with hμ
  -- measurability and integrability on the line
  have hFm : ∀ k, AEStronglyMeasurable (F k) μ := by
    intro k
    have h1 : AEStronglyMeasurable
        (fun t => (γ k).velocity t - P.averagedDynamics (ρe k) t ((γ k).value t)) μ :=
      (γ k).memLp_velocity.aestronglyMeasurable.sub
        (memLp_averagedDynamics_value P (γ k) (ρe k)).aestronglyMeasurable
    have h2 := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable h1
    rw [show F k = _ from funext (hF k)]
    exact (((h2.const_smul (2 * K k * P.horizon)).const_smul (1 / M k)).sub
      ((hΨm.sub (hΛm.smul hg₀m)).const_smul P.horizon)).norm
  have hvm : ∀ k, AEStronglyMeasurable (v k) μ := by
    intro k
    rw [show v k = _ from funext (hv k)]
    exact ((γ k).memLp_velocity.aestronglyMeasurable.sub
      γ₀.memLp_velocity.aestronglyMeasurable).norm
  have hvi : ∀ k, Integrable (v k) μ := by
    intro k
    rw [show v k = _ from funext (hv k)]
    exact (((γ k).memLp_velocity.sub γ₀.memLp_velocity).integrable one_le_two).norm
  have hGm : ∀ k, AEStronglyMeasurable (G k) μ := by
    intro k
    rw [show G k = _ from funext (hG k)]
    exact (((hFm k).sub ((hvm k).const_mul (2 * P.horizon))).aemeasurable.max
      aemeasurable_const).aestronglyMeasurable
  -- the pointwise estimate coming from the momentum identity
  have hkey : ∀ k, ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) P.horizon ∧
      F k t ≤ P.horizon * a k t + 2 * P.horizon * v k t := by
    intro k
    filter_upwards [hmom k, ae_restrict_mem measurableSet_Ioc] with t ht hmem
    refine ⟨Ioc_subset_Icc_self hmem, ?_⟩
    have hsm : (2 * K k * P.horizon) •
        innerSL ℝ ((γ k).velocity t - P.averagedDynamics (ρe k) t ((γ k).value t))
        = P.horizon • ((2 * K k) •
          innerSL ℝ ((γ k).velocity t - P.averagedDynamics (ρe k) t ((γ k).value t))) := by
      rw [smul_smul, mul_comm P.horizon]
    have hid : (1 / M k) • ((2 * K k * P.horizon) •
        innerSL ℝ ((γ k).velocity t - P.averagedDynamics (ρe k) t ((γ k).value t)))
          - P.horizon • (Ψ t - Λ t • g₀ t)
        = P.horizon • (((1 / M k) • Φ k t - Ψ t)
          - (((1 / M k) * lam k t) • Gx t ((γ k).value t) - Λ t • g₀ t)
          - (1 / M k) • ((2 : ℝ) • innerSL ℝ ((γ k).velocity t - γ₀.velocity t))) := by
      rw [hsm, ht]
      module
    have hd : ‖(1 / M k) • ((2 : ℝ) • innerSL ℝ ((γ k).velocity t - γ₀.velocity t))‖
        ≤ 2 * v k t := by
      have hMk := hMpos k
      rw [norm_smul, norm_smul, innerSL_apply_norm, Real.norm_of_nonneg (by positivity),
        Real.norm_two, ← hv]
      have h1 : 1 / M k ≤ 1 := by rw [div_le_one hMk]; exact hM k
      have hv0 : 0 ≤ 2 * v k t := by rw [hv]; positivity
      nlinarith
    rw [hF, hid, norm_smul, Real.norm_of_nonneg hT.le, ha]
    have h3 := norm_sub_le (((1 / M k) • Φ k t - Ψ t)
          - (((1 / M k) * lam k t) • Gx t ((γ k).value t) - Λ t • g₀ t))
          ((1 / M k) • ((2 : ℝ) • innerSL ℝ ((γ k).velocity t - γ₀.velocity t)))
    have h4 := norm_sub_le ((1 / M k) • Φ k t - Ψ t)
          (((1 / M k) * lam k t) • Gx t ((γ k).value t) - Λ t • g₀ t)
    have h5 := mul_le_mul_of_nonneg_left (show ‖((1 / M k) • Φ k t - Ψ t)
          - (((1 / M k) * lam k t) • Gx t ((γ k).value t) - Λ t • g₀ t)
          - (1 / M k) • ((2 : ℝ) • innerSL ℝ ((γ k).velocity t - γ₀.velocity t))‖
        ≤ (‖(1 / M k) • Φ k t - Ψ t‖
          + ‖((1 / M k) * lam k t) • Gx t ((γ k).value t) - Λ t • g₀ t‖) + 2 * v k t by
      linarith) hT.le
    linarith
  -- limits and bounds at a fixed time
  have hΨb : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖Ψ t‖ ≤ B := fun t ht =>
    le_of_tendsto' (hΦc t ht).norm (fun k => hΦb k t ht)
  have hg₀b : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖g₀ t‖ ≤ C := fun t ht =>
    le_of_tendsto' (hglim t ht).norm (fun k => hgb k t ht)
  have hΛb : ∀ t ∈ Icc (0 : ℝ) P.horizon, 0 ≤ Λ t ∧ Λ t ≤ 1 := fun t ht =>
    ⟨ge_of_tendsto' (hΛc t ht) (fun k => mul_nonneg (by have := hMpos k; positivity)
      (hlam k t ht).1), le_of_tendsto' (hΛc t ht) (fun k => (hlam k t ht).2)⟩
  have hab : ∀ k, ∀ t ∈ Icc (0 : ℝ) P.horizon, a k t ≤ 2 * B + 2 * C := by
    intro k t ht
    rw [ha]
    have hc0 : 0 ≤ (1 / M k) * lam k t := mul_nonneg (by have := hMpos k; positivity)
      (hlam k t ht).1
    have e1 := norm_sub_le ((1 / M k) • Φ k t) (Ψ t)
    have e2 := norm_sub_le (((1 / M k) * lam k t) • Gx t ((γ k).value t)) (Λ t • g₀ t)
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hc0, Real.norm_of_nonneg (hΛb t ht).1] at e2
    have e3 : (1 / M k * lam k t) * ‖Gx t ((γ k).value t)‖ ≤ C :=
      (mul_le_mul_of_nonneg_right (hlam k t ht).2 (norm_nonneg _)).trans
        ((one_mul _).le.trans (hgb k t ht))
    have e4 : Λ t * ‖g₀ t‖ ≤ C :=
      (mul_le_mul_of_nonneg_right (hΛb t ht).2 (norm_nonneg _)).trans
        ((one_mul _).le.trans (hg₀b t ht))
    linarith [hΦb k t ht, hΨb t ht]
  have halim : ∀ t ∈ Icc (0 : ℝ) P.horizon, Tendsto (fun k => a k t) atTop (𝓝 0) := by
    intro t ht
    have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (hΦc t ht)
    have h2 := tendsto_iff_norm_sub_tendsto_zero.1 ((hΛc t ht).smul (hglim t ht))
    simp only [ha]
    simpa using h1.add h2
  have hG0 : ∀ k t, 0 ≤ G k t := fun k t => by rw [hG]; exact le_max_right _ _
  have hFG : ∀ k t, F k t ≤ G k t + 2 * P.horizon * v k t := fun k t => by
    rw [hG]; linarith [le_max_left (F k t - 2 * P.horizon * v k t) 0]
  have hGa : ∀ k, ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) P.horizon ∧ G k t ≤ P.horizon * a k t := by
    intro k
    filter_upwards [hkey k] with t ht
    refine ⟨ht.1, ?_⟩
    rw [hG]
    have : 0 ≤ P.horizon * a k t := mul_nonneg hT.le (by rw [ha]; positivity)
    exact max_le (by linarith [ht.2]) this
  have hGb : ∀ k, ∀ᵐ t ∂μ, ‖G k t‖ ≤ P.horizon * (2 * B + 2 * C) := by
    intro k
    filter_upwards [hGa k] with t ht
    rw [Real.norm_of_nonneg (hG0 k t)]
    exact ht.2.trans (mul_le_mul_of_nonneg_left (hab k t ht.1) hT.le)
  have hGi : ∀ k, Integrable (G k) μ := fun k =>
    (integrable_const (P.horizon * (2 * B + 2 * C))).mono' (hGm k) (hGb k)
  have hF0 : ∀ k t, 0 ≤ F k t := fun k t => by rw [hF]; exact norm_nonneg _
  have hFi : ∀ k, Integrable (F k) μ := by
    intro k
    refine ((hGi k).add ((hvi k).const_mul (2 * P.horizon))).mono' (hFm k) ?_
    filter_upwards with t
    rw [Real.norm_of_nonneg (hF0 k t)]
    exact hFG k t
  -- dominated convergence for the bounded part
  have hGlim : Tendsto (fun k => ∫ t, G k t ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ => P.horizon * (2 * B + 2 * C))
      hGm (integrable_const _) hGb (f := fun _ => (0 : ℝ)) ?_
    · simpa using h
    filter_upwards [ae_all_iff.2 hGa] with t ht
    have htI := (ht 0).1
    have hup : Tendsto (fun k => P.horizon * a k t) atTop (𝓝 0) := by
      simpa using (halim t htI).const_mul P.horizon
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (hG0 · t)
      (fun k => (ht k).2)
  have hvlim' : Tendsto (fun k => ∫ t, v k t ∂μ) atTop (𝓝 0) := by
    refine hvlim.congr fun k => ?_
    rw [intervalIntegral.integral_of_le hT.le, hμ]
    exact integral_congr_ae (ae_of_all _ fun t => (hv k t).symm)
  have hFlim : Tendsto (fun k => ∫ t, F k t ∂μ) atTop (𝓝 0) := by
    have hup : Tendsto (fun k => ∫ t, G k t ∂μ + 2 * P.horizon * ∫ t, v k t ∂μ) atTop (𝓝 0) := by
      simpa using hGlim.add (hvlim'.const_mul (2 * P.horizon))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => integral_nonneg (hF0 k)) (fun k => ?_)
    rw [← integral_const_mul, ← integral_add (hGi k) ((hvi k).const_mul _)]
    exact integral_mono (hFi k) ((hGi k).add ((hvi k).const_mul _)) (hFG k)
  simp only [hFeq]
  refine ⟨fun k => integrable_horizonProbability_coe P (hFi k), ?_⟩
  simp only [integral_horizonProbability_coe P]
  simpa using hFlim.const_mul P.horizon⁻¹

end Problem

end OptimalControl.BoundedState
