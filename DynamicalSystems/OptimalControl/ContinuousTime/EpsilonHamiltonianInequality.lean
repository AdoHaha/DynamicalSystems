/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedControlMixture
public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwiseBoundaryPositivity

/-!
# The `ε`-level Hamiltonian inequality (11.3.36)–(11.3.37)

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.35)–(11.3.37), §11.6.

Let `(γ, ρe)` minimise the anchored pointwise penalty `F_K` over the tube `B(ε)` with the control
distance strictly inside the tube.  For every relaxed control `σ` the mixtures `ρ(θ) = (1−θ)ρe + θσ`
lie in the tube for small `θ`; along them the running cost is affine in `θ`, the pointwise defect
energy is quadratic (the realised velocity of a mixture is the mixture of the realised
velocities), and the control-distance term is bounded by convexity.  Comparing `F_K(γ,ρ(θ)) ≥
F_K(γ,ρe)` and letting `θ → 0⁺` gives

`−ε ≤ J(γ,σ) − J(γ,ρe) − 2K⟨γ' − f̄_e, f̄_σ − f̄_e⟩_{L²}`

(the book's (11.3.37) in integrated form, with `ερ'(0⁺) ≤ ε`), where `f̄_ρ` is the control-averaged
dynamics along `γ`.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]

namespace Problem

variable (P : Problem E V W)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- A property holding `ν`-a.e. on the time subtype holds a.e. on the real line along the clamped
time `Set.projIcc`, for the horizon measure. -/
theorem ae_horizonMeasure_projIcc {p : P.Time → Prop}
    (h : ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, p t) :
    ∀ᵐ s ∂(horizonMeasure P.horizon),
      p (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le s) := by
  have hT := P.horizon_pos
  rw [ae_iff] at h
  have hvol : horizonVolume P.horizon {t | ¬p t} = 0 := by
    have h' : ((ENNReal.ofReal P.horizon)⁻¹ • horizonVolume P.horizon) {t | ¬p t} = 0 := h
    rw [Measure.smul_apply, smul_eq_mul] at h'
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    · exact h0
  have himg : volume (((↑) : P.Time → ℝ) '' {t | ¬p t}) = 0 := by
    rw [horizonVolume, (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply] at hvol
    exact hvol
  rw [horizonMeasure, ae_restrict_iff' measurableSet_Ioc, ae_iff]
  refine measure_mono_null (fun s hs => ?_) himg
  simp only [not_imp, mem_ofPred_eq] at hs
  obtain ⟨hsI, hns⟩ := hs
  exact ⟨_, hns, by simp [Set.projIcc_of_mem hT.le (Ioc_subset_Icc_self hsI)]⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] in
/-- The dynamics along a trajectory is integrable in the control against any probability
measure on the compact control set. -/
theorem integrable_dynamics_control (x : P.Trajectory) (t : P.Time) (μ : Measure P.Control)
    [IsProbabilityMeasure μ] :
    Integrable (fun u : P.Control => P.dynamics t (x t) (u : V)) μ := by
  obtain ⟨C, hC⟩ := exists_bound_dynamics_trajectory P x
  have hcont : Continuous fun u : P.Control => P.dynamics t (x t) (u : V) :=
    P.dynamics_continuous.comp
      ((continuous_const.prodMk continuous_const).prodMk continuous_subtype_val)
  exact Integrable.of_bound hcont.aestronglyMeasurable C (Eventually.of_forall fun u => hC t u)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The realised velocity of a mixture is the mixture of the realised velocities, `ν`-a.e. -/
theorem realizedVelocity_mix_ae (x : P.Trajectory) (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (ρ σ : P.Relaxed) :
    ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure,
      realizedVelocity P x (OptimalControl.RelaxedControl.mix θ hθ ρ σ) t
        = (1 - θ) • realizedVelocity P x ρ t + θ • realizedVelocity P x σ t :=
  OptimalControl.RelaxedControl.integral_kernel_mix_ae (f := fun z : P.Time × P.Control =>
      P.dynamics z.1 (x z.1) (z.2 : V)) θ hθ ρ σ
    (Eventually.of_forall fun t => integrable_dynamics_control P x t _)
    (Eventually.of_forall fun t => integrable_dynamics_control P x t _)

omit [CompleteSpace E] in
/-- The realised velocity class of a mixture of relaxed controls is the mixture of the classes. -/
theorem realizedVelocityLp_mix (x : P.Trajectory) (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (ρ σ : P.Relaxed) :
    realizedVelocityLp P x (OptimalControl.RelaxedControl.mix θ hθ ρ σ)
      = (1 - θ) • realizedVelocityLp P x ρ + θ • realizedVelocityLp P x σ := by
  apply Lp.ext
  filter_upwards [realizedVelocityLp_coeFn P x (OptimalControl.RelaxedControl.mix θ hθ ρ σ),
    realizedVelocityLp_coeFn P x ρ, realizedVelocityLp_coeFn P x σ,
    Lp.coeFn_add ((1 - θ) • realizedVelocityLp P x ρ) (θ • realizedVelocityLp P x σ),
    Lp.coeFn_smul (1 - θ) (realizedVelocityLp P x ρ), Lp.coeFn_smul θ (realizedVelocityLp P x σ),
    ae_horizonMeasure_projIcc P (p := fun t => realizedVelocity P x
      (OptimalControl.RelaxedControl.mix θ hθ ρ σ) t
        = (1 - θ) • realizedVelocity P x ρ t + θ • realizedVelocity P x σ t)
      (realizedVelocity_mix_ae P x θ hθ ρ σ)]
    with s hm hρ hσ hadd hs1 hs2 hmix
  rw [hm, hadd, Pi.add_apply, hs1, hs2, Pi.smul_apply, Pi.smul_apply, hρ, hσ]
  exact hmix

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The relaxed running cost is affine along mixtures. -/
theorem relaxedCost_mix (x : P.Trajectory) (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (ρ σ : P.Relaxed) :
    P.relaxedCost x (OptimalControl.RelaxedControl.mix θ hθ ρ σ)
      = (1 - θ) * P.relaxedCost x ρ + θ * P.relaxedCost x σ := by
  have hcont : Continuous fun z : P.Time × P.Control => P.runningCost z.1 (x z.1) (z.2 : V) :=
    P.runningCost_continuous.comp
      (((continuous_fst).prodMk (x.continuous.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hint : ∀ μ : Measure (P.Time × P.Control), IsFiniteMeasure μ →
      Integrable (fun z : P.Time × P.Control => P.runningCost z.1 (x z.1) (z.2 : V)) μ :=
    fun μ _ => hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact OptimalControl.RelaxedControl.integral_mix θ hθ ρ σ (hint _ inferInstance)
    (hint _ inferInstance)

/-- **The `ε`-level Hamiltonian inequality** (BM (11.3.36)–(11.3.37), integrated form). -/
theorem epsilonHamiltonian_inequality (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (γ₀ γ : VelocityTrajectory P) (ρ₀ ρe : P.Relaxed)
    (hmem : InVelocityControlTube P γ₀ ρ₀ ε γ ρe)
    (hlt : relaxedControlDistance P ρe ρ₀ < ε)
    (hmin : ∀ (γ' : VelocityTrajectory P) (ρ' : P.Relaxed),
      InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
        velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ ρe ≤
          velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ' ρ')
    (σ : P.Relaxed) :
    -ε ≤ P.relaxedCost (toBoundedPath γ) σ - P.relaxedCost (toBoundedPath γ) ρe
      - 2 * K * inner ℝ (γ.toLp - realizedVelocityLp P (toBoundedPath γ) ρe)
          (realizedVelocityLp P (toBoundedPath γ) σ
            - realizedVelocityLp P (toBoundedPath γ) ρe) := by
  set x := toBoundedPath γ with hx
  set a := γ.toLp - realizedVelocityLp P x ρe with ha
  set b := realizedVelocityLp P x σ - realizedVelocityLp P x ρe with hb
  set d := relaxedControlDistance P ρe ρ₀ with hd
  set dσ := relaxedControlDistance P σ ρ₀ with hdσ
  set c := P.relaxedCost x σ - P.relaxedCost x ρe - 2 * K * inner ℝ a b with hc
  have hd0 : 0 ≤ d := relaxedControlDistance_nonneg P ρe ρ₀
  have hdσ1 : dσ ≤ 1 := OptimalControl.RelaxedControl.kernelDistance_le_one σ ρ₀
  have hdσ0 : 0 ≤ dσ := relaxedControlDistance_nonneg P σ ρ₀
  -- the key estimate along the mixtures
  have key : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → θ ≤ ε - d →
      0 ≤ θ * (c + ε) + K * θ ^ 2 * ‖b‖ ^ 2 := by
    intro θ hθ0 hθ1 hθε
    have hθ : θ ∈ Icc (0 : ℝ) 1 := ⟨hθ0.le, hθ1⟩
    set m := OptimalControl.RelaxedControl.mix θ hθ ρe σ with hm
    have hdm : relaxedControlDistance P m ρ₀ ≤ (1 - θ) * d + θ * dσ :=
      OptimalControl.RelaxedControl.kernelDistance_mix_le θ hθ ρe σ ρ₀
    have htube : InVelocityControlTube P γ₀ ρ₀ ε γ m := by
      refine ⟨hmem.1, hdm.trans ?_⟩
      nlinarith
    have hF := hmin γ m htube
    have hdef : pointwiseDefectEnergy P γ m
        = ‖a‖ ^ 2 - 2 * θ * inner ℝ a b + θ ^ 2 * ‖b‖ ^ 2 := by
      have heq : γ.toLp - realizedVelocityLp P x m = a - θ • b := by
        rw [hm, realizedVelocityLp_mix, ha, hb]
        module
      rw [pointwiseDefectEnergy, ← hx, heq, norm_sub_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hθ0]
      ring
    have hdefe : pointwiseDefectEnergy P γ ρe = ‖a‖ ^ 2 := rfl
    have hJ : P.relaxedCost x m = (1 - θ) * P.relaxedCost x ρe + θ * P.relaxedCost x σ :=
      relaxedCost_mix P x θ hθ ρe σ
    simp only [velocityPenalizedPointwiseAnchored, velocityPenalizedPointwise,
      velocityPenaltyRemainderPointwise, ← hx, hdef, hdefe, hJ, ← hd] at hF
    have h1 : 0 ≤ ε * θ * (1 - dσ) := mul_nonneg (mul_nonneg hε hθ0.le) (by linarith)
    have h2 : 0 ≤ ε * θ * d := mul_nonneg (mul_nonneg hε hθ0.le) hd0
    have hεd : ε * relaxedControlDistance P m ρ₀ ≤ ε * ((1 - θ) * d + θ * dσ) :=
      mul_le_mul_of_nonneg_left hdm hε
    rw [hc]
    linear_combination hF + hεd + h1 + h2
  by_contra hneg
  push Not at hneg
  set δ := -(c + ε) with hδ
  have hδ0 : 0 < δ := by rw [hδ, hc]; linarith
  set M := K * ‖b‖ ^ 2 with hM
  have hM0 : 0 ≤ M := mul_nonneg hK (sq_nonneg _)
  set θ := min (min 1 (ε - d)) (δ / (M + 1)) with hθdef
  have hθ0 : 0 < θ := lt_min (lt_min one_pos (by linarith)) (div_pos hδ0 (by linarith))
  have hθ1 : θ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hθε : θ ≤ ε - d := (min_le_left _ _).trans (min_le_right _ _)
  have hθδ : θ ≤ δ / (M + 1) := min_le_right _ _
  have hk := key θ hθ0 hθ1 hθε
  have hθM : θ * M < δ := by
    have h1 : θ * (M + 1) ≤ δ := (le_div_iff₀ (by linarith)).mp hθδ
    nlinarith
  have : 0 ≤ θ * (-δ + θ * M) := by
    have : θ * (c + ε) + K * θ ^ 2 * ‖b‖ ^ 2 = θ * (-δ + θ * M) := by rw [hδ, hM]; ring
    linarith
  have : -δ + θ * M < 0 := by linarith
  nlinarith

end Problem

end OptimalControl.BoundedState
