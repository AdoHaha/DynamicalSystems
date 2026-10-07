/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.BoundedStateFamily
public import DynamicalSystems.OptimalControl.ContinuousTime.EpsilonLimitTheorem
public import DynamicalSystems.OptimalControl.ContinuousTime.TubeFamilyData
public import DynamicalSystems.OptimalControl.ContinuousTime.TubeFamilyGradient
public import DynamicalSystems.OptimalControl.ContinuousTime.PenaltyCovectorConvergence
public import DynamicalSystems.OptimalControl.ContinuousTime.HamiltonianMinimumAe
public import DynamicalSystems.OptimalControl.ContinuousTime.EpsilonHamiltonianBridge

/-!
# The maximum principle for the bounded-state ODE problem (Theorem 11.6.3)

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Theorem 11.4.4,
Theorem 11.6.3.

For an optimal relaxed pair `(γ₀, ρ₀)` there are an absolutely continuous (bounded variation) `Φ`,
a nonincreasing `λ ≥ 0` with `λ(T) = 0`, an endpoint multiplier `β` and `λ⁰ ∈ [0,1]` with

* (i)   `|Φ(T)| + λ(0) + |β| + λ⁰ = 1`;
* (ii)  `Φ' = λ⁰ f⁰ₓ − (Φ − λ∇G)·fₓ + λ d(∇G)/dt` (integrated form) and its Stieltjes form;
* (iii) `Φ(0) = λ(0)∇G(0) + β·∂₁T`;   (iv) `Φ(T) = −β·∂₂T`;
* (v)   for a.e. `t` the conditional law `ν₀t` minimises the modified Hamiltonian
  `λ⁰ T⁻¹ f⁰ − (Φ − λ∇G)·f` over the control set.

`exists_boundedStateMaximumPrinciple_of_family` is the `ε → 0` passage for a
`BoundedStateFamily`; `exists_boundedStateMaximumPrinciple` combines it with the existence of the
family.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter ACEulerLagrange
open scoped Topology Interval

namespace OptimalControl.BoundedState

open Problem

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace V] [BorelSpace V]

namespace Problem

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] [BorelSpace V] in
/-- The Hamiltonian integral is jointly homogeneous in the weight and the cost coefficient. -/
theorem hamiltonianIntegral_smul (P : Problem E V W) (ρ : P.Relaxed) (x : P.Trajectory)
    (Θ : P.Time → E →L[ℝ] ℝ) (a : ℝ) :
    hamiltonianIntegral P ρ x (a • Θ) a = a * hamiltonianIntegral P ρ x Θ 1 := by
  simp only [hamiltonianIntegral, Pi.smul_apply, smul_apply, smul_eq_mul,
    one_mul]
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] [MeasurableSpace V]
  [BorelSpace V] in
/-- A line function a.e.-strongly measurable on `(0,T]` restricts to a function a.e.-strongly
measurable for the normalised horizon marginal. -/
theorem aestronglyMeasurable_horizonProbability_coe (P : Problem E V W) {Z : Type*}
    [NormedAddCommGroup Z] {f : ℝ → Z}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc (0 : ℝ) P.horizon))) :
    AEStronglyMeasurable (fun t : P.Time => f t)
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hf' : AEStronglyMeasurable f ((horizonVolume P.horizon).map ((↑) : P.Time → ℝ)) := by
    rw [← timeMeasure_eq_map_horizonVolume]; exact hf
  have h2 := (MeasurableEmbedding.subtype_coe measurableSet_Icc).aestronglyMeasurable_map_iff.1 hf'
  change AEStronglyMeasurable _ ((ENNReal.ofReal P.horizon)⁻¹ • horizonVolume P.horizon)
  exact h2.smul_measure _

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ W] in
/-- The penalty covector is a.e.-strongly measurable for the normalised horizon marginal. -/
theorem aestronglyMeasurable_penaltyCovector (P : Problem E V W) (K : ℝ)
    (γ : VelocityTrajectory P) (ρ : P.Relaxed) :
    AEStronglyMeasurable (penaltyCovector P K γ ρ)
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have h1 := (integrable_velocity_horizonProbability P γ).aestronglyMeasurable
  have h2 : StronglyMeasurable (fun t : P.Time => realizedVelocity P (toBoundedPath γ) ρ t) :=
    RelaxedControl.stronglyMeasurable_average ρ
      (continuous_dynamics_trajectory P (toBoundedPath γ)).stronglyMeasurable
  exact ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
    (h1.sub h2.aestronglyMeasurable)).const_smul (2 * K * P.horizon)

end Problem

/-- **The `ε → 0` passage for a family of tube minimisers: Theorem 11.6.3 (i)–(v).**
Conclusion (i) holds with `Λ(0⁺) := rightMultiplier P.horizon Λ 0` (`= Λ 0` under
Assumption 11.4.1, the collar hypothesis `hcollar`), and `Λ` is constant near `0` and vanishes
near `T`. Complementarity: `Λ` is constant on every interval where `G(·, γ₀) < 0`
(`supp dΛ ⊂ {G = 0}`). Non-triviality: under the rank hypothesis `hrank` (`∂₂T` surjective, a
normality condition) the multipliers `(Ψ, Λ, λ⁰)` do not all vanish. -/
theorem exists_boundedStateMaximumPrinciple_of_family (P : Problem E V W) (D : P.SmoothData)
    (hD : P.DerivativeContinuity D)
    {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)}
    (hG : Continuous fun p : ℝ × E => G p.1 p.2)
    (hGreg : StateConstraintRegularity G Gx) (hGx : StateGradientRegularity Gx Gxd)
    (hGdc : ∀ t, Continuous fun q : E × E => Gxd t q.1 (1, q.2))
    (hT : ContDiff ℝ 1 (fun q : E × E => P.endpointConstraint q.1 q.2))
    {γ₀ : VelocityTrajectory P} {ρ₀ : P.Relaxed}
    (hcollar : ∃ δ : ℝ, 0 < δ ∧ δ < P.horizon ∧ ∀ t ∈ Icc (0 : ℝ) P.horizon,
      (t < δ ∨ P.horizon - δ < t) → G t (γ₀.value t) < 0)
    (hrank : Function.Surjective ((fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
      (γ₀.value 0, γ₀.value P.horizon)).comp (ContinuousLinearMap.inr ℝ E E)))
    (F : BoundedStateFamily P D G Gx Gxd γ₀ ρ₀) :
    ∃ (Ψ : ℝ → E →L[ℝ] ℝ) (Λ : ℝ → ℝ) (β : (W →L[ℝ] ℝ) × (E →L[ℝ] ℝ)) (lam0 : ℝ)
      (_hΛ : AntitoneOn Λ (Icc (0 : ℝ) P.horizon)),
      eVariationOn Ψ (Icc (0 : ℝ) P.horizon) ≠ ⊤ ∧
      AbsolutelyContinuousOnInterval Ψ 0 P.horizon ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, 0 ≤ Λ t) ∧ Λ P.horizon = 0 ∧ 0 ≤ lam0 ∧ lam0 ≤ 1 ∧
      ‖Ψ P.horizon‖ + Λ 0 + ‖β‖ + lam0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, Ψ t = Ψ 0 + ∫ r in (0 : ℝ)..t,
        (lam0 • P.averagedRunningCovector D ρ₀ r (γ₀.value r)
          - (ContinuousLinearMap.compL ℝ E E ℝ).flip
              (P.averagedDynamicsDerivative D ρ₀ r (γ₀.value r))
            (Ψ r - Λ r • Gx r (γ₀.value r))
          + Λ r • Gxd r (γ₀.value r) (1, γ₀.velocity r))) ∧
      Ψ 0 = Λ 0 • Gx 0 (γ₀.value 0) + tubeDl (fderiv ℝ
        (fun q : E × E => P.endpointConstraint q.1 q.2) (γ₀.value 0, γ₀.value P.horizon)) β ∧
      Ψ P.horizon = -(tubeDr (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        (γ₀.value 0, γ₀.value P.horizon)) β) ∧
      (∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v : P.Control,
        ∫ u : P.Control, (lam0 * P.horizon⁻¹ * P.runningCost t (γ₀.value t) (u : V)
            - (Ψ t - Λ t • Gx t (γ₀.value t)) (P.dynamics t (γ₀.value t) (u : V)))
          ∂ρ₀.kernel t
        ≤ lam0 * P.horizon⁻¹ * P.runningCost t (γ₀.value t) (v : V)
            - (Ψ t - Λ t • Gx t (γ₀.value t)) (P.dynamics t (γ₀.value t) (v : V))) ∧
      (∃ δ' : ℝ, 0 < δ' ∧ (∀ t ∈ Icc (0 : ℝ) δ', Λ t = Λ 0) ∧
        ∀ t ∈ Icc (P.horizon - δ') P.horizon, Λ t = 0) ∧
      rightMultiplier P.horizon Λ 0 = Λ 0 ∧
      (∀ α β : ℝ, α ∈ Icc (0 : ℝ) P.horizon → β ∈ Icc (0 : ℝ) P.horizon →
        (∀ r ∈ Icc α β, G r (γ₀.value r) < 0) → ∀ t ∈ Icc α β, Λ t = Λ α) ∧
      ¬ ((∀ t ∈ Icc (0 : ℝ) P.horizon, Ψ t = 0) ∧ (∀ t ∈ Icc (0 : ℝ) P.horizon, Λ t = 0) ∧
        lam0 = 0) := by
  classical
  have hTp := P.horizon_pos
  have hT0 := hTp.le
  have hIcc0 : (0 : ℝ) ∈ Icc (0 : ℝ) P.horizon := ⟨le_rfl, hT0⟩
  have hIccT : P.horizon ∈ Icc (0 : ℝ) P.horizon := ⟨hT0, le_rfl⟩
  have hsq0 : 0 ≤ Real.sqrt P.horizon := Real.sqrt_nonneg _
  /- uniform bounds along the family -/
  obtain ⟨R₀, hR₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P.horizon)).exists_bound_of_continuousOn
    γ₀.continuousOn_value
  set R : ℝ := R₀ + (1 + Real.sqrt P.horizon) with hR
  have hdist : ∀ k, ∀ t ∈ Icc (0 : ℝ) P.horizon,
      dist ((F.γ k).value t) (γ₀.value t) ≤ F.ε k * (1 + Real.sqrt P.horizon) := fun k =>
    P.dist_value_le_of_tube (F.ε_pos k).le γ₀ (F.γ k) (F.velocity_lt k).le (F.initial_lt k).le
  have hγR : ∀ k, ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖(F.γ k).value t‖ ≤ R := by
    intro k t ht
    have h1 := hdist k t ht
    have h2 := hR₀ t ht
    have h3 : F.ε k * (1 + Real.sqrt P.horizon) ≤ 1 + Real.sqrt P.horizon := by
      have := F.ε_le_one k
      nlinarith
    have h4 := norm_le_norm_add_norm_sub' ((F.γ k).value t) (γ₀.value t)
    rw [dist_eq_norm] at h1
    linarith
  have hγ₀R : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖γ₀.value t‖ ≤ R := fun t ht => by
    have := hR₀ t ht
    linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := P.exists_bound_averagedDerivatives D hD R
  obtain ⟨C₂, hC₂0, hC₂⟩ := hGreg.bounded R
  obtain ⟨C₃, hC₃0, hC₃⟩ := Problem.exists_bound_integral_norm_gradientDerivative hGx γ₀
  set C : ℝ := C₁ + C₂ + C₃ with hC
  /- convergences along the family -/
  have hεlim : Tendsto (fun k => F.ε k * (1 + Real.sqrt P.horizon)) atTop (𝓝 0) := by
    simpa using F.ε_tendsto.mul_const (1 + Real.sqrt P.horizon)
  have hBCF : Tendsto (fun k => toBoundedPath (F.γ k)) atTop (𝓝 (toBoundedPath γ₀)) := by
    refine tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hεlim)
    refine (BoundedContinuousFunction.dist_le
      (mul_nonneg (F.ε_pos k).le (by positivity))).2 fun t => ?_
    simpa only [toBoundedPath_apply] using hdist k t t.2
  have hρlim : Tendsto (fun k => relaxedControlDistance P (F.ρe k) ρ₀) atTop (𝓝 0) :=
    squeeze_zero (fun k => relaxedControlDistance_nonneg P _ _) (fun k => (F.control_lt k).le)
      F.ε_tendsto
  have hvlim : Tendsto (fun k => ∫ r in (0 : ℝ)..P.horizon,
      ‖(F.γ k).velocity r - γ₀.velocity r‖) atTop (𝓝 0) :=
    squeeze_zero (fun k => intervalIntegral.integral_nonneg hT0 fun _ _ => norm_nonneg _)
      (fun k => P.integral_norm_velocity_sub_le (F.ε_pos k).le γ₀ (F.γ k) (F.velocity_lt k).le)
      (by simpa using F.ε_tendsto.const_mul (Real.sqrt P.horizon))
  have hunif : ∀ δ > 0, ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) P.horizon,
      dist ((F.γ k).value t) (γ₀.value t) < δ := by
    intro δ hδ
    filter_upwards [(tendsto_order.1 hεlim).2 δ hδ] with k hk t ht using
      (hdist k t ht).trans_lt hk
  have hptlim : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      Tendsto (fun k => (F.γ k).value t) atTop (𝓝 (γ₀.value t)) := fun t ht =>
    Metric.tendsto_nhds.2 fun δ hδ => (hunif δ hδ).mono fun k hk => hk t ht
  have hglim : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      Tendsto (fun k => Gx t ((F.γ k).value t)) atTop (𝓝 (Gx t (γ₀.value t))) := by
    intro t ht
    have hc : ContinuousAt (fun q : ℝ × E => Gx q.1 q.2) (t, γ₀.value t) :=
      (hGx.hasFDerivAt t (γ₀.value t)).continuousAt
    exact hc.tendsto.comp (tendsto_const_nhds.prodMk_nhds (hptlim t ht))
  have hDT : Tendsto (fun k => fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
      ((F.γ k).value 0, (F.γ k).value P.horizon)) atTop
      (𝓝 (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        (γ₀.value 0, γ₀.value P.horizon))) :=
    ((hT.continuous_fderiv one_ne_zero).tendsto _).comp
      ((hptlim 0 hIcc0).prodMk_nhds (hptlim _ hIccT))
  have hilim : Tendsto (fun k => ‖(F.γ k).value 0 - γ₀.initial‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun k => by rw [VelocityTrajectory.value_zero, ← dist_eq_norm]; exact (F.initial_lt k).le)
      F.ε_tendsto
  /- measurability of the data along paths -/
  have hbcx : ∀ (ρ : P.Relaxed) (R' : ℝ), ∃ C' : ℝ, ∀ t y, ‖y‖ ≤ R' →
      ‖P.averagedRunningCovector D ρ t y‖ ≤ C' := fun ρ R' => by
    obtain ⟨C', -, hC'⟩ := P.exists_bound_averagedDerivatives D hD R'
    exact ⟨C', fun t y hy => (hC' ρ t y hy).1⟩
  have hbFx : ∀ (ρ : P.Relaxed) (R' : ℝ), ∃ C' : ℝ, ∀ t y, ‖y‖ ≤ R' →
      ‖P.averagedDynamicsDerivative D ρ t y‖ ≤ C' := fun ρ R' => by
    obtain ⟨C', -, hC'⟩ := P.exists_bound_averagedDerivatives D hD R'
    exact ⟨C', fun t y hy => (hC' ρ t y hy).2⟩
  have hbGx : ∀ R' : ℝ, ∃ C' : ℝ, ∀ t y, ‖y‖ ≤ R' → ‖Gx t y‖ ≤ C' := fun R' => by
    obtain ⟨C', -, hC'⟩ := hGreg.bounded R'
    exact ⟨C', fun t y hy => (hC' t y hy).2⟩
  have hcx₀ : IntervalIntegrable (fun r => P.averagedRunningCovector D ρ₀ r (γ₀.value r))
      volume 0 P.horizon :=
    intervalIntegrable_comp_value γ₀ (P.measurable_averagedRunningCovector D hD ρ₀) (hbcx ρ₀)
  have hFx₀m : AEStronglyMeasurable (fun r => P.averagedDynamicsDerivative D ρ₀ r (γ₀.value r))
      (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).1 (intervalIntegrable_comp_value γ₀
      (P.measurable_averagedDynamicsDerivative D hD ρ₀) (hbFx ρ₀))).aestronglyMeasurable
  have hg₀m : AEStronglyMeasurable (fun r => Gx r (γ₀.value r))
      (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).1
      (intervalIntegrable_comp_value γ₀ hGreg.measurable_Gx hbGx)).aestronglyMeasurable
  have hFxm : ∀ k, AEStronglyMeasurable
      (fun r => P.averagedDynamicsDerivative D (F.ρe k) r ((F.γ k).value r))
      (volume.restrict (Ioc (0 : ℝ) P.horizon)) := fun k =>
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).1
      (intervalIntegrable_comp_value (F.γ k)
        (P.measurable_averagedDynamicsDerivative D hD (F.ρe k))
        (hbFx (F.ρe k)))).aestronglyMeasurable
  have hgC : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖Gx t (γ₀.value t)‖ ≤ C := fun t ht =>
    (hC₂ t _ (hγ₀R t ht)).2.trans (by linarith)
  /- Part A: conclusions (i)–(iv) -/
  obtain ⟨ψ, Ψ, Λ, β, lam0, hΛ, hψ, hBV, hAC, hnn, hΛT, h0, h1, hnorm, hint, hinit, hterm, hΨm,
      hΛm, -, M, hM, hlam0, hΦc, hΛc, B, hB⟩ :=
    Problem.exists_theorem_11_6_3_conclusions γ₀ F.system (C := C)
      (fun k t ht => (hC₁ (F.ρe k) t _ (hγR k t ht)).1.trans (by linarith))
      (fun k t ht => (hC₁ (F.ρe k) t _ (hγR k t ht)).2.trans (by linarith))
      (fun k t ht => (hC₂ t _ (hγR k t ht)).2.trans (by linarith))
      (fun k => (hC₃ (F.γ k) (F.ε k) (F.ε_pos k).le (F.ε_le_one k) (F.velocity_lt k).le
        (F.initial_lt k).le).trans (by linarith))
      (cx₀ := fun r => P.averagedRunningCovector D ρ₀ r (γ₀.value r))
      (Fx₀ := fun r => P.averagedDynamicsDerivative D ρ₀ r (γ₀.value r))
      (g₀ := fun r => Gx r (γ₀.value r))
      (gd₀ := fun r => Gxd r (γ₀.value r) (1, γ₀.velocity r))
      hcx₀ (γ₀.gradientAlongPath_eq_primitive hGx).1 hFxm hFx₀m hg₀m
      (fun t ht => (hC₁ ρ₀ t _ (hγ₀R t ht)).2.trans (by linarith)) hgC
      (P.tendsto_integral_norm_averagedRunningCovector_sub D hD hBCF hρlim)
      (P.tendsto_integral_norm_averagedDynamicsDerivative_sub D hD hBCF hρlim)
      (tendsto_integral_norm_gradientDerivative_sub hGx hGdc hunif hvlim) hvlim hglim hilim
      (γ₀.gradientAlongPath_eq_primitive hGx).2 hDT
  /- Assumption 11.4.1: collar behaviour of the limit multiplier -/
  have hψt := hψ.tendsto_atTop
  have hcol : (∃ δ' : ℝ, 0 < δ' ∧ (∀ t ∈ Icc (0 : ℝ) δ', Λ t = Λ 0) ∧
      ∀ t ∈ Icc (P.horizon - δ') P.horizon, Λ t = 0) ∧ rightMultiplier P.horizon Λ 0 = Λ 0 := by
    obtain ⟨δ, hδ, hδT, hδG⟩ := hcollar
    have hA : IsCompact (Icc (0 : ℝ) (δ / 2) ∪ Icc (P.horizon - δ / 2) P.horizon) :=
      isCompact_Icc.union isCompact_Icc
    have hAsub : Icc (0 : ℝ) (δ / 2) ∪ Icc (P.horizon - δ / 2) P.horizon
        ⊆ Icc (0 : ℝ) P.horizon := by
      rintro t (ht | ht)
      · exact ⟨ht.1, by linarith [ht.2]⟩
      · exact ⟨by linarith [ht.1], ht.2⟩
    obtain ⟨η, hη, hηG⟩ := exists_slack_radius hG hA (γ₀.continuousOn_value.mono hAsub)
      (fun r hr => hδG r (hAsub hr) (by
        rcases hr with hr | hr
        · exact Or.inl (by linarith [hr.2])
        · exact Or.inr (by linarith [hr.1])))
    have hev : ∀ᶠ k in atTop, (∀ t ∈ Icc (0 : ℝ) (δ / 2 / 2), F.lam (ψ k) t = F.lam (ψ k) 0) ∧
        ∀ t ∈ Icc (P.horizon - δ / 2 / 2) P.horizon, F.lam (ψ k) t = 0 := by
      filter_upwards [hψt.eventually (hunif η hη)] with k hk
      exact F.collar (δ / 2) (by linarith) (by linarith) (ψ k) fun t ht hts =>
        hηG t (by
          rcases hts with h | h
          · exact Or.inl ⟨ht.1, h.le⟩
          · exact Or.inr ⟨by linarith, ht.2⟩) _ (hk t ht)
    have hδ4 : 0 < δ / 2 / 2 := by positivity
    have hconst : ∀ t ∈ Icc (0 : ℝ) (δ / 2 / 2), Λ t = Λ 0 := by
      intro t ht
      refine tendsto_nhds_unique (hΛc t ⟨ht.1, by linarith [ht.2]⟩) ((hΛc 0 hIcc0).congr' ?_)
      filter_upwards [hev] with k hk
      rw [hk.1 t ht]
    refine ⟨⟨δ / 2 / 2, hδ4, hconst, fun t ht => ?_⟩, ?_⟩
    · refine tendsto_nhds_unique (hΛc t ⟨by linarith [ht.1], ht.2⟩)
        ((tendsto_const_nhds (x := (0 : ℝ))).congr' ?_)
      filter_upwards [hev] with k hk
      rw [hk.2 t ht, mul_zero]
    · exact rightMultiplier_eq_of_const (fun t ht => ⟨ht.1, by linarith [ht.2]⟩) hconst
        (s := 0) ⟨le_rfl, hδ4⟩
  /- complementarity: `Λ` is constant where the limit path is strictly slack -/
  have hcomp : ∀ α β : ℝ, α ∈ Icc (0 : ℝ) P.horizon → β ∈ Icc (0 : ℝ) P.horizon →
      (∀ r ∈ Icc α β, G r (γ₀.value r) < 0) → ∀ t ∈ Icc α β, Λ t = Λ α := by
    intro α β hα hβ hslack t ht
    have hsub : Icc α β ⊆ Icc (0 : ℝ) P.horizon := fun r hr => ⟨hα.1.trans hr.1, hr.2.trans hβ.2⟩
    obtain ⟨η, hη, hηG⟩ := exists_slack_radius hG (isCompact_Icc (a := α) (b := β))
      (γ₀.continuousOn_value.mono hsub) hslack
    refine tendsto_nhds_unique (hΛc t (hsub ht)) ((hΛc α hα).congr' ?_)
    filter_upwards [hψt.eventually (hunif η hη)] with k hk
    rw [F.complementary (ψ k) α β hα hβ (fun r hr => hηG r hr _ (hk r (hsub hr))) t ht]
  /- non-triviality: the degenerate witness is excluded by surjectivity of `∂₂T` -/
  have hnt : ¬ ((∀ t ∈ Icc (0 : ℝ) P.horizon, Ψ t = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, Λ t = 0) ∧ lam0 = 0) := by
    rintro ⟨hΨ0, hΛ0, hl0⟩
    have hr : tubeDr (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        (γ₀.value 0, γ₀.value P.horizon)) β = 0 := by
      have := hterm
      rw [hΨ0 _ hIccT] at this
      exact (neg_eq_zero.1 this.symm)
    have hb1 : β.1 = 0 := by
      refine ContinuousLinearMap.ext fun w => ?_
      obtain ⟨e, he⟩ := hrank w
      have key : β.1 ((fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
          (γ₀.value 0, γ₀.value P.horizon)) (ContinuousLinearMap.inr ℝ E E e)) = 0 :=
        congrArg (fun f => f e) hr
      have he' : (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
          (γ₀.value 0, γ₀.value P.horizon)) (ContinuousLinearMap.inr ℝ E E e) = w := he
      rw [he'] at key
      simpa using key
    have hi := hinit
    rw [hΨ0 0 hIcc0, hΛ0 0 hIcc0, zero_smul, zero_add] at hi
    have hb2 : β.2 = 0 := by
      have := congrArg (fun f => f) hi.symm
      simpa [tubeDl, hb1] using this
    have hβ : β = 0 := Prod.ext hb1 hb2
    rw [hΨ0 _ hIccT, hΛ0 0 hIcc0, hβ, hl0] at hnorm
    simp at hnorm
  refine ⟨Ψ, Λ, β, lam0, hΛ, hBV, hAC, hnn, hΛT, h0, h1, hnorm, hint, hinit, hterm, ?_, hcol.1,
    hcol.2, hcomp, hnt⟩
  /- Part B: conclusion (v) -/
  have hMpos : ∀ k, 0 < M k := fun k => lt_of_lt_of_le one_pos (hM k)
  have hlamsys : ∀ k, ∀ t ∈ Icc (0 : ℝ) P.horizon, 0 ≤ F.lam k t ∧ F.lam k t ≤ F.lam k 0 :=
    fun k t ht => ⟨(F.system k).nonneg t ht, (F.system k).antitone hIcc0 ht ht.1⟩
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, ∀ k, (1 / M k) * F.lam (ψ k) 0 ≤ L₀ := by
    obtain ⟨L₀, hL₀⟩ := (hΛc 0 hIcc0).bddAbove_range
    exact ⟨L₀, fun k => hL₀ ⟨k, rfl⟩⟩
  set L : ℝ := max L₀ 1 with hLdef
  have hL : 0 < L := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hΛg : ∀ s : ℝ, (L⁻¹ * Λ s) • (L • Gx s (γ₀.value s)) = Λ s • Gx s (γ₀.value s) := by
    intro s
    rw [smul_smul]
    congr 1
    field_simp
  have hpen := Problem.tendsto_integral_norm_penaltyCovector_sub P (K := fun k => F.K (ψ k))
    (γ₀ := γ₀) (γ := fun k => F.γ (ψ k)) (ρe := fun k => F.ρe (ψ k))
    (Gx := fun t y => L • Gx t y) (Φ := fun k => F.Φ (ψ k))
    (lam := fun k t => L⁻¹ * F.lam (ψ k) t) hM (Ψ := Ψ) (g₀ := fun t => L • Gx t (γ₀.value t))
    (Λ := fun t => L⁻¹ * Λ t) (B := B) (C := L * C)
    (fun k => by
      filter_upwards [F.momentum (ψ k)] with t ht
      have e : (L⁻¹ * F.lam (ψ k) t) • (L • Gx t ((F.γ (ψ k)).value t))
          = F.lam (ψ k) t • Gx t ((F.γ (ψ k)).value t) := by
        rw [smul_smul]
        congr 1
        field_simp
      rw [e]
      exact ht)
    hΦc
    (fun t ht => ((hΛc t ht).const_mul L⁻¹).congr fun k => by ring)
    (fun t ht => ((hglim t ht).comp hψt).const_smul L)
    hB
    (fun k t ht => by
      rw [norm_smul, Real.norm_of_nonneg hL.le]
      exact mul_le_mul_of_nonneg_left ((hC₂ t _ (hγR _ t ht)).2.trans (by linarith)) hL.le)
    (fun k t ht => by
      have hm : 0 ≤ 1 / M k := (one_div_pos.2 (hMpos k)).le
      refine ⟨mul_nonneg (inv_nonneg.2 hL.le) (hlamsys _ t ht).1, ?_⟩
      have h : (1 / M k) * F.lam (ψ k) t ≤ L :=
        (mul_le_mul_of_nonneg_left (hlamsys _ t ht).2 hm).trans
          ((hL₀ k).trans (le_max_left _ _))
      calc (1 / M k) * (L⁻¹ * F.lam (ψ k) t) = L⁻¹ * ((1 / M k) * F.lam (ψ k) t) := by ring
        _ ≤ L⁻¹ * L := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hL.le)
        _ = 1 := inv_mul_cancel₀ hL.ne')
    hΨm (hΛm.const_mul L⁻¹) (hg₀m.const_smul L) (hvlim.comp hψt)
  simp only [hΛg] at hpen
  -- the limit weight `T(Ψ − Λ∇G₀)` and a measurable bounded modification
  obtain ⟨X, hX⟩ : ∃ X : P.Time → E →L[ℝ] ℝ,
      ∀ t, X t = P.horizon • (Ψ t - Λ t • Gx t (γ₀.value t)) := ⟨_, fun _ => rfl⟩
  have hΨb : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖Ψ t‖ ≤ B := fun t ht =>
    le_of_tendsto' (hΦc t ht).norm fun k => hB k t ht
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hΨb 0 hIcc0)
  have hC0 : 0 ≤ C := by positivity
  have hΛ01 : ∀ t ∈ Icc (0 : ℝ) P.horizon, 0 ≤ Λ t ∧ Λ t ≤ 1 := by
    intro t ht
    refine ⟨hnn t ht, (hΛ hIcc0 ht ht.1).trans ?_⟩
    have := norm_nonneg (Ψ P.horizon)
    have := norm_nonneg β
    linarith
  set B' : ℝ := P.horizon * (B + C) with hB'
  have hXb : ∀ t, ‖X t‖ ≤ B' := by
    intro t
    have ht := t.2
    rw [hX, norm_smul, Real.norm_of_nonneg hT0]
    refine mul_le_mul_of_nonneg_left ?_ hT0
    calc ‖Ψ t - Λ t • Gx t (γ₀.value t)‖ ≤ ‖Ψ t‖ + ‖Λ t • Gx t (γ₀.value t)‖ := norm_sub_le _ _
      _ ≤ B + C := by
        refine add_le_add (hΨb t ht) ?_
        rw [norm_smul, Real.norm_of_nonneg (hΛ01 t ht).1]
        calc Λ t * ‖Gx t (γ₀.value t)‖ ≤ 1 * C :=
              mul_le_mul (hΛ01 t ht).2 (hgC t ht) (norm_nonneg _) zero_le_one
          _ = C := one_mul C
  have hXm : AEStronglyMeasurable X (horizonProbability P.horizon P.horizon_pos).toMeasure := by
    rw [show X = fun t : P.Time => P.horizon • (Ψ t - Λ t • Gx t (γ₀.value t)) from funext hX]
    exact Problem.aestronglyMeasurable_horizonProbability_coe P
      ((hΨm.sub (hΛm.smul hg₀m)).const_smul P.horizon)
  set S : Set P.Time := {t | ‖hXm.mk X t‖ ≤ B'} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_le hXm.stronglyMeasurable_mk.norm.measurable measurable_const
  set Θ' : P.Time → E →L[ℝ] ℝ := S.indicator (hXm.mk X) with hΘ'def
  have hΘ'sm : StronglyMeasurable Θ' := hXm.stronglyMeasurable_mk.indicator hS
  have hB'0 : 0 ≤ B' := by positivity
  have hΘ'b : ∀ t, ‖Θ' t‖ ≤ B' := fun t => by
    by_cases ht : t ∈ S
    · rw [hΘ'def, indicator_of_mem ht]; exact ht
    · rw [hΘ'def, indicator_of_notMem ht, norm_zero]; exact hB'0
  have hΘ'ae : ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, Θ' t = X t := by
    filter_upwards [hXm.ae_eq_mk] with t ht
    have htS : t ∈ S := by
      change ‖hXm.mk X t‖ ≤ B'
      rw [← ht]; exact hXb t
    rw [hΘ'def, indicator_of_mem htS, ht]
  -- the `ε`-level inequalities, normalised
  have hHk : ∀ (k : ℕ) (σ : P.Relaxed),
      hamiltonianIntegral P (F.ρe (ψ k)) (toBoundedPath (F.γ (ψ k)))
          ((1 / M k) • penaltyCovector P (F.K (ψ k)) (F.γ (ψ k)) (F.ρe (ψ k))) (1 / M k)
        ≤ hamiltonianIntegral P σ (toBoundedPath (F.γ (ψ k)))
          ((1 / M k) • penaltyCovector P (F.K (ψ k)) (F.γ (ψ k)) (F.ρe (ψ k))) (1 / M k)
          + (1 / M k) * F.ε (ψ k) := by
    intro k σ
    rw [Problem.hamiltonianIntegral_smul, Problem.hamiltonianIntegral_smul, ← mul_add]
    exact mul_le_mul_of_nonneg_left
      (hamiltonianIntegral_le_of_epsilonHamiltonian P (F.K (ψ k)) (F.ε (ψ k)) (F.K_nonneg _)
        (F.ε_pos _).le γ₀ (F.γ (ψ k)) ρ₀ (F.ρe (ψ k)) (F.mem_tube _) (F.control_lt _)
        (F.minimal _) σ) (one_div_pos.2 (hMpos k)).le
  have heps : Tendsto (fun k => (1 / M k) * F.ε (ψ k)) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => mul_nonneg (one_div_pos.2 (hMpos k)).le (F.ε_pos _).le)
      (fun k => ?_) (F.ε_tendsto.comp hψt)
    have h1 : 1 / M k ≤ 1 := (div_le_one (hMpos k)).2 (hM k)
    have := (F.ε_pos (ψ k)).le
    change 1 / M k * F.ε (ψ k) ≤ F.ε (ψ k)
    nlinarith
  have hmin := fun σ => hamiltonianIntegral_le_of_limit P (hBCF.comp hψt) (hρlim.comp hψt) hlam0
    (Θ := fun k => (1 / M k) • penaltyCovector P (F.K (ψ k)) (F.γ (ψ k)) (F.ρe (ψ k)))
    hΘ'b hΘ'sm.aestronglyMeasurable
    (fun k => (Problem.aestronglyMeasurable_penaltyCovector P _ _ _).const_smul _)
    (fun k => (hpen.1 k).congr (by filter_upwards [hΘ'ae] with t ht; rw [ht, hX]; rfl))
    (hpen.2.congr fun k => integral_congr_ae
      (by filter_upwards [hΘ'ae] with t ht; rw [ht, hX]; rfl))
    heps hHk σ
  have hae := ae_hamiltonian_le_of_hamiltonianIntegral_le P (toBoundedPath γ₀) ρ₀
    hΘ'sm.measurable hΘ'b lam0 hmin
  have e : ∀ a b : ℝ, lam0 * P.horizon⁻¹ * a - b
      = P.horizon⁻¹ * (lam0 * a - P.horizon * b) := by
    intro a b
    rw [mul_sub, ← mul_assoc P.horizon⁻¹ P.horizon b, inv_mul_cancel₀ hTp.ne', one_mul]
    ring
  filter_upwards [hae, hΘ'ae] with t ht hΘt v
  have key := ht v
  simp only [hΘt, hX, toBoundedPath_apply, smul_apply, smul_eq_mul] at key
  simp only [e, integral_const_mul]
  exact mul_le_mul_of_nonneg_left key (inv_nonneg.2 hT0)

/-- **Theorem 11.6.3 for the bounded-state ODE problem.** Conclusion (i) holds with
`Λ(0⁺) := rightMultiplier P.horizon Λ 0` (`= Λ 0` under Assumption 11.4.1, `hcollar`).
Complementarity: `Λ` is constant on every interval where `G(·, γ₀) < 0` (`supp dΛ ⊂ {G = 0}`).
Non-triviality: under `hrank` (`∂₂T` surjective, a normality condition) `(Ψ, Λ, λ⁰) ≠ 0`. -/
theorem exists_boundedStateMaximumPrinciple (P : Problem E V W) (D : P.SmoothData)
    (hD : P.DerivativeContinuity D)
    {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)} {ω ω' : ℝ → ℝ}
    (hG : Continuous fun p : ℝ × E => G p.1 p.2)
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hGreg : StateConstraintRegularity G Gx) (hGx : StateGradientRegularity Gx Gxd)
    (hGdc : ∀ t, Continuous fun q : E × E => Gxd t q.1 (1, q.2))
    (hω₁ : IsStatePenaltyProfile ω) (hω₂ : StatePenaltyProfile ω ω')
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (hT : ContDiff ℝ 1 (fun q : E × E => P.endpointConstraint q.1 q.2))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) (hγ₀m : Measurable γ₀.velocity)
    (hcollar : ∃ δ : ℝ, 0 < δ ∧ δ < P.horizon ∧ ∀ t ∈ Icc (0 : ℝ) P.horizon,
      (t < δ ∨ P.horizon - δ < t) → G t (γ₀.value t) < 0)
    (hND : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
      ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed), InVelocityControlTube P γ₀ ρ₀ ε γ ρ →
        ∀ t ∈ Icc (0 : ℝ) P.horizon, Gx t (γ.value t) ≠ 0)
    (hrank : Function.Surjective ((fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
      (γ₀.value 0, γ₀.value P.horizon)).comp (ContinuousLinearMap.inr ℝ E E))) :
    ∃ (Ψ : ℝ → E →L[ℝ] ℝ) (Λ : ℝ → ℝ) (β : (W →L[ℝ] ℝ) × (E →L[ℝ] ℝ)) (lam0 : ℝ)
      (_hΛ : AntitoneOn Λ (Icc (0 : ℝ) P.horizon)),
      eVariationOn Ψ (Icc (0 : ℝ) P.horizon) ≠ ⊤ ∧
      AbsolutelyContinuousOnInterval Ψ 0 P.horizon ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, 0 ≤ Λ t) ∧ Λ P.horizon = 0 ∧ 0 ≤ lam0 ∧ lam0 ≤ 1 ∧
      ‖Ψ P.horizon‖ + Λ 0 + ‖β‖ + lam0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, Ψ t = Ψ 0 + ∫ r in (0 : ℝ)..t,
        (lam0 • P.averagedRunningCovector D ρ₀ r (γ₀.value r)
          - (ContinuousLinearMap.compL ℝ E E ℝ).flip
              (P.averagedDynamicsDerivative D ρ₀ r (γ₀.value r))
            (Ψ r - Λ r • Gx r (γ₀.value r))
          + Λ r • Gxd r (γ₀.value r) (1, γ₀.velocity r))) ∧
      Ψ 0 = Λ 0 • Gx 0 (γ₀.value 0) + tubeDl (fderiv ℝ
        (fun q : E × E => P.endpointConstraint q.1 q.2) (γ₀.value 0, γ₀.value P.horizon)) β ∧
      Ψ P.horizon = -(tubeDr (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        (γ₀.value 0, γ₀.value P.horizon)) β) ∧
      (∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v : P.Control,
        ∫ u : P.Control, (lam0 * P.horizon⁻¹ * P.runningCost t (γ₀.value t) (u : V)
            - (Ψ t - Λ t • Gx t (γ₀.value t)) (P.dynamics t (γ₀.value t) (u : V)))
          ∂ρ₀.kernel t
        ≤ lam0 * P.horizon⁻¹ * P.runningCost t (γ₀.value t) (v : V)
            - (Ψ t - Λ t • Gx t (γ₀.value t)) (P.dynamics t (γ₀.value t) (v : V))) ∧
      (∃ δ' : ℝ, 0 < δ' ∧ (∀ t ∈ Icc (0 : ℝ) δ', Λ t = Λ 0) ∧
        ∀ t ∈ Icc (P.horizon - δ') P.horizon, Λ t = 0) ∧
      rightMultiplier P.horizon Λ 0 = Λ 0 ∧
      (∀ α β : ℝ, α ∈ Icc (0 : ℝ) P.horizon → β ∈ Icc (0 : ℝ) P.horizon →
        (∀ r ∈ Icc α β, G r (γ₀.value r) < 0) → ∀ t ∈ Icc α β, Λ t = Λ α) ∧
      ¬ ((∀ t ∈ Icc (0 : ℝ) P.horizon, Ψ t = 0) ∧ (∀ t ∈ Icc (0 : ℝ) P.horizon, Λ t = 0) ∧
        lam0 = 0) := by
  obtain ⟨F⟩ := exists_boundedStateFamily P D hD hG hGP hGreg hGx hGdc hω₁ hω₂ hEnd hT γ₀ ρ₀
    hopt hγ₀m hND
  exact exists_boundedStateMaximumPrinciple_of_family P D hD hG hGreg hGx hGdc hT hcollar hrank F

end OptimalControl.BoundedState
