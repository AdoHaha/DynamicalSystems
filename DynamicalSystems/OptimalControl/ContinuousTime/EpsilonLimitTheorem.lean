/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.EpsilonLevelBridge
public import DynamicalSystems.OptimalControl.ContinuousTime.EpsilonLimitPassage
public import DynamicalSystems.OptimalControl.ContinuousTime.StateMultiplierStieltjes

/-!
# The `ε → 0` passage to Theorem 11.4.4 / Theorem 11.6.3

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.4, Theorem 11.4.4,
Theorem 11.6.3.

`EpsilonLevelBridge.lean` writes the `j → ∞` limit at each level `ε` as an `ε`-level costate system
(the linear equation (11.3.25) with (11.3.33), (11.3.34)); `EpsilonLimitPassage.lean` runs the §11.4
limiting operations (normalisation (11.4.3), Gronwall bound (11.4.1)–(11.4.2), Helly selection
(11.4.4)–(11.4.5), passage to the limit (11.4.14)–(11.4.16)) on an abstract family of such systems.
This file instantiates the passage with the concrete systems of the bounded-state problem:

* `exists_theorem_11_6_3_conclusions`: for `ε_k → 0` with the data bounds and convergences
  `f⁰ₓ(φ_k) → f⁰ₓ(φ₀)`, `fₓ(φ_k) → fₓ(φ₀)`, `∇G(φ_k) → ∇G(φ₀)`, `d(∇G)/dt(φ_k) → d(∇G)/dt(φ₀)`,
  `φ_k' → φ₀'` in `L¹`, `φ_k(0) → φ₀(0)`, `∂T(φ_k) → ∂T(φ₀)`, there are a bounded-variation `Φ`,
  a nonincreasing `λ ≥ 0` with `λ(t₁) = 0`, an endpoint multiplier `β` and `λ⁰ ∈ [0,1]` with
  (i) `|Φ(t₁)| + λ(0) + |β| + λ⁰ = 1`, (ii) the adjoint law
  `Φ' = λ⁰f⁰ₓ − (Φ − λ∇G)·fₓ + λ d(∇G)/dt`, (iii) `Φ(0) = λ(0)∇G(0) + β∂₁T`,
  (iv) `Φ(t₁) = −β∂₂T`.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter ACEulerLagrange
open scoped Topology Interval ENNReal

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace V] [BorelSpace V]


omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- A function equal to a primitive `c + ∫₀ᵗ d` of an interval integrable covector function on
`[0,T]` is absolutely continuous there. -/
theorem absolutelyContinuousOnInterval_of_eq_primitive {T : ℝ} (hT : 0 ≤ T)
    {Ψ d : ℝ → E →L[ℝ] ℝ} (hd : IntervalIntegrable d volume 0 T)
    (hΨ : ∀ t ∈ Icc (0 : ℝ) T, Ψ t = Ψ 0 + ∫ r in (0 : ℝ)..t, d r) :
    AbsolutelyContinuousOnInterval Ψ 0 T := by
  have hΛ : AbsolutelyContinuousOnInterval (fun t => ∫ r in (0 : ℝ)..t, ‖d r‖) 0 T :=
    hd.norm.absolutelyContinuousOnInterval_intervalIntegral (by simp [uIcc])
  refine absolutelyContinuousOnInterval_of_dist_le (K := 1) hΛ fun x hx y hy => ?_
  rw [uIcc_of_le hT] at hx hy
  have h0x : IntervalIntegrable d volume 0 x := hd.mono_set (by
    rw [uIcc_of_le hx.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl hx.2)
  have h0y : IntervalIntegrable d volume 0 y := hd.mono_set (by
    rw [uIcc_of_le hy.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl hy.2)
  have e1 : (∫ r in (0 : ℝ)..x, d r) - ∫ r in (0 : ℝ)..y, d r = ∫ r in y..x, d r :=
    intervalIntegral.integral_interval_sub_left h0x h0y
  have e2 : (∫ r in (0 : ℝ)..x, ‖d r‖) - ∫ r in (0 : ℝ)..y, ‖d r‖ = ∫ r in y..x, ‖d r‖ :=
    intervalIntegral.integral_interval_sub_left h0x.norm h0y.norm
  rw [dist_eq_norm, Real.dist_eq, hΨ x hx, hΨ y hy, add_sub_add_left_eq_sub, e1, e2, one_mul]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- **The Stieltjes-measure form of the limit adjoint law (Theorem 11.4.4 (ii)).**  Let `Φ`, `λ`
satisfy the integrated adjoint law (ii) with `Φ(0) = λ(0)∇G(0) + β∂₁T` and `Φ(T) = −β∂₂T`, where
`λ ≥ 0` is nonincreasing with `λ(T) = 0` and `∇G` is absolutely continuous with derivative `gd₀`.
Then, for the Lebesgue–Stieltjes measure `μ` of `λ` (`multiplierMeasure`), for a.e. `t`
`Φ(t) − λ(t)∇G(t) = −β∂₂T − ∫_t^T (λ⁰ f⁰ₓ − (Φ − λ∇G)·fₓ) − ∫_{(t,T]} ∇G dμ`:
the term `λ ∇G` of the costate equation is the Stieltjes integral `∫ ∇G dλ`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Theorem 11.4.4 (ii)–(iv). -/
theorem adjointLaw_stieltjes {T : ℝ} (hT : 0 ≤ T) {lam : ℝ → ℝ}
    (hanti : AntitoneOn lam (Icc (0 : ℝ) T)) (hlam : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ lam t)
    (hlamT : lam T = 0) {Φ : ℝ → E →L[ℝ] ℝ} {lam0 : ℝ} {cx₀ g₀ gd₀ : ℝ → E →L[ℝ] ℝ}
    {A₀ : ℝ → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)} {c q : E →L[ℝ] ℝ}
    (hgd₀ : IntervalIntegrable gd₀ volume 0 T)
    (hg₀ : ∀ s ∈ Icc (0 : ℝ) T, g₀ s = g₀ 0 + ∫ r in (0 : ℝ)..s, gd₀ r)
    (hintegrand : IntervalIntegrable (fun r => lam0 • cx₀ r - A₀ r (Φ r - lam r • g₀ r)
      + lam r • gd₀ r) volume 0 T)
    (hΦ : ∀ t ∈ Icc (0 : ℝ) T, Φ t = Φ 0 + ∫ r in (0 : ℝ)..t,
      (lam0 • cx₀ r - A₀ r (Φ r - lam r • g₀ r) + lam r • gd₀ r))
    (hΦ0 : Φ 0 = lam 0 • g₀ 0 + c) (hΦT : Φ T = -q) :
    ∀ᵐ t ∂(timeMeasure T), Φ t - lam t • g₀ t = -q
      - (∫ r in t..T, (lam0 • cx₀ r - A₀ r (Φ r - lam r • g₀ r)))
      - ∫ s in Ioc t T, g₀ s ∂(multiplierMeasure hT hanti) := by
  classical
  set a : ℝ → E →L[ℝ] ℝ := fun r => lam0 • cx₀ r - A₀ r (Φ r - lam r • g₀ r) with ha
  have hlamgd : IntervalIntegrable (fun r => lam r • gd₀ r) volume 0 T :=
    intervalIntegrable_lam_smul hT hanti hlam hlamT hgd₀
  have haI : IntervalIntegrable a volume 0 T := by
    have := hintegrand.sub hlamgd
    refine this.congr ?_
    exact fun r _ => add_sub_cancel_right _ _
  have hLSC : ∀ t ∈ Icc (0 : ℝ) T,
      limitStateCostate c lam (g₀ 0) a gd₀ t = Φ t := by
    intro t ht
    rw [hΦ t ht, hΦ0]
    simp only [limitStateCostate, ha]
    rw [add_comm c, add_assoc]
  have hTT : limitStateCostate c lam (g₀ 0) a gd₀ T = -q := by
    rw [hLSC T ⟨hT, le_rfl⟩, hΦT]
  refine momentum_eq_stieltjesTail hT hanti hlam hlamT haI hgd₀ hg₀ hTT ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [hLSC t ⟨ht.1.le, ht.2⟩]

namespace Problem

variable {P : Problem E V W}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The covector action `Ψ ↦ Ψ∘f` of a linear map has operator norm at most `‖f‖`. -/
theorem norm_covectorAction_le (f : E →L[ℝ] E) :
    ‖(ContinuousLinearMap.compL ℝ E E ℝ).flip f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun Ψ => by
    have := ContinuousLinearMap.opNorm_comp_le Ψ f
    simpa [mul_comm] using this

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- **Theorem 11.4.4 / 11.6.3, conclusions (i)–(iv), from the `ε`-level tube systems.**

Let `Φ k, lam k` be the costate and multiplier of the `ε_k`-level tube limit
(`exists_epsilonCostateSystem_of_penalisedMultiplierLimit`), with the stated uniform bounds, and
suppose the data converge as `k → ∞`:

* `f⁰ₓ(φ_k) → cx₀`, `fₓ(φ_k) → Fx₀`, `d(∇G)/dt(φ_k) → gd₀` in `L¹(0,T)`, `∇G(t,φ_k(t)) → g₀(t)`,
  and `g₀` is absolutely continuous with derivative `gd₀`;
* `φ_k' → φ₀'` in `L¹(0,T)` and `φ_k(0) → φ₀(0)` (the defect and initial covectors tend to `0`);
* the derivatives of the endpoint constraint `∂T(φ_k) → ∂T₀`.

Then, along a subsequence, `Φ_k/M_k → Φ` and `λ_k/M_k → λ` at every point of `[0,T]` (Helly),
`β_k/M_k → β`, `1/M_k → λ⁰`, `Φ` is absolutely continuous (of bounded variation), `λ ≥ 0` is
nonincreasing with `λ(T) = 0`, `λ⁰ ∈ [0,1]`, and

* (i)   `|Φ(T)| + λ(0) + |β| + λ⁰ = 1`;
* (ii)  `Φ(t) = Φ(0) + ∫₀ᵗ (λ⁰ f⁰ₓ − (Φ − λ∇G)·fₓ + λ d(∇G)/dt)`;
* (iii) `Φ(0) = λ(0)∇G(0) + β·∂₁T`;
* (iv)  `Φ(T) = −β·∂₂T`;
* the Stieltjes form of (ii): for a.e. `t`, `Φ(t) − λ(t)∇G(t) = −β∂₂T − ∫_t^T (λ⁰f⁰ₓ − (Φ −
  λ∇G)·fₓ) − ∫_{(t,T]} ∇G dμ_λ` with `μ_λ` the Lebesgue–Stieltjes measure of `λ`.

(`λ(0) = λ(0⁺)` when the multipliers are constant near `0`, Assumption 11.4.1.)  The minimum
principle (v) is not part of this statement.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.4, Theorem 11.4.4,
Theorem 11.6.3. -/
theorem exists_theorem_11_6_3_conclusions (γ₀ : VelocityTrajectory P)
    {K : ℕ → ℝ} {γ : ℕ → VelocityTrajectory P}
    {cx : ℕ → ℝ → E → E →L[ℝ] ℝ} {Fx : ℕ → ℝ → E → E →L[ℝ] E}
    {Gx : ℝ → E → E →L[ℝ] ℝ} {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)}
    {DT : ℕ → E × E →L[ℝ] W} {Φ : ℕ → ℝ → E →L[ℝ] ℝ} {lam : ℕ → ℝ → ℝ}
    (hsys : ∀ k, IsEpsilonCostateSystem P.horizon
      (tubeCostateSystem P (K k) γ₀ (γ k) (cx k) (Fx k) Gx Gxd (DT k) (Φ k) (lam k)))
    {C : ℝ}
    (hcx : ∀ k, ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖cx k t ((γ k).value t)‖ ≤ C)
    (hF : ∀ k, ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖Fx k t ((γ k).value t)‖ ≤ C)
    (hg : ∀ k, ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖Gx t ((γ k).value t)‖ ≤ C)
    (hgd : ∀ k, ∫ r in (0 : ℝ)..P.horizon, ‖Gxd r ((γ k).value r) (1, (γ k).velocity r)‖ ≤ C)
    {cx₀ : ℝ → E →L[ℝ] ℝ} {Fx₀ : ℝ → E →L[ℝ] E} {g₀ gd₀ : ℝ → E →L[ℝ] ℝ}
    {DT₀ : E × E →L[ℝ] W}
    (hcx₀ : IntervalIntegrable cx₀ volume 0 P.horizon)
    (hgd₀ : IntervalIntegrable gd₀ volume 0 P.horizon)
    (hFxm : ∀ k, AEStronglyMeasurable (fun r => Fx k r ((γ k).value r))
      (volume.restrict (Ioc (0 : ℝ) P.horizon)))
    (hFx₀m : AEStronglyMeasurable Fx₀ (volume.restrict (Ioc (0 : ℝ) P.horizon)))
    (hg₀m : AEStronglyMeasurable g₀ (volume.restrict (Ioc (0 : ℝ) P.horizon)))
    (hF₀ : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖Fx₀ t‖ ≤ C)
    (hg₀ : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖g₀ t‖ ≤ C)
    (hcxlim : Tendsto (fun k => ∫ r in (0 : ℝ)..P.horizon,
      ‖cx k r ((γ k).value r) - cx₀ r‖) atTop (𝓝 0))
    (hFlim : Tendsto (fun k => ∫ r in (0 : ℝ)..P.horizon,
      ‖Fx k r ((γ k).value r) - Fx₀ r‖) atTop (𝓝 0))
    (hgdlim : Tendsto (fun k => ∫ r in (0 : ℝ)..P.horizon,
      ‖Gxd r ((γ k).value r) (1, (γ k).velocity r) - gd₀ r‖) atTop (𝓝 0))
    (hvlim : Tendsto (fun k => ∫ r in (0 : ℝ)..P.horizon,
      ‖(γ k).velocity r - γ₀.velocity r‖) atTop (𝓝 0))
    (hglim : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      Tendsto (fun k => Gx t ((γ k).value t)) atTop (𝓝 (g₀ t)))
    (hilim : Tendsto (fun k => ‖(γ k).value 0 - γ₀.initial‖) atTop (𝓝 0))
    (hg₀ac : ∀ s ∈ Icc (0 : ℝ) P.horizon, g₀ s = g₀ 0 + ∫ r in (0 : ℝ)..s, gd₀ r)
    (hDT : Tendsto DT atTop (𝓝 DT₀)) :
    ∃ (ψ : ℕ → ℕ) (Ψ : ℝ → E →L[ℝ] ℝ) (Λ : ℝ → ℝ) (β : (W →L[ℝ] ℝ) × (E →L[ℝ] ℝ))
      (lam0 : ℝ) (hΛ : AntitoneOn Λ (Icc (0 : ℝ) P.horizon)), StrictMono ψ ∧
      eVariationOn Ψ (Icc (0 : ℝ) P.horizon) ≠ ⊤ ∧
      AbsolutelyContinuousOnInterval Ψ 0 P.horizon ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, 0 ≤ Λ t) ∧
      Λ P.horizon = 0 ∧ 0 ≤ lam0 ∧ lam0 ≤ 1 ∧
      ‖Ψ P.horizon‖ + Λ 0 + ‖β‖ + lam0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, Ψ t = Ψ 0 + ∫ r in (0 : ℝ)..t,
        (lam0 • cx₀ r - (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx₀ r) (Ψ r - Λ r • g₀ r)
          + Λ r • gd₀ r)) ∧
      Ψ 0 = Λ 0 • g₀ 0 + tubeDl DT₀ β ∧ Ψ P.horizon = -(tubeDr DT₀ β) ∧
      AEStronglyMeasurable Ψ (volume.restrict (Ioc (0 : ℝ) P.horizon)) ∧
      AEStronglyMeasurable Λ (volume.restrict (Ioc (0 : ℝ) P.horizon)) ∧
      (∀ᵐ t ∂(timeMeasure P.horizon), Ψ t - Λ t • g₀ t = -(tubeDr DT₀ β)
        - (∫ r in t..P.horizon, (lam0 • cx₀ r
            - (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx₀ r) (Ψ r - Λ r • g₀ r)))
        - ∫ s in Ioc t P.horizon, g₀ s ∂(multiplierMeasure P.horizon_pos.le hΛ)) := by
  classical
  have hT := P.horizon_pos
  have hT0 := hT.le
  set s : ℕ → EpsilonCostateSystem (E →L[ℝ] ℝ) ((W →L[ℝ] ℝ) × (E →L[ℝ] ℝ)) := fun k =>
    tubeCostateSystem P (K k) γ₀ (γ k) (cx k) (Fx k) Gx Gxd (DT k) (Φ k) (lam k) with hs
  have hA : ∀ k, ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖(s k).A t‖ ≤ C := fun k t ht =>
    (norm_covectorAction_le _).trans (hF k t ht)
  have hA₀ : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      ‖(ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx₀ t)‖ ≤ C := fun t ht =>
    (norm_covectorAction_le _).trans (hF₀ t ht)
  have hA₀m : AEStronglyMeasurable (fun r => (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx₀ r))
      (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
    (ContinuousLinearMap.compL ℝ E E ℝ).flip.continuous.comp_aestronglyMeasurable hFx₀m
  have hAlim : Tendsto (fun k => ∫ r in (0 : ℝ)..P.horizon,
      ‖(s k).A r - (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx₀ r)‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => intervalIntegral.integral_nonneg hT0 fun r _ => norm_nonneg _)
      (fun k => ?_) hFlim
    have hdiffI : IntervalIntegrable (fun r => ‖Fx k r ((γ k).value r) - Fx₀ r‖) volume 0
        P.horizon := by
      refine intervalIntegrable_of_bounded_aestronglyMeasurable hT0 (C := C + C)
        ((hFxm k).sub hFx₀m).norm fun t ht => ?_
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (add_le_add (hF k t ht) (hF₀ t ht))
    have hAI : IntervalIntegrable (fun r => ‖(s k).A r
        - (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx₀ r)‖) volume 0 P.horizon := by
      refine intervalIntegrable_of_bounded_aestronglyMeasurable hT0 (C := C + C)
        (((hsys k).measurable_A.sub hA₀m).norm) fun t ht => ?_
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (add_le_add (hA k t ht) (hA₀ t ht))
    refine intervalIntegral.integral_mono_on hT0 hAI hdiffI fun r hr => ?_
    have : (s k).A r - (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx₀ r)
        = (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx k r ((γ k).value r) - Fx₀ r) := by
      exact ((ContinuousLinearMap.compL ℝ E E ℝ).flip.map_sub _ _).symm
    rw [this]
    exact norm_covectorAction_le _
  have hdeflim : Tendsto (fun k => ∫ r in (0 : ℝ)..P.horizon, ‖(s k).defect r‖) atTop (𝓝 0) := by
    have h2 := hvlim.const_mul 2
    rw [mul_zero] at h2
    refine h2.congr fun k => ?_
    simp only [hs, tubeCostateSystem]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [norm_smul, innerSL_apply_norm, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hιlim : Tendsto (fun k => ‖(s k).ι‖) atTop (𝓝 0) := by
    have h2 := hilim.const_mul 2
    rw [mul_zero] at h2
    refine h2.congr fun k => ?_
    simp only [hs, tubeCostateSystem]
    rw [norm_smul, innerSL_apply_norm, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  obtain ⟨ψ, Ψ, Λ, β, lam0, hψ, -, -, -, -, hBV, hanti, hnn, hΛT, h0, h1, hnorm, hint, hinit,
      hterm, hΨm, hΛm, hΨI⟩ := exists_limit_of_epsilonCostateSystems hT s hsys (C := C) hcx hA
    (fun k t ht => hg k t ht) hgd (A₀ := fun r => (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx₀ r))
    (g₀ := g₀) (gd₀ := gd₀) (Dl₀ := tubeDl DT₀) (Dr₀ := tubeDr DT₀) hcx₀ hgd₀ hA₀m hg₀m hA₀ hg₀
    hcxlim hAlim hgdlim hdeflim hglim hιlim
    ((continuous_tubeDl.tendsto DT₀).comp hDT) ((continuous_tubeDr.tendsto DT₀).comp hDT)
  refine ⟨ψ, Ψ, Λ, β, lam0, hanti, hψ, hBV, ?_, hnn, hΛT, h0, h1, hnorm, hint, hinit, hterm, hΨm,
    hΛm, ?_⟩
  · exact absolutelyContinuousOnInterval_of_eq_primitive hT0 hΨI hint
  · exact adjointLaw_stieltjes hT0 hanti hnn hΛT (A₀ := fun r =>
      (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx₀ r)) hgd₀ hg₀ac hΨI hint
      hinit hterm

end Problem

end OptimalControl.BoundedState
