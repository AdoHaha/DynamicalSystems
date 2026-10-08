/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.BoundedStateMaximumPrinciple
public import DynamicalSystems.OptimalControl.ContinuousTime.StatePenalisedVelocityFunctional
public import DynamicalSystems.OptimalControl.ContinuousTime.StatePenalisedTubeMinimizer

/-!
# The unconstrained Pontryagin maximum principle (Berkovitz & Medhin Thm 6.3.5 / 6.3.12)

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Theorem 6.3.5 (maximum
principle in integrated form, compact constraints) and Theorem 6.3.12 (pointwise maximum
principle).  These are the unconstrained companions of the bounded-state maximum principle
(Theorem 11.6.3) of `BoundedStateMaximumPrinciple.lean`.

## Rendering of the unconstrained problem

The bounded-state library encodes the state inequality `G(t, φ(t)) ≤ 0` through the problem field
`P.stateConstraint` and Assumption 11.3.8 (`∇G ≠ 0` on a tube) through the nondegeneracy hypothesis
`hND`.  The *unconstrained* problem is the case in which the inequality is vacuous.  The library
theorem `exists_boundedStateMaximumPrinciple` nevertheless requires `hND`, so a literal
`G ≡ -1` (whose gradient vanishes identically) cannot be fed to it.  This module therefore
specialises the bounded-state theorem at an **inactive but nondegenerate** constraint: a function
`G` with `G(t, y) < 0` for every `(t, y)` — so `G(t, φ(t)) ≤ 0` holds for *every* path, making the
state inequality vacuous — whose state gradient `Gx` does not vanish.  The reference path is then
strictly slack, so the state multiplier `Λ` is constant (complementarity) and hence identically
zero (terminal condition); the modified Hamiltonian `λ⁰ T⁻¹ f⁰ − (Ψ − Λ∇G)·f` reduces to the
unconstrained Hamiltonian `λ⁰ T⁻¹ f⁰ − Ψ·f`.  The resulting statement below mentions no state
constraint at all.

The abstract form `exists_unconstrainedMaximumPrinciple_of_relaxed_minimum` takes the inactive
nondegenerate constraint as data (a concrete witness is `G(t, y) = -exp (b y)` with `b ≠ 0`).  The
integrated-form companion
`hamiltonianIntegral_le_of_ae_hamiltonian_le` turns the a.e. pointwise minimum principle of
Theorem 6.3.12 into the integrated inequality (6.3.7) of Theorem 6.3.5 over an arbitrary relaxed
control.

Book citations live in docstrings only; all declaration names are concept names.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology Interval ProbabilityTheory

namespace OptimalControl.BoundedState

open Problem

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace V] [BorelSpace V]

/-- The library's smooth hinge (`smoothHinge = expNegInvGlue`) is a state penalty profile
(Berkovitz & Medhin, (11.3.7)): continuous, vanishing on `(-∞, 0]`, positive on `(0, ∞)`. -/
theorem isStatePenaltyProfile_smoothHinge : IsStatePenaltyProfile smoothHinge where
  continuous := smoothHinge_contDiff.continuous
  eq_zero_of_nonpos _ hs := smoothHinge_zero_of_nonpos hs
  pos_of_pos _ hs := smoothHinge_pos_of_pos hs

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] [BorelSpace V] in
/-- **An inactive state constraint is no constraint.**  If `G(t,y) < 0` for every `(t,y)` and
`P.stateConstraint = G`, then relaxed admissibility reduces to the trajectory equation and the
endpoint equality; the state inequality holds for every path.  This is the sense in which the
specialisation below is the *unconstrained* problem. -/
theorem isRelaxedAdmissible_iff_of_inactiveStateConstraint (P : Problem E V W) {G : ℝ → E → ℝ}
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hinactive : ∀ (t : ℝ) (y : E), G t y < 0)
    (x : P.Trajectory) (ρ : P.Relaxed) :
    P.IsRelaxedAdmissible x ρ ↔
      IsRelaxedTrajectory P.horizon_pos P.relaxedDynamics P.initial x ρ ∧
      P.endpointConstraint (x (timeZero P.horizon P.horizon_pos.le))
        (x (timeEnd P.horizon P.horizon_pos.le)) = 0 := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, fun t => le_of_lt ((hGP t (x t)).trans_lt (hinactive t (x t)))⟩

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ W] in
/-- **The integrated Hamiltonian minimum (Berkovitz & Medhin Theorem 6.3.5 (iii)).**  An a.e.
pointwise Hamiltonian minimum against every control value integrates to the inequality
`hamiltonianIntegral ρ₀ ≤ hamiltonianIntegral σ` for every relaxed control `σ` with the prescribed
time marginal.  This is the passage from the pointwise form of Theorem 6.3.12 to the integrated form
(6.3.7) of Theorem 6.3.5. -/
theorem hamiltonianIntegral_le_of_ae_hamiltonian_le
    (P : Problem E V W) (x₀ : P.Trajectory) (ρ₀ : P.Relaxed)
    {Θ : P.Time → E →L[ℝ] ℝ} {B : ℝ} (hΘ : Measurable Θ) (hΘb : ∀ t, ‖Θ t‖ ≤ B) (c : ℝ)
    (h : ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v : P.Control,
      ∫ u : P.Control, (c * P.runningCost t (x₀ t) (u : V)
          - Θ t (P.dynamics t (x₀ t) (u : V))) ∂ρ₀.kernel t
        ≤ c * P.runningCost t (x₀ t) (v : V) - Θ t (P.dynamics t (x₀ t) (v : V)))
    (σ : P.Relaxed) :
    hamiltonianIntegral P ρ₀ x₀ Θ c ≤ hamiltonianIntegral P σ x₀ Θ c := by
  obtain ⟨C₀, hC₀⟩ := P.exists_bound_runningCost_trajectory x₀
  obtain ⟨C₁, hC₁⟩ := P.exists_bound_dynamics_trajectory x₀
  let H : P.Time → P.Control → ℝ := fun t u =>
    c * P.runningCost t (x₀ t) (u : V) - Θ t (P.dynamics t (x₀ t) (u : V))
  have hB0 : 0 ≤ B :=
    (norm_nonneg _).trans (hΘb ⟨0, left_mem_Icc.2 P.horizon_pos.le⟩)
  have hm : ∀ u, Measurable fun t : P.Time => H t u := by
    intro u
    let _ : MeasurableSpace E := borel E
    have : BorelSpace E := ⟨rfl⟩
    have h1 : Continuous fun t : P.Time => P.runningCost t (x₀ t) (u : V) :=
      P.runningCost_continuous.comp
        ((continuous_id.prodMk x₀.continuous).prodMk continuous_const)
    have h2 : Continuous fun t : P.Time => P.dynamics t (x₀ t) (u : V) :=
      P.dynamics_continuous.comp
        ((continuous_id.prodMk x₀.continuous).prodMk continuous_const)
    have h3 : Measurable fun t : P.Time => Θ t (P.dynamics t (x₀ t) (u : V)) :=
      ContinuousLinearMap.measurable_apply₂.comp (hΘ.prodMk h2.measurable)
    exact (measurable_const.mul h1.measurable).sub h3
  have hc : ∀ t, Continuous (H t) := by
    intro t
    have h1 : Continuous fun u : P.Control => P.runningCost t (x₀ t) (u : V) :=
      P.runningCost_continuous.comp
        ((continuous_const : Continuous fun _ : P.Control => (t, x₀ t)).prodMk
          continuous_subtype_val)
    have h2 : Continuous fun u : P.Control => P.dynamics t (x₀ t) (u : V) :=
      P.dynamics_continuous.comp
        ((continuous_const : Continuous fun _ : P.Control => (t, x₀ t)).prodMk
          continuous_subtype_val)
    exact (continuous_const.mul h1).sub ((Θ t).continuous.comp h2)
  have hbd : ∀ t u, |H t u| ≤ |c| * C₀ + B * C₁ := by
    intro t u
    have h1 : |c * P.runningCost t (x₀ t) (u : V)| ≤ |c| * C₀ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hC₀ t u) (abs_nonneg c)
    have h2 : |Θ t (P.dynamics t (x₀ t) (u : V))| ≤ B * C₁ := by
      rw [← Real.norm_eq_abs]
      exact ((Θ t).le_opNorm _).trans (mul_le_mul (hΘb t) (hC₁ t u) (norm_nonneg _) hB0)
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hGi : Integrable (fun _ : P.Time => |c| * C₀ + B * C₁) σ.measure.fst := integrable_const _
  have hle : ∀ᵐ t ∂σ.measure.fst,
      ∫ u, H t u ∂ρ₀.kernel t ≤ ∫ u, H t u ∂(σ.measure.condKernel t) := by
    rw [σ.fst_measure]
    filter_upwards [h] with t ht
    have hHint : Integrable (fun u : P.Control => H t u) (σ.measure.condKernel t) :=
      (hc t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc ∫ u, H t u ∂ρ₀.kernel t
        = ∫ _u : P.Control, (∫ u, H t u ∂ρ₀.kernel t) ∂(σ.measure.condKernel t) := by
          rw [integral_const]
          simp [Measure.real]
      _ ≤ ∫ u, H t u ∂(σ.measure.condKernel t) :=
          integral_mono (integrable_const _) hHint fun u => ht u
  have key := DynamicalSystems.RelaxedHamiltonian.integral_compProd_le_of_fiber_le
    (ν := σ.measure) hm hc hbd hGi ρ₀.kernel hle
  have hmeasure : σ.measure.fst ⊗ₘ ρ₀.kernel = ρ₀.measure := by
    have hσ : σ.measure.fst = (horizonProbability P.horizon P.horizon_pos).toMeasure :=
      σ.fst_measure
    rw [hσ]
    exact RelaxedControl.disintegrate ρ₀
  rw [hmeasure] at key
  change (∫ x, Function.uncurry H x ∂ρ₀.measure) ≤ ∫ x, Function.uncurry H x ∂σ.measure
  exact key.2

/-- **The unconstrained Pontryagin maximum principle (Berkovitz & Medhin Theorem 6.3.5 / 6.3.12).**

Let `(γ₀, ρ₀)` be an optimal relaxed pair of the unconstrained problem: the state constraint is
*inactive* (`G(t, y) < 0` for every `(t, y)`, so every path satisfies `G ≤ 0`) and *nondegenerate*
(`Gx ≠ 0`).  Then there are an absolutely continuous costate `Ψ`, an endpoint multiplier `β` and a
cost coefficient `λ⁰ ∈ [0,1]` such that

* (i)   `‖Ψ(t₁)‖ + ‖β‖ + λ⁰ = 1` (normalisation);
* (ii)  `Ψ(t) = Ψ(0) + ∫₀ᵗ (λ⁰ T⁻¹ f⁰ₓ − Ψ·fₓ)` (integrated adjoint equation);
* (iii) `Ψ(0) = β·∂₁T` and (iv) `Ψ(t₁) = −β·∂₂T` (transversality);
* (v)   for a.e. `t` the conditional law `ρ₀.kernel t` minimises `λ⁰ T⁻¹ f⁰ − Ψ·f` over every
  control value (pointwise maximum principle); and
* the multipliers `(Ψ, λ⁰)` do not both vanish.

The state multiplier `Λ` is identically zero; it does not appear in the conclusion.

This is the `Λ ≡ 0` specialisation of
`OptimalControl.BoundedState.exists_boundedStateMaximumPrinciple` at an inactive nondegenerate
constraint (see the module docstring for why a literal `G ≡ -1` cannot be used). -/
theorem exists_unconstrainedMaximumPrinciple_of_relaxed_minimum
    (P : Problem E V W) (D : P.SmoothData) (hD : P.DerivativeContinuity D)
    {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)}
    (hG : Continuous fun p : ℝ × E => G p.1 p.2)
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hGreg : StateConstraintRegularity G Gx) (hGx : StateGradientRegularity Gx Gxd)
    (hGdc : ∀ t, Continuous fun q : E × E => Gxd t q.1 (1, q.2))
    (hnondegenerate : ∀ (t : ℝ) (y : E), Gx t y ≠ 0)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (hT : ContDiff ℝ 1 (fun q : E × E => P.endpointConstraint q.1 q.2))
    {γ₀ : VelocityTrajectory P} {ρ₀ : P.Relaxed}
    (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) (hγ₀m : Measurable γ₀.velocity)
    (hinactive : ∀ (t : ℝ) (y : E), G t y < 0)
    (hrank : Function.Surjective ((fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
      (γ₀.value 0, γ₀.value P.horizon)).comp (ContinuousLinearMap.inr ℝ E E))) :
    ∃ (Ψ : ℝ → E →L[ℝ] ℝ) (β : (W →L[ℝ] ℝ) × (E →L[ℝ] ℝ)) (lam0 : ℝ),
      eVariationOn Ψ (Icc (0 : ℝ) P.horizon) ≠ ⊤ ∧
      AbsolutelyContinuousOnInterval Ψ 0 P.horizon ∧
      0 ≤ lam0 ∧ lam0 ≤ 1 ∧
      ‖Ψ P.horizon‖ + ‖β‖ + lam0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, Ψ t = Ψ 0 + ∫ r in (0 : ℝ)..t,
        (lam0 • P.averagedRunningCovector D ρ₀ r (γ₀.value r)
          - (ContinuousLinearMap.compL ℝ E E ℝ).flip
              (P.averagedDynamicsDerivative D ρ₀ r (γ₀.value r)) (Ψ r))) ∧
      Ψ 0 = tubeDl (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        (γ₀.value 0, γ₀.value P.horizon)) β ∧
      Ψ P.horizon = -(tubeDr (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        (γ₀.value 0, γ₀.value P.horizon)) β) ∧
      (∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v : P.Control,
        ∫ u : P.Control, (lam0 * P.horizon⁻¹ * P.runningCost t (γ₀.value t) (u : V)
            - Ψ t (P.dynamics t (γ₀.value t) (u : V))) ∂ρ₀.kernel t
        ≤ lam0 * P.horizon⁻¹ * P.runningCost t (γ₀.value t) (v : V)
            - Ψ t (P.dynamics t (γ₀.value t) (v : V))) ∧
      ¬ ((∀ t ∈ Icc (0 : ℝ) P.horizon, Ψ t = 0) ∧ lam0 = 0) := by
  have hω₁ : IsStatePenaltyProfile smoothHinge := isStatePenaltyProfile_smoothHinge
  have hω₂ : StatePenaltyProfile smoothHinge (deriv smoothHinge) :=
    statePenaltyProfile_smoothHinge
  -- the inactive constraint is automatically strictly slack on a collar; the gradient is
  -- nonvanishing on every tube.
  have hcollar : ∃ δ : ℝ, 0 < δ ∧ δ < P.horizon ∧ ∀ t ∈ Icc (0 : ℝ) P.horizon,
      (t < δ ∨ P.horizon - δ < t) → G t (γ₀.value t) < 0 :=
    ⟨P.horizon / 2, by linarith [P.horizon_pos], by linarith [P.horizon_pos],
      fun t _ _ => hinactive t (γ₀.value t)⟩
  have hND : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
      ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed), InVelocityControlTube P γ₀ ρ₀ ε γ ρ →
        ∀ t ∈ Icc (0 : ℝ) P.horizon, Gx t (γ.value t) ≠ 0 :=
    ⟨1, one_pos, fun _ _ _ γ _ _ t _ => hnondegenerate t (γ.value t)⟩
  obtain ⟨Ψ, Λ, β, lam0, _hΛ, hBV, hAC, _hnn, hΛT, h0, h1, hnorm, hint, hinit, hterm, hmin, _hcol,
      _hrM, hcomp, hnt⟩ :=
    exists_boundedStateMaximumPrinciple P D hD hG hGP hGreg hGx hGdc hω₁ hω₂ hEnd hT γ₀ ρ₀ hopt
      hγ₀m hcollar hND hrank
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) P.horizon := ⟨le_rfl, P.horizon_pos.le⟩
  have hTI : P.horizon ∈ Icc (0 : ℝ) P.horizon := ⟨P.horizon_pos.le, le_rfl⟩
  -- the reference path is strictly slack everywhere, so `Λ` is constant, and its terminal value
  -- vanishes: `Λ ≡ 0`.
  have hΛ0 : Λ 0 = 0 := by
    rw [← hcomp 0 P.horizon h0I hTI (fun r _ => hinactive r (γ₀.value r)) P.horizon hTI, hΛT]
  have hΛzero : ∀ r ∈ Icc (0 : ℝ) P.horizon, Λ r = 0 := fun r hr =>
    (hcomp 0 P.horizon h0I hTI (fun s _ => hinactive s (γ₀.value s)) r hr).trans hΛ0
  refine ⟨Ψ, β, lam0, hBV, hAC, h0, h1, ?_, ?_, ?_, hterm, ?_, ?_⟩
  · simpa [hΛ0] using hnorm
  · intro t ht
    rw [hint t ht]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht.1] at hr
    have hrI : r ∈ Icc (0 : ℝ) P.horizon := ⟨hr.1, hr.2.trans ht.2⟩
    simp [hΛzero r hrI]
  · simpa [hΛ0] using hinit
  · filter_upwards [hmin] with t ht v
    have htI : (t : ℝ) ∈ Icc (0 : ℝ) P.horizon := ⟨t.2.1, t.2.2⟩
    simpa [hΛzero (t : ℝ) htI] using ht v
  · intro h
    exact hnt ⟨h.1, hΛzero, h.2⟩

end OptimalControl.BoundedState
