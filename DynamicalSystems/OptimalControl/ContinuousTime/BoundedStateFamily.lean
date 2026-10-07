/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.StatePenalisedTubeLimit
public import DynamicalSystems.OptimalControl.ContinuousTime.EpsilonLevelBridge
public import DynamicalSystems.OptimalControl.ContinuousTime.AveragedDataContinuity

/-!
# The family of `ε_k`-level objects of the bounded-state maximum principle

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.3–§11.4, §11.6.

For an optimal relaxed pair `(γ₀, ρ₀)` and `ε_k → 0` the tube minimisers `(γ_k, ρ_k)` of
`F_{K(ε_k)}` over `B(ε_k)` with their limit multipliers form a `BoundedStateFamily`: the data that
the `ε → 0` passage and the Hamiltonian-minimum limit consume.

* `BoundedStateFamily`: tubes, minimality, strictness, the `ε`-level costate systems
  (`IsEpsilonCostateSystem`) and the a.e. momentum identity.
* `exists_boundedStateFamily`: it exists under the hypotheses of the `j → ∞` limit.

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
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]

/-- The data of the `ε_k`-level objects of an optimal relaxed pair `(γ₀, ρ₀)`:
`ε_k → 0`; `(γ_k, ρ_k)` minimises `F_{K_k}` over `B(ε_k)` with the control distance strictly
inside the tube; `(Φ_k, λ_k)` is the limit costate/multiplier, a solution of the `ε`-level costate
system, with the a.e. momentum identity
`2K_k⟨γ_k' − f̄_k,·⟩ = Φ_k − λ_k∇G − 2⟨γ_k' − γ₀',·⟩`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.8)–(11.3.25), (11.6.8). -/
structure BoundedStateFamily (P : Problem E V W) (D : P.SmoothData) (G : ℝ → E → ℝ)
    (Gx : ℝ → E → E →L[ℝ] ℝ) (Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed) where
  /-- The tube radii. -/
  ε : ℕ → ℝ
  ε_pos : ∀ k, 0 < ε k
  ε_tendsto : Tendsto ε atTop (nhds 0)
  ε_le_one : ∀ k, ε k ≤ 1
  /-- The penalty scales. -/
  K : ℕ → ℝ
  K_nonneg : ∀ k, 0 ≤ K k
  /-- The frozen controls `ν^ε`. -/
  ρe : ℕ → P.Relaxed
  /-- The limit paths. -/
  γ : ℕ → VelocityTrajectory P
  /-- The costates and multipliers. -/
  Φ : ℕ → ℝ → E →L[ℝ] ℝ
  lam : ℕ → ℝ → ℝ
  mem_tube : ∀ k, InVelocityControlTube P γ₀ ρ₀ (ε k) (γ k) (ρe k)
  minimal : ∀ k (γ' : VelocityTrajectory P) (ρ' : P.Relaxed),
    InVelocityControlTube P γ₀ ρ₀ (ε k) γ' ρ' →
      velocityPenalizedPointwiseAnchored P (K k) (ε k) γ₀ ρ₀ (γ k) (ρe k) ≤
        velocityPenalizedPointwiseAnchored P (K k) (ε k) γ₀ ρ₀ γ' ρ'
  control_lt : ∀ k, relaxedControlDistance P (ρe k) ρ₀ < ε k
  velocity_lt : ∀ k, (∫ s in (0 : ℝ)..P.horizon, ‖(γ k).velocity s - γ₀.velocity s‖ ^ 2) < ε k ^ 2
  initial_lt : ∀ k, dist (γ k).initial γ₀.initial < ε k
  system : ∀ k, IsEpsilonCostateSystem P.horizon
    (tubeCostateSystem P (K k) γ₀ (γ k) (P.averagedRunningCovector D (ρe k))
      (P.averagedDynamicsDerivative D (ρe k)) Gx Gxd
      (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        ((γ k).value 0, (γ k).value P.horizon)) (Φ k) (lam k))
  /-- Assumption 11.4.1 at level `ε_k`: where the path is strictly slack near both endpoints,
  the multiplier is constant near `0` and vanishes near `T` (Lemma 11.3.9). -/
  collar : ∀ δ : ℝ, 0 < δ → δ < P.horizon → ∀ k, (∀ t ∈ Icc (0 : ℝ) P.horizon,
      (t < δ ∨ P.horizon - δ < t) → G t ((γ k).value t) < 0) →
    (∀ t ∈ Icc (0 : ℝ) (δ / 2), lam k t = lam k 0) ∧
      ∀ t ∈ Icc (P.horizon - δ / 2) P.horizon, lam k t = 0
  momentum : ∀ k, ∀ᵐ t ∂(timeMeasure P.horizon),
    (2 * K k) • innerSL ℝ ((γ k).velocity t - P.averagedDynamics (ρe k) t ((γ k).value t))
      = Φ k t - lam k t • Gx t ((γ k).value t)
        - (2 : ℝ) • innerSL ℝ ((γ k).velocity t - γ₀.velocity t)

/-- **Existence of the family** from the hypotheses of the `j → ∞` limit and an optimal pair. -/
theorem exists_boundedStateFamily (P : Problem E V W) (D : P.SmoothData)
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
    (hND : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
      ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed), InVelocityControlTube P γ₀ ρ₀ ε γ ρ →
        ∀ t ∈ Icc (0 : ℝ) P.horizon, Gx t (γ.value t) ≠ 0) :
    Nonempty (BoundedStateFamily P D G Gx Gxd γ₀ ρ₀) := by
  classical
  obtain ⟨ε₁, hε₁, hND⟩ := hND
  set ε : ℕ → ℝ := fun k => min ε₁ 1 / ((k : ℝ) + 1) with hεdef
  have hm : 0 < min ε₁ 1 := lt_min hε₁ one_pos
  have hk1 : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  have hεpos : ∀ k, 0 < ε k := fun k => div_pos hm (by linarith [hk1 k])
  have hεle : ∀ k, ε k ≤ min ε₁ 1 := fun k =>
    div_le_self hm.le (hk1 k)
  have hεtend : Tendsto ε atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (min ε₁ 1)
    rw [mul_zero] at h
    refine h.congr fun k => ?_
    simp only [hεdef]
    ring
  have hex := fun k : ℕ =>
    exists_tubeMultiplierLimit_of_relaxedMinimum P hG hGP hGreg hGx hGdc hω₁ hω₂ (hεpos k)
      hEnd hT γ₀ ρ₀ hopt
  choose K hK ρe hTML using hex
  have hTM : ∀ k, TubeMultiplierLimit P (K k) (ε k) γ₀ ρ₀ (ρe k) G Gx Gxd ω ω'
      (P.averagedRunningCovector D (ρe k)) (P.averagedDynamicsDerivative D (ρe k)) := fun k =>
    hTML k (P.pointwiseDefectRegularity D hD (ρe k) γ₀.velocity hγ₀m γ₀.memLp_velocity (K k)
        (hK k).le)
      (fun t => P.continuous_pointwiseDefectStateCovector D hD (ρe k) (K k) t)
      (fun t => P.continuous_pointwiseDefectVelocityCovector (ρe k) γ₀.velocity (K k) t)
      (fun γ hγ => hND (ε k) (hεpos k) ((hεle k).trans (min_le_left _ _)) γ (ρe k) hγ)
  choose γs hmem hmin _hG hvel hinit hctrl seq M hlim using hTM
  have hbr := fun k =>
    exists_epsilonCostateSystem_of_penalisedMultiplierLimit
      (P.pointwiseDefectRegularity D hD (ρe k) γ₀.velocity hγ₀m γ₀.memLp_velocity (K k)
        (hK k).le) hGx hT (seq k) (hlim k)
  choose Φ lam hsys _ hcol hmom using hbr
  exact ⟨{
    ε := ε
    ε_pos := hεpos
    ε_tendsto := hεtend
    ε_le_one := fun k => (hεle k).trans (min_le_right _ _)
    K := K
    K_nonneg := fun k => (hK k).le
    ρe := ρe
    γ := γs
    Φ := Φ
    lam := lam
    mem_tube := hmem
    minimal := hmin
    control_lt := hctrl
    velocity_lt := hvel
    initial_lt := hinit
    system := hsys
    collar := fun δ hδ hδT k hs => hcol k δ hδ hδT hs
    momentum := hmom }⟩

end OptimalControl.BoundedState
