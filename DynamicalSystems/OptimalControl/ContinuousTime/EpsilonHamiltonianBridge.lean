/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.EpsilonHamiltonianInequality
public import DynamicalSystems.OptimalControl.ContinuousTime.HamiltonianMinimumLimit

/-!
# The `ε`-level Hamiltonian inequality in occupation-measure form

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.37), (11.3.38).

`epsilonHamiltonian_inequality` is stated in `L²(0,T)`.  Here it is rewritten with occupation
integrals of the Hamiltonian integrand `f⁰ − Θ·f`, where `Θ(t) = 2KT⟨γ'(t) − f̄_e(t), ·⟩` is the
penalty part of the momentum `ψ − 2(γ' − φ₀')` (the factor `T` converts the normalised time
marginal of the relaxed controls to Lebesgue measure on `[0,T]`):

`∫ H dρe ≤ ∫ H dσ + ε` for every relaxed `σ`.

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

/-- The penalty covector `Θ(t) = 2KT⟨γ'(t) − f̄_e(t), ·⟩`. -/
noncomputable def penaltyCovector (P : Problem E V W) (K : ℝ) (γ : VelocityTrajectory P)
    (ρ : P.Relaxed) (t : P.Time) : E →L[ℝ] ℝ :=
  (2 * K * P.horizon) • innerSL ℝ (γ.velocity t - realizedVelocity P (toBoundedPath γ) ρ t)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The velocity of a carrier, restricted to the compact horizon, is integrable for the
normalised time marginal. -/
theorem integrable_velocity_horizonProbability (P : Problem E V W) (γ : VelocityTrajectory P) :
    Integrable (fun t : P.Time => γ.velocity t)
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hT := P.horizon_pos
  have h1 : IntegrableOn γ.velocity (Icc 0 P.horizon) volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 γ.velocity_intervalIntegrable
  have h2 : Integrable (fun t : P.Time => γ.velocity t) (horizonVolume P.horizon) := by
    have h1' : Integrable γ.velocity ((horizonVolume P.horizon).map ((↑) : P.Time → ℝ)) := by
      rw [map_horizonVolume]; exact h1
    exact (MeasurableEmbedding.subtype_coe measurableSet_Icc).integrable_map_iff.1 h1'
  change Integrable _ ((ENNReal.ofReal P.horizon)⁻¹ • horizonVolume P.horizon)
  exact h2.smul_measure (by simp [hT])

/-- The penalty covector applied to the dynamics, integrated against a relaxed control, is the
`L²` pairing of the velocity defect with the control-averaged velocity. -/
theorem integral_penaltyCovector_dynamics (P : Problem E V W) (K : ℝ) (γ : VelocityTrajectory P)
    (ρe ρ : P.Relaxed) :
    Integrable (fun z : P.Time × P.Control =>
        penaltyCovector P K γ ρe z.1 (P.dynamics z.1 (toBoundedPath γ z.1) (z.2 : V)))
        ρ.measure ∧
      ∫ z, penaltyCovector P K γ ρe z.1 (P.dynamics z.1 (toBoundedPath γ z.1) (z.2 : V))
          ∂ρ.measure
        = 2 * K * inner ℝ (γ.toLp - realizedVelocityLp P (toBoundedPath γ) ρe)
            (realizedVelocityLp P (toBoundedPath γ) ρ) := by
  have hT := P.horizon_pos
  set x : P.Trajectory := toBoundedPath γ with hx
  set ν := horizonProbability P.horizon hT with hν
  set w : P.Time → E := fun t => γ.velocity t - realizedVelocity P x ρe t with hw
  set f : P.Time × P.Control → E := fun z => P.dynamics z.1 (x z.1) (z.2 : V) with hf
  have hΘ : (fun z : P.Time × P.Control => penaltyCovector P K γ ρe z.1 (f z))
      = fun z => (2 * K * P.horizon) * inner ℝ (w z.1) (f z) := by
    funext z
    simp [penaltyCovector, hw, hx, inner_sub_left]
  -- integrability of the defect on the time marginal
  obtain ⟨Ce, hCe⟩ := exists_bound_realizedVelocity P x ρe
  have hrve : Integrable (fun t : P.Time => realizedVelocity P x ρe t) ν.toMeasure := by
    have hstrong : StronglyMeasurable (fun t : P.Time => realizedVelocity P x ρe t) :=
      RelaxedControl.stronglyMeasurable_average ρe
        (continuous_dynamics_trajectory P x).stronglyMeasurable
    exact Integrable.of_bound hstrong.aestronglyMeasurable Ce (Eventually.of_forall hCe)
  have hwi : Integrable w ν.toMeasure :=
    (integrable_velocity_horizonProbability P γ).sub hrve
  have hwfst : Integrable (fun z : P.Time × P.Control => w z.1) ρ.measure := by
    have h : Integrable w (ρ.measure.map Prod.fst) := by
      rw [← Measure.fst, ρ.fst_measure]; exact hwi
    exact h.comp_measurable measurable_fst
  obtain ⟨C, hC⟩ := exists_bound_dynamics_trajectory P x
  have hfc : Continuous f := continuous_dynamics_trajectory P x
  have hint : Integrable (fun z : P.Time × P.Control => inner ℝ (w z.1) (f z)) ρ.measure := by
    refine (hwfst.norm.mul_const C).mono'
      (hwfst.aestronglyMeasurable.inner hfc.aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    calc ‖inner ℝ (w z.1) (f z)‖ ≤ ‖w z.1‖ * ‖f z‖ := norm_inner_le_norm _ _
      _ ≤ ‖w z.1‖ * C := mul_le_mul_of_nonneg_left (hC z.1 z.2) (norm_nonneg _)
  refine ⟨?_, ?_⟩
  · rw [hΘ]; exact hint.const_mul _
  rw [hΘ, integral_const_mul]
  -- disintegrate
  rw [← OptimalControl.RelaxedControl.integral_kernel ρ hint]
  set g : P.Time → ℝ := fun t => inner ℝ (w t) (realizedVelocity P x ρ t) with hg
  have hkernel : (fun t => ∫ u, inner ℝ (w (t, u).1) (f (t, u)) ∂ρ.kernel t) = g := by
    funext t
    have hu : Integrable (fun u : P.Control => P.dynamics t (x t) (u : V)) (ρ.kernel t) := by
      have hcont : Continuous fun u : P.Control => P.dynamics t (x t) (u : V) :=
        P.dynamics_continuous.comp
          ((continuous_const.prodMk continuous_const).prodMk continuous_subtype_val)
      exact Integrable.of_bound hcont.aestronglyMeasurable C
        (Eventually.of_forall fun u => hC t u)
    exact integral_inner hu (w t)
  rw [hkernel]
  have h3 : ∫ s in (0 : ℝ)..P.horizon, g (Set.projIcc (0 : ℝ) P.horizon hT.le s)
      = P.horizon * ∫ t, g t ∂ν.toMeasure := by
    have hprefix := OptimalControl.integral_horizon_prefix hT g
      (timeEnd P.horizon hT.le)
    rw [show (((timeEnd P.horizon hT.le) : P.Time) : ℝ) = P.horizon from rfl] at hprefix
    have hfull := horizonProbability_integral_eq_prefix (T := P.horizon) hT g
    rw [hfull, ← hprefix, smul_eq_mul]
  -- the `L²` side
  have hL2 : inner ℝ (γ.toLp - realizedVelocityLp P x ρe) (realizedVelocityLp P x ρ)
      = ∫ s in (0 : ℝ)..P.horizon, g (Set.projIcc (0 : ℝ) P.horizon hT.le s) := by
    rw [L2.inner_def, intervalIntegral.integral_of_le hT.le]
    have hae : ∀ᵐ s ∂(horizonMeasure P.horizon),
        inner ℝ ((γ.toLp - realizedVelocityLp P x ρe : Lp E 2 (horizonMeasure P.horizon)) s)
            ((realizedVelocityLp P x ρ : Lp E 2 (horizonMeasure P.horizon)) s)
          = inner ℝ (γ.velocity s - realizedVelocityOnLine P x ρe s)
              (realizedVelocityOnLine P x ρ s) := by
      filter_upwards [Lp.coeFn_sub γ.toLp (realizedVelocityLp P x ρe), γ.coeFn_toLp,
        realizedVelocityLp_coeFn P x ρe, realizedVelocityLp_coeFn P x ρ] with s h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, h3, h4]
    rw [integral_congr_ae hae]
    have hae2 : ∀ᵐ s ∂(horizonMeasure P.horizon),
        inner ℝ (γ.velocity s - realizedVelocityOnLine P x ρe s)
              (realizedVelocityOnLine P x ρ s)
          = g (Set.projIcc (0 : ℝ) P.horizon hT.le s) := by
      rw [horizonMeasure, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with s hs
      have hs' : s ∈ Icc (0 : ℝ) P.horizon := ⟨hs.1.le, hs.2⟩
      simp only [hg, hw, realizedVelocityOnLine, Set.projIcc_of_mem hT.le hs']
    exact integral_congr_ae hae2
  rw [hL2, h3]
  ring

/-- With `c = 1` and `Θ` the penalty covector, the Hamiltonian integral is the relaxed cost
minus `2K` times the `L²` pairing of the velocity defect with the control-averaged velocity. -/
theorem hamiltonianIntegral_penaltyCovector_eq (P : Problem E V W) (K : ℝ)
    (γ : VelocityTrajectory P) (ρe ρ : P.Relaxed) :
    hamiltonianIntegral P ρ (toBoundedPath γ) (penaltyCovector P K γ ρe) 1
      = P.relaxedCost (toBoundedPath γ) ρ
        - 2 * K * inner ℝ (γ.toLp - realizedVelocityLp P (toBoundedPath γ) ρe)
            (realizedVelocityLp P (toBoundedPath γ) ρ) := by
  obtain ⟨hΘint, hΘeq⟩ := integral_penaltyCovector_dynamics P K γ ρe ρ
  set x : P.Trajectory := toBoundedPath γ with hx
  have hcont : Continuous fun z : P.Time × P.Control => P.runningCost z.1 (x z.1) (z.2 : V) :=
    P.runningCost_continuous.comp
      (((continuous_fst).prodMk (x.continuous.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hL : Integrable (fun z : P.Time × P.Control => P.runningCost z.1 (x z.1) (z.2 : V))
      ρ.measure :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [hamiltonianIntegral, one_mul]
  rw [integral_sub hL hΘint, hΘeq]
  rfl

/-- **The `ε`-level Hamiltonian inequality in occupation-measure form.** -/
theorem hamiltonianIntegral_le_of_epsilonHamiltonian (P : Problem E V W) (K ε : ℝ) (hK : 0 ≤ K)
    (hε : 0 ≤ ε) (γ₀ γ : VelocityTrajectory P) (ρ₀ ρe : P.Relaxed)
    (hmem : InVelocityControlTube P γ₀ ρ₀ ε γ ρe)
    (hlt : relaxedControlDistance P ρe ρ₀ < ε)
    (hmin : ∀ (γ' : VelocityTrajectory P) (ρ' : P.Relaxed),
      InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
        velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ ρe ≤
          velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ' ρ')
    (σ : P.Relaxed) :
    hamiltonianIntegral P ρe (toBoundedPath γ) (penaltyCovector P K γ ρe) 1
      ≤ hamiltonianIntegral P σ (toBoundedPath γ) (penaltyCovector P K γ ρe) 1 + ε := by
  have h := epsilonHamiltonian_inequality P K ε hK hε γ₀ γ ρ₀ ρe hmem hlt hmin σ
  rw [hamiltonianIntegral_penaltyCovector_eq, hamiltonianIntegral_penaltyCovector_eq]
  rw [inner_sub_right] at h
  linarith

end Problem

end OptimalControl.BoundedState
