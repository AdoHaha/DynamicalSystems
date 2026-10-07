/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.AffineControlPath
public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwiseEndpointConditions
public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwisePenaltyMinimizer

/-!
# From the pointwise-defect minimiser to the endpoint conditions

`VelocityPointwiseEndpointConditions.lean` proves (11.6.15)-(11.6.16) for the abstract
pointwise-defect action functional `∫ L + Φ₀ + Φ₁`.  This file connects it to the library's
penalty `Problem.velocityPenalizedPointwise` (the `F_K` of Berkovitz & Medhin §11.6 on the
velocity carrier, minimised by `Problem.exists_isMinOn_velocityPenalizedPointwise`):

* `Problem.velocityPenalizedPointwise_eq_action`: for a fixed relaxed control `ρ`, the penalty is
  `ε ‖ν - ν₀‖ +` the action of the pointwise-defect Lagrangian with the control-averaged cost
  `T⁻¹ ∫ f⁰ dν_t` (the factor `T⁻¹` is the normalisation of the occupation measure's time
  marginal) and dynamics `∫ f dν_t`;
* `Problem.eventually_perturbProfile_mem_tube`: if the velocity energy and initial distance are
  strictly inside the tube `B(ε)` and the state constraint is strictly slack along `γ`, every
  scalar-profile perturbation of `γ` stays in the tube for small parameter (the strict-interior
  hypothesis of the endpoint theorem, derived rather than assumed);
* `VelocityTrajectory.pointwisePenaltyMinimizer_endpointConditions`: the book-shaped endpoint
  conditions (11.6.15)-(11.6.16) for a strict-interior minimiser, from regularity of the
  control-averaged data (`PointwiseDefectRegularity`) and differentiability of the endpoint
  constraint.

What is *not* proved here: that the averaged data of a `Problem` with `SmoothData` satisfy
`PointwiseDefectRegularity` (that needs joint continuity of the derivative data and a
differentiation-under-the-kernel argument), and the case of an *active* state constraint along
`γ` (the book's multiplier measure).  See `AC_EL_REPORT.md`.
-/

@[expose] public section

open Set MeasureTheory Filter Metric ACEulerLagrange
open scoped Topology Interval BoundedContinuousFunction ENNReal


namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

section L2Algebra

variable {μ : Measure ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The pairing of two `L²` functions is integrable. -/
theorem integrable_inner_of_memLp {u w : ℝ → E} (hu : MemLp u 2 μ) (hw : MemLp w 2 μ) :
    Integrable (fun t => inner ℝ (u t) (w t)) μ := by
  have hsq : Integrable (fun t => ‖u t‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hsq' : Integrable (fun t => ‖w t‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).1 hw
  refine Integrable.mono' (hsq.add hsq') ?_ ?_
  · exact (continuous_inner.comp_aestronglyMeasurable
      (hu.aestronglyMeasurable.prodMk hw.aestronglyMeasurable))
  · refine Eventually.of_forall fun t => ?_
    simp only [Real.norm_eq_abs, Pi.add_apply]
    calc abs (inner ℝ (u t) (w t)) ≤ ‖u t‖ * ‖w t‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖u t‖ ^ 2 + ‖w t‖ ^ 2 := by
          have h := sq_nonneg (‖u t‖ - ‖w t‖)
          nlinarith [norm_nonneg (u t), norm_nonneg (w t)]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- Expansion of the `L²` energy of an affine perturbation. -/
theorem integral_norm_add_smul_sq {u w : ℝ → E} (hu : MemLp u 2 μ) (hw : MemLp w 2 μ) (θ : ℝ) :
    ∫ t, ‖u t + θ • w t‖ ^ 2 ∂μ
      = (∫ t, ‖u t‖ ^ 2 ∂μ) + 2 * θ * (∫ t, inner ℝ (u t) (w t) ∂μ)
        + θ ^ 2 * ∫ t, ‖w t‖ ^ 2 ∂μ := by
  have hsq : Integrable (fun t => ‖u t‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hsq' : Integrable (fun t => ‖w t‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).1 hw
  have hin := integrable_inner_of_memLp hu hw
  have hpt : ∀ t, ‖u t + θ • w t‖ ^ 2
      = ‖u t‖ ^ 2 + 2 * θ * inner ℝ (u t) (w t) + θ ^ 2 * ‖w t‖ ^ 2 := by
    intro t
    rw [norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have h12 : Integrable (fun t => ‖u t‖ ^ 2 + 2 * θ * inner ℝ (u t) (w t)) μ :=
    hsq.add (hin.const_mul (2 * θ))
  have h3 : Integrable (fun t => θ ^ 2 * ‖w t‖ ^ 2) μ := hsq'.const_mul (θ ^ 2)
  have h2 : Integrable (fun t => 2 * θ * inner ℝ (u t) (w t)) μ := hin.const_mul (2 * θ)
  simp_rw [hpt]
  rw [integral_add h12 h3, integral_add hsq h2, integral_const_mul, integral_const_mul]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The `L²` energy of an affine perturbation is a continuous (indeed quadratic) function of
the perturbation parameter. -/
theorem continuous_integral_norm_add_smul_sq {u w : ℝ → E} (hu : MemLp u 2 μ) (hw : MemLp w 2 μ) :
    Continuous fun θ : ℝ => ∫ t, ‖u t + θ • w t‖ ^ 2 ∂μ := by
  simp_rw [integral_norm_add_smul_sq hu hw]
  fun_prop
end L2Algebra

namespace Problem

/-- The control-averaged running cost. -/
noncomputable def averagedRunningCost (P : Problem E V W) (ρ : P.Relaxed) (t : ℝ) (y : E) : ℝ :=
  ∫ u, P.runningCost (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t) y (u : V)
    ∂ρ.kernel (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t)

/-- The control-averaged dynamics. -/
noncomputable def averagedDynamics (P : Problem E V W) (ρ : P.Relaxed) (t : ℝ) (y : E) : E :=
  ∫ u, P.dynamics (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t) y (u : V)
    ∂ρ.kernel (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The running cost along a trajectory is bounded (compact control set, continuous cost). -/
theorem exists_bound_runningCost_trajectory (P : Problem E V W) (x : P.Trajectory) :
    ∃ C, ∀ (t : P.Time) (u : P.Control), |P.runningCost t (x t) (u : V)| ≤ C := by
  have hK : IsCompact (((univ : Set P.Time) ×ˢ Set.range x) ×ˢ P.controlSet) :=
    (isCompact_univ.prod (isCompact_range x.continuous)).prod P.controlSet_compact
  have hc : ContinuousOn (fun z : (P.Time × E) × V => P.runningCost z.1.1 z.1.2 z.2)
      (((univ : Set P.Time) ×ˢ Set.range x) ×ˢ P.controlSet) :=
    P.runningCost_continuous.continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨C, fun t u => by simpa using hC ((t, x t), (u : V)) ⟨⟨mem_univ _, ⟨t, rfl⟩⟩, u.2⟩⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The realised velocity is the averaged dynamics along the trajectory. -/
theorem realizedVelocity_eq_averagedDynamics (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) (t : P.Time) :
    realizedVelocity P x ρ t = averagedDynamics P ρ (t : ℝ) (x t) := by
  simp [realizedVelocity, averagedDynamics, Set.projIcc_of_mem P.horizon_pos.le t.2]


/-- The relaxed running cost is the normalised horizon integral of the control-averaged cost along
the path.  (The occupation measure has the *normalised* time marginal, so the factor `T⁻¹`
appears; the book's `∫₀ᵀ f⁰ dt` is `T` times this.) -/
theorem relaxedCost_eq_inv_horizon_mul_intervalIntegral (P : Problem E V W)
    (γ : VelocityTrajectory P) (ρ : P.Relaxed) :
    P.relaxedCost (toBoundedPath γ) ρ =
      P.horizon⁻¹ * ∫ t in (0 : ℝ)..P.horizon, averagedRunningCost P ρ t (γ.value t) := by
  have hT := P.horizon_pos
  set x : P.Trajectory := toBoundedPath γ with hx
  have hcont : Continuous fun z : P.Time × P.Control => P.runningCost z.1 (x z.1) (z.2 : V) :=
    P.runningCost_continuous.comp
      (((continuous_fst).prodMk (x.continuous.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hint : Integrable (fun z : P.Time × P.Control => P.runningCost z.1 (x z.1) (z.2 : V))
      ρ.measure :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set g : P.Time → ℝ := fun t => ∫ u, P.runningCost t (x t) (u : V) ∂ρ.kernel t with hg
  have h1 : P.relaxedCost x ρ = ∫ t, g t ∂(horizonProbability P.horizon hT).toMeasure :=
    (OptimalControl.RelaxedControl.integral_kernel ρ hint).symm
  have h3 : ∫ s in (0 : ℝ)..P.horizon, g (Set.projIcc (0 : ℝ) P.horizon hT.le s)
      = P.horizon * ∫ t, g t ∂(horizonProbability P.horizon hT).toMeasure := by
    have hprefix := OptimalControl.integral_horizon_prefix hT g
      (timeEnd P.horizon hT.le)
    rw [show (((timeEnd P.horizon hT.le) : P.Time) : ℝ) = P.horizon from rfl] at hprefix
    have hfull := horizonProbability_integral_eq_prefix (T := P.horizon) hT g
    rw [hfull, ← hprefix, smul_eq_mul]
  have h4 : ∫ s in (0 : ℝ)..P.horizon, g (Set.projIcc (0 : ℝ) P.horizon hT.le s)
      = ∫ t in (0 : ℝ)..P.horizon, averagedRunningCost P ρ t (γ.value t) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT.le] at hs
    simp only [hg, averagedRunningCost, hx, toBoundedPath_apply, Set.projIcc_of_mem hT.le hs]
  rw [h1, ← h4, h3]
  field_simp


/-- The pointwise defect energy is the horizon integral of the squared pointwise velocity defect
`‖γ'(t) - f(γ(t),ν_t,t)‖²` (unnormalised: the `L²` space carries Lebesgue measure on `(0,T]`).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.6 dynamics defect. -/
theorem pointwiseDefectEnergy_eq_intervalIntegral (P : Problem E V W)
    (γ : VelocityTrajectory P) (ρ : P.Relaxed) :
    pointwiseDefectEnergy P γ ρ =
      ∫ t in (0 : ℝ)..P.horizon, ‖γ.velocity t - averagedDynamics P ρ t (γ.value t)‖ ^ 2 := by
  have hT := P.horizon_pos
  unfold pointwiseDefectEnergy
  rw [Lp_two_norm_sq_eq_integral_norm_sq, intervalIntegral.integral_of_le hT.le]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub γ.toLp (realizedVelocityLp P (toBoundedPath γ) ρ), γ.coeFn_toLp,
    realizedVelocityLp_coeFn P (toBoundedPath γ) ρ, ae_restrict_mem measurableSet_Ioc]
    with a hsub hγ hr hmem
  rw [hsub, Pi.sub_apply, hγ, hr]
  simp only [realizedVelocityOnLine, realizedVelocity, averagedDynamics, toBoundedPath_apply,
    Set.projIcc_of_mem hT.le (Ioc_subset_Icc_self hmem)]


/-- The averaged running cost along the carrier path is interval integrable. -/
theorem intervalIntegrable_averagedRunningCost (P : Problem E V W) (γ : VelocityTrajectory P)
    (ρ : P.Relaxed) :
    IntervalIntegrable (fun t => averagedRunningCost P ρ t (γ.value t)) volume 0 P.horizon := by
  have hT := P.horizon_pos
  set x : P.Trajectory := toBoundedPath γ with hx
  have hcont : Continuous fun z : P.Time × P.Control => P.runningCost z.1 (x z.1) (z.2 : V) :=
    P.runningCost_continuous.comp
      (((continuous_fst).prodMk (x.continuous.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd))
  set g : P.Time → ℝ := fun t => ∫ u, P.runningCost t (x t) (u : V) ∂ρ.kernel t with hg
  have hgm : Measurable g :=
    (OptimalControl.RelaxedControl.stronglyMeasurable_average ρ hcont.stronglyMeasurable).measurable
  obtain ⟨C, hC⟩ := exists_bound_runningCost_trajectory P x
  have hgb : ∀ t, ‖g t‖ ≤ C := by
    intro t
    have hb : ∀ᵐ u : P.Control ∂(ρ.kernel t), ‖P.runningCost t (x t) (u : V)‖ ≤ C :=
      Eventually.of_forall fun u => by simpa using hC t u
    calc ‖g t‖ ≤ C * (ρ.kernel t).real univ := norm_integral_le_of_norm_le_const hb
      _ = C := by rw [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]
  have h := OptimalControl.intervalIntegrable_horizon_extend hT hgm hgb
  refine h.congr ?_
  rw [uIoc_of_le hT.le]
  intro s hs
  simp only [hg, averagedRunningCost, hx, toBoundedPath_apply,
    Set.projIcc_of_mem hT.le (Ioc_subset_Icc_self hs)]


/-- The averaged dynamics along the carrier path is an `L²` function. -/
theorem memLp_averagedDynamics_value (P : Problem E V W) (γ : VelocityTrajectory P)
    (ρ : P.Relaxed) :
    MemLp (fun t => averagedDynamics P ρ t (γ.value t)) 2
      (ACEulerLagrange.timeMeasure P.horizon) := by
  have hT := P.horizon_pos
  have h := realizedVelocityOnLine_memLp P (toBoundedPath γ) ρ
  refine MemLp.ae_eq ?_ h
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a hmem
  simp only [realizedVelocityOnLine, realizedVelocity, averagedDynamics, toBoundedPath_apply,
    Set.projIcc_of_mem hT.le (Ioc_subset_Icc_self hmem)]

/-- The squared pointwise velocity defect is interval integrable. -/
theorem intervalIntegrable_sq_velocity_sub_averagedDynamics (P : Problem E V W)
    (γ : VelocityTrajectory P) (ρ : P.Relaxed) :
    IntervalIntegrable (fun t => ‖γ.velocity t - averagedDynamics P ρ t (γ.value t)‖ ^ 2)
      volume 0 P.horizon := by
  have h := γ.memLp_velocity.sub (memLp_averagedDynamics_value P γ ρ)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le P.horizon_pos.le]
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The squared velocity difference of two carriers is interval integrable. -/
theorem intervalIntegrable_sq_velocity_sub (P : Problem E V W)
    (γ γ₀ : VelocityTrajectory P) :
    IntervalIntegrable (fun t => ‖γ.velocity t - γ₀.velocity t‖ ^ 2) volume 0 P.horizon := by
  have h := γ.memLp_velocity.sub γ₀.memLp_velocity
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le P.horizon_pos.le]
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h


/-- **The pointwise-defect penalty is an action functional.**  For a fixed relaxed control `ρ` the
penalty `F_K` of §11.6 on the velocity carrier is the constant `ε ‖ν - ν₀‖` plus the action
`∫₀ᵀ L(t, γ, γ') dt + Φ₀(γ 0) + Φ₁(γ 0, γ T)` of the pointwise-defect Lagrangian
`L = T⁻¹ c + ‖v - γ₀'‖² + K ‖v - f‖²` (`c`, `f` the control-averaged cost and dynamics) with
`Φ₀ = ‖· - γ₀(0)‖²`, `Φ₁ = K ‖T(·,·)‖²`.  (The factor `T⁻¹` on the averaged running cost is the
normalisation of the occupation measure's time marginal.)

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.6) and §11.6. -/
theorem velocityPenalizedPointwise_eq_action (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed) (γ : VelocityTrajectory P) (ρ : P.Relaxed) :
    velocityPenalizedPointwise P K ε γ₀ ρ₀ γ ρ =
      ε * relaxedControlDistance P ρ ρ₀ +
        ACEulerLagrange.actionFunctional
          (pointwiseDefectLagrangian (fun t y => P.horizon⁻¹ * averagedRunningCost P ρ t y)
            (averagedDynamics P ρ) γ₀.velocity K)
          (fun y : E => ‖y - γ₀.initial‖ ^ 2)
          (fun q : E × E => K * ‖P.endpointConstraint q.1 q.2‖ ^ 2)
          P.horizon γ.initial γ.velocity := by
  have hT := P.horizon_pos
  have i1 : IntervalIntegrable (fun t => P.horizon⁻¹ * averagedRunningCost P ρ t (γ.value t))
      volume 0 P.horizon :=
    (intervalIntegrable_averagedRunningCost P γ ρ).const_mul _
  have i2 := intervalIntegrable_sq_velocity_sub P γ γ₀
  have i3 := (intervalIntegrable_sq_velocity_sub_averagedDynamics P γ ρ).const_mul K
  have hsplit : ∫ t in (0 : ℝ)..P.horizon,
      (P.horizon⁻¹ * averagedRunningCost P ρ t (γ.value t)
        + ‖γ.velocity t - γ₀.velocity t‖ ^ 2
        + K * ‖γ.velocity t - averagedDynamics P ρ t (γ.value t)‖ ^ 2)
      = P.horizon⁻¹ * (∫ t in (0 : ℝ)..P.horizon, averagedRunningCost P ρ t (γ.value t))
        + (∫ t in (0 : ℝ)..P.horizon, ‖γ.velocity t - γ₀.velocity t‖ ^ 2)
        + K * ∫ t in (0 : ℝ)..P.horizon,
            ‖γ.velocity t - averagedDynamics P ρ t (γ.value t)‖ ^ 2 := by
    rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  unfold velocityPenalizedPointwise velocityPenaltyRemainderPointwise
    ACEulerLagrange.actionFunctional pointwiseDefectLagrangian
  rw [relaxedCost_eq_inv_horizon_mul_intervalIntegral, pointwiseDefectEnergy_eq_intervalIntegral]
  have hval : ∀ t, ACEulerLagrange.primitive γ.initial γ.velocity t = γ.value t := fun t => rfl
  simp only [hval]
  rw [hsplit, dist_eq_norm]
  have h0 : (γ.value (timeZero P.horizon P.horizon_pos.le)) = γ.initial := γ.value_zero
  have hT' : γ.value (timeEnd P.horizon P.horizon_pos.le) = γ.value P.horizon := rfl
  rw [h0, hT']
  ring


/-- **Strict interior of the tube: scalar-profile perturbations stay admissible.**  If the
velocity energy, initial distance and control distance of `(γ, ρ)` are strictly inside the tube
`B(ε)` of (11.3.2) (control distance: non-strictly, as it is unchanged) and the state constraint is
strictly slack along `γ`, then every scalar-profile perturbation of `γ` lies in the tube for all
sufficiently small parameters.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.2), Lemma 11.3.4 and
(11.6.14). -/
theorem eventually_perturbProfile_mem_tube
    (P : Problem E V W) (γ₀ γ : VelocityTrajectory P) (ρ₀ ρ : P.Relaxed) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hv : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) < ε ^ 2)
    (hi : dist γ.initial γ₀.initial < ε) (hc : relaxedControlDistance P ρ ρ₀ ≤ ε)
    (hstate : ∀ t : P.Time, P.stateConstraint t (γ.value t) < 0)
    (e : E) (α : ℝ) (s : ℝ → ℝ) (hs : MemLp s 2 (ACEulerLagrange.timeMeasure P.horizon)) :
    ∀ᶠ θ in 𝓝 (0 : ℝ),
      InVelocityControlTube P γ₀ ρ₀ ε (γ.perturbProfile e α s hs θ) ρ := by
  have hT := P.horizon_pos
  -- the velocity energy
  have h1 : ∀ᶠ θ : ℝ in 𝓝 0,
      (∫ t in (0 : ℝ)..P.horizon,
        ‖(γ.perturbProfile e α s hs θ).velocity t - γ₀.velocity t‖ ^ 2) ≤ ε ^ 2 := by
    have hu : MemLp (fun t => γ.velocity t - γ₀.velocity t) 2
        (ACEulerLagrange.timeMeasure P.horizon) := γ.memLp_velocity.sub γ₀.memLp_velocity
    have hw := ACEulerLagrange.memLp_smul_const (E := E) hs e
    have hcont := continuous_integral_norm_add_smul_sq hu hw
    have hrw : ∀ θ : ℝ, (∫ t in (0 : ℝ)..P.horizon,
        ‖(γ.perturbProfile e α s hs θ).velocity t - γ₀.velocity t‖ ^ 2)
        = ∫ t, ‖(γ.velocity t - γ₀.velocity t) + θ • (s t • e)‖ ^ 2
            ∂(ACEulerLagrange.timeMeasure P.horizon) := by
      intro θ
      rw [intervalIntegral.integral_of_le hT.le]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [VelocityTrajectory.perturbProfile, VelocityTrajectory.perturb]
      congr 2
      abel
    have h0 : (∫ t, ‖(γ.velocity t - γ₀.velocity t) + (0 : ℝ) • (s t • e)‖ ^ 2
        ∂(ACEulerLagrange.timeMeasure P.horizon)) < ε ^ 2 := by
      have := hv
      rw [intervalIntegral.integral_of_le hT.le] at this
      simpa using this
    have hev := (hcont.continuousAt (x := (0 : ℝ))).eventually (Iio_mem_nhds h0)
    filter_upwards [hev] with θ hθ
    rw [hrw θ]
    exact le_of_lt hθ
  -- the initial distance
  have h2 : ∀ᶠ θ : ℝ in 𝓝 0, dist (γ.perturbProfile e α s hs θ).initial γ₀.initial ≤ ε := by
    have hcont : Continuous fun θ : ℝ => dist (γ.initial + θ • (α • e)) γ₀.initial := by
      fun_prop
    have h0 : dist (γ.initial + (0 : ℝ) • (α • e)) γ₀.initial < ε := by simpa using hi
    filter_upwards [(hcont.continuousAt (x := (0 : ℝ))).eventually (Iio_mem_nhds h0)] with θ hθ
    exact le_of_lt hθ
  -- the state constraint
  have h3 : ∀ᶠ θ : ℝ in 𝓝 0, ∀ t : P.Time,
      P.stateConstraint t ((γ.perturbProfile e α s hs θ).value t) ≤ 0 := by
    set η : ℝ → E := ACEulerLagrange.primitive (α • e) (fun t => s t • e) with hη
    have hηc : ContinuousOn η (Icc (0 : ℝ) P.horizon) :=
      ACEulerLagrange.continuousOn_primitive hT.le (α • e)
        (ACEulerLagrange.intervalIntegrable_of_memLp hT.le
          (ACEulerLagrange.memLp_smul_const (E := E) hs e))
    have hVal : Continuous fun t : P.Time => γ.value (t : ℝ) :=
      γ.continuousOn_value.domRestrict
    have hEta : Continuous fun t : P.Time => η (t : ℝ) := hηc.domRestrict
    have hFc : Continuous fun z : ℝ × P.Time =>
        P.stateConstraint z.2 (γ.value z.2 + z.1 • η z.2) :=
      P.stateConstraint_continuous.comp (continuous_snd.prodMk
        ((hVal.comp continuous_snd).add (continuous_fst.smul (hEta.comp continuous_snd))))
    have hcpt : IsCompact (univ : Set P.Time) := isCompact_univ
    have key := hcpt.eventually_forall_of_forall_eventually
      (x₀ := (0 : ℝ))
      (P := fun θ t => P.stateConstraint t (γ.value t + θ • η t) < 0) (fun t _ => by
        have h0 : P.stateConstraint t (γ.value t + (0 : ℝ) • η t) < 0 := by
          simpa using hstate t
        exact (hFc.continuousAt (x := ((0 : ℝ), t))).eventually (Iio_mem_nhds h0))
    filter_upwards [key] with θ hθ t
    have hval := VelocityTrajectory.perturb_value γ (α • e) (fun t => s t • e)
      (ACEulerLagrange.memLp_smul_const hs e) θ t.2
    change P.stateConstraint t ((γ.perturb (α • e) (fun t => s t • e)
      (ACEulerLagrange.memLp_smul_const hs e) θ).value t) ≤ 0
    rw [hval]
    exact (hθ t (mem_univ t)).le
  filter_upwards [h1, h2, h3] with θ hθ1 hθ2 hθ3
  exact ⟨⟨hε, hθ1, hθ2, hθ3⟩, hc⟩


/-- The pointwise-defect Lagrangian along the carrier is interval integrable. -/
theorem intervalIntegrable_pointwiseDefectLagrangian_value (P : Problem E V W) (K : ℝ)
    (γ₀ γ : VelocityTrajectory P) (ρ : P.Relaxed) :
    IntervalIntegrable (fun t => pointwiseDefectLagrangian
      (fun t y => P.horizon⁻¹ * averagedRunningCost P ρ t y) (averagedDynamics P ρ)
      γ₀.velocity K t (γ.value t) (γ.velocity t)) volume 0 P.horizon :=
  (((intervalIntegrable_averagedRunningCost P γ ρ).const_mul _).add
    (intervalIntegrable_sq_velocity_sub P γ γ₀)).add
    ((intervalIntegrable_sq_velocity_sub_averagedDynamics P γ ρ).const_mul K)

end Problem

/-- **Endpoint conditions (11.6.15)-(11.6.16) for a strict-interior minimiser of the
pointwise-defect penalty.**  Let `(γ, ρ)` minimise the pointwise-defect penalty `F_K`
(`velocityPenalizedPointwise`) over the tube `B(ε)` of (11.3.2), with the velocity energy, the
initial distance strictly inside the tube, the control distance inside the tube, and the state
constraint strictly slack along `γ` (the strict-interior minimiser of Lemma 11.3.4 /
Remark 11.6.6).  Assume the control-averaged data `c = T⁻¹∫ f⁰ dν_t`, `f = ∫ f dν_t` are regular
(`PointwiseDefectRegularity`: measurable, `C¹` in the state with locally bounded derivatives
`c_x`, `f_x`) and the endpoint constraint `T` has the derivative `D₁ ∂₁ + D₂ ∂₂` at
`(γ 0, γ T)`.  Then the momentum covector
`ψ(t) = 2⟨γ' - φ₀', ·⟩ + 2K⟨γ' - f, ·⟩` has an absolutely continuous representative `p` with
`p' = c_x - 2K⟨γ' - f, f_x ·⟩` a.e., and

* `p 0 = 2⟨γ 0 - φ₀(0), ·⟩ + 2K⟨T(γ 0, γ T), ∂₁T ·⟩`  (11.6.15),
* `p T = -2K⟨T(γ 0, γ T), ∂₂T ·⟩`  (11.6.16).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.4, (11.3.6),
(11.6.8)-(11.6.16). -/
theorem VelocityTrajectory.pointwisePenaltyMinimizer_endpointConditions [MeasurableSpace E]
    [BorelSpace E] (P : Problem E V W) (K ε : ℝ) (γ₀ γ : VelocityTrajectory P)
    (ρ₀ ρ : P.Relaxed) (hε : 0 ≤ ε)
    (hmin : ∀ (γ' : VelocityTrajectory P) (ρ' : P.Relaxed),
      InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
        Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ ρ ≤
          Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ' ρ')
    (hmem : InVelocityControlTube P γ₀ ρ₀ ε γ ρ)
    (hv : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) < ε ^ 2)
    (hi : dist γ.initial γ₀.initial < ε)
    (hstate : ∀ t : P.Time, P.stateConstraint t (γ.value t) < 0)
    {cx : ℝ → E → E →L[ℝ] ℝ} {Fx : ℝ → E → E →L[ℝ] E}
    (hreg : PointwiseDefectRegularity P.horizon
      (fun t y => P.horizon⁻¹ * Problem.averagedRunningCost P ρ t y) cx
      (Problem.averagedDynamics P ρ) Fx γ₀.velocity K)
    (D₁ D₂ : E →L[ℝ] W)
    (hT : HasFDerivAt (fun q : E × E => P.endpointConstraint q.1 q.2)
      (D₁.comp (ContinuousLinearMap.fst ℝ E E) + D₂.comp (ContinuousLinearMap.snd ℝ E E))
      (γ.value 0, γ.value P.horizon)) :
    ∃ p : ℝ → E →L[ℝ] ℝ,
      ContinuousOn p (Icc (0 : ℝ) P.horizon) ∧
      (∀ᵐ t ∂(ACEulerLagrange.timeMeasure P.horizon), p t =
        (2 : ℝ) • innerSL ℝ (γ.velocity t - γ₀.velocity t)
          + (2 * K) • innerSL ℝ (γ.velocity t - Problem.averagedDynamics P ρ t (γ.value t))) ∧
      (∀ᵐ t ∂(ACEulerLagrange.timeMeasure P.horizon), HasDerivAt p
        (cx t (γ.value t) - (2 * K) •
          (innerSL ℝ (γ.velocity t - Problem.averagedDynamics P ρ t (γ.value t))).comp
            (Fx t (γ.value t))) t) ∧
      p 0 = (2 : ℝ) • innerSL ℝ (γ.value 0 - γ₀.initial)
        + (2 * K) • (innerSL ℝ (P.endpointConstraint (γ.value 0) (γ.value P.horizon))).comp D₁ ∧
      p P.horizon = -((2 * K) •
        (innerSL ℝ (P.endpointConstraint (γ.value 0) (γ.value P.horizon))).comp D₂) := by
  set S : Set (VelocityTrajectory P) := {γ' | InVelocityControlTube P γ₀ ρ₀ ε γ' ρ} with hS
  refine γ.pointwiseDefect_endpointConditions
    (fun γ' => Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ' ρ
      - ε * Problem.relaxedControlDistance P ρ ρ₀) S
    hreg γ₀.initial P.endpointConstraint D₁ D₂ hT ?_ ?_ ?_
    (Problem.intervalIntegrable_pointwiseDefectLagrangian_value P K γ₀ γ ρ)
  · intro γ'
    rw [Problem.velocityPenalizedPointwise_eq_action]
    ring
  · intro γ' hγ'
    have := hmin γ' ρ hγ'
    change Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ ρ
        - ε * Problem.relaxedControlDistance P ρ ρ₀ ≤
      Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ' ρ
        - ε * Problem.relaxedControlDistance P ρ ρ₀
    linarith
  · intro e α s hs
    exact Problem.eventually_perturbProfile_mem_tube P γ₀ γ ρ₀ ρ hε hv hi hmem.2 hstate e α s hs

/-- **Endpoint conditions for a strict-interior minimiser of the *anchored* pointwise penalty.**
The anchored penalty `velocityPenalizedPointwise + K ‖γ(0) - P.initial‖²` (the fixed-initial
rendering of `F_K`; it is `velocityPenalizedPointwiseAnchored`) differs from the unanchored one only
in `Φ₀`, so its endpoint relations are those of
`pointwisePenaltyMinimizer_endpointConditions` with the initial relation augmented by the anchor
gradient `2K⟨γ 0 - P.initial, ·⟩`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.4, (11.3.6),
(11.6.8)-(11.6.16). -/
theorem VelocityTrajectory.pointwisePenaltyMinimizer_endpointConditions_anchored
    [MeasurableSpace E] [BorelSpace E] (P : Problem E V W) (K ε : ℝ) (γ₀ γ : VelocityTrajectory P)
    (ρ₀ ρ : P.Relaxed) (hε : 0 ≤ ε)
    (hmin : ∀ (γ' : VelocityTrajectory P) (ρ' : P.Relaxed),
      InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
        Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ ρ + K * dist γ.initial P.initial ^ 2 ≤
          Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ' ρ'
            + K * dist γ'.initial P.initial ^ 2)
    (hmem : InVelocityControlTube P γ₀ ρ₀ ε γ ρ)
    (hv : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) < ε ^ 2)
    (hi : dist γ.initial γ₀.initial < ε)
    (hstate : ∀ t : P.Time, P.stateConstraint t (γ.value t) < 0)
    {cx : ℝ → E → E →L[ℝ] ℝ} {Fx : ℝ → E → E →L[ℝ] E}
    (hreg : PointwiseDefectRegularity P.horizon
      (fun t y => P.horizon⁻¹ * Problem.averagedRunningCost P ρ t y) cx
      (Problem.averagedDynamics P ρ) Fx γ₀.velocity K)
    (D₁ D₂ : E →L[ℝ] W)
    (hT : HasFDerivAt (fun q : E × E => P.endpointConstraint q.1 q.2)
      (D₁.comp (ContinuousLinearMap.fst ℝ E E) + D₂.comp (ContinuousLinearMap.snd ℝ E E))
      (γ.value 0, γ.value P.horizon)) :
    ∃ p : ℝ → E →L[ℝ] ℝ,
      ContinuousOn p (Icc (0 : ℝ) P.horizon) ∧
      (∀ᵐ t ∂(ACEulerLagrange.timeMeasure P.horizon), p t =
        (2 : ℝ) • innerSL ℝ (γ.velocity t - γ₀.velocity t)
          + (2 * K) • innerSL ℝ (γ.velocity t - Problem.averagedDynamics P ρ t (γ.value t))) ∧
      (∀ᵐ t ∂(ACEulerLagrange.timeMeasure P.horizon), HasDerivAt p
        (cx t (γ.value t) - (2 * K) •
          (innerSL ℝ (γ.velocity t - Problem.averagedDynamics P ρ t (γ.value t))).comp
            (Fx t (γ.value t))) t) ∧
      p 0 = (2 : ℝ) • innerSL ℝ (γ.value 0 - γ₀.initial)
        + (2 * K) • innerSL ℝ (γ.value 0 - P.initial)
        + (2 * K) • (innerSL ℝ (P.endpointConstraint (γ.value 0) (γ.value P.horizon))).comp D₁ ∧
      p P.horizon = -((2 * K) •
        (innerSL ℝ (P.endpointConstraint (γ.value 0) (γ.value P.horizon))).comp D₂) := by
  set S : Set (VelocityTrajectory P) := {γ' | InVelocityControlTube P γ₀ ρ₀ ε γ' ρ} with hS
  refine γ.pointwiseDefect_endpointConditions_anchored
    (fun γ' => Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ' ρ
      + K * dist γ'.initial P.initial ^ 2 - ε * Problem.relaxedControlDistance P ρ ρ₀) S
    hreg γ₀.initial P.initial K P.endpointConstraint D₁ D₂ hT ?_ ?_ ?_
    (Problem.intervalIntegrable_pointwiseDefectLagrangian_value P K γ₀ γ ρ)
  · intro γ'
    rw [Problem.velocityPenalizedPointwise_eq_action]
    unfold ACEulerLagrange.actionFunctional
    rw [dist_eq_norm]
    ring
  · intro γ' hγ'
    have := hmin γ' ρ hγ'
    change Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ ρ + K * dist γ.initial P.initial ^ 2
        - ε * Problem.relaxedControlDistance P ρ ρ₀ ≤
      Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ' ρ + K * dist γ'.initial P.initial ^ 2
        - ε * Problem.relaxedControlDistance P ρ ρ₀
    linarith
  · intro e α s hs
    exact Problem.eventually_perturbProfile_mem_tube P γ₀ γ ρ₀ ρ hε hv hi hmem.2 hstate e α s hs

end OptimalControl.BoundedState
