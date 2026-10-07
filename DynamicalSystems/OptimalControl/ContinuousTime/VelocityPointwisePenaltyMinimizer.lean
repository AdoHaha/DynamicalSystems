/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.PenaltyBoundaryPositivity
public import DynamicalSystems.OptimalControl.ContinuousTime.AffineControlPath
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The pointwise-velocity-defect penalty `F_K` and its minimiser

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.6 define the penalty

`F_K(φ,ν) = ∫₀^{t₁} f⁰(φ(t),ν_t,t) dt + ‖φ′ − φ₀′‖² + |φ(0) − φ₀(0)|²
           + ε‖ν − ν₀‖_L + K|T(φ(0),φ(t₁))|² + K‖φ′(t) − f(φ(t),ν_t,t)‖²`

whose `K`-weighted dynamics defect is the **pointwise velocity defect** `φ′(t) − f(φ(t),ν_t,t)`,
not the Volterra residual
`φ(t) − φ(0) − t₁ ∫_{(0,t]} f` used by `velocityPenalized` in
`VelocityPenaltyMinimizer.lean`.

This module re-renders the penalty with the pointwise defect on the velocity carrier and closes
the analogue of BM Lemma 11.3.4 (`exists_isMinOn_velocityPenalizedPointwise`): the functional
attains its minimum over the tube `B(ε)` of (11.3.2), from the primitive problem data only.

The control dependence is rendered honestly: `f(φ(t),ν_t,t) = ∫_u f(t,φ(t),u) d(ρ.kernel t)`,
the control-averaged (`realizedVelocity`) field of the relaxed control `ρ`, whose conditional law
`ν_t` is `ρ.kernel t`.

## Route

The pointwise defect energy is the `L²(0,t₁;E)` squared norm of
`v − F(x,ρ)` where `v` is the candidate velocity class and `F(x,ρ)` is the `L²` class of the
control-averaged field.  The direct method (Weierstrass) needs this energy lower semicontinuous
on the weakly compact tube.  It is: `v ↦ v` is weakly continuous, and `(x,ρ) ↦ F(x,ρ)` is weakly
continuous because its pairing against every bounded continuous test function is an occupation
integral (`RelaxedControl.continuous_setIntegral_param`); the norm is weakly lower semicontinuous.
The Hilbert `L²` unit ball is weakly compact (`WeakL2Compactness`), and the remaining terms are
the continuous / weakly-lsc terms already available for the Volterra-residual penalty.

Book citations appear only in docstrings; all names are concept names.
-/

@[expose] public section

open Set MeasureTheory Filter Metric
open scoped Topology Interval BoundedContinuousFunction ENNReal

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

namespace Problem

/-! ## The pointwise velocity defect on the velocity carrier

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.6: the `K`-weighted
dynamics defect of `F_K` is `‖φ′(t) − f(φ(t),ν_t,t)‖²`.  The relaxed conditional law `ν_t` is
`ρ.kernel t`, so the defect is the candidate velocity minus the control-averaged dynamics. -/

/-- The control-averaged (realized) velocity field of a trajectory, clamped to the real line so
that it can be read as an `L²(0,t₁;E)` class.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), §11.6 dynamics defect. -/
noncomputable def realizedVelocityOnLine (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) (s : ℝ) : E :=
  realizedVelocity P x ρ (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le s)

/-- The pointwise velocity defect `φ′(t) − f(φ(t),ν_t,t)` on the velocity carrier, with
`f(φ(t),ν_t,t) = ∫_u f(t,φ(t),u) d(ρ.kernel t)`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), §11.6 dynamics defect. -/
noncomputable def pointwiseVelocityDefect (P : Problem E V W) (γ : VelocityTrajectory P)
    (ρ : P.Relaxed) (t : P.Time) : E :=
  γ.velocity t - realizedVelocity P (toBoundedPath γ) ρ t

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The dynamics field on `(time, control)` of a trajectory is jointly continuous. -/
theorem continuous_dynamics_trajectory (P : Problem E V W) (x : P.Trajectory) :
    Continuous fun z : P.Time × P.Control => P.dynamics z.1 (x z.1) (z.2 : V) :=
  P.dynamics_continuous.comp
    (((continuous_fst).prodMk (x.continuous.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The dynamics field of a trajectory is bounded uniformly in time and control: the range of a
continuous path on the compact horizon and the compact control set are compact.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Assumption 11.6.1 (compact control set, continuous dynamics). -/
theorem exists_bound_dynamics_trajectory (P : Problem E V W) (x : P.Trajectory) :
    ∃ C, ∀ (t : P.Time) (u : P.Control), ‖P.dynamics t (x t) (u : V)‖ ≤ C := by
  have hK : IsCompact (((univ : Set P.Time) ×ˢ Set.range x) ×ˢ P.controlSet) :=
    (isCompact_univ.prod (isCompact_range x.continuous)).prod P.controlSet_compact
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn P.dynamics_continuous.continuousOn
  exact ⟨C, fun t u => hC ((t, x t), (u : V)) ⟨⟨mem_univ _, ⟨t, rfl⟩⟩, u.2⟩⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The realized (control-averaged) velocity of a trajectory is bounded, by the uniform bound of
the dynamics field.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), §11.6 dynamics defect. -/
theorem exists_bound_realizedVelocity (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) :
    ∃ C, ∀ t : P.Time, ‖realizedVelocity P x ρ t‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_dynamics_trajectory P x
  refine ⟨C, fun t => ?_⟩
  have hb : ∀ᵐ u : P.Control ∂(ρ.kernel t),
      ‖P.dynamics t (x t) (u : V)‖ ≤ C :=
    Eventually.of_forall fun u => hC t u
  calc ‖realizedVelocity P x ρ t‖
      = ‖∫ u, P.dynamics t (x t) (u : V) ∂ρ.kernel t‖ := rfl
    _ ≤ C * (ρ.kernel t).real univ := norm_integral_le_of_norm_le_const hb
    _ = C := by
        rw [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]

omit [CompleteSpace E] in
/-- The realized velocity, read as a function on the real line, is `L²(0,t₁;E)`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), §11.6 dynamics defect. -/
theorem realizedVelocityOnLine_memLp (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) :
    MemLp (realizedVelocityOnLine P x ρ) 2 (horizonMeasure P.horizon) := by
  obtain ⟨C, hC⟩ := exists_bound_realizedVelocity P x ρ
  have hstrong : StronglyMeasurable (fun t : P.Time => realizedVelocity P x ρ t) :=
    RelaxedControl.stronglyMeasurable_average ρ
      (continuous_dynamics_trajectory P x).stronglyMeasurable
  have hmeas : AEStronglyMeasurable (realizedVelocityOnLine P x ρ)
      (horizonMeasure P.horizon) :=
    (hstrong.comp_measurable (continuous_projIcc (a := (0 : ℝ)) (b := P.horizon)
      (h := P.horizon_pos.le)).measurable).aestronglyMeasurable
  refine MemLp.of_bound hmeas C (Eventually.of_forall fun s => ?_)
  exact hC _

/-- The `L²(0,t₁;E)` class of the control-averaged velocity field of a trajectory and a relaxed
control.  This is the object that the pointwise velocity defect is measured against.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), §11.6 dynamics defect. -/
noncomputable def realizedVelocityLp (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) : Lp E 2 (horizonMeasure P.horizon) :=
  MemLp.toLp _ (realizedVelocityOnLine_memLp P x ρ)

/-- The pointwise defect energy `∫₀^{t₁} ‖φ′(t) − f(φ(t),ν_t,t)‖² dt`, rendered as the squared
`L²` norm of the velocity class minus the class of the control-averaged dynamics.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), §11.6 dynamics defect. -/
noncomputable def pointwiseDefectEnergy (P : Problem E V W) (γ : VelocityTrajectory P)
    (ρ : P.Relaxed) : ℝ :=
  ‖γ.toLp - realizedVelocityLp P (toBoundedPath γ) ρ‖ ^ 2

/-- The penalty remainder of the pointwise-defect `F_K`: the velocity defect, initial-value
defect, control distance, endpoint constraint and the `K`-weighted pointwise velocity defect.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), §11.6 (pointwise-defect penalty). -/
noncomputable def velocityPenaltyRemainderPointwise (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (γ : VelocityTrajectory P) (ρ : P.Relaxed) : ℝ :=
  (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2)
  + dist γ.initial γ₀.initial ^ 2
  + ε * relaxedControlDistance P ρ ρ₀
  + K * ‖P.endpointConstraint (γ.value (timeZero P.horizon P.horizon_pos.le))
      (γ.value (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2
  + K * pointwiseDefectEnergy P γ ρ

/-- The pointwise-defect penalty functional `F_K` of Berkovitz & Medhin (11.3.6)/§11.6 on the
velocity carrier: the relaxed running cost plus `velocityPenaltyRemainderPointwise`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6) and §11.6. -/
noncomputable def velocityPenalizedPointwise (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (γ : VelocityTrajectory P) (ρ : P.Relaxed) : ℝ :=
  P.relaxedCost (toBoundedPath γ) ρ
    + velocityPenaltyRemainderPointwise P K ε γ₀ ρ₀ γ ρ

/-- The pointwise-defect penalty decomposes as the relaxed running cost plus the remainder. -/
theorem velocityPenalizedPointwise_eq_cost_add_remainder (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (γ : VelocityTrajectory P) (ρ : P.Relaxed) :
    velocityPenalizedPointwise P K ε γ₀ ρ₀ γ ρ =
      P.relaxedCost (toBoundedPath γ) ρ
        + velocityPenaltyRemainderPointwise P K ε γ₀ ρ₀ γ ρ :=
  rfl

/-- The pointwise defect energy is nonnegative. -/
theorem pointwiseDefectEnergy_nonneg (P : Problem E V W) (γ : VelocityTrajectory P)
    (ρ : P.Relaxed) : 0 ≤ pointwiseDefectEnergy P γ ρ :=
  sq_nonneg _

/-- The normalized horizon integral agrees with its strict-prefix form: the two differ only by the
initial time, a null singleton.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) (the horizon has no atoms). -/
theorem horizonProbability_integral_eq_prefix {T : ℝ} (hT : 0 < T) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ControlTime T → F) :
    ∫ t, g t ∂horizonProbability T hT =
      ∫ t in Ioc (timeZero T hT.le) (timeEnd T hT.le), g t ∂horizonProbability T hT := by
  have hsub : (Ioc (timeZero T hT.le) (timeEnd T hT.le))ᶜ ⊆ {timeZero T hT.le} := by
    intro s hs
    simp only [mem_compl_iff, mem_Ioc, not_and] at hs
    simp only [mem_singleton_iff]
    by_contra hne
    exact hs (lt_of_le_of_ne s.2.1 (Ne.symm hne)) s.2.2
  have h : Ioc (timeZero T hT.le) (timeEnd T hT.le)
      =ᵐ[(horizonProbability T hT).toMeasure] univ := by
    rw [ae_eq_univ]
    exact measure_mono_null hsub (measure_singleton (timeZero T hT.le))
  simpa only [setIntegral_univ] using (setIntegral_congr_set (f := g) h).symm

omit [CompleteSpace E] in
/-- The `L²` class of the control-averaged velocity field agrees a.e. with its defining function. -/
theorem realizedVelocityLp_coeFn (P : Problem E V W) (x : P.Trajectory) (ρ : P.Relaxed) :
    (realizedVelocityLp P x ρ : ℝ → E) =ᵐ[horizonMeasure P.horizon]
      realizedVelocityOnLine P x ρ :=
  MemLp.coeFn_toLp _

/-- **The pairing of the control-averaged velocity class with a bounded continuous test function
is an occupation integral.**  For `gb : ℝ →ᵇ E`, the `L²(0,t₁;E)` inner product of the
control-averaged (`realizedVelocity`) field with `gb` equals `t₁` times the occupation integral
of `⟨f(t,x,u), gb(t)⟩`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), §11.6 dynamics defect (the control dependence through `ρ.kernel t`). -/
theorem inner_realizedVelocityLp_toLp (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) (gb : ℝ →ᵇ E) :
    inner ℝ (realizedVelocityLp P x ρ)
        (BoundedContinuousFunction.toLp (E := E) 2 (horizonMeasure P.horizon) ℝ gb) =
      P.horizon *
        ∫ z, inner ℝ (P.dynamics z.1 (x z.1) (z.2 : V)) (gb z.1) ∂ρ.measure := by
  have hT := P.horizon_pos
  -- Step 1: replace the `L²` classes by their defining functions, a.e.
  have h1 : ∫ s, inner ℝ (realizedVelocityLp P x ρ s)
        (BoundedContinuousFunction.toLp (E := E) 2 (horizonMeasure P.horizon) ℝ gb s)
        ∂(horizonMeasure P.horizon)
      = ∫ s, inner ℝ (realizedVelocity P x ρ
            (Set.projIcc (0 : ℝ) P.horizon hT.le s)) (gb s) ∂(horizonMeasure P.horizon) := by
    apply integral_congr_ae
    filter_upwards [realizedVelocityLp_coeFn P x ρ,
      BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := horizonMeasure P.horizon)
        (𝕜 := ℝ) gb] with s hs hg
    rw [hs, hg]
    rfl
  rw [L2.inner_def, h1]
  -- Step 2: the horizon measure is `volume` restricted to `(0,t₁]`; read it as an interval
  -- integral and replace `gb s` by `gb (proj s)` (equal on the interval).
  rw [← intervalIntegral.integral_of_le hT.le]
  have h2 : ∫ s in (0 : ℝ)..P.horizon, inner ℝ (realizedVelocity P x ρ
        (Set.projIcc (0 : ℝ) P.horizon hT.le s)) (gb s)
      = ∫ s in (0 : ℝ)..P.horizon, inner ℝ (realizedVelocity P x ρ
        (Set.projIcc (0 : ℝ) P.horizon hT.le s))
          (gb (Set.projIcc (0 : ℝ) P.horizon hT.le s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hT.le] at hs
    simp only [Set.projIcc_of_mem hT.le hs]
  rw [h2]
  -- Step 3: the subtype integral of `g(t) = ⟨realizedVelocity t, gb t⟩` is the interval integral
  -- of `g ∘ proj` after undoing the normalization.
  set g : P.Time → ℝ := fun t => inner ℝ (realizedVelocity P x ρ t) (gb t) with hg
  have h3 : ∫ s in (0 : ℝ)..P.horizon, g (Set.projIcc (0 : ℝ) P.horizon hT.le s)
      = P.horizon * ∫ t, g t ∂(horizonProbability P.horizon hT).toMeasure := by
    have hprefix := OptimalControl.integral_horizon_prefix hT g
      (timeEnd P.horizon hT.le)
    rw [show (((timeEnd P.horizon hT.le) : P.Time) : ℝ) = P.horizon from rfl] at hprefix
    have hfull := horizonProbability_integral_eq_prefix (T := P.horizon) hT g
    rw [hfull, ← hprefix, smul_eq_mul]
  change ∫ s in (0 : ℝ)..P.horizon, g (Set.projIcc (0 : ℝ) P.horizon hT.le s)
      = P.horizon * ∫ z, inner ℝ (P.dynamics z.1 (x z.1) (z.2 : V)) (gb z.1) ∂ρ.measure
  rw [h3]
  congr 1
  -- Step 4: the occupation integral of the inner product is the integrated conditional average.
  have hFcont : Continuous fun z : P.Time × P.Control =>
      inner ℝ (P.dynamics z.1 (x z.1) (z.2 : V)) (gb z.1) :=
    continuous_inner.comp ((continuous_dynamics_trajectory P x).prodMk
      (gb.continuous.comp (continuous_subtype_val.comp continuous_fst)))
  have hFint : Integrable (fun z : P.Time × P.Control =>
      inner ℝ (P.dynamics z.1 (x z.1) (z.2 : V)) (gb z.1)) ρ.measure :=
    hFcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← OptimalControl.RelaxedControl.integral_kernel ρ hFint]
  apply integral_congr_ae
  filter_upwards with t
  have hu : Integrable (fun u : P.Control => P.dynamics t (x t) (u : V)) (ρ.kernel t) := by
    obtain ⟨C, hC⟩ := exists_bound_dynamics_trajectory P x
    have hcont : Continuous fun u : P.Control => P.dynamics t (x t) (u : V) :=
      P.dynamics_continuous.comp
        ((continuous_const.prodMk continuous_const).prodMk continuous_subtype_val)
    exact Integrable.of_bound hcont.aestronglyMeasurable C
      (Eventually.of_forall fun u => hC t u)
  calc inner ℝ (realizedVelocity P x ρ t) (gb t)
      = inner ℝ (∫ u, P.dynamics t (x t) (u : V) ∂ρ.kernel t) (gb t) := rfl
    _ = inner ℝ (gb t) (∫ u, P.dynamics t (x t) (u : V) ∂ρ.kernel t) :=
        real_inner_comm _ _
    _ = ∫ u, inner ℝ (gb t) (P.dynamics t (x t) (u : V)) ∂ρ.kernel t :=
        (integral_inner hu (gb t)).symm
    _ = ∫ u, inner ℝ (P.dynamics t (x t) (u : V)) (gb t) ∂ρ.kernel t := by
        apply integral_congr_ae
        filter_upwards with u
        rw [real_inner_comm]

/-- The pointwise dynamics defect energy on the product domain
`E × WeakSpace(L²) × RelaxedControl`: the squared `L²` norm of `v − F` where `v` is the
candidate velocity class and `F` the control-averaged (`realizedVelocity`) dynamics field.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), §11.6 dynamics defect. -/
noncomputable def lpPointwiseDefectEnergy (P : Problem E V W)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) : ℝ :=
  ‖(toWeakSpace ℝ _).symm d.2.1 - realizedVelocityLp P (lpPath P d) d.2.2‖ ^ 2

/-- The pointwise-defect penalty `F_K` on the product domain
`E × WeakSpace(L²) × RelaxedControl`: the running cost, velocity/initial defects, control
distance, endpoint constraint and the `K`-weighted pointwise velocity defect.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), §11.6 (pointwise-defect penalty). -/
noncomputable def lpPenaltyPointwise (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) : ℝ :=
  P.relaxedCost (lpPath P d) d.2.2
  + ‖(toWeakSpace ℝ _).symm d.2.1 - γ₀.toLp‖ ^ 2
  + dist d.1 γ₀.initial ^ 2
  + ε * relaxedControlDistance P d.2.2 ρ₀
  + K * ‖P.endpointConstraint (lpPath P d (timeZero P.horizon P.horizon_pos.le))
      (lpPath P d (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2
  + K * lpPointwiseDefectEnergy P d

end Problem

/-- Elementary Fenchel inequality: `2⟪w,g⟫ − ‖g‖² ≤ ‖w‖²`. -/
theorem inner_sub_le_norm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g w : H) : 2 * inner ℝ w g - ‖g‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  nlinarith [norm_sub_sq_real w g, sq_nonneg (‖w - g‖)]

/-- The squared Hilbert norm is the supremum of its affine minorants over a dense test set.

This is the Fenchel conjugate representation `‖w‖² = sup_g (2⟪w,g⟫ − ‖g‖²)`, restricted to a
dense set of test vectors: the supremum over the dense set is the full supremum because the map
`g ↦ 2⟪w,g⟫ − ‖g‖²` is continuous and is maximised at `g = w`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 (direct method: the squared norm is a sup of weakly continuous
functionals). -/
theorem norm_sq_eq_iSup_inner_sub_norm_sq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {S : Set H} (hS : Dense S) (w : H) :
    ‖w‖ ^ 2 = ⨆ g : S, (2 * inner ℝ w (g : H) - ‖(g : H)‖ ^ 2) := by
  obtain ⟨x₀, hx₀⟩ := hS.nonempty
  have : Nonempty S := ⟨⟨x₀, hx₀⟩⟩
  apply le_antisymm
  · set F : H → ℝ := fun x => 2 * inner ℝ w x - ‖x‖ ^ 2 with hF
    have hFcont : Continuous F := by
      rw [hF]
      exact ((continuous_inner.comp (continuous_const.prodMk continuous_id)).const_mul 2).sub
        (continuous_norm.pow 2)
    have hFw : F w = ‖w‖ ^ 2 := by
      rw [hF]
      simp only [real_inner_self_eq_norm_sq]
      ring
    have hw : w ∈ closure S := by rw [hS.closure_eq]; exact mem_univ w
    choose u huS hudist using fun n : ℕ =>
      Metric.mem_closure_iff.1 hw (1 / ((n : ℝ) + 1)) (by positivity)
    have hu_tendsto : Tendsto u atTop (𝓝 w) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (f := fun n => dist (u n) w) (g := fun n => 1 / ((n : ℝ) + 1))
        (fun n => dist_nonneg) (fun n => ?_) ?_
      · exact (dist_comm (u n) w).le.trans (hudist n).le
      · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hval_tendsto : Tendsto (fun n => F (u n)) atTop (𝓝 (F w)) :=
      hFcont.continuousAt.tendsto.comp hu_tendsto
    rw [hFw] at hval_tendsto
    refine le_of_tendsto' hval_tendsto fun n => ?_
    exact le_ciSup ⟨‖w‖ ^ 2, by rintro _ ⟨g', rfl⟩; exact inner_sub_le_norm_sq (g' : H) w⟩
      (⟨u n, huS n⟩ : S)
  · refine ciSup_le fun g => ?_
    exact inner_sub_le_norm_sq (g : H) w

/-- The functional `w ↦ ⟪w, g⟫` is continuous for the weak topology. -/
theorem continuous_inner_weakSpace_right {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (g : H) :
    Continuous fun x : WeakSpace ℝ H => inner ℝ ((toWeakSpace ℝ H).symm x) g := by
  have hfun : (fun x : WeakSpace ℝ H => inner ℝ ((toWeakSpace ℝ H).symm x) g) =
      fun x => (InnerProductSpace.toDual ℝ H g) ((toWeakSpace ℝ H).symm x) := by
    funext x
    rw [real_inner_comm]
    simp
  rw [hfun]
  exact WeakBilin.eval_continuous (topDualPairing ℝ H).flip (InnerProductSpace.toDual ℝ H g)

/-- A nonnegative multiple of a lower semicontinuous function on a set is lower semicontinuous
on that set. -/
theorem lowerSemicontinuousOn_const_mul_of_nonneg {X : Type*} [TopologicalSpace X] {s : Set X}
    {f : X → ℝ} (hf : LowerSemicontinuousOn f s) {c : ℝ} (hc : 0 ≤ c) :
    LowerSemicontinuousOn (fun x => c * f x) s := by
  intro x hx
  rcases hc.eq_or_lt with rfl | hc
  · simpa using lowerSemicontinuousWithinAt_const
  · intro y hy
    have : y / c < f x := by rw [div_lt_iff₀ hc]; linarith
    filter_upwards [hf x hx (y / c) this] with x' hx'
    have h : y / c < f x' := hx'
    rw [div_lt_iff₀ hc] at h
    change y < c * f x'
    linarith

namespace Problem

variable {P : Problem E V W}

/-! ## Lower semicontinuity of the pointwise-defect penalty -/

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The occupation integral `∫ z, ⟨f(z), gb(z.1))⟩ dρ` is continuous in the trajectory and the
weak-* relaxed control, for a bounded continuous test function `gb`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), §11.6 dynamics defect (the control dependence through `ρ.kernel t`). -/
theorem continuous_occupationInner_param {Q : Type*} [TopologicalSpace Q]
    (P : Problem E V W) (π : Q → P.Trajectory) (hπ : Continuous π) (gb : ℝ →ᵇ E) :
    Continuous (fun p : Q × P.Relaxed =>
      ∫ z, inner ℝ (P.dynamics z.1 (π p.1 z.1) (z.2 : V)) (gb z.1) ∂p.2.measure) := by
  have hF : Continuous (Function.uncurry fun (q : Q) (z : P.Time × P.Control) =>
      inner ℝ (P.dynamics z.1 (π q z.1) (z.2 : V)) (gb z.1)) := by
    have hev : Continuous fun y : Q × (P.Time × P.Control) => π y.1 y.2.1 :=
      (hπ.comp continuous_fst).eval (continuous_fst.comp continuous_snd)
    exact continuous_inner.comp ((P.dynamics_continuous.comp
      (((continuous_fst.comp continuous_snd).prodMk hev).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))).prodMk
      (gb.continuous.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))))
  have h := OptimalControl.RelaxedControl.continuous_setIntegral_param
    (ν := horizonProbability P.horizon P.horizon_pos)
    (fun (q : Q) (z : P.Time × P.Control) =>
      inner ℝ (P.dynamics z.1 (π q z.1) (z.2 : V)) (gb z.1)) hF MeasurableSet.univ
  simpa only [univ_prod_univ, setIntegral_univ] using h

/-- The endpoint-constraint square is continuous on the bounded parameter set.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6). -/
theorem continuousOn_lpEndpointSq (P : Problem E V W)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint)) (R : ℝ) :
    ContinuousOn (fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
      ‖P.endpointConstraint (lpPath P d (timeZero P.horizon P.horizon_pos.le))
        (lpPath P d (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) := by
  set S₀ : Set (Lp E 2 (horizonMeasure P.horizon)) := {v | ‖v‖ ≤ R} with hS₀
  let Q := ↥((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' S₀))
  let π : Q → P.Trajectory := fun q =>
    primitiveBoundedPath P.horizon q.1.1 ((toWeakSpace ℝ _).symm q.1.2)
  have hπ : Continuous π :=
    continuousOn_iff_continuous_domRestrict.1
      (continuousOn_primitiveBoundedPath_weakSpace_prod (T := P.horizon) S₀ fun v hv => hv)
  have hend : Continuous fun q : Q =>
      ‖P.endpointConstraint (π q (timeZero P.horizon P.horizon_pos.le))
        (π q (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 :=
    (Continuous.pow (Continuous.norm (hEnd.comp
      ((hπ.eval_const _).prodMk (hπ.eval_const _)))) 2)
  let A : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    (univ : Set E) ×ˢ (toWeakSpace ℝ _ '' S₀) ×ˢ (univ : Set P.Relaxed)
  let ι : A → Q := fun d => ⟨(d.1.1, d.1.2.1), mem_univ _, d.2.2.1⟩
  have hι : Continuous ι := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
  have hcomp : Continuous fun d : A =>
      ‖P.endpointConstraint (π (ι d) (timeZero P.horizon P.horizon_pos.le))
        (π (ι d) (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 :=
    hend.comp hι
  refine continuousOn_iff_continuous_domRestrict.2 ?_
  convert hcomp using 1
  funext d
  rfl

/-- **Lower semicontinuity of the pointwise defect energy** on the weakly bounded parameter set.

The energy is `‖v − F‖²`; `v ↦ v` is weakly continuous and `(x,ρ) ↦ F` is weakly continuous
(its pairing against each bounded continuous test function is an occupation integral), so the
squared norm is weakly lower semicontinuous.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 and §11.6. -/
theorem lowerSemicontinuousOn_lpPointwiseDefectEnergy (P : Problem E V W) (R : ℝ) :
    LowerSemicontinuousOn (lpPointwiseDefectEnergy P)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) := by
  classical
  set S₀ : Set (Lp E 2 (horizonMeasure P.horizon)) := {v | ‖v‖ ≤ R} with hS₀
  set A : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    (univ : Set E) ×ˢ (toWeakSpace ℝ _ '' S₀) ×ˢ (univ : Set P.Relaxed) with hA
  let S : Set (Lp E 2 (horizonMeasure P.horizon)) :=
    Set.range (BoundedContinuousFunction.toLp (E := E) 2 (horizonMeasure P.horizon) ℝ)
  have hSdense : Dense S :=
    BoundedContinuousFunction.toLp_denseRange (E := E) (horizonMeasure P.horizon)
      (𝕜 := ℝ) (p := 2) ENNReal.coe_ne_top
  have hrepr : lpPointwiseDefectEnergy P =
      fun d => ⨆ g : S, (2 * inner ℝ
        ((toWeakSpace ℝ _).symm d.2.1 - realizedVelocityLp P (lpPath P d) d.2.2)
        (g : Lp E 2 (horizonMeasure P.horizon))
        - ‖(g : Lp E 2 (horizonMeasure P.horizon))‖ ^ 2) := by
    funext d
    exact norm_sq_eq_iSup_inner_sub_norm_sq hSdense _
  rw [hrepr]
  apply lowerSemicontinuousOn_ciSup
  · intro d _
    exact ⟨‖(toWeakSpace ℝ _).symm d.2.1 - realizedVelocityLp P (lpPath P d) d.2.2‖ ^ 2,
      by rintro _ ⟨g, rfl⟩
         exact inner_sub_le_norm_sq (g : Lp E 2 (horizonMeasure P.horizon))
           ((toWeakSpace ℝ _).symm d.2.1 - realizedVelocityLp P (lpPath P d) d.2.2)⟩
  · intro g
    obtain ⟨gb, hgb⟩ := g.2
    rw [← hgb]
    let g0 : Lp E 2 (horizonMeasure P.horizon) :=
      BoundedContinuousFunction.toLp (E := E) 2 (horizonMeasure P.horizon) ℝ gb
    have hv : ContinuousOn (fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ×
        P.Relaxed => inner ℝ ((toWeakSpace ℝ _).symm d.2.1) g0) A :=
      ((continuous_inner_weakSpace_right g0).comp
        (continuous_fst.comp continuous_snd)).continuousOn
    have hF : ContinuousOn (fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ×
        P.Relaxed => inner ℝ (realizedVelocityLp P (lpPath P d) d.2.2) g0) A := by
      have hfun : (fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
            inner ℝ (realizedVelocityLp P (lpPath P d) d.2.2) g0) =
          fun d => P.horizon * ∫ z,
            inner ℝ (P.dynamics z.1 ((lpPath P d) z.1) (z.2 : V)) (gb z.1)
              ∂(d.2.2).measure := by
        funext d
        exact inner_realizedVelocityLp_toLp P (lpPath P d) d.2.2 gb
      rw [hfun]
      refine ContinuousOn.const_mul ?_ P.horizon
      set Q := ↥((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' S₀))
      let π : Q → P.Trajectory := fun q =>
        primitiveBoundedPath P.horizon q.1.1 ((toWeakSpace ℝ _).symm q.1.2)
      have hπ : Continuous π :=
        continuousOn_iff_continuous_domRestrict.1
          (continuousOn_primitiveBoundedPath_weakSpace_prod (T := P.horizon) S₀ fun v hv => hv)
      have hocc := continuous_occupationInner_param P π hπ gb
      let ι : A → Q × P.Relaxed := fun d =>
        (⟨(d.1.1, d.1.2.1), mem_univ _, d.2.2.1⟩, d.1.2.2)
      have hι : Continuous ι := by
        refine Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_
        · exact (continuous_fst.comp continuous_subtype_val).prodMk
            (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
        · exact continuous_snd.comp (continuous_snd.comp continuous_subtype_val)
      have hcomp : Continuous fun d : A =>
          ∫ z, inner ℝ (P.dynamics z.1 (π (ι d).1 z.1) (z.2 : V)) (gb z.1)
            ∂(ι d).2.measure :=
        hocc.comp hι
      refine continuousOn_iff_continuous_domRestrict.2 ?_
      convert hcomp using 1
      funext d
      rfl
    have hcont : ContinuousOn (fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ×
        P.Relaxed => 2 * inner ℝ
          ((toWeakSpace ℝ _).symm d.2.1 - realizedVelocityLp P (lpPath P d) d.2.2) g0
          - ‖g0‖ ^ 2) A := by
      have hbase : ContinuousOn (fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ×
          P.Relaxed => 2 * inner ℝ ((toWeakSpace ℝ _).symm d.2.1) g0
            - 2 * inner ℝ (realizedVelocityLp P (lpPath P d) d.2.2) g0
            - ‖g0‖ ^ 2) A := by
        have hconst : Continuous fun _ : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ×
            P.Relaxed => ‖g0‖ ^ 2 := continuous_const
        exact ((hv.const_mul 2).sub (hF.const_mul 2)).sub hconst.continuousOn
      convert hbase using 1
      funext d
      rw [inner_sub_left, mul_sub]
    exact hcont.lowerSemicontinuousOn

/-- **Lower semicontinuity of the pointwise-defect penalty `F_K`** on the weakly bounded
parameter set (the lsc half of Lemma 11.3.4 for the pointwise defect).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 and §11.6. -/
theorem lowerSemicontinuousOn_lpPenaltyPointwise (P : Problem E V W) (K ε : ℝ) (hK : 0 ≤ K)
    (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed) (R : ℝ) :
    LowerSemicontinuousOn (lpPenaltyPointwise P K ε γ₀ ρ₀)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) := by
  set A : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    (univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
      (univ : Set P.Relaxed) with hA
  have hcost := continuousOn_lpRelaxedCost P R
  have hend := ((continuousOn_lpEndpointSq P hEnd R).const_mul K).lowerSemicontinuousOn
  have hvel : LowerSemicontinuousOn (fun d : E ×
      WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
      ‖(toWeakSpace ℝ _).symm d.2.1 - γ₀.toLp‖ ^ 2)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) := by
    have hcomp : LowerSemicontinuous (fun d : E ×
        WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
        ‖(toWeakSpace ℝ _).symm d.2.1 - γ₀.toLp‖ ^ 2) :=
      lowerSemicontinuous_comp_continuous
        (DynamicalSystems.WeakL2.lowerSemicontinuous_weakSpace_norm_sub_sq γ₀.toLp)
        (continuous_fst.comp continuous_snd)
    exact hcomp.lowerSemicontinuousOn A
  have hinit : ContinuousOn (fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ×
      P.Relaxed => dist d.1 γ₀.initial ^ 2)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) :=
    (continuous_fst.dist continuous_const).pow 2 |>.continuousOn
  have hdist : LowerSemicontinuousOn (fun d : E ×
      WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
      ε * relaxedControlDistance P d.2.2 ρ₀)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) := by
    have hcomp : LowerSemicontinuous (fun d : E ×
        WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
        ε * relaxedControlDistance P d.2.2 ρ₀) :=
      lowerSemicontinuous_const_mul_of_nonneg
        (lowerSemicontinuous_comp_continuous (lowerSemicontinuous_relaxedControlDistance P ρ₀)
          (continuous_snd.comp continuous_snd)) hε
    exact hcomp.lowerSemicontinuousOn A
  have hdef := lowerSemicontinuousOn_const_mul_of_nonneg
    (lowerSemicontinuousOn_lpPointwiseDefectEnergy P R) hK
  have h12 := (hcost.lowerSemicontinuousOn.add hvel).add hinit.lowerSemicontinuousOn
  have hsum := ((h12.add hdist).add hend).add hdef
  convert hsum using 1
  funext d
  simp only [lpPenaltyPointwise]

/-- The pointwise-defect penalty on the velocity carrier is the product-domain penalty at the
carrier data.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6) and §11.6. -/
theorem velocityPenalizedPointwise_eq_lpPenaltyPointwise (P : Problem E V W) (K ε : ℝ)
    (γ₀ γ : VelocityTrajectory P) (ρ₀ ρ : P.Relaxed) :
    velocityPenalizedPointwise P K ε γ₀ ρ₀ γ ρ =
      lpPenaltyPointwise P K ε γ₀ ρ₀ (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ) := by
  have hsq : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) =
      ‖γ.toLp - γ₀.toLp‖ ^ 2 := by
    rw [integral_sq_velocity_sub_eq γ₀ γ, Lp_two_norm_sq_eq_integral_norm_sq]
  have hpath := γ.toBoundedPath_eq_primitiveBoundedPath
  have hdefect : pointwiseDefectEnergy P γ ρ =
      lpPointwiseDefectEnergy P (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ) := by
    simp only [pointwiseDefectEnergy, lpPointwiseDefectEnergy, lpPath,
      LinearEquiv.symm_apply_apply, ← hpath]
  simp only [velocityPenalizedPointwise, velocityPenaltyRemainderPointwise, lpPenaltyPointwise,
    hsq, hdefect, lpPath, LinearEquiv.symm_apply_apply, ← hpath, toBoundedPath_apply]
  ring

/-- **Existence of a minimiser of the pointwise-defect penalty `F_K` on the velocity tube**
(the analogue of Berkovitz & Medhin, Lemma 11.3.4, for the §11.6 pointwise velocity defect).

For `0 ≤ K`, `ε ≥ 0`, a continuous endpoint constraint and a reference pair whose path satisfies
the state constraint, the pointwise-defect penalty attains its minimum over the tube `B(ε)` of
(11.3.2).  The proof is the direct method on the weakly compact product
`E × WeakSpace(L²) × RelaxedControl`: the defect energy is weakly lower semicontinuous, and the
remaining terms are continuous or already weakly lower semicontinuous.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4, (11.3.2) and §11.6. -/
theorem exists_isMinOn_velocityPenalizedPointwise (P : Problem E V W) (K ε : ℝ) (hK : 0 ≤ K)
    (hε : 0 ≤ ε) (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hstate : ∀ t : P.Time, P.stateConstraint t (γ₀.value t) ≤ 0) :
    ∃ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      InVelocityControlTube P γ₀ ρ₀ ε γ ρ ∧
      ∀ (γ' : VelocityTrajectory P) (ρ' : P.Relaxed),
        InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
          velocityPenalizedPointwise P K ε γ₀ ρ₀ γ ρ ≤
            velocityPenalizedPointwise P K ε γ₀ ρ₀ γ' ρ' := by
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
  obtain ⟨d, hd, hmin⟩ := (lowerSemicontinuousOn_lpPenaltyPointwise P K ε hK hε hEnd
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
  rw [velocityPenalizedPointwise_eq_lpPenaltyPointwise,
    velocityPenalizedPointwise_eq_lpPenaltyPointwise, hdγ]
  exact hmin ((mem_lpTube_iff P hε γ₀ γ' ρ₀ ρ').1 hγ')

end Problem

end OptimalControl.BoundedState
