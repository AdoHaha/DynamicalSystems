/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.EpsilonOptimality
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Velocity carriers for relaxed-control trajectories

The library's relaxed-trajectory model (`IsRelaxedTrajectory`) is a Volterra
integral equation: it records the state path but **not** its velocity `φ'`.
Berkovitz & Medhin's tube `B(ε)` (11.3.2) is defined by

  `‖φ' − φ₀'‖ ≤ ε` (an `L²` velocity condition),

so a faithful rendering of `B(ε)` needs an explicit absolutely-continuous /
velocity carrier.  This file supplies it.

A `VelocityTrajectory` is a path *defined* as the primitive of an interval
integrable velocity, together with the initial value.  This is exactly the
book's `φ ∈ AC(I, X), φ' ∈ L²(I)` of (11.3.1), and it makes the velocity `φ'`
a first-class object, so the tube's velocity clause gives a uniform `L²` bound
and hence (via Cauchy–Schwarz) Arzelà–Ascoli equicontinuity.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.1)–(11.3.2) and §11.6.  All names are concept names; the
citation lives only in docstrings.
-/

@[expose] public section

open Set MeasureTheory Filter Metric
open scoped Topology Interval BoundedContinuousFunction ENNReal

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]

/-- An absolutely continuous trajectory of the bounded-state problem, carried by
its velocity.

The path is the primitive of `velocity` from the initial state `initial`.  The
carrier records precisely the book's `φ ∈ AC(I, X)`, `φ' ∈ L²(I)` of (11.3.1):
interval integrability of the velocity (so the primitive is well-defined and
a.e. differentiable by the fundamental theorem of calculus) and square
integrability of its norm (so the `L²` velocity tube is a genuine constraint).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.1)–(11.3.2). -/
structure VelocityTrajectory (P : Problem E V W) where
  /-- The initial state `φ(0)`. -/
  initial : E
  /-- The velocity field `φ'`. -/
  velocity : ℝ → E
  /-- The velocity is interval-integrable on the horizon. -/
  velocity_intervalIntegrable : IntervalIntegrable velocity volume (0 : ℝ) P.horizon
  /-- The velocity is square-integrable on the horizon (`φ' ∈ L²`). -/
  velocity_sq_integrable :
    Integrable (fun s : ℝ => ‖velocity s‖ ^ 2) (volume.restrict (Ioc (0 : ℝ) P.horizon))

namespace VelocityTrajectory

variable {P : Problem E V W}

/-- The state path `φ(t) = φ(0) + ∫₀ᵗ φ'`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.1). -/
noncomputable def value (γ : VelocityTrajectory P) (t : ℝ) : E :=
  γ.initial + ∫ s in (0 : ℝ)..t, γ.velocity s

/-- The state path has the stated initial value. -/
@[simp] theorem value_zero (γ : VelocityTrajectory P) : γ.value 0 = γ.initial := by
  simp [value]

/-- The path is continuous on the horizon: the primitive of an interval
integrable velocity. -/
theorem continuousOn_value (γ : VelocityTrajectory P) :
    ContinuousOn γ.value (Icc (0 : ℝ) P.horizon) := by
  have hprim : ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, γ.velocity s)
      ([[(0 : ℝ), P.horizon]]) :=
    intervalIntegral.continuousOn_primitive_interval' (a := (0 : ℝ))
      γ.velocity_intervalIntegrable (by simp [uIcc])
  rw [uIcc_of_le P.horizon_pos.le] at hprim
  exact continuousOn_const.add hprim

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The path has velocity `φ'` almost everywhere on the horizon (the fundamental
theorem of calculus for the interval integral).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.1). -/
theorem ae_hasDerivAt_value (γ : VelocityTrajectory P) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) P.horizon)),
      HasDerivAt γ.value (γ.velocity t) t := by
  have h := IntervalIntegrable.ae_hasDerivAt_integral γ.velocity_intervalIntegrable
  rw [uIcc_of_le P.horizon_pos.le] at h
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h] with t ht hmem
  have hd := ht hmem 0 ⟨le_rfl, P.horizon_pos.le⟩
  exact hd.const_add γ.initial

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The increment of the path is the interval integral of the velocity. -/
theorem value_sub_value (γ : VelocityTrajectory P) {r s : ℝ}
    (hr : r ∈ Icc (0 : ℝ) P.horizon) (hs : s ∈ Icc (0 : ℝ) P.horizon) :
    γ.value s - γ.value r = ∫ x in r..s, γ.velocity x := by
  have hsub : ∀ u ∈ Icc (0 : ℝ) P.horizon,
      IntervalIntegrable γ.velocity volume (0 : ℝ) u := by
    intro u hu
    exact γ.velocity_intervalIntegrable.mono_set (by
      simp only [uIcc_of_le hu.1, uIcc_of_le P.horizon_pos.le]
      exact Icc_subset_Icc le_rfl hu.2)
  simp only [value, add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left (hsub s hs) (hsub r hr)

end VelocityTrajectory

/-! ## The `L²` velocity bound gives equicontinuity

The crux that the Volterra model could not provide: a uniform `L²` bound on the
velocity yields a uniform modulus of continuity for the paths (Cauchy–Schwarz),
so Arzelà–Ascoli applies.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.1)–(11.3.2) and Lemma 11.3.5. -/

/-- Cauchy–Schwarz for the integral: the integral of the norm is controlled by the
square root of the total mass and the square root of the `L²` norm.  This is the
analytic content of the book's `L²` velocity tube.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
theorem integral_norm_le_sqrt_mass_mul_sqrt_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {v : α → E} (hv : AEStronglyMeasurable v μ)
    (hv2 : Integrable (fun s => ‖v s‖ ^ 2) μ) :
    ∫ s, ‖v s‖ ∂μ ≤ Real.sqrt (μ.real univ) * Real.sqrt (∫ s, ‖v s‖ ^ 2 ∂μ) := by
  have hmem : MemLp v (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num]
    exact (memLp_two_iff_integrable_sq_norm hv).2 (by simpa using hv2)
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (f := fun s => ‖v s‖) (g := fun _ => (1 : ℝ))
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => zero_le_one) hmem.norm (memLp_const (1 : ℝ))
  have hleft : ∫ s, ‖v s‖ * 1 ∂μ = ∫ s, ‖v s‖ ∂μ := by simp
  have hright : ∫ s, (1 : ℝ) ^ (2 : ℝ) ∂μ = μ.real univ := by
    simp [integral_const]
  rw [hleft, hright] at hmain
  have h2 : ∫ s, ‖v s‖ ^ (2 : ℝ) ∂μ = ∫ s, ‖v s‖ ^ 2 ∂μ := by
    simp only [Real.rpow_two]
  rw [h2] at hmain
  calc (∫ s, ‖v s‖ ∂μ)
      ≤ (∫ s, ‖v s‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * (μ.real univ) ^ (1 / (2 : ℝ)) := hmain
    _ = Real.sqrt (∫ s, ‖v s‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    _ = Real.sqrt (μ.real univ) * Real.sqrt (∫ s, ‖v s‖ ^ 2 ∂μ) := by ring

/-- Cauchy–Schwarz specialized to a compact interval: the `L¹` velocity over
`[a,b]` is controlled by `√(b−a)` times the `L²` velocity.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
theorem intervalIntegral_norm_le_sqrt_mul
    {v : ℝ → E} {a b C : ℝ} (hab : a ≤ b)
    (hv : IntervalIntegrable v volume a b)
    (hv2 : IntegrableOn (fun s => ‖v s‖ ^ 2) (Ioc a b) volume)
    (hC : 0 ≤ C) (hL2 : ∫ s in a..b, ‖v s‖ ^ 2 ≤ C ^ 2) :
    ∫ s in a..b, ‖v s‖ ≤ Real.sqrt (b - a) * C := by
  have hvOn : IntegrableOn v (Ioc a b) volume := by
    simpa [uIoc_of_le hab] using hv.1
  have hv_meas : AEStronglyMeasurable v (volume.restrict (Ioc a b)) :=
    hvOn.aestronglyMeasurable
  have hmain := integral_norm_le_sqrt_mass_mul_sqrt_sq (μ := volume.restrict (Ioc a b))
    hv_meas hv2
  have hmass : (volume.restrict (Ioc a b)).real univ = b - a := by
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have hLI : ∫ s, ‖v s‖ ∂(volume.restrict (Ioc a b)) = ∫ s in a..b, ‖v s‖ := by
    rw [intervalIntegral.integral_of_le hab]
  have hSQ : ∫ s, ‖v s‖ ^ 2 ∂(volume.restrict (Ioc a b)) =
      ∫ s in a..b, ‖v s‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
  rw [hLI, hSQ, hmass] at hmain
  refine hmain.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc Real.sqrt (∫ s in a..b, ‖v s‖ ^ 2) ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hL2
    _ = C := Real.sqrt_sq hC

variable {P : Problem E V W}

/-- The square integral over a sub-interval is bounded by the horizon square
integral (the integrand is nonnegative). -/
theorem intervalIntegral_sq_le_horizon {v : ℝ → E} {r s : ℝ} (hrs : r ≤ s)
    (hr : 0 ≤ r) (hs : s ≤ P.horizon)
    (hint : IntegrableOn (fun x => ‖v x‖ ^ 2) (Ioc (0 : ℝ) P.horizon) volume) :
    ∫ x in r..s, ‖v x‖ ^ 2 ≤ ∫ x in (0 : ℝ)..P.horizon, ‖v x‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le hrs, intervalIntegral.integral_of_le P.horizon_pos.le]
  exact setIntegral_mono_set hint (Eventually.of_forall fun x => sq_nonneg _)
    (Eventually.of_forall fun x hx => Ioc_subset_Ioc hr hs hx)

/-- A uniform `L²` velocity bound gives a uniform `√`-Hölder modulus for the
state paths.  This is the analytic content of the book's velocity tube: it is
what the Volterra model could not provide.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.1)–(11.3.2). -/
theorem value_dist_le_of_velocity_l2_bound (γ : VelocityTrajectory P) {C : ℝ} (hC : 0 ≤ C)
    (hL2 : ∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s‖ ^ 2 ≤ C ^ 2) :
    ∀ {r s : ℝ}, r ∈ Icc (0 : ℝ) P.horizon → s ∈ Icc (0 : ℝ) P.horizon →
      dist (γ.value r) (γ.value s) ≤ Real.sqrt |s - r| * C := by
  have key : ∀ {r s : ℝ}, r ∈ Icc (0 : ℝ) P.horizon → s ∈ Icc (0 : ℝ) P.horizon →
      r ≤ s → dist (γ.value r) (γ.value s) ≤ Real.sqrt |s - r| * C := by
    intro r s hr hs hrs
    have hstep : dist (γ.value r) (γ.value s) ≤ ∫ x in r..s, ‖γ.velocity x‖ := by
      rw [dist_eq_norm, norm_sub_rev, VelocityTrajectory.value_sub_value γ hr hs]
      exact intervalIntegral.norm_integral_le_integral_norm hrs
    have hbound := intervalIntegral_norm_le_sqrt_mul hrs
      (γ.velocity_intervalIntegrable.mono_set (by
        rw [uIcc_of_le hrs, uIcc_of_le P.horizon_pos.le]
        exact Icc_subset_Icc hr.1 hs.2))
      ((show IntegrableOn (fun x => ‖γ.velocity x‖ ^ 2) (Ioc (0 : ℝ) P.horizon) volume
          from γ.velocity_sq_integrable).mono_set (Ioc_subset_Ioc hr.1 hs.2)) hC
      ((intervalIntegral_sq_le_horizon hrs hr.1 hs.2 γ.velocity_sq_integrable).trans hL2)
    rw [abs_of_nonneg (sub_nonneg.mpr hrs)]
    exact hstep.trans hbound
  intro r s hr hs
  rcases le_total r s with hrs | hsr
  · exact key hr hs hrs
  · rw [dist_comm, abs_sub_comm]
    exact key hs hr hsr

/-- A uniformly `L²`-bounded family of velocity trajectories is equicontinuous on
the compact horizon.  This is the Arzelà–Ascoli hypothesis manufactured by the
velocity tube.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and Lemma 11.3.5. -/
theorem equicontinuous_value_of_velocity_l2_bound
    (S : Set (VelocityTrajectory P)) {C : ℝ} (hC : 0 ≤ C)
    (hS : ∀ γ ∈ S, ∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s‖ ^ 2 ≤ C ^ 2) :
    Equicontinuous (fun γ : S => fun t : P.Time => (γ : VelocityTrajectory P).value t) := by
  have hunif : UniformEquicontinuous
      (fun γ : S => fun t : P.Time => (γ : VelocityTrajectory P).value t) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    have hCp : 0 < C + 1 := by linarith
    refine ⟨(ε / (C + 1)) ^ 2, by positivity, ?_⟩
    intro r s hrs i
    have hb : 0 < ε / (C + 1) := by positivity
    have hδ : dist r s < (ε / (C + 1)) ^ 2 := hrs
    have hsqrt_lt : Real.sqrt (dist r s) < ε / (C + 1) := by
      rw [← Real.sqrt_sq hb.le]
      exact (Real.sqrt_lt_sqrt_iff (by positivity : 0 ≤ dist r s)).2 hδ
    have hle := value_dist_le_of_velocity_l2_bound (i : VelocityTrajectory P) hC (hS i i.2)
      r.2 s.2
    have hsr : Real.sqrt |(s : ℝ) - r| = Real.sqrt (dist r s) := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    rw [hsr] at hle
    rcases eq_or_lt_of_le hC with hC0 | hCpos
    · rw [← hC0, mul_zero] at hle
      exact lt_of_le_of_lt hle hε
    · calc dist ((i : VelocityTrajectory P).value r) ((i : VelocityTrajectory P).value s)
          ≤ Real.sqrt (dist r s) * C := hle
        _ < (ε / (C + 1)) * C := mul_lt_mul_of_pos_right hsqrt_lt hCpos
        _ ≤ ε := by
            rw [div_mul_eq_mul_div]
            exact (div_le_iff₀ hCp).2 (by linarith)
  exact hunif.equicontinuous

/-! ## The velocity tube `B(ε)` and compactness of its paths

This is the corrected carrier for the book's tube (11.3.2): the velocity clause
is a genuine `L²` condition on `φ' − φ₀'`.  Arzelà–Ascoli then yields compactness
of the path projection, which the Volterra model could not supply.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and Lemma 11.3.5. -/

/-- Package a velocity trajectory as a bounded continuous path on the compact
horizon, so that Arzelà–Ascoli applies.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.1). -/
noncomputable def toBoundedPath (γ : VelocityTrajectory P) : P.Time →ᵇ E :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t : P.Time => γ.value t, γ.continuousOn_value.domRestrict⟩

@[simp] theorem toBoundedPath_apply (γ : VelocityTrajectory P) (t : P.Time) :
    toBoundedPath γ t = γ.value t := rfl

/-- The velocity tube `B(ε)` of Berkovitz & Medhin (11.3.2): the `L²` velocity is
within `ε` of the reference velocity, the initial states are within `ε`, and the
candidate satisfies the state constraint.  (The control-distance clause is kept
in the separate predicate `InVelocityControlTube`; it does not affect path
compactness.)

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
def InVelocityTube (P : Problem E V W) (γ₀ : VelocityTrajectory P) (ε : ℝ)
    (γ : VelocityTrajectory P) : Prop :=
  0 ≤ ε ∧
  (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) ≤ ε ^ 2 ∧
  dist γ.initial γ₀.initial ≤ ε ∧
  (∀ t : P.Time, P.stateConstraint t (γ.value t) ≤ 0)

/-- The reference trajectory lies in every velocity tube around itself, so the
tube is nonempty whenever the reference satisfies the state constraint.  This is
the nonemptiness input to the Weierstrass argument of Lemma 11.3.4.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
theorem self_mem_InVelocityTube (γ₀ : VelocityTrajectory P) {ε : ℝ} (hε : 0 ≤ ε)
    (hstate : ∀ t : P.Time, P.stateConstraint t (γ₀.value t) ≤ 0) :
    InVelocityTube P γ₀ ε γ₀ := by
  refine ⟨hε, ?_, ?_, hstate⟩
  · simp only [sub_self, norm_zero]
    simpa using sq_nonneg ε
  · simpa using hε

/-- The full book tube `B(ε)` of (11.3.2): the velocity tube together with the
control-distance clause `‖ν − ν₀‖ ≤ ε`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
def InVelocityControlTube (P : Problem E V W) (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (ε : ℝ) (γ : VelocityTrajectory P) (ρ : P.Relaxed) : Prop :=
  InVelocityTube P γ₀ ε γ ∧ Problem.relaxedControlDistance P ρ ρ₀ ≤ ε

/-- A velocity trajectory whose paths lie in a fixed ball of the state space is a
set of bounded continuous paths; with a uniform `L²` velocity bound they form a
relatively compact family.  This is the Arzelà–Ascoli compactness that the tube
needs for the Weierstrass minimizer of `F_K` (Lemma 11.3.4).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and Lemma 11.3.5. -/
theorem isCompact_toBoundedPath_of_velocity_l2_bound
    (A : Set (VelocityTrajectory P)) {C R : ℝ} (hC : 0 ≤ C) (c : E)
    (hS : ∀ γ ∈ A, ∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s‖ ^ 2 ≤ C ^ 2)
    (hball : ∀ γ ∈ A, ∀ t : P.Time, dist (γ.value t) c ≤ R) :
    IsCompact (closure (toBoundedPath '' A)) := by
  apply BoundedContinuousFunction.arzela_ascoli (closedBall c R)
    (isCompact_closedBall c R) (toBoundedPath '' A)
  · rintro f t ⟨γ, hγ, rfl⟩
    simpa only [toBoundedPath_apply, Metric.mem_closedBall] using hball γ hγ t
  · -- Equicontinuity of the image family.
    have hunif : UniformEquicontinuous
        ((fun f : toBoundedPath '' A => (f : P.Time → E)) :
          toBoundedPath '' A → P.Time → E) := by
      rw [Metric.uniformEquicontinuous_iff]
      intro ε hε
      have hCp : 0 < C + 1 := by linarith
      refine ⟨(ε / (C + 1)) ^ 2, by positivity, ?_⟩
      intro r s hrs f
      obtain ⟨γ, hγ, hfγ⟩ := f.2
      have hb : 0 < ε / (C + 1) := by positivity
      have hδ : dist r s < (ε / (C + 1)) ^ 2 := hrs
      have hsqrt_lt : Real.sqrt (dist r s) < ε / (C + 1) := by
        rw [← Real.sqrt_sq hb.le]
        exact (Real.sqrt_lt_sqrt_iff (by positivity : 0 ≤ dist r s)).2 hδ
      have hle := value_dist_le_of_velocity_l2_bound γ hC (hS γ hγ) r.2 s.2
      have hsr : Real.sqrt |(s : ℝ) - r| = Real.sqrt (dist r s) := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
      rw [hsr] at hle
      have hfr : (f : P.Time → E) r = γ.value r := by rw [← hfγ]; rfl
      have hfs : (f : P.Time → E) s = γ.value s := by rw [← hfγ]; rfl
      rw [hfr, hfs]
      rcases eq_or_lt_of_le hC with hC0 | hCpos
      · rw [← hC0, mul_zero] at hle
        exact lt_of_le_of_lt hle hε
      · calc dist (γ.value r) (γ.value s)
            ≤ Real.sqrt (dist r s) * C := hle
          _ < (ε / (C + 1)) * C := mul_lt_mul_of_pos_right hsqrt_lt hCpos
          _ ≤ ε := by
              rw [div_mul_eq_mul_div]
              exact (div_le_iff₀ hCp).2 (by linarith)
    exact hunif.equicontinuous

end OptimalControl.BoundedState
