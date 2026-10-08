/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.LinearGrowthControlExistence
public import DynamicalSystems.Mathlib.MeasureTheory.MeasurableArgmin
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Ordinary optimal controls under convex velocity–cost sets

This file formalizes the purification step of Berkovitz & Medhin, *Nonlinear
Optimal Control Theory*, Theorem 4.4.2: a relaxed minimiser can be converted
into an ordinary minimiser whenever the velocity–cost epigraph `Q⁺(t,x)` is
convex, even if the control set itself is not convex.

The relaxed minimiser is the one produced by the bounded/linear-growth
existence theory (BM Theorem 4.3.5); it is not re-proved here. Its occupation
average `t ↦ (∫ f dμ_t, ∫ f⁰ dμ_t)` lies in `Q⁺(t,x(t))` by convexity and
closedness of the epigraph, and the measurable selection lemma for a
Carathéodory integrand (the Filippov step, BM Corollary 3.4.3) returns a
measurable ordinary control realizing that average together with the running
cost bound. The resulting ordinary trajectory and cost are then compared with
the relaxed optimum.

The control set is an arbitrary nonempty compact metric space; no vector-space
or convexity structure is imposed on it.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction Topology

namespace OptimalControl

section VelocityCost

variable {T U E : Type*} [MeasurableSpace T]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [CompactSpace U]

omit [MeasurableSpace T] [MeasurableSpace U] [BorelSpace U] in
/-- The velocity–cost epigraph `Q⁺(t,x)` of Berkovitz & Medhin: the pairs
`(y, y⁰)` for which some control realizes the velocity `y` and has running
cost rate at most `y⁰`. The inequality direction encodes the epigraph in the
cost coordinate. -/
def velocityCostSet (f : T → E → U → E) (c : T → E → U → ℝ) (t : T) (x : E) :
    Set (E × ℝ) :=
  {p | ∃ u : U, f t x u = p.1 ∧ c t x u ≤ p.2}

omit [MeasurableSpace T] [MeasurableSpace U] [BorelSpace U] in
theorem isClosed_velocityCostSet [TopologicalSpace E] [T2Space E] (f : T → E → U → E)
    (c : T → E → U → ℝ) (t : T) (x : E)
    (hf : Continuous (fun u : U => f t x u)) (hc : Continuous (fun u : U => c t x u)) :
    IsClosed (velocityCostSet f c t x) := by
  let D : Set ((E × ℝ) × U) := {p | f t x p.2 = p.1.1 ∧ c t x p.2 ≤ p.1.2}
  have hD : IsClosed D := by
    have h1 : IsClosed {p : (E × ℝ) × U | f t x p.2 = p.1.1} :=
      isClosed_eq (hf.comp continuous_snd) continuous_fst.fst
    have h2 : IsClosed {p : (E × ℝ) × U | c t x p.2 ≤ p.1.2} :=
      isClosed_le (hc.comp continuous_snd) continuous_fst.snd
    exact h1.inter h2
  have himg : Prod.fst '' D = velocityCostSet f c t x := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq.1, hq.2⟩
    · rintro ⟨u, hvel, hcost⟩
      exact ⟨(p, u), ⟨hvel, hcost⟩, rfl⟩
  rw [← himg]
  exact isClosedMap_fst_of_compactSpace D hD

end VelocityCost

section Purification

variable {T U E : Type*} [MeasurableSpace T]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [CompactSpace U] [StandardBorelSpace U]
  [Nonempty U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ν : ProbabilityMeasure T}

/-- The occupation average of the velocity–cost pair over the conditional
kernel of a relaxed control. Its first coordinate is the averaged velocity and
its second coordinate the averaged running-cost rate. -/
noncomputable def integratedVelocityCost (f : T → E → U → E) (c : T → E → U → ℝ)
    (x : T → E) (ρ : RelaxedControl T U ν) (t : T) : E × ℝ :=
  ∫ u, (f t (x t) u, c t (x t) u) ∂ρ.kernel t

omit [MeasurableSpace E] [BorelSpace E] in
theorem integratedVelocityCost_fst (f : T → E → U → E) (c : T → E → U → ℝ)
    (x : T → E) (ρ : RelaxedControl T U ν) (t : T)
    (hf : Continuous (fun u : U => f t (x t) u)) (hc : Continuous (fun u : U => c t (x t) u)) :
    (integratedVelocityCost f c x ρ t).1 = ∫ u, f t (x t) u ∂ρ.kernel t := by
  have hcont : Continuous (fun u : U => (f t (x t) u, c t (x t) u)) := hf.prodMk hc
  have hint : Integrable (fun u : U => (f t (x t) u, c t (x t) u)) (ρ.kernel t) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := (ContinuousLinearMap.fst ℝ E ℝ).integral_comp_comm hint
  simpa [integratedVelocityCost] using h.symm

omit [MeasurableSpace E] [BorelSpace E] in
theorem integratedVelocityCost_snd (f : T → E → U → E) (c : T → E → U → ℝ)
    (x : T → E) (ρ : RelaxedControl T U ν) (t : T)
    (hf : Continuous (fun u : U => f t (x t) u)) (hc : Continuous (fun u : U => c t (x t) u)) :
    (integratedVelocityCost f c x ρ t).2 = ∫ u, c t (x t) u ∂ρ.kernel t := by
  have hcont : Continuous (fun u : U => (f t (x t) u, c t (x t) u)) := hf.prodMk hc
  have hint : Integrable (fun u : U => (f t (x t) u, c t (x t) u)) (ρ.kernel t) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := (ContinuousLinearMap.snd ℝ E ℝ).integral_comp_comm hint
  simpa [integratedVelocityCost] using h.symm

omit [MeasurableSpace E] [BorelSpace E] in
/-- The occupation average belongs to the velocity–cost epigraph: it is an
integral of points of `Q⁺` against the probability measure `ρ.kernel t`, so
convexity and closedness put it back in `Q⁺`. -/
theorem integratedVelocityCost_mem (f : T → E → U → E) (c : T → E → U → ℝ)
    (x : T → E) (ρ : RelaxedControl T U ν) (t : T)
    (hf : Continuous (fun u : U => f t (x t) u)) (hc : Continuous (fun u : U => c t (x t) u))
    (hconv : Convex ℝ (velocityCostSet f c t (x t))) :
    integratedVelocityCost f c x ρ t ∈ velocityCostSet f c t (x t) := by
  have hcont : Continuous (fun u : U => (f t (x t) u, c t (x t) u)) := hf.prodMk hc
  have hint : Integrable (fun u : U => (f t (x t) u, c t (x t) u)) (ρ.kernel t) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine hconv.integral_mem
    (isClosed_velocityCostSet f c t (x t) hf hc) (Eventually.of_forall ?_) hint
  intro u
  exact ⟨u, rfl, le_rfl⟩

/-- **Measurable purification** (the Filippov step, BM Corollary 3.4.3): if the
velocity–cost epigraph is convex at every time, then a relaxed control admits
a measurable ordinary control whose velocity–cost pair dominates the
occupation average pointwise. In particular, the ordinary control realizes the
averaged velocity and does not exceed the averaged running-cost rate. -/
theorem exists_measurable_purifyingControl (f : T → E → U → E) (c : T → E → U → ℝ)
    (x : T → E) (ρ : RelaxedControl T U ν)
    (hf_cont : ∀ t, Continuous (fun u : U => f t (x t) u))
    (hc_cont : ∀ t, Continuous (fun u : U => c t (x t) u))
    (hf_meas : StronglyMeasurable (fun p : T × U => f p.1 (x p.1) p.2))
    (hc_meas : StronglyMeasurable (fun p : T × U => c p.1 (x p.1) p.2))
    (hconv : ∀ t, Convex ℝ (velocityCostSet f c t (x t))) :
    ∃ u : T → U, Measurable u ∧
      (∀ t, f t (x t) (u t) = (integratedVelocityCost f c x ρ t).1) ∧
      (∀ t, c t (x t) (u t) ≤ (integratedVelocityCost f c x ρ t).2) := by
  let q : T → E × ℝ := integratedVelocityCost f c x ρ
  have hq1_meas : Measurable (fun t => (q t).1) := by
    have h := (RelaxedControl.stronglyMeasurable_average (E := E) ρ hf_meas).measurable
    convert h using 1
    ext t
    exact integratedVelocityCost_fst f c x ρ t (hf_cont t) (hc_cont t)
  have hq2_meas : Measurable (fun t => (q t).2) := by
    have h := (RelaxedControl.stronglyMeasurable_average (E := ℝ) ρ hc_meas).measurable
    convert h using 1
    ext t
    exact integratedVelocityCost_snd f c x ρ t (hf_cont t) (hc_cont t)
  let φ : T → U → ℝ := fun t u =>
    ‖f t (x t) u - (q t).1‖ ^ 2 + max 0 (c t (x t) u - (q t).2)
  have hφ_meas : ∀ u : U, Measurable (fun t => φ t u) := by
    intro u
    have h1 : Measurable (fun t : T => f t (x t) u) :=
      hf_meas.measurable.comp (measurable_id.prodMk measurable_const)
    have h2 : Measurable (fun t : T => c t (x t) u) :=
      hc_meas.measurable.comp (measurable_id.prodMk measurable_const)
    exact ((h1.sub hq1_meas).norm.pow_const 2).add
      ((measurable_const : Measurable (fun _ : T => (0 : ℝ))).max (h2.sub hq2_meas))
  have hφ_cont : ∀ t : T, Continuous (φ t) := by
    intro t
    exact (((hf_cont t).sub continuous_const).norm.pow 2).add
      (continuous_const.max ((hc_cont t).sub continuous_const))
  obtain ⟨u, hu_meas, hu_min⟩ :=
    DynamicalSystems.MeasurableArgmin.exists_measurable_isMinOn hφ_meas hφ_cont
  have hzero : ∀ t, φ t (u t) = 0 := by
    intro t
    obtain ⟨w, hwvel, hwcost⟩ :=
      integratedVelocityCost_mem f c x ρ t (hf_cont t) (hc_cont t) (hconv t)
    have hw : φ t w = 0 := by
      have h1 : f t (x t) w - (q t).1 = 0 := sub_eq_zero.mpr hwvel
      have h2 : max 0 (c t (x t) w - (q t).2) = 0 :=
        max_eq_left (sub_nonpos.mpr hwcost)
      simp [φ, h1, h2]
    have hle : φ t (u t) ≤ 0 := (hu_min t w).trans_eq hw
    have hnonneg : 0 ≤ φ t (u t) :=
      add_nonneg (pow_nonneg (norm_nonneg _) 2) (le_max_left _ _)
    linarith
  have hcoord : ∀ t, (f t (x t) (u t) = (q t).1) ∧ (c t (x t) (u t) ≤ (q t).2) := by
    intro t
    have hsum : φ t (u t) = ‖f t (x t) (u t) - (q t).1‖ ^ 2 +
        max 0 (c t (x t) (u t) - (q t).2) := rfl
    have hA : ‖f t (x t) (u t) - (q t).1‖ ^ 2 = 0 := by
      have h1 : 0 ≤ ‖f t (x t) (u t) - (q t).1‖ ^ 2 := pow_nonneg (norm_nonneg _) 2
      have h2 : 0 ≤ max 0 (c t (x t) (u t) - (q t).2) := le_max_left _ _
      linarith [hzero t, hsum]
    have hvel : f t (x t) (u t) = (q t).1 := by
      have hnorm : ‖f t (x t) (u t) - (q t).1‖ = 0 := sq_eq_zero_iff.mp hA
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    have hcost : c t (x t) (u t) ≤ (q t).2 := by
      have hB : max 0 (c t (x t) (u t) - (q t).2) = 0 := by
        have h1 : 0 ≤ ‖f t (x t) (u t) - (q t).1‖ ^ 2 := pow_nonneg (norm_nonneg _) 2
        linarith [hzero t, hsum]
      have : c t (x t) (u t) - (q t).2 ≤ 0 := by
        have := le_max_right (0 : ℝ) (c t (x t) (u t) - (q t).2)
        linarith
      linarith
    exact ⟨hvel, hcost⟩
  exact ⟨u, hu_meas, fun t => (hcoord t).1, fun t => (hcoord t).2⟩

end Purification

section OrdinaryVolterra

variable {T : ℝ} {U E : Type*}
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [CompactSpace U] [StandardBorelSpace U]
  [Nonempty U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The purified ordinary control satisfies the same actual Volterra equation
as the relaxed trajectory, because its velocity equals the occupation average
at every time. -/
theorem IsRelaxedTrajectory.ordinaryVolterra_of_purifyingControl {hT : 0 < T}
    {f : ControlTime T → E → U → E} {c : ControlTime T → E → U → ℝ}
    {x₀ : E} {x : ControlTime T →ᵇ E}
    {ρ : RelaxedControl (ControlTime T) U (horizonProbability T hT)} {u : ControlTime T → U}
    (hf_cont : ∀ t, Continuous (fun w : U => f t (x t) w))
    (hc_cont : ∀ t, Continuous (fun w : U => c t (x t) w))
    (hx : IsRelaxedTrajectory hT f x₀ x ρ)
    (hfi : Integrable (fun z : ControlTime T × U => f z.1 (x z.1) z.2) ρ.measure)
    (hvel : ∀ t, f t (x t) (u t) = (integratedVelocityCost f c x ρ t).1) :
    ∀ t, x t = x₀ + T • ∫ s in Ioc (timeZero T hT.le) t,
      f s (x s) (u s) ∂horizonProbability T hT := by
  intro t
  have hInt : (∫ z in Ioc (timeZero T hT.le) t ×ˢ univ,
        f z.1 (x z.1) z.2 ∂ρ.measure) =
      ∫ s in Ioc (timeZero T hT.le) t, f s (x s) (u s) ∂horizonProbability T hT := by
    rw [← RelaxedControl.setIntegral_kernel ρ measurableSet_Ioc hfi.integrableOn]
    apply integral_congr_ae
    refine Eventually.of_forall fun s => ?_
    dsimp only
    rw [hvel s]
    exact (integratedVelocityCost_fst f c x ρ s (hf_cont s) (hc_cont s)).symm
  rw [hx t, hInt]

end OrdinaryVolterra

namespace BoundedContinuousProblem

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [CompactSpace U]

/-- **Berkovitz & Medhin Theorem 4.4.2** for bounded continuous data: if the
velocity–cost epigraph `Q⁺(t,x)` is convex, then an optimal ordinary pair
exists. The ordinary optimum is attained by de-relaxing the relaxed minimiser
of BM Theorem 4.3.5 with a measurable selection. -/
theorem exists_ordinary_minimizer_of_convex_velocityCost (P : BoundedContinuousProblem E U)
    (hconv : ∀ t x, Convex ℝ (velocityCostSet P.dynamics P.runningCost t x))
    (hfeasible : ∃ x u, P.OrdinaryAdmissible x u) :
    ∃ x u, P.OrdinaryAdmissible x u ∧
      ∀ y v, P.OrdinaryAdmissible y v → P.ordinaryCost x u ≤ P.ordinaryCost y v := by
  obtain ⟨x₀, u₀, h₀⟩ := hfeasible
  have : Nonempty U := ⟨u₀ (timeZero P.horizon P.horizon_pos.le)⟩
  obtain ⟨x, ρ, hx, hmin⟩ := P.exists_relaxed_minimizer
    ⟨x₀, RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ h₀.1,
      h₀.to_relaxed⟩
  have hf_cont : ∀ t : P.Time, Continuous (fun u : U => P.dynamics t (x t) u) := fun t =>
    P.dynamics_continuous.comp
      ((continuous_const : Continuous (fun _ : U => (t, x t))).prodMk continuous_id)
  have hc_cont : ∀ t : P.Time, Continuous (fun u : U => P.runningCost t (x t) u) := fun t =>
    P.runningCost_continuous.comp
      ((continuous_const : Continuous (fun _ : U => (t, x t))).prodMk continuous_id)
  have hf_meas : StronglyMeasurable (fun p : P.Time × U => P.dynamics p.1 (x p.1) p.2) :=
    (P.dynamics_continuous.comp
      ((continuous_fst.prodMk (x.continuous.comp continuous_fst)).prodMk
        continuous_snd)).stronglyMeasurable
  have hc_meas : StronglyMeasurable (fun p : P.Time × U => P.runningCost p.1 (x p.1) p.2) :=
    (P.runningCost_continuous.comp
      ((continuous_fst.prodMk (x.continuous.comp continuous_fst)).prodMk
        continuous_snd)).stronglyMeasurable
  obtain ⟨u, hu_meas, hvel, hcost⟩ :=
    exists_measurable_purifyingControl P.dynamics P.runningCost x ρ
      hf_cont hc_cont hf_meas hc_meas (fun t => hconv t (x t))
  have hfi : Integrable (fun z : P.Time × U => P.dynamics z.1 (x z.1) z.2) ρ.measure :=
    integrable_trajectoryField P.horizon_pos P.dynamics P.dynamics_continuous x ρ
  have hx_traj := hx.1.ordinaryVolterra_of_purifyingControl hf_cont hc_cont hfi hvel
  have hrc : Integrable (fun z : P.Time × U => P.runningCost z.1 (x z.1) z.2) ρ.measure :=
    (P.runningCost_continuous.comp
      ((continuous_fst.prodMk (x.continuous.comp continuous_fst)).prodMk
        continuous_snd)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgr := P.integrable_ordinary_composition x u hu_meas P.runningCost P.runningCost_continuous
  have hgo : Integrable (fun t : P.Time => ∫ u, P.runningCost t (x t) u ∂ρ.kernel t)
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
    have h := hrc.integral_condKernel
    rwa [ρ.fst_measure] at h
  have hcost_le : P.ordinaryCost x u ≤ P.relaxedCost x ρ := by
    unfold ordinaryCost relaxedCost
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ P.horizon_pos.le)
    rw [← RelaxedControl.integral_kernel ρ hrc]
    refine integral_mono hgr hgo ?_
    intro t
    dsimp only
    rw [← integratedVelocityCost_snd P.dynamics P.runningCost x ρ t (hf_cont t) (hc_cont t)]
    exact hcost t
  refine ⟨x, u, ⟨hu_meas, hx_traj, hx.2⟩, ?_⟩
  intro y v hv
  calc
    P.ordinaryCost x u ≤ P.relaxedCost x ρ := hcost_le
    _ ≤ P.relaxedCost y
          (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) v hv.1) :=
        hmin y _ hv.to_relaxed
    _ = P.ordinaryCost y v := P.relaxedCost_ofControl y v hv.1

end BoundedContinuousProblem

namespace LinearGrowthProblem

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [CompactSpace U]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The ordinary graph embedding preserves the Bolza objective exactly for the
linear-growth problem. -/
theorem relaxedCost_ofControl (P : LinearGrowthProblem E U) (x : P.Path) (u : P.Time → U)
    (hu : Measurable u) :
    P.relaxedCost x (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u hu) =
      P.ordinaryCost x u := by
  unfold relaxedCost ordinaryCost
  rw [RelaxedControl.integral_ofControl]
  exact (P.runningCost_continuous.comp
    ((continuous_fst.prodMk (x.continuous.comp continuous_fst)).prodMk
      continuous_snd)).aestronglyMeasurable

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Continuous field/cost compositions with a measurable control are
integrable for the linear-growth problem. -/
theorem integrable_ordinary_composition {F : Type*} [NormedAddCommGroup F]
    (P : LinearGrowthProblem E U) (x : P.Path) (u : P.Time → U) (hu : Measurable u)
    (g : P.Time → E → U → F)
    (hg : Continuous (fun z : (P.Time × E) × U => g z.1.1 z.1.2 z.2)) :
    Integrable (fun t => g t (x t) (u t))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hc : Continuous (fun z : P.Time × U => g z.1 (x z.1) z.2) :=
    hg.comp ((continuous_fst.prodMk (x.continuous.comp continuous_fst)).prodMk continuous_snd)
  have hi : Integrable (fun z : P.Time × U => g z.1 (x z.1) z.2)
      (Measure.map (fun t => (t, u t)) (horizonProbability P.horizon P.horizon_pos).toMeasure) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact hi.comp_measurable (measurable_id.prodMk hu)

/-- De-relaxation of an admissible relaxed pair, with the cost comparison:
the purified ordinary control realizes the same trajectory and does not
increase the relaxed objective. This packages the Filippov selection step
(BM Corollary 3.4.3) for reuse. -/
theorem exists_ordinaryAdmissible_cost_le (P : LinearGrowthProblem E U) [Nonempty U]
    (hconv : ∀ t x, Convex ℝ (velocityCostSet P.dynamics P.runningCost t x))
    {x : P.Path} {ρ : P.Relaxed} (hx : P.RelaxedAdmissible x ρ) :
    ∃ u : P.Time → U, P.OrdinaryAdmissible x u ∧ P.ordinaryCost x u ≤ P.relaxedCost x ρ := by
  have hf_cont : ∀ t : P.Time, Continuous (fun u : U => P.dynamics t (x t) u) := fun t =>
    P.dynamics_continuous.comp
      ((continuous_const : Continuous (fun _ : U => (t, x t))).prodMk continuous_id)
  have hc_cont : ∀ t : P.Time, Continuous (fun u : U => P.runningCost t (x t) u) := fun t =>
    P.runningCost_continuous.comp
      ((continuous_const : Continuous (fun _ : U => (t, x t))).prodMk continuous_id)
  have hf_meas : StronglyMeasurable (fun p : P.Time × U => P.dynamics p.1 (x p.1) p.2) :=
    (P.dynamics_continuous.comp
      ((continuous_fst.prodMk (x.continuous.comp continuous_fst)).prodMk
        continuous_snd)).stronglyMeasurable
  have hc_meas : StronglyMeasurable (fun p : P.Time × U => P.runningCost p.1 (x p.1) p.2) :=
    (P.runningCost_continuous.comp
      ((continuous_fst.prodMk (x.continuous.comp continuous_fst)).prodMk
        continuous_snd)).stronglyMeasurable
  obtain ⟨u, hu_meas, hvel, hcost⟩ :=
    exists_measurable_purifyingControl P.dynamics P.runningCost x ρ
      hf_cont hc_cont hf_meas hc_meas (fun t => hconv t (x t))
  have hfi : Integrable (fun z : P.Time × U => P.dynamics z.1 (x z.1) z.2) ρ.measure :=
    integrable_trajectoryField P.horizon_pos P.dynamics P.dynamics_continuous x ρ
  have hx_traj := hx.1.ordinaryVolterra_of_purifyingControl hf_cont hc_cont hfi hvel
  have hrc : Integrable (fun z : P.Time × U => P.runningCost z.1 (x z.1) z.2) ρ.measure :=
    (P.runningCost_continuous.comp
      ((continuous_fst.prodMk (x.continuous.comp continuous_fst)).prodMk
        continuous_snd)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgr := P.integrable_ordinary_composition x u hu_meas P.runningCost P.runningCost_continuous
  have hgo : Integrable (fun t : P.Time => ∫ u, P.runningCost t (x t) u ∂ρ.kernel t)
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
    have h := hrc.integral_condKernel
    rwa [ρ.fst_measure] at h
  have hcost_le : P.ordinaryCost x u ≤ P.relaxedCost x ρ := by
    unfold ordinaryCost relaxedCost
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ P.horizon_pos.le)
    rw [← RelaxedControl.integral_kernel ρ hrc]
    refine integral_mono hgr hgo ?_
    intro t
    dsimp only
    rw [← integratedVelocityCost_snd P.dynamics P.runningCost x ρ t (hf_cont t) (hc_cont t)]
    exact hcost t
  exact ⟨u, ⟨hu_meas, hx_traj, hx.2⟩, hcost_le⟩

/-- **Berkovitz & Medhin Theorem 4.4.2** for linearly growing dynamics on an
arbitrary finite horizon: convexity of the velocity–cost epigraph `Q⁺(t,x)`
yields an optimal ordinary pair. The relaxed minimiser is the global one of BM
Theorem 4.3.5 (`exists_relaxed_minimizer_global`); it is purified by the
Filippov selection step without imposing any tube on the competitors. -/
theorem exists_ordinaryMinimizer_of_convex_velocity (P : LinearGrowthProblem E U)
    (hconv : ∀ t x, Convex ℝ (velocityCostSet P.dynamics P.runningCost t x))
    (hfeasible : ∃ x u, P.OrdinaryAdmissible x u) :
    ∃ x u, P.OrdinaryAdmissible x u ∧
      ∀ y v, P.OrdinaryAdmissible y v → P.ordinaryCost x u ≤ P.ordinaryCost y v := by
  obtain ⟨x₀, u₀, h₀⟩ := hfeasible
  have : Nonempty U := ⟨u₀ (timeZero P.horizon P.horizon_pos.le)⟩
  obtain ⟨x, ρ, hx, hmin⟩ := P.exists_relaxed_minimizer_global
    ⟨x₀, RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ h₀.1,
      h₀.to_relaxed⟩
  obtain ⟨u, hu, hcost_le⟩ := P.exists_ordinaryAdmissible_cost_le hconv hx
  refine ⟨x, u, hu, ?_⟩
  intro y v hv
  calc
    P.ordinaryCost x u ≤ P.relaxedCost x ρ := hcost_le
    _ ≤ P.relaxedCost y
          (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) v hv.1) :=
        hmin y _ hv.to_relaxed
    _ = P.ordinaryCost y v := P.relaxedCost_ofControl y v hv.1

/-- **Convexity-based relaxation identity** (the form of BM Theorem 4.4.6
guaranteed by convexity of `Q⁺`): the ordinary minimiser's graph measure is
also a relaxed minimiser, so the ordinary and relaxed optimal values coincide.
BM's own Theorem 4.4.6 replaces the convexity hypothesis by local
controllability at the terminal set; that hypothesis is not formalized here. -/
theorem ordinary_min_eq_relaxed_min_of_convex_velocity (P : LinearGrowthProblem E U)
    (hconv : ∀ t x, Convex ℝ (velocityCostSet P.dynamics P.runningCost t x))
    (hfeasible : ∃ x u, P.OrdinaryAdmissible x u) :
    ∃ x u, ∃ hu : P.OrdinaryAdmissible x u,
      (∀ y v, P.OrdinaryAdmissible y v → P.ordinaryCost x u ≤ P.ordinaryCost y v) ∧
      (∀ y σ, P.RelaxedAdmissible y σ →
        P.relaxedCost x
            (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u hu.1) ≤
          P.relaxedCost y σ) := by
  obtain ⟨x₀, u₀, h₀⟩ := hfeasible
  have : Nonempty U := ⟨u₀ (timeZero P.horizon P.horizon_pos.le)⟩
  obtain ⟨x, ρ, hx, hmin⟩ := P.exists_relaxed_minimizer_global
    ⟨x₀, RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ h₀.1,
      h₀.to_relaxed⟩
  obtain ⟨u, hu, hcost_le⟩ := P.exists_ordinaryAdmissible_cost_le hconv hx
  have hmin_ord : ∀ y v, P.OrdinaryAdmissible y v → P.ordinaryCost x u ≤ P.ordinaryCost y v :=
    fun y v hv ↦ by
      calc
        P.ordinaryCost x u ≤ P.relaxedCost x ρ := hcost_le
        _ ≤ P.relaxedCost y
              (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) v hv.1) :=
            hmin y _ hv.to_relaxed
        _ = P.ordinaryCost y v := P.relaxedCost_ofControl y v hv.1
  refine ⟨x, u, hu, hmin_ord, ?_⟩
  intro y σ hσ
  rw [P.relaxedCost_ofControl x u hu.1]
  obtain ⟨w, hw, hwcost⟩ := P.exists_ordinaryAdmissible_cost_le hconv hσ
  exact (hmin_ord y w hw).trans hwcost

end LinearGrowthProblem

end OptimalControl
