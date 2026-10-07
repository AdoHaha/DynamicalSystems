/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.StatePenalisedConvergenceData
public import DynamicalSystems.OptimalControl.ContinuousTime.StateMultiplierMassBound

/-!
# The state-constraint data along the tube family

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.4.

For paths `γ_k → γ₀` uniformly with `φ_k' → φ₀'` in `L¹`, the total derivative of the constraint
gradient `d(∇G)/dt = ∇²G(t,γ)(1,γ')` converges in `L¹(0,T)`, and its `L¹` norm is bounded in
terms of `‖γ'‖_{L¹}`.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]

namespace Problem

variable {P : Problem E V W}

/-- `L¹` convergence of `d(∇G)/dt` along paths converging uniformly with `L¹`-convergent
velocities. -/
theorem tendsto_integral_norm_gradientDerivative_sub
    {Gx : ℝ → E → E →L[ℝ] ℝ} {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)}
    (hGx : StateGradientRegularity Gx Gxd)
    (hGdc : ∀ t, Continuous fun q : E × E => Gxd t q.1 (1, q.2))
    {γ : ℕ → VelocityTrajectory P} {γ₀ : VelocityTrajectory P}
    (hγ : ∀ ε > 0, ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) P.horizon,
      dist ((γ k).value t) (γ₀.value t) < ε)
    (hv : Tendsto (fun k => ∫ r in (0 : ℝ)..P.horizon, ‖(γ k).velocity r - γ₀.velocity r‖)
      atTop (nhds 0)) :
    Tendsto (fun k => ∫ r in (0 : ℝ)..P.horizon,
      ‖Gxd r ((γ k).value r) (1, (γ k).velocity r) - Gxd r (γ₀.value r) (1, γ₀.velocity r)‖)
      atTop (nhds 0) := by
  classical
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  obtain ⟨R₀, hR₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P.horizon)).exists_bound_of_continuousOn
    γ₀.continuousOn_value
  obtain ⟨N₀, hN₀⟩ := (hγ 1 one_pos).exists_forall_of_atTop
  set R : ℝ := R₀ + 1 with hR
  have hybd : ∀ n, ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖(γ (n + N₀)).value t‖ ≤ R := by
    intro n t ht
    have h1 := hN₀ (n + N₀) (Nat.le_add_left _ _) t ht
    have h2 := hR₀ t ht
    calc ‖(γ (n + N₀)).value t‖
        = ‖(γ (n + N₀)).value t - γ₀.value t + γ₀.value t‖ := by rw [sub_add_cancel]
      _ ≤ ‖(γ (n + N₀)).value t - γ₀.value t‖ + ‖γ₀.value t‖ := norm_add_le _ _
      _ ≤ R := by
          have : ‖(γ (n + N₀)).value t - γ₀.value t‖ < 1 := by
            simpa [dist_eq_norm] using h1
          linarith
  have hy'bd : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖γ₀.value t‖ ≤ R := fun t ht => by
    have := hR₀ t ht; linarith
  have hptS : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      Tendsto (fun n => (γ (n + N₀)).value t) atTop (nhds (γ₀.value t)) := fun t ht =>
    (Metric.tendsto_nhds.2 fun ε hε => (hγ ε hε).mono fun n hn => hn t ht).comp
      (tendsto_add_atTop_nat N₀)
  have hw1S : Tendsto (fun n => ∫ r in (0 : ℝ)..P.horizon,
      ‖(γ (n + N₀)).velocity r - γ₀.velocity r‖) atTop (nhds 0) :=
    hv.comp (tendsto_add_atTop_nat N₀)
  have hyS : ∀ n, ContinuousOn (γ (n + N₀)).value (Icc 0 P.horizon) := fun n =>
    (γ (n + N₀)).continuousOn_value
  have hwS : ∀ n, IntervalIntegrable (γ (n + N₀)).velocity volume 0 P.horizon := fun n =>
    (γ (n + N₀)).velocity_intervalIntegrable
  obtain ⟨C₁, hC₁, hC₁b⟩ := hGx.bounded R
  have hev : Measurable (fun p : ((ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)) × (ℝ × E) => p.1 p.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  have hmeasG : Measurable fun p : ℝ × E × E => Gxd p.1 p.2.1 (1, p.2.2) :=
    hev.comp ((hGx.measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
        (measurable_const.prodMk (measurable_snd.comp measurable_snd)))
  have hgr : ∀ t (y w : E), ‖y‖ ≤ R → ‖Gxd t y (1, w)‖ ≤ C₁ + C₁ * ‖w‖ := by
    intro t y w hy
    calc ‖Gxd t y (1, w)‖ ≤ ‖Gxd t y‖ * ‖((1 : ℝ), w)‖ := (Gxd t y).le_opNorm _
      _ ≤ C₁ * (1 + ‖w‖) := by
          refine mul_le_mul (hC₁b t y hy) ?_ (norm_nonneg _) hC₁
          rw [Prod.norm_def, norm_one]
          exact max_le (by linarith [norm_nonneg w]) (by linarith)
      _ = C₁ + C₁ * ‖w‖ := by ring
  have := tendsto_integral_norm_sub_nemytskii hT (N := fun t y w => Gxd t y (1, w)) hmeasG
    hGdc hC₁ (a := fun _ => C₁) intervalIntegrable_const hgr hyS γ₀.continuousOn_value hwS
    γ₀.velocity_intervalIntegrable hybd hy'bd hptS hw1S
  exact (tendsto_add_atTop_iff_nat N₀).1 this

/-- Uniform `L¹` bound of `d(∇G)/dt` along the tube. -/
theorem exists_bound_integral_norm_gradientDerivative
    {Gx : ℝ → E → E →L[ℝ] ℝ} {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)}
    (hGx : StateGradientRegularity Gx Gxd) (γ₀ : VelocityTrajectory P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : VelocityTrajectory P) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) ≤ ε ^ 2 →
      dist γ.initial γ₀.initial ≤ ε →
        ∫ r in (0 : ℝ)..P.horizon, ‖Gxd r (γ.value r) (1, γ.velocity r)‖ ≤ C := by
  classical
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  obtain ⟨R₀, hR₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P.horizon)).exists_bound_of_continuousOn
    γ₀.continuousOn_value
  set A₀ : ℝ := ∫ r in (0 : ℝ)..P.horizon, ‖γ₀.velocity r‖ with hA₀
  have hA₀0 : 0 ≤ A₀ :=
    intervalIntegral.integral_nonneg hT fun _ _ => norm_nonneg _
  obtain ⟨C₁, hC₁, hC₁b⟩ := hGx.bounded (R₀ + 1 + Real.sqrt P.horizon)
  refine ⟨C₁ * (P.horizon + A₀ + Real.sqrt P.horizon), by positivity, ?_⟩
  intro γ ε hε0 hε1 hL2 hinit
  have hdmem : MemLp (fun r => γ.velocity r - γ₀.velocity r) 2
      (ACEulerLagrange.timeMeasure P.horizon) :=
    γ.memLp_velocity.sub γ₀.memLp_velocity
  have hdint : IntervalIntegrable (fun r => γ.velocity r - γ₀.velocity r) volume 0 P.horizon :=
    γ.velocity_intervalIntegrable.sub γ₀.velocity_intervalIntegrable
  have hL1 : ∫ r in (0 : ℝ)..P.horizon, ‖γ.velocity r - γ₀.velocity r‖
      ≤ Real.sqrt P.horizon := by
    have := intervalIntegral_norm_le_sqrt_mul hT hdint hdmem.norm.integrable_sq hε0
      (by simpa using hL2)
    simp only [sub_zero] at this
    calc _ ≤ Real.sqrt P.horizon * ε := this
      _ ≤ Real.sqrt P.horizon * 1 := mul_le_mul_of_nonneg_left hε1 (Real.sqrt_nonneg _)
      _ = Real.sqrt P.horizon := mul_one _
  have hval : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖γ.value t‖ ≤ R₀ + 1 + Real.sqrt P.horizon := by
    intro t ht
    have heq : γ.value t - γ₀.value t
        = (γ.initial - γ₀.initial) + ∫ r in (0 : ℝ)..t, (γ.velocity r - γ₀.velocity r) := by
      rw [intervalIntegral.integral_sub
        (γ.velocity_intervalIntegrable.mono_set (by
          rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2))
        (γ₀.velocity_intervalIntegrable.mono_set (by
          rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2))]
      simp only [VelocityTrajectory.value]
      abel
    have hint_t : ‖∫ r in (0 : ℝ)..t, (γ.velocity r - γ₀.velocity r)‖
        ≤ Real.sqrt P.horizon := by
      refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
      refine le_trans ?_ hL1
      rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le hT]
      exact setIntegral_mono_set
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hdint.norm)
        (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall fun x hx => Ioc_subset_Ioc le_rfl ht.2 hx)
    have hi : ‖γ.initial - γ₀.initial‖ ≤ 1 := by
      rw [← dist_eq_norm]; linarith
    have h0 := hR₀ t ht
    calc ‖γ.value t‖ = ‖(γ.value t - γ₀.value t) + γ₀.value t‖ := by rw [sub_add_cancel]
      _ ≤ ‖γ.value t - γ₀.value t‖ + ‖γ₀.value t‖ := norm_add_le _ _
      _ ≤ (‖γ.initial - γ₀.initial‖
            + ‖∫ r in (0 : ℝ)..t, (γ.velocity r - γ₀.velocity r)‖) + ‖γ₀.value t‖ := by
          rw [heq]; gcongr; exact norm_add_le _ _
      _ ≤ R₀ + 1 + Real.sqrt P.horizon := by linarith
  have hGint := (γ.gradientAlongPath_eq_primitive hGx).1.norm
  have hg1 : IntervalIntegrable (fun r => ‖γ₀.velocity r‖) volume 0 P.horizon :=
    γ₀.velocity_intervalIntegrable.norm
  have hg2 : IntervalIntegrable (fun r => ‖γ.velocity r - γ₀.velocity r‖) volume 0 P.horizon :=
    hdint.norm
  calc ∫ r in (0 : ℝ)..P.horizon, ‖Gxd r (γ.value r) (1, γ.velocity r)‖
      ≤ ∫ r in (0 : ℝ)..P.horizon,
          C₁ * (1 + (‖γ₀.velocity r‖ + ‖γ.velocity r - γ₀.velocity r‖)) := by
        refine intervalIntegral.integral_mono_on hT hGint
          ((intervalIntegrable_const.add (hg1.add hg2)).const_mul C₁) fun r hr => ?_
        calc ‖Gxd r (γ.value r) (1, γ.velocity r)‖
            ≤ ‖Gxd r (γ.value r)‖ * ‖((1 : ℝ), γ.velocity r)‖ := (Gxd r (γ.value r)).le_opNorm _
          _ ≤ C₁ * (1 + (‖γ₀.velocity r‖ + ‖γ.velocity r - γ₀.velocity r‖)) := by
            refine mul_le_mul (hC₁b r _ (hval r hr)) ?_ (norm_nonneg _) hC₁
            rw [Prod.norm_def, norm_one]
            have := norm_le_norm_add_norm_sub' (γ.velocity r) (γ₀.velocity r)
            exact max_le (by linarith [norm_nonneg (γ.velocity r)]) (by linarith)
    _ = C₁ * (P.horizon + (A₀ + ∫ r in (0 : ℝ)..P.horizon, ‖γ.velocity r - γ₀.velocity r‖)) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add intervalIntegrable_const (hg1.add hg2),
          intervalIntegral.integral_add hg1 hg2]
        simp [hA₀]
    _ ≤ C₁ * (P.horizon + A₀ + Real.sqrt P.horizon) := by
        rw [← add_assoc]; gcongr

end Problem

end OptimalControl.BoundedState
