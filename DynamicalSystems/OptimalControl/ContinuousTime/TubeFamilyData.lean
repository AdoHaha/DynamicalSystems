/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.KernelAverageConvergence
public import DynamicalSystems.OptimalControl.ContinuousTime.AveragedDataContinuity
public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwiseBoundaryPositivity

/-!
# The data of the `ε_k`-tube family converge to the data of the optimal pair

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.4.

Paths `γ_k` in the tubes `B(ε_k)` around `γ₀`, `ε_k → 0`, converge to `γ₀` uniformly and in
`W^{1,1}`; with the control distance `d_L(ρ_k,ρ₀) → 0` the control-averaged derivative data
`f⁰ₓ(γ_k,ν_k)`, `fₓ(γ_k,ν_k)` converge in `L¹(0,T)` to those of `(γ₀,ν₀)`, and they are uniformly
bounded.  These are the hypotheses of `exists_theorem_11_6_3_conclusions`.

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

variable (P : Problem E V W)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The difference of two carrier velocities is square integrable on the horizon. -/
theorem integrableOn_sq_norm_velocity_sub (γ₀ γ : VelocityTrajectory P) :
    IntegrableOn (fun s => ‖γ.velocity s - γ₀.velocity s‖ ^ 2) (Ioc (0 : ℝ) P.horizon) volume := by
  have hm : ∀ δ : VelocityTrajectory P, MemLp δ.velocity 2 (volume.restrict (Ioc 0 P.horizon)) :=
    fun δ => (memLp_two_iff_integrable_sq_norm
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le P.horizon_pos.le).1
        δ.velocity_intervalIntegrable).aestronglyMeasurable).2 δ.velocity_sq_integrable
  have h := (hm γ).sub (hm γ₀)
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A real interval integral over `[0,T]` of a clamped-time function is `T` times its integral
against the normalized horizon probability. -/
theorem intervalIntegral_projIcc_eq_horizon_mul (h : P.Time → ℝ) :
    ∫ r in (0 : ℝ)..P.horizon, h (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le r) =
      P.horizon * ∫ t, h t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have h1 := integral_horizon_prefix P.horizon_pos h (timeEnd P.horizon P.horizon_pos.le)
  rw [horizonProbability_integral_eq_prefix P.horizon_pos h, ← smul_eq_mul, h1]
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- A velocity trajectory in the tube stays within `ε(1 + √T)` of the reference, uniformly. -/
theorem dist_value_le_of_tube {ε : ℝ} (hε : 0 ≤ ε) (γ₀ γ : VelocityTrajectory P)
    (hv : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) ≤ ε ^ 2)
    (hi : dist γ.initial γ₀.initial ≤ ε) :
    ∀ t ∈ Icc (0 : ℝ) P.horizon, dist (γ.value t) (γ₀.value t) ≤ ε * (1 + Real.sqrt P.horizon) := by
  intro t ht
  have hT := P.horizon_pos
  have hw : IntervalIntegrable (fun s => γ.velocity s - γ₀.velocity s) volume 0 P.horizon :=
    γ.velocity_intervalIntegrable.sub γ₀.velocity_intervalIntegrable
  have hw2 : IntegrableOn (fun s => ‖γ.velocity s - γ₀.velocity s‖ ^ 2) (Ioc (0 : ℝ) P.horizon)
      volume := integrableOn_sq_norm_velocity_sub P γ₀ γ
  have hsub : ∀ {f : ℝ → E}, IntervalIntegrable f volume 0 P.horizon →
      IntervalIntegrable f volume 0 t := fun hf => hf.mono_set (by
        rw [uIcc_of_le ht.1, uIcc_of_le hT.le]
        exact Icc_subset_Icc le_rfl ht.2)
  have heq : γ.value t - γ₀.value t =
      (γ.initial - γ₀.initial) + ∫ s in (0 : ℝ)..t, (γ.velocity s - γ₀.velocity s) := by
    rw [intervalIntegral.integral_sub (hsub γ.velocity_intervalIntegrable)
      (hsub γ₀.velocity_intervalIntegrable)]
    simp only [VelocityTrajectory.value]
    abel
  have hL1 : ∫ s in (0 : ℝ)..t, ‖γ.velocity s - γ₀.velocity s‖ ≤ Real.sqrt (t - 0) * ε :=
    intervalIntegral_norm_le_sqrt_mul ht.1 (hsub hw) (hw2.mono_set (Ioc_subset_Ioc le_rfl ht.2))
      hε ((intervalIntegral_sq_le_horizon (P := P) ht.1 le_rfl ht.2 hw2).trans hv)
  rw [sub_zero] at hL1
  have hsq : Real.sqrt t ≤ Real.sqrt P.horizon := Real.sqrt_le_sqrt ht.2
  rw [dist_eq_norm, heq]
  calc ‖(γ.initial - γ₀.initial) + ∫ s in (0 : ℝ)..t, (γ.velocity s - γ₀.velocity s)‖
      ≤ ‖γ.initial - γ₀.initial‖ + ∫ s in (0 : ℝ)..t, ‖γ.velocity s - γ₀.velocity s‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl
          (intervalIntegral.norm_integral_le_integral_norm ht.1))
    _ ≤ ε + Real.sqrt P.horizon * ε := by
        rw [← dist_eq_norm]
        exact add_le_add hi (hL1.trans (mul_le_mul_of_nonneg_right hsq hε))
    _ = ε * (1 + Real.sqrt P.horizon) := by ring

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The `L¹` distance of the velocities is at most `√T ε`. -/
theorem integral_norm_velocity_sub_le {ε : ℝ} (hε : 0 ≤ ε) (γ₀ γ : VelocityTrajectory P)
    (hv : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) ≤ ε ^ 2) :
    (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖) ≤ Real.sqrt P.horizon * ε := by
  have h := intervalIntegral_norm_le_sqrt_mul P.horizon_pos.le
    (γ.velocity_intervalIntegrable.sub γ₀.velocity_intervalIntegrable)
    (integrableOn_sq_norm_velocity_sub P γ₀ γ) hε hv
  simpa only [sub_zero] using h

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- Uniform bounds of the averaged derivative data on a state ball, independent of the control. -/
theorem exists_bound_averagedDerivatives (D : P.SmoothData) (hD : P.DerivativeContinuity D)
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : P.Relaxed) (t : ℝ) (y : E), ‖y‖ ≤ R →
      ‖P.averagedRunningCovector D ρ t y‖ ≤ C ∧ ‖P.averagedDynamicsDerivative D ρ t y‖ ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := P.exists_bound_dynamicsDerivative D hD R
  obtain ⟨C₂, hC₂0, hC₂⟩ := P.exists_bound_runningDerivative D hD R
  refine ⟨max (P.horizon⁻¹ * C₂) C₁, le_max_of_le_right hC₁0, fun ρ t y hy => ⟨?_, ?_⟩⟩
  · set q : P.Time := Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t
    have hb : ∀ u : P.Control,
        ‖(D.runningDerivative q (y, (u : V))).comp (ContinuousLinearMap.inl ℝ E V)‖ ≤ C₂ :=
      fun u => (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul (hC₂ q y u hy) (ContinuousLinearMap.norm_inl_le_one ℝ E V)
          (by positivity) hC₂0).trans (by rw [mul_one]))
    have hI := P.norm_integral_kernel_le ρ q hb
    refine le_trans ?_ (le_max_left _ _)
    simp only [averagedRunningCovector, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos P.horizon_pos]
    exact mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr P.horizon_pos.le)
  · refine le_trans ?_ (le_max_right _ _)
    exact P.norm_integral_kernel_le ρ _ (fun u => hC₁ _ y u hy)

omit [MeasurableSpace E] [BorelSpace E] in
/-- `L¹` convergence of the averaged cost covector along the tube family. -/
theorem tendsto_integral_norm_averagedRunningCovector_sub (D : P.SmoothData)
    (hD : P.DerivativeContinuity D) {γ : ℕ → VelocityTrajectory P} {γ₀ : VelocityTrajectory P}
    (hγ : Tendsto (fun k => toBoundedPath (γ k)) atTop (nhds (toBoundedPath γ₀)))
    {ρ : ℕ → P.Relaxed} {ρ₀ : P.Relaxed}
    (hρ : Tendsto (fun k => relaxedControlDistance P (ρ k) ρ₀) atTop (nhds 0)) :
    Tendsto (fun k => ∫ r in (0 : ℝ)..P.horizon,
      ‖P.averagedRunningCovector D (ρ k) r ((γ k).value r)
        - P.averagedRunningCovector D ρ₀ r (γ₀.value r)‖) atTop (nhds 0) := by
  have hg : Continuous fun z : (P.Time × E) × V =>
      P.horizon⁻¹ • (D.runningDerivative z.1.1 (z.1.2, z.2)).comp
        (ContinuousLinearMap.inl ℝ E V) := by
    have h0 := hD.continuous_runningDerivative.clm_comp_const (ContinuousLinearMap.inl ℝ E V)
    exact h0.const_smul P.horizon⁻¹
  obtain ⟨-, hlim⟩ := P.tendsto_integral_norm_kernelAverage_sub
    (fun t y v => P.horizon⁻¹ • (D.runningDerivative t (y, v)).comp
      (ContinuousLinearMap.inl ℝ E V)) hg hγ hρ
  have hT := hlim.const_mul P.horizon
  rw [mul_zero] at hT
  refine hT.congr fun k => ?_
  rw [← intervalIntegral_projIcc_eq_horizon_mul]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le P.horizon_pos.le] at hr
  have hq : ((Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le r : P.Time) : ℝ) = r := by
    rw [Set.projIcc_of_mem _ hr]
  simp only [averagedRunningCovector, toBoundedPath_apply, hq, integral_smul]

omit [MeasurableSpace E] [BorelSpace E] in
/-- `L¹` convergence of the averaged dynamics derivative along the tube family. -/
theorem tendsto_integral_norm_averagedDynamicsDerivative_sub (D : P.SmoothData)
    (hD : P.DerivativeContinuity D) {γ : ℕ → VelocityTrajectory P} {γ₀ : VelocityTrajectory P}
    (hγ : Tendsto (fun k => toBoundedPath (γ k)) atTop (nhds (toBoundedPath γ₀)))
    {ρ : ℕ → P.Relaxed} {ρ₀ : P.Relaxed}
    (hρ : Tendsto (fun k => relaxedControlDistance P (ρ k) ρ₀) atTop (nhds 0)) :
    Tendsto (fun k => ∫ r in (0 : ℝ)..P.horizon,
      ‖P.averagedDynamicsDerivative D (ρ k) r ((γ k).value r)
        - P.averagedDynamicsDerivative D ρ₀ r (γ₀.value r)‖) atTop (nhds 0) := by
  obtain ⟨-, hlim⟩ := P.tendsto_integral_norm_kernelAverage_sub
    (fun t y v => D.dynamicsDerivative t y v) hD.continuous_dynamicsDerivative hγ hρ
  have hT := hlim.const_mul P.horizon
  rw [mul_zero] at hT
  refine hT.congr fun k => ?_
  rw [← intervalIntegral_projIcc_eq_horizon_mul]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le P.horizon_pos.le] at hr
  have hq : ((Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le r : P.Time) : ℝ) = r := by
    rw [Set.projIcc_of_mem _ hr]
  simp only [averagedDynamicsDerivative, toBoundedPath_apply, hq]

end Problem

end OptimalControl.BoundedState
