/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.WeakEulerLagrangeMinimum

/-!
# The original Euler–Lagrange endpoint predicate needs more than C1 data

The globally C1 curve equal to `t²` before zero and zero afterwards minimizes
the kinetic action on `[0,1]`. Its momentum has left derivative two and right
derivative zero at the initial endpoint. Thus finite-horizon optimality cannot
force the two-sided endpoint derivative in the existing `eulerLagrange`.
-/

@[expose] public section

namespace WeakEulerLagrange.Counterexamples.TwoSidedEndpointDerivative

open Set MeasureTheory
open scoped Interval Topology

/-- A C1 curve whose acceleration jumps at the initial endpoint. -/
noncomputable def curve (t : ℝ) : ℝ := if t ≤ 0 then t ^ 2 else 0

/-- The actual continuous velocity of `curve`. -/
noncomputable def velocity (t : ℝ) : ℝ := if t ≤ 0 then 2 * t else 0

/-- The polynomial branch derivative used in the gluing proof. -/
theorem hasDerivAt_square (t : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
  convert (hasDerivAt_id t).pow 2 using 1 <;> first | rfl | norm_num

/-- The two branch velocities match at zero, giving a genuine global derivative. -/
theorem curve_hasDerivAt (t : ℝ) : HasDerivAt curve (velocity t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h := (hasDerivAt_square t).congr_of_eventuallyEq (f₁ := curve) (by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp only [curve, ite_eq_left (le_of_lt hs)])
    simpa only [velocity, ite_eq_left ht.le] using h
  · have hl : HasDerivWithinAt curve 0 (Iic 0) 0 := by
      have hd : HasDerivWithinAt (fun s : ℝ => s ^ 2) 0 (Iic 0) 0 := by
        simpa using (hasDerivAt_square 0).hasDerivWithinAt
      exact hd.congr_of_mem (fun s hs => by simp only [curve, ite_eq_left (show s ≤ 0 from hs)])
        (mem_Iic.mpr le_rfl)
    have hr : HasDerivWithinAt curve 0 (Ici 0) 0 := by
      apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr_of_mem
        _ (mem_Ici.mpr le_rfl)
      intro s hs
      by_cases hs₀ : s ≤ 0
      · have hs_eq : s = 0 := le_antisymm hs₀ hs
        subst s
        simp [curve]
      · simp only [curve, ite_eq_right hs₀]
    have h := hl.union hr
    rw [Iic_union_Ici] at h
    simpa [velocity] using h.hasDerivAt (by simp)
  · have h := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (f₁ := curve) (by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp only [curve, ite_eq_right (not_le.mpr hs)])
    simpa only [velocity, ite_eq_right (not_le.mpr ht)] using h

/-- The derivative is the explicitly glued continuous velocity. -/
theorem deriv_curve : deriv curve = velocity := funext (fun t => (curve_hasDerivAt t).deriv)

/-- Global continuous differentiability includes the initial endpoint. -/
theorem curve_contDiff : ContDiff ℝ 1 curve := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (curve_hasDerivAt t).differentiableAt, ?_⟩
  rw [deriv_curve]
  apply Continuous.if_le (continuous_const.mul continuous_id) continuous_const
    continuous_id continuous_const
  intro t ht
  simp [show t = 0 from ht]

/-- Kinetic energy is jointly smooth in time, state, and velocity. -/
noncomputable def kinetic (_t _x v : ℝ) : ℝ := v ^ 2 / 2

/-- The running Lagrangian has stronger regularity than required by the weak theorem. -/
theorem kinetic_contDiff : ContDiff ℝ 2 (uncurryLagrangian kinetic) := by
  change ContDiff ℝ 2 (fun q : ℝ × ℝ × ℝ => q.2.2 ^ 2 / 2)
  fun_prop

/-- The velocity vanishes throughout the horizon, including its initial point. -/
theorem velocity_eq_zero_of_nonneg {t : ℝ} (ht : 0 ≤ t) : velocity t = 0 := by
  by_cases ht₀ : t ≤ 0
  · have ht_eq : t = 0 := le_antisymm ht₀ ht
    simp [velocity, ht_eq]
  · simp [velocity, ht₀]

/-- The velocity derivative of the kinetic Lagrangian is the velocity itself. -/
theorem kinetic_hasDerivAt (v : ℝ) : HasDerivAt (fun w : ℝ => w ^ 2 / 2) v v := by
  convert (hasDerivAt_square v).div_const 2 using 1
  ring

/-- Applying the actual momentum to a scalar gives multiplication by the velocity. -/
theorem momentum_apply (t e : ℝ) :
    (fderiv ℝ (fun v : ℝ => kinetic t (curve t) v) (deriv curve t)) e =
      velocity t * e := by
  rw [fderiv_eq_deriv_mul]
  rw [show deriv (fun v : ℝ => kinetic t (curve t) v) (deriv curve t) = deriv curve t
    from (kinetic_hasDerivAt (deriv curve t)).deriv]
  rw [deriv_curve]

/-- The state covector is zero since the kinetic Lagrangian is state independent. -/
theorem stateCovector_eq_zero (t : ℝ) :
    fderiv ℝ (fun y : ℝ => kinetic t y (deriv curve t)) (curve t) = 0 := by
  exact fderiv_const_apply _

/-- No two-sided zero derivative exists for the momentum at the initial endpoint. -/
theorem not_velocity_hasDerivAt_zero : ¬ HasDerivAt velocity 0 0 := by
  intro h
  have hl : HasDerivWithinAt velocity 2 (Iic 0) 0 := by
    have hd : HasDerivWithinAt (fun t : ℝ => 2 * t) 2 (Iic 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).hasDerivWithinAt
    exact hd.congr_of_mem (fun t ht => by
      simp only [velocity, ite_eq_left (show t ≤ 0 from ht)]) (mem_Iic.mpr le_rfl)
  have heq := UniqueDiffWithinAt.eq_deriv (Iic 0) (uniqueDiffWithinAt_Iic 0)
    hl h.hasDerivWithinAt
  norm_num at heq

/-- Finite-horizon stationarity does not imply the original two-sided endpoint predicate. -/
theorem not_eulerLagrange : ¬ eulerLagrange kinetic 1 curve := by
  intro h
  have hd := h 0 (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  have heval := hd.clm_apply (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  have heq : (fun s : ℝ =>
      (fderiv ℝ (fun v : ℝ => kinetic s (curve s) v) (deriv curve s)) 1) = velocity := by
    funext s
    simpa using momentum_apply s 1
  rw [heq, stateCovector_eq_zero] at heval
  exact not_velocity_hasDerivAt_zero (by simpa using heval)

/-- The reference has zero kinetic action on the horizon. -/
theorem cvFunctional_curve_eq_zero : cvFunctional kinetic (fun _ => 0) 1 curve = 0 := by
  unfold cvFunctional
  simp only [add_zero]
  have heq : (∫ t in (0 : ℝ)..1, kinetic t (curve t) (deriv curve t)) =
      ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht₀ : 0 ≤ t := (by simpa using ht : t ∈ Icc (0 : ℝ) 1).1
    simp [kinetic, deriv_curve, velocity_eq_zero_of_nonneg ht₀]
  rw [heq]
  simp

/-- The reference is an actual global action minimizer, hence a fixed-endpoint C1 minimizer. -/
theorem curve_isMinOn : IsMinOn (cvFunctional kinetic (fun _ => 0) 1) univ curve := by
  intro y _
  rw [cvFunctional_curve_eq_zero]
  change 0 ≤ (∫ t in (0 : ℝ)..1, (deriv y t) ^ 2 / 2) + 0
  simp only [add_zero]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t _
  exact div_nonneg (sq_nonneg _) (by norm_num)

/-- Even the original all-differentiable first-variation predicate holds in this example. -/
theorem curve_hasVanishingFirstVariation :
    HasVanishingFirstVariation kinetic (fun _ => 0) 1 curve := by
  intro η _ _ _
  unfold firstVariation
  simp only [fderiv_const_apply, zero_apply, add_zero]
  have heq : (∫ t in (0 : ℝ)..1,
      (fderiv ℝ (fun y : ℝ => kinetic t y (deriv curve t)) (curve t)) (η t) +
      (fderiv ℝ (fun v : ℝ => kinetic t (curve t) v) (deriv curve t)) (deriv η t)) =
      ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht₀ : 0 ≤ t := (by simpa using ht : t ∈ Icc (0 : ℝ) 1).1
    dsimp only
    rw [stateCovector_eq_zero, momentum_apply, velocity_eq_zero_of_nonneg ht₀]
    simp
  rw [heq]
  simp

end WeakEulerLagrange.Counterexamples.TwoSidedEndpointDerivative

end
