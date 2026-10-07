/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityTrajectories
public import DynamicalSystems.Mathlib.MeasureTheory.WeakL2Compactness
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# ε-optimality on the velocity carrier

This file re-instantiates the penalty functional `F_K` of Berkovitz & Medhin,
*Nonlinear Optimal Control Theory* (CRC 2012), (11.3.6) / §11.6 on the explicit
absolutely-continuous velocity carrier `VelocityTrajectory` introduced in
`VelocityTrajectories.lean`.

The velocity-defect term uses the candidate's own velocity `γ'` (not the old
control-averaged Volterra field), while the running cost and the Volterra
residual are evaluated on the primitive `γ.value`. This is the mechanical
re-instantiation flagged in `R2_REPORT.md` §3.2 before Lemma 11.3.4.

Book citations live only in docstrings; all names are concept names.
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

namespace Problem

/-- The penalty remainder of `F_K` on the velocity carrier: all of (11.3.6)
except the running cost.

The velocity-defect term is the interval `L²` norm of `γ' − γ₀'` of the
candidates' own velocities; the initial-state, control-distance,
endpoint-constraint and Volterra-residual terms are evaluated on the primitive
`γ.value`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6) and §11.6. -/
noncomputable def velocityPenaltyRemainder (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (γ : VelocityTrajectory P) (ρ : P.Relaxed) : ℝ :=
  (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2)
  + dist γ.initial γ₀.initial ^ 2
  + ε * relaxedControlDistance P ρ ρ₀
  + K * ‖P.endpointConstraint (γ.value (timeZero P.horizon P.horizon_pos.le))
      (γ.value (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2
  + K * ∫ t, ‖dynamicsResidual P (toBoundedPath γ) ρ t‖ ^ 2
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure

/-- The penalty functional `F_K` of Berkovitz & Medhin (11.3.6) / §11.6 on the
velocity carrier: the running cost plus `velocityPenaltyRemainder`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6) and §11.6. -/
noncomputable def velocityPenalized (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (γ : VelocityTrajectory P) (ρ : P.Relaxed) : ℝ :=
  P.relaxedCost (toBoundedPath γ) ρ
    + velocityPenaltyRemainder P K ε γ₀ ρ₀ γ ρ

/-- The velocity-carrier penalty decomposes as the relaxed running cost plus the
velocity penalty remainder.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6). -/
theorem velocityPenalized_eq_cost_add_remainder (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (γ : VelocityTrajectory P) (ρ : P.Relaxed) :
    velocityPenalized P K ε γ₀ ρ₀ γ ρ =
      P.relaxedCost (toBoundedPath γ) ρ
        + velocityPenaltyRemainder P K ε γ₀ ρ₀ γ ρ :=
  rfl

/-- The reference velocity trajectory lies in every velocity control tube
around itself. This is the nonemptiness input to the Weierstrass argument of
Lemma 11.3.4 on the velocity carrier.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
theorem self_mem_InVelocityControlTube (P : Problem E V W) {γ₀ : VelocityTrajectory P}
    {ρ₀ : P.Relaxed} {ε : ℝ} (hε : 0 ≤ ε)
    (hstate : ∀ t : P.Time, P.stateConstraint t (γ₀.value t) ≤ 0) :
    InVelocityControlTube P γ₀ ρ₀ ε γ₀ ρ₀ := by
  refine ⟨self_mem_InVelocityTube γ₀ hε hstate, ?_⟩
  rw [relaxedControlDistance, RelaxedControl.kernelDistance_self]
  exact hε

end Problem

/-! ## The velocity carrier as an `L²` class

`VelocityTrajectory.velocity` is a raw square-integrable function; its `L²`
class is what the weak-compactness machinery of `WeakL2Compactness` acts on.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.1)–(11.3.2). -/

section ToLp

variable {P : Problem E V W}

/-- The velocity of a `VelocityTrajectory` as an element of the Bochner space
`L²(0,t1; E)`. -/
noncomputable def VelocityTrajectory.toLp (γ : VelocityTrajectory P) :
    Lp E 2 (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
  MemLp.toLp γ.velocity (by
    rw [memLp_two_iff_integrable_sq_norm]
    · exact γ.velocity_sq_integrable
    · have h := γ.velocity_intervalIntegrable
      rw [intervalIntegrable_iff, uIoc_of_le P.horizon_pos.le] at h
      exact h.aestronglyMeasurable)

/-- The `L²` class of the velocity agrees a.e. with the raw velocity. -/
theorem VelocityTrajectory.coeFn_toLp (γ : VelocityTrajectory P) :
    (γ.toLp : ℝ → E) =ᵐ[volume.restrict (Ioc (0 : ℝ) P.horizon)] γ.velocity := by
  unfold VelocityTrajectory.toLp
  exact MemLp.coeFn_toLp _

/-- The `L²` energy of the velocity defect equals the interval integral that the
velocity tube (11.3.2) and the penalty `F_K` (11.3.6) use.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and (11.3.6). -/
theorem integral_sq_velocity_sub_eq (γ₀ γ : VelocityTrajectory P) :
    (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2)
      = ∫ a, ‖(γ.toLp - γ₀.toLp : Lp E 2 (volume.restrict (Ioc (0 : ℝ) P.horizon))) a‖ ^ 2
          ∂(volume.restrict (Ioc (0 : ℝ) P.horizon)) := by
  rw [intervalIntegral.integral_of_le P.horizon_pos.le]
  apply integral_congr_ae
  filter_upwards [γ.coeFn_toLp, γ₀.coeFn_toLp, Lp.coeFn_sub γ.toLp γ₀.toLp] with a hγ hγ₀ hsub
  rw [hsub, Pi.sub_apply, ← hγ, ← hγ₀]

end ToLp

/-! ## The translated `L²` energy ball (the M2 translation step)

`WeakL2Compactness.exists_isMinOn_norm_sub_sq_integral_norm_sq_le` minimises on
the *origin-centred* energy ball. The book's tube `B(ε)` (11.3.2) uses the
*translated* ball `∫‖φ' − φ₀'‖² ≤ ε²`. Because the weak topology is a vector
topology, translation is a homeomorphism, and the direct method transports.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and Lemma 11.3.4. -/

section TranslatedDirectMethod

open DynamicalSystems.WeakL2 in
/-- **Translated direct method**: a weakly lower-semicontinuous functional
attains its minimum over the translated energy ball
`{v | ∫‖v − v₀‖² ≤ C}`. This is the translation step noted by the M2 review;
the compactness/`lsc` content is that of
`WeakL2.exists_isMinOn_norm_sub_sq_integral_norm_sq_le`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and Lemma 11.3.4. -/
theorem exists_isMinOn_norm_sub_sq_integral_norm_sq_le_translated
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (v₀ : Lp E 2 μ) {C : ℝ} (hC : 0 ≤ C)
    {f : WeakSpace ℝ (Lp E 2 μ) → ℝ} (hf : LowerSemicontinuous f) :
    ∃ v : Lp E 2 μ, (∫ a, ‖v a - v₀ a‖ ^ 2 ∂μ) ≤ C ∧
      ∀ w : Lp E 2 μ, (∫ a, ‖w a - v₀ a‖ ^ 2 ∂μ) ≤ C →
        f (toWeakSpace ℝ (Lp E 2 μ) v) ≤ f (toWeakSpace ℝ (Lp E 2 μ) w) := by
  let g : WeakSpace ℝ (Lp E 2 μ) → ℝ :=
    fun x => f (x + toWeakSpace ℝ (Lp E 2 μ) v₀)
  have hg : LowerSemicontinuous g := hf.comp (continuous_id.add continuous_const)
  obtain ⟨u, hu, hmin⟩ :=
    DynamicalSystems.WeakL2.exists_isMinOn_integral_norm_sq_le (f := g) hg hC
  have h1 : (∫ a, ‖(u + v₀ : Lp E 2 μ) a - v₀ a‖ ^ 2 ∂μ) = ∫ a, ‖u a‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add u v₀] with a ha
    rw [ha, Pi.add_apply, add_sub_cancel_right]
  refine ⟨u + v₀, ?_, ?_⟩
  · rw [h1]; exact hu
  · intro w hw
    have h2 : (∫ a, ‖(w - v₀ : Lp E 2 μ) a‖ ^ 2 ∂μ) = ∫ a, ‖w a - v₀ a‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub w v₀] with a ha
      rw [ha, Pi.sub_apply]
    have hw' : (∫ a, ‖(w - v₀ : Lp E 2 μ) a‖ ^ 2 ∂μ) ≤ C := by rw [h2]; exact hw
    have h := hmin (w - v₀) hw'
    have heq : (toWeakSpace ℝ (Lp E 2 μ)) (w - v₀) +
        (toWeakSpace ℝ (Lp E 2 μ)) v₀ = (toWeakSpace ℝ (Lp E 2 μ)) w := by
      rw [← map_add, sub_add_cancel]
    change f ((toWeakSpace ℝ (Lp E 2 μ)) (u + v₀)) ≤ f ((toWeakSpace ℝ (Lp E 2 μ)) w)
    rw [map_add, ← heq]
    exact h

end TranslatedDirectMethod

section TranslatedCompactness

open DynamicalSystems.WeakL2 in
/-- **Weak compactness of the translated `L²` energy ball**
`{v | ∫‖v − v₀‖² ≤ C}`. This is the compactness half of Lemma 11.3.4 on the
velocity carrier, obtained from the origin-centred compactness of
`WeakL2.isCompact_toWeakSpace_image_integral_norm_sq_le` by the vector-topology
translation `v ↦ v + v₀`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and Lemma 11.3.4. -/
theorem isCompact_toWeakSpace_image_integral_norm_sub_sq_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (v₀ : Lp E 2 μ) (C : ℝ) :
    IsCompact (toWeakSpace ℝ (Lp E 2 μ) ''
      {v : Lp E 2 μ | ∫ a, ‖v a - v₀ a‖ ^ 2 ∂μ ≤ C}) := by
  by_cases hC : 0 ≤ C
  · have hset : {v : Lp E 2 μ | ∫ a, ‖v a - v₀ a‖ ^ 2 ∂μ ≤ C} =
        (fun u : Lp E 2 μ => u + v₀) '' {u : Lp E 2 μ | ∫ a, ‖u a‖ ^ 2 ∂μ ≤ C} := by
      ext v; constructor
      · intro hv
        refine ⟨v - v₀, ?_, by simp⟩
        have h2 : (∫ a, ‖(v - v₀ : Lp E 2 μ) a‖ ^ 2 ∂μ) =
            ∫ a, ‖v a - v₀ a‖ ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_sub v v₀] with a ha
          rw [ha, Pi.sub_apply]
        change (∫ a, ‖(v - v₀ : Lp E 2 μ) a‖ ^ 2 ∂μ) ≤ C
        rw [h2]; exact hv
      · rintro ⟨u, hu, rfl⟩
        have h1 : (∫ a, ‖(u + v₀ : Lp E 2 μ) a - v₀ a‖ ^ 2 ∂μ) =
            ∫ a, ‖u a‖ ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_add u v₀] with a ha
          rw [ha, Pi.add_apply, add_sub_cancel_right]
        change (∫ a, ‖(u + v₀ : Lp E 2 μ) a - v₀ a‖ ^ 2 ∂μ) ≤ C
        rw [h1]; exact hu
    rw [hset]
    have himg : (toWeakSpace ℝ (Lp E 2 μ)) ''
          ((fun u : Lp E 2 μ => u + v₀) '' {u : Lp E 2 μ | ∫ a, ‖u a‖ ^ 2 ∂μ ≤ C}) =
        (fun x : WeakSpace ℝ (Lp E 2 μ) => x + (toWeakSpace ℝ (Lp E 2 μ)) v₀) ''
          ((toWeakSpace ℝ (Lp E 2 μ)) ''
            {u : Lp E 2 μ | ∫ a, ‖u a‖ ^ 2 ∂μ ≤ C}) := by
      ext x; constructor
      · rintro ⟨u, ⟨u', hu', rfl⟩, rfl⟩
        exact ⟨(toWeakSpace ℝ (Lp E 2 μ)) u', ⟨u', hu', rfl⟩, by rw [map_add]⟩
      · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨u + v₀, ⟨u, hu, rfl⟩, by rw [map_add]⟩
    rw [himg]
    exact (Homeomorph.addRight (toWeakSpace ℝ (Lp E 2 μ) v₀)).isCompact_image.mpr
      (DynamicalSystems.WeakL2.isCompact_toWeakSpace_image_integral_norm_sq_le C)
  · have hempty : {v : Lp E 2 μ | ∫ a, ‖v a - v₀ a‖ ^ 2 ∂μ ≤ C} = ∅ := by
      ext v
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (not_le.mp hC)
        (integral_nonneg fun a => sq_nonneg _)
    rw [hempty]; simp

end TranslatedCompactness

end OptimalControl.BoundedState
