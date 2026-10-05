/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.TimeReparametrizationFamily
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Global arc extensions of the original piecewise-C1 predicate

Continuous one-sided velocity fields define global primitives. The original
within-derivative hypotheses identify those primitives with the reference curve
on its two closed arcs, without any assumption on the reference outside its horizon.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace PiecewiseC1Extensions

open TimeReparametrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The global left-velocity primitive with the original initial state. -/
noncomputable def leftArc (x vL : ℝ → E) (t : ℝ) : E :=
  x 0 + ∫ q in 0..t, vL q

/-- The global right-velocity primitive, parameterized from the original corner. -/
noncomputable def rightArc (x vR : ℝ → E) (τ s : ℝ) : E :=
  x τ + ∫ q in 0..s, vR (τ + q)

/-- The constructed left arc has the prescribed actual global derivative. -/
theorem hasDerivAt_leftArc (x : ℝ → E) {vL : ℝ → E} (hvL : Continuous vL) (t : ℝ) :
    HasDerivAt (leftArc x vL) (vL t) t := by
  change HasDerivAt (fun q : ℝ ↦ x 0 + ∫ s in 0..q, vL s) (vL t) t
  have h := intervalIntegral.integral_hasDerivAt_right (hvL.intervalIntegrable 0 t)
    hvL.aestronglyMeasurable.stronglyMeasurableAtFilter hvL.continuousAt
  exact h.const_add (x 0)

/-- The constructed right arc has the prescribed shifted actual global derivative. -/
theorem hasDerivAt_rightArc (x : ℝ → E) {vR : ℝ → E} (hvR : Continuous vR)
    (τ s : ℝ) : HasDerivAt (rightArc x vR τ) (vR (τ + s)) s := by
  change HasDerivAt (fun q : ℝ ↦ x τ + ∫ t in 0..q, vR (τ + t)) (vR (τ + s)) s
  have hv : Continuous (fun q ↦ vR (τ + q)) :=
    hvR.comp (continuous_const.add continuous_id)
  have h := intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 s)
    hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt
  exact h.const_add (x τ)

omit [CompleteSpace E] in
/-- The primitive has the correct initial endpoint even before identification. -/
theorem leftArc_zero (x vL : ℝ → E) : leftArc x vL 0 = x 0 := by
  simp [leftArc]

omit [CompleteSpace E] in
/-- The right primitive starts at the original corner state. -/
theorem rightArc_zero (x vR : ℝ → E) (τ : ℝ) : rightArc x vR τ 0 = x τ := by
  simp [rightArc]

/-- FTC identifies the global left primitive on the original closed left arc. -/
theorem leftArc_eq_on {x vL vR : ℝ → E} {T τ : ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ) (hvL : Continuous vL)
    {t : ℝ} (ht : t ∈ Icc 0 τ) : leftArc x vL t = x t := by
  have hc : ContinuousOn x (Icc 0 t) := hcorner.2.2.1.mono (by
    intro q hq
    exact ⟨hq.1, hq.2.trans (ht.2.trans hcorner.2.1.le)⟩)
  have hd : ∀ q ∈ Ioo 0 t, HasDerivAt x (vL q) q := by
    intro q hq
    have hqτ : q < τ := hq.2.trans_le ht.2
    exact (hcorner.2.2.2.1 q ⟨hq.1.le, hqτ.le⟩).hasDerivAt (Iic_mem_nhds hqτ)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hc hd
    (hvL.intervalIntegrable 0 t)
  rw [leftArc, hi]
  abel

/-- FTC identifies the shifted global right primitive on the original closed right arc. -/
theorem rightArc_eq_on {x vL vR : ℝ → E} {T τ : ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ) (hvR : Continuous vR)
    {s : ℝ} (hs : s ∈ Icc 0 (T - τ)) : rightArc x vR τ s = x (τ + s) := by
  have hτs : τ ≤ τ + s := le_add_of_nonneg_right hs.1
  have hsT : τ + s ≤ T := by linarith [hs.2]
  have hc : ContinuousOn x (Icc τ (τ + s)) := hcorner.2.2.1.mono (by
    intro q hq
    exact ⟨hcorner.1.le.trans hq.1, hq.2.trans hsT⟩)
  have hd : ∀ q ∈ Ioo τ (τ + s), HasDerivAt x (vR q) q := by
    intro q hq
    exact (hcorner.2.2.2.2 q ⟨hq.1.le, hq.2.le.trans hsT⟩).hasDerivAt
      (Ici_mem_nhds hq.1)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτs hc hd
    (hvR.intervalIntegrable τ (τ + s))
  have hshift : (∫ q in 0..s, vR (τ + q)) = ∫ q in τ..τ + s, vR q := by
    simpa only [add_zero] using intervalIntegral.integral_comp_add_left vR τ (a := 0) (b := s)
  rw [rightArc, hshift, hi]
  abel

/-- The left primitive reaches exactly the original corner state. -/
theorem leftArc_corner {x vL vR : ℝ → E} {T τ : ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ) (hvL : Continuous vL) :
    leftArc x vL τ = x τ :=
  leftArc_eq_on hcorner hvL ⟨hcorner.1.le, le_rfl⟩

/-- The right primitive reaches exactly the original terminal state. -/
theorem rightArc_terminal {x vL vR : ℝ → E} {T τ : ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ) (hvR : Continuous vR) :
    rightArc x vR τ (T - τ) = x T := by
  have h := rightArc_eq_on hcorner hvR
    (show T - τ ∈ Icc 0 (T - τ) from ⟨sub_nonneg.mpr hcorner.2.1.le, le_rfl⟩)
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

/-- The constructed global extensions genuinely join at the original corner. -/
theorem arcs_join {x vL vR : ℝ → E} {T τ : ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ) (hvL : Continuous vL) :
    leftArc x vL τ = rightArc x vR τ 0 := by
  rw [leftArc_corner hcorner hvL, rightArc_zero]

/-- The actual concatenation agrees with the original curve at every horizon time. -/
theorem eqOn_concatenate {x vL vR : ℝ → E} {T τ : ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ)
    (hvL : Continuous vL) (hvR : Continuous vR) :
    EqOn x (concatenate τ (leftArc x vL) (rightArc x vR τ)) (Icc 0 T) := by
  intro t ht
  by_cases htτ : t ≤ τ
  · simp only [concatenate, htτ, ite_true]
    exact (leftArc_eq_on hcorner hvL ⟨ht.1, htτ⟩).symm
  · have hs : t - τ ∈ Icc 0 (T - τ) :=
      ⟨sub_nonneg.mpr (le_of_not_ge htτ), sub_le_sub_right ht.2 τ⟩
    have h := rightArc_eq_on hcorner hvR hs
    simp only [concatenate, htτ, ite_false]
    simpa only [← add_sub_assoc, add_sub_cancel_left] using h.symm

/-- The original one-corner predicate supplies two actual global C1 arcs and all
endpoint, join and representation facts needed by the finite-context theorems. -/
theorem exists_global_arcs {x vL vR : ℝ → E} {T τ : ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ)
    (hvL : Continuous vL) (hvR : Continuous vR) :
    ∃ xL xR : ℝ → E,
      (∀ t, HasDerivAt xL (vL t) t) ∧
      (∀ s, HasDerivAt xR (vR (τ + s)) s) ∧
      xL 0 = x 0 ∧ xL τ = x τ ∧ xR 0 = x τ ∧ xR (T - τ) = x T ∧
      xL τ = xR 0 ∧ EqOn x (concatenate τ xL xR) (Icc 0 T) := by
  exact ⟨leftArc x vL, rightArc x vR τ, hasDerivAt_leftArc x hvL,
    hasDerivAt_rightArc x hvR τ, leftArc_zero x vL, leftArc_corner hcorner hvL,
    rightArc_zero x vR τ, rightArc_terminal hcorner hvR, arcs_join hcorner hvL,
    eqOn_concatenate hcorner hvL hvR⟩

end PiecewiseC1Extensions
