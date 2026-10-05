/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.StateTransition
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Duhamel's formula for trajectories with switching points

Needle controls generally produce continuous trajectories whose derivatives jump
at the switch times. This version of the formula only requires differentiability
off a countable set and integrability of the transformed forcing. The exceptional
set can in particular consist of the two endpoints of a needle interval.
-/

@[expose] public section

open MeasureTheory Set
open scoped Interval


variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Duhamel's formula for a continuous trajectory solving the inhomogeneous ODE
away from a countable set, with integrable transformed forcing. The cancellation
is still derived pointwise wherever the trajectory equation is available. -/
theorem IsStateTransition.variationOfConstants_off_countable
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    {b x : ℝ → X} {s t : ℝ} {exceptions : Set ℝ}
    (hPhi : IsStateTransition A Phi)
    (hexc : exceptions.Countable)
    (hxc : ContinuousOn x (Set.uIcc s t))
    (hx : ∀ r ∈ Set.Ioo (min s t) (max s t) \ exceptions,
      HasDerivAt x (A r (x r) + b r) r)
    (hint : IntervalIntegrable (fun r => Phi t r (b r)) volume s t) :
    x t = Phi t s (x s) + ∫ r in s..t, Phi t r (b r) := by
  have hPc : ContinuousOn (fun r => Phi t r) (Set.uIcc s t) :=
    fun r _ => (hPhi.backward t r).continuousAt.continuousWithinAt
  have hFTC := MeasureTheory.integral_eq_of_hasDerivAt_off_countable
    (fun r => Phi t r (x r)) (fun r => Phi t r (b r)) hexc
    (hPc.clm_apply hxc)
    (fun r hr => hPhi.duhamel_cancellation (hx r hr)) hint
  simp only [hPhi.diag t, ContinuousLinearMap.id_apply] at hFTC
  rw [hFTC]
  abel


omit [CompleteSpace X] in
/-- The backward product cancellation for a right-differentiable trajectory. -/
theorem duhamel_cancellation_right
    {A : ℝ → X →L[ℝ] X} {P : ℝ → X →L[ℝ] X}
    {b x : ℝ → X} {t : ℝ}
    (hP : HasDerivAt P (-(P t).comp (A t)) t)
    (hx : HasDerivWithinAt x (A t (x t) + b t) (Ici t) t) :
    HasDerivWithinAt (fun s => P s (x s)) (P t (b t)) (Ici t) t := by
  simpa [map_add] using hP.hasDerivWithinAt.clm_apply hx

/-- Duhamel's formula using the actual right derivatives and the backward
operator equation. This works at finite switching corners. -/
theorem variationOfConstants_right_of_backward
    {A : ℝ → X →L[ℝ] X} {P : ℝ → X →L[ℝ] X}
    {b x : ℝ → X} {a t : ℝ}
    (hat : a ≤ t) (hPt : P t = ContinuousLinearMap.id ℝ X)
    (hP : ∀ s ∈ Icc a t, HasDerivAt P (-(P s).comp (A s)) s)
    (hxc : ContinuousOn x (Icc a t))
    (hx : ∀ s ∈ Ioo a t, HasDerivWithinAt x (A s (x s) + b s) (Ici s) s)
    (hint : IntervalIntegrable (fun s => P s (b s)) volume a t) :
    x t = P a (x a) + ∫ s in a..t, P s (b s) := by
  have hPc : ContinuousOn P (Icc a t) :=
    fun s hs => (hP s hs).continuousAt.continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hat (hPc.clm_apply hxc)
    (fun s hs => (duhamel_cancellation_right (hP s ⟨hs.1.le, hs.2.le⟩)
      (hx s hs)).mono Ioi_subset_Ici_self) hint
  simp only [hPt, ContinuousLinearMap.id_apply] at hFTC
  rw [hFTC]
  abel


end
