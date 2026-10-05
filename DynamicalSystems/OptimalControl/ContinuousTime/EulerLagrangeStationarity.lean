/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.CalculusOfVariations

/-!
# Euler–Lagrange implies vanishing first variation on differentiable tests

The repository's `HasVanishingFirstVariation` quantifies over every differentiable
endpoint-zero perturbation, even if its derivative is not continuous. The
Euler–Lagrange equation implies this full statement by applying the fundamental
theorem of calculus to the momentum paired with the perturbation.
The horizon-local variants use either interior derivatives with continuity at
the endpoints, or derivatives within the closed horizon. They require no
momentum derivative across the endpoints.

If the first-variation density is not interval integrable, the repository's
totalized interval integral is zero by definition. Thus this result uses the
exact existing definition; it does not assert integrability of every test's
first-variation density or identify a cost derivative for such a test.
-/

@[expose] public section

open MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Interior Euler–Lagrange equations and momentum continuity on the closed
horizon imply the full existing first-variation predicate. No condition on the
momentum outside the horizon or derivative at its endpoints is required. -/
theorem hasVanishingFirstVariation_of_eulerLagrange_interior
    (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x : ℝ → E)
    (hT : 0 ≤ T)
    (hPcont : ContinuousOn
      (fun t ↦ fderiv ℝ (fun v : E ↦ L t (x t) v) (deriv x t)) (Set.Icc 0 T))
    (hEL : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt (fun s ↦ fderiv ℝ (fun v : E ↦ L s (x s) v) (deriv x s))
        (fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t)) t) :
    HasVanishingFirstVariation L K T x := by
  intro η hη hη0 hηT
  let P : ℝ → E →L[ℝ] ℝ :=
    fun t ↦ fderiv ℝ (fun v : E ↦ L t (x t) v) (deriv x t)
  let S : ℝ → E →L[ℝ] ℝ :=
    fun t ↦ fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t)
  let density : ℝ → ℝ := fun t ↦ (S t) (η t) + (P t) (deriv η t)
  have hboundary : (fderiv ℝ K (x T)) (η T) = 0 := by rw [hηT, map_zero]
  change (∫ t in 0..T, density t) + (fderiv ℝ K (x T)) (η T) = 0
  rw [hboundary, add_zero]
  by_cases hint : IntervalIntegrable density volume 0 T
  · have hpair : ∀ t ∈ Set.Ioo 0 T,
        HasDerivAt (fun s ↦ (P s) (η s)) (density t) t := by
      intro t ht
      exact (hEL t ht).clm_apply (hη t)
    have hηcont : ContinuousOn η (Set.Icc 0 T) :=
      fun t _ ↦ (hη t).continuousAt.continuousWithinAt
    have hpaircont : ContinuousOn (fun s ↦ (P s) (η s)) (Set.Icc 0 T) :=
      hPcont.clm_apply hηcont
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hpaircont hpair hint]
    rw [hηT, hη0, map_zero, map_zero, sub_zero]
  · exact intervalIntegral.integral_undef hint

/-- The Euler–Lagrange equation expressed by derivatives within the closed
horizon implies the full existing first-variation predicate. Its endpoint
derivatives need no extension beyond the horizon. -/
theorem hasVanishingFirstVariation_of_eulerLagrange_within
    (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x : ℝ → E)
    (hT : 0 ≤ T)
    (hEL : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun s ↦ fderiv ℝ (fun v : E ↦ L s (x s) v) (deriv x s))
        (fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t)) (Set.Icc 0 T) t) :
    HasVanishingFirstVariation L K T x := by
  apply hasVanishingFirstVariation_of_eulerLagrange_interior L K T x hT
  · exact fun t ht ↦ (hEL t ht).continuousWithinAt
  · intro t ht
    exact (hEL t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- The Euler–Lagrange equation implies the existing first-variation predicate
for every differentiable endpoint-zero perturbation. No continuity of the
perturbation's derivative is required. -/
theorem hasVanishingFirstVariation_of_eulerLagrange
    (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x : ℝ → E)
    (hT : 0 ≤ T) (hEL : eulerLagrange L T x) :
    HasVanishingFirstVariation L K T x := by
  intro η hη hη0 hηT
  let P : ℝ → E →L[ℝ] ℝ :=
    fun t ↦ fderiv ℝ (fun v : E ↦ L t (x t) v) (deriv x t)
  let S : ℝ → E →L[ℝ] ℝ :=
    fun t ↦ fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t)
  let density : ℝ → ℝ := fun t ↦ (S t) (η t) + (P t) (deriv η t)
  have hboundary : (fderiv ℝ K (x T)) (η T) = 0 := by rw [hηT, map_zero]
  change (∫ t in 0..T, density t) + (fderiv ℝ K (x T)) (η T) = 0
  rw [hboundary, add_zero]
  by_cases hint : IntervalIntegrable density volume 0 T
  · have hpair : ∀ t ∈ Set.uIcc 0 T,
        HasDerivAt (fun s ↦ (P s) (η s)) (density t) t := by
      intro t ht
      rw [Set.uIcc_of_le hT] at ht
      exact (hEL t ht).clm_apply (hη t)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hpair hint]
    rw [hηT, hη0, map_zero, map_zero, sub_zero]
  · exact intervalIntegral.integral_undef hint
