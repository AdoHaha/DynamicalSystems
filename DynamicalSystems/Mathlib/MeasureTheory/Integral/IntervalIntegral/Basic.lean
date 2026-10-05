/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Basic interval-integrability and indicator identities

Generic closure facts for interval integrals: integrability of vector pairs and
of functions restricted to a left-closed right-open interval, and the identity
that the interval integral of such an indicator is the integral over the
indicator's support. No control-theoretic data appears.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Interval


section Pair

variable {X : Type*} [NormedAddCommGroup X]

/-- Interval integrability of vector pairs from the two primitive components. -/
theorem intervalIntegrable_pair {f : ℝ → ℝ} {g : ℝ → X} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t => (f t, g t)) volume a b :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

end Pair


section Normed

variable {E : Type*} [NormedAddCommGroup E]

theorem intervalIntegrable_indicator_Ico
    {g : ℝ → E} {a b c d : ℝ}
    (hg : IntervalIntegrable g volume c d) :
    IntervalIntegrable ((Ico a b).indicator g) volume c d :=
  ⟨hg.1.indicator measurableSet_Ico, hg.2.indicator measurableSet_Ico⟩

theorem intervalIntegrable_ite_Ico
    {g₀ gv : ℝ → E} {a b c d : ℝ}
    (h₀ : IntervalIntegrable g₀ volume c d)
    (hv : IntervalIntegrable gv volume c d) :
    IntervalIntegrable (fun t => if t ∈ Ico a b then gv t else g₀ t) volume c d := by
  have h := h₀.add (intervalIntegrable_indicator_Ico (a := a) (b := b) (hv.sub h₀))
  convert h using 1
  funext t
  by_cases ht : t ∈ Ico a b <;> simp [ht]

end Normed


section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_indicator_Ico
    {g : ℝ → E} {a b T : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (∫ t in 0..T, (Ico a b).indicator g t) = ∫ t in a..b, g t := by
  have hT : 0 ≤ T := ha.trans (hab.trans hb)
  have heq : (Ico a b).indicator g =ᵐ[volume] (Ioc a b).indicator g :=
    indicator_ae_eq_of_ae_eq_set Ico_ae_eq_Ioc
  calc
    (∫ t in 0..T, (Ico a b).indicator g t) =
        ∫ t in 0..T, (Ioc a b).indicator g t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [heq] with t ht _
      exact ht
    _ = ∫ t in a..b, g t := by
      rw [intervalIntegral.integral_of_le hT,
        MeasureTheory.integral_indicator measurableSet_Ioc,
        Measure.restrict_restrict measurableSet_Ioc,
        Set.inter_eq_left.mpr (Ioc_subset_Ioc ha hb),
        intervalIntegral.integral_of_le hab]

end NormedSpace
