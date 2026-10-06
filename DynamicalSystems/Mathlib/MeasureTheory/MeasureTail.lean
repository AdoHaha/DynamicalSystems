/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Tactic.Linarith

/-!
# Finite-measure tails and bounded variation

The closed tail includes an atom at its argument. Its increments therefore
use `[a,b)`, and its difference from the open tail is exactly the atom mass.
These conventions are appropriate for left-continuous costate representatives.
-/

@[expose] public section
open Set MeasureTheory
namespace MeasureTheory.Measure

/-- The closed real-valued tail of a finite positive measure. -/
noncomputable def tailMass (μ : Measure ℝ) (t : ℝ) : ℝ := μ.real (Ici t)

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

/-- Positivity and the total-mass bound are derived from the measure. -/
theorem tailMass_bounds (t : ℝ) : 0 ≤ μ.tailMass t ∧ μ.tailMass t ≤ μ.real univ :=
  ⟨measureReal_nonneg, measureReal_mono (subset_univ _)⟩

/-- Closed tails are antitone, including at atoms. -/
theorem antitone_tailMass : Antitone μ.tailMass := by
  intro a b hab
  exact measureReal_mono (Ici_subset_Ici.mpr hab)

/-- The actual measure tail has bounded variation on the entire real line. -/
theorem boundedVariationOn_tailMass : BoundedVariationOn μ.tailMass univ := by
  have hm : Monotone (fun t => -μ.tailMass t) := fun a b hab =>
    neg_le_neg (μ.antitone_tailMass hab)
  have hv := hm.monotoneOn.boundedVariationOn
    (C := μ.real univ) (fun t _ => by
      rw [abs_neg, abs_of_nonneg (μ.tailMass_bounds t).1]
      exact (μ.tailMass_bounds t).2)
  simpa only [neg_neg] using hv.neg

/-- The measurable representative is derived from monotonicity. -/
theorem measurable_tailMass : Measurable μ.tailMass := μ.antitone_tailMass.measurable

/-- Exact interval balance, retaining a possible atom at the left endpoint. -/
theorem tailMass_sub {a b : ℝ} (hab : a ≤ b) :
    μ.tailMass a - μ.tailMass b = μ.real (Ico a b) := by
  have hu : Ico a b ∪ Ici b = Ici a := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact ht.1
      · exact hab.trans ht
    · intro ht
      rcases lt_or_ge t b with htb | hbt
      · exact Or.inl ⟨ht, htb⟩
      · exact Or.inr hbt
  have hd : Disjoint (Ico a b) (Ici b) := disjoint_left.mpr
    (fun t ht hb => (not_lt_of_ge hb) ht.2)
  have he := measureReal_union (μ := μ) hd measurableSet_Ici
  rw [hu] at he
  unfold tailMass
  linarith

/-- Closed-tail minus open-tail is exactly the atom at that time. -/
theorem tailMass_sub_openTail (t : ℝ) :
    μ.tailMass t - μ.real (Ioi t) = μ.real {t} := by
  have hu : ({t} : Set ℝ) ∪ Ioi t = Ici t := by
    ext s
    simp only [mem_union, mem_singleton_iff, mem_Ioi, mem_Ici]
    constructor
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.le
    · intro h
      exact (eq_or_lt_of_le h).imp Eq.symm id
  have hd : Disjoint ({t} : Set ℝ) (Ioi t) := by
    apply disjoint_left.mpr
    intro s hs ht
    rw [mem_singleton_iff] at hs
    subst s
    exact lt_irrefl _ ht
  have he := measureReal_union (μ := μ) hd measurableSet_Ioi
  rw [hu] at he
  unfold tailMass
  linarith

/-- No multiplier mass on an interval means the costate contribution is constant. -/
theorem tailMass_eq_of_null_interval {a b : ℝ} (hab : a ≤ b) (hμ : μ (Ico a b) = 0) :
    μ.tailMass a = μ.tailMass b := by
  have h := μ.tailMass_sub hab
  have hz : μ.real (Ico a b) = 0 := (measureReal_eq_zero_iff).mpr hμ
  linarith

end MeasureTheory.Measure
