/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Classical equi-absolute continuity and moving-interval extensions

The definition uses sums of trajectory increments over arbitrary finite
families of disjoint intervals. It does not assume uniform integrability of
velocities. Endpoints may depend on the trajectory, while the epsilon--delta
modulus is common to the family.
-/

@[expose] public section

open Set
open scoped BigOperators

namespace DynamicalSystems.ClassicalEquiAC

/-- Clamp a time to a closed interval. For ordered endpoints this gives the
constant extension of a trajectory beyond its active interval. -/
def clampTime (l r t : ℝ) : ℝ := max l (min r t)

/-- A clamped interval is exactly the original interval intersected with the
active interval. Empty intervals and intervals outside the active range are
included in this identity. -/
theorem Ioc_clampTime (l r s t : ℝ) (hlr : l ≤ r) :
    Ioc (clampTime l r s) (clampTime l r t) = Ioc s t ∩ Ioc l r := by
  ext y
  simp only [clampTime, mem_Ioc, mem_inter_iff]
  constructor
  · rintro ⟨hleft, hright⟩
    have hly : l < y := (le_max_left _ _).trans_lt hleft
    have hmin : min r s < y := (le_max_right _ _).trans_lt hleft
    have hyr : y ≤ r := hright.trans (max_le hlr (min_le_left _ _))
    have hsy : s < y := (min_lt_iff.mp hmin).resolve_left (not_lt_of_ge hyr)
    have hyt : y ≤ t := by
      rcases le_max_iff.mp hright with h | h
      · exact False.elim ((not_le_of_gt hly) h)
      · exact h.trans (min_le_right _ _)
    exact ⟨⟨hsy, hyt⟩, hly, hyr⟩
  · rintro ⟨⟨hsy, hyt⟩, hly, hyr⟩
    exact ⟨max_lt hly ((min_le_right _ _).trans_lt hsy),
      (le_min hyr hyt).trans (le_max_right _ _)⟩

/-- Clamping preserves time order. -/
theorem clampTime_mono (l r : ℝ) : Monotone (clampTime l r) :=
  fun _ _ h ↦ max_le_max_left l (min_le_min_left r h)

/-- Clamping cannot increase an interval's length. -/
theorem clampTime_sub_le_sub (l r s t : ℝ) (hst : s ≤ t) :
    clampTime l r t - clampTime l r s ≤ t - s := by
  simp only [clampTime, max_def, min_def]
  split_ifs <;> linarith

/-- Every clamped time is in the active interval. -/
theorem clampTime_mem_Icc (l r t : ℝ) (hlr : l ≤ r) :
    clampTime l r t ∈ Icc l r :=
  ⟨le_max_left _ _, max_le hlr (min_le_left _ _)⟩

/-- Clamping fixes active times. -/
theorem clampTime_eq_self {l r t : ℝ} (ht : t ∈ Icc l r) :
    clampTime l r t = t := by
  simp only [clampTime, min_eq_right ht.2, max_eq_right ht.1]

/-- The extension is constant to the left. -/
theorem clampTime_eq_left {l r t : ℝ} (ht : t ≤ l) : clampTime l r t = l :=
  max_eq_left ((min_le_right _ _).trans ht)

/-- The extension is constant to the right. -/
theorem clampTime_eq_right {l r t : ℝ} (hlr : l ≤ r) (ht : r ≤ t) :
    clampTime l r t = r := by
  simp only [clampTime, min_eq_left ht, max_eq_right hlr]

variable {ι E : Type*} [NormedAddCommGroup E]

/-- Classical equi-absolute continuity on possibly varying time intervals.
There is one modulus for all trajectories and all finite families of disjoint
ordered subintervals. The controlled quantities are actual trajectory
increments, not integrals of velocity norms. -/
def EquiAbsolutelyContinuousOn (x : ι → ℝ → E) (l r : ι → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (i : ι) (κ : Type) [Fintype κ] (s t : κ → ℝ),
      (∀ j, l i ≤ s j ∧ s j ≤ t j ∧ t j ≤ r i) →
      Pairwise (fun j k ↦ Disjoint (Ioc (s j) (t j)) (Ioc (s k) (t k))) →
      (∑ j : κ, (t j - s j)) < δ → (∑ j : κ, ‖x i (t j) - x i (s j)‖) < ε

/-- Constant extension from each active interval preserves the same classical
modulus on a common interval. Clipping preserves disjointness and only
shortens total interval length; it does not require endpoint convergence. -/
theorem EquiAbsolutelyContinuousOn.clamp
    {x : ι → ℝ → E} {l r : ι → ℝ}
    (hx : EquiAbsolutelyContinuousOn x l r) (hlr : ∀ i, l i ≤ r i) (a b : ℝ) :
    EquiAbsolutelyContinuousOn (fun i t ↦ x i (clampTime (l i) (r i) t))
      (fun _ ↦ a) (fun _ ↦ b) := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hx ε hε
  refine ⟨δ, hδ, ?_⟩
  intro i κ inst s t hst hdisj hlength
  apply hbound i κ (fun j ↦ clampTime (l i) (r i) (s j))
    (fun j ↦ clampTime (l i) (r i) (t j))
  · intro j
    exact ⟨(clampTime_mem_Icc _ _ _ (hlr i)).1,
      clampTime_mono _ _ (hst j).2.1, (clampTime_mem_Icc _ _ _ (hlr i)).2⟩
  · intro j k hjk
    rw [Ioc_clampTime _ _ _ _ (hlr i), Ioc_clampTime _ _ _ _ (hlr i)]
    exact (hdisj hjk).mono inter_subset_left inter_subset_left
  · exact (Finset.sum_le_sum (fun j _ ↦
      clampTime_sub_le_sub _ _ _ _ (hst j).2.1)).trans_lt hlength

end DynamicalSystems.ClassicalEquiAC
