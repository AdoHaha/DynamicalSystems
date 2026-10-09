/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Carathéodory representations with an exact number of slots

Carathéodory gives an affinely independent finite family. Control applications
need an actual `Fin N` family, including admissible atoms in zero-weight slots.
The padding below repeats an existing point, rather than assuming that the
underlying constraint set is inhabited independently of convex-hull membership.
-/

@[expose] public section

open Set
open scoped BigOperators

namespace DynamicalSystems.ConvexAnalysis

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Every point in a convex hull has an exact `N`-slot convex representation when
`N` is at least the ambient dimension plus one. All slots, including zero-weight
padding slots, belong to the original set. -/
theorem exists_fin_convexCombination_of_mem_convexHull
    {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) (N : ℕ)
    (hN : Module.finrank ℝ E + 1 ≤ N) :
    ∃ (w : Fin N → ℝ) (z : Fin N → E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∀ i, z i ∈ s) ∧
      (∑ i, w i • z i) = x := by
  classical
  obtain ⟨ι, inst, z, w, hz, hind, hw, hsum, heq⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  letI := inst
  have hcard : Fintype.card ι ≤ N :=
    hind.card_le_finrank_succ.trans
      ((Nat.add_le_add_right (Submodule.finrank_le _) 1).trans hN)
  have hι : Nonempty ι := by
    by_contra h
    letI : IsEmpty ι := not_nonempty_iff.mp h
    simp at hsum
  let i₀ : ι := Classical.choice hι
  let e := (Fintype.equivFin ι).symm
  have hsum' : (∑ i : Fin (Fintype.card ι), w (e i)) = 1 := by
    calc
      _ = ∑ i, w i := Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
      _ = 1 := hsum
  have heq' : (∑ i : Fin (Fintype.card ι), w (e i) • z (e i)) = x := by
    calc
      _ = ∑ i, w i • z i := Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
      _ = x := heq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hcard
  let W : Fin (Fintype.card ι + k) → ℝ :=
    Fin.addCases (fun i ↦ w (e i)) (fun _ ↦ 0)
  let Z : Fin (Fintype.card ι + k) → E :=
    Fin.addCases (fun i ↦ z (e i)) (fun _ ↦ z i₀)
  refine ⟨W, Z, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [W] using (hw (e j)).le
    · intro j
      simp [W]
  · simpa [W, Fin.sum_univ_add] using hsum'
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [Z] using hz (mem_range_self (e j))
    · intro j
      simpa [Z] using hz (mem_range_self i₀)
  · simpa [W, Z, Fin.sum_univ_add] using heq'

end DynamicalSystems.ConvexAnalysis
