/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.Convex.FiniteCaratheodory
public import DynamicalSystems.OptimalControl.ContinuousTime.FiniteRelaxedEpigraph

/-!
# The finite relaxed epigraph is the convex hull of the ordinary epigraph

For a state space of dimension `d`, exactly `d + 2` atom slots suffice: the
velocity--cost space has dimension `d + 1`. The argument treats the epigraph
slack explicitly and does not require nonempty constraint fibers in advance.
-/

@[expose] public section

open Set DynamicalSystems.MeasurableLift DynamicalSystems.ConvexAnalysis
open scoped BigOperators

namespace OptimalControl

variable {T E U : Type*} [AddCommGroup E] [Module ℝ E]

/-- Every finite relaxed velocity--cost pair is in the convex hull of the
ordinary constrained epigraph. The common nonnegative cost slack is assigned
to every atom, so the convex combination has exactly the requested cost. -/
theorem finiteRelaxedVelocityCostSet_subset_convexHull (N : ℕ)
    (C : Set (T × E × U)) (f : T × E × U → E) (c : T × E × U → ℝ)
    (t : T) (x : E) :
    constrainedVelocityCostSet (finiteRelaxedControlGraph N C)
      (finiteRelaxedVelocity N f) (finiteRelaxedRunningCost N c) t x ⊆
        convexHull ℝ (constrainedVelocityCostSet C f c t x) := by
  rintro p ⟨u, hu, hvel, hcost⟩
  let q : ℝ := finiteRelaxedRunningCost N c (t, x, u)
  have hslack : 0 ≤ p.2 - q := sub_nonneg.mpr hcost
  apply mem_convexHull_of_exists_fintype u.1
    (fun i ↦ (f (t, x, u.2 i), c (t, x, u.2 i) + (p.2 - q))) hu.1 hu.2.1
  · intro i
    exact ⟨u.2 i, hu.2.2 i, rfl, le_add_of_nonneg_right hslack⟩
  · apply Prod.ext
    · simpa [finiteRelaxedVelocity] using hvel
    · change (∑ i, u.1 i * (c (t, x, u.2 i) + (p.2 - q))) = p.2
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hu.2.1, one_mul]
      change q + (p.2 - q) = p.2
      ring

/-- Carathéodory's theorem realizes the entire convex hull of the original
velocity--cost epigraph with `N ≥ d + 2` admissible atom slots. -/
theorem convexHull_subset_finiteRelaxedVelocityCostSet [FiniteDimensional ℝ E]
    (N : ℕ) (hN : Module.finrank ℝ E + 2 ≤ N)
    (C : Set (T × E × U)) (f : T × E × U → E) (c : T × E × U → ℝ)
    (t : T) (x : E) :
    convexHull ℝ (constrainedVelocityCostSet C f c t x) ⊆
      constrainedVelocityCostSet (finiteRelaxedControlGraph N C)
        (finiteRelaxedVelocity N f) (finiteRelaxedRunningCost N c) t x := by
  classical
  intro p hp
  have hdim : Module.finrank ℝ (E × ℝ) + 1 ≤ N := by
    simpa [Module.finrank_prod, Nat.add_assoc] using hN
  obtain ⟨w, z, hw, hsum, hz, heq⟩ :=
    exists_fin_convexCombination_of_mem_convexHull hp N hdim
  choose atoms hgraph hvel hcost using hz
  refine ⟨(w, atoms), ⟨hw, hsum, hgraph⟩, ?_, ?_⟩
  · have h := congrArg Prod.fst heq
    simpa [finiteRelaxedVelocity, ← hvel] using h
  · change (∑ i, w i * c (t, x, atoms i)) ≤ p.2
    calc
      _ ≤ ∑ i, w i * (z i).2 :=
        Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hcost i) (hw i))
      _ = p.2 := by simpa using congrArg Prod.snd heq

/-- The `d + 2`-atom constrained epigraph agrees exactly with the convex hull of
its ordinary counterpart; no closure or additional fiber assumption is hidden
in this equality. -/
theorem finiteRelaxedVelocityCostSet_eq_convexHull [FiniteDimensional ℝ E]
    (N : ℕ) (hN : Module.finrank ℝ E + 2 ≤ N)
    (C : Set (T × E × U)) (f : T × E × U → E) (c : T × E × U → ℝ)
    (t : T) (x : E) :
    constrainedVelocityCostSet (finiteRelaxedControlGraph N C)
      (finiteRelaxedVelocity N f) (finiteRelaxedRunningCost N c) t x =
        convexHull ℝ (constrainedVelocityCostSet C f c t x) :=
  Subset.antisymm (finiteRelaxedVelocityCostSet_subset_convexHull N C f c t x)
    (convexHull_subset_finiteRelaxedVelocityCostSet N hN C f c t x)

/-- Under convexity of the ordinary epigraph, any finite relaxed pair can be
realized by an ordinary control with the same velocity and no larger cost.
This statement is pointwise; measurable recovery is supplied by the selector. -/
theorem finiteRelaxedVelocityCostSet_subset_of_convex (N : ℕ)
    (C : Set (T × E × U)) (f : T × E × U → E) (c : T × E × U → ℝ)
    (t : T) (x : E) (hconvex : Convex ℝ (constrainedVelocityCostSet C f c t x)) :
    constrainedVelocityCostSet (finiteRelaxedControlGraph N C)
      (finiteRelaxedVelocity N f) (finiteRelaxedRunningCost N c) t x ⊆
        constrainedVelocityCostSet C f c t x := by
  simpa [hconvex.convexHull_eq] using
    finiteRelaxedVelocityCostSet_subset_convexHull N C f c t x

end OptimalControl
