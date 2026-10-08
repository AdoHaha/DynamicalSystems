/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.NonconvexControlExistence

/-!
# A two-point (nonconvex) control space with convex velocity–cost epigraph

The control space `{0, 1} ⊆ ℝ` is compact but not convex. The dynamics is the
zero field, so the velocity image is the single point `0` and the velocity–cost
epigraph is `{0} × [0, ∞)`, which is convex. BM Theorem 4.4.2 therefore
produces an optimal ordinary pair despite the nonconvex control space.
-/

open Set MeasureTheory OptimalControl
open scoped BoundedContinuousFunction

local instance : CompactSpace ↥(({0, 1} : Set ℝ)) :=
  isCompact_iff_compactSpace.mp (by
    have h : ({0, 1} : Set ℝ) = {0} ∪ {1} := by
      ext x
      simp only [mem_insert_iff, mem_singleton_iff, mem_union]
    rw [h]
    exact isCompact_singleton.union isCompact_singleton)

noncomputable def twoPointProblem : LinearGrowthProblem ℝ ↥(({0, 1} : Set ℝ)) where
  horizon := 1
  horizon_pos := by norm_num
  initial := 0
  dynamics := fun _ _ _ => 0
  dynamics_continuous := continuous_const
  growthConstant := 0
  growthRate := 0
  dynamics_growth := fun _ _ _ => by simp
  runningCost := fun _ _ _ => 0
  runningCost_continuous := continuous_const
  terminalCost := fun _ => 0
  terminalCost_continuous := continuous_const
  target := univ
  target_closed := isClosed_univ
  stateConstraint := fun _ => univ
  stateConstraint_closed := fun _ => isClosed_univ

/-- The velocity–cost epigraph is convex although the control space is not. -/
theorem twoPointProblem_convex_velocityCost :
    ∀ t x, Convex ℝ
      (velocityCostSet twoPointProblem.dynamics twoPointProblem.runningCost t x) := by
  intro t x
  have hset : velocityCostSet twoPointProblem.dynamics twoPointProblem.runningCost t x =
      ({0} : Set ℝ) ×ˢ Ici (0 : ℝ) := by
    ext p
    constructor
    · rintro ⟨u, h1, h2⟩
      exact ⟨h1.symm, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨0, by simp⟩, h1.symm, h2⟩
  rw [hset]
  exact (convex_singleton (0 : ℝ)).prod (convex_Ici (0 : ℝ))

theorem twoPointProblem_feasible :
    ∃ x u, twoPointProblem.OrdinaryAdmissible x u := by
  refine ⟨BoundedContinuousFunction.const _ 0, fun _ => ⟨0, by simp⟩, measurable_const, ?_, ?_, ?_⟩
  · intro t
    change (0 : ℝ) = 0 + (1 : ℝ) • ∫ _ in Ioc (timeZero (1) _) t,
      (0 : ℝ) ∂horizonProbability (1) _
    simp
  · exact mem_univ _
  · intro t
    exact mem_univ _

example : ∃ x u, twoPointProblem.OrdinaryAdmissible x u ∧
    ∀ y v, twoPointProblem.OrdinaryAdmissible y v →
      twoPointProblem.ordinaryCost x u ≤ twoPointProblem.ordinaryCost y v :=
  twoPointProblem.exists_ordinaryMinimizer_of_convex_velocity
    twoPointProblem_convex_velocityCost twoPointProblem_feasible

#print axioms OptimalControl.exists_measurable_purifyingControl
#print axioms OptimalControl.integratedVelocityCost_mem
#print axioms OptimalControl.BoundedContinuousProblem.exists_ordinary_minimizer_of_convex_velocityCost
#print axioms OptimalControl.LinearGrowthProblem.exists_ordinaryMinimizer_of_convex_velocity
#print axioms OptimalControl.LinearGrowthProblem.ordinary_min_eq_relaxed_min_of_convex_velocity
