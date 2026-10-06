/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module
import DynamicalSystems.Mathlib.Analysis.ODE.MeasureAdjoint
import DynamicalSystems.OptimalControl.ContinuousTime.IntegratorStateMinimumPrinciple
import Mathlib.Tactic.NormNum
open Set MeasureTheory MeasureAdjoint
open scoped Topology
namespace MeasureAdjointTest
noncomputable def q : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
/-- An interior Dirac measure produces the intended costate step. -/
theorem dirac_step (t : ℝ) :
    costate (Measure.dirac 1) (fun _ ↦ q) (-q) t = if t < 1 then 0 else -q := by
  by_cases ht : t < 1 <;> simp [costate, openIntegralTail, q, ht]
/-- The integral costate has a genuinely nonzero interior jump. -/
theorem dirac_jump :
    costate (Measure.dirac 1) (fun _ ↦ q) (-q) 1 -
      Function.leftLim (costate (Measure.dirac 1) (fun _ ↦ q) (-q)) 1 = -q := by
  simpa using jump (-q) (μ := Measure.dirac 1) (w := fun _ ↦ q)
    (integrable_const q) 1
/-- The left terminal trace differs from the terminal covector for an atomic multiplier. -/
theorem terminal_atom :
    Function.leftLim
      (costate ((Measure.dirac 1).restrict (Iic 1)) (fun _ ↦ q) (-q)) 1 = 0 := by
  simpa using terminal_left_trace (-q) (μ := Measure.dirac 1) (w := fun _ ↦ q) 1
    (integrable_const q)
/-- At the terminal endpoint the open tail excludes the atom. -/
theorem terminal_atom_value :
    costate ((Measure.dirac 1).restrict (Iic 1)) (fun _ ↦ q) (-q) 1 = -q :=
  terminal_value (-q) _ _ _
#print axioms OptimalControl.ConvexStateControlProblem.exists_integrator_state_pmp
#print axioms OptimalControl.ConvexStateControlProblem.integrator_augmented_cost_eq
#print axioms MeasureTheory.boundedVariationOn_openIntegralTail
#print axioms MeasureTheory.tendsto_openIntegralTail_left
#print axioms MeasureAdjoint.integral_order_tail_pairing
#print axioms MeasureAdjoint.integral_tail_pairing
#print axioms MeasureAdjoint.propagated_boundedVariation
#print axioms MeasureAdjoint.propagated_balance
#print axioms MeasureAdjoint.propagated_jump
#print axioms MeasureAdjoint.propagated_formula
#print axioms MeasureAdjoint.terminal_left_trace
#print axioms MeasureAdjointTest.dirac_jump
end MeasureAdjointTest
