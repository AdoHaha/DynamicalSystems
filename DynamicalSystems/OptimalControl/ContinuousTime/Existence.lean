/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedTrajectories
public import Mathlib.Topology.Order.Compact

/-!
# Existence of optimal controls for bounded continuous finite-horizon problems

The data below are primitive field/cost continuity, a uniform velocity bound,
and closed endpoint/state constraints. They do not contain trajectory
compactness, dynamics closure, or an ordinary-recovery conclusion. Feasibility
is a genuine hypothesis: an arbitrary endpoint target need not be reachable.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction NNReal Topology

namespace OptimalControl

variable (E U : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace U]

/-- Primitive data for a bounded continuous finite-horizon problem. Uniform
velocity boundedness is an explicit scope restriction of this existence
result; it is not a hidden compactness assumption on solutions. -/
structure BoundedContinuousProblem where
  horizon : ℝ
  horizon_pos : 0 < horizon
  initial : E
  dynamics : ControlTime horizon → E → U → E
  dynamics_continuous : Continuous (fun z : (ControlTime horizon × E) × U =>
    dynamics z.1.1 z.1.2 z.2)
  velocityBound : ℝ≥0
  dynamics_bound : ∀ t x u, ‖dynamics t x u‖ ≤ velocityBound
  runningCost : ControlTime horizon → E → U → ℝ
  runningCost_continuous : Continuous (fun z : (ControlTime horizon × E) × U =>
    runningCost z.1.1 z.1.2 z.2)
  terminalCost : E → ℝ
  terminalCost_continuous : Continuous terminalCost
  target : Set E
  target_closed : IsClosed target
  stateConstraint : ControlTime horizon → Set E
  stateConstraint_closed : ∀ t, IsClosed (stateConstraint t)

namespace BoundedContinuousProblem

variable {E U} [MeasurableSpace U] [BorelSpace U] [CompactSpace U]
  [FiniteDimensional ℝ E]

abbrev Time (P : BoundedContinuousProblem E U) := ControlTime P.horizon
abbrev Path (P : BoundedContinuousProblem E U) := P.Time →ᵇ E
abbrev Relaxed (P : BoundedContinuousProblem E U) :=
  RelaxedControl P.Time U (horizonProbability P.horizon P.horizon_pos)

/-- Actual dynamics and the explicitly supplied endpoint/state constraints. -/
def RelaxedAdmissible (P : BoundedContinuousProblem E U) (x : P.Path) (ρ : P.Relaxed) : Prop :=
  IsRelaxedTrajectory P.horizon_pos P.dynamics P.initial x ρ ∧
    x (timeEnd P.horizon P.horizon_pos.le) ∈ P.target ∧ ∀ t, x t ∈ P.stateConstraint t

/-- Bolza objective of a relaxed trajectory. -/
noncomputable def relaxedCost (P : BoundedContinuousProblem E U) (x : P.Path) (ρ : P.Relaxed) : ℝ :=
  P.terminalCost (x (timeEnd P.horizon P.horizon_pos.le)) +
    P.horizon * ∫ z, P.runningCost z.1 (x z.1) z.2 ∂ρ.measure

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The objective is jointly continuous in uniform path and weak relaxed
control topology. -/
theorem continuous_relaxedCost (P : BoundedContinuousProblem E U) :
    Continuous (fun p : P.Path × P.Relaxed => P.relaxedCost p.1 p.2) := by
  apply (P.terminalCost_continuous.comp
    (continuous_fst.eval_const (timeEnd P.horizon P.horizon_pos.le))).add
  apply continuous_const.mul
  have hc := RelaxedControl.continuous_setIntegral_param
    (ν := horizonProbability P.horizon P.horizon_pos)
    (fun (x : P.Path) (z : P.Time × U) => P.runningCost z.1 (x z.1) z.2)
    (P.runningCost_continuous.comp
      ((continuous_snd.fst.prodMk (continuous_fst.eval continuous_snd.fst)).prodMk continuous_snd.snd))
    MeasurableSet.univ
  simpa only [univ_prod_univ, setIntegral_univ] using hc

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Closedness of endpoint and path-state constraints, derived by continuous
point evaluation. -/
theorem isClosed_constraints (P : BoundedContinuousProblem E U) :
    IsClosed {p : P.Path × P.Relaxed |
      p.1 (timeEnd P.horizon P.horizon_pos.le) ∈ P.target ∧
        ∀ t, p.1 t ∈ P.stateConstraint t} := by
  have ht := P.target_closed.preimage
    (continuous_fst.eval_const (timeEnd P.horizon P.horizon_pos.le) :
      Continuous (fun p : P.Path × P.Relaxed => p.1 (timeEnd P.horizon P.horizon_pos.le)))
  have hs : IsClosed {p : P.Path × P.Relaxed | ∀ t, p.1 t ∈ P.stateConstraint t} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun t => (P.stateConstraint_closed t).preimage (continuous_fst.eval_const t))
  exact ht.inter hs

/-- The feasible trajectory/control set is actually compact. -/
theorem isCompact_relaxedAdmissible (P : BoundedContinuousProblem E U) :
    IsCompact {p : P.Path × P.Relaxed | P.RelaxedAdmissible p.1 p.2} :=
  (isCompact_relaxedTrajectoryGraph P.horizon_pos P.dynamics P.dynamics_continuous
    P.velocityBound P.dynamics_bound P.initial).inter_right P.isClosed_constraints

/-- **Existence of an optimal relaxed control**, under primitive bounded
continuous data and a genuine feasible pair. The minimum is against all
admissible relaxed pairs, not only a preselected minimizing sequence. -/
theorem exists_relaxed_minimizer (P : BoundedContinuousProblem E U)
    (hfeasible : ∃ x ρ, P.RelaxedAdmissible x ρ) :
    ∃ x ρ, P.RelaxedAdmissible x ρ ∧
      ∀ y σ, P.RelaxedAdmissible y σ → P.relaxedCost x ρ ≤ P.relaxedCost y σ := by
  obtain ⟨x₀, ρ₀, h₀⟩ := hfeasible
  obtain ⟨p, hp, hmin⟩ := P.isCompact_relaxedAdmissible.exists_isMinOn
    ⟨(x₀, ρ₀), h₀⟩ P.continuous_relaxedCost.continuousOn
  refine ⟨p.1, p.2, hp, ?_⟩
  intro y σ h
  exact hmin (a := (y, σ)) h

end BoundedContinuousProblem
end OptimalControl
