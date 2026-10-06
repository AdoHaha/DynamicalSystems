/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedTrajectories
public import DynamicalSystems.OptimalControl.ContinuousTime.MeasurableHamiltonian
public import DynamicalSystems.Mathlib.Analysis.Calculus.IntegralAffineVariation
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# ε-optimality machinery for the bounded-state problem

This file sets up the primitive data of the bounded-state ODE problem of
Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012),
(11.6.1)–(11.6.5), together with the relaxed-control primitives and the
penalty/ε-optimality objects of Section 11.3 specialized to ordinary
differential systems (Section 11.6).

The book citation for every declaration lives only in its docstring; all
declaration names are concept names.  The direct ODE route of Section 11.6 is
followed, so the hereditary Γ/Fréchet machinery of Section 11.3 is not needed.

## Rendering notes (honesty)

* The relaxed control is a probability measure on `time × Ω` with the
  normalized Lebesgue time marginal `horizonProbability`, exactly as in the
  existing library.  The book's `∫_0^{t1} · dt` is recovered from the
  normalized marginal by `T • ∫ · ∂horizonProbability`.
* The book's velocity `φ'` is not carried by the library's Volterra trajectory
  model.  We use the *control-averaged field* `realizedVelocity` as the faithful
  derivative-free rendering: for an actual relaxed trajectory it is a.e. equal
  to `φ'`.  The L² tube and the penalty defect are phrased with it.
* The book's `Λ(t) ∈ L²` envelope is replaced by continuity plus compact
  control, exactly as in the existing affine-convex development.
-/

@[expose] public section

open Set MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal BoundedContinuousFunction

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]

/-- Primitive bounded-state ODE problem.

This is the data of Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.6.1)–(11.6.5): running cost `f⁰`, dynamics `f`, a fixed compact
control set `Ω`, an endpoint equality `T(φ(0),φ(t1)) = 0`, and a state
inequality `G(t,φ(t)) ≤ 0`.  The endpoint-constraint carrier is primitive data
(not a multiplier certificate), and `controlSet_nonempty` records that the
book's `Ω` is a genuine (nonempty) control set. -/
structure Problem (E V W : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] where
  /-- Positive horizon `t1`. -/
  horizon : ℝ
  horizon_pos : 0 < horizon
  /-- Initial state `φ(0) = x₀` (also carried by the Volterra equation). -/
  initial : E
  /-- The compact control set `Ω`. -/
  controlSet : Set V
  controlSet_compact : IsCompact controlSet
  controlSet_convex : Convex ℝ controlSet
  controlSet_nonempty : controlSet.Nonempty
  /-- The dynamics `f(t,x,u)`. -/
  dynamics : ControlTime horizon → E → V → E
  dynamics_continuous :
    Continuous (fun z : (ControlTime horizon × E) × V ↦ dynamics z.1.1 z.1.2 z.2)
  /-- The running cost `f⁰(t,x,u)`. -/
  runningCost : ControlTime horizon → E → V → ℝ
  runningCost_continuous :
    Continuous (fun z : (ControlTime horizon × E) × V ↦ runningCost z.1.1 z.1.2 z.2)
  /-- The endpoint equality `T(φ(0),φ(t1)) = 0`. This is the carrier required by
  Berkovitz & Medhin (11.6.4); the affine-convex substrate did not have it. -/
  endpointConstraint : E → E → W
  /-- The state inequality `G(t,φ(t)) ≤ 0`. -/
  stateConstraint : ControlTime horizon → E → ℝ
  stateConstraint_continuous :
    Continuous (fun z : (ControlTime horizon × E) ↦ stateConstraint z.1 z.2)

namespace Problem

/-- The compact time interval `[0,t1]`. -/
abbrev Time (P : Problem E V W) := ControlTime P.horizon

/-- The compact control set as a type; relaxed controls range over it. -/
abbrev Control (P : Problem E V W) := ↥P.controlSet

/-- Bounded continuous candidate trajectories on the horizon. -/
abbrev Trajectory (P : Problem E V W) := P.Time →ᵇ E

/-- The dynamics restricted to the compact control type. -/
def relaxedDynamics (P : Problem E V W) : P.Time → E → P.Control → E :=
  fun t x u ↦ P.dynamics t x (u : V)

/-- The running cost restricted to the compact control type. -/
def relaxedRunningCost (P : Problem E V W) : P.Time → E → P.Control → ℝ :=
  fun t x u ↦ P.runningCost t x (u : V)

instance (P : Problem E V W) : CompactSpace P.Control :=
  isCompact_iff_compactSpace.mp P.controlSet_compact

instance (P : Problem E V W) : Nonempty P.Control :=
  P.controlSet_nonempty.to_subtype

end Problem

/-- Relaxed controls on the horizon with the normalized Lebesgue time marginal.
The control type is the compact set `Ω = P.controlSet`. -/
abbrev Problem.Relaxed (P : Problem E V W) :=
  RelaxedControl P.Time P.Control (horizonProbability P.horizon P.horizon_pos)

namespace Problem

/-- First-order derivative data of the primitive problem.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Assumptions 11.6.1 and 11.5.1.  The state gradients `fₓ`, `f⁰ₓ`,
`∇G` and the endpoint partial derivatives `∂₁T, ∂₂T` are primitive smooth data
of the problem; they are not multipliers or adjoints. -/
structure SmoothData (P : Problem E V W) where
  /-- `fₓ(t,x,u)`: the state derivative of the dynamics. -/
  dynamicsDerivative : P.Time → E → V → E →L[ℝ] E
  dynamics_hasFDerivAt : ∀ (t : P.Time) (u : V) (x : E),
    HasFDerivAt (fun y : E ↦ P.dynamics t y u) (dynamicsDerivative t x u) x
  /-- The joint derivative of the running cost in `(x,u)`. -/
  runningDerivative : P.Time → E × V → (E × V) →L[ℝ] ℝ
  running_hasFDerivAt : ∀ (t : P.Time) (a : E × V),
    HasFDerivAt (fun z : E × V ↦ P.runningCost t z.1 z.2) (runningDerivative t a) a
  /-- `∂₁T(x,y)`. -/
  endpointDerivative₁ : E → E → E →L[ℝ] W
  /-- `∂₂T(x,y)`. -/
  endpointDerivative₂ : E → E → E →L[ℝ] W
  endpoint_hasFDerivAt : ∀ x y : E,
    HasFDerivAt (fun p : E × E ↦ P.endpointConstraint p.1 p.2)
      ((endpointDerivative₁ x y).comp (ContinuousLinearMap.fst ℝ E E) +
       (endpointDerivative₂ x y).comp (ContinuousLinearMap.snd ℝ E E)) (x, y)
  /-- `∇G(t,x)`. -/
  stateConstraintDerivative : P.Time → E → E →L[ℝ] ℝ
  stateConstraint_hasFDerivAt : ∀ (t : P.Time) (x : E),
    HasFDerivAt (P.stateConstraint t) (stateConstraintDerivative t x) x

/-- The state normal `∇G(t,x(t))` along a reference path.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Assumption 11.2.2 and (11.6.5). -/
noncomputable def stateConstraintNormal (P : Problem E V W) (D : P.SmoothData)
    (x : P.Time → E) (t : P.Time) : E →L[ℝ] ℝ :=
  D.stateConstraintDerivative t (x t)

/-- The total time derivative `d∇G(t,φ(t))/dt` along a path, rendered through the
clamped extension of `t ↦ ∇G(t,φ(t))` to `ℝ` and Mathlib's `deriv`.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Theorem 11.6.3 (ii). -/
noncomputable def stateConstraintTotalDerivative (P : Problem E V W) (D : P.SmoothData)
    (x : P.Time → E) (t : P.Time) : E →L[ℝ] ℝ :=
  deriv (fun s : ℝ ↦ D.stateConstraintDerivative
    (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le s)
    (x (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le s))) (t : ℝ)

/-- The control-averaged field `∫_u f(t,x,u) dρ.kernel t`, the derivative-free
rendering of the velocity `φ'` of a relaxed trajectory.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.6.2) with the conditional law `ν^t`. -/
noncomputable def realizedVelocity (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) (t : P.Time) : E :=
  ∫ u, P.dynamics t (x t) (u : V) ∂ρ.kernel t

/-- The Volterra dynamics residual: how far a candidate pair is from satisfying
the integral form of `φ' = f(φ,ν,t)`.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6)/§11.6 dynamics-defect penalty. -/
noncomputable def dynamicsResidual (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) (t : P.Time) : E :=
  x t - P.initial - P.horizon •
    ∫ z in (Ioc (timeZero P.horizon P.horizon_pos.le) t) ×ˢ (univ : Set P.Control),
      P.dynamics z.1 (x z.1) (z.2 : V) ∂ρ.measure

/-- The relaxed running cost `∫ f⁰(φ(t),ν_t,t) dt`.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.6.1). -/
noncomputable def relaxedCost (P : Problem E V W)
    (x : P.Trajectory) (ρ : P.Relaxed) : ℝ :=
  ∫ z, P.runningCost z.1 (x z.1) (z.2 : V) ∂ρ.measure

/-- Relaxed admissibility: a relaxed trajectory, the endpoint equality, and the
state inequality.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.6.2)–(11.6.5). -/
def IsRelaxedAdmissible (P : Problem E V W) (x : P.Trajectory) (ρ : P.Relaxed) : Prop :=
  IsRelaxedTrajectory P.horizon_pos P.relaxedDynamics P.initial x ρ ∧
  P.endpointConstraint (x (timeZero P.horizon P.horizon_pos.le))
    (x (timeEnd P.horizon P.horizon_pos.le)) = 0 ∧
  ∀ t, P.stateConstraint t (x t) ≤ 0

/-- A relaxed optimal pair.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), "let `(φ₀,ν₀)` be optimal for the relaxed version" (§11.3). -/
def IsRelaxedMinimum (P : Problem E V W) (x : P.Trajectory) (ρ : P.Relaxed) : Prop :=
  P.IsRelaxedAdmissible x ρ ∧
  ∀ y σ, P.IsRelaxedAdmissible y σ → P.relaxedCost x ρ ≤ P.relaxedCost y σ

/-- Assumption 11.4.1: strict interior of the state constraint near both
endpoints.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Assumption 11.4.1. -/
def EndpointInterior (P : Problem E V W) (x : P.Trajectory) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < P.horizon ∧
    ∀ t : P.Time, ((t : ℝ) < δ ∨ P.horizon - δ < (t : ℝ)) →
      P.stateConstraint t (x t) < 0

/-- Assumption 11.3.8: the state normal `∇G` does not vanish on a tube around
the reference path.  The book's Theorem 11.6.3 uses `ξ_ε = -∇G/|∇G|²` but does
not list this among its hypotheses, so it is carried explicitly.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Assumption 11.3.8. -/
def ConstraintNondegenerate (P : Problem E V W) (D : P.SmoothData)
    (x : P.Time → E) : Prop :=
  ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ (t : P.Time) (y : E),
    dist y (x t) < ε₂ → stateConstraintNormal P D x t ≠ 0

/-- The total-variation distance between two relaxed controls, used to render
the book's `‖ν - ν₀‖_L` control distance.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
noncomputable def relaxedControlDistance (P : Problem E V W)
    (ρ σ : P.Relaxed) : ℝ :=
  sSup {d : ℝ | ∃ A : Set (P.Time × P.Control), MeasurableSet A ∧
    d = |ρ.measure.real A - σ.measure.real A|}

/-- The book's tube `B(ε)` around the reference pair.

The velocity clause is rendered by the control-averaged field `realizedVelocity`
(equal a.e. to `φ'` for actual relaxed trajectories); the control clause is the
total-variation distance `relaxedControlDistance`.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and §11.6. -/
def InTube (P : Problem E V W) (_D : P.SmoothData) (x₀ : P.Trajectory) (ρ₀ : P.Relaxed)
    (ε : ℝ) (x : P.Trajectory) (ρ : P.Relaxed) : Prop :=
  0 ≤ ε ∧
  (∫ t, ‖realizedVelocity P x ρ t - realizedVelocity P x₀ ρ₀ t‖ ^ 2
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure) ≤ ε ^ 2 ∧
  dist (x (timeZero P.horizon P.horizon_pos.le))
    (x₀ (timeZero P.horizon P.horizon_pos.le)) ≤ ε ∧
  relaxedControlDistance P ρ ρ₀ ≤ ε ∧
  (∀ t, P.stateConstraint t (x t) ≤ 0)

/-- The penalty remainder of `F_K` (all `F_K` terms except the running cost).

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6) and §11.6. -/
noncomputable def penaltyRemainder (P : Problem E V W) (K ε : ℝ)
    (x₀ : P.Trajectory) (ρ₀ : P.Relaxed) (x : P.Trajectory) (ρ : P.Relaxed) : ℝ :=
  (∫ t, ‖realizedVelocity P x ρ t - realizedVelocity P x₀ ρ₀ t‖ ^ 2
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure)
  + dist (x (timeZero P.horizon P.horizon_pos.le))
      (x₀ (timeZero P.horizon P.horizon_pos.le)) ^ 2
  + ε * relaxedControlDistance P ρ ρ₀
  + K * ‖P.endpointConstraint (x (timeZero P.horizon P.horizon_pos.le))
      (x (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2
  + K * ∫ t, ‖dynamicsResidual P x ρ t‖ ^ 2
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure

/-- The penalty functional `F_K` of Berkovitz & Medhin (11.3.6), specialized to
ordinary differential systems as in §11.6.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6) and §11.6. -/
noncomputable def Penalized (P : Problem E V W) (K ε : ℝ)
    (x₀ : P.Trajectory) (ρ₀ : P.Relaxed) (x : P.Trajectory) (ρ : P.Relaxed) : ℝ :=
  P.relaxedCost x ρ + penaltyRemainder P K ε x₀ ρ₀ x ρ

/-- The control-averaged state derivative `∫_u fₓ(t,x,u) dρ.kernel t`.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Theorem 11.6.3 (ii). -/
noncomputable def relaxedDynamicsDerivative (P : Problem E V W) (D : P.SmoothData)
    (x : P.Time → E) (ρ : P.Relaxed) (t : P.Time) : E →L[ℝ] E :=
  ∫ u, D.dynamicsDerivative t (x t) (u : V) ∂ρ.kernel t

/-- The control-averaged running-cost state covector
`∫_u f⁰ₓ(t,x,u) dρ.kernel t`.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Theorem 11.6.3 (ii). -/
noncomputable def relaxedRunningStateCovector (P : Problem E V W) (D : P.SmoothData)
    (x : P.Time → E) (ρ : P.Relaxed) (t : P.Time) : E →L[ℝ] ℝ :=
  ∫ u, (D.runningDerivative t (x t, (u : V))).comp (ContinuousLinearMap.inl ℝ E V)
    ∂ρ.kernel t

/-- The modified Hamiltonian of Berkovitz & Medhin (11.6.13)/(v): the
`λ⁰`-scaled running cost minus the shifted adjoint paired with the dynamics.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.6.13) and Theorem 11.6.3 (v). -/
noncomputable def modifiedHamiltonian (P : Problem E V W) (D : P.SmoothData)
    (x : P.Time → E) (ψ : P.Time → E →L[ℝ] ℝ) (lam : P.Time → ℝ) (lam0 : ℝ)
    (t : P.Time) (u : V) : ℝ :=
  lam0 * P.runningCost t (x t) u
    - (ψ t + lam t • stateConstraintNormal P D x t) (P.dynamics t (x t) u)

/-- Specification predicate for the ε-multiplier curve of Lemma 11.3.7: a
nonnegative, nonincreasing scalar function on the horizon.  The existence of
such a curve (together with the Stieltjes formula (11.6.7)) is the content of
Lemma 11.3.7 and is not proved in this module.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.7 and (11.6.7). -/
def IsStateMultiplierCurve (P : Problem E V W) (lam : P.Time → ℝ) : Prop :=
  0 ≤ lam ∧ Antitone lam

/-- Specification predicate for the ε-minimum principle (11.6.13)/(v): the
conditional law of the reference relaxed control minimizes the modified
Hamiltonian over every probability measure on the control set, almost
everywhere in time.  Establishing this from an integral minimum over relaxed
controls is the genuinely new analytic step of Phase D and is not proved here.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.6.13) and Theorem 11.6.3 (v). -/
def SatisfiesEpsilonMinimumPrinciple (P : Problem E V W) (D : P.SmoothData)
    (x : P.Time → E) (ψ : P.Time → E →L[ℝ] ℝ) (lam : P.Time → ℝ) (lam0 : ℝ)
    (ρ₀ : P.Relaxed) : Prop :=
  ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure,
    ∀ σ : ProbabilityMeasure P.Control,
      (∫ u : P.Control, modifiedHamiltonian P D x ψ lam lam0 t (u : V)
          ∂ρ₀.kernel t) ≤
        ∫ u : P.Control, modifiedHamiltonian P D x ψ lam lam0 t (u : V) ∂σ

/-! ## Structural consequences of the definitions -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [BorelSpace V] in
theorem IsRelaxedMinimum.isAdmissible {P : Problem E V W} {x : P.Trajectory}
    {ρ : P.Relaxed} (h : P.IsRelaxedMinimum x ρ) : P.IsRelaxedAdmissible x ρ :=
  h.1

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [BorelSpace V] in
theorem IsRelaxedMinimum.optimal {P : Problem E V W} {x : P.Time →ᵇ E}
    {ρ : P.Relaxed} (h : P.IsRelaxedMinimum x ρ) :
    ∀ y : P.Time →ᵇ E, ∀ σ : P.Relaxed,
      P.IsRelaxedAdmissible y σ → P.relaxedCost x ρ ≤ P.relaxedCost y σ :=
  h.2

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [BorelSpace V] in
theorem IsRelaxedAdmissible.trajectory {P : Problem E V W} {x : P.Time →ᵇ E}
    {ρ : P.Relaxed} (h : P.IsRelaxedAdmissible x ρ) :
    IsRelaxedTrajectory P.horizon_pos P.relaxedDynamics P.initial x ρ :=
  h.1

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [BorelSpace V] in
theorem IsRelaxedAdmissible.endpoint {P : Problem E V W} {x : P.Time →ᵇ E}
    {ρ : P.Relaxed} (h : P.IsRelaxedAdmissible x ρ) :
    P.endpointConstraint (x (timeZero P.horizon P.horizon_pos.le))
      (x (timeEnd P.horizon P.horizon_pos.le)) = 0 :=
  h.2.1

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [BorelSpace V] in
theorem IsRelaxedAdmissible.state {P : Problem E V W} {x : P.Time →ᵇ E}
    {ρ : P.Relaxed} (h : P.IsRelaxedAdmissible x ρ) :
    ∀ t, P.stateConstraint t (x t) ≤ 0 :=
  h.2.2

omit [FiniteDimensional ℝ E] in
/-- The reference pair lies in every tube around itself.  This is the
nonemptiness input to the Weierstrass minimizer argument of Lemma 11.3.4,
derived from admissibility rather than assumed.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
theorem self_mem_InTube {P : Problem E V W} {D : P.SmoothData}
    {x₀ : P.Trajectory} {ρ₀ : P.Relaxed}
    (h : P.IsRelaxedAdmissible x₀ ρ₀) {ε : ℝ} (hε : 0 ≤ ε) :
    P.InTube D x₀ ρ₀ ε x₀ ρ₀ := by
  refine ⟨hε, ?_, ?_, ?_, h.state⟩
  · have hzero : (∫ t, ‖realizedVelocity P x₀ ρ₀ t - realizedVelocity P x₀ ρ₀ t‖ ^ 2
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure) = 0 := by simp
    rw [hzero]
    exact sq_nonneg ε
  · simpa using hε
  · have hset : {d : ℝ | ∃ A : Set (P.Time × P.Control), MeasurableSet A ∧
        d = |ρ₀.measure.real A - ρ₀.measure.real A|} = {0} := by
      ext d
      constructor
      · rintro ⟨A, hA, rfl⟩
        simp
      · intro hd
        exact ⟨∅, MeasurableSet.empty, by simpa using hd⟩
    rw [relaxedControlDistance, hset, csSup_singleton]
    exact hε

omit [FiniteDimensional ℝ E] in
/-- The running cost plus the penalty remainder decomposes `F_K`.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6). -/
theorem Penalized_eq_cost_add_remainder (P : Problem E V W) (K ε : ℝ)
    (x₀ : P.Trajectory) (ρ₀ : P.Relaxed) (x : P.Trajectory) (ρ : P.Relaxed) :
    P.Penalized K ε x₀ ρ₀ x ρ =
      P.relaxedCost x ρ + penaltyRemainder P K ε x₀ ρ₀ x ρ :=
  rfl

end Problem

/-- A smooth nonnegative hinge on the real line, vanishing on `(-∞,0]`.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.8): `ω(t) = 0` for `t ≤ 0` and `ω(t) > 0` for `t > 0`.
The concrete witness is Mathlib's `expNegInvGlue`; a convex variant is the
primitive of `expNegInvGlue` and is not needed for the structural statements of
this module. -/
noncomputable def smoothHinge (t : ℝ) : ℝ := expNegInvGlue t

theorem smoothHinge_nonneg (t : ℝ) : 0 ≤ smoothHinge t :=
  expNegInvGlue.nonneg t

theorem smoothHinge_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : smoothHinge t = 0 :=
  expNegInvGlue.zero_of_nonpos ht

theorem smoothHinge_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < smoothHinge t :=
  expNegInvGlue.pos_of_pos ht

theorem smoothHinge_contDiff : ContDiff ℝ (⊤ : ℕ∞) smoothHinge := by
  unfold smoothHinge
  fun_prop

/-- The endpoint scale `2K(ε)` multiplying `∂T` in the ε-end conditions.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.31)–(11.3.34) and (11.6.15)–(11.6.16). -/
noncomputable def endpointScale (K : ℝ) : ℝ := 2 * K

/-! ## A.e. localization of a Hamiltonian integral minimum (11.6.13)

The relaxed form over `ρ₀.kernel t` is the genuinely new analytic step of
Phase D and is reported as blocked.  The ordinary-control localization below is
the exact Mathlib reuse named by the design
(`MeasurableHamiltonian.ae_hamiltonian_minimizing_of_integral_minimizing`), and
is the mechanism from which the a.e. pointwise (v) is obtained once the
integral minimization over measurable controls is available.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.6.13). -/
theorem epsilonHamiltonianMinimum_of_integral_minimizing
    {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
    [TopologicalSpace W] [SeparableSpace W] {μ : Measure Ω}
    (H : Ω → W → ℝ) (u : Ω → W) (hu : Measurable u)
    (hi : Integrable (fun t ↦ H t (u t)) μ)
    (hc : ∀ w, Integrable (fun t ↦ H t w) μ)
    (hcont : ∀ᵐ t ∂μ, Continuous (H t))
    (hmin : ∀ v : Ω → W, Measurable v →
      (∫ t, H t (u t) ∂μ) ≤ ∫ t, H t (v t) ∂μ) :
    ∀ᵐ t ∂μ, ∀ w, H t (u t) ≤ H t w :=
  ae_hamiltonian_minimizing_of_integral_minimizing H u hu hi hc hcont hmin

end OptimalControl.BoundedState
