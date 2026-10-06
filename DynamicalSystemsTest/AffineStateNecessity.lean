import DynamicalSystems.OptimalControl.ContinuousTime.StateConstrainedMinimumPrinciple
import DynamicalSystems.OptimalControl.ContinuousTime.AffineStateMinimumPrinciple
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum

open Set MeasureTheory OptimalControl
open scoped Topology

namespace AffineStateNecessityTests

noncomputable def problem : ConvexStateControlProblem ℝ ℝ 1 where
  horizon := 1
  horizon_pos := by norm_num
  initial := 0
  controlSet := Icc (-1) 1
  controlSet_compact := isCompact_Icc
  controlSet_convex := convex_Icc _ _
  dynamics := fun _ x u ↦ x + u
  dynamics_continuous := continuous_fst.snd.add continuous_snd
  dynamics_affine := fun _ x y u v a b _ _ _ ↦ by
    simp only [smul_eq_mul]
    ring
  runningCost := fun _ _ u ↦ u ^ 2
  runningCost_continuous := continuous_snd.pow 2
  runningCost_convex := fun _ ↦ by
    convert ((show Even (2 : ℕ) by decide).convexOn_pow (𝕜 := ℝ)).comp_linearMap
      (LinearMap.snd ℝ ℝ ℝ) using 1 <;> rfl
  terminalCost := fun x ↦ x ^ 2
  terminalCost_convex := (show Even (2 : ℕ) by decide).convexOn_pow (𝕜 := ℝ)
  constraint := fun _ x ↦ x ^ 2 - 1
  constraint_continuous := (continuous_snd.pow 2).sub continuous_const
  constraint_convex := fun _ ↦ by
    convert ((show Even (2 : ℕ) by decide).convexOn_pow (𝕜 := ℝ)).add_const (-1)
      using 1

noncomputable def data : problem.ContinuouslyDifferentiableData where
  terminalDerivative := fun x ↦ (2 * x) • ContinuousLinearMap.id ℝ ℝ
  terminalDerivative_continuous := (continuous_const.mul continuous_id).smul continuous_const
  terminal_hasFDerivAt := fun x ↦ by
    convert (hasDerivAt_pow 2 x).hasFDerivAt using 1 <;> ext <;> simp [problem]
  runningDerivative := fun _ a ↦ (2 * a.2) • ContinuousLinearMap.snd ℝ ℝ ℝ
  runningDerivative_continuous := (continuous_const.mul continuous_snd.snd).smul continuous_const
  running_hasFDerivAt := fun _ a ↦ by
    have hs : HasFDerivAt (fun a : ℝ × ℝ ↦ a.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) a :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
    convert (hasDerivAt_pow 2 a.2).hasFDerivAt.comp a hs using 1 <;> ext <;> simp [problem]
  constraintDerivative := fun _ x ↦ (2 * x) • ContinuousLinearMap.id ℝ ℝ
  constraintDerivative_continuous := (continuous_const.mul continuous_snd).smul continuous_const
  constraint_hasFDerivAt := fun _ x ↦ by
    convert ((hasDerivAt_pow 2 x).sub_const 1).hasFDerivAt using 1 <;> ext <;> simp [problem]

noncomputable def zeroCandidate : problem.Candidate :=
  (⟨fun _ ↦ 0, continuous_const⟩, fun _ ↦ 0)

/-- The reference solves the original nonzero-state-coefficient integral equation. -/
theorem zero_dynamics : problem.DynamicsAdmissible zeroCandidate := by
  refine ⟨measurable_const, ?_, ?_⟩
  · intro t
    change (0 : ℝ) ∈ Icc (-1) 1
    norm_num
  · intro t
    change (0 : ℝ) = 0 + 1 • ∫ _ in Ioc (timeZero 1 (by norm_num)) t,
      (0 + 0 : ℝ) ∂(horizonProbability 1 (by norm_num)).toMeasure
    simp

/-- The nonlinear state inequality is strictly feasible for the actual reference. -/
theorem zero_feasible : problem.residual zeroCandidate ≤ 0 := by
  intro q
  change (0 : ℝ)^2 - 1 ≤ 0
  norm_num

/-- Actual global optimality against every measurable admissible pair follows from square positivity. -/
theorem zero_isMinimum : problem.IsMinimum zeroCandidate := by
  refine ⟨zero_dynamics, zero_feasible, ?_⟩
  intro y hy hfeas
  have hi : 0 ≤ ∫ t, (y.2 t)^2 ∂(horizonProbability 1 (by norm_num)).toMeasure :=
    integral_nonneg (fun _ ↦ sq_nonneg _)
  change 0^2 + 1 * (∫ t, (0 : ℝ)^2 ∂(horizonProbability 1 (by norm_num)).toMeasure) ≤
    (y.1 (timeEnd 1 (by norm_num)))^2 + 1 *
      (∫ t, (y.2 t)^2 ∂(horizonProbability 1 (by norm_num)).toMeasure)
  simpa using add_nonneg (sq_nonneg _) hi

/-- The final necessity theorem is applied to actual optimality with nonzero A and a
nonlinear state constraint, producing a genuine finite measure and Hamiltonian minimum. -/
theorem actual_optimum_constructs_minimum_principle :
    ∃ (α : ℝ) (μ : Measure problem.ConstraintIndex) (Aext : ℝ → ℝ →L[ℝ] ℝ)
      (Phi : ℝ → ℝ → ℝ →L[ℝ] ℝ), IsFiniteMeasure μ ∧ 0 ≤ α ∧
      (α ≠ 0 ∨ μ ≠ 0) ∧ (∫ q, problem.residual zeroCandidate q ∂μ) = 0 ∧
      μ {q | problem.residual zeroCandidate q ≠ 0} = 0 ∧ Continuous Aext ∧
      (∀ t : problem.Time, Aext t = ContinuousLinearMap.id ℝ ℝ) ∧
      IsStateTransition Aext Phi ∧
      ∀ᵐ t ∂(horizonProbability problem.horizon problem.horizon_pos).toMeasure,
        ∀ v ∈ problem.controlSet,
          let p := problem.affineMeasureCostate data zeroCandidate α μ
            (fun s ↦ Phi s 0) (fun s ↦ Phi 0 s) t
          α * problem.runningCost t (zeroCandidate.1 t) (zeroCandidate.2 t) +
            p (problem.dynamics t (zeroCandidate.1 t) (zeroCandidate.2 t)) ≤
          α * problem.runningCost t (zeroCandidate.1 t) v +
            p (problem.dynamics t (zeroCandidate.1 t) v) := by
  exact problem.exists_affine_state_minimum_principle data
    (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) continuous_const
    (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) continuous_const
    (fun _ ↦ 0) continuous_const (fun _ _ _ ↦ by simp [problem])
    zeroCandidate zero_isMinimum

/-- Full K6 assembly from primitive problem data and actual global optimality.
The nonzero state coefficient and nonlinear state constraint are accepted without a
supplied transition, first variation, measure, adjoint, BV proof, or minimum certificate. -/
theorem actual_optimum_constructs_full_pmp :
    ∃ (α : ℝ) (μ : Measure problem.ConstraintIndex) (Aext : ℝ → ℝ →L[ℝ] ℝ)
      (Phi : ℝ → ℝ → ℝ →L[ℝ] ℝ) (p : ℝ → ℝ →L[ℝ] ℝ),
      IsFiniteMeasure μ ∧ 0 ≤ α ∧ (α ≠ 0 ∨ μ ≠ 0) ∧
      (∫ q, problem.residual zeroCandidate q ∂μ) = 0 ∧ μ {q | problem.residual zeroCandidate q ≠ 0} = 0 ∧
      Continuous Aext ∧ (∀ t : problem.Time, Aext t = ContinuousLinearMap.id ℝ ℝ) ∧ IsStateTransition Aext Phi ∧
      p = problem.affineCostateReal data zeroCandidate α μ Phi ∧ BoundedVariationOn p (Icc 0 problem.horizon) ∧
      (∀ t : problem.Time, ContinuousWithinAt p (Ici (t : ℝ)) t) ∧
      (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ problem.horizon →
        p s - p r = -(∫ t in r..s, (p t).comp (Aext t)) -
          (problem.horizon * α) • (∫ t in {t : problem.Time | r < (t : ℝ) ∧ (t : ℝ) ≤ s},
            problem.runningStateCovector data zeroCandidate t ∂horizonProbability problem.horizon problem.horizon_pos) -
          ∫ q in {q : problem.ConstraintIndex | r < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ s},
            problem.stateConstraintNormal data zeroCandidate q ∂μ) ∧
      (∀ t ∈ Ioc (0 : ℝ) problem.horizon,
        p t - Function.leftLim p t =
          -∫ q in {q : problem.ConstraintIndex | (q.1 : ℝ) = t}, problem.stateConstraintNormal data zeroCandidate q ∂μ) ∧
      p problem.horizon = α • data.terminalDerivative (zeroCandidate.1 (timeEnd problem.horizon problem.horizon_pos.le)) ∧
      Function.leftLim p problem.horizon =
        α • data.terminalDerivative (zeroCandidate.1 (timeEnd problem.horizon problem.horizon_pos.le)) +
          ∫ q in {q : problem.ConstraintIndex | (q.1 : ℝ) = problem.horizon},
            problem.stateConstraintNormal data zeroCandidate q ∂μ ∧
      ∀ᵐ t ∂(horizonProbability problem.horizon problem.horizon_pos).toMeasure, ∀ v ∈ problem.controlSet,
        α * problem.runningCost t (zeroCandidate.1 t) (zeroCandidate.2 t) + p t (problem.dynamics t (zeroCandidate.1 t) (zeroCandidate.2 t)) ≤
          α * problem.runningCost t (zeroCandidate.1 t) v + p t (problem.dynamics t (zeroCandidate.1 t) v) := by
  exact problem.exists_stateConstrainedPMP_of_affine_convex_minimum data
    (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) continuous_const
    (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) continuous_const
    (fun _ ↦ 0) continuous_const (fun _ _ _ ↦ by simp [problem])
    zeroCandidate zero_isMinimum

#print axioms actual_optimum_constructs_full_pmp
#print axioms actual_optimum_constructs_minimum_principle
#print axioms zero_isMinimum

end AffineStateNecessityTests
