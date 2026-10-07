import DynamicalSystems.OptimalControl.ContinuousTime.StateControlAdjointPairing
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum

open Set MeasureTheory OptimalControl
open scoped Topology

namespace StateControlFirstVariationTests

noncomputable def problem : ConvexStateControlProblem ℝ ℝ 1 where
  horizon := 1
  horizon_pos := by norm_num
  initial := 0
  controlSet := Icc (-1) 1
  controlSet_compact := isCompact_Icc
  controlSet_convex := convex_Icc _ _
  dynamics := fun _ _ u ↦ u
  dynamics_continuous := continuous_snd
  dynamics_affine := fun _ _ _ _ _ _ _ _ _ _ ↦ rfl
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

noncomputable def reference : problem.Candidate :=
  (⟨fun t ↦ (t : ℝ), continuous_subtype_val⟩, fun _ ↦ 1)

noncomputable def zeroCandidate : problem.Candidate :=
  (⟨fun _ ↦ 0, continuous_const⟩, fun _ ↦ 0)

theorem reference_dynamics : problem.DynamicsAdmissible reference := by
  refine ⟨measurable_const, ?_, ?_⟩
  · intro t
    change (1 : ℝ) ∈ Icc (-1) 1
    norm_num
  · intro t
    change (t : ℝ) = 0 + (1 : ℝ) • ∫ _ in Ioc (timeZero 1 (by norm_num)) t,
      (1 : ℝ) ∂horizonProbability 1 (by norm_num)
    rw [zero_add, one_smul, setIntegral_const, smul_eq_mul, mul_one]
    have hm := scale_horizonProbability_real_Ioc 1 (by norm_num)
      (timeZero 1 (by norm_num)) t t.2.1
    simpa [timeZero] using hm.symm

theorem zero_dynamics : problem.DynamicsAdmissible zeroCandidate := by
  refine ⟨measurable_const, ?_, ?_⟩
  · intro t
    change (0 : ℝ) ∈ Icc (-1) 1
    norm_num
  · intro t
    change (0 : ℝ) = 0 + 1 • ∫ _ in Ioc (timeZero 1 (by norm_num)) t,
      (0 : ℝ) ∂horizonProbability 1 (by norm_num)
    simp

/-- Quadratic terminal, control running cost, and nonlinear state constraint all differentiate
along actual dynamics competitors. A terminal Dirac contributes a nonzero constraint term. -/
theorem quadratic_terminal_atom_derivative :
    HasDerivAt (fun θ ↦ problem.penalizedCost 1
      (Measure.dirac (timeEnd 1 (by norm_num), (0 : Fin 1)))
      (problem.candidateAffineVariation reference zeroCandidate θ)) (-6) 0 := by
  have h := problem.hasDerivAt_penalizedCost_candidateAffineVariation data 1
    (Measure.dirac (timeEnd 1 (by norm_num), (0 : Fin 1)))
    reference zeroCandidate reference_dynamics zero_dynamics
  convert h.2.2 using 1
  norm_num [ConvexStateControlProblem.stateControlFirstVariation, data, reference,
    zeroCandidate, problem, timeEnd]

/-- The constructed costate-control pairing retains the nonlinear terminal atom contribution. -/
theorem quadratic_terminal_atom_control_pairing :
    (∫ t, ((1 : ℝ) • problem.runningControlCovector data reference t +
      (problem.affineMeasureCostate data reference 1
        (Measure.dirac (timeEnd 1 (by norm_num), (0 : Fin 1)))
        (fun _ ↦ ContinuousLinearMap.id ℝ ℝ)
        (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) t).comp
          (ContinuousLinearMap.id ℝ ℝ)) (zeroCandidate.2 t-reference.2 t)
      ∂(horizonProbability problem.horizon problem.horizon_pos).toMeasure) = -6 := by
  have hresponse (t : problem.Time) : zeroCandidate.1 t-reference.1 t =
      problem.horizon • (ContinuousLinearMap.id ℝ ℝ)
        (∫ s in Iio t, (ContinuousLinearMap.id ℝ ℝ)
          ((ContinuousLinearMap.id ℝ ℝ) (zeroCandidate.2 s-reference.2 s))
          ∂horizonProbability problem.horizon problem.horizon_pos) := by
    have hp := integralControlPath_prefix (E := ℝ) (T := 1) (by norm_num) 0
      (fun _ ↦ (1 : ℝ)) (integrable_const 1) t
    have hd := reference_dynamics.2.2 t
    change (t : ℝ) = 0 + 1 • ∫ _ in Ioc (timeZero 1 (by norm_num)) t,
      (1 : ℝ) ∂(horizonProbability 1 (by norm_num)).toMeasure at hd
    have he : (∫ s in Iio t, (1 : ℝ) ∂(horizonProbability 1 (by norm_num)).toMeasure) = t := by
      change (0 : ℝ) + 1 • (∫ _ in Ioc (timeZero 1 (by norm_num)) t,
        (1 : ℝ) ∂(horizonProbability 1 (by norm_num)).toMeasure) = _ at hp
      simpa only [zero_add, one_smul] using hp.symm.trans hd.symm
    change (0 : ℝ) - (t : ℝ) = (1 : ℝ) •
      ∫ s in Iio t, ((0 : ℝ)-1) ∂(horizonProbability 1 (by norm_num)).toMeasure
    simp only [one_smul, zero_sub]
    rw [integral_neg, he]
  have h := problem.firstVariation_eq_control_pairing data 1
    (Measure.dirac (timeEnd 1 (by norm_num), (0 : Fin 1))) reference zeroCandidate
    reference_dynamics zero_dynamics
    (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) (fun _ ↦ ContinuousLinearMap.id ℝ ℝ)
    (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) continuous_const continuous_const continuous_const
    hresponse
  have hv : problem.stateControlFirstVariation data 1
      (Measure.dirac (timeEnd 1 (by norm_num), (0 : Fin 1))) reference zeroCandidate = -6 := by
    norm_num [ConvexStateControlProblem.stateControlFirstVariation, data, reference,
      zeroCandidate, problem, timeEnd]
  rw [hv] at h
  simpa only [show problem.horizon = 1 from rfl, one_mul] using h.symm

#print axioms quadratic_terminal_atom_control_pairing
#print axioms OptimalControl.ConvexStateControlProblem.firstVariation_eq_control_pairing
#print axioms OptimalControl.ConvexStateControlProblem.ae_runningHamiltonian_minimizing_of_nonnegative_pairings

#print axioms OptimalControl.ConvexStateControlProblem.hasDerivAt_penalizedCost_candidateAffineVariation
#print axioms OptimalControl.ConvexStateControlProblem.firstVariation_nonneg_of_penalized_minimum
#print axioms OptimalControl.ConvexStateControlProblem.exists_nonnegative_firstVariation_of_isMinimum
#print axioms quadratic_terminal_atom_derivative
#print axioms OptimalControl.ConvexStateControlProblem.runningCost_supporting_controlDerivative

end StateControlFirstVariationTests
