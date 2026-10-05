import DynamicalSystems.OptimalControl.ContinuousTime.GeometricNeedlePMP
import DynamicalSystems.OptimalControl.ContinuousTime.CovectorPMPBridge
import DynamicalSystems.OptimalControl.ContinuousTime.ReferenceExtension

/-!
# Integral optimality implies the existing PMP predicates by geometric needles

This final theorem assembles the actual augmented needle construction, terminal
sensitivity, optimality inequality, constructed variation cone, geometric
Hahn–Banach extraction, adjoint propagation, and Riesz identification. All three
conclusions use the existing project predicates unchanged. The competitor class
is explicitly the corrected integral class, and the primitive global branch
assumptions are visible in the theorem statement.
-/

namespace KirkMedhin.K1

open Set

variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]

/-- Normal PMP for the corrected integral optimality notion, derived by the
literal augmented-state geometric Hahn–Banach route. The global branch
assumptions concern the actual physical dynamics and running cost. No feasible
family, state transition, endpoint expansion, separator, adjoint, or Hamiltonian
inequality is an assumed residual. -/
theorem integralOptimal_implies_PMP_via_hahnBanach
    (prob : ContinuousOCP X U) (x_init : X) (x : ℝ → X) (u : ℝ → U)
    (hT : 0 < prob.T)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x_init x u)
    (r₀ : BolzaBranchRegularity prob u)
    (rtest : ∀ v ∈ prob.controlSet, BolzaBranchRegularity prob (fun _ => v))
    (hx : IsIntegralCurve x (fun t z => prob.f t z (u t)))
    (DL : ℝ → X → X →L[ℝ] ℝ) (Df : ℝ → X → X →L[ℝ] X)
    (hDL : ∀ t ∈ Icc 0 prob.T, ∀ z,
      HasFDerivAt (fun y => prob.L t y (u t)) (DL t z) z)
    (hDf : ∀ t ∈ Icc 0 prob.T, ∀ z,
      HasFDerivAt (fun y => prob.f t y (u t)) (Df t z) z)
    (hDLc : ∀ t ∈ Icc 0 prob.T,
      ContinuousAt (fun q : ℝ × X => DL q.1 q.2) (t, x t))
    (hDfc : ∀ t ∈ Icc 0 prob.T,
      ContinuousAt (fun q : ℝ × X => Df q.1 q.2) (t, x t))
    (DK : X →L[ℝ] ℝ) (hK : HasFDerivAt prob.K DK (x prob.T)) :
    ∃ p : ℝ → X,
      costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p ∧
      HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u p := by
  obtain ⟨Φ, _q, _α, _hq, _hα, _hcoefficient, _hnormalize, _hcone, hpd, hpT, hmin⟩ :=
    exists_geometricNormalPMP_of_primitive_data prob x_init x u hT hopt r₀ rtest hx
      DL Df hDL hDf hDLc hDfc DK hK
  let pcov : ℝ → X →L[ℝ] ℝ := fun t => propagatedStateCovector DK (Φ prob.T t)
  refine ⟨K1CovectorPMP.vectorCostate pcov, ?_⟩
  exact K1CovectorPMP.projectPMP_of_covector prob x u pcov
    (fun t => Df t (x t)) (fun t => DL t (x t)) DK hpd hpT
    (fun t ht => hDf t ht (x t)) (fun t ht => hDL t ht (x t)) hK hmin

/-- The literal geometric normal PMP from integral optimality alone, without a
supplied classical reference or any requirement on its values outside the horizon.

The nominal dynamics hypotheses construct a global reference representative and
prove equality on `[0,T]` by uniqueness for the actual integral dynamics. The
geometric proof is applied to that representative, then all three unchanged
project predicates transfer back to the user's original state curve. -/
theorem integralOptimal_implies_PMP_via_hahnBanach_of_integral_reference
    (prob : ContinuousOCP X U) (x_init : X) (x : ℝ → X) (u : ℝ → U)
    (hT : 0 < prob.T)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x_init x u)
    (r₀ : BolzaBranchRegularity prob u)
    (rtest : ∀ v ∈ prob.controlSet, BolzaBranchRegularity prob (fun _ => v))
    (DL : ℝ → X → X →L[ℝ] ℝ) (Df : ℝ → X → X →L[ℝ] X)
    (hDL : ∀ t ∈ Icc 0 prob.T, ∀ z,
      HasFDerivAt (fun y => prob.L t y (u t)) (DL t z) z)
    (hDf : ∀ t ∈ Icc 0 prob.T, ∀ z,
      HasFDerivAt (fun y => prob.f t y (u t)) (Df t z) z)
    (hDLc : ∀ t ∈ Icc 0 prob.T,
      ContinuousAt (fun q : ℝ × X => DL q.1 q.2) (t, x t))
    (hDfc : ∀ t ∈ Icc 0 prob.T,
      ContinuousAt (fun q : ℝ × X => Df q.1 q.2) (t, x t))
    (DK : X →L[ℝ] ℝ) (hK : HasFDerivAt prob.K DK (x prob.T)) :
    ∃ p : ℝ → X,
      costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p ∧
      HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u p := by
  obtain ⟨y, hy, heq, hyopt⟩ := NeedleIntegralModel.exists_global_optimal_reference_of_integral
    prob x_init x u hT.le r₀.dynamics_lipschitz r₀.dynamics_zero_bound
      r₀.dynamics_continuous hopt
  have hDLcy : ∀ t ∈ Icc 0 prob.T,
      ContinuousAt (fun q : ℝ × X => DL q.1 q.2) (t, y t) := by
    intro t ht
    simpa only [heq ht] using hDLc t ht
  have hDfcy : ∀ t ∈ Icc 0 prob.T,
      ContinuousAt (fun q : ℝ × X => Df q.1 q.2) (t, y t) := by
    intro t ht
    simpa only [heq ht] using hDfc t ht
  have hKy : HasFDerivAt prob.K DK (y prob.T) := by
    simpa only [heq (right_mem_Icc.mpr hT.le)] using hK
  obtain ⟨p, hcostate, hterminal, hminimum⟩ :=
    integralOptimal_implies_PMP_via_hahnBanach prob x_init y u hT hyopt r₀ rtest hy
      DL Df hDL hDf hDLcy hDfcy DK hKy
  exact ⟨p,
    (NeedleIntegralModel.costateEquation_congr_state prob u p heq).mp hcostate,
    (NeedleIntegralModel.transversalityCondition_congr_state prob p hT.le heq).mp hterminal,
    (NeedleIntegralModel.HamiltonianMinimizing_congr_state prob u p heq).mp hminimum⟩

end KirkMedhin.K1
