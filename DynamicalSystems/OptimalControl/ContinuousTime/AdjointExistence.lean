import DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple
import DynamicalSystems.Mathlib.Analysis.ODE.Adjoint

/-!
# Adjoint existence from continuous coefficients on the control horizon

The adjoint is constructed by the generic global ODE existence theorem after
clamping the two actual linearized coefficients to the compact time interval.
Neither a costate nor its derivative is supplied as an input.  The final bridge
identifies this constructed linear adjoint with the project's Hamiltonian-gradient
predicate using actual spatial derivatives of the dynamics and running cost.
-/


open Set
open scoped NNReal

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem _root_.exists_costate_of_spatial_derivatives
    (prob : ContinuousOCP E U) (x : ℝ → E) (u : ℝ → U)
    (A : ℝ → E →L[ℝ] E) (ell : ℝ → E)
    (hT : 0 ≤ prob.T)
    (hA : ContinuousOn A (Icc 0 prob.T))
    (hell : ContinuousOn ell (Icc 0 prob.T))
    (hf : ∀ t ∈ Icc 0 prob.T,
      HasFDerivAt (fun y => prob.f t y (u t)) (A t) (x t))
    (hL : ∀ t ∈ Icc 0 prob.T,
      HasGradientAt (fun y => prob.L t y (u t)) (ell t) (x t)) :
    ∃ p : ℝ → E, Continuous p ∧
      (∀ t ∈ Icc 0 prob.T,
        HasDerivAt p (-(A t).adjoint (p t) - ell t) t) ∧
      costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p := by
  obtain ⟨p, hpc, hpT, hpd⟩ := exists_adjointOn_Icc hT hA hell
    (gradient prob.K (x prob.T))
  refine ⟨p, hpc, hpd, ?_, hpT⟩
  intro t ht
  have hgrad := hasGradientAt_hamiltonian
    (p := p t) (hL t ht) (hf t ht)
  change HasDerivAt p
    (-gradient (fun y => prob.L t y (u t) + inner ℝ (p t) (prob.f t y (u t)))
      (x t)) t
  rw [hgrad.gradient]
  convert hpd t ht using 1
  abel
