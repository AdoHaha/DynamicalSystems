/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.HJBResidualBridge
public import DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple

/-!
# Smooth HJB implies the existing Pontryagin conditions

This module derives the three Pontryagin conditions from a joint C² candidate
value function, the HJB differential inequality at every state and control,
equality along an admissible trajectory, and the terminal equality.

The adjoint equation uses a spatial minimum of the nonnegative fixed-control
HJB residual. No differentiability of a minimizing control selector, no
derivative of an infimum, and no assumed costate equation occurs.

This is the smooth sufficient HJB-to-PMP direction. It does not claim that
every optimal problem has a smooth value function, or that arbitrary PMP
extremals are optimal. The pointwise endpoint regularity matches the existing
`IsAdmissiblePair` and `costateEquation` predicates.

Classical background: Kirk, Optimal Control Theory, Dover 2004, §7.1;
Berkovitz and Medhin, Nonlinear Optimal Control Theory, CRC 2012, §6.2.
-/

@[expose] public section

open Filter
open scoped Topology
open HJBResidualBridge

variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X]

/-- The joint HJB residual is the time derivative plus the Hamiltonian at the
spatial value gradient. -/
theorem hjbResidual_eq_time_add_hamiltonian
    (prob : ContinuousOCP X U) (W : ℝ → X → ℝ) (t : ℝ) (y : X) (v : U)
    (hW : DifferentiableAt ℝ (fun z : ℝ × X ↦ W z.1 z.2) (t, y)) :
    prob.L t y v + fderiv ℝ (fun z : ℝ × X ↦ W z.1 z.2)
        (t, y) (1, prob.f t y v) =
      fderiv ℝ (fun z : ℝ × X ↦ W z.1 z.2) (t, y) (1, 0) +
        hamiltonianOf prob.L prob.f t y v (gradient (W t) y) := by
  let J : (ℝ × X) →L[ℝ] ℝ :=
    fderiv ℝ (fun z : ℝ × X ↦ W z.1 z.2) (t, y)
  have hrestrict := jointDerivative_restrict_eq_spatial
    (fun z : ℝ × X ↦ W z.1 z.2) t y hW
  have hspatial : ∀ w : X, J (0, w) = inner ℝ (gradient (W t) y) w := by
    intro w
    have heq := congrArg (fun q : X →L[ℝ] ℝ ↦ q w) hrestrict
    simp only [ContinuousLinearMap.comp_apply, spatialInclusion_apply] at heq
    change J (0, w) = (fderiv ℝ (W t) y) w at heq
    rw [← toDual_gradient] at heq
    exact heq
  have hsplit : J (1, prob.f t y v) = J (1, 0) + J (0, prob.f t y v) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      J.map_add ((1 : ℝ), (0 : X)) ((0 : ℝ), prob.f t y v)
  change prob.L t y v + J (1, prob.f t y v) =
    J (1, 0) + (prob.L t y v + inner ℝ (gradient (W t) y) (prob.f t y v))
  rw [hsplit, hspatial]
  ring

/-- Hamiltonian minimization follows from the HJB lower inequality and its
attainment along the selected trajectory. -/
theorem hjbMinimizing_of_residual
    (prob : ContinuousOCP X U) (W : ℝ → X → ℝ) (x : ℝ → X) (u : ℝ → U)
    (hW : Differentiable ℝ (fun z : ℝ × X ↦ W z.1 z.2))
    (hHJB : ∀ t ∈ Set.Icc 0 prob.T, ∀ y, ∀ v ∈ prob.controlSet,
      0 ≤ prob.L t y v + fderiv ℝ (fun z : ℝ × X ↦ W z.1 z.2)
        (t, y) (1, prob.f t y v))
    (hattained : ∀ t ∈ Set.Icc 0 prob.T,
      prob.L t (x t) (u t) + fderiv ℝ (fun z : ℝ × X ↦ W z.1 z.2)
        (t, x t) (1, prob.f t (x t) (u t)) = 0) :
    HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u
      (fun t ↦ gradient (W t) (x t)) := by
  intro t ht v hv
  have hbound := hHJB t ht (x t) v hv
  have heq := hattained t ht
  rw [hjbResidual_eq_time_add_hamiltonian prob W t (x t) v (hW (t, x t))] at hbound
  rw [hjbResidual_eq_time_add_hamiltonian prob W t (x t) (u t) (hW (t, x t))] at heq
  linarith

/-- The costate equation is derived from the HJB residual and ordinary
smoothness, by the spatial Fermat/Hessian calculation. -/
theorem hjbCostateEquation_of_residual
    (prob : ContinuousOCP X U) (x₀ : X) (W : ℝ → X → ℝ)
    (x : ℝ → X) (u : ℝ → U)
    (hadm : IsAdmissiblePair prob x₀ x u)
    (hW : ContDiff ℝ 2 (fun z : ℝ × X ↦ W z.1 z.2))
    (hf : ∀ t ∈ Set.Icc 0 prob.T,
      DifferentiableAt ℝ (fun y ↦ prob.f t y (u t)) (x t))
    (hL : ∀ t ∈ Set.Icc 0 prob.T,
      DifferentiableAt ℝ (fun y ↦ prob.L t y (u t)) (x t))
    (hHJB : ∀ t ∈ Set.Icc 0 prob.T, ∀ y, ∀ v ∈ prob.controlSet,
      0 ≤ prob.L t y v + fderiv ℝ (fun z : ℝ × X ↦ W z.1 z.2)
        (t, y) (1, prob.f t y v))
    (hattained : ∀ t ∈ Set.Icc 0 prob.T,
      prob.L t (x t) (u t) + fderiv ℝ (fun z : ℝ × X ↦ W z.1 z.2)
        (t, x t) (1, prob.f t (x t) (u t)) = 0) :
    costateEquation prob.L prob.f prob.T x u (fun t ↦ gradient (W t) (x t)) := by
  intro t ht
  exact hjb_value_gradient_adjoint (fun z : ℝ × X ↦ W z.1 z.2) x t
    (fun y ↦ prob.f t y (u t)) (fun y ↦ prob.L t y (u t))
    (fderiv ℝ (fun y ↦ prob.f t y (u t)) (x t))
    (fderiv ℝ (fun y ↦ prob.L t y (u t)) (x t)) hW
    (hadm.2.2.1 t ht) (hf t ht).hasFDerivAt (hL t ht).hasFDerivAt
    (Filter.Eventually.of_forall fun y ↦ hHJB t ht y (u t) (hadm.2.1 t ht))
    (hattained t ht)

/-- **Smooth HJB-to-PMP bridge using the existing costate predicates.**

All three Pontryagin conditions are derived for the single costate
`p(t) = gradient (W t) (x t)` and packaged by `pmpAssembly_minimizing`.
-/
theorem hjbPMPAssembly_of_residual
    (prob : ContinuousOCP X U) (x₀ : X) (W : ℝ → X → ℝ)
    (x : ℝ → X) (u : ℝ → U)
    (hadm : IsAdmissiblePair prob x₀ x u)
    (hW : ContDiff ℝ 2 (fun z : ℝ × X ↦ W z.1 z.2))
    (hf : ∀ t ∈ Set.Icc 0 prob.T,
      DifferentiableAt ℝ (fun y ↦ prob.f t y (u t)) (x t))
    (hL : ∀ t ∈ Set.Icc 0 prob.T,
      DifferentiableAt ℝ (fun y ↦ prob.L t y (u t)) (x t))
    (hHJB : ∀ t ∈ Set.Icc 0 prob.T, ∀ y, ∀ v ∈ prob.controlSet,
      0 ≤ prob.L t y v + fderiv ℝ (fun z : ℝ × X ↦ W z.1 z.2)
        (t, y) (1, prob.f t y v))
    (hattained : ∀ t ∈ Set.Icc 0 prob.T,
      prob.L t (x t) (u t) + fderiv ℝ (fun z : ℝ × X ↦ W z.1 z.2)
        (t, x t) (1, prob.f t (x t) (u t)) = 0)
    (hterminal : ∀ y, W prob.T y = prob.K y) :
    IsAdmissiblePair prob x₀ x u ∧ ∃ p : ℝ → X,
      costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p ∧
      HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u p := by
  apply pmpAssembly_minimizing prob x₀ x u (fun t ↦ gradient (W t) (x t)) hadm
  · refine ⟨hjbCostateEquation_of_residual prob x₀ W x u hadm hW hf hL hHJB hattained, ?_⟩
    change gradient (W prob.T) (x prob.T) = gradient prob.K (x prob.T)
    rw [funext hterminal]
  · exact hjbMinimizing_of_residual prob W x u
      (hW.differentiable (by norm_num)) hHJB hattained
