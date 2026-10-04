/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.SpatialVariational
public import DynamicalSystems.Control.Geometric.FlowIncrement
public import DynamicalSystems.Control.Geometric.FlowCommutator

/-! # The variational equation for the local flow

The spatial derivative of the local flow satisfies the linear variational
equation at every sufficiently small time. In particular, its time derivative
at zero is the derivative of the vector field. This discharges the `hVar`
premise of the time-zero Lie-derivative identity.

These are local statements at the fixed initial point. They do not assert the
transport identity on the entire original Picard--Lindelöf box, nor the
Frobenius integrability theorem.

Reference: Hartman, *Ordinary Differential Equations*, Chapter V.
-/

@[expose] public section

open Set Filter
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]

/-- The operator-valued spatial derivative satisfies the variational equation
throughout a neighborhood of time zero. -/
theorem eventually_hasDerivAt_fderiv_localFlow
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun u ↦ fderiv ℝ (localFlow hf u) x₀)
        ((fderiv ℝ f (localFlow hf t x₀)).comp
          (fderiv ℝ (localFlow hf t) x₀)) t := by
  obtain ⟨δ, hδ, J, hJ₀, hJ⟩ := exists_localFlow_tangent_solution hf
  have heq : (fun t ↦ fderiv ℝ (localFlow hf t) x₀) =ᶠ[𝓝 (0 : ℝ)] J := by
    filter_upwards [localFlow_hasFDerivAt_of_tangent hf hδ hJ₀ hJ] with t ht
    exact ht.fderiv
  have htime : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < δ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    simpa only [Metric.mem_ball, Real.dist_0_eq_abs] using ht
  filter_upwards [heq.eventuallyEq_nhds, heq, htime] with t ht hvalue hsmall
  have h := (hJ t hsmall).congr_of_eventuallyEq ht
  rwa [← hvalue] at h

/-- The first-order time expansion of the flow's spatial derivative at zero:
its derivative is `Df(x₀)`. No spatial-regularity premise is needed beyond the
continuous differentiability of the vector field. -/
theorem flow_deriv_firstOrder
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    HasDerivAt (fun t ↦ fderiv ℝ (localFlow hf t) x₀) (fderiv ℝ f x₀) 0 := by
  have h : HasDerivAt (fun u ↦ fderiv ℝ (localFlow hf u) x₀)
      ((fderiv ℝ f (localFlow hf 0 x₀)).comp
        (fderiv ℝ (localFlow hf 0) x₀)) 0 :=
    (eventually_hasDerivAt_fderiv_localFlow hf).self_of_nhds
  simpa only [localFlow_zero_apply f x₀ hf, flow_deriv_at_zero f x₀ hf,
    ContinuousLinearMap.comp_id] using h

/-- The norm remainder in `DΦₜ(x₀) = id + t • Df(x₀) + o(t)` is little-o of
time in the operator norm. -/
theorem flow_deriv_firstOrder_isLittleO
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    (fun t : ℝ ↦ ‖fderiv ℝ (localFlow hf t) x₀ - ContinuousLinearMap.id ℝ X
      - t • fderiv ℝ f x₀‖) =o[𝓝 (0 : ℝ)] (fun t : ℝ ↦ t) := by
  simpa only [flow_deriv_at_zero f x₀ hf, sub_zero] using
    (flow_deriv_firstOrder hf).isLittleO.norm_left

/-- The pullback of a `C¹` field along a `C¹` flow has time-zero derivative
equal to the Lie bracket. The variational premise of `lieDerivative_along_flow`
is discharged by `flow_deriv_firstOrder`. -/
theorem lieDerivative_along_flow_of_contDiffAt
    (f g : X → X) (x₀ : X)
    (hf : ContDiffAt ℝ 1 f x₀) (hg : ContDiffAt ℝ 1 g x₀) :
    HasDerivAt (fun t : ℝ ↦ VectorField.pullback ℝ (localFlow hf t) g x₀)
      (lieBracket f g x₀) 0 :=
  lieDerivative_along_flow f g x₀ hf hg (flow_deriv_firstOrder hf)
