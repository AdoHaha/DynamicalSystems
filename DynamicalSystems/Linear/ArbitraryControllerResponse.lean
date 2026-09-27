/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GenericControllerNecessity
public import DynamicalSystems.Linear.DynamicFeedbackNecessity

/-! # Stable external response with arbitrary controller state

The controller state space is existentially quantified, rather than fixed to
the plant state space. Geometric sufficiency and the first necessity inclusion
follow from the existing construction and the real-space Bohl bridge. The dual
necessity inclusion requires a generic controller-state transpose bridge.
-/

@[expose] public section


open Filter
open scoped Topology

universe u

namespace LinearSystem

noncomputable section

variable {X U Y D Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- **Arbitrary-controller-state stable external response (book Corollary 6.22
quantifier).** There exists a finite-dimensional real normed controller state
space `W` and a dynamic controller `ctrl : DynamicController ℝ W Y U` such that
the forced external response of the generic zero-`F` interconnection decays to
zero in every disturbance direction.

This is the literal reading of the Corollary 6.22 statement, in which the
controller order is not fixed: the fixed-state predicate
`StableNonzeroExternalResponse` only allows `W = X`. The generic
interconnection is `genericZeroFInterconnection`, which is the same
`⟨sys, ctrl, E, 0, H⟩` interconnection as `cabPairInterconnection` but with an
arbitrary controller state. -/
def AnyStateStableExternalResponse (sys : LinearSystem ℝ X U Y)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) : Prop :=
  ∃ (W : Type u) (_ : NormedAddCommGroup W) (_ : NormedSpace ℝ W)
      (_ : FiniteDimensional ℝ W),
    ∃ ctrl : DynamicController ℝ W Y U,
      ∀ d : D, Filter.Tendsto
        (fun t : ℝ => (genericZeroFInterconnection sys ctrl E H).externalResponse
          ((genericZeroFInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD) t d)
        Filter.atTop (nhds 0)

/-- The fixed-state stable-nonzero external response implies the arbitrary-state
predicate, by taking the witness `W = X`. -/
theorem anyStateStableExternalResponse_of_stableNonzeroExternalResponse
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : StableNonzeroExternalResponse sys hD E H) :
    AnyStateStableExternalResponse sys hD E H := by
  obtain ⟨ctrl, hdec⟩ := h
  refine ⟨X, inferInstance, inferInstance, inferInstance, ctrl, ?_⟩
  simpa only [genericZeroFInterconnection, cabPairInterconnection] using hdec

section ExternalStabilizationConditionsToAnyState

variable [FiniteDimensional ℝ Y] [FiniteDimensional ℝ D]

/-- The Corollary 6.22 geometric subspace conditions imply the arbitrary-state
stable external response, by composing the existing fixed-state sufficiency
`stableNonzeroExternalResponse_of_externalStabilizationConditions` with the
fixed-to-arbitrary packaging above. -/
theorem anyStateStableExternalResponse_of_externalStabilizationConditions
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : ExternalStabilizationConditions sys E H) :
    AnyStateStableExternalResponse sys hD E H :=
  anyStateStableExternalResponse_of_stableNonzeroExternalResponse sys hD E H
    (stableNonzeroExternalResponse_of_externalStabilizationConditions sys hD E H h)

end ExternalStabilizationConditionsToAnyState

section FirstInclusion

variable [FiniteDimensional ℝ U]

/-- The arbitrary-state stable external response implies the first geometric
inclusion of Corollary 6.22, using the generic first-inclusion theorem
`range_E_le_outputStabilizableSubspace_of_genericStableResponse`. -/
theorem first_inclusion_of_anyStateStableExternalResponse
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : AnyStateStableExternalResponse sys hD E H) :
    LinearMap.range E ≤ outputStabilizableSubspace sys.A sys.B H := by
  obtain ⟨W, hW1, hW2, hW3, ctrl, hdec⟩ := h
  exact range_E_le_outputStabilizableSubspace_of_genericStableResponse
    (W := W) sys hD E H ctrl hdec

end FirstInclusion

end

end LinearSystem
