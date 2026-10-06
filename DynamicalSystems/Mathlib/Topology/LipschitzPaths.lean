/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compactness of uniformly Lipschitz paths with a fixed initial value

The compactness is derived from Arzelà–Ascoli and finite-dimensional closed
ball compactness. It is not an assumption on a feasible trajectory set.
-/

@[expose] public section

open Set Metric
open scoped BoundedContinuousFunction NNReal

namespace BoundedContinuousFunction

variable {τ E : Type*} [MetricSpace τ] [CompactSpace τ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Uniformly Lipschitz paths with a prescribed value at one time. -/
def LipschitzPaths (K : ℝ≥0) (t₀ : τ) (x₀ : E) : Set (τ →ᵇ E) :=
  {x | LipschitzWith K x ∧ x t₀ = x₀}

omit [CompactSpace τ] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Uniform limits preserve both the Lipschitz estimate and the initial value. -/
theorem isClosed_lipschitzPaths (K : ℝ≥0) (t₀ : τ) (x₀ : E) :
    IsClosed (LipschitzPaths K t₀ x₀) := by
  have hc : Continuous (fun x : τ →ᵇ E => (x : τ → E)) := continuous_coe
  have hl : IsClosed {x : τ →ᵇ E | LipschitzWith K (x : τ → E)} :=
    (isClosed_setOfPred_lipschitzWith (α := τ) (β := E) K).preimage hc
  have he : IsClosed {x : τ →ᵇ E | x t₀ = x₀} :=
    isClosed_eq ((continuous_apply t₀).comp hc) continuous_const
  exact hl.inter he

/-- Actual compactness of the uniformly Lipschitz trajectory tube. -/
theorem isCompact_lipschitzPaths (K : ℝ≥0) (t₀ : τ) (x₀ : E) :
    IsCompact (LipschitzPaths K t₀ x₀) := by
  apply arzela_ascoli₂ (closedBall x₀ (K * diam (univ : Set τ)))
    (isCompact_closedBall _ _) _ (isClosed_lipschitzPaths K t₀ x₀)
  · intro x t hx
    change dist (x t) x₀ ≤ _
    rw [← hx.2]
    exact (hx.1.dist_le_mul t t₀).trans
      (mul_le_mul_of_nonneg_left (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _))
        K.coe_nonneg)
  · exact (LipschitzWith.uniformEquicontinuous _ K (fun x => x.2.1)).equicontinuous

end BoundedContinuousFunction
