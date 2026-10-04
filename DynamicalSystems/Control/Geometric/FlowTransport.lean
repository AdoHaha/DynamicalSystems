/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.VariationalEquation

/-! # Local transport along a continuously differentiable flow

The spatial derivative of the flow is invertible near time zero. Differentiating
its inverse and using the variational equation proves the transported
Lie-derivative identity at every sufficiently small time, at the fixed initial
point. These results make no claim about the entire original flow box or about
uniformity in the initial point.
-/

@[expose] public section

open Set Filter
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]

/-- The spatial derivative of the local flow is a unit for sufficiently small
times, since it depends continuously on time and equals the identity at zero. -/
theorem eventually_isUnit_fderiv_localFlow
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (fderiv ℝ (localFlow hf t) x₀) := by
  have hnhds : {A : X →L[ℝ] X | IsUnit A} ∈
      𝓝 (fderiv ℝ (localFlow hf 0) x₀) := by
    rw [flow_deriv_at_zero f x₀ hf]
    exact Units.isOpen.mem_nhds (isUnit_one : IsUnit (1 : X →L[ℝ] X))
  exact (flow_deriv_firstOrder hf).continuousAt.eventually hnhds

/-- The local flow has invertible spatial derivative at its base point for all
sufficiently small times. -/
theorem eventually_isInvertible_fderiv_localFlow
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (fderiv ℝ (localFlow hf t) x₀).IsInvertible := by
  filter_upwards [eventually_isUnit_fderiv_localFlow hf] with t ht
  obtain ⟨u, hu⟩ := ht
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ X u, hu⟩

/-- The pullback of a `C¹` vector field along a `C¹` flow satisfies the
transported Lie-derivative identity at all sufficiently small times, at the
fixed initial point. The variational equation and invertibility are proved
consequences of the hypotheses. -/
theorem eventually_lieDerivative_along_flow
    {f g : X → X} {x₀ : X}
    (hf : ContDiffAt ℝ 1 f x₀) (hg : ContDiffAt ℝ 1 g x₀) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun u ↦ VectorField.pullback ℝ (localFlow hf u) g x₀)
        (VectorField.pullback ℝ (localFlow hf t) (lieBracket f g) x₀) t := by
  have htend : Tendsto (fun t ↦ localFlow hf t x₀) (𝓝 (0 : ℝ)) (𝓝 x₀) := by
    simpa only [localFlow_zero_apply f x₀ hf] using
      (localFlow_hasDerivAt_zero f x₀ hf).continuousAt.tendsto
  have htime : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun u ↦ localFlow hf u x₀) (f (localFlow hf t x₀)) t := by
    have hε := (getLocalFlowData hf).hε
    filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hε) hε] with t ht
    exact (getLocalFlowData hf).ϕ_hasDerivAt t ht x₀
      (Metric.mem_closedBall_self (getLocalFlowData hf).hr.le)
  filter_upwards [eventually_hasDerivAt_fderiv_localFlow hf,
    eventually_isUnit_fderiv_localFlow hf, htime,
    htend.eventually (hg.eventually (by simp))] with t hJ hu hΦ hg'
  obtain ⟨u, hu⟩ := hu
  have hInv : HasDerivAt
      (fun s ↦ Ring.inverse (fderiv ℝ (localFlow hf s) x₀))
      ((-ContinuousLinearMap.mulLeftRight ℝ (X →L[ℝ] X)
          (↑u⁻¹) (↑u⁻¹))
        ((fderiv ℝ f (localFlow hf t x₀)).comp
          (fderiv ℝ (localFlow hf t) x₀))) t := by
    have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hu] at h
    exact h.comp_hasDerivAt t hJ
  have hG : HasDerivAt (fun s ↦ g (localFlow hf s x₀))
      (fderiv ℝ g (localFlow hf t x₀) (f (localFlow hf t x₀))) t :=
    hg'.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t hΦ
  have hprod := hInv.clm_apply hG
  have hfun : (fun s ↦ VectorField.pullback ℝ (localFlow hf s) g x₀) =
      fun s ↦ Ring.inverse (fderiv ℝ (localFlow hf s) x₀) (g (localFlow hf s x₀)) := by
    funext s
    rw [ContinuousLinearMap.ringInverse_eq_inverse]
    rfl
  rw [hfun]
  convert hprod using 1
  rw [VectorField.pullback, lieBracket_apply, ← ContinuousLinearMap.ringInverse_eq_inverse,
    ← hu]
  simp only [neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    ← ContinuousLinearMap.mul_def, mul_assoc, Units.mul_inv, mul_one,
    Ring.inverse_unit, mul_apply_eq_comp, map_sub]
  abel

/-! ## Transport on the common box (GPT Pro follow-up, step 1)

This section implements step 1 of the follow-up plan recorded in
`docs/variational-equation.md` (\"Remaining Frobenius work\"): expose a common flow
domain and state transport on that box. The transported Lie-derivative identity,
proved above locally in time at a fixed base point, is lifted to EVERY point `y` of
a `CommonFlowDomain` box (see `FlowCommutator.lean`). References: Hartman,
*Ordinary Differential Equations*, Ch. V; Sontag, *Mathematical Control Theory*,
Ch. 4 §4.2/§4.4 (Lemma 4.4.2). No originality is claimed.

The invariant is respected: the common domain is fixed FIRST, and the coefficient
bound below is proved on that fixed box as an available building block.
`CommonFlowDomain.uniform_fderiv_bound` gives a single `C` bounding `‖Df‖` and
`‖Dg‖` over the whole closed box (compactness in finite dimensions plus `C¹`
continuity of the derivative at each point). It is a compactness bound only: the
Picard lemma `ContinuousOn.exists_local_linearODE_solution` in `TangentSolution.lean`
takes no coefficient-bound parameter and computes its own constant. The per-point
trajectory windows still vary with `y`; making the final time radius independent of
`y` (flow-agreement across fibers) remains open and is stated honestly here:
`lieDerivative_along_flow_onBox` gives the transported identity at every `y` of the
box, each on its own time neighbourhood. That neighbourhood depends on `y` and is
NOT uniform in `y`.
-/

omit [CompleteSpace X] in
/-- Coefficient bound on the common box: a single `C` dominates `‖Df‖` and `‖Dg‖` at
every point of the closed box (Hartman, Ch. V). This is an available building block
for the tangent ODE — a compactness bound on the derivatives over the box — not an
input to the Picard construction: `ContinuousOn.exists_local_linearODE_solution`
takes no coefficient-bound parameter and computes its own constant. -/
theorem CommonFlowDomain.uniform_fderiv_bound
    {f g : X → X} {x₀ : X} (D : CommonFlowDomain f g x₀) :
    ∃ C : ℝ, ∀ y ∈ Metric.closedBall x₀ D.r,
      ‖fderiv ℝ f y‖ ≤ C ∧ ‖fderiv ℝ g y‖ ≤ C := by
  have hcont_f : ContinuousOn (fun y ↦ fderiv ℝ f y) (Metric.closedBall x₀ D.r) := by
    intro y hy
    exact ((D.hf y hy).continuousAt_fderiv one_ne_zero).continuousWithinAt
  have hcont_g : ContinuousOn (fun y ↦ fderiv ℝ g y) (Metric.closedBall x₀ D.r) := by
    intro y hy
    exact ((D.hg y hy).continuousAt_fderiv one_ne_zero).continuousWithinAt
  obtain ⟨Cf, hCf⟩ :=
    (isCompact_closedBall x₀ D.r).exists_bound_of_continuousOn hcont_f
  obtain ⟨Cg, hCg⟩ :=
    (isCompact_closedBall x₀ D.r).exists_bound_of_continuousOn hcont_g
  exact ⟨max Cf Cg, fun y hy ↦
    ⟨le_max_of_le_left (hCf y hy), le_max_of_le_right (hCg y hy)⟩⟩

/-- Transport on the common box (Sontag Lemma 4.4.2, every-point form): on a common
flow domain, `∂ₜ (Φₜ)^* g (y) = (Φₜ)^* [f, g] (y)` holds eventually in time at
EVERY `y` of the box — not just at the base point — for the per-point local flow.
This is the box-localized lift of `eventually_lieDerivative_along_flow`; the time
neighbourhood it produces depends on `y`, so it is NOT uniform in `y`. Both fields
are needed `C¹` only on the box. -/
theorem lieDerivative_along_flow_onBox
    {f g : X → X} {x₀ : X} (D : CommonFlowDomain f g x₀)
    {y : X} (hy : y ∈ Metric.closedBall x₀ D.r) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun u ↦ VectorField.pullback ℝ (localFlow (D.hf y hy) u) g y)
        (VectorField.pullback ℝ (localFlow (D.hf y hy) t) (lieBracket f g) y) t :=
  eventually_lieDerivative_along_flow (D.hf y hy) (D.hg y hy)

/-- Time-zero transport at every point of the box, unconditionally: the pullback
of `g` along the flow of `f` through `y` has derivative `[f, g](y)` at `t = 0`.
The variational premise is discharged per fiber by `flow_deriv_firstOrder`. -/
theorem lieDerivative_timeZero_onBox
    {f g : X → X} {x₀ : X} (D : CommonFlowDomain f g x₀)
    {y : X} (hy : y ∈ Metric.closedBall x₀ D.r) :
    HasDerivAt (fun t : ℝ ↦ VectorField.pullback ℝ (localFlow (D.hf y hy) t) g y)
      (lieBracket f g y) 0 :=
  lieDerivative_along_flow_of_contDiffAt f g y (D.hf y hy) (D.hg y hy)

/-! ## G11 projection: single-flow uniform invariance (Hartman, Ch. V; Sontag, Ch. 4)

This is the one-flow projection of `uniformFlowInvariance` (proved in
`FlowCommutator.lean` to avoid a module cycle: `FlowCommutator` cannot import this
file). It records, for the `f`-flow alone, the uniform-δ conclusion used by the
flow-agreement step: one radius works for every initial point of a smaller ball.
-/

omit [FiniteDimensional ℝ X] in
/-- Single-flow projection of `uniformFlowInvariance`: on a `CommonFlowDomain`, one
radius `δ > 0` works for every `y ∈ ball x₀ δ` at once — the `f`-flow stays in the
box for `|t| < δ`, uniformly in `y`. -/
theorem uniformFlowInvariance_f
    {f g : X → X} {x₀ : X} (D : CommonFlowDomain f g x₀) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∀ y ∈ Metric.ball x₀ δ,
      localFlow D.hf0 t y ∈ Metric.closedBall x₀ D.r := by
  obtain ⟨δ, hδ, ρ, hρ, hmem⟩ := uniformFlowInvariance D
  refine ⟨min δ ρ, lt_min hδ hρ, fun t ht y hy ↦ ?_⟩
  have ht' : |t| < δ := lt_of_lt_of_le ht (min_le_left _ _)
  have hy' : y ∈ Metric.ball x₀ ρ :=
    Metric.ball_subset_ball (min_le_right _ _) hy
  exact (hmem t ht' y hy').1
