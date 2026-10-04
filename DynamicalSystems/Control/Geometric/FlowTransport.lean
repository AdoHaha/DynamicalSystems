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
point. These pre-G12 per-point results make no claim about the entire original
flow box or about uniformity in the initial point; the G12 section below proves
uniformity across fibers on a smaller concentric ball, closing the residual
hypotheses of the box commuting reduction unconditionally
(`flowsCommute_unconditional_onBox`).
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

/-! ## G12: uniform variational theory across fibers (Hartman, Ch. V; Sontag, Ch. 4)

This section discharges the uniform residuals `hDiffInv`/`hTransU` of
`flowsCommute_of_uniformResiduals_onBox` (see `FlowCommutator.lean`) from `C¹`-on-the-box
data alone. The per-fiber facts (`eventually_differentiableAt_localFlow`,
`eventually_isInvertible_fderiv_localFlow`, `lieDerivative_along_flow_onBox`) each carry
their own `y`-dependent time neighbourhood; here a SINGLE time radius works for every
fiber at once. The uniformity comes from finite-dimensional compactness: the common
coefficient bound `CommonFlowDomain.uniform_fderiv_bound` over the compact box makes the
Picard existence time for the tangent ODE independent of the base point, and the uniform
Taylor remainder (`ContDiffAt.exists_uniform_fderiv_remainder`) makes the Gronwall
constant independent of the fiber. The invariant is respected throughout: the common
domain is fixed FIRST, and only afterwards are the time radius and the working ball
shrunk.

Honest scope: uniformity is proved on a SMALLER concentric ball `ball x₀ ρ` (whose
existence is part of each statement), not on the whole `closedBall x₀ D.r`. The common
flow `localFlow D.hf0` is only defined on the base flow box, and the Taylor remainder
ball sits inside it; shrinking is what makes one radius work for all fibers. Full-box
uniformity would additionally need uniform nonlinear-flow data and is not claimed.
References: Hartman, *Ordinary Differential Equations*, Ch. V (differentiable dependence
on initial data); Sontag, *Mathematical Control Theory*, Ch. 4 §4.2/§4.4 (the `Ad`
operator and Lemma 4.4.2). No originality is claimed.
-/

/-- Uniform tangent data on a smaller concentric ball (Hartman, Ch. V): on a
`CommonFlowDomain`, one time radius `T > 0` and one spatial ball `ball x₀ ρ` work for
EVERY base point at once. For each `y`, some `J` solves the tangent ODE along the
common trajectory through `y` starting from the identity, and is identified with the
spatial derivative of the common flow at `y`. The Picard existence time is uniform because the
coefficient bound `C₀` (from `CommonFlowDomain.uniform_fderiv_bound`) is valid over the
whole box; the Gronwall identification is uniform because the Taylor remainder ball is
fixed at `x₀`. This master lemma feeds `uniformDifferentiability_onBox`,
`uniformInvertibility_onBox` and `uniformTransport_onBox` below. -/
theorem uniformTangentSolution_onBox
    {f g : X → X} {x₀ : X} (D : CommonFlowDomain f g x₀) :
    ∃ T > 0, ∃ ρ > 0, ∀ y ∈ Metric.ball x₀ ρ, ∃ J : ℝ → X →L[ℝ] X,
      J 0 = ContinuousLinearMap.id ℝ X ∧
      (∀ t : ℝ, |t| < T → HasDerivAt J
        ((fderiv ℝ f (localFlow D.hf0 t y)).comp (J t)) t) ∧
      (∀ t : ℝ, |t| < T → HasFDerivAt (localFlow D.hf0 t) (J t) y) := by
  -- Uniform Taylor remainder at `x₀` (finite-dimensional compactness).
  obtain ⟨rT, hrT, hTaylor⟩ := D.hf0.exists_uniform_fderiv_remainder
  -- Common coefficient bound over the box.
  obtain ⟨C₀, hC₀⟩ := D.uniform_fderiv_bound
  have hx₀mem : x₀ ∈ Metric.closedBall x₀ D.r :=
    Metric.mem_closedBall_self D.hr.le
  have hC₀nn : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ x₀ hx₀mem).1
  -- Uniform trajectory invariance from G11.
  obtain ⟨δ₀, hδ₀, ρ₀, hρ₀, hmem⟩ := uniformFlowInvariance D
  -- Trajectories from a uniform product neighbourhood stay in the Taylor ball.
  have hΦ0 : localFlow D.hf0 0 x₀ = x₀ := localFlow_zero_apply f x₀ D.hf0
  have hflow : Filter.Tendsto (fun p : ℝ × X ↦ localFlow D.hf0 p.1 p.2)
      (𝓝 (0, x₀)) (𝓝 x₀) := by
    have h := (localFlow_continuousAt f x₀ D.hf0).tendsto
    rwa [hΦ0] at h
  obtain ⟨b, hb, hbflow⟩ := Metric.eventually_nhds_iff_ball.mp
    (hflow.eventually (Metric.ball_mem_nhds x₀ hrT))
  -- Uniform constants (all from `x₀`-data and the box bound).
  set K : ℝ := C₀ + 1 with hKdef
  have hKpos : 0 < K := by linarith
  have hC₀K : C₀ ≤ K := by linarith
  set L₀ : ℝ := C₀ * (1 + ‖ContinuousLinearMap.id ℝ X‖) + 1 with hL₀def
  have hL₀pos : 0 < L₀ := by
    have h1 : (0 : ℝ) ≤ 1 + ‖ContinuousLinearMap.id ℝ X‖ := by positivity
    have h2 : (0 : ℝ) ≤ C₀ * (1 + ‖ContinuousLinearMap.id ℝ X‖) :=
      mul_nonneg hC₀nn h1
    rw [hL₀def]
    linarith
  set b' : ℝ := min b (getLocalFlowData D.hf0).r with hb'def
  have hb'pos : 0 < b' := lt_min hb (getLocalFlowData D.hf0).hr
  have hb'b : b' ≤ b := min_le_left _ _
  have hb'dr : b' ≤ (getLocalFlowData D.hf0).r := min_le_right _ _
  set T₀ : ℝ := min δ₀ (min (getLocalFlowData D.hf0).ε b') with hT₀def
  have hT₀pos : 0 < T₀ :=
    lt_min hδ₀ (lt_min (getLocalFlowData D.hf0).hε hb'pos)
  have hT₀δ₀ : T₀ ≤ δ₀ := min_le_left _ _
  have hT₀ε : T₀ ≤ (getLocalFlowData D.hf0).ε :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hT₀b' : T₀ ≤ b' := (min_le_right _ _).trans (min_le_right _ _)
  set ρ : ℝ := min ρ₀ (b' / 2) with hρdef
  have hρpos : 0 < ρ := lt_min hρ₀ (by linarith)
  have hρ₀le : ρ ≤ ρ₀ := min_le_left _ _
  have hρble : ρ ≤ b' / 2 := min_le_right _ _
  have hρdr : ρ ≤ (getLocalFlowData D.hf0).r :=
    le_trans hρble (le_trans (by linarith [hb'pos.le]) hb'dr)
  -- Uniform Picard time for the tangent ODE (same `C₀`, same initial value).
  set δP : ℝ := min (T₀ / 2) (1 / L₀) with hδPdef
  have hδPpos : 0 < δP :=
    lt_min (by linarith) (one_div_pos.mpr hL₀pos)
  have hδPle : δP ≤ T₀ / 2 := min_le_left _ _
  have hδPT₀le : δP ≤ T₀ := le_trans hδPle (by linarith [hT₀pos.le])
  have hδPltT : δP < T₀ := lt_of_le_of_lt hδPle (by linarith [hT₀pos])
  set C : ℝ := (Real.exp (K * δP) - 1) / K with hCdef
  have hCpos : 0 < C := gronwall_symmetric_multiplier_pos hδPpos hKpos
  -- Working-scale invariance and membership facts.
  have hinv : ∀ y ∈ Metric.ball x₀ ρ, ∀ t : ℝ, |t| < T₀ →
      localFlow D.hf0 t y ∈ Metric.closedBall x₀ D.r := by
    intro y hy t ht
    exact (hmem t (lt_of_lt_of_le ht hT₀δ₀) y
      (Metric.ball_subset_ball hρ₀le hy)).1
  have hmemBall : ∀ y ∈ Metric.ball x₀ ρ,
      y ∈ Metric.closedBall x₀ (getLocalFlowData D.hf0).r := by
    intro y hy
    rw [Metric.mem_closedBall]
    exact le_of_lt (lt_of_lt_of_le (Metric.mem_ball.mp hy) hρdr)
  have hblt : ∀ y ∈ Metric.ball x₀ ρ, ∀ t : ℝ, |t| < T₀ →
      localFlow D.hf0 t y ∈ Metric.ball x₀ rT := by
    intro y hy t ht
    apply hbflow (t, y)
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_0_eq_abs]
    refine max_lt (lt_of_lt_of_le ht (le_trans hT₀b' hb'b)) ?_
    exact lt_of_lt_of_le (Metric.mem_ball.mp hy)
      (le_trans hρble (le_trans (by linarith [hb'pos.le]) hb'b))
  have hAcont : ∀ y ∈ Metric.ball x₀ ρ,
      ContinuousOn (fun t : ℝ ↦ fderiv ℝ f (localFlow D.hf0 t y))
        (Metric.closedBall (0 : ℝ) (T₀ / 2)) := by
    intro y hy u hu
    have huT : |u| < T₀ := by
      have hle : |u| ≤ T₀ / 2 := by
        have hmem := Metric.mem_closedBall.mp hu
        rwa [Real.dist_0_eq_abs] at hmem
      linarith [hT₀pos]
    have hut : u ∈ Set.Ioo (-T₀) T₀ := abs_lt.mp huT
    have hΦmem : localFlow D.hf0 u y ∈ Metric.closedBall x₀ D.r :=
      hinv y hy u huT
    have htime : u ∈ Set.Ioo (-(getLocalFlowData D.hf0).ε)
        (getLocalFlowData D.hf0).ε :=
      ⟨lt_of_le_of_lt (neg_le_neg hT₀ε) hut.1, lt_of_lt_of_le hut.2 hT₀ε⟩
    have h1 : ContinuousAt (fun z : X ↦ fderiv ℝ f z) (localFlow D.hf0 u y) :=
      (D.hf _ hΦmem).continuousAt_fderiv one_ne_zero
    have h2 : ContinuousAt (fun u : ℝ ↦ localFlow D.hf0 u y) u :=
      ((getLocalFlowData D.hf0).ϕ_hasDerivAt u htime y (hmemBall y hy)).continuousAt
    exact (ContinuousAt.comp (g := fun z : X ↦ fderiv ℝ f z)
      (f := fun u : ℝ ↦ localFlow D.hf0 u y) (x := u) h1 h2).continuousWithinAt
  have hAbound : ∀ y ∈ Metric.ball x₀ ρ, ∀ u ∈ Set.Icc (-δP) δP,
      ‖fderiv ℝ f (localFlow D.hf0 u y)‖ ≤ C₀ := by
    intro y hy u hu
    have huT : |u| < T₀ := lt_of_le_of_lt (abs_le.mpr hu) hδPltT
    exact (hC₀ _ (hinv y hy u huT)).1
  -- Per-fiber construction with uniform time `δP`.
  have hmain : ∀ y ∈ Metric.ball x₀ ρ, ∃ Jy : ℝ → X →L[ℝ] X,
      Jy 0 = ContinuousLinearMap.id ℝ X ∧
      (∀ t : ℝ, |t| < δP → HasDerivAt Jy
        ((fderiv ℝ f (localFlow D.hf0 t y)).comp (Jy t)) t) ∧
      (∀ t : ℝ, |t| < δP → HasFDerivAt (localFlow D.hf0 t) (Jy t) y) := by
    intro y hy
    have hsubIcc : Set.Icc (-δP) δP ⊆ Metric.closedBall (0 : ℝ) (T₀ / 2) := by
      intro u hu
      rw [Metric.mem_closedBall, Real.dist_0_eq_abs]
      exact le_trans (abs_le.mpr hu) hδPle
    have hδPL : L₀ * δP ≤ 1 := by
      have h : δP ≤ 1 / L₀ := min_le_right _ _
      have h' := (le_div_iff₀ hL₀pos).mp h
      rwa [mul_comm] at h'
    have hpl : IsPicardLindelof
        (fun t Y ↦ (fderiv ℝ f (localFlow D.hf0 t y)).comp Y)
        (tmin := -δP) (tmax := δP)
        ⟨0, ⟨by linarith [hδPpos], hδPpos.le⟩⟩
        (ContinuousLinearMap.id ℝ X) 1 0 ⟨L₀, hL₀pos.le⟩ ⟨C₀, hC₀nn⟩ := by
      constructor
      · intro t ht
        refine (lipschitzOnWith_iff_dist_le_mul).mpr ?_
        intro Y₁ _ Y₂ _
        change dist ((fderiv ℝ f (localFlow D.hf0 t y)).comp Y₁)
            ((fderiv ℝ f (localFlow D.hf0 t y)).comp Y₂) ≤
            (⟨C₀, hC₀nn⟩ : NNReal) * dist Y₁ Y₂
        have hsub : (fderiv ℝ f (localFlow D.hf0 t y)).comp Y₁
            - (fderiv ℝ f (localFlow D.hf0 t y)).comp Y₂
            = (fderiv ℝ f (localFlow D.hf0 t y)).comp (Y₁ - Y₂) := by
          have h := map_sub (ContinuousLinearMap.compL ℝ X X X
            (fderiv ℝ f (localFlow D.hf0 t y))) Y₁ Y₂
          simpa only [ContinuousLinearMap.compL_apply] using h.symm
        change dist ((fderiv ℝ f (localFlow D.hf0 t y)).comp Y₁)
            ((fderiv ℝ f (localFlow D.hf0 t y)).comp Y₂) ≤
            (⟨C₀, hC₀nn⟩ : NNReal) * dist Y₁ Y₂
        rw [dist_eq_norm, dist_eq_norm, hsub]
        have hAb : ‖fderiv ℝ f (localFlow D.hf0 t y)‖ ≤ C₀ :=
          hAbound y hy t ht
        calc ‖(fderiv ℝ f (localFlow D.hf0 t y)).comp (Y₁ - Y₂)‖
            ≤ ‖fderiv ℝ f (localFlow D.hf0 t y)‖ * ‖Y₁ - Y₂‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ C₀ * ‖Y₁ - Y₂‖ :=
              mul_le_mul_of_nonneg_right hAb (norm_nonneg _)
      · intro Y _
        change ContinuousOn
          (fun t : ℝ ↦ (fderiv ℝ f (localFlow D.hf0 t y)).comp Y)
          (Set.Icc (-δP) δP)
        have h1 : ContinuousOn
            (fun t : ℝ ↦ ContinuousLinearMap.compL ℝ X X X
              (fderiv ℝ f (localFlow D.hf0 t y))) (Set.Icc (-δP) δP) :=
          (ContinuousLinearMap.compL ℝ X X X).continuous.comp_continuousOn
            ((hAcont y hy).mono hsubIcc)
        have h2 : ContinuousOn (fun t : ℝ ↦ (ContinuousLinearMap.compL ℝ X X X
            (fderiv ℝ f (localFlow D.hf0 t y))) Y) (Set.Icc (-δP) δP) :=
          h1.clm_apply (continuousOn_const (c := Y))
        simpa only [ContinuousLinearMap.compL_apply] using h2
      · intro t ht Y hY
        change ‖(fderiv ℝ f (localFlow D.hf0 t y)).comp Y‖ ≤ _
        have hAb : ‖fderiv ℝ f (localFlow D.hf0 t y)‖ ≤ C₀ :=
          hAbound y hy t ht
        have hYnorm : ‖Y‖ ≤ 1 + ‖ContinuousLinearMap.id ℝ X‖ := by
          have hle : ‖Y - ContinuousLinearMap.id ℝ X‖ ≤ (1 : ℝ) := by
            simpa only [dist_eq_norm, NNReal.coe_one] using
              Metric.mem_closedBall.mp hY
          calc ‖Y‖ ≤ ‖Y - ContinuousLinearMap.id ℝ X‖
                + ‖ContinuousLinearMap.id ℝ X‖ :=
              norm_le_norm_sub_add Y _
            _ ≤ 1 + ‖ContinuousLinearMap.id ℝ X‖ := by linarith [hle]
        calc ‖(fderiv ℝ f (localFlow D.hf0 t y)).comp Y‖
            ≤ ‖fderiv ℝ f (localFlow D.hf0 t y)‖ * ‖Y‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ C₀ * (1 + ‖ContinuousLinearMap.id ℝ X‖) :=
              mul_le_mul hAb hYnorm (norm_nonneg _) hC₀nn
          _ ≤ L₀ := by rw [hL₀def]; linarith
      · change L₀ * max (δP - 0) (0 - -δP) ≤ (1 : ℝ) - 0
        simpa only [sub_zero, zero_sub, neg_neg, max_self] using hδPL
    obtain ⟨Jy, hJy0, hJy⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    have hJyode : ∀ t : ℝ, |t| < δP → HasDerivAt Jy
        ((fderiv ℝ f (localFlow D.hf0 t y)).comp (Jy t)) t := by
      intro t ht
      have ht' : t ∈ Set.Ioo (-δP) δP := abs_lt.mp ht
      exact (hJy t (Set.Ioo_subset_Icc_self ht')).hasDerivAt
        (Icc_mem_nhds ht'.1 ht'.2)
    have huT₀ : ∀ u ∈ Set.Ioo (-δP) δP, |u| < T₀ := fun u hu ↦
      lt_of_lt_of_le (abs_lt.mpr hu) hδPT₀le
    refine ⟨Jy, hJy0, hJyode, ?_⟩
    intro t ht
    have htIoo : t ∈ Set.Ioo (-δP) δP := abs_lt.mp ht
    apply HasFDerivAt.of_isLittleO
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    set η : ℝ := c / (C * (((getLocalFlowData D.hf0).L' : ℝ) + 1)) with hηdef
    have hL₁ : (0 : ℝ) < ((getLocalFlowData D.hf0).L' : ℝ) + 1 := by
      have hnn := NNReal.coe_nonneg (getLocalFlowData D.hf0).L'
      linarith
    have hη : 0 < η := div_pos hc (mul_pos hCpos hL₁)
    obtain ⟨δTay, hδTay, hrem⟩ := hTaylor η hη
    set σ : ℝ := min (b' / 2)
      (δTay / (((getLocalFlowData D.hf0).L' : ℝ) + 1)) with hσdef
    have hσpos : 0 < σ :=
      lt_min (by linarith [hb'pos]) (div_pos hδTay hL₁)
    filter_upwards [Metric.ball_mem_nhds y hσpos] with z hz
    have hzdist : dist z x₀ < b' := by
      have hzy : dist z y < σ := Metric.mem_ball.mp hz
      have hyx : dist y x₀ < ρ := Metric.mem_ball.mp hy
      have hσb : σ ≤ b' / 2 := min_le_left _ _
      calc dist z x₀ ≤ dist z y + dist y x₀ := dist_triangle _ _ _
        _ < σ + ρ := add_lt_add hzy hyx
        _ ≤ b' / 2 + b' / 2 := add_le_add hσb hρble
        _ = b' := by ring
    have hzmem : z ∈ Metric.closedBall x₀ (getLocalFlowData D.hf0).r :=
      Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hzdist hb'dr))
    have hboxz : ∀ u ∈ Set.Ioo (-δP) δP,
        localFlow D.hf0 u z ∈ Metric.ball x₀ rT := by
      intro u hu
      apply hbflow (u, z)
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_0_eq_abs]
      exact max_lt (lt_of_lt_of_le (huT₀ u hu) (le_trans hT₀b' hb'b))
        (lt_of_lt_of_le hzdist hb'b)
    have hΦdist : ∀ u ∈ Set.Ioo (-δP) δP,
        ‖localFlow D.hf0 u z - localFlow D.hf0 u y‖
          ≤ ((getLocalFlowData D.hf0).L' : ℝ) * ‖z - y‖ := by
      intro u hu
      have huIcc : u ∈ Set.Icc (-(getLocalFlowData D.hf0).ε)
          (getLocalFlowData D.hf0).ε :=
        Set.Ioo_subset_Icc_self
          (abs_lt.mp (lt_of_lt_of_le (huT₀ u hu) hT₀ε))
      have hlip := ((getLocalFlowData D.hf0).ϕ_lipschitz u huIcc).dist_le_mul
        z hzmem y (hmemBall y hy)
      simpa only [dist_eq_norm, localFlow] using hlip
    have hdist : ‖z - y‖
        < δTay / (((getLocalFlowData D.hf0).L' : ℝ) + 1) := by
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
    have hΦclose : ∀ u ∈ Set.Ioo (-δP) δP,
        dist (localFlow D.hf0 u z) (localFlow D.hf0 u y) < δTay := by
      intro u hu
      rw [dist_eq_norm]
      calc ‖localFlow D.hf0 u z - localFlow D.hf0 u y‖
            ≤ ((getLocalFlowData D.hf0).L' : ℝ) * ‖z - y‖ := hΦdist u hu
        _ ≤ (((getLocalFlowData D.hf0).L' : ℝ) + 1) * ‖z - y‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            linarith [NNReal.coe_nonneg (getLocalFlowData D.hf0).L']
        _ < δTay := by
            have h := (mul_lt_mul_iff_right₀ hL₁).mpr hdist
            simpa only [mul_div_cancel₀ _ (ne_of_gt hL₁)] using h
    have he₀ : (fun w : ℝ ↦ localFlow D.hf0 w z - localFlow D.hf0 w y
        - Jy w (z - y)) 0 = 0 := by
      have hz₀ : localFlow D.hf0 0 z = z :=
        (getLocalFlowData D.hf0).ϕ_zero z hzmem
      have hy₀ : localFlow D.hf0 0 y = y :=
        (getLocalFlowData D.hf0).ϕ_zero y (hmemBall y hy)
      simp only [hz₀, hy₀, hJy0, ContinuousLinearMap.id_apply, sub_self]
    have he : ∀ u ∈ Set.Ioo (-δP) δP, HasDerivAt
        (fun w : ℝ ↦ localFlow D.hf0 w z - localFlow D.hf0 w y
          - Jy w (z - y))
        (f (localFlow D.hf0 u z) - f (localFlow D.hf0 u y)
          - (fderiv ℝ f (localFlow D.hf0 u y)) (Jy u (z - y))) u := by
      intro u hu
      have htime : u ∈ Set.Ioo (-(getLocalFlowData D.hf0).ε)
          (getLocalFlowData D.hf0).ε :=
        abs_lt.mp (lt_of_lt_of_le (huT₀ u hu) hT₀ε)
      have h₁ : HasDerivAt (fun w : ℝ ↦ localFlow D.hf0 w z)
          (f (localFlow D.hf0 u z)) u :=
        (getLocalFlowData D.hf0).ϕ_hasDerivAt u htime z hzmem
      have h₂ : HasDerivAt (fun w : ℝ ↦ localFlow D.hf0 w y)
          (f (localFlow D.hf0 u y)) u :=
        (getLocalFlowData D.hf0).ϕ_hasDerivAt u htime y (hmemBall y hy)
      have h₃ : HasDerivAt (fun w : ℝ ↦ Jy w (z - y))
          ((fderiv ℝ f (localFlow D.hf0 u y)) (Jy u (z - y))) u := by
        simpa using (hJyode u (abs_lt.mpr hu)).clm_apply
          (hasDerivAt_const u (z - y))
      exact (h₁.sub h₂).sub h₃
    have hbound : ∀ u ∈ Set.Ioo (-δP) δP,
        ‖f (localFlow D.hf0 u z) - f (localFlow D.hf0 u y)
          - (fderiv ℝ f (localFlow D.hf0 u y)) (Jy u (z - y))‖
        ≤ K * ‖localFlow D.hf0 u z - localFlow D.hf0 u y - Jy u (z - y)‖
          + η * ((getLocalFlowData D.hf0).L' : ℝ) * ‖z - y‖ := by
      intro u hu
      have herr : (f (localFlow D.hf0 u z) - f (localFlow D.hf0 u y)
          - (fderiv ℝ f (localFlow D.hf0 u y)) (Jy u (z - y)))
          = (f (localFlow D.hf0 u z) - f (localFlow D.hf0 u y)
            - (fderiv ℝ f (localFlow D.hf0 u y))
              (localFlow D.hf0 u z - localFlow D.hf0 u y))
          + (fderiv ℝ f (localFlow D.hf0 u y))
            (localFlow D.hf0 u z - localFlow D.hf0 u y - Jy u (z - y)) := by
        simp only [map_sub]
        abel
      have hR : ‖f (localFlow D.hf0 u z) - f (localFlow D.hf0 u y)
          - (fderiv ℝ f (localFlow D.hf0 u y))
            (localFlow D.hf0 u z - localFlow D.hf0 u y)‖
          ≤ η * ‖localFlow D.hf0 u z - localFlow D.hf0 u y‖ :=
        hrem _ (hboxz u hu) _ (hblt y hy u (huT₀ u hu)) (hΦclose u hu)
      rw [herr]
      calc ‖(f (localFlow D.hf0 u z) - f (localFlow D.hf0 u y)
            - (fderiv ℝ f (localFlow D.hf0 u y))
              (localFlow D.hf0 u z - localFlow D.hf0 u y))
          + (fderiv ℝ f (localFlow D.hf0 u y))
            (localFlow D.hf0 u z - localFlow D.hf0 u y - Jy u (z - y))‖
          ≤ ‖f (localFlow D.hf0 u z) - f (localFlow D.hf0 u y)
            - (fderiv ℝ f (localFlow D.hf0 u y))
              (localFlow D.hf0 u z - localFlow D.hf0 u y)‖
            + ‖(fderiv ℝ f (localFlow D.hf0 u y))
              (localFlow D.hf0 u z - localFlow D.hf0 u y - Jy u (z - y))‖ :=
            norm_add_le _ _
        _ ≤ η * ‖localFlow D.hf0 u z - localFlow D.hf0 u y‖
            + ‖fderiv ℝ f (localFlow D.hf0 u y)‖
              * ‖localFlow D.hf0 u z - localFlow D.hf0 u y - Jy u (z - y)‖ :=
            add_le_add hR ((fderiv ℝ f (localFlow D.hf0 u y)).le_opNorm _)
        _ ≤ η * (((getLocalFlowData D.hf0).L' : ℝ) * ‖z - y‖)
            + K * ‖localFlow D.hf0 u z - localFlow D.hf0 u y
              - Jy u (z - y)‖ := by
            have g1 : η * ‖localFlow D.hf0 u z - localFlow D.hf0 u y‖
                ≤ η * (((getLocalFlowData D.hf0).L' : ℝ) * ‖z - y‖) :=
              mul_le_mul_of_nonneg_left (hΦdist u hu) (le_of_lt hη)
            have g2 : ‖fderiv ℝ f (localFlow D.hf0 u y)‖
                * ‖localFlow D.hf0 u z - localFlow D.hf0 u y - Jy u (z - y)‖
                ≤ K * ‖localFlow D.hf0 u z - localFlow D.hf0 u y
                  - Jy u (z - y)‖ :=
              mul_le_mul_of_nonneg_right
                (le_trans (hAbound y hy u (Set.Ioo_subset_Icc_self hu)) hC₀K)
                (norm_nonneg _)
            exact add_le_add g1 g2
        _ = K * ‖localFlow D.hf0 u z - localFlow D.hf0 u y - Jy u (z - y)‖
            + η * ((getLocalFlowData D.hf0).L' : ℝ) * ‖z - y‖ := by ring
    have hE := norm_le_gronwall_symmetric_uniform hδPpos hKpos
      (show (0 : ℝ) ≤ η * ((getLocalFlowData D.hf0).L' : ℝ) * ‖z - y‖ by
        positivity) he₀ he hbound htIoo
    calc ‖localFlow D.hf0 t z - localFlow D.hf0 t y - Jy t (z - y)‖
        ≤ C * (η * ((getLocalFlowData D.hf0).L' : ℝ) * ‖z - y‖) := hE
      _ ≤ C * (η * ((((getLocalFlowData D.hf0).L' : ℝ) + 1)) * ‖z - y‖) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos)
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hη)
          linarith [NNReal.coe_nonneg (getLocalFlowData D.hf0).L']
      _ = c * ‖z - y‖ := by
          have h1 : ((getLocalFlowData D.hf0).L' : ℝ) + 1 ≠ 0 := ne_of_gt hL₁
          have hC2 : C * (((getLocalFlowData D.hf0).L' : ℝ) + 1) ≠ 0 :=
            mul_ne_zero hCpos.ne' h1
          rw [hηdef]
          field_simp
  exact ⟨δP, hδPpos, ρ, hρpos, hmain⟩

/-- Uniform differentiability on the box (Hartman, Ch. V): on a `CommonFlowDomain`,
one radius `δ > 0` and one smaller ball `ball x₀ ρ` work for EVERY `y` at once — the
common `f`-flow is differentiable at `y` for `|t| < δ`, uniformly in `y`. This promotes
`eventually_differentiableAt_localFlow` from per-point to per-box data. -/
theorem uniformDifferentiability_onBox
    {f g : X → X} {x₀ : X} (D : CommonFlowDomain f g x₀) :
    ∃ δ > 0, ∃ ρ > 0, ∀ y ∈ Metric.ball x₀ ρ, ∀ t : ℝ, |t| < δ →
      DifferentiableAt ℝ (localFlow D.hf0 t) y := by
  obtain ⟨T, hT, ρ, hρ, hmain⟩ := uniformTangentSolution_onBox D
  refine ⟨T, hT, ρ, hρ, fun y hy t ht ↦ ?_⟩
  obtain ⟨Jy, -, -, hJident⟩ := hmain y hy
  exact (hJident t ht).differentiableAt

/-- Uniform invertibility on the box (Hartman, Ch. V): on a `CommonFlowDomain`, one
radius `δ > 0` and one smaller ball work for EVERY `y` at once — the spatial derivative
of the common flow is a unit for `|t| < δ`, uniformly in `y`. This promotes
`eventually_isInvertible_fderiv_localFlow` to per-box data, via the uniform tangent ODE
(a Gronwall bound gives `‖J - id‖ < 1` uniformly, and the geometric series supplies the
unit). -/
theorem uniformInvertibility_onBox
    {f g : X → X} {x₀ : X} (D : CommonFlowDomain f g x₀) :
    ∃ δ > 0, ∃ ρ > 0, ∀ y ∈ Metric.ball x₀ ρ, ∀ t : ℝ, |t| < δ →
      IsUnit (fderiv ℝ (localFlow D.hf0 t) y) := by
  obtain ⟨T, hT, ρ, hρ, hmain⟩ := uniformTangentSolution_onBox D
  obtain ⟨C₀, hC₀⟩ := D.uniform_fderiv_bound
  have hC₀nn : 0 ≤ C₀ := le_trans (norm_nonneg _)
    (hC₀ x₀ (Metric.mem_closedBall_self D.hr.le)).1
  set K : ℝ := C₀ + 1 with hKdef
  have hKpos : 0 < K := by linarith
  have hKne : K ≠ 0 := ne_of_gt hKpos
  obtain ⟨δ₀, hδ₀, ρ₀, hρ₀, hmem⟩ := uniformFlowInvariance D
  set T' : ℝ := min T δ₀ with hT'def
  have hT'pos : 0 < T' := lt_min hT hδ₀
  have hT'T : T' ≤ T := min_le_left _ _
  have hT'δ₀ : T' ≤ δ₀ := min_le_right _ _
  set ρ' : ℝ := min ρ ρ₀ with hρ'def
  have hρ'pos : 0 < ρ' := lt_min hρ hρ₀
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hρ'ρ₀ : ρ' ≤ ρ₀ := min_le_right _ _
  have hcont_exp : ContinuousAt (fun t : ℝ ↦ Real.exp (K * |t|)) 0 :=
    Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul continuousAt_id.abs)
  have hexp0 : Real.exp (K * |(0 : ℝ)|) < 3 / 2 := by
    rw [abs_zero, mul_zero, Real.exp_zero]; norm_num
  have hexp : ∀ᶠ t in 𝓝 (0 : ℝ), Real.exp (K * |t|) < 3 / 2 :=
    hcont_exp.eventually (Iio_mem_nhds hexp0)
  obtain ⟨δe, hδe, hDe⟩ := Metric.eventually_nhds_iff_ball.mp hexp
  set T₃ : ℝ := min T' δe with hT₃def
  have hT₃pos : 0 < T₃ := lt_min hT'pos hδe
  have hT₃T' : T₃ ≤ T' := min_le_left _ _
  have hT₃δe : T₃ ≤ δe := min_le_right _ _
  refine ⟨T₃, hT₃pos, ρ', hρ'pos, fun y hy t ht ↦ ?_⟩
  have hyρ : y ∈ Metric.ball x₀ ρ :=
    Metric.ball_subset_ball hρ'ρ hy
  have hyρ₀ : y ∈ Metric.ball x₀ ρ₀ :=
    Metric.ball_subset_ball hρ'ρ₀ hy
  obtain ⟨Jy, hJy0, hJyode, hJyident⟩ := hmain y hyρ
  have htT : |t| < T := lt_of_lt_of_le (lt_of_lt_of_le ht hT₃T') hT'T
  have htδe : dist t 0 < δe := by
    rw [Real.dist_0_eq_abs]
    exact lt_of_lt_of_le ht hT₃δe
  have hfderiv_eq : fderiv ℝ (localFlow D.hf0 t) y = Jy t :=
    (hJyident t htT).fderiv
  have hAb : ∀ u ∈ Set.Ioo (-T₃) T₃,
      ‖fderiv ℝ f (localFlow D.hf0 u y)‖ ≤ C₀ := by
    intro u hu
    have hut : |u| < δ₀ := lt_of_lt_of_le (abs_lt.mpr hu)
      (le_trans hT₃T' hT'δ₀)
    exact (hC₀ _ ((hmem u hut y hyρ₀).1)).1
  set η : ℝ := K * ‖ContinuousLinearMap.id ℝ X‖ with hηdef
  have hηnn : 0 ≤ η := by positivity
  have he0 : (fun u : ℝ ↦ Jy u - ContinuousLinearMap.id ℝ X) 0 = 0 := by
    simp only [hJy0, sub_self]
  have he : ∀ u ∈ Set.Ioo (-T₃) T₃, HasDerivAt
      (fun u : ℝ ↦ Jy u - ContinuousLinearMap.id ℝ X)
      ((fderiv ℝ f (localFlow D.hf0 u y)).comp (Jy u)) u := by
    intro u hu
    have hJu : |u| < T :=
      lt_of_lt_of_le (abs_lt.mpr hu) (le_trans hT₃T' hT'T)
    have h := (hJyode u hJu).sub_const (ContinuousLinearMap.id ℝ X)
    simpa only [sub_zero] using h
  have hbound : ∀ u ∈ Set.Ioo (-T₃) T₃,
      ‖(fderiv ℝ f (localFlow D.hf0 u y)).comp (Jy u)‖
        ≤ K * ‖Jy u - ContinuousLinearMap.id ℝ X‖
          + K * ‖ContinuousLinearMap.id ℝ X‖ := by
    intro u hu
    have h1 : ‖Jy u‖ ≤ ‖Jy u - ContinuousLinearMap.id ℝ X‖
        + ‖ContinuousLinearMap.id ℝ X‖ := by
      nth_rewrite 1 [← sub_add_cancel (Jy u)
        (ContinuousLinearMap.id ℝ X)]
      exact norm_add_le _ _
    calc ‖(fderiv ℝ f (localFlow D.hf0 u y)).comp (Jy u)‖
        ≤ ‖fderiv ℝ f (localFlow D.hf0 u y)‖ * ‖Jy u‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C₀ * (‖Jy u - ContinuousLinearMap.id ℝ X‖
          + ‖ContinuousLinearMap.id ℝ X‖) :=
          mul_le_mul (hAb u hu) h1 (norm_nonneg _) hC₀nn
      _ ≤ K * ‖Jy u - ContinuousLinearMap.id ℝ X‖
          + K * ‖ContinuousLinearMap.id ℝ X‖ := by
          have g1 : C₀ * ‖Jy u - ContinuousLinearMap.id ℝ X‖
              ≤ K * ‖Jy u - ContinuousLinearMap.id ℝ X‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
          have g2 : C₀ * ‖ContinuousLinearMap.id ℝ X‖
              ≤ K * ‖ContinuousLinearMap.id ℝ X‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
          rw [mul_add C₀ _ _]; exact add_le_add g1 g2
  have htIoo : t ∈ Set.Ioo (-T₃) T₃ := abs_lt.mp ht
  have hEst := norm_le_gronwall_symmetric hT₃pos hKpos he0 he hbound htIoo
  have hexp_t : Real.exp (K * |t|) < 3 / 2 := hDe t
    (Metric.mem_ball.mpr htδe)
  have hid1le : ‖ContinuousLinearMap.id ℝ X‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x ↦ by simp)
  have hηK : η / K = ‖ContinuousLinearMap.id ℝ X‖ := by
    rw [div_eq_iff hKne, hηdef]; ring
  have hnorm : ‖Jy t - ContinuousLinearMap.id ℝ X‖ < 1 := by
    have hexp1 : (1 : ℝ) ≤ Real.exp (K * |t|) := by
      have hnn : (0 : ℝ) ≤ K * |t| :=
        mul_nonneg (le_of_lt hKpos) (abs_nonneg _)
      linarith [Real.add_one_le_exp (K * |t|)]
    calc ‖Jy t - ContinuousLinearMap.id ℝ X‖
        ≤ (η / K) * (Real.exp (K * |t|) - 1) := hEst
      _ = ‖ContinuousLinearMap.id ℝ X‖ * (Real.exp (K * |t|) - 1) := by
          rw [hηK]
      _ ≤ 1 * (Real.exp (K * |t|) - 1) := by
          apply mul_le_mul_of_nonneg_right hid1le (by linarith [hexp1])
      _ < 1 := by
          have h32 : Real.exp (K * |t|) - 1 < 1 / 2 := by linarith [hexp_t]
          linarith [h32]
  have hid1 : (1 : X →L[ℝ] X) = ContinuousLinearMap.id ℝ X := rfl
  have hunit : IsUnit (Jy t) := by
    have h := IsUnit.one_sub_of_norm_lt_one
      (x := (1 : X →L[ℝ] X) - Jy t) ?_
    · rwa [hid1, sub_sub_cancel] at h
    · rw [hid1, ← neg_sub, norm_neg]
      exact hnorm
  rw [hfderiv_eq]
  exact hunit

/-- Uniform transport on the box (Sontag Lemma 4.4.2, uniform-in-`y` form): on a
`CommonFlowDomain`, one radius `δ > 0` and one smaller ball work for EVERY `y` at
once — `∂ₜ (Φₜ)^* g (y) = (Φₜ)^* [f, g] (y)` for `|t| < δ`, uniformly in `y`. This
promotes `lieDerivative_along_flow_onBox` (whose time neighbourhood depends on `y`) to
a single-`δ` statement, using the uniform tangent ODE and uniform invertibility above.
Both fields are needed `C¹` only on the box. -/
theorem uniformTransport_onBox
    {f g : X → X} {x₀ : X} (D : CommonFlowDomain f g x₀) :
    ∃ δ > 0, ∃ ρ > 0, ∀ y ∈ Metric.ball x₀ ρ, ∀ t : ℝ, |t| < δ →
      HasDerivAt (fun u ↦ VectorField.pullback ℝ (localFlow D.hf0 u) g y)
        (VectorField.pullback ℝ (localFlow D.hf0 t) (lieBracket f g) y) t := by
  obtain ⟨T, hT, ρm, hρm, hmain⟩ := uniformTangentSolution_onBox D
  obtain ⟨δ₀, hδ₀, ρ₀, hρ₀, hmem⟩ := uniformFlowInvariance D
  obtain ⟨δ₂, hδ₂, ρ₂, hρ₂, hinvU⟩ := uniformInvertibility_onBox D
  set dε : ℝ := (getLocalFlowData D.hf0).ε with hdεdef
  have hdεpos : 0 < dε := (getLocalFlowData D.hf0).hε
  set dr : ℝ := (getLocalFlowData D.hf0).r with hdrdef
  have hdrpos : 0 < dr := (getLocalFlowData D.hf0).hr
  set δ : ℝ := min T (min δ₀ (min δ₂ dε)) with hδdef
  have hδpos : 0 < δ := lt_min hT (lt_min hδ₀ (lt_min hδ₂ hdεpos))
  have hδT : δ ≤ T := min_le_left _ _
  have hδδ₀ : δ ≤ δ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hδδ₂ : δ ≤ δ₂ := (min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _))
  have hδdε : δ ≤ dε := (min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _))
  set ρ : ℝ := min ρm (min ρ₀ (min ρ₂ dr)) with hρdef
  have hρpos : 0 < ρ := lt_min hρm (lt_min hρ₀ (lt_min hρ₂ hdrpos))
  have hρmle : ρ ≤ ρm := min_le_left _ _
  have hρ₀le : ρ ≤ ρ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hρ₂le : ρ ≤ ρ₂ := (min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _))
  have hρdr : ρ ≤ dr := (min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _))
  refine ⟨δ, hδpos, ρ, hρpos, fun y hy t ht ↦ ?_⟩
  have hyρm : y ∈ Metric.ball x₀ ρm := Metric.ball_subset_ball hρmle hy
  have hyρ₀ : y ∈ Metric.ball x₀ ρ₀ := Metric.ball_subset_ball hρ₀le hy
  have hyρ₂ : y ∈ Metric.ball x₀ ρ₂ := Metric.ball_subset_ball hρ₂le hy
  have hyballd : y ∈ Metric.closedBall x₀ (getLocalFlowData D.hf0).r := by
    rw [Metric.mem_closedBall]
    have : dr = (getLocalFlowData D.hf0).r := rfl
    rw [← this]
    exact le_of_lt (lt_of_lt_of_le (Metric.mem_ball.mp hy) hρdr)
  have htT : |t| < T := lt_of_lt_of_le ht hδT
  obtain ⟨Jy, -, hJyode, hJyident⟩ := hmain y hyρm
  have hJvar_t : HasDerivAt (fun u ↦ fderiv ℝ (localFlow D.hf0 u) y)
      ((fderiv ℝ f (localFlow D.hf0 t y)).comp (Jy t)) t := by
    have hIooT : Set.Ioo (-T) T ∈ 𝓝 t :=
      Ioo_mem_nhds (abs_lt.mp htT).1 (abs_lt.mp htT).2
    have heq : (fun u ↦ fderiv ℝ (localFlow D.hf0 u) y)
        =ᶠ[𝓝 t] (fun u ↦ Jy u) := by
      filter_upwards [hIooT] with u hu
      exact (hJyident u (abs_lt.mpr hu)).fderiv
    exact (hJyode t htT).congr_of_eventuallyEq heq
  have htδ₀ : |t| < δ₀ := lt_of_lt_of_le ht hδδ₀
  have htδ₂ : |t| < δ₂ := lt_of_lt_of_le ht hδδ₂
  have htime : t ∈ Set.Ioo (-(getLocalFlowData D.hf0).ε)
      (getLocalFlowData D.hf0).ε :=
    abs_lt.mp (lt_of_lt_of_le ht hδdε)
  obtain ⟨u, hu⟩ := hinvU y hyρ₂ t htδ₂
  have hfJ : fderiv ℝ (localFlow D.hf0 t) y = Jy t :=
    (hJyident t htT).fderiv
  have hInv : HasDerivAt
      (fun s ↦ Ring.inverse (fderiv ℝ (localFlow D.hf0 s) y))
      ((-ContinuousLinearMap.mulLeftRight ℝ (X →L[ℝ] X)
          (↑u⁻¹) (↑u⁻¹))
        ((fderiv ℝ f (localFlow D.hf0 t y)).comp
          (fderiv ℝ (localFlow D.hf0 t) y))) t := by
    have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hu] at h
    rw [hfJ]
    exact h.comp_hasDerivAt t hJvar_t
  have hΦ : HasDerivAt (fun s : ℝ ↦ localFlow D.hf0 s y)
      (f (localFlow D.hf0 t y)) t :=
    (getLocalFlowData D.hf0).ϕ_hasDerivAt t htime y hyballd
  have hgAt : ContDiffAt ℝ 1 g (localFlow D.hf0 t y) :=
    D.hg _ ((hmem t htδ₀ y hyρ₀).1)
  have hG : HasDerivAt (fun s ↦ g (localFlow D.hf0 s y))
      (fderiv ℝ g (localFlow D.hf0 t y) (f (localFlow D.hf0 t y))) t :=
    hgAt.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t hΦ
  have hprod := hInv.clm_apply hG
  have hfun : (fun s ↦ VectorField.pullback ℝ (localFlow D.hf0 s) g y) =
      fun s ↦ Ring.inverse (fderiv ℝ (localFlow D.hf0 s) y)
        (g (localFlow D.hf0 s y)) := by
    funext s
    rw [ContinuousLinearMap.ringInverse_eq_inverse]
    rfl
  rw [hfun]
  convert hprod using 1
  rw [VectorField.pullback, lieBracket_apply,
    ← ContinuousLinearMap.ringInverse_eq_inverse, ← hu]
  simp only [neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    ← ContinuousLinearMap.mul_def, mul_assoc, Units.mul_inv, mul_one,
    Ring.inverse_unit, mul_apply_eq_comp, map_sub]
  abel

/-- Flows commute near `x₀` with NO residual variational hypotheses (Sontag, Ch. 4
§4.2/§4.4; Hartman, Ch. V): on a `CommonFlowDomain` with `[f, g] = 0` on the box, the
base local flows commute near `(0, 0)`. The uniform residuals `hDiffInv`/`hTransU` of
`flowsCommute_of_uniformResiduals_onBox` are discharged by
`uniformDifferentiability_onBox`, `uniformInvertibility_onBox` and
`uniformTransport_onBox` above (uniform-`δ` variational theory across fibers), and the
box-invariance input `hFlow` by `uniformFlowInvariance`; the conclusion then follows
from `flowsCommute_of_bracketVanishing_onBox`. Hypotheses are only the common domain
and bracket vanishing. -/
theorem flowsCommute_unconditional_onBox
    {f g : X → X} {x₀ : X} (D : CommonFlowDomain f g x₀)
    (hbr : ∀ y ∈ Metric.closedBall x₀ D.r, lieBracket f g y = 0) :
    ∃ δ > 0, ∀ t ∈ Set.Ioo (-δ) δ, ∀ s ∈ Set.Ioo (-δ) δ,
      localFlow D.hf0 t (localFlow D.hg0 s x₀) =
        localFlow D.hg0 s (localFlow D.hf0 t x₀) := by
  obtain ⟨δ₁, hδ₁, ρ₁, hρ₁, hdiffU⟩ := uniformDifferentiability_onBox D
  obtain ⟨δ₂, hδ₂, ρ₂, hρ₂, hinvU⟩ := uniformInvertibility_onBox D
  obtain ⟨δ₃, hδ₃, ρ₃, hρ₃, htransU⟩ := uniformTransport_onBox D
  obtain ⟨δ₀, hδ₀, ρ₀, hρ₀, hmem⟩ := uniformFlowInvariance D
  set T : ℝ := min δ₁ (min δ₂ (min δ₃ δ₀)) with hTdef
  have hTpos : 0 < T := lt_min hδ₁ (lt_min hδ₂ (lt_min hδ₃ hδ₀))
  have hT₁ : T ≤ δ₁ := min_le_left _ _
  have hT₂ : T ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hT₃ : T ≤ δ₃ := (min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _))
  have hT₀ : T ≤ δ₀ := (min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _))
  set ρ : ℝ := min ρ₁ (min ρ₂ (min ρ₃ ρ₀)) with hρdef
  have hρpos : 0 < ρ := lt_min hρ₁ (lt_min hρ₂ (lt_min hρ₃ hρ₀))
  have hρ₁ : ρ ≤ ρ₁ := min_le_left _ _
  have hρ₂ : ρ ≤ ρ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hρ₃ : ρ ≤ ρ₃ := (min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _))
  have hρ₀ : ρ ≤ ρ₀ := (min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _))
  refine flowsCommute_of_bracketVanishing_onBox f g x₀ D hρpos hTpos hbr
    ?_ ?_ ?_ ?_
  · intro t ht y hy
    exact hdiffU y (Metric.ball_subset_ball hρ₁ hy) t
      (lt_of_lt_of_le (abs_lt.mpr ht) hT₁)
  · intro t ht y hy
    obtain ⟨u, hu⟩ := hinvU y (Metric.ball_subset_ball hρ₂ hy) t
      (lt_of_lt_of_le (abs_lt.mpr ht) hT₂)
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ X u, hu⟩
  · intro y hy t ht
    exact htransU y (Metric.ball_subset_ball hρ₃ hy) t
      (lt_of_lt_of_le (abs_lt.mpr ht) hT₃)
  · intro t ht y hy
    exact (hmem t (lt_of_lt_of_le (abs_lt.mpr ht) hT₀) y
      (Metric.ball_subset_ball hρ₀ hy)).1
