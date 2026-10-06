/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.CalculusOfVariations
public import DynamicalSystems.OptimalControl.ContinuousTime.FirstVariationDifferentiation
public import DynamicalSystems.OptimalControl.ContinuousTime.LagrangianCovectorRegularity

/-!
# Endpoint transversality (natural boundary) conditions

This file formalises the endpoint first-order conditions of an endpoint-penalized
calculus-of-variations functional

`F x = ∫₀ᵀ L(t, x t, x' t) dt + Φ₀(x 0) + Φ₁(x 0, x T)`,

i.e. the two transversality relations

`∂ᵥL(0, x 0, x' 0) = ∂Φ₀(x 0) + ∂₁Φ₁(x 0, x T)`,
`∂ᵥL(T, x T, x' T) = -∂₂Φ₁(x 0, x T)`.

For Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.6, the
functional above is the direct ODE penalty `F_{K(ε)}` of (11.3.6)/(11.6) with

* `L(t,x,v) = f⁰(t,x,ν^ε_t) + ‖v − φ₀'(t)‖² + K‖v − f(x,ν^ε_t,t)‖²`,
* `Φ₀(x) = |x − φ₀(0)|²`,
* `Φ₁(x,y) = K|T(x,y)|²`,

so that `∂ᵥL` is exactly the book's `ψ(ε;·)` of (11.6.8), `∂Φ₀(x 0) = 2(x 0 − φ₀(0))`, and
`∂₁Φ₁ = 2K T ∂₁T`, `∂₂Φ₁ = 2K T ∂₂T`.  The two relations are therefore the *consistent*
form of the printed endpoint conditions (11.6.15)–(11.6.16); the printed lines omit the
factor `2` on the initial penalty and the factor `T` in the endpoint-constraint gradients
(the report records this discrepancy, which is present in the book's own `F_K` as printed
in §11.6).  The book obtains them by varying `F` along the smooth bump `ζ` times the
exponential test functions `η_i(t) = e^{−Nt}` and letting `N → ∞`.  We instead isolate the
boundary terms by integrating the first variation by parts against the Euler–Lagrange
equation: this is the "cleaner rigorous route" and it produces the same relations (the
exponential limit is one way to see that the localized boundary directions are admissible).
Which route is taken, and what remains, is recorded in the slice report.

## What is proved and what is assumed

The endpoint conditions are *derived* from

* the Euler–Lagrange equation `eulerLagrange L T x` (itself obtained from the minimiser's
  first variation against endpoint-vanishing directions, the standard fixed-endpoint
  argument), and
* the first variation of the **full** functional vanishing against the localized endpoint
  directions `t ↦ c t • e` (an admissible direction near an endpoint where the state
  constraint is slack).

They are **not** a renaming of a weaker statement: the conclusion identifies the momentum
covector `∂ᵥL(0)` with the endpoint penalty gradients, in `E →L[ℝ] ℝ`, with no Riesz
identification introduced.

The declaration names are concept names; the book citation lives in the docstrings only.
-/

@[expose] public section

open Set MeasureTheory
open scoped Topology Interval

namespace OptimalControl.EndpointTransversality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The endpoint-penalized variational functional
`F x = ∫₀ᵀ L(t, x t, x' t) dt + Φ₀(x 0) + Φ₁(x 0, x T)`.

For Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.6, this is
the direct ODE penalty `F_{K(ε)}` of (11.3.6)/(11.6): the running Lagrangian carries the
running cost, the velocity-defect term and the pointwise dynamics-defect term, while `Φ₀`
is the initial-value penalty and `Φ₁` the endpoint-constraint penalty.

The index is `E`-valued; all covariant objects are genuine continuous linear maps
`E →L[ℝ] ℝ`. -/
noncomputable def penalizedFunctional
    (L : ℝ → E → E → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) (T : ℝ)
    (x : ℝ → E) : ℝ :=
  (∫ t in (0 : ℝ)..T, L t (x t) (deriv x t)) + Φ₀ (x 0) + Φ₁ (x 0, x T)

/-- The full first variation of `penalizedFunctional` at `x` in the direction `η`,
including the initial- and endpoint-penalty boundary terms.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012),
(11.6.9) and (11.6.14) (the boundary terms that the endpoint-vanishing test class of
(11.6.9) drops and the localized endpoint directions of (11.6.14) retain). -/
noncomputable def firstVariationWithEndpoints
    (L : ℝ → E → E → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) (T : ℝ)
    (x η : ℝ → E) : ℝ :=
  firstVariation L (fun _ => (0 : ℝ)) T x η
    + (fderiv ℝ Φ₀ (x 0)) (η 0)
    + (fderiv ℝ Φ₁ (x 0, x T)) (η 0, η T)

/-- The momentum covector `∂ᵥL(t, x t, x' t) ∈ E →L[ℝ] ℝ`.

For the §11.6 penalty this is the book's `ψ(ε;·)` of (11.6.8).

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012),
(11.6.8). -/
noncomputable def momentumCovector (L : ℝ → E → E → ℝ) (x : ℝ → E) (t : ℝ) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun v : E => L t (x t) v) (deriv x t)

/-- The state covector `∂ₓL(t, x t, x' t) ∈ E →L[ℝ] ℝ`.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012),
(11.6.9) (`f₁⁰`) and Theorem 11.6.3 (ii). -/
noncomputable def stateCovector (L : ℝ → E → E → ℝ) (x : ℝ → E) (t : ℝ) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun y : E => L t y (deriv x t)) (x t)

/-! ## The Gateaux derivative of the endpoint-penalized functional -/

/-- The full first variation written as the integral of the first-variation integrand plus the
initial- and endpoint-penalty boundary terms. -/
theorem firstVariationWithEndpoints_eq_integral
    (L : ℝ → E → E → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) (T : ℝ)
    (x η : ℝ → E) :
    firstVariationWithEndpoints L Φ₀ Φ₁ T x η =
      (∫ t in (0 : ℝ)..T, firstVariationIntegrand L x η t)
        + (fderiv ℝ Φ₀ (x 0)) (η 0)
        + (fderiv ℝ Φ₁ (x 0, x T)) (η 0, η T) := by
  unfold firstVariationWithEndpoints
  rw [firstVariation_eq_integrand]
  simp

/-- The first-variation integrand along a direction `t ↦ c t • e` is the derivative of the
scalar product of the momentum covector with the scalar profile. -/
theorem firstVariationIntegrand_smul_const
    (L : ℝ → E → E → ℝ) (x : ℝ → E) {c : ℝ → ℝ} (hc : ContDiff ℝ 1 c)
    (e : E) (t : ℝ) :
    firstVariationIntegrand L x (fun s => c s • e) t =
      (stateCovector L x t) e * c t + (momentumCovector L x t) e * deriv c t := by
  unfold firstVariationIntegrand stateCovector momentumCovector
  rw [deriv_smul_const ((hc.differentiable (by norm_num)) t) e]
  simp only [map_smul, smul_eq_mul]
  ring

/-- **Gateaux derivative of the endpoint-penalized functional.**  For a jointly `C¹` Lagrangian
and `C¹` penalties and perturbation, the derivative at `θ = 0` of `θ ↦ F(x + θ η)` is the full
first variation (running first variation plus the initial- and endpoint-penalty boundary terms).

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012),
(11.6.9) and (11.6.14). -/
theorem hasDerivAt_penalizedFunctional_affine
    (L : ℝ → E → E → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) (T : ℝ) (x η : ℝ → E)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hΦ₀ : ContDiff ℝ 1 Φ₀) (hΦ₁ : ContDiff ℝ 1 Φ₁)
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 1 η) (hT : 0 ≤ T) :
    HasDerivAt
      (fun ε : ℝ => penalizedFunctional L Φ₀ Φ₁ T (fun t => x t + ε • η t))
      (firstVariationWithEndpoints L Φ₀ Φ₁ T x η) 0 := by
  have hcv := hasDerivAt_cvFunctional_affine L (fun _ => (0 : ℝ)) T x η
    hL contDiff_const hx hη hT
  have hpath0 : HasDerivAt (fun ε : ℝ => x 0 + ε • η 0) (η 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (η 0)).const_add (x 0)
  have hpathT : HasDerivAt (fun ε : ℝ => x T + ε • η T) (η T) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (η T)).const_add (x T)
  have hΦ₀d : HasDerivAt (fun ε : ℝ => Φ₀ (x 0 + ε • η 0))
      ((fderiv ℝ Φ₀ (x 0)) (η 0)) 0 :=
    (show HasFDerivAt Φ₀ (fderiv ℝ Φ₀ (x 0)) (x 0 + (0 : ℝ) • η 0) from by
      simpa using ((hΦ₀.differentiable (by norm_num)) (x 0)).hasFDerivAt
      ).comp_hasDerivAt 0 hpath0
  have hΦ₁d : HasDerivAt (fun ε : ℝ => Φ₁ (x 0 + ε • η 0, x T + ε • η T))
      ((fderiv ℝ Φ₁ (x 0, x T)) (η 0, η T)) 0 :=
    (show HasFDerivAt Φ₁ (fderiv ℝ Φ₁ (x 0, x T))
        ((x 0 + (0 : ℝ) • η 0), (x T + (0 : ℝ) • η T)) from by
      simpa using ((hΦ₁.differentiable (by norm_num)) (x 0, x T)).hasFDerivAt
      ).comp_hasDerivAt 0 (hpath0.prodMk hpathT)
  have hsum := (hcv.add hΦ₀d).add hΦ₁d
  convert hsum using 1
  · funext ε
    simp only [penalizedFunctional, cvFunctional, Pi.add_apply]
    ring
  · rfl

/-- At a local minimum of the endpoint-penalized functional, the full first variation vanishes
in every `C¹` direction.  This is the one-sided-derivative step: both `η` and `-η` keep the
candidate admissible for small `θ`, so the derivative is squeezed to zero.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012),
(11.6.14) and the end-condition passage following it. -/
theorem firstVariationWithEndpoints_eq_zero_of_isLocalMin
    (L : ℝ → E → E → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) (T : ℝ) (x η : ℝ → E)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hΦ₀ : ContDiff ℝ 1 Φ₀) (hΦ₁ : ContDiff ℝ 1 Φ₁)
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 1 η) (hT : 0 ≤ T)
    (hmin : IsLocalMin
      (fun ε : ℝ => penalizedFunctional L Φ₀ Φ₁ T (fun t => x t + ε • η t)) 0) :
    firstVariationWithEndpoints L Φ₀ Φ₁ T x η = 0 :=
  IsLocalMin.hasDerivAt_eq_zero hmin
    (hasDerivAt_penalizedFunctional_affine L Φ₀ Φ₁ T x η hL hΦ₀ hΦ₁ hx hη hT)

/-! ## Integration by parts and the endpoint transversality relations -/

/-- Integration by parts for the first-variation integrand along a scalar-profile direction
`t ↦ c t • e`: under the Euler–Lagrange equation, the integral collapses to the difference of
the momentum covector paired with the profile at the two endpoints.

Docstring citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012),
(11.6.9)–(11.6.10) and the end-condition passage (11.6.14)–(11.6.16). -/
theorem integral_firstVariationIntegrand_smul_const
    (L : ℝ → E → E → ℝ) (x : ℝ → E) (e : E) {c : ℝ → ℝ} (hc : ContDiff ℝ 1 c)
    (T : ℝ) (hT : 0 < T)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (hx : ContDiff ℝ 1 x)
    (heuler : eulerLagrange L T x) :
    (∫ t in (0 : ℝ)..T, firstVariationIntegrand L x (fun s => c s • e) t)
      = (momentumCovector L x T) e * c T - (momentumCovector L x 0) e * c 0 := by
  have hderiv_e : ∀ t ∈ Ioo (min (0 : ℝ) T) (max (0 : ℝ) T),
      HasDerivAt (fun s : ℝ => (momentumCovector L x s) e) ((stateCovector L x t) e) t := by
    intro t ht
    rw [min_eq_left hT.le, max_eq_right hT.le] at ht
    have h1 : HasDerivAt (momentumCovector L x) (stateCovector L x t) t :=
      heuler t ⟨ht.1.le, ht.2.le⟩
    have h2 := h1.clm_apply (hasDerivAt_const (x := t) e)
    simpa using h2
  have hderiv_c : ∀ t ∈ Ioo (min (0 : ℝ) T) (max (0 : ℝ) T),
      HasDerivAt c (deriv c t) t := by
    intro t _
    exact ((hc.differentiable (by norm_num)) t).hasDerivAt
  have hu_cont : ContinuousOn (fun s : ℝ => (momentumCovector L x s) e) [[(0 : ℝ), T]] :=
    ((continuous_momentumCovector L x hL hx).clm_apply continuous_const).continuousOn
  have hv_cont : ContinuousOn c [[(0 : ℝ), T]] := hc.continuous.continuousOn
  have hu'_int : IntervalIntegrable (fun s : ℝ => (stateCovector L x s) e) volume 0 T :=
    ((continuous_stateCovector L x hL hx).clm_apply continuous_const).intervalIntegrable 0 T
  have hv'_int : IntervalIntegrable (deriv c) volume 0 T :=
    hc.continuous_deriv_one.intervalIntegrable 0 T
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    hu_cont hv_cont hderiv_e hderiv_c hu'_int hv'_int
  rw [← hibp]
  apply intervalIntegral.integral_congr
  intro t _
  rw [firstVariationIntegrand_smul_const L x hc e t]

/-- **Initial endpoint transversality.**  If the Euler–Lagrange equation holds and the full
first variation vanishes against the localized endpoint direction `t ↦ c t • e` with `c 0 = 1`
and `c T = 0`, then the initial momentum covector equals the sum of the initial-penalty
gradient and the first endpoint-penalty gradient:
`∂ᵥL(0) = ∂Φ₀(x 0) + ∂₁Φ₁(x 0, x T)`.

This is the initial end condition (11.6.15) of Berkovitz & Medhin, *Nonlinear Optimal Control
Theory* (CRC 2012), §11.6, with the momentum covector `∂ᵥL` being the book's `ψ(ε;·)` of
(11.6.8).  The book obtains it by the `N → ∞` exponential test-function limit; here the
boundary term is isolated by the integration-by-parts identity above. -/
theorem momentumCovector_zero_eq_penalty_derivatives
    (L : ℝ → E → E → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) (T : ℝ) (x : ℝ → E)
    (hT : 0 < T)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (hx : ContDiff ℝ 1 x)
    (heuler : eulerLagrange L T x)
    {c : ℝ → ℝ} (hc : ContDiff ℝ 1 c) (hc0 : c 0 = 1) (hcT : c T = 0)
    (hstat : ∀ e : E, firstVariationWithEndpoints L Φ₀ Φ₁ T x (fun t => c t • e) = 0) :
    momentumCovector L x 0 =
      (fderiv ℝ Φ₀ (x 0))
        + (fderiv ℝ Φ₁ (x 0, x T)).comp (ContinuousLinearMap.inl ℝ E E) := by
  ext e
  have hstat_e := hstat e
  rw [firstVariationWithEndpoints_eq_integral] at hstat_e
  rw [integral_firstVariationIntegrand_smul_const L x e hc T hT hL hx heuler,
    hc0, hcT] at hstat_e
  simp only [mul_zero, mul_one, one_smul, zero_smul] at hstat_e
  have hgoal : (momentumCovector L x 0) e
      = (fderiv ℝ Φ₀ (x 0)) e + (fderiv ℝ Φ₁ (x 0, x T)) (e, 0) := by
    linarith
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply] using hgoal

/-- **Terminal endpoint transversality.**  If the Euler–Lagrange equation holds and the full
first variation vanishes against the localized endpoint direction `t ↦ c t • e` with `c 0 = 0`
and `c T = 1`, then the terminal momentum covector equals the negative of the second
endpoint-penalty gradient: `∂ᵥL(T) = -∂₂Φ₁(x 0, x T)`.

This is the terminal end condition (11.6.16) of Berkovitz & Medhin, *Nonlinear Optimal Control
Theory* (CRC 2012), §11.6. -/
theorem momentumCovector_horizon_eq_neg_penalty_derivative
    (L : ℝ → E → E → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) (T : ℝ) (x : ℝ → E)
    (hT : 0 < T)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (hx : ContDiff ℝ 1 x)
    (heuler : eulerLagrange L T x)
    {c : ℝ → ℝ} (hc : ContDiff ℝ 1 c) (hc0 : c 0 = 0) (hcT : c T = 1)
    (hstat : ∀ e : E, firstVariationWithEndpoints L Φ₀ Φ₁ T x (fun t => c t • e) = 0) :
    momentumCovector L x T =
      -((fderiv ℝ Φ₁ (x 0, x T)).comp (ContinuousLinearMap.inr ℝ E E)) := by
  ext e
  have hstat_e := hstat e
  rw [firstVariationWithEndpoints_eq_integral] at hstat_e
  rw [integral_firstVariationIntegrand_smul_const L x e hc T hT hL hx heuler,
    hc0, hcT] at hstat_e
  simp only [mul_zero, mul_one, sub_zero, one_smul, zero_smul, map_zero] at hstat_e
  have hgoal : (momentumCovector L x T) e = -((fderiv ℝ Φ₁ (x 0, x T)) (0, e)) := by
    linarith
  simpa only [neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply] using hgoal

/-! ## Assembly: the two end conditions from an endpoint minimiser

This packages the Euler–Lagrange step and the two localized endpoint directions into a single
statement.  The Euler–Lagrange equation is obtained from the first variation on endpoint-vanishing
directions (the fixed-endpoint argument); the two endpoint relations come from the localized
directions `t ↦ c₀ t • e` (initial, `c₀ 0 = 1`, `c₀ T = 0`) and `t ↦ c₁ t • e` (terminal,
`c₁ 0 = 0`, `c₁ T = 1`).  These are precisely the directions the book realizes by
`ζ(t) e^{−N t}` and `ζ(t) e^{−N (t₁ − t)}` and then lets `N → ∞`; choosing a `C¹` profile with
the right endpoint values and compact support near the endpoint is the equivalent rigorous
construction. -/

theorem endpointTransversality_of_endpointMinimizer
    (L : ℝ → E → E → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) (T : ℝ) (x : ℝ → E)
    (hT : 0 < T)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hΦ₀ : ContDiff ℝ 1 Φ₀) (hΦ₁ : ContDiff ℝ 1 Φ₁) (hx : ContDiff ℝ 1 x)
    (hvan : HasVanishingFirstVariation L (fun _ => (0 : ℝ)) T x)
    (Q : ℝ → E →L[ℝ] ℝ)
    (hPderiv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (momentumCovector L x) (Q t) t)
    (hPcont : Continuous (momentumCovector L x))
    (hQcont : Continuous Q)
    (hScont : Continuous (stateCovector L x))
    {c₀ c₁ : ℝ → ℝ} (hc₀ : ContDiff ℝ 1 c₀) (hc₀0 : c₀ 0 = 1) (hc₀T : c₀ T = 0)
    (hc₁ : ContDiff ℝ 1 c₁) (hc₁0 : c₁ 0 = 0) (hc₁T : c₁ T = 1)
    (hmin₀ : ∀ e : E, IsLocalMin (fun θ : ℝ =>
      penalizedFunctional L Φ₀ Φ₁ T (fun t => x t + θ • (c₀ t • e))) 0)
    (hmin₁ : ∀ e : E, IsLocalMin (fun θ : ℝ =>
      penalizedFunctional L Φ₀ Φ₁ T (fun t => x t + θ • (c₁ t • e))) 0) :
    (momentumCovector L x 0 =
        (fderiv ℝ Φ₀ (x 0))
          + (fderiv ℝ Φ₁ (x 0, x T)).comp (ContinuousLinearMap.inl ℝ E E)) ∧
      (momentumCovector L x T =
        -((fderiv ℝ Φ₁ (x 0, x T)).comp (ContinuousLinearMap.inr ℝ E E))) := by
  have heuler : eulerLagrange L T x :=
    eulerLagrange_of_firstVariation_zero L (fun _ => (0 : ℝ)) Q T x hT hvan
      hPderiv hPcont hQcont hScont
  refine ⟨momentumCovector_zero_eq_penalty_derivatives L Φ₀ Φ₁ T x hT hL hx heuler
      hc₀ hc₀0 hc₀T ?_,
    momentumCovector_horizon_eq_neg_penalty_derivative L Φ₀ Φ₁ T x hT hL hx heuler
      hc₁ hc₁0 hc₁T ?_⟩
  · intro e
    exact firstVariationWithEndpoints_eq_zero_of_isLocalMin L Φ₀ Φ₁ T x (fun t => c₀ t • e)
      hL hΦ₀ hΦ₁ hx (hc₀.smul contDiff_const) hT.le (hmin₀ e)
  · intro e
    exact firstVariationWithEndpoints_eq_zero_of_isLocalMin L Φ₀ Φ₁ T x (fun t => c₁ t • e)
      hL hΦ₀ hΦ₁ hx (hc₁.smul contDiff_const) hT.le (hmin₁ e)

end OptimalControl.EndpointTransversality
