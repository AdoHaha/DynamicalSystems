/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.BoundedStateMaximumPrinciple
public import DynamicalSystems.OptimalControl.ContinuousTime.StateMultiplierStieltjes
public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwiseBoundaryPositivity
public import DynamicalSystems.Mathlib.Analysis.Calculus.ACIntegrationByParts
public import DynamicalSystems.OptimalControl.ContinuousTime.StateControlFirstVariation

/-!
# Sufficiency of the bounded-state maximum principle

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Theorem 11.8.2 and
Theorem 11.8.4.

This module closes the trajectory-level sufficiency question for the state-constrained
bounded-state problem.  The bounded-state maximum principle
(`OptimalControl.BoundedState.exists_boundedStateMaximumPrinciple`) is a *necessary* condition:
it assumes optimality and produces the multiplier triple `(Ψ, Λ, β, λ⁰)` together with the
costate equation, the endpoint transversality conditions, the pointwise minimum principle and
complementarity.  Theorem 11.8.4 turns the *same* PMP data into a *sufficient* condition under a
convexity hypothesis on the modified Hamiltonian.

The mathematical content is the algebraic identity (11.8.6)–(11.8.10): writing `p = Ψ − Λ∇G` for
the momentum and
`H(t, x, u) = λ⁰ f⁰(t, x, u) − p(t) · f(t, x, u)`
for the `λ⁰`-weighted modified Hamiltonian, the first-order convex support inequality,
the costate equation `p' = Hₓ`, the minimum principle `H_u(φ₀, u₀)(u − u₀) ≥ 0` and integration
by parts along the absolutely continuous paths give, for every admissible relaxed competitor,
`J(φ₀, u₀) − J(φ, u) ≤ −∫ G(φ) dΛ ≤ 0`.
No limit passages, weak topologies or measurable selectors are used.

Book citations live in docstrings only.

## Main results

* `relaxedCost_eq_kernel`: disintegration of the relaxed cost into the conditional kernel.
* `relaxedCost_ofControl`: the cost of an ordinary control.
* `relaxedCost_le_of_convex_momentumHamiltonian`: the algebraic sufficiency inequality
  (Berkovitz & Medhin Theorem 11.8.4).
* `isRelaxedMinimum_of_boundedStateExtremal_of_convex`: the headline sufficiency theorem.

## Implementation notes

The momentum carrier is the library's `VelocityTrajectory`, so the integration by parts along the
path only assumes absolute continuity of the state and `L²` of its velocity — never `C¹`.  The
constraint multiplier enters only through the complementarity inequality
`∫ G d(multiplierMeasure) ≤ 0` of `StateMultiplierStieltjes`; this is the `−∫ G dΛ` term of the
book.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology Interval ENNReal

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]

namespace Problem

/-- The `λ⁰`-weighted modified Hamiltonian of the sufficiency theorem (Berkovitz & Medhin,
*Nonlinear Optimal Control Theory* (CRC 2012), Theorem 11.8.2/11.8.4): with momentum `p` (the
momentum form of the costate), `H(t, x, u) = λ⁰ f⁰(t, x, u) − p(t) · f(t, x, u)`. -/
noncomputable def momentumHamiltonian (P : Problem E V W) (lam0 : ℝ)
    (p : ℝ → E →L[ℝ] ℝ) (t : P.Time) (z : E × V) : ℝ :=
  lam0 * P.runningCost t z.1 z.2 - p t (P.dynamics t z.1 z.2)

/-- The running cost along a bounded continuous trajectory is jointly continuous on the compact
`time × control` space, hence integrable for every relaxed occupation measure. -/
theorem integrable_runningCost_trajectory (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) :
    Integrable (fun z : P.Time × P.Control => P.runningCost z.1 (x z.1) (z.2 : V)) ρ.measure :=
  (continuous_runningCost_along P x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The dynamics along a bounded continuous trajectory is jointly continuous on the compact
`time × control` space, hence integrable for every relaxed occupation measure. -/
theorem integrable_dynamics_trajectory (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) :
    Integrable (fun z : P.Time × P.Control => P.dynamics z.1 (x z.1) (z.2 : V)) ρ.measure :=
  (continuous_dynamics_along P x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The relaxed cost disintegrates along the conditional kernel of the relaxed control. -/
theorem relaxedCost_eq_kernel (P : Problem E V W) (x : P.Trajectory) (ρ : P.Relaxed) :
    P.relaxedCost x ρ = ∫ t, ∫ u : P.Control,
      P.runningCost t (x t) (u : V) ∂ρ.kernel t
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure := by
  rw [relaxedCost]
  exact (RelaxedControl.integral_kernel ρ (P.integrable_runningCost_trajectory x ρ)).symm

/-- The relaxed cost of an ordinary (graph) control is the ordinary running-cost integral. -/
theorem relaxedCost_ofControl (P : Problem E V W) (x : P.Trajectory)
    (u : P.Time → P.Control) (hu : Measurable u) :
    P.relaxedCost x
        (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u hu) =
      ∫ t, P.runningCost t (x t) (u t : V)
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure := by
  rw [relaxedCost]
  exact RelaxedControl.integral_ofControl _ u hu _
    (continuous_runningCost_along P x).aestronglyMeasurable

end Problem

section Integrability

/-- The dynamics along a bounded continuous trajectory is continuous in the control on the
compact control set. -/
theorem continuous_dynamics_control (P : Problem E V W) (x : P.Trajectory) (t : P.Time) :
    Continuous fun u : P.Control => P.dynamics t (x t) (u : V) :=
  P.dynamics_continuous.comp
    ((continuous_const.prodMk continuous_const).prodMk continuous_subtype_val)

/-- The running cost along a bounded continuous trajectory is continuous in the control on the
compact control set. -/
theorem continuous_runningCost_control (P : Problem E V W) (x : P.Trajectory) (t : P.Time) :
    Continuous fun u : P.Control => P.runningCost t (x t) (u : V) :=
  P.runningCost_continuous.comp
    ((continuous_const.prodMk continuous_const).prodMk continuous_subtype_val)

/-- The modified Hamiltonian is continuous in the control on the compact control set. -/
theorem continuous_momentumHamiltonian_control (P : Problem E V W) (lam0 : ℝ)
    (p : ℝ → E →L[ℝ] ℝ) (x : P.Trajectory) (t : P.Time) :
    Continuous fun u : P.Control => P.momentumHamiltonian lam0 p t (x t, (u : V)) := by
  unfold Problem.momentumHamiltonian
  exact ((continuous_runningCost_control P x t).const_mul lam0).sub
      (continuous_const.clm_apply (continuous_dynamics_control P x t))

/-- The running cost along a trajectory is integrable in the control against any probability
measure on the compact control set. -/
theorem integrable_runningCost_control (P : Problem E V W) (x : P.Trajectory) (t : P.Time)
    (μ : Measure P.Control) [IsProbabilityMeasure μ] :
    Integrable (fun u : P.Control => P.runningCost t (x t) (u : V)) μ :=
  (continuous_runningCost_control P x t).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end Integrability

section IntegrationByParts

/-- **Integration by parts for the momentum pairing.**  If `p` is the primitive of `pd` and `γ` is
carried by its velocity, then the normalised pairing equals the boundary terms minus the pairing
of `pd` with the state path.  Only absolute continuity of the path is used
(`ACIntegrationByParts`); no `C¹` assumption appears. -/
theorem integral_momentum_velocity_eq (P : Problem E V W) (γ : VelocityTrajectory P)
    {p pd : ℝ → E →L[ℝ] ℝ}
    (hp_int : IntervalIntegrable pd volume 0 P.horizon)
    (hp : ∀ t ∈ Icc (0 : ℝ) P.horizon, p t = p 0 + ∫ r in (0 : ℝ)..t, pd r) :
    (∫ t : P.Time, p t (γ.velocity t)
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure)
      = P.horizon⁻¹ * (p P.horizon (γ.value P.horizon) - p 0 (γ.value 0)
          - ∫ s in (0 : ℝ)..P.horizon, pd s (γ.value s)) := by
  have hT : (0 : ℝ) ≤ P.horizon := P.horizon_pos.le
  have hcoe := Problem.integral_horizonProbability_coe P (fun t => p t (γ.velocity t))
  have hp_cont : ContinuousOn p (Icc (0 : ℝ) P.horizon) :=
    continuousOn_of_primitive hT hp_int hp
  have hpd_int : IntervalIntegrable (fun s => pd s (γ.value s)) volume 0 P.horizon :=
    intervalIntegrable_clm_apply_of_continuousOn hT hp_int γ.continuousOn_value
  have hpv_int : IntervalIntegrable (fun s => p s (γ.velocity s)) volume 0 P.horizon :=
    intervalIntegrable_clm_apply_of_continuousOn' hT hp_cont γ.velocity_intervalIntegrable
  have hsum : (∫ t in (0 : ℝ)..P.horizon, (pd t (γ.value t) + p t (γ.velocity t)))
      = p P.horizon (γ.value P.horizon) - p 0 (γ.value 0) :=
    calc (∫ t in (0 : ℝ)..P.horizon, (pd t (γ.value t) + p t (γ.velocity t)))
        = ∫ t in (0 : ℝ)..P.horizon,
            (pd t (γ.initial + ∫ r in (0 : ℝ)..t, γ.velocity r)
              + (p 0 + ∫ r in (0 : ℝ)..t, pd r) (γ.velocity t)) := by
          refine intervalIntegral.integral_congr fun t ht => ?_
          rw [uIcc_of_le hT] at ht
          rw [VelocityTrajectory.value, hp t ht]
      _ = (p 0 + ∫ r in (0 : ℝ)..P.horizon, pd r)
            (γ.initial + ∫ r in (0 : ℝ)..P.horizon, γ.velocity r) - p 0 γ.initial :=
          ACIntegrationByParts.integral_apply_add_apply_eq_sub_of_primitive
            hT hp_int γ.velocity_intervalIntegrable
      _ = p P.horizon (γ.value P.horizon) - p 0 (γ.value 0) := by
          rw [← hp P.horizon ⟨hT, le_rfl⟩, VelocityTrajectory.value,
            VelocityTrajectory.value_zero]
  have hsplit : (∫ t in (0 : ℝ)..P.horizon, (pd t (γ.value t) + p t (γ.velocity t)))
      = (∫ t in (0 : ℝ)..P.horizon, pd t (γ.value t))
        + ∫ t in (0 : ℝ)..P.horizon, p t (γ.velocity t) :=
    intervalIntegral.integral_add hpd_int hpv_int
  have hgoal : (∫ t, p t (γ.velocity t) ∂ACEulerLagrange.timeMeasure P.horizon)
      = p P.horizon (γ.value P.horizon) - p 0 (γ.value 0)
          - ∫ s in (0 : ℝ)..P.horizon, pd s (γ.value s) := by
    rw [ACEulerLagrange.timeMeasure, ← intervalIntegral.integral_of_le hT]
    have key : (∫ t in (0 : ℝ)..P.horizon, p t (γ.velocity t))
        = (∫ t in (0 : ℝ)..P.horizon, (pd t (γ.value t) + p t (γ.velocity t)))
          - ∫ t in (0 : ℝ)..P.horizon, pd t (γ.value t) := by
      rw [hsplit]; ring
    rw [key, hsum]
  rw [hcoe, hgoal]

end IntegrationByParts

section ConvexSupport

/-- **Integrated convex support inequality.**  For a convex differentiable `φ`, the tangent
support at `w₀` integrated against a probability measure is below the integral of `φ`. -/
theorem integral_convex_support {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W]
    (φ : W → ℝ) (hφ : ConvexOn ℝ univ φ) (w₀ : W) (D : W →L[ℝ] ℝ)
    (hD : HasFDerivAt φ D w₀) {μ : Measure W} [IsProbabilityMeasure μ]
    (hφint : Integrable φ μ) (hDint : Integrable (fun w => D (w - w₀)) μ) :
    φ w₀ + ∫ w, D (w - w₀) ∂μ ≤ ∫ w, φ w ∂μ := by
  have hpoint : ∀ w, φ w₀ + D (w - w₀) ≤ φ w := fun w =>
    OptimalControl.ConvexStateControlProblem.convex_supporting_derivative φ hφ w₀ w D hD
  have h := integral_mono ((integrable_const (φ w₀)).add hDint) hφint hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const (φ w₀)) hDint, integral_const] at h
  simpa [Measure.real] using h

/-- **The Hamiltonian integral support bound.**  Under joint convexity of the modified
Hamiltonian and the costate/minimum-principle data at the reference point, the integral of the
Hamiltonian over the competitor's control measure is bounded below by the tangent support at the
reference plus the momentum pairings. -/
theorem hamiltonian_integral_lower_bound (P : Problem E V W) (H : P.Time → E × V → ℝ)
    (Hd : P.Time → E × V → (E × V) →L[ℝ] ℝ)
    (hHd : ∀ t z, HasFDerivAt (fun w : E × V => H t w) (Hd t z) z)
    (hconv : ∀ t, ConvexOn ℝ univ (fun w : E × V => H t w))
    (x : P.Trajectory) (ρ : P.Relaxed) (y : E) (u₀ : P.Control) (t : P.Time)
    {pd : ℝ → E →L[ℝ] ℝ}
    (hcostate_t : (Hd t (y, (u₀ : V))).comp (ContinuousLinearMap.inl ℝ E V) = pd (t : ℝ))
    (hpmp_t : ∀ v : V,
      (Hd t (y, (u₀ : V))).comp (ContinuousLinearMap.inr ℝ E V) (v - (u₀ : V)) ≥ 0)
    (hHint : Integrable (fun u : P.Control => H t (x t, (u : V))) (ρ.kernel t)) :
    H t (y, (u₀ : V)) + pd (t : ℝ) (x t - y)
      ≤ ∫ u : P.Control, H t (x t, (u : V)) ∂ρ.kernel t := by
  have hpoint : ∀ u : P.Control, H t (y, (u₀ : V))
      + (Hd t (y, (u₀ : V))) (x t - y, (u : V) - (u₀ : V)) ≤ H t (x t, (u : V)) :=
    fun u => OptimalControl.ConvexStateControlProblem.convex_supporting_derivative
      (fun w : E × V => H t w) (hconv t) (y, (u₀ : V)) (x t, (u : V))
      (Hd t (y, (u₀ : V))) (hHd t _)
  have hDint : Integrable
      (fun u : P.Control => (Hd t (y, (u₀ : V))) (x t - y, (u : V) - (u₀ : V)))
      (ρ.kernel t) :=
    ((Hd t (y, (u₀ : V))).continuous.comp
      ((continuous_const).prodMk (continuous_subtype_val.sub continuous_const))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hmono := integral_mono ((integrable_const (H t (y, (u₀ : V)))).add hDint) hHint hpoint
  simp only [Pi.add_apply] at hmono
  rw [integral_add (integrable_const _) hDint, integral_const] at hmono
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hmono
  have hsplit : ∀ u : P.Control,
      (Hd t (y, (u₀ : V))) (x t - y, (u : V) - (u₀ : V))
        = (Hd t (y, (u₀ : V))) (x t - y, 0)
          + (Hd t (y, (u₀ : V))) (0, (u : V) - (u₀ : V)) := by
    intro u
    rw [← map_add]
    congr 1
    ext <;> simp
  have hD0int : Integrable
      (fun _ : P.Control => (Hd t (y, (u₀ : V))) (x t - y, 0)) (ρ.kernel t) :=
    integrable_const _
  have hD0'int : Integrable
      (fun u : P.Control => (Hd t (y, (u₀ : V))) (0, (u : V) - (u₀ : V))) (ρ.kernel t) :=
    ((Hd t (y, (u₀ : V))).continuous.comp
      ((continuous_const).prodMk (continuous_subtype_val.sub continuous_const))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hInt_eq : (∫ u : P.Control,
        (Hd t (y, (u₀ : V))) (x t - y, (u : V) - (u₀ : V)) ∂ρ.kernel t)
      = (Hd t (y, (u₀ : V))) (x t - y, 0)
        + ∫ u : P.Control, (Hd t (y, (u₀ : V))) (0, (u : V) - (u₀ : V)) ∂ρ.kernel t := by
    have hconst_eq : (Hd t (y, (u₀ : V))) (x t - y, 0)
        = ∫ _ : P.Control, (Hd t (y, (u₀ : V))) (x t - y, 0) ∂ρ.kernel t := by
      rw [integral_const]
      simp [Measure.real]
    rw [hconst_eq, ← integral_add hD0int hD0'int]
    exact integral_congr_ae (Eventually.of_forall fun u => hsplit u)
  have hnonneg : 0 ≤ ∫ u : P.Control,
      (Hd t (y, (u₀ : V))) (0, (u : V) - (u₀ : V)) ∂ρ.kernel t :=
    integral_nonneg fun u => hpmp_t (u : V)
  have hcostate_apply : (Hd t (y, (u₀ : V))) (x t - y, 0) = pd (t : ℝ) (x t - y) := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L (x t - y)) hcostate_t
    simpa [ContinuousLinearMap.comp_apply] using h
  rw [hInt_eq, hcostate_apply] at hmono
  linarith [hmono, hnonneg]

/-- **The cost-integrand support bound.**  Identical to `hamiltonian_integral_lower_bound` but
stated for the `λ⁰`-weighted running cost `λ⁰ f⁰ = H + p·f`, with the realised velocity carrying
the momentum pairing. -/
theorem momentumHamiltonian_cost_lower_bound (P : Problem E V W) (lam0 : ℝ)
    (p : ℝ → E →L[ℝ] ℝ) (pd : ℝ → E →L[ℝ] ℝ)
    (H : P.Time → E × V → ℝ) (Hd : P.Time → E × V → (E × V) →L[ℝ] ℝ)
    (hH : ∀ t z, H t z = P.momentumHamiltonian lam0 p t z)
    (hHd : ∀ t z, HasFDerivAt (fun w : E × V => H t w) (Hd t z) z)
    (hconv : ∀ t, ConvexOn ℝ univ (fun w : E × V => H t w))
    (x : P.Trajectory) (ρ : P.Relaxed) (y : E) (u₀ : P.Control) (t : P.Time)
    (hcostate_t : (Hd t (y, (u₀ : V))).comp (ContinuousLinearMap.inl ℝ E V) = pd (t : ℝ))
    (hpmp_t : ∀ v : V,
      (Hd t (y, (u₀ : V))).comp (ContinuousLinearMap.inr ℝ E V) (v - (u₀ : V)) ≥ 0) :
    H t (y, (u₀ : V)) + pd (t : ℝ) (x t - y) + p t (Problem.realizedVelocity P x ρ t)
      ≤ ∫ u : P.Control, lam0 * P.runningCost t (x t) (u : V) ∂ρ.kernel t := by
  have hHint : Integrable (fun u : P.Control => H t (x t, (u : V))) (ρ.kernel t) := by
    have heq : (fun u : P.Control => H t (x t, (u : V)))
        = fun u : P.Control => P.momentumHamiltonian lam0 p t (x t, (u : V)) := by
      funext u
      exact hH t _
    rw [heq]
    exact (continuous_momentumHamiltonian_control P lam0 p x t).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlb := hamiltonian_integral_lower_bound P H Hd hHd hconv x ρ y u₀ t
    hcostate_t hpmp_t hHint
  have hpoint : ∀ u : P.Control, lam0 * P.runningCost t (x t) (u : V)
      = H t (x t, (u : V)) + p t (P.dynamics t (x t) (u : V)) := by
    intro u
    rw [hH t]
    simp only [Problem.momentumHamiltonian]
    ring
  have hsplit : (∫ u : P.Control, lam0 * P.runningCost t (x t) (u : V) ∂ρ.kernel t)
      = (∫ u : P.Control, H t (x t, (u : V)) ∂ρ.kernel t)
        + p t (Problem.realizedVelocity P x ρ t) := by
    rw [show (∫ u : P.Control, lam0 * P.runningCost t (x t) (u : V) ∂ρ.kernel t)
        = ∫ u : P.Control,
            (H t (x t, (u : V)) + p t (P.dynamics t (x t) (u : V))) ∂ρ.kernel t from
          integral_congr_ae (Eventually.of_forall hpoint)]
    rw [integral_add hHint ((p t).integrable_comp (P.integrable_dynamics_control x t (ρ.kernel t)))]
    rw [ContinuousLinearMap.integral_comp_comm (p t)
      (P.integrable_dynamics_control x t (ρ.kernel t))]
    rfl
  linarith [hlb, hsplit]

/-- The conditional average of a continuous function on the compact time-control product is
integrable for the normalised time marginal. -/
theorem integrable_average_of_continuous (P : Problem E V W) (ρ : P.Relaxed)
    {f : P.Time × P.Control → ℝ} (hf : Continuous f) :
    Integrable (fun t : P.Time => ∫ u : P.Control, f (t, u) ∂ρ.kernel t)
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  refine Integrable.of_bound
    (RelaxedControl.stronglyMeasurable_average ρ hf.stronglyMeasurable).aestronglyMeasurable
    C (Filter.Eventually.of_forall fun t => ?_)
  have hft : Continuous fun u : P.Control => f (t, u) :=
    hf.comp (continuous_const.prodMk continuous_id)
  calc ‖∫ u : P.Control, f (t, u) ∂ρ.kernel t‖
      ≤ ∫ u : P.Control, ‖f (t, u)‖ ∂ρ.kernel t := norm_integral_le_integral_norm _
    _ ≤ ∫ _u : P.Control, C ∂ρ.kernel t :=
        integral_mono (hft.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (integrable_const C) fun u => hC (t, u) (mem_univ _)
    _ = C := by rw [integral_const]; simp [Measure.real]

end ConvexSupport



section Sufficiency

variable {P : Problem E V W}

omit [MeasurableSpace E] [BorelSpace E] in
/-- The pairing of an interval integrable covector with the state path against the normalised
time marginal, as an unnormalised interval integral. -/
theorem integral_pd_value_eq (P : Problem E V W) (γ : VelocityTrajectory P)
    {pd : ℝ → E →L[ℝ] ℝ} (hpd : IntervalIntegrable pd volume 0 P.horizon) :
    (∫ t : P.Time, pd t (γ.value t)
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure)
      = P.horizon⁻¹ * ∫ s in (0 : ℝ)..P.horizon, pd s (γ.value s) := by
  have hT : (0 : ℝ) ≤ P.horizon := P.horizon_pos.le
  rw [Problem.integral_horizonProbability_coe P (fun s => pd s (γ.value s))]
  congr 1
  rw [ACEulerLagrange.timeMeasure, intervalIntegral.integral_of_le hT]

/-- **The relaxed-cost momentum expansion.**  With the `λ⁰`-weighted modified Hamiltonian
`λ⁰ f⁰ = H + p·f`, the normalised relaxed cost splits into the Hamiltonian average and the
momentum pairing with the realised velocity. -/
theorem relaxedCost_momentum_expansion (P : Problem E V W) (lam0 : ℝ)
    (p : ℝ → E →L[ℝ] ℝ) (H : P.Time → E × V → ℝ)
    (hH : ∀ t z, H t z = P.momentumHamiltonian lam0 p t z)
    (x : P.Trajectory) (ρ : P.Relaxed)
    (hintH : Integrable (fun z : P.Time × P.Control => H z.1 (x z.1, (z.2 : V))) ρ.measure)
    (hintpf : Integrable (fun z : P.Time × P.Control =>
      p z.1 (P.dynamics z.1 (x z.1) (z.2 : V))) ρ.measure) :
    lam0 * P.relaxedCost x ρ
      = (∫ t : P.Time, (∫ u : P.Control, H t (x t, (u : V)) ∂ρ.kernel t)
          ∂(horizonProbability P.horizon P.horizon_pos).toMeasure)
        + ∫ t : P.Time, p t (Problem.realizedVelocity P x ρ t)
          ∂(horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hintcur : Integrable (fun z : P.Time × P.Control =>
      P.runningCost z.1 (x z.1) (z.2 : V)) ρ.measure := P.integrable_runningCost_trajectory x ρ
  calc lam0 * P.relaxedCost x ρ
      = ∫ z, lam0 * P.runningCost z.1 (x z.1) (z.2 : V) ∂ρ.measure := by
        rw [Problem.relaxedCost, ← integral_const_mul]
    _ = ∫ z, (H z.1 (x z.1, (z.2 : V))
          + p z.1 (P.dynamics z.1 (x z.1) (z.2 : V))) ∂ρ.measure := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        show lam0 * P.runningCost z.1 (x z.1) (z.2 : V)
          = H z.1 (x z.1, (z.2 : V)) + p z.1 (P.dynamics z.1 (x z.1) (z.2 : V))
        rw [hH z.1]
        simp only [Problem.momentumHamiltonian]
        ring
    _ = (∫ z, H z.1 (x z.1, (z.2 : V)) ∂ρ.measure)
          + ∫ z, p z.1 (P.dynamics z.1 (x z.1) (z.2 : V)) ∂ρ.measure :=
        integral_add hintH hintpf
    _ = (∫ t : P.Time, (∫ u : P.Control, H t (x t, (u : V)) ∂ρ.kernel t)
          ∂(horizonProbability P.horizon P.horizon_pos).toMeasure)
          + ∫ t : P.Time, p t (Problem.realizedVelocity P x ρ t)
            ∂(horizonProbability P.horizon P.horizon_pos).toMeasure := by
        rw [← RelaxedControl.integral_kernel ρ hintH,
          ← RelaxedControl.integral_kernel ρ hintpf]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        change (∫ u : P.Control, p t (P.dynamics t (x t) (u : V)) ∂ρ.kernel t)
          = p t (Problem.realizedVelocity P x ρ t)
        rw [ContinuousLinearMap.integral_comp_comm (p t)
          (P.integrable_dynamics_control x t (ρ.kernel t))]
        rfl

/-- The running cost along the reference ordinary control is integrable for the normalised time
marginal. -/
theorem integrable_runningCost_reference (P : Problem E V W) (γ₀ : VelocityTrajectory P)
    (u₀ : P.Time → P.Control) (hu₀ : Measurable u₀) :
    Integrable (fun t : P.Time => P.runningCost t (γ₀.value t) (u₀ t))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  obtain ⟨C, hC⟩ := Problem.exists_bound_runningCost_trajectory P (toBoundedPath γ₀)
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun t => ?_)
  · have hm : Measurable fun t : P.Time => ((t, γ₀.value t), (u₀ t : V)) :=
      (measurable_id.prodMk (toBoundedPath γ₀).continuous.measurable).prodMk
        (measurable_subtype_coe.comp hu₀)
    exact (P.runningCost_continuous.measurable.comp hm).aestronglyMeasurable
  · simpa [Real.norm_eq_abs] using hC t (u₀ t)

/-- The momentum pairing with the reference dynamics is integrable for the normalised time
marginal. -/
theorem integrable_momentum_dynamics_reference (P : Problem E V W) (γ₀ : VelocityTrajectory P)
    (u₀ : P.Time → P.Control) (hu₀ : Measurable u₀) {p pd : ℝ → E →L[ℝ] ℝ}
    (hp_int : IntervalIntegrable pd volume 0 P.horizon)
    (hp : ∀ t ∈ Icc (0 : ℝ) P.horizon, p t = p 0 + ∫ r in (0 : ℝ)..t, pd r) :
    Integrable (fun t : P.Time => p t (P.dynamics t (γ₀.value t) (u₀ t)))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hT : (0 : ℝ) ≤ P.horizon := P.horizon_pos.le
  have hp_cont : ContinuousOn p (Icc (0 : ℝ) P.horizon) :=
    continuousOn_of_primitive hT hp_int hp
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hp_cont
  obtain ⟨C, hC⟩ := Problem.exists_bound_dynamics_trajectory P (toBoundedPath γ₀)
  let t0 : P.Time := timeZero P.horizon P.horizon_pos.le
  have hB0 : 0 ≤ B := (norm_nonneg (p 0)).trans (hB 0 ⟨le_rfl, hT⟩)
  have hC0 : 0 ≤ C := (norm_nonneg (P.dynamics t0 (γ₀.value t0) (u₀ t0))).trans (hC t0 (u₀ t0))
  refine Integrable.of_bound ?_ (B * C) (Filter.Eventually.of_forall fun t => ?_)
  · have hdyn : Measurable fun t : P.Time => P.dynamics t (γ₀.value t) (u₀ t) :=
      P.dynamics_continuous.measurable.comp
        ((measurable_id.prodMk (toBoundedPath γ₀).continuous.measurable).prodMk
          (measurable_subtype_coe.comp hu₀))
    have hp_c : Continuous fun t : P.Time => p t := hp_cont.domRestrict
    have hpair : Measurable fun t : P.Time => (p t, P.dynamics t (γ₀.value t) (u₀ t)) :=
      hp_c.measurable.prod hdyn
    exact ((continuous_fst.clm_apply continuous_snd).measurable.comp hpair).aestronglyMeasurable
  · calc ‖p t (P.dynamics t (γ₀.value t) (u₀ t))‖
        ≤ ‖p t‖ * ‖P.dynamics t (γ₀.value t) (u₀ t)‖ := (p t).le_opNorm _
      _ ≤ B * C := mul_le_mul (hB t t.2) (hC t (u₀ t)) (norm_nonneg _) hB0

/-- The pairing of the interval integrable costate derivative with the state difference is
integrable for the normalised time marginal. -/
theorem integrable_pd_value_sub (P : Problem E V W) (γ₀ : VelocityTrajectory P)
    {pd : ℝ → E →L[ℝ] ℝ} (hpd : IntervalIntegrable pd volume 0 P.horizon)
    (γ : VelocityTrajectory P) :
    Integrable (fun t : P.Time => pd t (γ.value t - γ₀.value t))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hT : (0 : ℝ) ≤ P.horizon := P.horizon_pos.le
  have hcont : ContinuousOn (fun s : ℝ => γ.value s - γ₀.value s) (Icc (0 : ℝ) P.horizon) :=
    γ.continuousOn_value.sub γ₀.continuousOn_value
  have hii : IntervalIntegrable (fun s : ℝ => pd s (γ.value s - γ₀.value s)) volume 0 P.horizon :=
    intervalIntegrable_clm_apply_of_continuousOn hT hpd hcont
  exact Problem.integrable_horizonProbability_coe P
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hii)

/-- The momentum pairing with the realised velocity is integrable for the normalised time
marginal. -/
theorem integrable_momentum_realizedVelocity (P : Problem E V W) (γ : VelocityTrajectory P)
    (ρ : P.Relaxed) {p pd : ℝ → E →L[ℝ] ℝ}
    (hp_int : IntervalIntegrable pd volume 0 P.horizon)
    (hp : ∀ t ∈ Icc (0 : ℝ) P.horizon, p t = p 0 + ∫ r in (0 : ℝ)..t, pd r) :
    Integrable (fun t : P.Time => p t (Problem.realizedVelocity P (toBoundedPath γ) ρ t))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hT : (0 : ℝ) ≤ P.horizon := P.horizon_pos.le
  have hp_cont : Continuous fun t : P.Time => p t :=
    (continuousOn_of_primitive hT hp_int hp).domRestrict
  have hcont : Continuous fun z : P.Time × P.Control =>
      p z.1 (P.dynamics z.1 (γ.value z.1) (z.2 : V)) :=
    (hp_cont.comp continuous_fst).clm_apply (P.continuous_dynamics_along (toBoundedPath γ))
  have havg := integrable_average_of_continuous P ρ hcont
  refine havg.congr ?_
  filter_upwards with t
  change (∫ u : P.Control, p t (P.dynamics t ((toBoundedPath γ) t) (u : V)) ∂ρ.kernel t)
    = p t (Problem.realizedVelocity P (toBoundedPath γ) ρ t)
  rw [ContinuousLinearMap.integral_comp_comm (p t)
    (P.integrable_dynamics_control (toBoundedPath γ) t (ρ.kernel t))]
  rfl

/-- The pairing of an interval integrable costate derivative with a state path is integrable for
the normalised time marginal. -/
theorem integrable_pd_value (P : Problem E V W) (γ : VelocityTrajectory P)
    {pd : ℝ → E →L[ℝ] ℝ} (hpd : IntervalIntegrable pd volume 0 P.horizon) :
    Integrable (fun t : P.Time => pd t (γ.value t))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hT : (0 : ℝ) ≤ P.horizon := P.horizon_pos.le
  have hii : IntervalIntegrable (fun s : ℝ => pd s (γ.value s)) volume 0 P.horizon :=
    intervalIntegrable_clm_apply_of_continuousOn hT hpd γ.continuousOn_value
  exact Problem.integrable_horizonProbability_coe P
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hii)

/-- Trajectory-level relaxed minimality on the velocity carrier: the reference pair is admissible
and no admissible velocity-trajectory competitor has smaller relaxed cost.  This is the natural
carrier for the sufficiency proof, since it carries an explicit velocity for integration by
parts. -/
def IsVelocityRelaxedMinimum (P : Problem E V W) (γ₀ : VelocityTrajectory P)
    (ρ₀ : P.Relaxed) : Prop :=
  P.IsRelaxedAdmissible (toBoundedPath γ₀) ρ₀ ∧
    ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      P.IsRelaxedAdmissible (toBoundedPath γ) ρ →
        P.relaxedCost (toBoundedPath γ₀) ρ₀ ≤ P.relaxedCost (toBoundedPath γ) ρ

/-- **The algebraic sufficiency identity of Berkovitz & Medhin (11.8.6)–(11.8.10).**  Under the
joint convexity of the modified Hamiltonian and the costate/minimum-principle data of Theorem
11.8.2, the relaxed cost difference dominates the integrated momentum pairing
`∫ (p'·(φ−φ₀) + p·φ' − p·f(φ₀,u₀))`.  Adding the transversality boundary identity
(see the report) yields the sufficiency conclusion. -/
theorem relaxedCost_sub_lowerBound_of_boundedStateExtremal_of_convex
    (P : Problem E V W) (γ₀ : VelocityTrajectory P) (u₀ : P.Time → P.Control)
    (hu₀ : Measurable u₀)
    (hadm₀ : P.IsRelaxedAdmissible (toBoundedPath γ₀)
      (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ hu₀))
    (hvel₀ : (fun t : P.Time => γ₀.velocity t)
        =ᵐ[(horizonProbability P.horizon P.horizon_pos).toMeasure]
          fun t : P.Time => P.dynamics t (γ₀.value t) (u₀ t))
    (hvel : ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      P.IsRelaxedAdmissible (toBoundedPath γ) ρ →
        (fun t : P.Time => Problem.realizedVelocity P (toBoundedPath γ) ρ t)
          =ᵐ[(horizonProbability P.horizon P.horizon_pos).toMeasure]
            fun t : P.Time => γ.velocity t)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (p pd : ℝ → E →L[ℝ] ℝ)
    (H : P.Time → E × V → ℝ) (Hd : P.Time → E × V → (E × V) →L[ℝ] ℝ)
    (hH : ∀ t z, H t z = P.momentumHamiltonian lam0 p t z)
    (hHd : ∀ t z, HasFDerivAt (fun w : E × V => H t w) (Hd t z) z)
    (hconv : ∀ t, ConvexOn ℝ univ (fun w : E × V => H t w))
    (hp_int : IntervalIntegrable pd volume 0 P.horizon)
    (hp : ∀ t ∈ Set.Icc (0 : ℝ) P.horizon, p t = p 0 + ∫ r in (0 : ℝ)..t, pd r)
    (hcostate : ∀ᵐ (t : P.Time) ∂(horizonProbability P.horizon P.horizon_pos).toMeasure,
      pd t = (Hd t (γ₀.value t, u₀ t)).comp (ContinuousLinearMap.inl ℝ E V))
    (hpmp : ∀ᵐ (t : P.Time) ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v : V,
      (Hd t (γ₀.value t, u₀ t)).comp (ContinuousLinearMap.inr ℝ E V) (v - (u₀ t : V)) ≥ 0) :
    ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      P.IsRelaxedAdmissible (toBoundedPath γ) ρ →
        (∫ t : P.Time, (pd t ((toBoundedPath γ) t - γ₀.value t)
            + p t (Problem.realizedVelocity P (toBoundedPath γ) ρ t)
            - p t (P.dynamics t (γ₀.value t) (u₀ t)))
          ∂(horizonProbability P.horizon P.horizon_pos).toMeasure)
          ≤ lam0 * (P.relaxedCost (toBoundedPath γ) ρ
              - P.relaxedCost (toBoundedPath γ₀)
                  (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ hu₀)) := by
  intro γ ρ hadm
  let ν := horizonProbability P.horizon P.horizon_pos
  let ρ₀ := RelaxedControl.ofControl ν u₀ hu₀
  have hcostγ : lam0 * P.relaxedCost (toBoundedPath γ) ρ
      = ∫ t : P.Time, (∫ u : P.Control,
          lam0 * P.runningCost t ((toBoundedPath γ) t) (u : V) ∂ρ.kernel t) ∂ν := by
    rw [Problem.relaxedCost_eq_kernel]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [← integral_const_mul]
  have hcostγ₀ : lam0 * P.relaxedCost (toBoundedPath γ₀) ρ₀
      = ∫ t : P.Time, lam0 * P.runningCost t (γ₀.value t) (u₀ t) ∂ν := by
    change lam0 * P.relaxedCost (toBoundedPath γ₀) (RelaxedControl.ofControl ν u₀ hu₀) = _
    rw [Problem.relaxedCost_ofControl]
    rw [← integral_const_mul]
    simp only [toBoundedPath_apply]
    rfl
  let A : P.Time → ℝ := fun t =>
    ∫ u : P.Control, lam0 * P.runningCost t ((toBoundedPath γ) t) (u : V) ∂ρ.kernel t
  let B : P.Time → ℝ := fun t => lam0 * P.runningCost t (γ₀.value t) (u₀ t)
  let R : P.Time → ℝ := fun t => pd t ((toBoundedPath γ) t - γ₀.value t)
    + p t (Problem.realizedVelocity P (toBoundedPath γ) ρ t)
    - p t (P.dynamics t (γ₀.value t) (u₀ t))
  have hbound_ae : ∀ᵐ t ∂ν.toMeasure, R t ≤ A t - B t := by
    filter_upwards [hcostate, hpmp] with t hc hp
    have h := momentumHamiltonian_cost_lower_bound P lam0 p pd H Hd hH hHd hconv
      (toBoundedPath γ) ρ (γ₀.value t) (u₀ t) t hc.symm hp
    have hHval : H t (γ₀.value t, (u₀ t : V))
        = lam0 * P.runningCost t (γ₀.value t) (u₀ t)
          - p t (P.dynamics t (γ₀.value t) (u₀ t)) := by
      rw [hH t]
      simp only [Problem.momentumHamiltonian]
    simp only [R, A, B]
    nlinarith [h, hHval]
  have hA : Integrable A ν.toMeasure := by
    have hcont : Continuous fun z : P.Time × P.Control =>
        lam0 * P.runningCost z.1 ((toBoundedPath γ) z.1) (z.2 : V) :=
      (P.continuous_runningCost_along (toBoundedPath γ)).const_mul lam0
    exact integrable_average_of_continuous P ρ hcont
  have hB : Integrable B ν.toMeasure := (integrable_runningCost_reference P γ₀ u₀ hu₀).const_mul lam0
  have hRint : Integrable R ν.toMeasure := by
    simp only [R]
    exact ((integrable_pd_value_sub P γ₀ hp_int γ).add
      (integrable_momentum_realizedVelocity P γ ρ hp_int hp)).sub
        (integrable_momentum_dynamics_reference P γ₀ u₀ hu₀ hp_int hp)
  have h1 : (∫ t : P.Time, (A t - B t) ∂ν.toMeasure) ≥ ∫ t : P.Time, R t ∂ν.toMeasure :=
    integral_mono_ae hRint (hA.sub hB) hbound_ae
  have h2 : (∫ t : P.Time, (A t - B t) ∂ν.toMeasure)
      = (∫ t : P.Time, A t ∂ν.toMeasure) - ∫ t : P.Time, B t ∂ν.toMeasure :=
    integral_sub hA hB
  rw [mul_sub, hcostγ, hcostγ₀, ← h2]
  exact h1

/-- **Sufficiency of the bounded-state maximum principle (Berkovitz & Medhin, Theorem 11.8.4).**

Let `(φ₀, u₀)` be an admissible ordinary relaxed pair carrying the maximum-principle data
`(p, H)` at weight `λ⁰ > 0`: `H = λ⁰ f⁰ − p·f` is jointly convex in `(x,u)`, its derivative
`Hd` has state part `pd = ∂ₓH` and nonnegative control directional derivative at the reference,
and `p` is a primitive of `pd`.  If the integrated transversality pairing `∫R` is nonnegative for
every admissible competitor, then `(φ₀, u₀)` is a velocity-carrier relaxed minimum
(`IsVelocityRelaxedMinimum`).

The proof combines the convexity/costate identity
`relaxedCost_sub_lowerBound_of_boundedStateExtremal_of_convex` with the transversality
hypothesis; the integrated pairing is exactly the boundary term of (11.8.10). -/
theorem isVelocityRelaxedMinimum_of_boundedStateExtremal_of_convex
    (P : Problem E V W) (γ₀ : VelocityTrajectory P) (u₀ : P.Time → P.Control)
    (hu₀ : Measurable u₀)
    (hadm₀ : P.IsRelaxedAdmissible (toBoundedPath γ₀)
      (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ hu₀))
    (hvel₀ : (fun t : P.Time => γ₀.velocity t)
        =ᵐ[(horizonProbability P.horizon P.horizon_pos).toMeasure]
          fun t : P.Time => P.dynamics t (γ₀.value t) (u₀ t))
    (hvel : ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      P.IsRelaxedAdmissible (toBoundedPath γ) ρ →
        (fun t : P.Time => Problem.realizedVelocity P (toBoundedPath γ) ρ t)
          =ᵐ[(horizonProbability P.horizon P.horizon_pos).toMeasure]
            fun t : P.Time => γ.velocity t)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (p pd : ℝ → E →L[ℝ] ℝ)
    (H : P.Time → E × V → ℝ) (Hd : P.Time → E × V → (E × V) →L[ℝ] ℝ)
    (hH : ∀ t z, H t z = P.momentumHamiltonian lam0 p t z)
    (hHd : ∀ t z, HasFDerivAt (fun w : E × V => H t w) (Hd t z) z)
    (hconv : ∀ t, ConvexOn ℝ univ (fun w : E × V => H t w))
    (hp_int : IntervalIntegrable pd volume 0 P.horizon)
    (hp : ∀ t ∈ Set.Icc (0 : ℝ) P.horizon, p t = p 0 + ∫ r in (0 : ℝ)..t, pd r)
    (hcostate : ∀ᵐ (t : P.Time) ∂(horizonProbability P.horizon P.horizon_pos).toMeasure,
      pd t = (Hd t (γ₀.value t, u₀ t)).comp (ContinuousLinearMap.inl ℝ E V))
    (hpmp : ∀ᵐ (t : P.Time) ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v : V,
      (Hd t (γ₀.value t, u₀ t)).comp (ContinuousLinearMap.inr ℝ E V) (v - (u₀ t : V)) ≥ 0)
    (htransv : ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      P.IsRelaxedAdmissible (toBoundedPath γ) ρ →
        0 ≤ ∫ t : P.Time, (pd t ((toBoundedPath γ) t - γ₀.value t)
          + p t (Problem.realizedVelocity P (toBoundedPath γ) ρ t)
          - p t (P.dynamics t (γ₀.value t) (u₀ t)))
          ∂(horizonProbability P.horizon P.horizon_pos).toMeasure) :
    IsVelocityRelaxedMinimum P γ₀
      (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ hu₀) := by
  refine ⟨hadm₀, ?_⟩
  intro γ ρ hadm
  have h := relaxedCost_sub_lowerBound_of_boundedStateExtremal_of_convex P γ₀ u₀ hu₀ hadm₀
    hvel₀ hvel lam0 hlam0 p pd H Hd hH hHd hconv hp_int hp hcostate hpmp γ ρ hadm
  have hb := htransv γ ρ hadm
  have hnonneg : 0 ≤ lam0 * (P.relaxedCost (toBoundedPath γ) ρ
      - P.relaxedCost (toBoundedPath γ₀)
          (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ hu₀)) := by
    linarith [h, hb]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hnonneg hlam0)

end Sufficiency

end OptimalControl.BoundedState
