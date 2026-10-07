/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.MaximumPrincipleSufficiency
public import DynamicalSystems.OptimalControl.ContinuousTime.StateMultiplierStieltjes

/-!
# Sufficiency of the maximum principle for state-constrained problems

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Theorem 11.8.4
(equations (11.8.6)–(11.8.10); printed pp. 329–332).

This module proves the **convex / Mangasarian sufficiency form** of the maximum principle for the
bounded-state optimal control problem with state constraints `G(t, x) ≤ 0`.  While the unconstrained
/ affine-endpoint Mangasarian core (`OptimalControl.BoundedState.MaximumPrincipleSufficiency`, R6a)
handled `Λ ≡ 0`, this module incorporates the state-constraint multiplier shift `Λ ∇G` of Berkovitz
& Medhin Theorem 11.8.4.  It **assumes** the maximum-principle multiplier data `(Φ, Λ, β, λ⁰)` of
Theorem 11.8.2 (costate equation, transversality, complementarity) and an affine endpoint constraint
`T`; the *existence* of that data is not derived here — that is the necessary-condition direction
(`exists_boundedStateMaximumPrinciple`, BM Theorem 11.6.3).

The theorem takes as hypotheses an admissible reference pair `(γ₀, u₀)` together with the
maximum-principle multiplier data `(Φ, Λ, β, λ⁰)`:
* `Φ` is the absolutely continuous costate satisfying `Φ' = H̃_x`, with terminal transversality
  `Φ(t₁) = −β ∂₂T`;
* `Λ ≥ 0` is a nonincreasing multiplier with `Λ(t₁) = 0` and complementarity
  `supp dΛ ⊆ {G = 0}` (so `∫ G(·, γ₀) dΛ = 0`);
* `H̃(t, x, u) = λ⁰ f⁰(t, x, u) − (Φ(t) − Λ(t) • ∇G(t, x)) · f(t, x, u)` is the modified
  Hamiltonian, jointly convex in `(x, u)` with the minimum principle `H̃_u(u − u₀) ≥ 0`.

The proof formalises the algebraic identity (11.8.6)–(11.8.10):
```text
J(γ, u) − J(γ₀, u₀) ≥ ∫ (H̃(γ, u) − H̃(γ₀, u₀) − H̃_x · (γ − γ₀) − H̃_u · (u − u₀)) dt
                        − ∫ G(γ) dΛ ≥ 0,
```
where the first integral is non-negative by joint convexity and the pointwise minimum principle,
the boundary terms cancel by terminal transversality and the fixed initial state, and the
Stieltjes integral `−∫ G(γ) dΛ` is non-negative by admissibility of the competitor (`G(γ) ≤ 0`)
and monotonicity of `Λ`.

Book citations live in docstrings only.

## Main results

* `Problem.stateConstrainedHamiltonian`: the modified Hamiltonian `H̃ = λ⁰ f⁰ − (Φ − Λ∇G) · f`.
* `intervalIntegral_lam_mul_eq_stieltjes`: Stieltjes integration by parts for a nonincreasing
  multiplier against an absolutely continuous path.
* `isVelocityRelaxedMinimum_of_boundedStateExtremal_of_convex_stateConstrained`: the headline
  sufficiency theorem for the state-constrained problem on the velocity carrier.
* `isRelaxedMinimum_of_boundedStateExtremal_of_convex_stateConstrained`: the Volterra-carrier
  sufficiency theorem.
-/

@[expose] public section

open Set MeasureTheory Filter ACEulerLagrange
open scoped Topology Interval ENNReal

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]

namespace Problem

/-- The state-constrained modified Hamiltonian of Berkovitz & Medhin (Theorem 11.8.4;
equations (11.8.6)–(11.8.10)):
`H̃(t, x, u) = λ⁰ f⁰(t, x, u) − (Φ(t) − Λ(t) • ∇G(t, x)) · f(t, x, u)`.
This generalises `momentumHamiltonian` (where `Λ ≡ 0`) by incorporating the constraint multiplier
shift `Λ(t) • ∇G(t, x)`. -/
noncomputable def stateConstrainedHamiltonian (P : Problem E V W) (lam0 : ℝ)
    (Φ : ℝ → E →L[ℝ] ℝ) (Λ : ℝ → ℝ) (Gx : ℝ → E → E →L[ℝ] ℝ) (t : P.Time) (z : E × V) : ℝ :=
  lam0 * P.runningCost t z.1 z.2 - (Φ t - Λ t • Gx t z.1) (P.dynamics t z.1 z.2)

end Problem

section Integrability

/-- The state-constrained modified Hamiltonian is continuous in the control on the compact
control set. -/
theorem continuous_stateConstrainedHamiltonian_control (P : Problem E V W) (lam0 : ℝ)
    (Φ : ℝ → E →L[ℝ] ℝ) (Λ : ℝ → ℝ) (Gx : ℝ → E → E →L[ℝ] ℝ) (x : P.Trajectory) (t : P.Time) :
    Continuous fun u : P.Control =>
      Problem.stateConstrainedHamiltonian P lam0 Φ Λ Gx t (x t, (u : V)) := by
  unfold Problem.stateConstrainedHamiltonian
  exact ((continuous_runningCost_control P x t).const_mul lam0).sub
      ((Φ t - Λ t • Gx t (x t)).continuous.comp (continuous_dynamics_control P x t))

end Integrability

section StieltjesIBP

/-- **Stieltjes integration by parts for a nonincreasing multiplier and an absolutely continuous
scalar function.**  If `g s = c + ∫ r in 0..s, k r` on `[0,T]` and `λ` is nonincreasing and
nonnegative with `λ(T) = 0`, then the integral of `λ * k` equals the Stieltjes integral of `g`
minus the boundary term `c * μ(0,T]`. -/
theorem intervalIntegral_lam_mul_eq_stieltjes {T : ℝ} (hT : 0 ≤ T) {lam : ℝ → ℝ}
    (hanti : AntitoneOn lam (Icc (0 : ℝ) T))
    (hlam : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ lam t) (hlamT : lam T = 0)
    {k : ℝ → ℝ} (hk : IntervalIntegrable k volume 0 T) {g : ℝ → ℝ} {c : ℝ}
    (hg : ∀ s ∈ Icc (0 : ℝ) T, g s = c + ∫ r in (0 : ℝ)..s, k r) :
    (∫ r in (0 : ℝ)..T, lam r * k r)
      = (∫ s in Ioc 0 T, g s ∂(multiplierMeasure hT hanti))
        - c * (multiplierMeasure hT hanti).real (Ioc 0 T) := by
  set μ := multiplierMeasure hT hanti with hμ
  have hrm := rightMultiplier_ae_eq hT hanti
  have hreal : ∀ r ∈ Icc (0 : ℝ) T, μ.real (Ioc r T) = rightMultiplier T lam r :=
    fun r _ => real_Ioc_multiplierMeasure hT hanti hlam hlamT r
  have hcongr : (∫ r in (0 : ℝ)..T, μ.real (Ioc r T) * k r)
      = ∫ r in (0 : ℝ)..T, lam r * k r := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hrm] with r hr hrI
    rw [uIoc_of_le hT] at hrI
    have hrI' : r ∈ Icc (0 : ℝ) T := ⟨hrI.1.le, hrI.2⟩
    rw [hreal r hrI', hr hrI']
  have hprim := integral_Ioc_primitive_stieltjes (μ := μ) (c := c) hT hk
  have hgeq : (∫ s in Ioc 0 T, g s ∂μ) = ∫ s in Ioc 0 T, (c + ∫ r in (0 : ℝ)..s, k r) ∂μ := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    exact hg s ⟨hs.1.le, hs.2⟩
  rw [hgeq, hprim, hcongr]
  ring

/-- **Stieltjes cancellation for two paths with identical initial state.**  When two trajectories
satisfy the same initial condition `g₁(0) = g₂(0) = c`, the initial boundary terms in the
Stieltjes integration by parts cancel, leaving the difference of the Stieltjes integrals. -/
theorem intervalIntegral_lam_mul_sub_eq_stieltjes {T : ℝ} (hT : 0 ≤ T) {lam : ℝ → ℝ}
    (hanti : AntitoneOn lam (Icc (0 : ℝ) T))
    (hlam : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ lam t) (hlamT : lam T = 0)
    {k₁ k₂ : ℝ → ℝ}
    (hk₁ : IntervalIntegrable k₁ volume 0 T) (hk₂ : IntervalIntegrable k₂ volume 0 T)
    {g₁ g₂ : ℝ → ℝ} {c : ℝ}
    (hg₁ : ∀ s ∈ Icc (0 : ℝ) T, g₁ s = c + ∫ r in (0 : ℝ)..s, k₁ r)
    (hg₂ : ∀ s ∈ Icc (0 : ℝ) T, g₂ s = c + ∫ r in (0 : ℝ)..s, k₂ r) :
    (∫ r in (0 : ℝ)..T, lam r * k₁ r) - (∫ r in (0 : ℝ)..T, lam r * k₂ r)
      = (∫ s in Ioc 0 T, g₁ s ∂(multiplierMeasure hT hanti))
        - (∫ s in Ioc 0 T, g₂ s ∂(multiplierMeasure hT hanti)) := by
  have h1 := intervalIntegral_lam_mul_eq_stieltjes hT hanti hlam hlamT hk₁ hg₁
  have h2 := intervalIntegral_lam_mul_eq_stieltjes hT hanti hlam hlamT hk₂ hg₂
  linarith

end StieltjesIBP

section HorizonConversion

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A normalised horizon integral of a line function is `T⁻¹` times its interval integral. -/
theorem integral_horizonProbability_eq_intervalIntegral (P : Problem E V W)
    (f : ℝ → ℝ) :
    (∫ t : P.Time, f t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure)
      = P.horizon⁻¹ * ∫ s in (0 : ℝ)..P.horizon, f s := by
  have hT : (0 : ℝ) ≤ P.horizon := P.horizon_pos.le
  rw [Problem.integral_horizonProbability_coe P f]
  congr 1
  rw [ACEulerLagrange.timeMeasure, intervalIntegral.integral_of_le hT]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The difference of two interval integrable line functions restricts to an integrable function
for the normalised horizon probability. -/
theorem integrable_lam_difference (P : Problem E V W)
    {f₁ f₂ : ℝ → ℝ}
    (hf₁ : IntervalIntegrable f₁ volume 0 P.horizon)
    (hf₂ : IntervalIntegrable f₂ volume 0 P.horizon) :
    Integrable (fun t : P.Time => f₁ t - f₂ t)
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hT : (0 : ℝ) ≤ P.horizon := P.horizon_pos.le
  have h1 : Integrable (fun t : P.Time => f₁ t)
      (horizonProbability P.horizon P.horizon_pos).toMeasure :=
    Problem.integrable_horizonProbability_coe P
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hf₁)
  have h2 : Integrable (fun t : P.Time => f₂ t)
      (horizonProbability P.horizon P.horizon_pos).toMeasure :=
    Problem.integrable_horizonProbability_coe P
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hf₂)
  exact h1.sub h2

end HorizonConversion

section ConvexSupport

/-- **The state-constrained cost-integrand support bound.**  Under joint convexity of the
state-constrained modified Hamiltonian `H̃ = λ⁰ f⁰ − (Φ − Λ∇G) · f`, the running cost integrand is
bounded below by the tangent support at the reference point plus the momentum and multiplier
pairings with the realised velocity. -/
theorem stateConstrainedHamiltonian_cost_lower_bound (P : Problem E V W) (lam0 : ℝ)
    (Φ : ℝ → E →L[ℝ] ℝ) (pd : ℝ → E →L[ℝ] ℝ) (Λ : ℝ → ℝ) (Gx : ℝ → E → E →L[ℝ] ℝ)
    (H : P.Time → E × V → ℝ) (Hd : P.Time → E × V → (E × V) →L[ℝ] ℝ)
    (hH : ∀ t z, H t z = Problem.stateConstrainedHamiltonian P lam0 Φ Λ Gx t z)
    (hHd : ∀ t z, HasFDerivAt (fun w : E × V => H t w) (Hd t z) z)
    (hconv : ∀ t, ConvexOn ℝ univ (fun w : E × V => H t w))
    (x : P.Trajectory) (ρ : P.Relaxed) (y : E) (u₀ : P.Control) (t : P.Time)
    (hcostate_t : (Hd t (y, (u₀ : V))).comp (ContinuousLinearMap.inl ℝ E V) = pd (t : ℝ))
    (hpmp_t : ∀ v : P.Control,
      (Hd t (y, (u₀ : V))).comp (ContinuousLinearMap.inr ℝ E V) ((v : V) - (u₀ : V)) ≥ 0) :
    H t (y, (u₀ : V)) + pd (t : ℝ) (x t - y)
      + (Φ t - Λ t • Gx t (x t)) (Problem.realizedVelocity P x ρ t)
      ≤ ∫ u : P.Control, lam0 * P.runningCost t (x t) (u : V) ∂ρ.kernel t := by
  have hHint : Integrable (fun u : P.Control => H t (x t, (u : V))) (ρ.kernel t) := by
    have heq : (fun u : P.Control => H t (x t, (u : V)))
        = fun u : P.Control =>
            Problem.stateConstrainedHamiltonian P lam0 Φ Λ Gx t (x t, (u : V)) := by
      funext u
      exact hH t _
    rw [heq]
    have hcont := continuous_stateConstrainedHamiltonian_control P lam0 Φ Λ Gx x t
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlb := hamiltonian_integral_lower_bound P H Hd hHd hconv x ρ y u₀ t
    hcostate_t hpmp_t hHint
  let L : E →L[ℝ] ℝ := Φ t - Λ t • Gx t (x t)
  have hpoint : ∀ u : P.Control, lam0 * P.runningCost t (x t) (u : V)
      = H t (x t, (u : V)) + L (P.dynamics t (x t) (u : V)) := by
    intro u
    rw [hH t]
    simp only [Problem.stateConstrainedHamiltonian, L]
    ring
  have hsplit : (∫ u : P.Control, lam0 * P.runningCost t (x t) (u : V) ∂ρ.kernel t)
      = (∫ u : P.Control, H t (x t, (u : V)) ∂ρ.kernel t)
        + L (Problem.realizedVelocity P x ρ t) := by
    rw [show (∫ u : P.Control, lam0 * P.runningCost t (x t) (u : V) ∂ρ.kernel t)
        = ∫ u : P.Control,
            (H t (x t, (u : V)) + L (P.dynamics t (x t) (u : V))) ∂ρ.kernel t from
          integral_congr_ae (Eventually.of_forall hpoint)]
    rw [integral_add hHint (L.integrable_comp (P.integrable_dynamics_control x t (ρ.kernel t)))]
    rw [ContinuousLinearMap.integral_comp_comm L
      (P.integrable_dynamics_control x t (ρ.kernel t))]
    rfl
  linarith [hlb, hsplit]

end ConvexSupport

section Sufficiency

variable {P : Problem E V W}

/-- **The algebraic sufficiency identity of Berkovitz & Medhin (11.8.6)–(11.8.10) for
state-constrained problems.**

Under joint convexity of the state-constrained modified Hamiltonian `H̃ = λ⁰ f⁰ − (Φ − Λ∇G) · f`,
the costate equation `Φ' = H̃_x`, the pointwise minimum principle `H̃_u(u − u₀) ≥ 0`, and the
Stieltjes representation of the constraint multiplier `Λ`, the relaxed cost difference dominates
the sum of the transversality pairing and the Stieltjes pairing `−∫ G dΛ`. -/
theorem relaxedCost_sub_lowerBound_of_boundedStateExtremal_of_convex_stateConstrained
    (P : Problem E V W) (γ₀ : VelocityTrajectory P) (u₀ : P.Time → P.Control)
    (hu₀ : Measurable u₀)
    (lam0 : ℝ)
    (Φ Φd : ℝ → E →L[ℝ] ℝ)
    (Λ : ℝ → ℝ) (Gx : ℝ → E → E →L[ℝ] ℝ)
    (H : P.Time → E × V → ℝ) (Hd : P.Time → E × V → (E × V) →L[ℝ] ℝ)
    (hH : ∀ t z, H t z = Problem.stateConstrainedHamiltonian P lam0 Φ Λ Gx t z)
    (hHd : ∀ t z, HasFDerivAt (fun w : E × V => H t w) (Hd t z) z)
    (hconv : ∀ t, ConvexOn ℝ univ (fun w : E × V => H t w))
    (hΦ_int : IntervalIntegrable Φd volume 0 P.horizon)
    (hΦ : ∀ t ∈ Set.Icc (0 : ℝ) P.horizon, Φ t = Φ 0 + ∫ r in (0 : ℝ)..t, Φd r)
    (hcostate : ∀ᵐ (t : P.Time) ∂(horizonProbability P.horizon P.horizon_pos).toMeasure,
      Φd t = (Hd t (γ₀.value t, u₀ t)).comp (ContinuousLinearMap.inl ℝ E V))
    (hpmp : ∀ᵐ (t : P.Time) ∂(horizonProbability P.horizon P.horizon_pos).toMeasure,
      ∀ v : P.Control,
      (Hd t (γ₀.value t, u₀ t)).comp (ContinuousLinearMap.inr ℝ E V)
        ((v : V) - (u₀ t : V)) ≥ 0)
    (γ : VelocityTrajectory P) (ρ : P.Relaxed)
    (hadm : P.IsRelaxedAdmissible (toBoundedPath γ) ρ)
    (hvel₀ : (fun t : P.Time => γ₀.velocity t)
        =ᵐ[(horizonProbability P.horizon P.horizon_pos).toMeasure]
          fun t : P.Time => P.dynamics t (γ₀.value t) (u₀ t))
    (hk_lam_int : IntervalIntegrable (fun r => Λ r * (Gx r (γ.value r) (γ.velocity r)))
      volume 0 P.horizon)
    (hk₀_lam_int : IntervalIntegrable (fun r => Λ r * (Gx r (γ₀.value r) (γ₀.velocity r)))
      volume 0 P.horizon) :
    (∫ t : P.Time, (Φd t ((toBoundedPath γ) t - γ₀.value t)
        + Φ t (Problem.realizedVelocity P (toBoundedPath γ) ρ t)
        - Φ t (P.dynamics t (γ₀.value t) (u₀ t)))
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure)
      - (∫ t : P.Time, (Λ t * (Gx t (γ.value t) (γ.velocity t))
          - Λ t * (Gx t (γ₀.value t) (γ₀.velocity t)))
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure)
      ≤ lam0 * (P.relaxedCost (toBoundedPath γ) ρ
          - P.relaxedCost (toBoundedPath γ₀)
              (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ hu₀)) := by
  let ν := horizonProbability P.horizon P.horizon_pos
  let ρ₀ := RelaxedControl.ofControl ν u₀ hu₀
  have hvel := realizedVelocity_ae_eq_velocity_of_isRelaxedAdmissible P γ ρ hadm
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
  let R_transv : P.Time → ℝ := fun t => Φd t ((toBoundedPath γ) t - γ₀.value t)
    + Φ t (Problem.realizedVelocity P (toBoundedPath γ) ρ t)
    - Φ t (P.dynamics t (γ₀.value t) (u₀ t))
  let R_lam : P.Time → ℝ := fun t =>
    Λ t * (Gx t (γ.value t) (γ.velocity t)) - Λ t * (Gx t (γ₀.value t) (γ₀.velocity t))
  let R : P.Time → ℝ := fun t => R_transv t - R_lam t
  have hbound_ae : ∀ᵐ t ∂ν.toMeasure, R t ≤ A t - B t := by
    filter_upwards [hcostate, hpmp, hvel, hvel₀] with t hc hp hv hv₀
    have h := stateConstrainedHamiltonian_cost_lower_bound P lam0 Φ Φd Λ Gx H Hd hH hHd hconv
      (toBoundedPath γ) ρ (γ₀.value t) (u₀ t) t hc.symm hp
    have hHval : H t (γ₀.value t, (u₀ t : V))
        = lam0 * P.runningCost t (γ₀.value t) (u₀ t)
          - (Φ t - Λ t • Gx t (γ₀.value t)) (P.dynamics t (γ₀.value t) (u₀ t)) := by
      rw [hH t]
      simp only [Problem.stateConstrainedHamiltonian]
    simp only [R, R_transv, R_lam, A, B]
    have hLγ : (Φ t - Λ t • Gx t ((toBoundedPath γ) t))
        (Problem.realizedVelocity P (toBoundedPath γ) ρ t)
        = Φ t (Problem.realizedVelocity P (toBoundedPath γ) ρ t)
          - Λ t * (Gx t (γ.value t) (γ.velocity t)) := by
      simp only [sub_apply, smul_apply, smul_eq_mul]
      rw [toBoundedPath_apply, hv]
    have hLγ₀ : (Φ t - Λ t • Gx t (γ₀.value t)) (P.dynamics t (γ₀.value t) (u₀ t))
        = Φ t (P.dynamics t (γ₀.value t) (u₀ t))
          - Λ t * (Gx t (γ₀.value t) (γ₀.velocity t)) := by
      simp only [sub_apply, smul_apply, smul_eq_mul]
      rw [← hv₀]
    nlinarith [h, hHval, hLγ, hLγ₀]
  have hA : Integrable A ν.toMeasure := by
    have hcont : Continuous fun z : P.Time × P.Control =>
        lam0 * P.runningCost z.1 ((toBoundedPath γ) z.1) (z.2 : V) :=
      (P.continuous_runningCost_along (toBoundedPath γ)).const_mul lam0
    exact integrable_average_of_continuous P ρ hcont
  have hB : Integrable B ν.toMeasure :=
    (integrable_runningCost_reference P γ₀ u₀ hu₀).const_mul lam0
  have hR_transv : Integrable R_transv ν.toMeasure := by
    simp only [R_transv]
    exact ((integrable_pd_value_sub P γ₀ hΦ_int γ).add
      (integrable_momentum_realizedVelocity P γ ρ hΦ_int hΦ)).sub
        (integrable_momentum_dynamics_reference P γ₀ u₀ hu₀ hΦ_int hΦ)
  have hR_lam : Integrable R_lam ν.toMeasure :=
    integrable_lam_difference P hk_lam_int hk₀_lam_int
  have hRint : Integrable R ν.toMeasure := hR_transv.sub hR_lam
  have h1 : (∫ t : P.Time, (A t - B t) ∂ν.toMeasure) ≥ ∫ t : P.Time, R t ∂ν.toMeasure :=
    integral_mono_ae hRint (hA.sub hB) hbound_ae
  have h2 : (∫ t : P.Time, (A t - B t) ∂ν.toMeasure)
      = (∫ t : P.Time, A t ∂ν.toMeasure) - ∫ t : P.Time, B t ∂ν.toMeasure :=
    integral_sub hA hB
  have hRsplit : (∫ t : P.Time, R t ∂ν.toMeasure)
      = (∫ t : P.Time, R_transv t ∂ν.toMeasure) - ∫ t : P.Time, R_lam t ∂ν.toMeasure :=
    integral_sub hR_transv hR_lam
  rw [mul_sub, hcostγ, hcostγ₀, ← h2]
  linarith [h1, hRsplit]

/-- **Mangasarian sufficiency of the maximum principle for state-constrained problems
(Berkovitz & Medhin, Theorem 11.8.4).**

Let `(γ₀, u₀)` be an admissible pair carrying the maximum-principle multiplier data `(Φ, Λ, β, λ⁰)`
at weight `λ⁰ > 0`:
* `H̃ = λ⁰ f⁰ − (Φ − Λ∇G) · f` is jointly convex in `(x, u)`;
* its Fréchet derivative `Hd` satisfies the costate equation `Φd = ∂ₓH̃` and the pointwise
  minimum principle `∂ᵤH̃(v − u₀) ≥ 0`;
* `Φ` is an absolutely continuous primitive of `Φd`, with terminal transversality `Φ(t₁) = −β ∂₂T`;
* the endpoint constraint `T` is affine at the reference;
* `Λ ≥ 0` is nonincreasing on `[0, t₁]` with `Λ(t₁) = 0`;
* along each admissible path, `G(·, γ)` is an absolutely continuous primitive of `∇G(·, γ)·γ'`;
* complementarity holds at the reference in the `μ = −dΛ` convention: `0 ≤ ∫_{(0, t₁]} G(·, γ₀) dμ`
  (equivalently `∫_{(0, t₁]} G(·, γ₀) dΛ = 0`, since `G(·, γ₀) ≤ 0`).

Note on sign conventions: `stateConstrainedHamiltonian` uses `−(Φ − Λ∇G)·f`, i.e. the `Λ∇G` shift
enters with a `+` (consistent with BM and with R1's `exists_boundedStateMaximumPrinciple`);
`EpsilonOptimality.modifiedHamiltonian` writes the shift as `−(Ψ + Λ∇G)·f`, so the two differ only
by the sign convention on the constraint multiplier, not in content.

Then `(γ₀, u₀)` is a relaxed minimum on the velocity trajectory carrier. -/
theorem isVelocityRelaxedMinimum_of_boundedStateExtremal_of_convex_stateConstrained
    (P : Problem E V W) (γ₀ : VelocityTrajectory P) (u₀ : P.Time → P.Control)
    (hu₀ : Measurable u₀)
    (hadm₀ : P.IsRelaxedAdmissible (toBoundedPath γ₀)
      (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ hu₀))
    (hvel₀ : (fun t : P.Time => γ₀.velocity t)
        =ᵐ[(horizonProbability P.horizon P.horizon_pos).toMeasure]
          fun t : P.Time => P.dynamics t (γ₀.value t) (u₀ t))
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (Φ Φd : ℝ → E →L[ℝ] ℝ)
    (Λ : ℝ → ℝ) (Gx : ℝ → E → E →L[ℝ] ℝ)
    (H : P.Time → E × V → ℝ) (Hd : P.Time → E × V → (E × V) →L[ℝ] ℝ)
    (hH : ∀ t z, H t z = Problem.stateConstrainedHamiltonian P lam0 Φ Λ Gx t z)
    (hHd : ∀ t z, HasFDerivAt (fun w : E × V => H t w) (Hd t z) z)
    (hconv : ∀ t, ConvexOn ℝ univ (fun w : E × V => H t w))
    (hΦ_int : IntervalIntegrable Φd volume 0 P.horizon)
    (hΦ : ∀ t ∈ Set.Icc (0 : ℝ) P.horizon, Φ t = Φ 0 + ∫ r in (0 : ℝ)..t, Φd r)
    (hcostate : ∀ᵐ (t : P.Time) ∂(horizonProbability P.horizon P.horizon_pos).toMeasure,
      Φd t = (Hd t (γ₀.value t, u₀ t)).comp (ContinuousLinearMap.inl ℝ E V))
    (hpmp : ∀ᵐ (t : P.Time) ∂(horizonProbability P.horizon P.horizon_pos).toMeasure,
      ∀ v : P.Control,
      (Hd t (γ₀.value t, u₀ t)).comp (ContinuousLinearMap.inr ℝ E V)
        ((v : V) - (u₀ t : V)) ≥ 0)
    (β : W →L[ℝ] ℝ)
    (hΦ_term : Φ P.horizon = -β.comp
      ((fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        (γ₀.value 0, γ₀.value P.horizon)).comp (ContinuousLinearMap.inr ℝ E E)))
    (hT_affine : ∀ x y : E, P.endpointConstraint x y =
      (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        (γ₀.value 0, γ₀.value P.horizon)) (x - γ₀.value 0, y - γ₀.value P.horizon))
    (hΛ_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) P.horizon, 0 ≤ Λ t)
    (hΛ_anti : AntitoneOn Λ (Set.Icc (0 : ℝ) P.horizon))
    (hΛ_term : Λ P.horizon = 0)
    (G : ℝ → E → ℝ)
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hk₀_int : IntervalIntegrable (fun r => Gx r (γ₀.value r) (γ₀.velocity r)) volume 0 P.horizon)
    (hk₀_lam_int : IntervalIntegrable (fun r => Λ r * (Gx r (γ₀.value r) (γ₀.velocity r)))
      volume 0 P.horizon)
    (hG_prim₀ : ∀ s ∈ Set.Icc (0 : ℝ) P.horizon,
      G s (γ₀.value s) = G 0 (γ₀.value 0) + ∫ r in (0 : ℝ)..s, Gx r (γ₀.value r) (γ₀.velocity r))
    (hcomp₀ : 0 ≤ ∫ s in Set.Ioc (0 : ℝ) P.horizon, G s (γ₀.value s)
      ∂(multiplierMeasure P.horizon_pos.le hΛ_anti))
    (hk_int : ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      P.IsRelaxedAdmissible (toBoundedPath γ) ρ →
        IntervalIntegrable (fun r => Gx r (γ.value r) (γ.velocity r)) volume 0 P.horizon)
    (hk_lam_int : ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      P.IsRelaxedAdmissible (toBoundedPath γ) ρ →
        IntervalIntegrable (fun r => Λ r * (Gx r (γ.value r) (γ.velocity r))) volume 0 P.horizon)
    (hG_prim : ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      P.IsRelaxedAdmissible (toBoundedPath γ) ρ →
        ∀ s ∈ Set.Icc (0 : ℝ) P.horizon,
          G s (γ.value s) = G 0 (γ.value 0) + ∫ r in (0 : ℝ)..s, Gx r (γ.value r) (γ.velocity r)) :
    IsVelocityRelaxedMinimum P γ₀
      (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ hu₀) := by
  refine ⟨hadm₀, ?_⟩
  intro γ ρ hadm
  have hvel := realizedVelocity_ae_eq_velocity_of_isRelaxedAdmissible P γ ρ hadm
  have hk_int_γ := hk_int γ ρ hadm
  have hk_lam_int_γ := hk_lam_int γ ρ hadm
  have hG_prim_γ := hG_prim γ ρ hadm
  have h := relaxedCost_sub_lowerBound_of_boundedStateExtremal_of_convex_stateConstrained
    P γ₀ u₀ hu₀ lam0 Φ Φd Λ Gx H Hd hH hHd hconv hΦ_int hΦ hcostate hpmp
    γ ρ hadm hvel₀ hk_lam_int_γ hk₀_lam_int
  have hinit₀ : γ₀.value 0 = P.initial := by
    have h0 := IsRelaxedTrajectory.initial hadm₀.1
    simpa [toBoundedPath_apply, timeZero] using h0
  have hinit : γ.value 0 = P.initial := by
    have h0 := IsRelaxedTrajectory.initial hadm.1
    simpa [toBoundedPath_apply, timeZero] using h0
  have hTγ : P.endpointConstraint (γ.value 0) (γ.value P.horizon) = 0 := by
    have h0 := hadm.2.1
    simpa [toBoundedPath_apply, timeZero, timeEnd] using h0
  have hboundary := integral_transversalityPairing_eq P γ₀ γ u₀ ρ hvel₀ hvel Φ Φd hΦ_int hΦ
  have hpair : 0 ≤ Φ P.horizon (γ.value P.horizon - γ₀.value P.horizon)
      - Φ 0 (γ.value 0 - γ₀.value 0) :=
    boundaryPairing_nonneg_of_affineEndpoint P γ₀ γ Φ β hinit₀ hinit hΦ_term hT_affine hTγ
  have hb_transv : 0 ≤ ∫ t : P.Time, (Φd t ((toBoundedPath γ) t - γ₀.value t)
      + Φ t (Problem.realizedVelocity P (toBoundedPath γ) ρ t)
      - Φ t (P.dynamics t (γ₀.value t) (u₀ t)))
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure := by
    rw [hboundary]
    exact mul_nonneg (inv_nonneg.mpr P.horizon_pos.le) hpair
  have hinit_G : G 0 (γ.value 0) = G 0 (γ₀.value 0) := by rw [hinit, hinit₀]
  have hG_prim_γ' : ∀ s ∈ Set.Icc (0 : ℝ) P.horizon,
      G s (γ.value s) = G 0 (γ₀.value 0) + ∫ r in (0 : ℝ)..s, Gx r (γ.value r) (γ.velocity r) := by
    intro s hs
    rw [← hinit_G]
    exact hG_prim_γ s hs
  have hstieltjes := intervalIntegral_lam_mul_sub_eq_stieltjes P.horizon_pos.le hΛ_anti
    hΛ_nonneg hΛ_term hk_int_γ hk₀_int hG_prim_γ' hG_prim₀
  have h_int_equiv : (∫ t : P.Time, (Λ t * (Gx t (γ.value t) (γ.velocity t))
        - Λ t * (Gx t (γ₀.value t) (γ₀.velocity t)))
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure)
      = P.horizon⁻¹ * (∫ s in (0 : ℝ)..P.horizon,
        (Λ s * (Gx s (γ.value s) (γ.velocity s)) - Λ s * (Gx s (γ₀.value s) (γ₀.velocity s)))) :=
    integral_horizonProbability_eq_intervalIntegral P (fun s =>
      Λ s * (Gx s (γ.value s) (γ.velocity s)) - Λ s * (Gx s (γ₀.value s) (γ₀.velocity s)))
  have hstieltjes_sub : (∫ s in (0 : ℝ)..P.horizon,
        (Λ s * (Gx s (γ.value s) (γ.velocity s)) - Λ s * (Gx s (γ₀.value s) (γ₀.velocity s))))
      = (∫ s in Set.Ioc (0 : ℝ) P.horizon, G s (γ.value s)
          ∂(multiplierMeasure P.horizon_pos.le hΛ_anti))
        - (∫ s in Set.Ioc (0 : ℝ) P.horizon, G s (γ₀.value s)
          ∂(multiplierMeasure P.horizon_pos.le hΛ_anti)) := by
    rw [intervalIntegral.integral_sub hk_lam_int_γ hk₀_lam_int]
    exact hstieltjes
  have hG_nonpos : ∀ s ∈ Set.Ioc (0 : ℝ) P.horizon, G s (γ.value s) ≤ 0 := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) P.horizon := ⟨hs.1.le, hs.2⟩
    let t : P.Time := ⟨s, hs'⟩
    have hstate := hadm.2.2 t
    have hGP_t := hGP t (γ.value s)
    change P.stateConstraint t ((toBoundedPath γ) t) ≤ 0 at hstate
    rw [toBoundedPath_apply, hGP_t] at hstate
    exact hstate
  have hstieltjes_γ_nonpos : (∫ s in Set.Ioc (0 : ℝ) P.horizon, G s (γ.value s)
      ∂(multiplierMeasure P.horizon_pos.le hΛ_anti)) ≤ 0 :=
    setIntegral_nonpos measurableSet_Ioc hG_nonpos
  have hb_stieltjes : 0 ≤ - (∫ t : P.Time, (Λ t * (Gx t (γ.value t) (γ.velocity t))
        - Λ t * (Gx t (γ₀.value t) (γ₀.velocity t)))
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure) := by
    rw [h_int_equiv, hstieltjes_sub]
    have hdiff_nonpos : (∫ s in Set.Ioc (0 : ℝ) P.horizon, G s (γ.value s)
          ∂(multiplierMeasure P.horizon_pos.le hΛ_anti))
        - (∫ s in Set.Ioc (0 : ℝ) P.horizon, G s (γ₀.value s)
          ∂(multiplierMeasure P.horizon_pos.le hΛ_anti)) ≤ 0 := by
      linarith [hstieltjes_γ_nonpos, hcomp₀]
    have hprod_nonpos : P.horizon⁻¹ * ((∫ s in Set.Ioc (0 : ℝ) P.horizon, G s (γ.value s)
          ∂(multiplierMeasure P.horizon_pos.le hΛ_anti))
        - (∫ s in Set.Ioc (0 : ℝ) P.horizon, G s (γ₀.value s)
          ∂(multiplierMeasure P.horizon_pos.le hΛ_anti))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr P.horizon_pos.le) hdiff_nonpos
    linarith
  have htotal_nonneg : 0 ≤ lam0 * (P.relaxedCost (toBoundedPath γ) ρ
      - P.relaxedCost (toBoundedPath γ₀)
          (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ hu₀)) := by
    linarith [h, hb_transv, hb_stieltjes]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right htotal_nonneg hlam0)

/-- **The Volterra-carrier sufficiency theorem for state-constrained problems.**
Minimality on the velocity trajectory carrier implies relaxed minimality on the library's
standard Volterra trajectory carrier. -/
theorem isRelaxedMinimum_of_boundedStateExtremal_of_convex_stateConstrained
    (P : Problem E V W) (γ₀ : VelocityTrajectory P) (u₀ : P.Time → P.Control)
    (hu₀ : Measurable u₀)
    (hadm₀ : P.IsRelaxedAdmissible (toBoundedPath γ₀)
      (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ hu₀))
    (hvel₀ : (fun t : P.Time => γ₀.velocity t)
        =ᵐ[(horizonProbability P.horizon P.horizon_pos).toMeasure]
          fun t : P.Time => P.dynamics t (γ₀.value t) (u₀ t))
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (Φ Φd : ℝ → E →L[ℝ] ℝ)
    (Λ : ℝ → ℝ) (Gx : ℝ → E → E →L[ℝ] ℝ)
    (H : P.Time → E × V → ℝ) (Hd : P.Time → E × V → (E × V) →L[ℝ] ℝ)
    (hH : ∀ t z, H t z = Problem.stateConstrainedHamiltonian P lam0 Φ Λ Gx t z)
    (hHd : ∀ t z, HasFDerivAt (fun w : E × V => H t w) (Hd t z) z)
    (hconv : ∀ t, ConvexOn ℝ univ (fun w : E × V => H t w))
    (hΦ_int : IntervalIntegrable Φd volume 0 P.horizon)
    (hΦ : ∀ t ∈ Set.Icc (0 : ℝ) P.horizon, Φ t = Φ 0 + ∫ r in (0 : ℝ)..t, Φd r)
    (hcostate : ∀ᵐ (t : P.Time) ∂(horizonProbability P.horizon P.horizon_pos).toMeasure,
      Φd t = (Hd t (γ₀.value t, u₀ t)).comp (ContinuousLinearMap.inl ℝ E V))
    (hpmp : ∀ᵐ (t : P.Time) ∂(horizonProbability P.horizon P.horizon_pos).toMeasure,
      ∀ v : P.Control,
      (Hd t (γ₀.value t, u₀ t)).comp (ContinuousLinearMap.inr ℝ E V)
        ((v : V) - (u₀ t : V)) ≥ 0)
    (β : W →L[ℝ] ℝ)
    (hΦ_term : Φ P.horizon = -β.comp
      ((fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        (γ₀.value 0, γ₀.value P.horizon)).comp (ContinuousLinearMap.inr ℝ E E)))
    (hT_affine : ∀ x y : E, P.endpointConstraint x y =
      (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        (γ₀.value 0, γ₀.value P.horizon)) (x - γ₀.value 0, y - γ₀.value P.horizon))
    (hΛ_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) P.horizon, 0 ≤ Λ t)
    (hΛ_anti : AntitoneOn Λ (Set.Icc (0 : ℝ) P.horizon))
    (hΛ_term : Λ P.horizon = 0)
    (G : ℝ → E → ℝ)
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hk₀_int : IntervalIntegrable (fun r => Gx r (γ₀.value r) (γ₀.velocity r)) volume 0 P.horizon)
    (hk₀_lam_int : IntervalIntegrable (fun r => Λ r * (Gx r (γ₀.value r) (γ₀.velocity r)))
      volume 0 P.horizon)
    (hG_prim₀ : ∀ s ∈ Set.Icc (0 : ℝ) P.horizon,
      G s (γ₀.value s) = G 0 (γ₀.value 0) + ∫ r in (0 : ℝ)..s, Gx r (γ₀.value r) (γ₀.velocity r))
    (hcomp₀ : 0 ≤ ∫ s in Set.Ioc (0 : ℝ) P.horizon, G s (γ₀.value s)
      ∂(multiplierMeasure P.horizon_pos.le hΛ_anti))
    (hk_int : ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      P.IsRelaxedAdmissible (toBoundedPath γ) ρ →
        IntervalIntegrable (fun r => Gx r (γ.value r) (γ.velocity r)) volume 0 P.horizon)
    (hk_lam_int : ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      P.IsRelaxedAdmissible (toBoundedPath γ) ρ →
        IntervalIntegrable (fun r => Λ r * (Gx r (γ.value r) (γ.velocity r))) volume 0 P.horizon)
    (hG_prim : ∀ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      P.IsRelaxedAdmissible (toBoundedPath γ) ρ →
        ∀ s ∈ Set.Icc (0 : ℝ) P.horizon,
          G s (γ.value s) = G 0 (γ.value 0) + ∫ r in (0 : ℝ)..s, Gx r (γ.value r) (γ.velocity r)) :
    P.IsRelaxedMinimum (toBoundedPath γ₀)
      (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u₀ hu₀) :=
  isRelaxedMinimum_of_isVelocityRelaxedMinimum P γ₀ _
    (isVelocityRelaxedMinimum_of_boundedStateExtremal_of_convex_stateConstrained
      P γ₀ u₀ hu₀ hadm₀ hvel₀ lam0 hlam0 Φ Φd Λ Gx H Hd hH hHd hconv hΦ_int hΦ hcostate hpmp
      β hΦ_term hT_affine hΛ_nonneg hΛ_anti hΛ_term G hGP hk₀_int hk₀_lam_int hG_prim₀ hcomp₀
      hk_int hk_lam_int hG_prim)

end Sufficiency

end OptimalControl.BoundedState
