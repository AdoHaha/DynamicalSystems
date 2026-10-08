/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.UnconstrainedMaximumPrinciple
public import DynamicalSystems.OptimalControl.ContinuousTime.TimeOptimal
public import DynamicalSystems.OptimalControl.ContinuousTime.FiniteSwitching
public import DynamicalSystems.OptimalControl.ContinuousTime.LinearSwitching
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The minimum-time maximum principle (Kirk §5.4 / Berkovitz–Medhin §6.8, Thm 6.3.17)

This module assembles the Pontryagin necessary conditions for the **minimum-time**
problem — the time-optimal problem with running cost `f⁰ ≡ 1` and a free terminal
time — off the merged R2 unconstrained maximum principle
`OptimalControl.BoundedState.exists_unconstrainedMaximumPrinciple_of_relaxed_minimum`
(Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Theorems 6.3.5
and 6.3.12).

For the minimum-time problem the cost integrand is identically `1`, so the relaxed
cost is the elapsed horizon `T` (`TimeOptimal.timeOptimalOCP_totalCost`).  Writing
`Ψ` for the costate, `λ⁰ ∈ [0,1]` for the cost coefficient and
`H(t,u) = λ⁰ T⁻¹ − Ψ(t)·f(t, x(t), u)` for the time-optimal Hamiltonian, the R2
theorem specialises to:

* `‖Ψ(T)‖ + ‖β‖ + λ⁰ = 1`, the integrated adjoint equation, the endpoint
  transversality `Ψ(0) = ∂₁T·β`, `Ψ(T) = −∂₂T·β`;
* the **a.e. pointwise Hamiltonian minimum** of `H` over the control set; and
* non-triviality `¬(Ψ ≡ 0 ∧ λ⁰ = 0)`.

This is the nonlinear minimum-time necessity statement of Kirk, *Optimal Control
Theory: An Introduction* (Dover 2004), §5.4 (the Hamiltonian `1 + pᵀf` and its
minimisation) and of Berkovitz & Medhin §6.8 for the linear case, restricted to
the hypotheses of R2 (a fixed-horizon, compact convex control set, an inactive
nondegenerate state constraint, and the endpoint-equality transversality).

## Free terminal time: what is and is not proved here

The *free-terminal-time transversality* `H(t₁) = 0` is **not** a consequence of the
fixed-horizon R2 theorem: R2 constrains only variations that keep the terminal time
fixed.  Deriving `H(t₁) = 0` from time-optimality is Berkovitz & Medhin's
Theorem 6.3.22 (the horizontal variation / orthogonality condition (6.3.24)), whose
proof is a genuine horizontal-variation argument not present in this library.  This
module therefore

* states the free-terminal-time condition as the explicit predicate
  `FreeTerminalTimeTransversality`, and proves that under it the time-optimal
  Hamiltonian vanishes at the terminal time (a definitional bridge, no black box);
* proves the **autonomous Hamiltonian conservation** `hamiltonian_conserved_of_autonomous`
  (Berkovitz & Medhin Theorem 6.3.17 / Corollary 6.3.19) in its pointwise
  (ordinary-control / smooth) form: for autonomous data, along a solution of
  `ẋ = f(x)` and a solution `Ψ' = −Ψ ∘ f'(x)` of the adjoint equation, the
  Hamiltonian `t ↦ c − Ψ(t)(f(x(t)))` is constant; consequently `H(t₁) = 0` forces
  `H ≡ 0` (`minimumTimeHamiltonian_eq_zero_of_conserved`);
* does **not** claim the full nonlinear minimum-time necessity with `H ≡ 0`, because
  the passage from time-optimality to `H(t₁) = 0` (BM 6.3.22) and the relaxed
  (averaged) conservation are not assembled here.

Book citations live in docstrings only; all declaration names are concept names.

## Main results

* `minimumTimeMaximumPrinciple`: the R2 maximum principle at `f⁰ ≡ 1`, with the
  time-optimal Hamiltonian `λ⁰ T⁻¹ − Ψ·f`.
* `hamiltonian_conserved_of_autonomous`: autonomous Hamiltonian conservation.
* `minimumTimeHamiltonian_eq_zero_of_conserved`: conservation plus `H(T) = 0`
  gives `H ≡ 0`.
* `timeOptimalHamiltonianMinimizer_bangBang`: the box bang-bang conclusion for a
  minimiser of the time-optimal Hamiltonian, reusing
  `TimeOptimal.linearMinimizer_bangBang` / `TimeOptimal.timeOptimal_bangBang`.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace OptimalControl.BoundedState

open Problem

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace V] [BorelSpace V]

/-! ## The time-optimal Hamiltonian -/

/-- The **time-optimal Hamiltonian** along a reference path `x`, for the problem with
running cost `f⁰ ≡ 1`:

`H(t, x, u) = λ⁰ T⁻¹ − Ψ(t)·f(t, x, u)`.

This is the `f⁰ ≡ 1` specialisation of the Hamiltonian of the maximum principle as
rendered in `exists_unconstrainedMaximumPrinciple_of_relaxed_minimum`
(`λ⁰ T⁻¹ f⁰ − Ψ·f`), i.e. of Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Theorem 6.3.5 (v) / Theorem 11.6.3 (v).  It is the `λ⁰`-scaled,
`T⁻¹`-normalised form of Kirk's minimum-time Hamiltonian `1 + pᵀf`
(*Optimal Control Theory: An Introduction*, Dover 2004, §5.4, Eq. (5.4-15)), with
costate `p = −Ψ` (the two minimisations have the same minimisers).

The `T⁻¹` factor normalises the unit-interval time marginal used by the library's
relaxed controls. -/
noncomputable def minimumTimeHamiltonian (P : Problem E V W) (lam0 : ℝ)
    (Ψ : ℝ → E →L[ℝ] ℝ) (t : P.Time) (z : E × V) : ℝ :=
  lam0 * P.horizon⁻¹ - Ψ t (P.dynamics t z.1 z.2)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem minimumTimeHamiltonian_apply (P : Problem E V W) (lam0 : ℝ)
    (Ψ : ℝ → E →L[ℝ] ℝ) (t : P.Time) (z : E × V) :
    minimumTimeHamiltonian P lam0 Ψ t z = lam0 * P.horizon⁻¹ - Ψ t (P.dynamics t z.1 z.2) :=
  rfl

/-! ## The minimum-time maximum principle -/

/-- **The minimum-time maximum principle (Kirk §5.4 / BM §6.8, Thms 6.3.5 and 6.3.12).**

Let `(γ₀, ρ₀)` be an optimal relaxed pair of the unconstrained problem whose running
cost is identically `1` (the time-optimal cost; the horizon `T` is fixed here).  Then
there are an absolutely continuous costate `Ψ`, an endpoint multiplier `β` and a cost
coefficient `λ⁰ ∈ [0,1]` such that

* (i)   `‖Ψ(T)‖ + ‖β‖ + λ⁰ = 1` (normalisation);
* (ii)  `Ψ(t) = Ψ(0) + ∫₀ᵗ (λ⁰ f⁰ₓ − Ψ·fₓ)` (integrated adjoint equation);
* (iii) `Ψ(0) = ∂₁T·β` and (iv) `Ψ(T) = −∂₂T·β` (endpoint transversality);
* (v)   for a.e. `t` the conditional law `ρ₀.kernel t` minimises the time-optimal
  Hamiltonian `minimumTimeHamiltonian` over every control value; and
* the multipliers `(Ψ, λ⁰)` do not both vanish.

The state multiplier `Λ` is identically zero.  This is the `f⁰ ≡ 1` specialisation of
`exists_unconstrainedMaximumPrinciple_of_relaxed_minimum`; its a.e. minimum clause is
the nonlinear minimum-time Hamiltonian condition of Kirk, *Optimal Control Theory: An
Introduction* (Dover 2004), §5.4, Eq. (5.4-15)–(5.4-16), and of Berkovitz & Medhin,
*Nonlinear Optimal Control Theory* (CRC 2012), §6.8.

The free-terminal-time transversality `H(t₁) = 0` is **not** concluded here; see the
module docstring and `FreeTerminalTimeTransversality`. -/
theorem minimumTimeMaximumPrinciple
    (P : Problem E V W) (D : P.SmoothData) (hD : P.DerivativeContinuity D)
    {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)}
    (hG : Continuous fun p : ℝ × E => G p.1 p.2)
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hGreg : StateConstraintRegularity G Gx) (hGx : StateGradientRegularity Gx Gxd)
    (hGdc : ∀ t, Continuous fun q : E × E => Gxd t q.1 (1, q.2))
    (hnondegenerate : ∀ (t : ℝ) (y : E), Gx t y ≠ 0)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (hT : ContDiff ℝ 1 (fun q : E × E => P.endpointConstraint q.1 q.2))
    {γ₀ : VelocityTrajectory P} {ρ₀ : P.Relaxed}
    (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) (hγ₀m : Measurable γ₀.velocity)
    (hinactive : ∀ (t : ℝ) (y : E), G t y < 0)
    (hcost : ∀ (t : P.Time) (x : E) (u : V), P.runningCost t x u = 1)
    (hrank : Function.Surjective ((fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
      (γ₀.value 0, γ₀.value P.horizon)).comp (ContinuousLinearMap.inr ℝ E E))) :
    ∃ (Ψ : ℝ → E →L[ℝ] ℝ) (β : (W →L[ℝ] ℝ) × (E →L[ℝ] ℝ)) (lam0 : ℝ),
      eVariationOn Ψ (Icc (0 : ℝ) P.horizon) ≠ ⊤ ∧
      AbsolutelyContinuousOnInterval Ψ 0 P.horizon ∧
      0 ≤ lam0 ∧ lam0 ≤ 1 ∧
      ‖Ψ P.horizon‖ + ‖β‖ + lam0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, Ψ t = Ψ 0 + ∫ r in (0 : ℝ)..t,
        (lam0 • P.averagedRunningCovector D ρ₀ r (γ₀.value r)
          - (ContinuousLinearMap.compL ℝ E E ℝ).flip
              (P.averagedDynamicsDerivative D ρ₀ r (γ₀.value r)) (Ψ r))) ∧
      Ψ 0 = tubeDl (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        (γ₀.value 0, γ₀.value P.horizon)) β ∧
      Ψ P.horizon = -(tubeDr (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
        (γ₀.value 0, γ₀.value P.horizon)) β) ∧
      (∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v : P.Control,
        ∫ u : P.Control, minimumTimeHamiltonian P lam0 Ψ t (γ₀.value t, (u : V))
            ∂ρ₀.kernel t
        ≤ minimumTimeHamiltonian P lam0 Ψ t (γ₀.value t, (v : V))) ∧
      ¬ ((∀ t ∈ Icc (0 : ℝ) P.horizon, Ψ t = 0) ∧ lam0 = 0) := by
  obtain ⟨Ψ, β, lam0, hBV, hAC, h0, h1, hnorm, hint, hinit, hterm, hmin, hnt⟩ :=
    exists_unconstrainedMaximumPrinciple_of_relaxed_minimum P D hD hG hGP hGreg hGx hGdc
      hnondegenerate hEnd hT hopt hγ₀m hinactive hrank
  refine ⟨Ψ, β, lam0, hBV, hAC, h0, h1, hnorm, hint, hinit, hterm, ?_, hnt⟩
  filter_upwards [hmin] with t ht v
  simpa only [minimumTimeHamiltonian_apply, hcost, mul_one] using ht v

/-! ## Free terminal time and autonomous conservation -/

/-- The **free-terminal-time transversality** of the minimum-time problem: the
reference relaxed control attains the value `0` of the time-optimal Hamiltonian at the
terminal time (Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012),
Theorem 6.3.22 / (6.3.24); Kirk, *Optimal Control Theory: An Introduction* (Dover
2004), §5.4).

For a time-invariant endpoint constraint this is exactly `H(t₁) = 0`.  It is stated
as an explicit predicate because its derivation from time-optimality is the horizontal
variation theorem BM 6.3.22, which is not formalised in this library; see the module
docstring. -/
def FreeTerminalTimeTransversality (P : Problem E V W) (lam0 : ℝ)
    (Ψ : ℝ → E →L[ℝ] ℝ) (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed) : Prop :=
  ∫ u : P.Control, minimumTimeHamiltonian P lam0 Ψ (timeEnd P.horizon P.horizon_pos.le)
      (γ₀.value P.horizon, (u : V)) ∂ρ₀.kernel (timeEnd P.horizon P.horizon_pos.le) = 0

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ W] in
/-- Under the free-terminal-time transversality the time-optimal Hamiltonian vanishes
at the terminal time (definitional bridge). -/
theorem minimumTimeHamiltonian_terminal_eq_zero_of_freeTerminalTime
    {P : Problem E V W} {lam0 : ℝ} {Ψ : ℝ → E →L[ℝ] ℝ}
    {γ₀ : VelocityTrajectory P} {ρ₀ : P.Relaxed}
    (h : FreeTerminalTimeTransversality P lam0 Ψ γ₀ ρ₀) :
    ∫ u : P.Control, minimumTimeHamiltonian P lam0 Ψ (timeEnd P.horizon P.horizon_pos.le)
        (γ₀.value P.horizon, (u : V)) ∂ρ₀.kernel (timeEnd P.horizon P.horizon_pos.le) = 0 :=
  h

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise (ordinary-control / smooth) form of the **autonomous Hamiltonian
conservation** of Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012),
Theorem 6.3.17 and Corollary 6.3.19.

Let `f : E → E` be autonomous with derivative `f'`, let `x` solve `ẋ = f(x)`, and let
the costate `Ψ` solve the pointwise adjoint equation `Ψ' = −Ψ ∘ f'(x)`.  Then the
Hamiltonian `t ↦ c − Ψ(t)(f(x(t)))` is constant.

This is the `f⁰ ≡ 1` Hamiltonian `λ⁰ T⁻¹ − Ψ·f` up to the constant `c`, whose
derivative vanishes because the `t`-dependence of the autonomous dynamics cancels the
adjoint term.  The relaxed (control-averaged) version is not assembled here. -/
theorem hamiltonian_conserved_of_autonomous
    {f : E → E} {f' : E → E →L[ℝ] E}
    {x : ℝ → E} {Ψ : ℝ → E →L[ℝ] ℝ} {c : ℝ}
    (hf : ∀ y, HasFDerivAt f (f' y) y)
    (hx : ∀ t, HasDerivAt x (f (x t)) t)
    (hΨ : ∀ t, HasDerivAt Ψ
      (-(ContinuousLinearMap.compL ℝ E E ℝ).flip (f' (x t)) (Ψ t)) t) :
    ∀ t, c - Ψ t (f (x t)) = c - Ψ 0 (f (x 0)) := by
  have hB : IsBoundedBilinearMap ℝ (fun p : (E →L[ℝ] ℝ) × E => p.1 p.2) :=
    isBoundedBilinearMap_apply
  have hmain : ∀ t, HasDerivAt (fun s => Ψ s (f (x s))) 0 t := by
    intro t
    have hfx : HasDerivAt (fun s => f (x s)) (f' (x t) (f (x t))) t :=
      (hf (x t)).comp_hasDerivAt t (hx t)
    have hpair : HasDerivAt (fun s => (Ψ s, f (x s)))
        ((-(ContinuousLinearMap.compL ℝ E E ℝ).flip (f' (x t)) (Ψ t)),
          f' (x t) (f (x t))) t :=
      HasDerivAt.prodMk (hΨ t) hfx
    have happly := (hB.hasFDerivAt (Ψ t, f (x t))).comp_hasDerivAt t hpair
    have hval : hB.deriv (Ψ t, f (x t))
        ((-(ContinuousLinearMap.compL ℝ E E ℝ).flip (f' (x t)) (Ψ t)),
          f' (x t) (f (x t))) = 0 := by
      rw [IsBoundedBilinearMap.deriv_apply]
      simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.comp_apply, neg_apply]
      abel
    rw [hval] at happly
    exact happly
  have hderiv : ∀ t, deriv (fun s => c - Ψ s (f (x s))) t = 0 := by
    intro t
    rw [deriv_const_sub (c := c) (f := fun s => Ψ s (f (x s)))]
    rw [(hmain t).deriv, neg_zero]
  have hdiff : Differentiable ℝ (fun s => c - Ψ s (f (x s))) := by
    have h1 : Differentiable ℝ (fun s => Ψ s (f (x s))) := fun t => (hmain t).differentiableAt
    exact (differentiable_const c).sub h1
  intro t
  exact is_const_of_deriv_eq_zero hdiff hderiv t 0

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- **Conservation plus the free-terminal-time condition.** If the time-optimal
Hamiltonian is conserved along an autonomous extremal (in the pointwise form of
`hamiltonian_conserved_of_autonomous`) and vanishes in the sense of
`FreeTerminalTimeTransversality`, then it vanishes everywhere.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Remark 6.3.20:
`H(t) ≡ const`, so `H(t₁) = 0` gives `H ≡ 0`. -/
theorem minimumTimeHamiltonian_eq_zero_of_conserved
    {H : ℝ → ℝ} {t₁ : ℝ}
    (hcons : ∀ t, H t = H 0) (hterm : H t₁ = 0) :
    ∀ t, H t = 0 := by
  intro t
  rw [hcons t, ← hcons t₁]
  exact hterm

/-! ## Bang-bang structure of time-optimal Hamiltonian minimisers -/

/-- **Bang-bang structure from the time-optimal Hamiltonian minimum.**  For the
time-optimal problem with control-affine dynamics `ẋ = A x + B u` and the unit box
`U = {u | ∀ i, |uᵢ| ≤ 1}`, an admissible control `u` that minimises the
control-dependent part `pᵀ(A x + B u)` of the Hamiltonian at a single time (with
`λ⁰ T⁻¹` and the `A x` term being control-independent) takes values at the box
vertices: `uᵢ · (Bᵀp)ᵢ ≤ 0`, with `uᵢ = −sign (Bᵀp)ᵢ` and `|uᵢ| = 1` whenever
`(Bᵀp)ᵢ ≠ 0`.

This is the reusable bridge between the Hamiltonian-minimum clause of the
maximum principle and the switching structure of `TimeOptimal`
(`timeOptimal_hamiltonianMinimizing`, `timeOptimal_bangBang`,
`linearMinimizer_bangBang`) and `FiniteSwitching`.  The singular case `(Bᵀp)ᵢ = 0` is
left unconstrained, consistent with `sign 0 = 0` (Kirk, *Optimal Control Theory: An
Introduction* (Dover 2004), §5.4, Eq. (5.4-20)). -/
theorem timeOptimalHamiltonianMinimizer_bangBang {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : EuclideanSpace ℝ ι →L[ℝ] E) (p : E) (u : EuclideanSpace ℝ ι)
    (hu : u ∈ unitBox ι)
    (hmin : ∀ w ∈ unitBox ι, inner ℝ p (B u) ≤ inner ℝ p (B w)) :
    (∀ i, u i * (B.adjoint p) i ≤ 0) ∧
      (∀ i, (B.adjoint p) i ≠ 0 → u i = -Real.sign ((B.adjoint p) i)) ∧
      (∀ i, (B.adjoint p) i ≠ 0 → |u i| = 1) := by
  refine linearMinimizer_bangBang (B.adjoint p) u hu fun w hw => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  exact hmin w hw

end OptimalControl.BoundedState
