/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.ContinuousOCP
public import DynamicalSystems.OptimalControl.ContinuousTime.DynamicProgramming
public import DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # Dynamic programming to minimum principle bridge

This file builds the classical bridge from dynamic programming to the Pontryagin
minimum principle: a smooth value function `W : ℝ → X → ℝ` satisfying the
Hamilton–Jacobi–Bellman equation yields, with costate `p = ∇ₓW` (the
value-function gradient), the Pontryagin conditions of
`DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple`.

The HJB equation at `(t, x)` reads
`∂ₜW t x + min_{v ∈ controlSet} (L(t,x,v) + ⟨∇ₓW t x, f(t,x,v)⟩) = 0`
with terminal condition `W prob.T = prob.K`. The three directions are:

1. `hjbMinimizing`: the `min` in the HJB equation is exactly pointwise
   Hamiltonian minimization (`HamiltonianMinimizing`) for the gradient costate.
2. `hjbTransversality`: differentiating the terminal equality `W prob.T = prob.K`
   gives the transversality condition (`transversalityCondition`).
3. `hjbCostateEquation_of_envelope`: differentiating the HJB equation in `x`
   along an optimal trajectory gives the backward adjoint ODE (`costateEquation`).
   The differentiation-under-`min` interchange (envelope theorem) together with
   the second-order chain rule and Clairaut symmetry of mixed partials needs a
   `C²` value function and a regular minimizing selector, which is beyond the
   first-order chain-rule tools available here (`hasDerivAt_of_hjb`); hence this
   direction is proved under an explicit named hypothesis
   (`envelopeHypothesis`, Path B), with the analytic gap documented there.

The `min` over `controlSet` is stated via `IsMinOn`: optimal controls need not
exist as a single-valued continuous selector, so there is no `argmin` value.

This formalizes the classical sufficient-direction reading of Kirk, *Optimal
Control Theory: An Introduction* (Dover, 2004), §7.1 and Berkovitz–Medhin,
*Nonlinear Optimal Control Theory* (CRC Press, 2012), §6.2; no originality is
claimed.

## Main definitions

* `valueGradientCostate`: the gradient costate as a covector,
  `p t x = fderiv ℝ (W t) x`.
* `valueGradientVec`: the gradient costate as a state-space vector,
  `gradient (W t) x` (Riesz representative used by the Hamiltonian).
* `envelopeHypothesis`: the Path-B differentiability/envelope data turning the
  differentiated HJB equation into the adjoint ODE.

## Main results

* `gradientCostate_duality`: Riesz duality between the two costate forms.
* `hjbChainRuleAlongTrajectory`: scalar chain rule along a trajectory via
  `hasDerivAt_of_hjb` (first-order data underlying the envelope computation).
* `hjbMinimizing`: HJB minimization implies `HamiltonianMinimizing`.
* `hjbTransversality`: terminal equality implies `transversalityCondition`.
* `hjbCostateEquation_of_envelope`: envelope data implies `costateEquation`.
* `hjbPMPAssembly_of_envelope`: end-to-end packaging via `pmpAssembly_minimizing`.
-/

@[expose] public section

variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]

/-- The gradient costate (value-function gradient as a covector):
`p t x = fderiv ℝ (W t) x`, the spatial part of `dW` (Kirk, *Optimal Control
Theory*, Dover 2004, §7.1; Berkovitz–Medhin, *Nonlinear Optimal Control Theory*,
CRC 2012, §6.2). The Hamiltonian and costate predicates consume state-space
vectors, so `valueGradientVec` below is its Riesz representative. -/
noncomputable def valueGradientCostate (W : ℝ → X → ℝ) (t : ℝ) (x : X) : X →L[ℝ] ℝ :=
  fderiv ℝ (W t) x

/-- The gradient costate as a state-space vector: `gradient (W t) x`, the Riesz
representative of `valueGradientCostate W t x` used by `hamiltonianOf`,
`costateEquation` and `transversalityCondition`. -/
noncomputable def valueGradientVec (W : ℝ → X → ℝ) (t : ℝ) (x : X) : X :=
  gradient (W t) x

omit [FiniteDimensional ℝ X] in
/-- Riesz duality between the covector and vector forms of the gradient costate:
pairing `valueGradientCostate W t x` with a dynamics vector equals the inner
product with `gradient (W t) x` (via `toDual_gradient`). -/
theorem gradientCostate_duality (W : ℝ → X → ℝ) (t : ℝ) (x y : X) :
    (valueGradientCostate W t x) y = inner ℝ (gradient (W t) x) y := by
  have h : valueGradientCostate W t x =
      (InnerProductSpace.toDual ℝ X) (gradient (W t) x) := by
    change fderiv ℝ (W t) x = _
    rw [toDual_gradient]
  rw [h]
  exact InnerProductSpace.toDual_apply_apply

omit [CompleteSpace X] [FiniteDimensional ℝ X] in
/-- Scalar chain rule along a controlled trajectory: if `W` has joint Fréchet
derivative `dW t y` at `(t, y)` and `x` follows the dynamics for control `u`,
then `s ↦ W s (x s)` has the expected derivative. This is `hasDerivAt_of_hjb`
instantiated along dynamics, i.e. the first-order data on which the envelope
computation builds (Kirk, Dover 2004, §7.1). -/
theorem hjbChainRuleAlongTrajectory (prob : ContinuousOCP X U) (W : ℝ → X → ℝ)
    (dW : ℝ → X → (ℝ × X) →L[ℝ] ℝ) (x : ℝ → X) (u : ℝ → U)
    (hW : ∀ t ∈ Set.Icc 0 prob.T, ∀ y,
      HasFDerivAt (fun p : ℝ × X ↦ W p.1 p.2) (dW t y) (t, y))
    (hx : ∀ t ∈ Set.Icc 0 prob.T, HasDerivAt x (prob.f t (x t) (u t)) t) :
    ∀ t ∈ Set.Icc 0 prob.T,
      HasDerivAt (fun s ↦ W s (x s)) (dW t (x t) (1, prob.f t (x t) (u t))) t := by
  intro t ht
  exact hasDerivAt_of_hjb W x t (prob.f t (x t) (u t)) (dW t (x t)) (hW t ht (x t))
    (hx t ht)

omit [FiniteDimensional ℝ X] in
/-- **HJB minimization gives Pontryagin minimization.** If at each time the
control `u t` minimizes `v ↦ L(t,x(t),v) + ⟨∇ₓW, f(t,x(t),v)⟩` over
`prob.controlSet` (the `min` in the HJB equation, stated via `IsMinOn`), then
the Hamiltonian with the gradient costate is minimized at `u t`
(`HamiltonianMinimizing`). The proof is the Riesz duality
`gradientCostate_duality` (Kirk, Dover 2004, §7.1; Berkovitz–Medhin, CRC 2012,
§6.2). -/
theorem hjbMinimizing (prob : ContinuousOCP X U) (W : ℝ → X → ℝ) (x : ℝ → X)
    (u : ℝ → U)
    (hmin : ∀ t ∈ Set.Icc 0 prob.T,
      IsMinOn (fun v ↦ prob.L t (x t) v
        + (valueGradientCostate W t (x t)) (prob.f t (x t) v))
        prob.controlSet (u t)) :
    HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u
      (fun t ↦ gradient (W t) (x t)) := by
  intro t ht w hw
  have hle : prob.L t (x t) (u t)
        + (valueGradientCostate W t (x t)) (prob.f t (x t) (u t))
      ≤ prob.L t (x t) w + (valueGradientCostate W t (x t)) (prob.f t (x t) w) :=
    (isMinOn_iff.mp (hmin t ht)) w hw
  have e1 := gradientCostate_duality W t (x t) (prob.f t (x t) (u t))
  have e2 := gradientCostate_duality W t (x t) (prob.f t (x t) w)
  change prob.L t (x t) (u t) + inner ℝ (gradient (W t) (x t)) (prob.f t (x t) (u t))
    ≤ prob.L t (x t) w + inner ℝ (gradient (W t) (x t)) (prob.f t (x t) w)
  rw [← e1, ← e2]
  exact hle

omit [FiniteDimensional ℝ X] in
/-- **HJB terminal condition gives transversality.** From `W prob.T = prob.K`
(differentiating the terminal equality) the gradient costate satisfies
`transversalityCondition`, i.e. it ends at `∇K` (Kirk, Dover 2004, §7.1;
Berkovitz–Medhin, CRC 2012, §6.2). -/
theorem hjbTransversality (prob : ContinuousOCP X U) (W : ℝ → X → ℝ) (x : ℝ → X)
    (hterm : ∀ y, W prob.T y = prob.K y) :
    transversalityCondition prob.K prob.T x (fun t ↦ gradient (W t) (x t)) := by
  have hfun : W prob.T = prob.K := funext hterm
  change gradient (W prob.T) (x prob.T) = gradient prob.K (x prob.T)
  rw [hfun]

/-- Envelope/differentiability data (Path B) turning the differentiated HJB
equation into the adjoint ODE. The field `D t` is the would-be envelope
derivative `(∂ₜ∇ₓW)(t, x t)` plus the Hessian action on the dynamics; the second
conjunct identifies it with `-∇ₓH` at the HJB-minimizing control.

Why this is assumed rather than proved: identifying `D t` with `-∇ₓH` from the
HJB equation needs (i) Danskin-type interchange of `d/dx` with `min` over
`controlSet` (regularity of the minimizing selector plus a stationarity
cancellation of the `Dₓu⋆` terms), (ii) a `C²` value function with Clairaut
symmetry of mixed partials, and (iii) cancellation of the Hessian action against
`∂ₚH = f`. The library only provides the first-order chain rule
(`hasDerivAt_of_hjb`, packaged above as `hjbChainRuleAlongTrajectory`), so the
full Path-A derivation is out of reach and its composite derivative is taken as
this explicit hypothesis (Kirk, Dover 2004, §7.1; Berkovitz–Medhin, CRC 2012,
§6.2). -/
def envelopeHypothesis (prob : ContinuousOCP X U) (W : ℝ → X → ℝ) (x : ℝ → X)
    (u : ℝ → U) (D : ℝ → X) : Prop :=
  (∀ t ∈ Set.Icc 0 prob.T, HasDerivAt (fun s ↦ gradient (W s) (x s)) (D t) t)
    ∧ (∀ t ∈ Set.Icc 0 prob.T,
      D t = -gradient (fun y ↦ hamiltonianOf prob.L prob.f t y (u t)
        (gradient (W t) (x t))) (x t))

omit [FiniteDimensional ℝ X] in
/-- **HJB equation gives the costate equation, modulo the envelope data.** Under
`envelopeHypothesis` (the differentiated-HJB identity whose proof needs the
`C²`/Danskin/Clairaut analysis described there), the gradient costate
`t ↦ ∇ₓW(t, x t)` satisfies the backward adjoint ODE `ṗ = -∂ₓH`
(`costateEquation`). The proof composes the two conjuncts of the hypothesis
(Kirk, Dover 2004, §7.1; Berkovitz–Medhin, CRC 2012, §6.2). -/
theorem hjbCostateEquation_of_envelope (prob : ContinuousOCP X U) (W : ℝ → X → ℝ)
    (x : ℝ → X) (u : ℝ → U) (D : ℝ → X)
    (henv : envelopeHypothesis prob W x u D) :
    costateEquation prob.L prob.f prob.T x u (fun t ↦ gradient (W t) (x t)) := by
  intro t ht
  rw [← henv.2 t ht]
  exact henv.1 t ht

omit [FiniteDimensional ℝ X] in
/-- **End-to-end bridge assembly.** An admissible pair whose control minimizes
the HJB Hamiltonian at the gradient costate, whose value function matches the
terminal cost, and whose envelope data holds, is packaged with its PMP triple
(costate equation, transversality, Hamiltonian minimization) via
`pmpAssembly_minimizing`. -/
theorem hjbPMPAssembly_of_envelope (prob : ContinuousOCP X U) (x₀ : X)
    (W : ℝ → X → ℝ) (x : ℝ → X) (u : ℝ → U) (D : ℝ → X)
    (hadm : IsAdmissiblePair prob x₀ x u)
    (hmin : ∀ t ∈ Set.Icc 0 prob.T,
      IsMinOn (fun v ↦ prob.L t (x t) v
        + (valueGradientCostate W t (x t)) (prob.f t (x t) v))
        prob.controlSet (u t))
    (hterm : ∀ y, W prob.T y = prob.K y)
    (henv : envelopeHypothesis prob W x u D) :
    IsAdmissiblePair prob x₀ x u ∧ ∃ q : ℝ → X,
      costateEquation prob.L prob.f prob.T x u q ∧
        transversalityCondition prob.K prob.T x q ∧
        HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u q :=
  pmpAssembly_minimizing prob x₀ x u (fun t ↦ gradient (W t) (x t)) hadm
    ⟨hjbCostateEquation_of_envelope prob W x u D henv,
      hjbTransversality prob W x hterm⟩
    (hjbMinimizing prob W x u hmin)

end
