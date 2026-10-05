/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.ContinuousOCP
public import DynamicalSystems.OptimalControl.ContinuousTime.CalculusOfVariations
public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# PMP Statement and Variational Bridge (Assembly Schema)

This module formalizes the *statement* of the Pontryagin Minimum Principle (PMP) and its
variational bridge (Euler–Lagrange ↔ costate equation) for continuous-time optimal
control problems in its smooth, variational formulation following Sontag (*Mathematical
Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., 1998, Ch. 9 §9.2,
Theorem 43, and §9.5, Theorem 44, printed pp. 403, 418–421) and Liberzon (*Calculus of
Variations and Optimal Control Theory: A Concise Introduction*, 2012, Ch. 4 §4.1–4.2,
particularly Theorem 4.1, p. 101); the derivation from optimality
(optimality ⇒ existence of a costate) is NOT proved here.

## Scope and Design

The costate arc `λ : ℝ → E` is introduced as the Lagrange multiplier enforcing
the dynamic constraint `ẋ = f(t, x, u)` in the augmented functional:
$$J_a(x, u, λ) = \int_0^T \left( L(t, x(t), u(t)) +
    \langle λ(t), f(t, x(t), u(t)) - \dot{x}(t) \rangle \right) dt + K(x(T))$$
which can be rewritten in terms of the **control Hamiltonian**
$H(t, x, u, λ) = L(t, x, u) + \langle λ, f(t, x, u) \rangle$ as:
$$J_a(x, u, λ) = \int_0^T \left( H(t, x(t), u(t), λ(t)) -
    \langle λ(t), \dot{x}(t) \rangle \right) dt + K(x(T)).$$

The variational reading of the three PMP conclusions is:
1. The **costate differential equation** (adjoint ODE):
   $$\dot{λ}(t) = - \nabla_x H(t, x(t), u(t), λ(t))$$
   with the crucial negative gradient sign;
2. The **transversality condition** at the terminal time:
   $$λ(T) = \nabla K(x(T));$$
3. Either pointwise **Hamiltonian minimization** over the control set,
   $\forall w \in U, H(t, x(t), u(t), λ(t)) \le H(t, x(t), w, λ(t))$,
   or, at interior points of the control set, **Hamiltonian stationarity**
   $\partial_u H(t, x(t), u(t), λ(t)) = 0$.

**Derivation gap:** the implication from optimality (`IsOptimalPair`) to the existence
of such a costate — the control-variation / needle-variation step — is NOT proved here.
Proving it would require an explicit admissible control-variation family
(`u* + ε • w` staying in the control set), differentiability of the state flow in the
control (the linearized ODE), and the Gateaux identification of the cost derivative with
the first variation (differentiation under the interval integral, out of scope for S4).
Accordingly the main theorem below is stated as an explicit **assembly schema**: its
hypotheses are (i) admissibility, (ii) a costate satisfying the adjoint ODE and
transversality, and (iii) stationarity (resp. minimization) for that same costate, and
the conclusion packages them. There is deliberately NO `IsOptimalPair` hypothesis
anywhere in this file. The full needle-variation PMP with arbitrary measurable controls
and non-smooth sets `U` is out of scope.

**Interior vs boundary:** `HamiltonianStationary` is the interior (open-`U`) form of the
optimality condition. Minimization implies stationarity only at interior points of the
control set (with differentiability of `H` in `u`), proved here as
`stationary_of_minimizing_interior` via Fermat's theorem; at boundary points only the
minimization form applies. Conversely, stationarity implies minimization only under a
convexity hypothesis on `w ↦ H(t, x, w, λ)` (not stated or proved here).

## Main Definitions

* `hamiltonianOf`: The control Hamiltonian
  $H(t, x, u, λ) = L(t, x, u) + \langle λ, f(t, x, u) \rangle$.
* `costateEquation`: The adjoint ODE predicate
  $\dot{λ}(t) = - \nabla_x H(t, x(t), u(t), λ(t))$.
* `transversalityCondition`: The terminal boundary condition `λ(T) = ∇K(x(T))`.
* `HamiltonianStationary`: Stationarity in the control variable
  $\partial_u H(t, x(t), u(t), λ(t)) = 0$ (interior / open-`U` form).
* `HamiltonianMinimizing`: Pointwise minimization
  $\forall w \in U, H(t, x, u, λ) \le H(t, x, w, λ)$.
* `augmentedLagrangian`: The augmented Lagrangian
  $L_a(t, x, v, u, λ) = H(t, x, u, λ) - \langle λ, v \rangle$.
* `cvLagrangianOf`: The calculus-of-variations Lagrangian induced by $L_a$.

## Main Results

* `eulerLagrange_cvLagrangianOf_of_costateEquation`: the costate ODE implies the
  Euler–Lagrange equation of the augmented Lagrangian.
* `costateEquation_of_eulerLagrange_augmented`: converse — the augmented
  Euler–Lagrange equation plus differentiability of `p` implies the costate ODE
  (via `HasDerivAt.unique` and `innerSL_inj`).
* `cvCost_eq_running_cost_of_admissible`: along an admissible pair the augmented
  Lagrangian evaluated at `ẋ` equals the running cost pointwise.
* `cvFunctional_eq_totalCost_of_admissible`: along an admissible pair (with `0 ≤ T`)
  the augmented CV functional equals `continuousTotalCost`.
* `exists_costate_of_lipschitz`: global existence of the costate arc by solving the
  adjoint ODE backward from the transversality value (transversality is the prescribed
  terminal data, not a derived consequence).
* `stationarity_of_vanishing_first_variation`: Hamiltonian stationarity from vanishing
  integral variations via S4's fundamental lemma
  (`integral_mul_eq_zero_of_continuous`).
* `stationary_of_minimizing_interior`: minimization plus an explicit interior
  hypothesis (`u t ∈ interior controlSet`) implies stationarity (Fermat).
* `ibp_costate_velocity`, `ibp_costate_velocity_deriv`: the scalar IBP step of the
  variational derivation from S4's `integral_deriv_mul_eq_neg_integral_mul_deriv`
  and `integral_deriv_mul_eq_neg_integral_mul_deriv_deriv`.
* `firstVariation_augmented_vanishes`: unpacking of `HasVanishingFirstVariation`
  at the augmented Lagrangian.
* `eulerLagrange_augmented_of_vanishing`: S4's `eulerLagrange_of_firstVariation_zero`
  instantiated at the augmented Lagrangian.
* `costateEquation_of_vanishing_augmented`: end-to-end composition recovering the
  costate ODE from a vanishing first variation under explicit regularity hypotheses.
* `pmpAssembly`: assembly schema packaging admissibility with a stationary
  costate (adjoint ODE + transversality + stationarity).
* `pmpAssembly_minimizing`: assembly schema packaging admissibility with a
  minimizing costate (adjoint ODE + transversality + minimization).
-/

@[expose] public section

open scoped Interval Topology NNReal
open MeasureTheory InnerProductSpace

variable {E U : Type*}

/-! ### The Control Hamiltonian -/

section Hamiltonian

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The control Hamiltonian `H(t, x, u, λ) = L(t, x, u) + ⟨λ, f(t, x, u)⟩`
associated to a running cost `L` and system dynamics `f` (Sontag, *Mathematical
Control Theory*, 2nd ed., 1998, Ch. 9 §9.5, Eq. (9.36), printed p. 418;
Liberzon, *Calculus of Variations and Optimal Control Theory*, 2012, §4.1, p. 100). -/
def hamiltonianOf (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) : ℝ → E → U → E → ℝ :=
  fun t x u p ↦ L t x u + inner ℝ p (f t x u)

@[simp]
theorem hamiltonianOf_apply (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E)
    (t : ℝ) (x : E) (u : U) (p : E) :
    hamiltonianOf L f t x u p = L t x u + inner ℝ p (f t x u) :=
  rfl

end Hamiltonian

/-! ### Costate Equation and Transversality Condition -/

section Adjoint

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Spatial differentiation of the control Hamiltonian produces the usual
linear adjoint expression. This bridges the pairing lemmas to the project's
gradient-based `costateEquation`. -/
theorem hasGradientAt_hamiltonian
    {L : E → ℝ} {f : E → E} {x p ell : E} {A : E →L[ℝ] E}
    (hL : HasGradientAt L ell x) (hf : HasFDerivAt f A x) :
    HasGradientAt (fun y => L y + inner ℝ p (f y)) (ell + A.adjoint p) x := by
  have hlin : HasFDerivAt (fun y => inner ℝ p (f y))
      ((InnerProductSpace.toDual ℝ E p).comp A) x :=
    (InnerProductSpace.toDual ℝ E p).hasFDerivAt.comp x hf
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hL.hasFDerivAt.add hlin using 1
  ext v
  change inner ℝ (ell + A.adjoint p) v = inner ℝ ell v + inner ℝ p (A v)
  rw [inner_add_left, ContinuousLinearMap.adjoint_inner_left]

/-- The costate (adjoint) differential equation along a state trajectory `x` and control `u`:
the costate arc `λ : ℝ → E` satisfies `λ̇(t) = - ∂ₓH(t, x(t), u(t), λ(t))` for all `t ∈ [0, T]`.
Here the state derivative is expressed via the Hilbert-space gradient
`gradient (fun y ↦ hamiltonianOf L f t y (u t) (λ t)) (x t)` (Sontag, *Mathematical Control
Theory*, 2nd ed., 1998, Ch. 9 §9.5, Eq. (9.36), printed p. 418; Liberzon, *Calculus of
Variations and Optimal Control Theory*, 2012, Eq. (4.13), p. 101).

The transversality condition `λ T = ∇K (x T)` is maintained as a separate clause
`transversalityCondition K T x λ` for modularity across free-endpoint and fixed-endpoint
formulations. -/
def costateEquation (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (T : ℝ) (x : ℝ → E) (u : ℝ → U)
    (p : ℝ → E) : Prop :=
  ∀ t ∈ Set.Icc 0 T,
    HasDerivAt p (- gradient (fun y : E ↦ hamiltonianOf L f t y (u t) (p t)) (x t)) t

/-- The transversality condition for the costate at horizon `T`:
`λ T = ∇K (x T)` for a terminal penalty function `K : E → ℝ` (Sontag, *Mathematical Control
Theory*, 2nd ed., 1998, Ch. 9 §9.5, Eq. (9.36), printed p. 418; Liberzon, *Calculus of
Variations and Optimal Control Theory*, 2012, Eq. (4.15), p. 101). -/
def transversalityCondition (K : E → ℝ) (T : ℝ) (x : ℝ → E) (p : ℝ → E) : Prop :=
  p T = gradient K (x T)

/-- Pointwise Hamiltonian minimisation over the control set `controlSet`:
along the trajectory `x` and control `u`, the control `u(t)` minimizes
the Hamiltonian `H(t, x(t), ·, λ(t))` over all `w ∈ controlSet` for each `t ∈ [0, T]`:
`∀ w ∈ controlSet, H(t, x(t), u(t), λ(t)) ≤ H(t, x(t), w, λ(t))`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 9 §9.5, Eq. (9.37), printed p. 418;
Liberzon, *Calculus of Variations and Optimal Control Theory*, 2012, Theorem 4.1, p. 101).
This is the boundary-capable form of the optimality condition: unlike
`HamiltonianStationary` it requires no interior or differentiability hypotheses. -/
def HamiltonianMinimizing (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (controlSet : Set U) (T : ℝ)
    (x : ℝ → E) (u : ℝ → U) (p : ℝ → E) : Prop :=
  ∀ t ∈ Set.Icc 0 T, ∀ w ∈ controlSet,
    hamiltonianOf L f t (x t) (u t) (p t) ≤ hamiltonianOf L f t (x t) w (p t)

/-- Hamiltonian stationarity in the control variable (interior / open-control-set form):
along the trajectory `x` and control `u`, the Fréchet derivative of
`w ↦ H(t, x(t), w, λ(t))` at `u(t)` vanishes for each `t ∈ [0, T]`:
`∂ᵤH(t, x(t), u(t), λ(t)) = 0` (Sontag, *Mathematical Control Theory*, 2nd ed., 1998,
Ch. 9 §9.2, Eq. (9.14), printed p. 403; Liberzon, *Calculus of Variations and Optimal
Control Theory*, 2012, §4.1).

This is valid only at interior points of the control set: minimization implies
stationarity only when `u t ∈ interior controlSet` (see
`stationary_of_minimizing_interior`), and at boundary points only the minimization
form `HamiltonianMinimizing` applies. Conversely, stationarity implies minimization
only under a convexity hypothesis on `w ↦ H(t, x, w, λ)` (not stated or proved here). -/
def HamiltonianStationary [NormedAddCommGroup U] [NormedSpace ℝ U]
    (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (T : ℝ)
    (x : ℝ → E) (u : ℝ → U) (p : ℝ → E) : Prop :=
  ∀ t ∈ Set.Icc 0 T,
    fderiv ℝ (fun w : U ↦ hamiltonianOf L f t (x t) w (p t)) (u t) = 0

end Adjoint

/-! ### Augmented Lagrangian and Calculus of Variations Connection -/

section AugmentedLagrangian

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The augmented Lagrangian for the optimal control problem with multiplier (costate) `p`:
`L_aug(t, x, v, u, p) = L(t, x, u) + ⟨p, f(t, x, u) - v⟩ = H(t, x, u, p) - ⟨p, v⟩`.
Along an admissible pair where `v = ẋ = f(t, x, u)`, the dynamic constraint vanishes identically,
recovering the running cost `L(t, x, u)`. -/
def augmentedLagrangian (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (t : ℝ) (x : E) (v : E)
    (u : U) (p : E) : ℝ :=
  hamiltonianOf L f t x u p - inner ℝ p v

/-- The calculus-of-variations Lagrangian induced by the augmented Lagrangian along a control
trajectory `u : ℝ → U` and a costate trajectory `p : ℝ → E`:
`L_cv(t, x, v) = H(t, x, u(t), p(t)) - ⟨p(t), v⟩`. -/
def cvLagrangianOf (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (u : ℝ → U) (p : ℝ → E) :
    ℝ → E → E → ℝ :=
  fun t x v ↦ augmentedLagrangian L f t x v (u t) (p t)

omit [CompleteSpace E] in
/-- Along any trajectory satisfying the dynamics `ẋ = f(t, x, u)`, the augmented Lagrangian
recovers the running cost identically. -/
theorem augmentedLagrangian_eq_running_cost (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E)
    (t : ℝ) (x : E) (u : U) (p : E) :
    augmentedLagrangian L f t x (f t x u) u p = L t x u := by
  unfold augmentedLagrangian hamiltonianOf
  simp only [add_sub_cancel_right]

/-- The Fréchet derivative of the augmented Lagrangian with respect to the velocity variable `v`
equals `- toDual ℝ E (p s)` (the negative costate as a continuous dual element). -/
theorem fderiv_velocity_cvLagrangianOf (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E)
    (u : ℝ → U) (p : ℝ → E) (s : ℝ) (x : ℝ → E) :
    fderiv ℝ (fun v : E ↦ cvLagrangianOf L f u p s (x s) v) (deriv x s) =
      - toDual ℝ E (p s) := by
  have hcongr : (fun v : E ↦ cvLagrangianOf L f u p s (x s) v) =
      (fun _ ↦ hamiltonianOf L f s (x s) (u s) (p s)) - (fun v ↦ inner ℝ (p s) v) := by
    ext v
    rfl
  rw [hcongr]
  have hconst : HasFDerivAt (fun _ : E ↦ hamiltonianOf L f s (x s) (u s) (p s))
      (0 : E →L[ℝ] ℝ) (deriv x s) :=
    hasFDerivAt_const (𝕜 := ℝ) (hamiltonianOf L f s (x s) (u s) (p s)) (deriv x s)
  have hlin : HasFDerivAt (fun v : E ↦ inner ℝ (p s) v) (toDual ℝ E (p s)) (deriv x s) := by
    have heq : (fun v : E ↦ inner ℝ (p s) v) = ⇑(toDual ℝ E (p s)) := rfl
    rw [heq]
    exact (toDual ℝ E (p s)).hasFDerivAt
  have hsub := hconst.sub hlin
  simp only [zero_sub] at hsub
  exact hsub.fderiv

omit [CompleteSpace E] in
/-- The Fréchet derivative of the augmented Lagrangian with respect to the state variable `x`
equals the Fréchet derivative of the Hamiltonian. -/
theorem fderiv_state_cvLagrangianOf (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E)
    (u : ℝ → U) (p : ℝ → E) (t : ℝ) (x : ℝ → E) :
    fderiv ℝ (fun y : E ↦ cvLagrangianOf L f u p t y (deriv x t)) (x t) =
      fderiv ℝ (fun y : E ↦ hamiltonianOf L f t y (u t) (p t)) (x t) := by
  have hcongr : (fun y : E ↦ cvLagrangianOf L f u p t y (deriv x t)) =
      fun y ↦ (hamiltonianOf L f t y (u t) (p t)) - (inner ℝ (p t) (deriv x t)) := by
    ext y
    rfl
  rw [hcongr]
  exact fderiv_sub_const (inner ℝ (p t) (deriv x t))

/-- **The Costate Equation as Euler–Lagrange.**
If the costate arc `p : ℝ → E` satisfies the costate differential equation
`ṗ = - ∇ₓH`, then the state trajectory `x` satisfies the Euler–Lagrange differential
equation for the augmented Lagrangian `cvLagrangianOf L f u p`. -/
theorem eulerLagrange_cvLagrangianOf_of_costateEquation
    (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (T : ℝ) (x : ℝ → E) (u : ℝ → U)
    (p : ℝ → E) (hode : costateEquation L f T x u p) :
    eulerLagrange (cvLagrangianOf L f u p) T x := by
  intro t ht
  have h_deriv_p := hode t ht
  have h_vel : (fun s : ℝ ↦ fderiv ℝ (fun v : E ↦ cvLagrangianOf L f u p s (x s) v) (deriv x s)) =
      fun s ↦ - toDual ℝ E (p s) :=
    funext fun s ↦ fderiv_velocity_cvLagrangianOf L f u p s x
  rw [h_vel]
  rw [fderiv_state_cvLagrangianOf]
  rw [← toDual_gradient]
  have h_diff : HasDerivAt (fun s ↦ - toDual ℝ E (p s))
      (- toDual ℝ E (- gradient (fun y : E ↦ hamiltonianOf L f t y (u t) (p t)) (x t))) t := by
    have h_inner : (fun s ↦ - toDual ℝ E (p s)) = (fun s ↦ - innerSL ℝ (p s)) := by
      ext s v
      rfl
    rw [h_inner]
    have h_comp := (- innerSL ℝ (E := E)).hasFDerivAt.comp_hasDerivAt t h_deriv_p
    have h_eval : (- innerSL ℝ (E := E))
          (- gradient (fun y : E ↦ hamiltonianOf L f t y (u t) (p t)) (x t)) =
        - toDual ℝ E (- gradient (fun y : E ↦ hamiltonianOf L f t y (u t) (p t)) (x t)) := by
      ext v
      rfl
    rw [← h_eval]
    exact h_comp
  have h_neg_neg : - toDual ℝ E (- gradient (fun y : E ↦ hamiltonianOf L f t y (u t) (p t)) (x t)) =
      toDual ℝ E (gradient (fun y : E ↦ hamiltonianOf L f t y (u t) (p t)) (x t)) := by
    simp only [map_neg, neg_neg]
  rw [h_neg_neg] at h_diff
  exact h_diff

/-- **Euler–Lagrange as the Costate Equation (converse bridge).**
If the state trajectory `x` satisfies the Euler–Lagrange equation for the augmented
Lagrangian `cvLagrangianOf L f u p` and the costate arc `p` is differentiable with
derivative `p'`, then `p` satisfies the costate equation `ṗ = - ∇ₓH`. The proof pushes
the differentiability of `p` through the Riesz isometry and concludes by uniqueness of
derivatives (`HasDerivAt.unique`) with injectivity of the duality pairing
(`innerSL_inj`). Together with `eulerLagrange_cvLagrangianOf_of_costateEquation` this
shows the costate ODE and the augmented Euler–Lagrange equation coincide. -/
theorem costateEquation_of_eulerLagrange_augmented
    (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (T : ℝ) (x : ℝ → E) (u : ℝ → U)
    (p : ℝ → E) (p' : ℝ → E)
    (hp : ∀ t ∈ Set.Icc 0 T, HasDerivAt p (p' t) t)
    (hel : eulerLagrange (cvLagrangianOf L f u p) T x) :
    costateEquation L f T x u p := by
  intro t ht
  have hEL := hel t ht
  have hvel : (fun s : ℝ ↦ fderiv ℝ (fun v : E ↦ cvLagrangianOf L f u p s (x s) v)
      (deriv x s)) = fun s ↦ - toDual ℝ E (p s) :=
    funext fun s ↦ fderiv_velocity_cvLagrangianOf L f u p s x
  rw [hvel, fderiv_state_cvLagrangianOf, ← toDual_gradient] at hEL
  have hcomp : HasDerivAt (fun s ↦ - toDual ℝ E (p s)) (- toDual ℝ E (p' t)) t := by
    have hbase := ((- innerSL ℝ (E := E)).hasFDerivAt).comp_hasDerivAt t (hp t ht)
    exact hbase
  have huniq := hEL.unique hcomp
  have huniq' : innerSL ℝ
      (gradient (fun y : E ↦ hamiltonianOf L f t y (u t) (p t)) (x t)) =
      -innerSL ℝ (p' t) := huniq
  rw [← map_neg] at huniq'
  have hinj := innerSL_inj.mp huniq'
  rw [hinj, neg_neg]
  exact hp t ht

end AugmentedLagrangian

/-! ### Augmented Cost Coincides with the OCP Cost along Admissible Pairs -/

section CostIdentification

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Along an admissible pair, the augmented Lagrangian evaluated at the true velocity
`ẋ` equals the running cost pointwise: the constraint term vanishes by the dynamics. -/
theorem cvCost_eq_running_cost_of_admissible (prob : ContinuousOCP E U)
    (x₀ : E) (x : ℝ → E) (u : ℝ → U) (p : ℝ → E) (t : ℝ)
    (Hadm : IsAdmissiblePair prob x₀ x u) (ht : t ∈ Set.Icc 0 prob.T) :
    cvLagrangianOf prob.L prob.f u p t (x t) (deriv x t) = prob.L t (x t) (u t) := by
  have hdyn := Hadm.2.2.1 t ht
  rw [hdyn.deriv]
  exact augmentedLagrangian_eq_running_cost _ _ _ _ _ _

omit [CompleteSpace E] in
/-- Along an admissible pair (with `0 ≤ T`), the augmented calculus-of-variations
functional coincides with the optimal control total cost. -/
theorem cvFunctional_eq_totalCost_of_admissible (prob : ContinuousOCP E U)
    (x₀ : E) (x : ℝ → E) (u : ℝ → U) (p : ℝ → E)
    (Hadm : IsAdmissiblePair prob x₀ x u) (hT : 0 ≤ prob.T) :
    cvFunctional (cvLagrangianOf prob.L prob.f u p) prob.K prob.T x =
      continuousTotalCost prob x u := by
  unfold cvFunctional continuousTotalCost
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hT] at ht
  exact cvCost_eq_running_cost_of_admissible prob x₀ x u p t Hadm ht

end CostIdentification

/-! ### Global Existence of the Costate Arc -/

section Existence

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Existence of an adjoint arc (costate) `λ : ℝ → E` satisfying both the costate equation
`λ̇ = - ∇ₓH` on `[0, T]` and the terminal transversality condition `λ(T) = ∇K(x(T))`.
This solves the adjoint linear ODE backward from the prescribed terminal value
`∇K(x(T))` using the global ODE existence theorem for Lipschitz vector fields from
`DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear`; transversality enters
as the prescribed terminal data, not as a derived consequence. -/
theorem exists_costate_of_lipschitz (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E)
    (K : E → ℝ) (T : ℝ) (x : ℝ → E) (u : ℝ → U)
    {K_lip : ℝ≥0} {C' : ℝ}
    (h_lip : ∀ t, LipschitzWith K_lip
      (fun p : E ↦ - gradient (fun y : E ↦ hamiltonianOf L f t y (u t) p) (x t)))
    (ht_bdd : ∀ t,
      ‖- gradient (fun y : E ↦ hamiltonianOf L f t y (u t) 0) (x t)‖ ≤ C')
    (h_cont : Continuous (fun p : ℝ × E ↦
      - gradient (fun y : E ↦ hamiltonianOf L f p.1 y (u p.1) p.2) (x p.1))) :
    ∃ p : ℝ → E, costateEquation L f T x u p ∧ transversalityCondition K T x p := by
  let V : ℝ → E → E := fun t p ↦
    - gradient (fun y : E ↦ hamiltonianOf L f t y (u t) p) (x t)
  have h_cont' : Continuous V.uncurry := h_cont
  obtain ⟨Φ, hΦ⟩ := global_existence (f := V) h_lip ht_bdd h_cont'
  let p₀ : E := gradient K (x T)
  let p : ℝ → E := Φ T p₀
  have hint : IsIntegralCurve p V := (hΦ T p₀).1
  have hinit : p T = p₀ := (hΦ T p₀).2
  refine ⟨p, ?_, ?_⟩
  · intro t _
    exact hint t
  · exact hinit

end Existence

/-! ### Variational Derivation of Control Stationarity -/

section Stationarity

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- **Control Stationarity from Vanishing Variation.**
If the directional derivative of the Hamiltonian along control variations vanishes
when integrated against every smooth endpoint-vanishing test function `φ`, then the
pointwise stationarity condition `∂ᵤH(t, x(t), u(t), λ(t)) = 0` holds for all `t ∈ [0, T]`.
This is established via the Fundamental Lemma of the Calculus of Variations
(`integral_mul_eq_zero_of_continuous`) from S4. -/
theorem stationarity_of_vanishing_first_variation
    (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (T : ℝ) (x : ℝ → E) (u : ℝ → U) (p : ℝ → E)
    (hT : 0 < T)
    (hcont : ∀ w : U, Continuous (fun t ↦
      (fderiv ℝ (fun v : U ↦ hamiltonianOf L f t (x t) v (p t)) (u t)) w))
    (hvar : ∀ (w : U) (φ : ℝ → ℝ), ContDiff ℝ 1 φ → tsupport φ ⊆ Set.Ioo 0 T →
      ∫ t in 0..T, (fderiv ℝ (fun v : U ↦ hamiltonianOf L f t (x t) v (p t)) (u t)) w * φ t = 0) :
    HamiltonianStationary L f T x u p := by
  intro t ht
  ext w
  have h := integral_mul_eq_zero_of_continuous hT (hcont w)
    (fun φ hφ hsupp ↦ hvar w φ hφ hsupp) t ht
  exact h

/-- **Minimization Implies Stationarity at Interior Points.**
If the Hamiltonian is minimized over `controlSet` along the trajectory, each
`u t` lies in the interior of `controlSet` (the explicit open-`U` hypothesis), and
`w ↦ H(t, x(t), w, λ(t))` is differentiable at `u t` (the explicit `hHdiff`
hypothesis), then the pointwise stationarity condition holds. The proof is Fermat's
theorem (`IsLocalMin.hasFDerivAt_eq_zero`): a set-minimum at an interior point is a
local minimum. At boundary points this implication fails and only
`HamiltonianMinimizing` applies.

Note on the differentiability hypothesis: Mathlib's `fderiv` is defined to be the junk
value `0` at points where the function is not differentiable, so concluding
`fderiv … = 0` via `IsLocalMin.fderiv_eq_zero` alone would be vacuous exactly where
it matters. The explicit `hHdiff` hypothesis rules this out, and the conclusion is
derived via `hloc.hasFDerivAt_eq_zero hHdiff.hasFDerivAt`. -/
theorem stationary_of_minimizing_interior
    (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (controlSet : Set U) (T : ℝ)
    (x : ℝ → E) (u : ℝ → U) (p : ℝ → E)
    (hmin : HamiltonianMinimizing L f controlSet T x u p)
    (hinterior : ∀ t ∈ Set.Icc 0 T, u t ∈ interior controlSet)
    (hHdiff : ∀ t ∈ Set.Icc 0 T,
      DifferentiableAt ℝ (fun w : U ↦ hamiltonianOf L f t (x t) w (p t)) (u t)) :
    HamiltonianStationary L f T x u p := by
  intro t ht
  have hminOn : IsMinOn (fun w : U ↦ hamiltonianOf L f t (x t) w (p t)) controlSet (u t) :=
    fun w hw ↦ hmin t ht w hw
  have hmem : controlSet ∈ 𝓝 (u t) := mem_interior_iff_mem_nhds.mp (hinterior t ht)
  have hloc : IsLocalMin (fun w : U ↦ hamiltonianOf L f t (x t) w (p t)) (u t) :=
    hminOn.isLocalMin hmem
  exact hloc.hasFDerivAt_eq_zero (hHdiff t ht).hasFDerivAt

/-! #### Integration by parts at the scalarized costate pairing -/

/-- Scalar integration-by-parts step of the variational derivation (explicit-derivative
form): for an endpoint-vanishing weight `φ` and the scalarized costate pairing
`s ↦ ⟪p s, e⟫`, the velocity-pairing integral flips sign. This is S4's
`integral_deriv_mul_eq_neg_integral_mul_deriv` instantiated at the augmented-Lagrangian
velocity term; it is the move that trades `η̇` for `λ̇` in the first variation. -/
theorem ibp_costate_velocity {φ φ' : ℝ → ℝ} {T : ℝ} {p : ℝ → E} {e : E} {v' : ℝ → ℝ}
    (hφ : ∀ x ∈ Set.uIcc 0 T, HasDerivAt φ (φ' x) x)
    (hv : ∀ x ∈ Set.uIcc 0 T, HasDerivAt (fun s ↦ inner ℝ (p s) e) (v' x) x)
    (hφi : IntervalIntegrable φ' volume 0 T)
    (hvi : IntervalIntegrable v' volume 0 T)
    (hφ0 : φ 0 = 0) (hφT : φ T = 0) :
    ∫ x in 0..T, φ' x * inner ℝ (p x) e = -∫ x in 0..T, φ x * v' x :=
  integral_deriv_mul_eq_neg_integral_mul_deriv hφ hv hφi hvi hφ0 hφT

/-- Scalar integration-by-parts step of the variational derivation (`deriv` form):
same as `ibp_costate_velocity` with derivatives written via `deriv`. This is S4's
`integral_deriv_mul_eq_neg_integral_mul_deriv_deriv`. -/
theorem ibp_costate_velocity_deriv {φ : ℝ → ℝ} {T : ℝ} {p : ℝ → E} {e : E}
    (hφ : ∀ x ∈ Set.uIcc 0 T, HasDerivAt φ (deriv φ x) x)
    (hv : ∀ x ∈ Set.uIcc 0 T,
      HasDerivAt (fun s ↦ inner ℝ (p s) e) (deriv (fun s ↦ inner ℝ (p s) e) x) x)
    (hφi : IntervalIntegrable (deriv φ) volume 0 T)
    (hvi : IntervalIntegrable (deriv (fun s ↦ inner ℝ (p s) e)) volume 0 T)
    (hφ0 : φ 0 = 0) (hφT : φ T = 0) :
    ∫ x in 0..T, deriv φ x * inner ℝ (p x) e
      = -∫ x in 0..T, φ x * deriv (fun s ↦ inner ℝ (p s) e) x :=
  integral_deriv_mul_eq_neg_integral_mul_deriv_deriv hφ hv hφi hvi hφ0 hφT

/-! #### From vanishing first variation to the augmented Euler–Lagrange equation -/

omit [NormedAddCommGroup U] [NormedSpace ℝ U] in
/-- Unpacking of `HasVanishingFirstVariation` at the augmented Lagrangian: vanishing on
endpoint-vanishing perturbations gives `firstVariation … = 0` for each such `η`. -/
theorem firstVariation_augmented_vanishes
    (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (u : ℝ → U) (p : ℝ → E)
    (K : E → ℝ) (T : ℝ) (x : ℝ → E)
    (hvan : HasVanishingFirstVariation (cvLagrangianOf L f u p) K T x)
    (η : ℝ → E) (hη : ∀ t, HasDerivAt η (deriv η t) t) (h0 : η 0 = 0) (hT : η T = 0) :
    firstVariation (cvLagrangianOf L f u p) K T x η = 0 :=
  hvan η hη h0 hT

omit [NormedAddCommGroup U] [NormedSpace ℝ U] in
/-- **Augmented Euler–Lagrange from vanishing first variation.**
If the first variation of the augmented calculus-of-variations functional vanishes on
endpoint-vanishing perturbations, and the velocity-derivative curve is differentiable
with continuous data, then the trajectory satisfies the augmented Euler–Lagrange
equation. This is S4's `eulerLagrange_of_firstVariation_zero` instantiated at
`cvLagrangianOf L f u p`; each link is proved separately, and the end-to-end composition
recovering the costate ODE from the variational principle is provided as
`costateEquation_of_vanishing_augmented` below. -/
theorem eulerLagrange_augmented_of_vanishing
    (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (u : ℝ → U) (p : ℝ → E)
    (K : E → ℝ) (Q : ℝ → E →L[ℝ] ℝ) (T : ℝ) (x : ℝ → E)
    (hT : 0 < T)
    (hvan : HasVanishingFirstVariation (cvLagrangianOf L f u p) K T x)
    (hPderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt
      (fun s ↦ fderiv ℝ (fun v : E ↦ cvLagrangianOf L f u p s (x s) v) (deriv x s)) (Q t) t)
    (hPcont : Continuous
      (fun s ↦ fderiv ℝ (fun v : E ↦ cvLagrangianOf L f u p s (x s) v) (deriv x s)))
    (hQcont : Continuous Q)
    (hScont : Continuous
      (fun t ↦ fderiv ℝ (fun y : E ↦ cvLagrangianOf L f u p t y (deriv x t)) (x t))) :
    eulerLagrange (cvLagrangianOf L f u p) T x :=
  eulerLagrange_of_firstVariation_zero _ _ _ _ _ hT hvan hPderiv hPcont hQcont hScont

omit [NormedAddCommGroup U] [NormedSpace ℝ U] in
/-- **Costate equation from vanishing first variation (end-to-end composition).**
If the first variation of the augmented calculus-of-variations functional vanishes on
endpoint-vanishing perturbations (with the explicit regularity hypotheses of
`eulerLagrange_augmented_of_vanishing`), and the costate arc `p` is differentiable with
derivative `p'`, then `p` satisfies the costate equation `ṗ = - ∇ₓH`. This chains
`eulerLagrange_augmented_of_vanishing` with `costateEquation_of_eulerLagrange_augmented`.
The scalar IBP steps `ibp_costate_velocity` / `ibp_costate_velocity_deriv` and the
unpacking `firstVariation_augmented_vanishes` remain available as standalone ingredients
for callers. -/
theorem costateEquation_of_vanishing_augmented [CompleteSpace E]
    (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (u : ℝ → U) (p : ℝ → E)
    (p' : ℝ → E) (K : E → ℝ) (Q : ℝ → E →L[ℝ] ℝ) (T : ℝ) (x : ℝ → E)
    (hT : 0 < T)
    (hvan : HasVanishingFirstVariation (cvLagrangianOf L f u p) K T x)
    (hp : ∀ t ∈ Set.Icc 0 T, HasDerivAt p (p' t) t)
    (hPderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt
      (fun s ↦ fderiv ℝ (fun v : E ↦ cvLagrangianOf L f u p s (x s) v) (deriv x s)) (Q t) t)
    (hPcont : Continuous
      (fun s ↦ fderiv ℝ (fun v : E ↦ cvLagrangianOf L f u p s (x s) v) (deriv x s)))
    (hQcont : Continuous Q)
    (hScont : Continuous
      (fun t ↦ fderiv ℝ (fun y : E ↦ cvLagrangianOf L f u p t y (deriv x t)) (x t))) :
    costateEquation L f T x u p :=
  costateEquation_of_eulerLagrange_augmented L f T x u p p' hp
    (eulerLagrange_augmented_of_vanishing L f u p K Q T x hT hvan hPderiv hPcont
      hQcont hScont)

end Stationarity

/-! ### The Main Theorem: PMP Assembly Schema -/

section MainTheorem

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The PMP assembly schema (stationary form).**
Let `(x, u)` be an admissible trajectory/control pair for the continuous optimal control
problem `prob`. Given a costate arc `p : ℝ → E` satisfying along the trajectory:
1. The **costate differential equation**: `λ̇(t) = - ∂ₓH(t, x(t), u(t), λ(t))` on `[0, T]`;
2. The **transversality condition**: `λ(T) = ∇K(x(T))`;
3. The **Hamiltonian stationarity condition** (interior form):
   `∂ᵤH(t, x(t), u(t), λ(t)) = 0` on `[0, T]`,
the pair is certified with its PMP triple. Every hypothesis is used: admissibility is
returned, and the costate data is repackaged existentially.

This is the standard "how to check PMP" statement of Sontag (*Mathematical Control
Theory*, 2nd ed., 1998, Ch. 9 §9.2, Theorem 43, and §9.5, Theorem 44) and Liberzon
(*Calculus of Variations and Optimal Control Theory*, 2012, Ch. 4 §4.1, Theorem 4.1).
It takes no optimality hypothesis: the variational/needle step from optimality to the
existence of such a costate is not proved here (see the module-level derivation-gap
note). Note that `exists_costate_of_lipschitz` above already gives costate existence
(without optimality) under regularity hypotheses, so the schema's `hadj` hypothesis is a
genuine under-claim relative to the file's own machinery. -/
theorem pmpAssembly [NormedAddCommGroup U] [NormedSpace ℝ U]
    (prob : ContinuousOCP E U) (x₀ : E) (x : ℝ → E) (u : ℝ → U) (p : ℝ → E)
    (Hadm : IsAdmissiblePair prob x₀ x u)
    (hadj : costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p)
    (hstat : HamiltonianStationary prob.L prob.f prob.T x u p) :
    IsAdmissiblePair prob x₀ x u ∧ ∃ q : ℝ → E,
      costateEquation prob.L prob.f prob.T x u q ∧
      transversalityCondition prob.K prob.T x q ∧
      HamiltonianStationary prob.L prob.f prob.T x u q :=
  ⟨Hadm, p, hadj.1, hadj.2, hstat⟩

/-- **The PMP assembly schema with pointwise minimization.**
Same assembly schema as `pmpAssembly`, but the costate hypothesis is pointwise
Hamiltonian minimization over `prob.controlSet`:
`∀ w ∈ prob.controlSet, H(t, x(t), u(t), λ(t)) ≤ H(t, x(t), w, λ(t))`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 9 §9.5, Eq. (9.37), printed p. 418;
Liberzon, *Calculus of Variations and Optimal Control Theory*, 2012, Theorem 4.1, p. 101).
This is the boundary-capable form: at interior points
`stationary_of_minimizing_interior` recovers stationarity from it. -/
theorem pmpAssembly_minimizing
    (prob : ContinuousOCP E U) (x₀ : E) (x : ℝ → E) (u : ℝ → U) (p : ℝ → E)
    (Hadm : IsAdmissiblePair prob x₀ x u)
    (hadj : costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p)
    (hmin : HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u p) :
    IsAdmissiblePair prob x₀ x u ∧ ∃ q : ℝ → E,
      costateEquation prob.L prob.f prob.T x u q ∧
      transversalityCondition prob.K prob.T x q ∧
      HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u q :=
  ⟨Hadm, p, hadj.1, hadj.2, hmin⟩

end MainTheorem

end
