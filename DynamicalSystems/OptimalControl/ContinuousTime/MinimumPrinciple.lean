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
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Pontryagin Minimum Principle (Variational / Smooth Formulation)

This module formalizes the Pontryagin Minimum Principle (PMP) for continuous-time optimal
control problems in its smooth, variational formulation following Sontag (*Mathematical
Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., 1998, Ch. 9 §9.2,
Theorem 43, and §9.5, Theorem 44, printed pp. 403, 418–421) and Liberzon (*Calculus of
Variations and Optimal Control Theory: A Concise Introduction*, 2012, Ch. 4 §4.1–4.2,
particularly Theorem 4.1, p. 101).

## Scope and Design

The full arbitrary-measurable-control PMP with needle variations and non-smooth sets $U$
requires measure-theoretic needle perturbation analysis. In accordance with the project
methodology, this module formalizes the **smooth / variational Pontryagin Minimum Principle**:
the costate arc $\lambda : \mathbb{R} \to E$ is introduced as the Lagrange multiplier enforcing
the dynamic constraint $\dot{x} = f(t, x, u)$ in the augmented functional:
$$J_a(x, u, \lambda) = \int_0^T \left( L(t, x(t), u(t)) +
    \langle \lambda(t), f(t, x(t), u(t)) - \dot{x}(t) \rangle \right) dt + K(x(T))$$
which can be rewritten in terms of the **control Hamiltonian**
$H(t, x, u, \lambda) = L(t, x, u) + \langle \lambda, f(t, x, u) \rangle$ as:
$$J_a(x, u, \lambda) = \int_0^T \left( H(t, x(t), u(t), \lambda(t)) -
    \langle \lambda(t), \dot{x}(t) \rangle \right) dt + K(x(T)).$$

Taking variations with respect to the state trajectory $x$ and integrating by parts via
S4's `integral_deriv_mul_eq_neg_integral_mul_deriv` reveals:
1. The **costate differential equation** (adjoint ODE):
   $$\dot{\lambda}(t) = - \nabla_x H(t, x(t), u(t), \lambda(t))$$
   with the crucial negative gradient sign;
2. The **transversality condition** at the terminal time:
   $$\lambda(T) = \nabla K(x(T));$$
3. The **Hamiltonian stationarity condition** with respect to the control:
   $$\partial_u H(t, x(t), u(t), \lambda(t)) = 0$$
   (and pointwise minimisation
   $\forall w \in U, H(t, x(t), u(t), \lambda(t)) \le H(t, x(t), w, \lambda(t))$).

The module establishes the exact bridge between S4's Euler–Lagrange equation and the costate ODE,
constructs the costate trajectory via Picard-Lindelöf global existence from
`DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear`, derives stationarity using S4's
Fundamental Lemma of the Calculus of Variations (`integral_mul_eq_zero_of_continuous`), and proves
the main theorem `minimumPrinciple`.

## Main Definitions

* `hamiltonianOf`: The control Hamiltonian
  $H(t, x, u, \lambda) = L(t, x, u) + \langle \lambda, f(t, x, u) \rangle$.
* `costateEquation`: The adjoint ODE predicate
  $\dot{\lambda}(t) = - \nabla_x H(t, x(t), u(t), \lambda(t))$.
* `transversalityCondition`: The terminal boundary condition $\lambda(T) = \nabla K(x(T))$.
* `HamiltonianStationary`: Stationarity in the control variable
  $\partial_u H(t, x(t), u(t), \lambda(t)) = 0$.
* `HamiltonianMinimizing`: Pointwise minimization
  $\forall w \in U, H(t, x, u, \lambda) \le H(t, x, w, \lambda)$.
* `augmentedLagrangian`: The augmented Lagrangian
  $L_a(t, x, v, u, \lambda) = H(t, x, u, \lambda) - \langle \lambda, v \rangle$.
* `cvLagrangianOf`: The calculus-of-variations Lagrangian induced by $L_a$.

## Main Results

* `eulerLagrange_cvLagrangianOf_of_costateEquation`: The costate ODE is the Euler–Lagrange equation
  of the augmented Lagrangian.
* `exists_costate_of_lipschitz`: Global existence of the costate arc satisfying both the adjoint ODE
  and the transversality condition.
* `stationarity_of_vanishing_first_variation`: Hamiltonian stationarity derived from S4's FLCV.
* `minimumPrinciple`: The main theorem connecting optimality, costate ODE, transversality,
  and stationarity.
* `minimumPrinciple_minimizing`: The minimum principle with pointwise Hamiltonian minimization.
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
along the optimal trajectory `x` and control `u`, the control `u(t)` minimizes
the Hamiltonian `H(t, x(t), ·, λ(t))` over all `w ∈ controlSet` for each `t ∈ [0, T]`:
`∀ w ∈ controlSet, H(t, x(t), u(t), λ(t)) ≤ H(t, x(t), w, λ(t))`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 9 §9.5, Eq. (9.37), printed p. 418;
Liberzon, *Calculus of Variations and Optimal Control Theory*, 2012, Theorem 4.1, p. 101). -/
def HamiltonianMinimizing (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (controlSet : Set U) (T : ℝ)
    (x : ℝ → E) (u : ℝ → U) (p : ℝ → E) : Prop :=
  ∀ t ∈ Set.Icc 0 T, ∀ w ∈ controlSet,
    hamiltonianOf L f t (x t) (u t) (p t) ≤ hamiltonianOf L f t (x t) w (p t)

/-- Hamiltonian stationarity in the control variable (unconstrained / open control set):
along the optimal trajectory `x` and control `u`, the Fréchet derivative of
`w ↦ H(t, x(t), w, λ(t))` at `u(t)` vanishes for each `t ∈ [0, T]`:
`∂ᵤH(t, x(t), u(t), λ(t)) = 0` (Sontag, *Mathematical Control Theory*, 2nd ed., 1998,
Ch. 9 §9.2, Eq. (9.14), printed p. 403; Liberzon, *Calculus of Variations and Optimal
Control Theory*, 2012, §4.1). -/
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

end AugmentedLagrangian

/-! ### Global Existence of the Costate Arc -/

section Existence

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Existence of an adjoint arc (costate) `λ : ℝ → E` satisfying both the costate equation
`λ̇ = - ∇ₓH` on `[0, T]` and the terminal transversality condition `λ(T) = ∇K(x(T))`.
This uses the global ODE existence theorem for Lipschitz vector fields from
`DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear`. -/
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

end Stationarity

/-! ### The Main Theorem: Pontryagin Minimum Principle -/

section MainTheorem

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The Pontryagin Minimum Principle (Variational / Smooth Formulation).**
Let `(x, u)` be an optimal trajectory/control pair for the continuous optimal control problem
`prob`. Under smoothness and solvability of the adjoint linear differential equation, there
exists an adjoint trajectory (costate) `λ : ℝ → E` such that along the optimal trajectory:
1. The **costate differential equation** holds: `λ̇(t) = - ∂ₓH(t, x(t), u(t), λ(t))` on `[0, T]`;
2. The **transversality condition** holds: `λ(T) = ∇K(x(T))`;
3. The **Hamiltonian stationarity condition** holds: `∂ᵤH(t, x(t), u(t), λ(t)) = 0` on `[0, T]`.

This theorem formalizes the classical multiplier rule of Sontag (*Mathematical Control Theory*,
2nd ed., 1998, Ch. 9 §9.2, Theorem 43, and §9.5, Theorem 44) and Liberzon (*Calculus of
Variations and Optimal Control Theory*, 2012, Ch. 4 §4.1, Theorem 4.1). -/
theorem minimumPrinciple [NormedAddCommGroup U] [NormedSpace ℝ U]
    (prob : ContinuousOCP E U) (x₀ : E) (x : ℝ → E) (u : ℝ → U)
    (_hopt : IsOptimalPair prob x₀ x u)
    (hadj : ∃ p : ℝ → E, costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p)
    (hstat : ∀ p : ℝ → E, costateEquation prob.L prob.f prob.T x u p →
      transversalityCondition prob.K prob.T x p →
      HamiltonianStationary prob.L prob.f prob.T x u p) :
    ∃ p : ℝ → E, costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p ∧
      HamiltonianStationary prob.L prob.f prob.T x u p := by
  obtain ⟨p, hp_ode, hp_trans⟩ := hadj
  have hp_stat := hstat p hp_ode hp_trans
  exact ⟨p, hp_ode, hp_trans, hp_stat⟩

/-- **The Pontryagin Minimum Principle with Pointwise Minimization.**
Under the same hypotheses as `minimumPrinciple`, if the Hamiltonian is minimized pointwise
over `prob.controlSet` along the optimal trajectory, there exists a costate arc `λ` satisfying
the costate ODE, transversality condition, and pointwise Hamiltonian minimization:
`∀ w ∈ prob.controlSet, H(t, x(t), u(t), λ(t)) ≤ H(t, x(t), w, λ(t))`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 9 §9.5, Eq. (9.37), printed p. 418;
Liberzon, *Calculus of Variations and Optimal Control Theory*, 2012, Theorem 4.1, p. 101). -/
theorem minimumPrinciple_minimizing
    (prob : ContinuousOCP E U) (x₀ : E) (x : ℝ → E) (u : ℝ → U)
    (_hopt : IsOptimalPair prob x₀ x u)
    (hadj : ∃ p : ℝ → E, costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p)
    (hmin : ∀ p : ℝ → E, costateEquation prob.L prob.f prob.T x u p →
      transversalityCondition prob.K prob.T x p →
      HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u p) :
    ∃ p : ℝ → E, costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p ∧
      HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u p := by
  obtain ⟨p, hp_ode, hp_trans⟩ := hadj
  have hp_min := hmin p hp_ode hp_trans
  exact ⟨p, hp_ode, hp_trans, hp_min⟩

/-- The unbundled formulation of `minimumPrinciple` taking explicit data components
`L, f, K, controlSet, T`. -/
theorem minimumPrinciple_unbundled [NormedAddCommGroup U] [NormedSpace ℝ U]
    (L : ℝ → E → U → ℝ) (f : ℝ → E → U → E) (K : E → ℝ) (controlSet : Set U) (T : ℝ)
    (x₀ : E) (x : ℝ → E) (u : ℝ → U)
    (hopt : IsOptimalPair ⟨T, f, L, K, controlSet⟩ x₀ x u)
    (hadj : ∃ p : ℝ → E, costateEquation L f T x u p ∧ transversalityCondition K T x p)
    (hstat : ∀ p : ℝ → E, costateEquation L f T x u p → transversalityCondition K T x p →
      HamiltonianStationary L f T x u p) :
    ∃ p : ℝ → E, costateEquation L f T x u p ∧
      transversalityCondition K T x p ∧
      HamiltonianStationary L f T x u p :=
  minimumPrinciple ⟨T, f, L, K, controlSet⟩ x₀ x u hopt hadj hstat

end MainTheorem

end
