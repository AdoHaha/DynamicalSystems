/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.DiscreteTime.UltimateBoundedness
public import Mathlib.Analysis.Normed.Group.Basic

/-! # Nominal (inherent) robustness of model predictive control

This file formalises the nominal-robustness core of Rawlings, Mayne and Diehl,
*Model Predictive Control: Theory, Computation, and Design*, 2nd ed., 2019,
Chapter 3, §3.2 (printed pp. 204–207, PDF pp. 253–256).  The chapter asks when the
nominal (disturbance-free) receding-horizon controller is *inherently robust*: the
value function used as a Lyapunov function for the nominal closed loop has a
one-sided Lipschitz constant `L`, and the true plant is the additive-disturbance
system `x⁺ = f x (κ x) + w` with `‖w‖ ≤ d`.  Chaining the nominal descent
`V (f x (κ x)) ≤ V x − ℓ x (κ x)` with that Lipschitz estimate gives the ISS-style
decrease

`V (f x (κ x) + w) ≤ V x − ℓ x (κ x) + L * d`,

which is the discrete-time counterpart of the robust Lyapunov decrease behind
Theorem 3.2 (printed p. 208 / PDF p. 256): the value function of the online optimal
control problem is a continuous Lyapunov function and therefore the origin is
robustly stable for the disturbed system.

Adding coercivity of the stage cost, `γ * V ≤ ℓ` for some `0 < γ`, turns the
decrease into the affine contraction `V (x_{n+1}) ≤ (1 − γ) * V (x_n) + L * d`,
whose ultimate bound `(L * d) / γ + ε` is the robust attraction part of
Definition 3.1 (printed p. 207 / PDF p. 255): every realization of the disturbed
trajectory is eventually contained in the tube of radius `(L * d) / γ + ε` around
the origin.

## Scope

This slice is deliberately *nominal* (inherent) robustness, as in §3.2.  The
tube-based design of §3.5–3.6 and the min-max dynamic-programming formulation of
§3.3–3.4 (feedback MPC, the optimal policy `μ⁰`) are separate future slices and are
not formalised here.

## Reuse

The ultimate-bound step is *not* re-derived: it is exactly the existing
`eventually_le_add_of_succ_le_mul_add` of
`DynamicalSystems.DiscreteTime.UltimateBoundedness` (the discrete ISS
ultimate-boundedness machinery), instantiated with `a = 1 − γ` and `d = L * d`.
The nominal descent hypothesis `hdesc` is left generic so that this module stays
reusable; it is discharged by `mpc_valueFunction_decrease` of
`DynamicalSystems.Control.MPC.Stability` for a concrete finite-horizon MPC problem.
Class-K comparison functions (`MemK`/`MemKL`) of
`DynamicalSystems.Basic.ComparisonFunctions` would supply the `γ * V ≤ ℓ`
hypothesis for a concrete quadratic cost and are not needed at this level of
generality.

## Correction

The task header lists both `[NormedAddCommGroup X]` and `[NormedAddCommGroup U]`.
The input space `U` only indexes the control and no norm on `U` is used by any
declaration here, so the statements carry the metric structure on `X` alone (the
declarations are elaborated with `omit [NormedAddCommGroup U]`).  This is strictly
more general than the requested signature and keeps the hypotheses tight, avoiding
the `unusedArguments` lint.

## Main definitions

* `DifferenceInclusion`: the uncertain dynamics `x⁺ ∈ F x u` of §3.1.5
  (printed p. 203 / PDF p. 251).
* `RobustlyAdmissible`: a state/control trajectory respects the state and input
  constraints and every successor lies in the difference inclusion.
* `additiveInclusion`: the additive uncertainty model `F x u = {f x u + w | w ∈ W}`.

## Main results

* `nominal_robust_descent`: the ISS-Lyapunov decrease `V (f x (κ x) + w) ≤
  V x − ℓ x (κ x) + L * d` from the nominal descent and the one-sided Lipschitz
  bound.
* `robust_ultimate_boundedness`: coercivity upgrades the decrease to
  `V (x_{n+1}) ≤ (1 − γ) * V (x_n) + L * d`, and the existing discrete ultimate
  boundedness lemma yields the eventual tube bound `(L * d) / γ + ε`.
-/

open Filter

open scoped Topology

@[expose] public section

variable {X U : Type*}

/-- The uncertain dynamics as a set-valued map `F : X → U → Set X`, writing
`x⁺ ∈ F x u` for the difference inclusion of Rawlings–Mayne–Diehl 2019, 2nd ed.,
§3.1.5 (printed p. 203 / PDF p. 251).  The set `F x u` collects *every* admissible
successor of the pair `(x, u)`; a deterministic plant `x⁺ = f x u` is the special
case `F x u = {f x u}`, and the additive uncertainty model of §3.2 (printed
p. 207 / PDF p. 255) is `F x u = {f x u + w | w ∈ W}` (see `additiveInclusion`). -/
def DifferenceInclusion (X U : Type*) : Type _ := X → U → Set X

/-- Robust admissibility of a state/control trajectory `(x, u)` for the difference
inclusion `F`: at every time `k` the state `x k` lies in the state constraint set
`Xs`, the control `u k` lies in the input constraint set `Us`, and the successor
`x (k + 1)` lies in the successor set `F (x k) (u k)`.

Because `F (x k) (u k)` is the set of *all* admissible successors of `(x k, u k)`,
the membership `x (k + 1) ∈ F (x k) (u k)` holds for every realization of the
uncertainty; it is the constraint-satisfaction clause of §3.1.5
(printed p. 203 / PDF p. 251), `x⁺ ∈ F (x, μ k x)`, paired with the state and input
constraints of the trajectory. -/
def RobustlyAdmissible (F : DifferenceInclusion X U) (Xs : Set X) (Us : Set U)
    (x : ℕ → X) (u : ℕ → U) : Prop :=
  (∀ k, x k ∈ Xs) ∧ (∀ k, u k ∈ Us) ∧ (∀ k, x (k + 1) ∈ F (x k) (u k))

variable [NormedAddCommGroup X] [NormedAddCommGroup U]

omit [NormedAddCommGroup U] in
/-- The additive uncertainty model of Rawlings–Mayne–Diehl 2019, 2nd ed., §3.1.5
(printed p. 203 / PDF p. 251): given the nominal dynamics `f` and a disturbance set
`W`, the successor set is `F x u = {f x u + w | w ∈ W}`, i.e.
`additiveInclusion f W x u`. -/
def additiveInclusion (f : X → U → X) (W : Set X) : DifferenceInclusion X U :=
  fun x u ↦ (fun w ↦ f x u + w) '' W

omit [NormedAddCommGroup U] in
/-- Membership in the additive inclusion unwinds to a disturbance witness: `y` is an
admissible successor of `(x, u)` under `additiveInclusion f W` exactly when
`y = f x u + w` for some `w ∈ W`. -/
theorem mem_additiveInclusion_iff {f : X → U → X} {W : Set X} {x : X} {u : U} {y : X} :
    y ∈ additiveInclusion f W x u ↔ ∃ w ∈ W, f x u + w = y := Iff.rfl

omit [NormedAddCommGroup U] in
/-- Unfolding `RobustlyAdmissible` for the additive uncertainty model: a trajectory
is robustly admissible for `additiveInclusion f W` exactly when it respects the
state and input constraints and every successor equals `f (x k) (u k) + w` for some
disturbance `w ∈ W`, i.e. it is a valid realization of the additive uncertainty
`x⁺ = f x u + w` of §3.1.5 (printed p. 203 / PDF p. 251). -/
theorem robustlyAdmissible_additive_iff {f : X → U → X} {W : Set X} {Xs : Set X}
    {Us : Set U} {x : ℕ → X} {u : ℕ → U} :
    RobustlyAdmissible (additiveInclusion f W) Xs Us x u ↔
      (∀ k, x k ∈ Xs) ∧ (∀ k, u k ∈ Us) ∧
        (∀ k, ∃ w ∈ W, f (x k) (u k) + w = x (k + 1)) := by
  simp only [RobustlyAdmissible, mem_additiveInclusion_iff]

omit [NormedAddCommGroup U] in
/-- **Nominal-robust (ISS-Lyapunov) one-step decrease** (Rawlings–Mayne–Diehl 2019,
2nd ed., Ch. 3 §3.2, printed pp. 204–207 / PDF pp. 253–256).  Suppose the nominal
closed loop `x⁺ = f x (κ x)` has the descent
`V (f x (κ x)) ≤ V x − ℓ x (κ x)` and the value function `V` obeys the one-sided
Lipschitz bound `V (y + w) ≤ V y + L * ‖w‖` with `L ≥ 0`.  Then for the true
additive-disturbance system `x⁺ = f x (κ x) + w` with `‖w‖ ≤ d` the value function
satisfies

`V (f x (κ x) + w) ≤ V x − ℓ x (κ x) + L * d`.

The proof chains the Lipschitz estimate at `y = f x (κ x)` with the nominal descent
and monotonicity of `x ↦ L * x` for `L ≥ 0`.  The descent hypothesis is left
generic; for a finite-horizon MPC problem it is supplied by
`mpc_valueFunction_decrease` of `DynamicalSystems.Control.MPC.Stability`. -/
theorem nominal_robust_descent (f : X → U → X) (κ : X → U) (V : X → ℝ) (ℓ : X → U → ℝ)
    (L d : ℝ) (hL : 0 ≤ L)
    (hdesc : ∀ x, V (f x (κ x)) ≤ V x - ℓ x (κ x))
    (hlip : ∀ y w, V (y + w) ≤ V y + L * ‖w‖)
    (x : X) (w : X) (hw : ‖w‖ ≤ d) :
    V (f x (κ x) + w) ≤ V x - ℓ x (κ x) + L * d := by
  have h1 : L * ‖w‖ ≤ L * d := mul_le_mul_of_nonneg_left hw hL
  have h2 : V (f x (κ x)) ≤ V x - ℓ x (κ x) := hdesc x
  calc
    V (f x (κ x) + w) ≤ V (f x (κ x)) + L * ‖w‖ := hlip _ _
    _ ≤ V x - ℓ x (κ x) + L * d := by linarith

omit [NormedAddCommGroup U] in
/-- **Robust ultimate boundedness of the value function** (Rawlings–Mayne–Diehl
2019, 2nd ed., Ch. 3 §3.2, printed pp. 204–208 / PDF pp. 253–256).  Let the nominal
closed loop have the descent `V (f x (κ x)) ≤ V x − ℓ x (κ x)`, let `V` be
one-sided Lipschitz with constant `L ≥ 0`, and let the stage cost dominate
`γ * V` with `0 < γ` (`γ * V y ≤ ℓ y (κ y)`, the coercivity used by
`mpc_geometric_decay` of `DynamicalSystems.Control.MPC.Stability`).  For a true
trajectory `x (n + 1) = f (x n) (κ (x n)) + w n` with `‖w n‖ ≤ d` along which `V` is
non-negative, the value function is ultimately bounded by `(L * d) / γ + ε` for
every `ε > 0`:

`∀ᶠ n, V (x n) ≤ (L * d) / γ + ε`.

Each step applies `nominal_robust_descent` and the domination to obtain
`V (x (n + 1)) ≤ (1 − γ) * V (x n) + L * d`; the affine contraction is then turned
into the ultimate bound by *reusing* the existing
`eventually_le_add_of_succ_le_mul_add` of
`DynamicalSystems.DiscreteTime.UltimateBoundedness` with `a = 1 − γ` and
`d = L * d`, noting `1 − (1 − γ) = γ`.  This is the robust-attraction clause of
Definition 3.1 (printed p. 207 / PDF p. 255): every realization ends up in the tube
of radius `(L * d) / γ + ε` around the origin.  The bound is an eventual one because
the pointwise bound without the `ε` slack fails in general (see the discussion in
`DynamicalSystems.DiscreteTime.UltimateBoundedness`). -/
theorem robust_ultimate_boundedness (f : X → U → X) (κ : X → U) (V : X → ℝ) (ℓ : X → U → ℝ)
    (L d γ ε : ℝ) (hL : 0 ≤ L) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hdesc : ∀ x, V (f x (κ x)) ≤ V x - ℓ x (κ x))
    (hlip : ∀ y w, V (y + w) ≤ V y + L * ‖w‖)
    (hcoer : ∀ y, γ * V y ≤ ℓ y (κ y))
    (x : ℕ → X) (w : ℕ → X)
    (hx : ∀ n, x (n + 1) = f (x n) (κ (x n)) + w n)
    (hw : ∀ n, ‖w n‖ ≤ d)
    (hVnn : ∀ n, 0 ≤ V (x n))
    (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, V (x n) ≤ (L * d) / γ + ε := by
  have ha0 : 0 ≤ 1 - γ := by linarith
  have ha1 : 1 - γ < 1 := by linarith
  have hrec : ∀ n, V (x (n + 1)) ≤ (1 - γ) * V (x n) + L * d := by
    intro n
    have hstep := nominal_robust_descent f κ V ℓ L d hL hdesc hlip (x n) (w n) (hw n)
    have hc := hcoer (x n)
    rw [hx n]
    linarith
  have hb := eventually_le_add_of_succ_le_mul_add ha0 ha1 hVnn hrec hε
  have hsub : (1 : ℝ) - (1 - γ) = γ := by ring
  rwa [hsub] at hb
