/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.FiniteHorizon
public import DynamicalSystems.DiscreteTime.Lyapunov

/-! # Economic model predictive control: dissipativity and average performance

This file formalises the algebraic core of economic model predictive control as
presented in Rawlings, Mayne and Diehl, *Model Predictive Control: Theory,
Computation, and Design*, 2nd ed., 2019, §2.8 (printed pp. 153–162, PDF
pp. 196–205).

In economic MPC the stage cost `ℓ x u` measures the economics of the process and is
not positive definite about a target equilibrium; instead the best steady-state
pair `(xs, us)` minimises `ℓ` over the steady states `x = f x u`.  Two ingredients
of §2.8 are isolated here over an arbitrary state space `X` and input space `U`:

* the *discrete pointwise storage inequality* of Definition 2.53 (printed p. 156),
  `λ (f x u) - λ x ≤ s x u`, formalised as `IsDissipative`;
* the *rotated stage cost* of Theorem 2.56 (printed p. 157),
  `ℓ x u - ℓ xs us + λ x - λ (f x u)`, formalised as `rotatedCost`.

The point of the rotation is recorded in `rotatedCost_nonneg`: when the system is
dissipative with respect to the supply rate `s x u = ℓ x u - ℓ xs us`, the rotated
cost is non-negative, which is exactly the positive-definiteness (2.37) that makes
economic MPC amenable to Lyapunov analysis.

Telescoping the storage inequality along an arbitrary trajectory
`x (k + 1) = f (x k) (u k)` yields the partial-sum average-performance bound
`N * ℓ xs us + λ (x N) - λ (x 0) ≤ ∑_{k < N} ℓ (x k) (u k)`: the average stage cost
is at least the steady-state cost up to the bounded storage term.  This is the
storage-inequality form of the asymptotic average performance discussion of §2.8.1
(printed p. 155): a storage function that is bounded below along the trajectory
makes the correction vanish, giving `liminf` of the average at least `ℓ xs us`.  The
complementary upper bound of Proposition 2.52 for the optimal economic MPC closed
loop rests on the terminal constraint and the value function rather than
dissipativity, and is a separate future step.

## Main definitions

* `IsDissipative`: the discrete storage inequality `λ (f x u) - λ x ≤ s x u` of
  Definition 2.53 (printed p. 156).
* `rotatedCost`: the rotated stage cost `ℓ x u + λ x - λ (f x u) - ℓ xs us` of
  Theorem 2.56 (printed p. 157).

## Main results

* `rotatedCost_nonneg`: dissipativity with supply rate `ℓ x u - ℓ xs us` makes the
  rotated cost non-negative (2.37), printed p. 157.
* `economic_average_performance`: the telescoped partial-sum bound from the
  storage inequality, the economic-MPC average-performance discussion of §2.8.1
  (printed p. 155).

## Scope

This is the algebraic core of §2.8 only.  The stability bridge of Theorem 2.56 — the
rotated value function `Ṽ_N` as a Lyapunov function for the economic MPC closed
loop, using the continuity Assumption 2.54 and the terminal equality constraint of
Assumption 2.51 — is a separate future step and is not established here. -/

@[expose] public section

variable {X U : Type*}

/-- The discrete, pointwise *storage inequality* of dissipativity
(Rawlings–Mayne–Diehl 2019, Definition 2.53, §2.8.2, printed p. 156): the system
`x⁺ = f x u` is dissipative with respect to the supply rate `s` if there is a
storage function `lam` with

`lam (f x u) - lam x ≤ s x u` for all states `x` and inputs `u`.

This is the discrete state-space storage condition (2.35).  It is deliberately kept
apart from `InputOutput.Dissipative.IsDissipativeWith`, which is the
continuous-time `L^p` *integral* supply inequality, and from
`Control.ControlLyapunov.IsControlLyapunovFunction`, which is a continuous,
control-affine object. -/
def IsDissipative (f : X → U → X) (s : X → U → ℝ) (lam : X → ℝ) : Prop :=
  ∀ x u, lam (f x u) - lam x ≤ s x u

/-- The *rotated stage cost* of economic MPC (Rawlings–Mayne–Diehl 2019,
Theorem 2.56, §2.8.2, printed p. 157):

`rotatedCost f ℓ lam xs us x u = ℓ x u + lam x - lam (f x u) - ℓ xs us`.

It is the economic stage cost `ℓ x u` shifted by the storage difference
`lam x - lam (f x u)` and by the steady-state cost `ℓ xs us`, matching (2.37) and
the displayed rotation before it.  With the dissipativity supply rate
`s x u = ℓ x u - ℓ xs us` it is non-negative (see `rotatedCost_nonneg`), which
supplies the positive-definiteness that the raw economic cost lacks. -/
def rotatedCost (f : X → U → X) (ℓ : X → U → ℝ) (lam : X → ℝ) (xs : X) (us : U)
    (x : X) (u : U) : ℝ :=
  ℓ x u + lam x - lam (f x u) - ℓ xs us

/-- The rotated stage cost is non-negative under dissipativity with respect to the
supply rate `s x u = ℓ x u - ℓ xs us` (Rawlings–Mayne–Diehl 2019, Theorem 2.56
and equation (2.37), §2.8.2, printed p. 157).

The storage inequality `lam (f x u) - lam x ≤ ℓ x u - ℓ xs us` rearranges directly
into `0 ≤ ℓ x u + lam x - lam (f x u) - ℓ xs us`, i.e.
`0 ≤ rotatedCost f ℓ lam xs us x u`.  This is equation (2.37) with `α` the zero
function; the strict version would add a comparison function `α (|x - xs|)` on the
right-hand side. -/
theorem rotatedCost_nonneg {f : X → U → X} {ℓ : X → U → ℝ} {lam : X → ℝ}
    {xs : X} {us : U}
    (h : IsDissipative f (fun x u ↦ ℓ x u - ℓ xs us) lam) (x : X) (u : U) :
    0 ≤ rotatedCost f ℓ lam xs us x u := by
  have hh : lam (f x u) - lam x ≤ ℓ x u - ℓ xs us := h x u
  simp only [rotatedCost]
  linarith

/-- **Asymptotic average performance of economic MPC, partial-sum form**
(Rawlings–Mayne–Diehl 2019, §2.8.1, printed p. 155).

Let `x (k + 1) = f (x k) (u k)` be any trajectory of the system and let the system
be dissipative with respect to the supply rate `s x u = ℓ x u - ℓ xs us` with storage
function `lam`.  Telescoping the storage inequality along the trajectory gives, for
every horizon `N`,

`N * ℓ xs us + lam (x N) - lam (x 0) ≤ ∑_{k < N} ℓ (x k) (u k)`,

i.e. the average stage cost `(1 / N) ∑_{k < N} ℓ (x k) (u k)` is at least the
steady-state cost `ℓ xs us` up to the bounded storage term
`(lam (x N) - lam (x 0)) / N`.  If `lam` is bounded below along the trajectory then
dividing by `N` and letting `N → ∞` gives `liminf` of the average at least
`ℓ xs us` (the storage-inequality form of the average-performance discussion of
§2.8.1, printed p. 155); the statement below keeps the exact finite-horizon
inequality, which is all the telescoping argument needs and requires no
boundedness. -/
theorem economic_average_performance {f : X → U → X} {ℓ : X → U → ℝ} {lam : X → ℝ}
    {xs : X} {us : U} {x : ℕ → X} {u : ℕ → U}
    (h : IsDissipative f (fun x u ↦ ℓ x u - ℓ xs us) lam)
    (hx : ∀ k, x (k + 1) = f (x k) (u k)) (N : ℕ) :
    (N : ℝ) * ℓ xs us + lam (x N) - lam (x 0) ≤
      ∑ k ∈ Finset.range N, ℓ (x k) (u k) := by
  have hstep : ∀ k, lam (x (k + 1)) - lam (x k) ≤ ℓ (x k) (u k) - ℓ xs us := by
    intro k
    have hk := h (x k) (u k)
    rwa [← hx k] at hk
  have htel : (∑ k ∈ Finset.range N, (lam (x (k + 1)) - lam (x k))) =
      lam (x N) - lam (x 0) :=
    Finset.sum_range_sub (fun k ↦ lam (x k)) N
  have hsum : (∑ k ∈ Finset.range N, (lam (x (k + 1)) - lam (x k))) ≤
      ∑ k ∈ Finset.range N, (ℓ (x k) (u k) - ℓ xs us) :=
    Finset.sum_le_sum fun k _ ↦ hstep k
  rw [htel] at hsum
  have hconst : (∑ k ∈ Finset.range N, (ℓ (x k) (u k) - ℓ xs us)) =
      (∑ k ∈ Finset.range N, ℓ (x k) (u k)) - (N : ℝ) * ℓ xs us := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hconst] at hsum
  linarith
