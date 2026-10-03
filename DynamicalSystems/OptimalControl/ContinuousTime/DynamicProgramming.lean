/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.ContinuousOCP
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Continuous-time dynamic programming and Hamilton-Jacobi-Bellman verification

This file develops the dynamic-programming principle and the Hamilton-Jacobi-Bellman (HJB)
verification theorem for continuous-time deterministic optimal control problems.

Given an optimal control problem `prob : ContinuousOCP X U`, the time-shifted subproblem starting at
time `t₀` with horizon `prob.T - t₀` is `continuousTailProblem prob t₀`. Its value function is
`valueFunctionFrom prob t₀ x₀`, representing the optimal cost-to-go from initial event `(t₀, x₀)`.

The main result is the **HJB verification theorem** (sufficiency / verification condition):
let `W : ℝ → X → ℝ` be a candidate cost-to-go satisfying the terminal condition
`W prob.T x ≤ prob.K x` and the HJB differential inequality
`-(∂ₜW)(t, x) ≤ prob.L t x u + ⟨∇ₓW(t, x), prob.f t x u⟩`
for all admissible states and controls. Then:
1. `W t₀ x₀ ≤ valueFunctionFrom prob t₀ x₀` (the lower bound, `hjb_verification_lower`).
2. If equality is attained along an admissible pair `(x, u)`, then `(x, u)` is an optimal pair for
   the time-shifted problem (`hjb_verification_optimal`).

The proofs proceed via the fundamental theorem of calculus along admissible trajectories and avoid
any assertion that the value function is differentiable or solves HJB as a PDE, following the
treatment in Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.1 (printed pp. 349–363,
in particular Lemma 8.1.6 and Theorem 36) and Hernández-Lerma, *An Introduction to Optimal Control
Theory: The Dynamic Programming Approach*, 1994, Ch. 3.

## Main definitions

* `continuousTailProblem`: the time-shifted subproblem starting at `t₀` with horizon `prob.T - t₀`.
* `valueFunctionFrom`: the optimal cost-to-go from `(t₀, x₀)`, i.e. the value function of
  `continuousTailProblem prob t₀`.
* `totalDerivOfPartials`: the continuous linear map on `ℝ × X` formed from a partial time
  derivative `Wt : ℝ` and a spatial Fréchet derivative `Wx : X →L[ℝ] ℝ`.

## Main results

* `hasDerivAt_of_hjb`: the multivariable chain rule along a trajectory for candidate functions `W`.
* `hasDerivAt_of_hjb_shift`: the chain rule along a time-shifted trajectory.
* `hjb_verification_trajectory_le`: the fundamental lower bound along any single admissible
  trajectory.
* `hjb_verification_lower`: the HJB verification theorem (lower-bound direction) bounding
  `valueFunctionFrom prob t₀ x₀`.
* `hjb_verification_optimal`: the HJB verification theorem (optimality direction) establishing
  optimality of an admissible pair when the lower bound is attained.
-/

@[expose] public section

open scoped Interval
open MeasureTheory

variable {X U : Type*}

/-- The time-shifted optimal control problem starting at time `t₀`: horizon `prob.T - t₀`,
time-shifted dynamics `s ↦ prob.f (t₀ + s) x u`, time-shifted running cost
`s ↦ prob.L (t₀ + s) x u`, terminal cost `prob.K`, and control constraint set `prob.controlSet`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.1, printed pp. 349–363;
Hernández-Lerma, *An Introduction to Optimal Control Theory: The Dynamic Programming Approach*,
1994, Ch. 3 §3.2). -/
def continuousTailProblem (prob : ContinuousOCP X U) (t₀ : ℝ) : ContinuousOCP X U where
  T := prob.T - t₀
  f := fun s x u ↦ prob.f (t₀ + s) x u
  L := fun s x u ↦ prob.L (t₀ + s) x u
  K := prob.K
  controlSet := prob.controlSet

@[simp] theorem continuousTailProblem_T (prob : ContinuousOCP X U) (t₀ : ℝ) :
    (continuousTailProblem prob t₀).T = prob.T - t₀ := rfl

@[simp] theorem continuousTailProblem_f (prob : ContinuousOCP X U) (t₀ : ℝ) (s : ℝ) (x : X)
    (u : U) :
    (continuousTailProblem prob t₀).f s x u = prob.f (t₀ + s) x u := rfl

@[simp] theorem continuousTailProblem_L (prob : ContinuousOCP X U) (t₀ : ℝ) (s : ℝ) (x : X)
    (u : U) :
    (continuousTailProblem prob t₀).L s x u = prob.L (t₀ + s) x u := rfl

@[simp] theorem continuousTailProblem_K (prob : ContinuousOCP X U) (t₀ : ℝ) :
    (continuousTailProblem prob t₀).K = prob.K := rfl

@[simp] theorem continuousTailProblem_controlSet (prob : ContinuousOCP X U) (t₀ : ℝ) :
    (continuousTailProblem prob t₀).controlSet = prob.controlSet := rfl

/-- Explicit expansion of the total cost for the time-shifted problem
`continuousTailProblem prob t₀`. -/
lemma continuousTotalCost_continuousTailProblem (prob : ContinuousOCP X U) (t₀ : ℝ)
    (x : ℝ → X) (u : ℝ → U) :
    continuousTotalCost (continuousTailProblem prob t₀) x u =
      (∫ s in 0..(prob.T - t₀), prob.L (t₀ + s) (x s) (u s)) + prob.K (x (prob.T - t₀)) := rfl

section Normed

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The dynamic-programming value function from initial time `t₀` and initial state `x₀`:
the infimum of total costs for `continuousTailProblem prob t₀` over all admissible pairs from `x₀`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.1, printed pp. 349–363;
Hernández-Lerma, 1994, Ch. 3 §3.2). -/
noncomputable def valueFunctionFrom (prob : ContinuousOCP X U) (t₀ : ℝ) (x₀ : X) : ℝ :=
  continuousValueFunction (continuousTailProblem prob t₀) x₀

/-- The multivariable chain rule along a trajectory: if `W : ℝ → X → ℝ` has joint Fréchet
derivative `dW` at `(t, x t)` and `x` has derivative `x' t` at `t`, then `s ↦ W s (x s)` has
derivative `dW (1, x' t)` at `t` (Sontag, *Mathematical Control Theory*, 2nd ed., 1998,
Ch. 8 §8.1, printed pp. 349–363). -/
theorem hasDerivAt_of_hjb (W : ℝ → X → ℝ) (x : ℝ → X) (t : ℝ) (x' : X)
    (dW : (ℝ × X) →L[ℝ] ℝ)
    (hW : HasFDerivAt (fun p : ℝ × X ↦ W p.1 p.2) dW (t, x t))
    (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s ↦ W s (x s)) (dW (1, x')) t := by
  have hpair : HasDerivAt (fun s ↦ (s, x s)) (1, x') t :=
    HasDerivAt.prodMk (hasDerivAt_id' t) hx
  exact HasFDerivAt.comp_hasDerivAt (x := t) hW hpair

/-- The multivariable chain rule along a time-shifted trajectory: if `W : ℝ → X → ℝ` has
joint Fréchet derivative `dW` at `(t₀ + s, x s)` and `x` has derivative `x' s` at `s`,
then `s ↦ W (t₀ + s) (x s)` has derivative `dW (1, x' s)` at `s` (Sontag, *Mathematical
Control Theory*, 2nd ed., 1998, Ch. 8 §8.1, printed pp. 349–363). -/
theorem hasDerivAt_of_hjb_shift (W : ℝ → X → ℝ) (t₀ : ℝ) (x : ℝ → X) (s : ℝ) (x' : X)
    (dW : (ℝ × X) →L[ℝ] ℝ)
    (hW : HasFDerivAt (fun p : ℝ × X ↦ W p.1 p.2) dW (t₀ + s, x s))
    (hx : HasDerivAt x x' s) :
    HasDerivAt (fun s ↦ W (t₀ + s) (x s)) (dW (1, x')) s := by
  have h1 : HasDerivAt (fun s ↦ t₀ + s) 1 s := by
    simpa using (hasDerivAt_id' s).const_add t₀
  have hpair : HasDerivAt (fun s ↦ (t₀ + s, x s)) (1, x') s :=
    HasDerivAt.prodMk h1 hx
  exact HasFDerivAt.comp_hasDerivAt (x := s) hW hpair

/-- Total Fréchet derivative on `ℝ × X` assembled from a partial time derivative `Wt : ℝ`
and a spatial Fréchet derivative `Wx : X →L[ℝ] ℝ`. -/
def totalDerivOfPartials (Wt : ℝ) (Wx : X →L[ℝ] ℝ) : (ℝ × X) →L[ℝ] ℝ :=
  ContinuousLinearMap.coprod (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) Wt) Wx

@[simp] theorem totalDerivOfPartials_apply (Wt : ℝ) (Wx : X →L[ℝ] ℝ) (dt : ℝ) (dx : X) :
    totalDerivOfPartials Wt Wx (dt, dx) = dt * Wt + Wx dx := by
  simp [totalDerivOfPartials]

theorem totalDerivOfPartials_one (Wt : ℝ) (Wx : X →L[ℝ] ℝ) (dx : X) :
    totalDerivOfPartials Wt Wx (1, dx) = Wt + Wx dx := by
  simp [totalDerivOfPartials]

/-- The fundamental lower-bound inequality along any admissible trajectory:
integrating the derivative of `s ↦ W (t₀ + s) (x s)` via FTC on `[0, prob.T - t₀]` shows that
`W t₀ x₀` is bounded above by the total cost of `(x, u)` (Sontag, *Mathematical Control Theory*,
2nd ed., 1998, Ch. 8 §8.1, Lemma 8.1.6 and Theorem 36; Hernández-Lerma, 1994, Ch. 3 §3.2). -/
theorem hjb_verification_trajectory_le (prob : ContinuousOCP X U) (t₀ : ℝ) (x₀ : X)
    (W : ℝ → X → ℝ) (W' : ℝ → ℝ) (x : ℝ → X) (u : ℝ → U)
    (ht : t₀ ≤ prob.T)
    (hadm : IsAdmissiblePair (continuousTailProblem prob t₀) x₀ x u)
    (hW_term : W prob.T (x (prob.T - t₀)) ≤ prob.K (x (prob.T - t₀)))
    (hW_deriv : ∀ s ∈ Set.Icc 0 (prob.T - t₀),
      HasDerivAt (fun s ↦ W (t₀ + s) (x s)) (W' s) s)
    (hW_int : IntervalIntegrable W' volume 0 (prob.T - t₀))
    (h_hjb : ∀ s ∈ Set.Icc 0 (prob.T - t₀),
      -prob.L (t₀ + s) (x s) (u s) ≤ W' s) :
    W t₀ x₀ ≤ continuousTotalCost (continuousTailProblem prob t₀) x u := by
  have hT' : 0 ≤ prob.T - t₀ := sub_nonneg.mpr ht
  have huIcc : Set.uIcc 0 (prob.T - t₀) = Set.Icc 0 (prob.T - t₀) := Set.uIcc_of_le hT'
  have hderiv : ∀ s ∈ Set.uIcc 0 (prob.T - t₀),
      HasDerivAt (fun s ↦ W (t₀ + s) (x s)) (W' s) s := by
    intro s hs
    rw [huIcc] at hs
    exact hW_deriv s hs
  have hftc : ∫ s in 0..(prob.T - t₀), W' s =
      W prob.T (x (prob.T - t₀)) - W t₀ x₀ := by
    have h_eval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hW_int
    have h0 : t₀ + 0 = t₀ := add_zero t₀
    have hT : t₀ + (prob.T - t₀) = prob.T := add_sub_cancel t₀ prob.T
    have hx0 : x 0 = x₀ := hadm.1
    simp only [h0, hT, hx0] at h_eval
    exact h_eval
  have hL_int : IntervalIntegrable (fun s ↦ prob.L (t₀ + s) (x s) (u s)) volume 0 (prob.T - t₀) :=
    hadm.2.2.2
  have hnegL_int :
      IntervalIntegrable (fun s ↦ -prob.L (t₀ + s) (x s) (u s)) volume 0 (prob.T - t₀) :=
    hL_int.neg
  have hmono : (∫ s in 0..(prob.T - t₀), -prob.L (t₀ + s) (x s) (u s)) ≤
      ∫ s in 0..(prob.T - t₀), W' s := by
    exact intervalIntegral.integral_mono_on hT' hnegL_int hW_int h_hjb
  rw [intervalIntegral.integral_neg] at hmono
  rw [hftc] at hmono
  unfold continuousTotalCost
  simp only [continuousTailProblem_T, continuousTailProblem_L, continuousTailProblem_K]
  linarith

/-- **HJB verification theorem (lower-bound direction).** If a candidate cost-to-go `W : ℝ → X → ℝ`
satisfies the terminal condition `W prob.T x ≤ prob.K x` and along every admissible pair `(x, u)`
admits an integrable trajectory derivative satisfying the HJB inequality
`-prob.L ≤ W'`, then `W t₀ x₀ ≤ valueFunctionFrom prob t₀ x₀`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.1, Theorem 36;
Hernández-Lerma, 1994, Ch. 3 §3.2). -/
theorem hjb_verification_lower (prob : ContinuousOCP X U) (t₀ : ℝ) (x₀ : X)
    (W : ℝ → X → ℝ)
    (ht : t₀ ≤ prob.T)
    (hne : (continuousCostSet (continuousTailProblem prob t₀) x₀).Nonempty)
    (hW_term : ∀ x, W prob.T x ≤ prob.K x)
    (hW_traj : ∀ x u, IsAdmissiblePair (continuousTailProblem prob t₀) x₀ x u →
      ∃ W' : ℝ → ℝ,
        (∀ s ∈ Set.Icc 0 (prob.T - t₀),
          HasDerivAt (fun s ↦ W (t₀ + s) (x s)) (W' s) s) ∧
        IntervalIntegrable W' volume 0 (prob.T - t₀) ∧
        (∀ s ∈ Set.Icc 0 (prob.T - t₀),
          -prob.L (t₀ + s) (x s) (u s) ≤ W' s)) :
    W t₀ x₀ ≤ valueFunctionFrom prob t₀ x₀ := by
  unfold valueFunctionFrom
  refine le_continuousValueFunction (continuousTailProblem prob t₀) x₀ hne ?_
  rintro c ⟨x, u, hadm, rfl⟩
  obtain ⟨W', hderiv, hint, hhjb⟩ := hW_traj x u hadm
  exact hjb_verification_trajectory_le prob t₀ x₀ W W' x u ht hadm (hW_term (x (prob.T - t₀)))
    hderiv hint hhjb

/-- HJB verification lower bound under pointwise joint Fréchet differentiability:
if `W` has joint derivative `dW` and satisfies `-prob.L ≤ dW (1, prob.f)`, then
`W t₀ x₀ ≤ valueFunctionFrom prob t₀ x₀` (Sontag, 1998, Ch. 8 §8.1, Theorem 36). -/
theorem hjb_verification_lower_of_fderiv (prob : ContinuousOCP X U) (t₀ : ℝ) (x₀ : X)
    (W : ℝ → X → ℝ) (dW : ℝ → X → (ℝ × X) →L[ℝ] ℝ)
    (ht : t₀ ≤ prob.T)
    (hne : (continuousCostSet (continuousTailProblem prob t₀) x₀).Nonempty)
    (hW_term : ∀ x, W prob.T x ≤ prob.K x)
    (hW_diff : ∀ s ∈ Set.Icc 0 (prob.T - t₀), ∀ x,
      HasFDerivAt (fun p : ℝ × X ↦ W p.1 p.2) (dW (t₀ + s) x) (t₀ + s, x))
    (h_hjb : ∀ s ∈ Set.Icc 0 (prob.T - t₀), ∀ x, ∀ u ∈ prob.controlSet,
      -prob.L (t₀ + s) x u ≤ dW (t₀ + s) x (1, prob.f (t₀ + s) x u))
    (h_int : ∀ x u, IsAdmissiblePair (continuousTailProblem prob t₀) x₀ x u →
      IntervalIntegrable
        (fun s ↦ dW (t₀ + s) (x s) (1, prob.f (t₀ + s) (x s) (u s)))
        volume 0 (prob.T - t₀)) :
    W t₀ x₀ ≤ valueFunctionFrom prob t₀ x₀ := by
  refine hjb_verification_lower prob t₀ x₀ W ht hne hW_term ?_
  intro x u hadm
  refine ⟨fun s ↦ dW (t₀ + s) (x s) (1, prob.f (t₀ + s) (x s) (u s)), ?_, h_int x u hadm, ?_⟩
  · intro s hs
    exact hasDerivAt_of_hjb_shift W t₀ x s (prob.f (t₀ + s) (x s) (u s))
      (dW (t₀ + s) (x s)) (hW_diff s hs (x s)) (hadm.2.2.1 s hs)
  · intro s hs
    exact h_hjb s hs (x s) (u s) (hadm.2.1 s hs)

/-- HJB verification lower bound in classical partial-derivative form:
if `W` has partial time derivative `Wt` and spatial Fréchet derivative `Wx` satisfying
`-(∂ₜW)(t, x) ≤ prob.L t x u + ⟨∇ₓW(t, x), prob.f t x u⟩`, then
`W t₀ x₀ ≤ valueFunctionFrom prob t₀ x₀` (Sontag, 1998, Ch. 8 §8.1, Theorem 36;
Hernández-Lerma, 1994, Ch. 3 §3.2). -/
theorem hjb_verification_lower_of_partials (prob : ContinuousOCP X U) (t₀ : ℝ) (x₀ : X)
    (W : ℝ → X → ℝ) (Wt : ℝ → X → ℝ) (Wx : ℝ → X → (X →L[ℝ] ℝ))
    (ht : t₀ ≤ prob.T)
    (hne : (continuousCostSet (continuousTailProblem prob t₀) x₀).Nonempty)
    (hW_term : ∀ x, W prob.T x ≤ prob.K x)
    (hW_diff : ∀ s ∈ Set.Icc 0 (prob.T - t₀), ∀ x,
      HasFDerivAt (fun p : ℝ × X ↦ W p.1 p.2)
        (totalDerivOfPartials (Wt (t₀ + s) x) (Wx (t₀ + s) x)) (t₀ + s, x))
    (h_hjb : ∀ s ∈ Set.Icc 0 (prob.T - t₀), ∀ x, ∀ u ∈ prob.controlSet,
      - (Wt (t₀ + s) x) ≤ prob.L (t₀ + s) x u + Wx (t₀ + s) x (prob.f (t₀ + s) x u))
    (h_int : ∀ x u, IsAdmissiblePair (continuousTailProblem prob t₀) x₀ x u →
      IntervalIntegrable
        (fun s ↦ Wt (t₀ + s) (x s) + Wx (t₀ + s) (x s) (prob.f (t₀ + s) (x s) (u s)))
        volume 0 (prob.T - t₀)) :
    W t₀ x₀ ≤ valueFunctionFrom prob t₀ x₀ := by
  refine hjb_verification_lower_of_fderiv prob t₀ x₀ W
    (fun t x ↦ totalDerivOfPartials (Wt t x) (Wx t x)) ht hne hW_term hW_diff ?_ ?_
  · intro s hs x u hu
    have hjb := h_hjb s hs x u hu
    simp only [totalDerivOfPartials_one]
    linarith
  · intro x u hadm
    have hint := h_int x u hadm
    simp only [totalDerivOfPartials_one]
    exact hint

/-- **HJB verification theorem (optimality direction).** Under the HJB verification hypotheses,
if an admissible pair `(x, u)` achieves cost no greater than `W t₀ x₀` (in particular when
`continuousTotalCost (continuousTailProblem prob t₀) x u = W t₀ x₀`), then `(x, u)` is an
optimal pair for `continuousTailProblem prob t₀` (Sontag, *Mathematical Control Theory*, 2nd ed.,
1998, Ch. 8 §8.1, Lemma 8.1.6 and Theorem 36; Hernández-Lerma, 1994, Ch. 3 §3.2). -/
theorem hjb_verification_optimal (prob : ContinuousOCP X U) (t₀ : ℝ) (x₀ : X)
    (W : ℝ → X → ℝ) (x : ℝ → X) (u : ℝ → U)
    (ht : t₀ ≤ prob.T)
    (hadm : IsAdmissiblePair (continuousTailProblem prob t₀) x₀ x u)
    (hW_term : ∀ y, W prob.T y ≤ prob.K y)
    (hW_traj : ∀ v w, IsAdmissiblePair (continuousTailProblem prob t₀) x₀ v w →
      ∃ W' : ℝ → ℝ,
        (∀ s ∈ Set.Icc 0 (prob.T - t₀),
          HasDerivAt (fun s ↦ W (t₀ + s) (v s)) (W' s) s) ∧
        IntervalIntegrable W' volume 0 (prob.T - t₀) ∧
        (∀ s ∈ Set.Icc 0 (prob.T - t₀),
          -prob.L (t₀ + s) (v s) (w s) ≤ W' s))
    (hW_eq : continuousTotalCost (continuousTailProblem prob t₀) x u ≤ W t₀ x₀) :
    IsOptimalPair (continuousTailProblem prob t₀) x₀ x u := by
  rw [isOptimalPair_iff]
  refine ⟨hadm, fun v w hvw ↦ ?_⟩
  obtain ⟨W', hderiv, hint, hhjb⟩ := hW_traj v w hvw
  have hvw_le := hjb_verification_trajectory_le prob t₀ x₀ W W' v w ht hvw
    (hW_term (v (prob.T - t₀))) hderiv hint hhjb
  exact le_trans hW_eq hvw_le

/-- Optimality direction when equality `W t₀ x₀ = continuousTotalCost ...` holds. -/
theorem hjb_verification_optimal_of_eq (prob : ContinuousOCP X U) (t₀ : ℝ) (x₀ : X)
    (W : ℝ → X → ℝ) (x : ℝ → X) (u : ℝ → U)
    (ht : t₀ ≤ prob.T)
    (hadm : IsAdmissiblePair (continuousTailProblem prob t₀) x₀ x u)
    (hW_term : ∀ y, W prob.T y ≤ prob.K y)
    (hW_traj : ∀ v w, IsAdmissiblePair (continuousTailProblem prob t₀) x₀ v w →
      ∃ W' : ℝ → ℝ,
        (∀ s ∈ Set.Icc 0 (prob.T - t₀),
          HasDerivAt (fun s ↦ W (t₀ + s) (v s)) (W' s) s) ∧
        IntervalIntegrable W' volume 0 (prob.T - t₀) ∧
        (∀ s ∈ Set.Icc 0 (prob.T - t₀),
          -prob.L (t₀ + s) (v s) (w s) ≤ W' s))
    (hW_eq : W t₀ x₀ = continuousTotalCost (continuousTailProblem prob t₀) x u) :
    IsOptimalPair (continuousTailProblem prob t₀) x₀ x u :=
  hjb_verification_optimal prob t₀ x₀ W x u ht hadm hW_term hW_traj (le_of_eq hW_eq.symm)

/-- Optimality direction under pointwise joint Fréchet differentiability of `W`. -/
theorem hjb_verification_optimal_of_fderiv (prob : ContinuousOCP X U) (t₀ : ℝ) (x₀ : X)
    (W : ℝ → X → ℝ) (dW : ℝ → X → (ℝ × X) →L[ℝ] ℝ) (x : ℝ → X) (u : ℝ → U)
    (ht : t₀ ≤ prob.T)
    (hadm : IsAdmissiblePair (continuousTailProblem prob t₀) x₀ x u)
    (hW_term : ∀ y, W prob.T y ≤ prob.K y)
    (hW_diff : ∀ s ∈ Set.Icc 0 (prob.T - t₀), ∀ y,
      HasFDerivAt (fun p : ℝ × X ↦ W p.1 p.2) (dW (t₀ + s) y) (t₀ + s, y))
    (h_hjb : ∀ s ∈ Set.Icc 0 (prob.T - t₀), ∀ y, ∀ w ∈ prob.controlSet,
      -prob.L (t₀ + s) y w ≤ dW (t₀ + s) y (1, prob.f (t₀ + s) y w))
    (h_int : ∀ v w, IsAdmissiblePair (continuousTailProblem prob t₀) x₀ v w →
      IntervalIntegrable
        (fun s ↦ dW (t₀ + s) (v s) (1, prob.f (t₀ + s) (v s) (w s)))
        volume 0 (prob.T - t₀))
    (hW_eq : continuousTotalCost (continuousTailProblem prob t₀) x u ≤ W t₀ x₀) :
    IsOptimalPair (continuousTailProblem prob t₀) x₀ x u := by
  refine hjb_verification_optimal prob t₀ x₀ W x u ht hadm hW_term ?_ hW_eq
  intro v w hvw
  refine ⟨fun s ↦ dW (t₀ + s) (v s) (1, prob.f (t₀ + s) (v s) (w s)), ?_, h_int v w hvw, ?_⟩
  · intro s hs
    exact hasDerivAt_of_hjb_shift W t₀ v s (prob.f (t₀ + s) (v s) (w s))
      (dW (t₀ + s) (v s)) (hW_diff s hs (v s)) (hvw.2.2.1 s hs)
  · intro s hs
    exact h_hjb s hs (v s) (w s) (hvw.2.1 s hs)

/-- Optimality direction under pointwise partial derivatives of `W`. -/
theorem hjb_verification_optimal_of_partials (prob : ContinuousOCP X U) (t₀ : ℝ) (x₀ : X)
    (W : ℝ → X → ℝ) (Wt : ℝ → X → ℝ) (Wx : ℝ → X → (X →L[ℝ] ℝ)) (x : ℝ → X) (u : ℝ → U)
    (ht : t₀ ≤ prob.T)
    (hadm : IsAdmissiblePair (continuousTailProblem prob t₀) x₀ x u)
    (hW_term : ∀ y, W prob.T y ≤ prob.K y)
    (hW_diff : ∀ s ∈ Set.Icc 0 (prob.T - t₀), ∀ y,
      HasFDerivAt (fun p : ℝ × X ↦ W p.1 p.2)
        (totalDerivOfPartials (Wt (t₀ + s) y) (Wx (t₀ + s) y)) (t₀ + s, y))
    (h_hjb : ∀ s ∈ Set.Icc 0 (prob.T - t₀), ∀ y, ∀ w ∈ prob.controlSet,
      - (Wt (t₀ + s) y) ≤ prob.L (t₀ + s) y w + Wx (t₀ + s) y (prob.f (t₀ + s) y w))
    (h_int : ∀ v w, IsAdmissiblePair (continuousTailProblem prob t₀) x₀ v w →
      IntervalIntegrable
        (fun s ↦ Wt (t₀ + s) (v s) + Wx (t₀ + s) (v s) (prob.f (t₀ + s) (v s) (w s)))
        volume 0 (prob.T - t₀))
    (hW_eq : continuousTotalCost (continuousTailProblem prob t₀) x u ≤ W t₀ x₀) :
    IsOptimalPair (continuousTailProblem prob t₀) x₀ x u := by
  refine hjb_verification_optimal_of_fderiv prob t₀ x₀ W
    (fun t x ↦ totalDerivOfPartials (Wt t x) (Wx t x)) x u ht hadm hW_term hW_diff ?_ ?_ hW_eq
  · intro s hs y w hw
    have hjb := h_hjb s hs y w hw
    simp only [totalDerivOfPartials_one]
    linarith
  · intro v w hvw
    have hint := h_int v w hvw
    simp only [totalDerivOfPartials_one]
    exact hint

/-- An admissible pair is optimal whenever its total cost matches an established lower bound
on all admissible costs. -/
theorem isOptimalPair_of_cost_le_all (prob : ContinuousOCP X U) (t₀ : ℝ) (x₀ : X)
    (W : ℝ → X → ℝ) (x : ℝ → X) (u : ℝ → U)
    (hadm : IsAdmissiblePair (continuousTailProblem prob t₀) x₀ x u)
    (hW_le : ∀ v w, IsAdmissiblePair (continuousTailProblem prob t₀) x₀ v w →
      W t₀ x₀ ≤ continuousTotalCost (continuousTailProblem prob t₀) v w)
    (hW_eq : continuousTotalCost (continuousTailProblem prob t₀) x u ≤ W t₀ x₀) :
    IsOptimalPair (continuousTailProblem prob t₀) x₀ x u := by
  rw [isOptimalPair_iff]
  refine ⟨hadm, fun v w hvw ↦ ?_⟩
  exact le_trans hW_eq (hW_le v w hvw)

end Normed
