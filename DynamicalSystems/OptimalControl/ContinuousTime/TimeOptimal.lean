/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.ContinuousOCP
public import DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Real.Sign

/-!
# Time-optimal control for linear systems

This module formalizes the *setup* of the minimum-time problem for the
time-invariant continuous-time linear system
$$\dot{x} = A x + B u, \qquad u(t) \in U,$$
with a compact convex control-value set `U` (here instantiated for the unit box
`U = {u | ∀ i, |u i| ≤ 1}` in the bang-bang computation), following Sontag,
*Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed.,
1998, Ch. 10 (printed pp. 423–444, PDF pp. 435–456).

For time-optimal problems the running cost is *identically one*, so the integral
cost **is** the elapsed time. We package this as `timeOptimalOCP`, for which
`continuousTotalCost` reduces to the horizon `T`
(`timeOptimalOCP_totalCost`). The minimal time to steer the origin into a target
`xf` is then the infimum of the feasible times (`minimumTime`, over the
reachability predicate `ReachableByTime`). Following the contract for the
continuous OCP substrate, no global solution map is postulated and no topological
closedness of the reachable set is claimed: the minimum is a genuine `sInf`, whose
basic lower-bound and upper-bound properties are recorded.

The two structural results that are fully proved here are:

* `timeOptimal_hamiltonianMinimizing`: for `L ≡ 1` the Pontryagin Hamiltonian is
  `H = 1 + ⟨λ, A x + B u⟩`, so the Hamiltonian-minimisation clause of S5's
  `HamiltonianMinimizing` is *exactly* the linear-form minimisation
  `⟨λ, B u⟩ ≤ ⟨λ, B w⟩` for all admissible `w` (the constant `1` and the `A x`
  term cancel, Sontag §10.2, Theorem 48);
* `timeOptimal_bangBang`: over the box `U = {u | ∀ i, |u i| ≤ 1}` the minimiser
  of the linear form `⟨λ, B u⟩ = ⟨Bᵀ λ, u⟩` is componentwise
  `uᵢ = -sign (Bᵀλ)ᵢ`, so a time-optimal control takes values at the box
  vertices; at minimisers `uᵢ · (Bᵀλ)ᵢ ≤ 0` and `|uᵢ| = 1` whenever the `i`-th
  component of `Bᵀλ` is nonzero. The `sign 0 = 0` corner (a singular arc, where
  the corresponding component is unconstrained) is stated honestly: the
  equality `uᵢ = -sign (Bᵀλ)ᵢ` is only asserted when `(Bᵀλ)ᵢ ≠ 0`. The
  general-compact-convex-set version is out of scope; the box is stated
  explicitly.

## Main definitions

* `timeOptimalOCP`: the time-optimal OCP data (`L ≡ 1`, `K ≡ 0`).
* `ReachableByTime`: reachability of a target at a prescribed time.
* `minimumTime`: the infimum of feasible steering times.
* `unitBox`: the componentwise unit box in `EuclideanSpace ℝ ι`.
* `linearMinimizer_bangBang`: minimiser of a linear form over the box.

## Main results

* `timeOptimal_hamiltonianMinimizing`: the PMP reduction to the linear form.
* `timeOptimal_bangBang`: bang-bang structure of time-optimal controls.

## References

* E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional
  Systems*, 2nd ed., Springer, 1998, Ch. 10, §10.1–§10.3 (Theorems 45–51).
* L. D. Berkovitz and N. G. Medhin, *Nonlinear Optimal Control Theory*, Chapman
  & Hall/CRC, 2013, Ch. 5–6 (existence and the maximum principle).
-/

@[expose] public section

open scoped Interval
open MeasureTheory

variable {E U : Type*}

/-! ### The time-optimal optimal control problem -/

section TimeOptimalProblem

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- The time-optimal optimal control problem for the time-invariant linear system
`ẋ = A x + B u` with control-value set `controlSet`: the running cost is
identically `1` (so the integral cost is exactly the elapsed time, Sontag,
*Mathematical Control Theory*, 2nd ed., 1998, Ch. 10 §10.1, printed pp. 423–429),
the terminal cost is `0`, and the horizon is `T`. -/
def timeOptimalOCP (A : E →L[ℝ] E) (B : U →L[ℝ] E) (controlSet : Set U) (T : ℝ) :
    ContinuousOCP E U where
  T := T
  f := fun _ x u ↦ A x + B u
  L := fun _ _ _ ↦ 1
  K := fun _ ↦ 0
  controlSet := controlSet

/-- For the time-optimal OCP the total cost is exactly the horizon `T`: the
running cost `L ≡ 1` integrates to `T` and the terminal cost vanishes. -/
theorem timeOptimalOCP_totalCost (A : E →L[ℝ] E) (B : U →L[ℝ] E) (controlSet : Set U)
    (T : ℝ) (x : ℝ → E) (u : ℝ → U) :
    continuousTotalCost (timeOptimalOCP A B controlSet T) x u = T := by
  simp [continuousTotalCost, timeOptimalOCP, intervalIntegral.integral_const]

/-- Reachability of `xf` from `x₀` at the prescribed time `T` for the linear
system `ẋ = A x + B u` with controls in `controlSet`: there is an admissible
trajectory/control pair (in the relational sense of `IsAdmissiblePair`) with
`x T = xf` (Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 10 §10.1,
reachable set `R_T(x₀)`, printed p. 423). -/
def ReachableByTime (A : E →L[ℝ] E) (B : U →L[ℝ] E) (controlSet : Set U)
    (x₀ xf : E) (T : ℝ) : Prop :=
  ∃ x : ℝ → E, ∃ u : ℝ → U,
    IsAdmissiblePair (timeOptimalOCP A B controlSet T) x₀ x u ∧ x T = xf

/-- The minimum time to steer the linear system `ẋ = A x + B u` from `x₀` to the
target `xf` using controls in `controlSet`, defined as the infimum of the times
`T ≥ 0` at which `xf` is reachable (Sontag, *Mathematical Control Theory*, 2nd
ed., 1998, Ch. 10 §10.1, printed pp. 430–431). The target set of the chapter is
the origin, encoded here by the instance `xf = 0`.

This is a genuine `sInf` into `ℝ`: existence of a minimiser is not claimed (it
requires closedness of the reachable set, Sontag Theorem 46), and the value can be
`0` when the feasible set is empty. Only nonnegative times are allowed. -/
noncomputable def minimumTime (A : E →L[ℝ] E) (B : U →L[ℝ] E) (controlSet : Set U)
    (x₀ xf : E) : ℝ :=
  sInf {T : ℝ | 0 ≤ T ∧ ReachableByTime A B controlSet x₀ xf T}

/-- The feasible-time set of `minimumTime` is bounded below by `0`. -/
theorem bddBelow_minimumTimeSet (A : E →L[ℝ] E) (B : U →L[ℝ] E) (controlSet : Set U)
    (x₀ xf : E) :
    BddBelow {T : ℝ | 0 ≤ T ∧ ReachableByTime A B controlSet x₀ xf T} :=
  ⟨0, fun _ hT ↦ hT.1⟩

/-- A feasible time bounds the minimum time from above. -/
theorem minimumTime_le (A : E →L[ℝ] E) (B : U →L[ℝ] E) (controlSet : Set U)
    (x₀ xf : E) {T : ℝ} (hT : 0 ≤ T) (h : ReachableByTime A B controlSet x₀ xf T) :
    minimumTime A B controlSet x₀ xf ≤ T :=
  csInf_le (bddBelow_minimumTimeSet A B controlSet x₀ xf) ⟨hT, h⟩

/-- The minimum time is nonnegative whenever the target is reachable at all. -/
theorem minimumTime_nonneg (A : E →L[ℝ] E) (B : U →L[ℝ] E) (controlSet : Set U)
    (x₀ xf : E)
    (hne : {T : ℝ | 0 ≤ T ∧ ReachableByTime A B controlSet x₀ xf T}.Nonempty) :
    0 ≤ minimumTime A B controlSet x₀ xf :=
  le_csInf hne fun _ hT ↦ hT.1

end TimeOptimalProblem

/-! ### The Pontryagin reduction for the time-optimal Hamiltonian -/

section HamiltonianReduction

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- **Maximum-principle form for time-optimality.**
For the time-optimal problem the running cost is `L ≡ 1` and the dynamics is
`ẋ = A x + B u`, so the Pontryagin Hamiltonian is `H = 1 + ⟨λ, A x + B u⟩`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 10 §10.2, the adjoint
equation `λ̇ = -Aᵀλ` and the maximisation `λ(t)ᵀ B ω(t) = max_u λ(t)ᵀ B u`,
Theorem 48, printed p. 434). The constant `1` and the state term `⟨λ, A x⟩`
cancel additively, so the pointwise minimisation clause of S5's
`HamiltonianMinimizing` for this Hamiltonian is *exactly* the linear-form
minimisation `⟨λ, B u⟩ ≤ ⟨λ, B w⟩` over the control set. -/
theorem timeOptimal_hamiltonianMinimizing (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (controlSet : Set U) (T : ℝ) (x : ℝ → E) (u : ℝ → U) (p : ℝ → E) :
    HamiltonianMinimizing (fun _ _ _ ↦ (1 : ℝ)) (fun _ x u ↦ A x + B u) controlSet T x u p ↔
      ∀ t ∈ Set.Icc 0 T, ∀ w ∈ controlSet,
        inner ℝ (p t) (B (u t)) ≤ inner ℝ (p t) (B w) := by
  unfold HamiltonianMinimizing
  simp only [hamiltonianOf_apply]
  constructor
  · intro h t ht w hw
    have hle := h t ht w hw
    rw [inner_add_right, inner_add_right] at hle
    linarith
  · intro h t ht w hw
    rw [inner_add_right, inner_add_right]
    linarith [h t ht w hw]

end HamiltonianReduction

/-! ### Bang-bang structure over the unit box -/

section BangBang

/-- The componentwise unit box `{u : EuclideanSpace ℝ ι | ∀ i, |u i| ≤ 1}` in
`EuclideanSpace ℝ ι`, the control-value set of the bang-bang computation
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 10 §10.3, the
hypercube case, printed p. 438). -/
def unitBox (ι : Type*) : Set (EuclideanSpace ℝ ι) :=
  {u | ∀ i, |u i| ≤ 1}

/-- **Minimiser of a scalar linear form over the unit interval.**
If `t ∈ [-1, 1]` minimises `s ↦ c * s` on `[-1, 1]`, then `c * t` attains the
minimal value `-|c|`, the product is nonpositive, and whenever `c ≠ 0` the
minimiser is the unique endpoint `t = -sign c` with `|t| = 1`. The degenerate case
`c = 0` (a singular arc) is excluded from the endpoint conclusion, matching the
`sign 0 = 0` convention. -/
theorem mul_minimizer_on_Icc {c t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hmin : ∀ s ∈ Set.Icc (-1 : ℝ) 1, c * t ≤ c * s) :
    c * t = -|c| ∧ c * t ≤ 0 ∧ (c ≠ 0 → t = -Real.sign c) ∧ (c ≠ 0 → |t| = 1) := by
  have h1 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hm1 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hle1 : c * t ≤ c := by simpa using hmin 1 h1
  have hlem1 : c * t ≤ -c := by simpa using hmin (-1) hm1
  have hlow : -|c| ≤ c * t := by
    have habs : |c * t| ≤ |c| := by
      rw [abs_mul]
      calc |c| * |t| ≤ |c| * 1 :=
            mul_le_mul_of_nonneg_left (abs_le.mpr ⟨ht.1, ht.2⟩) (abs_nonneg c)
        _ = |c| := mul_one _
    exact (abs_le.mp habs).1
  have hup : c * t ≤ -|c| := by
    rcases le_total 0 c with hc | hc
    · rw [abs_of_nonneg hc]; exact hlem1
    · rw [abs_of_nonpos hc]; simpa using hle1
  have habs_eq : c * t = -|c| := le_antisymm hup hlow
  have hnonpos : c * t ≤ 0 := by rw [habs_eq]; exact neg_nonpos.mpr (abs_nonneg c)
  refine ⟨habs_eq, hnonpos, ?_, ?_⟩
  · intro hc
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · rw [abs_of_neg hlt] at habs_eq
      have hct : c * t = c * 1 := by linarith
      have ht1 : t = 1 := mul_left_cancel₀ hc hct
      simp [ht1, Real.sign_of_neg hlt]
    · rw [abs_of_pos hgt] at habs_eq
      have hct : c * t = c * (-1) := by linarith
      have ht1 : t = -1 := mul_left_cancel₀ hc hct
      simp [ht1, Real.sign_of_pos hgt]
  · intro hc
    have h : |c| * |t| = |c| * 1 := by
      rw [← abs_mul, habs_eq, abs_neg, abs_abs, mul_one]
    exact mul_left_cancel₀ (abs_ne_zero.mpr hc) h

/-- **Minimiser of a linear form over the box.**
Let `c, u : EuclideanSpace ℝ ι` with `u` in the unit box and suppose that `u`
minimises the linear form `w ↦ ⟨c, w⟩` over the box. Then every coordinate `uᵢ`
minimises the scalar form `s ↦ cᵢ * s` over `[-1, 1]`, and consequently:
`uᵢ * cᵢ ≤ 0` for all `i`, and `uᵢ = -sign cᵢ`, `|uᵢ| = 1` whenever `cᵢ ≠ 0`.
This is the coordinatewise minimiser-of-a-linear-form-over-a-box
characterisation (Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 10
§10.3, Eq. (10.18), printed p. 438). -/
theorem linearMinimizer_bangBang {ι : Type*} [Fintype ι]
    (c u : EuclideanSpace ℝ ι) (hu : u ∈ unitBox ι)
    (hmin : ∀ w ∈ unitBox ι, inner ℝ c u ≤ inner ℝ c w) :
    (∀ i, u i * c i ≤ 0) ∧
      (∀ i, c i ≠ 0 → u i = -Real.sign (c i)) ∧
      (∀ i, c i ≠ 0 → |u i| = 1) := by
  classical
  have key : ∀ i, ∀ s ∈ Set.Icc (-1 : ℝ) 1, c i * u i ≤ c i * s := by
    intro i s hs
    let w : EuclideanSpace ℝ ι := u + (s - u i) • EuclideanSpace.single i (1 : ℝ)
    have hw : w ∈ unitBox ι := by
      intro j
      by_cases hji : j = i
      · rw [hji]
        have hwi : w i = s := by simp [w]
        rw [hwi]
        exact abs_le.mpr ⟨hs.1, hs.2⟩
      · have hwj : w j = u j := by simp [w, hji]
        rw [hwj]
        exact hu j
    have hinner : inner ℝ c w = inner ℝ c u + (s - u i) * c i := by
      simp only [w]
      rw [inner_add_right, inner_smul_right, EuclideanSpace.inner_single_right]
      simp
    have hle := hmin w hw
    rw [hinner] at hle
    nlinarith
  have hscalar : ∀ i, c i * u i = -|c i| ∧ c i * u i ≤ 0 ∧
      (c i ≠ 0 → u i = -Real.sign (c i)) ∧ (c i ≠ 0 → |u i| = 1) :=
    fun i => mul_minimizer_on_Icc (abs_le.mp (hu i)) (key i)
  refine ⟨fun i => ?_, fun i => (hscalar i).2.2.1, fun i => (hscalar i).2.2.2⟩
  rw [mul_comm]
  exact (hscalar i).2.1

section Complete

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Bang-bang structure of time-optimal controls.**
Consider the time-optimal problem for `ẋ = A x + B u` over the unit box
`U = {u | ∀ i, |u i| ≤ 1}`. If `u` is admissible (`u t` lies in the box) and
satisfies the Hamiltonian-minimisation clause of the maximum principle for the
time-optimal Hamiltonian, then along every `t ∈ [0, T]` the control is
componentwise opposite in sign to `Bᵀ λ(t)`:
`u(t)ᵢ · (Bᵀλ(t))ᵢ ≤ 0`, with `u(t)ᵢ = -sign ((Bᵀλ(t))ᵢ)` and
`|u(t)ᵢ| = 1` whenever `(Bᵀλ(t))ᵢ ≠ 0`. Thus time-optimal controls take values at
the vertices of the box (Sontag, *Mathematical Control Theory*, 2nd ed., 1998,
Ch. 10 §10.3, Theorem 49 and Theorem 51 / Eq. (10.19), printed pp. 436–438).
The zero-component case (a singular arc) is left unconstrained, consistent with
`sign 0 = 0`. -/
theorem timeOptimal_bangBang {ι : Type*} [Fintype ι]
    (A : E →L[ℝ] E) (B : EuclideanSpace ℝ ι →L[ℝ] E)
    (T : ℝ) (x : ℝ → E) (u : ℝ → EuclideanSpace ℝ ι) (p : ℝ → E)
    (hu : ∀ t ∈ Set.Icc 0 T, u t ∈ unitBox ι)
    (hmin : HamiltonianMinimizing (fun _ _ _ ↦ (1 : ℝ))
      (fun _ x u ↦ A x + B u) (unitBox ι) T x u p) :
    ∀ t ∈ Set.Icc 0 T,
      (∀ i, u t i * (B.adjoint (p t)) i ≤ 0) ∧
      (∀ i, (B.adjoint (p t)) i ≠ 0 → u t i = -Real.sign ((B.adjoint (p t)) i)) ∧
      (∀ i, (B.adjoint (p t)) i ≠ 0 → |u t i| = 1) := by
  intro t ht
  have hmin' :=
    (timeOptimal_hamiltonianMinimizing A B (unitBox ι) T x u p).mp hmin t ht
  have hinner : ∀ w ∈ unitBox ι,
      inner ℝ (B.adjoint (p t)) (u t) ≤ inner ℝ (B.adjoint (p t)) w := by
    intro w hw
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    exact hmin' w hw
  exact linearMinimizer_bangBang (B.adjoint (p t)) (u t) (hu t ht) hinner

end Complete

end BangBang
