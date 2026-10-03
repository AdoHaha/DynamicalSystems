/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.FiniteHorizon
public import DynamicalSystems.OptimalControl.ValueFunction

/-! # The receding-horizon (model predictive control) law

This file defines the model predictive control law for a generic finite-horizon
optimal control problem and its one-step closed loop.

Given a finite-horizon problem `prob` and a state `x`, MPC selects an optimal
admissible input sequence of `prob` at `x` and applies its first control to the
plant.  Because Mathlib has no continuous `argmin`, the optimal sequence is
obtained with `Classical.choose` from the existence hypothesis on `IsOptimalInput`.
The resulting `mpcLaw` therefore depends on the chosen minimizer; for a state at
which the optimal sequence is non-unique the controller picks one element of the
minimizer set, matching the set-valued convention of the receding-horizon law
(Rawlings–Mayne–Diehl 2019, Ch. 2 §2.2, printed p. 99).

## Main definitions

* `mpcLaw`: the first control of a `Classical.choose`-selected optimal input
  sequence, i.e. the receding-horizon control `κ_N x = u⁰(0; x)`.
* `mpcClosedLoop`: the one-step closed loop `x⁺ = f x (κ_N x)`.
* `IsTerminalCLF`: the discrete terminal control-Lyapunov condition of
  Assumption 2.14(a), a fresh predicate kept apart from the continuous,
  control-affine `IsControlLyapunovFunction`.

## Main results

* `mpcLaw_firstControlAdmissible`: the chosen first control is admissible, i.e.
  `x` lies in the state set and `mpcLaw prob x hN h` lies in the input set.
* `recursiveFeasibility`: recursive feasibility — the successor state of the MPC
  closed loop stays feasible when the terminal set is control invariant and
  contained in the state set (the standing `Xf ⊆ X` assumption).
* `recursiveFeasibility_of_isTerminalCLF`: recursive feasibility from the discrete
  terminal control-Lyapunov condition of Assumption 2.14(a).
* `recursiveFeasibility_hXf_of_terminalLaw`: the per-state terminal-step hypothesis
  consumed by `recursiveFeasibility`, from the invariance package
  `Set.MapsTo (fun x ↦ f x (κf x)) Xf Xf`, `Set.MapsTo κf Xf U`, `Xf ⊆ X`.
* `IsTerminalCLF.invariance_step`: the per-state terminal-step witness extracted
  from `IsTerminalCLF` and `Xf ⊆ X`.

## Correction relative to the task statement

The raw statement of recursive feasibility with only the existence of an optimal
input can fail: the tail of an optimal sequence has one control fewer, so it
witnesses feasibility of the *tail* problem, not of the horizon-`N` problem, and
an extra terminal step may be needed to close the horizon.  The statement below
therefore carries the book's terminal-control-invariance condition
(Definition 2.9(b) and Assumption 2.14(a), written without the decrease clause,
which feasibility does not need) and the standing inclusion `Xf ⊆ X` of
Assumption 2.2/2.3.  These are hypotheses of the statement, not of the proof
only; the docstring of `recursiveFeasibility` records the details.
-/

@[expose] public section

variable {X U : Type*}

/-- The receding-horizon (model predictive control) control law: the first control
of an optimal admissible input sequence for `prob` at `x`
(Rawlings–Mayne–Diehl 2019, Ch. 2 §2.2, printed p. 99).

The optimal sequence is extracted from the existence hypothesis `h` with
`Classical.choose`.  Mathlib has no continuous `argmin` (its `argmin` is only
defined for well-founded orders such as `ℕ`), so `Classical.choose` on the
`IsMinOn`-minimizer set is the intended mechanism; by
`isOptimalInput_iff_isMinOn` the predicate `IsOptimalInput prob x` is exactly
minimality of `finiteHorizonTotalCost prob x` over the admissible sequences, and
a non-unique minimizer is resolved by choosing one representative. -/
noncomputable def mpcLaw (prob : FiniteHorizonProblem X U) (x : X)
    (hN : 0 < prob.horizon)
    (h : ∃ u : Fin prob.horizon → U, IsOptimalInput prob x u) : U :=
  (Classical.choose h) ⟨0, hN⟩

/-- The one-step MPC closed loop from `x`: apply the receding-horizon control
`mpcLaw prob x hN h` to the dynamics `prob.f`, i.e. `x⁺ = f x (κ_N x)`
(Rawlings–Mayne–Diehl 2019, Ch. 2 §2.2, printed p. 99). -/
noncomputable def mpcClosedLoop (prob : FiniteHorizonProblem X U) (x : X)
    (hN : 0 < prob.horizon)
    (h : ∃ u : Fin prob.horizon → U, IsOptimalInput prob x u) : X :=
  prob.f x (mpcLaw prob x hN h)

/-- The receding-horizon control selected at `x` is admissible: the current state
lies in the state set and the chosen first control lies in the input set.  This is
the `k = 0` clause of the admissibility of the chosen optimal sequence
(Rawlings–Mayne–Diehl 2019, Ch. 2 §2.2, printed pp. 95–99). -/
theorem mpcLaw_firstControlAdmissible (prob : FiniteHorizonProblem X U) (x : X)
    (hN : 0 < prob.horizon)
    (h : ∃ u : Fin prob.horizon → U, IsOptimalInput prob x u) :
    x ∈ prob.stateSet ∧ mpcLaw prob x hN h ∈ prob.inputSet := by
  have hopt : IsOptimalInput prob x (Classical.choose h) := Classical.choose_spec h
  have hadm : FiniteHorizonAdmissible prob x (Classical.choose h) := hopt.1
  have hk := hadm.1 ⟨0, hN⟩
  rw [Fin.castSucc_mk, Fin.mk_zero, finiteHorizonRollout_zero] at hk
  unfold mpcLaw
  exact hk

/-- The discrete terminal control-Lyapunov condition (Rawlings–Mayne–Diehl 2019,
Ch. 2 §2.4.2, Assumption 2.14(a); descent property at printed p. 117 / PDF p. 160):
for every state
`x` of the terminal set `Xf` there is an admissible input `u ∈ Uset` whose
successor stays in `Xf` and whose terminal-cost decrease is at least the stage
cost, `Vf (f x u) - Vf x ≤ -ℓ x u`.

This is a genuinely discrete-time object and must not be confused with the
continuous, control-affine `IsControlLyapunovFunction` of
`DynamicalSystems.Control.ControlLyapunov`, which bounds the Lie derivative along
`f(x) + u·g(x)` rather than a one-step difference. -/
def IsTerminalCLF (f : X → U → X) (ℓ : X → U → ℝ) (Vf : X → ℝ)
    (Xf : Set X) (Uset : Set U) : Prop :=
  ∀ x ∈ Xf, ∃ u ∈ Uset, f x u ∈ Xf ∧ Vf (f x u) - Vf x ≤ -ℓ x u

/-- Recursive feasibility of the receding-horizon law (Rawlings–Mayne–Diehl 2019,
Ch. 2 §2.3, printed pp. 111–112 / PDF pp. 154–155): if `prob` is
feasible at `x` with an optimal input `u`, then the successor state
`x⁺ = f x (u 0)` of the MPC closed loop is again feasible for `prob`.

After the first optimal control the remaining controls `Fin.tail u` are admissible
for the horizon-one-shorter tail problem, and a single terminal step
`w` that keeps the terminal state inside `Xf` restores the original horizon.  The
invariance is expressed by `hXf`, which packages Definition 2.9(b) (for every
`z ∈ Xf` there is an admissible `w` with `f z w ∈ Xf`) together with the standing
assumption `Xf ⊆ X` needed because the old terminal state becomes an interior
state of the extended horizon.

Note the output type: recursive feasibility yields `FiniteHorizonFeasible prob x⁺`, i.e. the
existence of an *admissible* input sequence at `x⁺`.  It does not yield
`∃ u, IsOptimalInput prob x⁺ u`, and hence does not by itself let `mpcClosedLoop` take another
step; stepping the closed loop additionally requires the existence of an optimal (minimizer)
input — a Weierstrass-type compactness hypothesis (the admissible set is compact and the cost
is continuous), which is a separate assumption rather than a consequence of recursive
feasibility.

## Correction

The statement intended in the task, which assumed only `hN` and `h`, is not
derivable: `Fin.tail u` has length `prob.horizon - 1`, so it witnesses feasibility
of the tail problem, and without terminal control invariance and `Xf ⊆ X` there
are counterexamples (e.g. `f x u = x + 1`, `Xf = {0}`, `Xs = Us = ℝ`, horizon `2`,
`x = -2`: the successor `-1` is infeasible).  The two book hypotheses are therefore
explicit here rather than implicit; no conclusion was weakened. -/
theorem recursiveFeasibility (prob : FiniteHorizonProblem X U) (x : X)
    (hN : 0 < prob.horizon)
    (h : ∃ u : Fin prob.horizon → U, IsOptimalInput prob x u)
    (hXf : ∀ z ∈ prob.terminalSet, z ∈ prob.stateSet ∧
      ∃ w ∈ prob.inputSet, prob.f z w ∈ prob.terminalSet) :
    FiniteHorizonFeasible prob (mpcClosedLoop prob x hN h) := by
  obtain ⟨f, ℓ, Vf, N, Xs, Us, Xf⟩ := prob
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN)
  let u := Classical.choose h
  have hu : IsOptimalInput ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u := Classical.choose_spec h
  have hadm : FiniteHorizonAdmissible ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u := hu.1
  have hterm : finiteHorizonRollout ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u (Fin.last (M + 1)) ∈ Xf :=
    hadm.2
  obtain ⟨htermXs, hw⟩ := hXf _ hterm
  let w := Classical.choose hw
  have hwU : w ∈ Us := (Classical.choose_spec hw).1
  have hwXf : f (finiteHorizonRollout ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u
      (Fin.last (M + 1))) w ∈ Xf := (Classical.choose_spec hw).2
  have hmcl : mpcClosedLoop ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x hN h = f x (u 0) := by
    simp only [mpcClosedLoop, mpcLaw]
    rfl
  rw [hmcl]
  exact ⟨Fin.snoc (Fin.tail u) w,
    finiteHorizonAdmissible_snoc x u w hadm htermXs hwU hwXf⟩

/-- The per-state terminal-step hypothesis consumed by `recursiveFeasibility`,
obtained from a terminal controller `κf` that leaves the terminal set invariant and
admissible, together with the standing inclusion `Xf ⊆ X`
(Rawlings–Mayne–Diehl 2019, Ch. 2 §2.4.2, Definition 2.9 and Assumption 2.14(a),
printed pp. 111–112 / PDF pp. 154–155): if
`Set.MapsTo (fun x ↦ f x (κf x)) Xf Xf`, `Set.MapsTo κf Xf U` and `Xf ⊆ X`, then
every `z ∈ Xf` lies in the state set and admits an admissible `w` with
`f z w ∈ Xf`. -/
theorem recursiveFeasibility_hXf_of_terminalLaw (prob : FiniteHorizonProblem X U) (κf : X → U)
    (hXf : Set.MapsTo (fun x ↦ prob.f x (κf x)) prob.terminalSet prob.terminalSet)
    (hU : Set.MapsTo κf prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet) :
    ∀ z ∈ prob.terminalSet, z ∈ prob.stateSet ∧
      ∃ w ∈ prob.inputSet, prob.f z w ∈ prob.terminalSet :=
  fun z hz => ⟨hsub hz, ⟨κf z, hU hz, hXf hz⟩⟩

/-- The per-state terminal-step witness extracted from the discrete terminal
control-Lyapunov condition `IsTerminalCLF` and the inclusion `Xf ⊆ X`.  The decrease
clause of `IsTerminalCLF` is not needed for feasibility, so the witness only retains
the input-admissibility and terminal-invariance parts. -/
theorem IsTerminalCLF.invariance_step {f : X → U → X} {ℓ : X → U → ℝ} {Vf : X → ℝ}
    {Xf : Set X} {Uset : Set U} {Xs : Set X}
    (hclf : IsTerminalCLF f ℓ Vf Xf Uset) (hsub : Xf ⊆ Xs) :
    ∀ z ∈ Xf, z ∈ Xs ∧ ∃ w ∈ Uset, f z w ∈ Xf :=
  fun z hz => ⟨hsub hz, by obtain ⟨w, hwU, hwXf, -⟩ := hclf z hz; exact ⟨w, hwU, hwXf⟩⟩

/-- Recursive feasibility of the MPC closed loop from the discrete terminal
control-Lyapunov condition: if the terminal set satisfies `IsTerminalCLF` and is
contained in the state set, then the successor state of the receding-horizon law is
again feasible (Rawlings–Mayne–Diehl 2019, Ch. 2 §2.3, printed pp. 111–112 /
PDF pp. 154–155). -/
theorem recursiveFeasibility_of_isTerminalCLF (prob : FiniteHorizonProblem X U) (x : X)
    (hN : 0 < prob.horizon)
    (h : ∃ u : Fin prob.horizon → U, IsOptimalInput prob x u)
    (hclf : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet) :
    FiniteHorizonFeasible prob (mpcClosedLoop prob x hN h) :=
  recursiveFeasibility prob x hN h (IsTerminalCLF.invariance_step hclf hsub)
