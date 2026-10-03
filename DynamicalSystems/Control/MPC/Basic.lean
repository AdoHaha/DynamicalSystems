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

## Main results

* `mpcLaw_firstControlAdmissible`: the chosen first control is admissible, i.e.
  `x` lies in the state set and `mpcLaw prob x hN h` lies in the input set.
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
