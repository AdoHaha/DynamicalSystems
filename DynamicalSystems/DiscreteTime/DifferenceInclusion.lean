/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Data.Set.Basic

/-! # Difference inclusions and additive uncertainty

This file is the foundational home of the discrete-time *difference-inclusion*
vocabulary of Rawlings, Mayne and Diehl, *Model Predictive Control: Theory,
Computation, and Design*, 2nd ed., 2019, §3.1.5 (printed p. 203 / PDF p. 251).
An uncertain discrete-time system is written as the set-valued transition
`x⁺ ∈ F x u` with `F : X → U → Set X` (`DifferenceInclusion`), collecting every
admissible successor of the pair `(x, u)`.  The bounded additive-uncertainty model
`F x u = {f x u + w | w ∈ W}` is `additiveInclusion`, and
`mem_additiveInclusion_iff` unwinds membership in it to a disturbance witness.

The vocabulary is generic: only `Set` and an addition on the state space are
required, so the module stays independent of any control application in
`Control.*`.  The additive model is stated over an arbitrary `[Add X]` rather than
over a normed group, because the disturbance is only ever added to `f x u`; the
metric structure is introduced by consumers such as
`DynamicalSystems.Control.MPC.Robust`, which imports this module for its robust-MPC
nominal-robustness results and keeps the trajectory-level robust-admissibility
predicate `RobustlyAdmissible` (it is stated over state and input constraint sets
and a trajectory `ℕ → X`, so it belongs with the MPC robustness theory).

## Main definitions

* `DifferenceInclusion`: the uncertain dynamics `x⁺ ∈ F x u` of §3.1.5
  (printed p. 203 / PDF p. 251).
* `additiveInclusion`: the additive uncertainty model `F x u = {f x u + w | w ∈ W}`.

## Main results

* `mem_additiveInclusion_iff`: membership in `additiveInclusion` unwinds to a
  disturbance witness.
-/

@[expose] public section

variable {X U : Type*}

/-- The uncertain dynamics as a set-valued map `F : X → U → Set X`, writing
`x⁺ ∈ F x u` for the difference inclusion of Rawlings–Mayne–Diehl 2019, 2nd ed.,
§3.1.5 (printed p. 203 / PDF p. 251).  The set `F x u` collects *every* admissible
successor of the pair `(x, u)`; a deterministic plant `x⁺ = f x u` is the special
case `F x u = {f x u}`, and the additive uncertainty model of §3.2 (printed
p. 207 / PDF p. 255) is `F x u = {f x u + w | w ∈ W}` (see `additiveInclusion`). -/
def DifferenceInclusion (X U : Type*) : Type _ := X → U → Set X

/-- The additive uncertainty model of Rawlings–Mayne–Diehl 2019, 2nd ed., §3.1.5
(printed p. 203 / PDF p. 251): given the nominal dynamics `f` and a disturbance set
`W`, the successor set is `F x u = {f x u + w | w ∈ W}`, i.e.
`additiveInclusion f W x u`.  Only an addition on the state space is required. -/
def additiveInclusion [Add X] (f : X → U → X) (W : Set X) : DifferenceInclusion X U :=
  fun x u ↦ (fun w ↦ f x u + w) '' W

/-- Membership in the additive inclusion unwinds to a disturbance witness: `y` is an
admissible successor of `(x, u)` under `additiveInclusion f W` exactly when
`y = f x u + w` for some `w ∈ W`. -/
theorem mem_additiveInclusion_iff [Add X] {f : X → U → X} {W : Set X} {x : X} {u : U}
    {y : X} : y ∈ additiveInclusion f W x u ↔ ∃ w ∈ W, f x u + w = y := Iff.rfl
