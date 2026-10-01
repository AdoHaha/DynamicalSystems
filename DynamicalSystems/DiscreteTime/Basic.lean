/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Function.Iterate

/-! # Discrete-time core primitives

This file sets up the basic vocabulary for discrete-time dynamical systems, in the
form used throughout I. D. Landau, R. Lozano, M'Saad and A. Karimi, *Adaptive
Control: Algorithms, Analysis and Applications*, 2nd ed., Springer 2011.

A discrete-time system is a self-map `f : E → E` of a state space `E`. Its forward
orbit is Mathlib's `n`-fold iterate `f^[n]`, exposed as `discreteFlow f n`. The file
also records the notion of a forward-invariant set and of an equilibrium point.

## Main definitions

* `discreteFlow f n`: the `n`-th iterate of `f`, i.e. the forward orbit of the system.
* `IsForwardInvariant f S`: the set `S` is mapped into itself by `f`.
* `IsDiscreteEquilibrium f x`: `x` is a fixed point of `f`.

## Main results

* `discreteFlow_zero`, `discreteFlow_succ`, `discreteFlow_add`: the iterate is a
  monoid action of `(ℕ, +)` on `E`, stated in terms of `Function.iterate`.
* `IsForwardInvariant.iterate`: forward invariance is preserved by every iterate.
-/

@[expose] public section

/-- The forward orbit of the discrete-time system `f`: the `n`-fold iterate. -/
def discreteFlow {E : Type*} (f : E → E) : ℕ → E → E := fun n x ↦ f^[n] x

/-- A set is forward invariant under `f`. -/
def IsForwardInvariant {E : Type*} (f : E → E) (S : Set E) : Prop := Set.MapsTo f S S

/-- `x` is an equilibrium (fixed point) of the discrete-time system `f`. -/
def IsDiscreteEquilibrium {E : Type*} (f : E → E) (x : E) : Prop := f x = x

/-- The zeroth iterate of a discrete-time system is the identity. -/
@[simp]
theorem discreteFlow_zero {E : Type*} (f : E → E) : discreteFlow f 0 = id := by
  funext x
  simp only [discreteFlow, Function.iterate_zero, id_eq]

/-- The successor iterate of a discrete-time system is `f` applied after the `n`-th
iterate. -/
theorem discreteFlow_succ {E : Type*} (f : E → E) (n : ℕ) :
    discreteFlow f (n + 1) = f ∘ discreteFlow f n := by
  funext x
  simp only [discreteFlow, Function.iterate_succ_apply', Function.comp_apply]

/-- The iterate of a discrete-time system is additive in the number of steps. -/
theorem discreteFlow_add {E : Type*} (f : E → E) (m n : ℕ) :
    discreteFlow f (m + n) = discreteFlow f m ∘ discreteFlow f n := by
  funext x
  simp only [discreteFlow, Function.iterate_add_apply, Function.comp_apply]

/-- A forward-invariant set is invariant under every iterate of the system. -/
theorem IsForwardInvariant.iterate {E : Type*} {f : E → E} {S : Set E}
    (h : IsForwardInvariant f S) (n : ℕ) : IsForwardInvariant (discreteFlow f n) S :=
  (show Set.MapsTo f S S from h).iterate n
