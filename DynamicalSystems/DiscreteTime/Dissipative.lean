/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Basic.Real.Basic

/-! # Discrete dissipativity: the pointwise storage inequality

This file is the foundational home of the *discrete, pointwise* dissipativity
predicate used throughout the discrete-time control library.  For a system
`x⁺ = f x u` with supply rate `s : X → U → ℝ`, a storage function `lam : X → ℝ`
witnesses dissipativity when

`lam (f x u) - lam x ≤ s x u` for all states `x` and inputs `u`.

This is the discrete state-space storage condition (2.35) of Rawlings, Mayne and
Diehl, *Model Predictive Control: Theory, Computation, and Design*, 2nd ed., 2019,
Definition 2.53, §2.8.2 (printed p. 156).  It is deliberately kept apart from
`InputOutput.Dissipative.IsDissipativeWith`, which is the continuous-time `L^p`
*integral* supply inequality, and from
`Control.ControlLyapunov.IsControlLyapunovFunction`, which is a continuous,
control-affine object.  The definition is purely order-theoretic on `ℝ`; no
DynamicalSystems import is required.

The economic-MPC consumer `DynamicalSystems.Control.MPC.Economic` imports this
module and uses `IsDissipative` for the storage inequality behind the rotated
stage cost, so `DiscreteTime` no longer has to reach into `Control.MPC` for it.

## Main definitions

* `IsDissipative`: the discrete storage inequality
  `lam (f x u) - lam x ≤ s x u` of Definition 2.53 (printed p. 156).
-/

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
