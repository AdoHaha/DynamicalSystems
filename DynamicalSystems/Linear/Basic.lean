/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic

/-! # Linear time-invariant systems

This file sets up the bundled algebraic data of a linear time-invariant system.
Following Trentelman, Stoorvogel and Hautus, *Control Theory for Linear Systems*,
Section 3.1, a system `Σ` is described by

```
x'(t) = A x(t) + B u(t),
y(t)  = C x(t) + D u(t),
```

with `A : X →ₗ[𝕜] X` the *state map*, `B : U →ₗ[𝕜] X` the *input map*,
`C : X →ₗ[𝕜] Y` the *output map* and `D : U →ₗ[𝕜] Y` the *feedthrough map*.
The spaces `X`, `U` and `Y` are the state, input and output spaces respectively.
The linear maps live over a field `𝕜`; no finite-dimensionality hypothesis is
imposed at this algebraic level.

Besides the bundled system we provide the algebraic operations used throughout
the theory:

* `LinearSystem.dynamics` and `LinearSystem.readout`: the right-hand sides of
  the state and output equations;
* `LinearSystem.stateFeedback`: the state feedback `u = F x + v`, giving
  `A + B.comp F` (and, since the feedthrough is retained, `C + D.comp F`);
* `LinearSystem.changeState`, `LinearSystem.changeInput` and
  `LinearSystem.changeOutput`: coordinate changes on the state, input and
  output spaces.

## Main definitions

* `LinearSystem`: the bundled quadruple `(A, B, C, D)`.
* `LinearSystem.dynamics`, `LinearSystem.readout`: the state and output maps.
* `LinearSystem.stateFeedback`: state-feedback interconnection.
* `LinearSystem.changeState`, `LinearSystem.changeInput`, `LinearSystem.changeOutput`:
  coordinate changes.

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Section 3.1.
-/

@[expose] public section

/-- A linear time-invariant system `Σ = (A, B, C, D)` with state space `X`,
input space `U` and output space `Y`, encoded by the state equation
`x' = A x + B u` and the readout `y = C x + D u`.

Source: Trentelman–Stoorvogel–Hautus, Section 3.1, equations (3.1). -/
structure LinearSystem (𝕜 X U Y : Type*) [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup U] [Module 𝕜 U]
    [AddCommGroup Y] [Module 𝕜 Y] where
  /-- State map `A : X →ₗ[𝕜] X`. -/
  A : X →ₗ[𝕜] X
  /-- Input map `B : U →ₗ[𝕜] X`. -/
  B : U →ₗ[𝕜] X
  /-- Output map `C : X →ₗ[𝕜] Y`. -/
  C : X →ₗ[𝕜] Y
  /-- Feedthrough map `D : U →ₗ[𝕜] Y`. -/
  D : U →ₗ[𝕜] Y

namespace LinearSystem

variable {𝕜 X U Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-! ### Dynamics and readout -/

/-- The state dynamics `x ↦ A x + B u` of an LTI system, i.e. the right-hand
side of the state equation `x' = A x + B u`. -/
def dynamics (sys : LinearSystem 𝕜 X U Y) (x : X) (u : U) : X :=
  sys.A x + sys.B u

/-- Evaluation lemma for `LinearSystem.dynamics`. -/
@[simp]
theorem dynamics_apply (sys : LinearSystem 𝕜 X U Y) (x : X) (u : U) :
    sys.dynamics x u = sys.A x + sys.B u := rfl

/-- With zero input the dynamics reduces to the state map `A`. -/
@[simp]
theorem dynamics_zero_input (sys : LinearSystem 𝕜 X U Y) (x : X) :
    sys.dynamics x 0 = sys.A x := by
  simp [dynamics]

/-- From the origin the dynamics is the input map `B` applied to the input. -/
@[simp]
theorem dynamics_zero_state (sys : LinearSystem 𝕜 X U Y) (u : U) :
    sys.dynamics 0 u = sys.B u := by
  simp [dynamics]

/-- The dynamics is additive in the pair `(x, u)`. -/
theorem dynamics_add (sys : LinearSystem 𝕜 X U Y) (x₁ x₂ : X) (u₁ u₂ : U) :
    sys.dynamics (x₁ + x₂) (u₁ + u₂) = sys.dynamics x₁ u₁ + sys.dynamics x₂ u₂ := by
  simp only [dynamics, map_add]
  ac_rfl

/-- The dynamics is homogeneous in the pair `(x, u)`. -/
theorem dynamics_smul (sys : LinearSystem 𝕜 X U Y) (c : 𝕜) (x : X) (u : U) :
    sys.dynamics (c • x) (c • u) = c • sys.dynamics x u := by
  simp only [dynamics, map_smul, smul_add]

/-- The readout `y = C x + D u` of an LTI system. -/
def readout (sys : LinearSystem 𝕜 X U Y) (x : X) (u : U) : Y :=
  sys.C x + sys.D u

/-- Evaluation lemma for `LinearSystem.readout`. -/
@[simp]
theorem readout_apply (sys : LinearSystem 𝕜 X U Y) (x : X) (u : U) :
    sys.readout x u = sys.C x + sys.D u := rfl

/-- With zero input the readout reduces to the output map `C`. -/
@[simp]
theorem readout_zero_input (sys : LinearSystem 𝕜 X U Y) (x : X) :
    sys.readout x 0 = sys.C x := by
  simp [readout]

/-- At the origin the readout is the feedthrough map `D` applied to the input. -/
@[simp]
theorem readout_zero_state (sys : LinearSystem 𝕜 X U Y) (u : U) :
    sys.readout 0 u = sys.D u := by
  simp [readout]

/-- The readout is additive in the pair `(x, u)`. -/
theorem readout_add (sys : LinearSystem 𝕜 X U Y) (x₁ x₂ : X) (u₁ u₂ : U) :
    sys.readout (x₁ + x₂) (u₁ + u₂) = sys.readout x₁ u₁ + sys.readout x₂ u₂ := by
  simp only [readout, map_add]
  ac_rfl

/-- The readout is homogeneous in the pair `(x, u)`. -/
theorem readout_smul (sys : LinearSystem 𝕜 X U Y) (c : 𝕜) (x : X) (u : U) :
    sys.readout (c • x) (c • u) = c • sys.readout x u := by
  simp only [readout, map_smul, smul_add]

/-! ### State feedback

State feedback `u = F x + v` substitutes the input by `F x + v`, where `v` is
the new external input. The closed-loop system has state map `A + B.comp F` and,
because the feedthrough term is kept, output map `C + D.comp F`. -/

/-- State feedback `u = F x + v`. The resulting system has state map
`A + B.comp F` and output map `C + D.comp F`, while `B` and `D` are unchanged. -/
def stateFeedback (sys : LinearSystem 𝕜 X U Y) (F : X →ₗ[𝕜] U) :
    LinearSystem 𝕜 X U Y where
  A := sys.A + sys.B.comp F
  B := sys.B
  C := sys.C + sys.D.comp F
  D := sys.D

@[simp]
theorem stateFeedback_A (sys : LinearSystem 𝕜 X U Y) (F : X →ₗ[𝕜] U) :
    (sys.stateFeedback F).A = sys.A + sys.B.comp F := rfl

@[simp]
theorem stateFeedback_B (sys : LinearSystem 𝕜 X U Y) (F : X →ₗ[𝕜] U) :
    (sys.stateFeedback F).B = sys.B := rfl

@[simp]
theorem stateFeedback_C (sys : LinearSystem 𝕜 X U Y) (F : X →ₗ[𝕜] U) :
    (sys.stateFeedback F).C = sys.C + sys.D.comp F := rfl

@[simp]
theorem stateFeedback_D (sys : LinearSystem 𝕜 X U Y) (F : X →ₗ[𝕜] U) :
    (sys.stateFeedback F).D = sys.D := rfl

/-- The closed-loop dynamics of the state-feedback system is the open-loop
dynamics evaluated at the fed-back input `F x + v`. -/
theorem stateFeedback_dynamics (sys : LinearSystem 𝕜 X U Y) (F : X →ₗ[𝕜] U)
    (x : X) (v : U) :
    (sys.stateFeedback F).dynamics x v = sys.dynamics x (F x + v) := by
  simp only [dynamics, stateFeedback, LinearMap.add_apply, LinearMap.comp_apply, map_add]
  ac_rfl

/-- The closed-loop readout of the state-feedback system is the open-loop
readout evaluated at the fed-back input `F x + v`. -/
theorem stateFeedback_readout (sys : LinearSystem 𝕜 X U Y) (F : X →ₗ[𝕜] U)
    (x : X) (v : U) :
    (sys.stateFeedback F).readout x v = sys.readout x (F x + v) := by
  simp only [readout, stateFeedback, LinearMap.add_apply, LinearMap.comp_apply, map_add]
  ac_rfl

/-! ### Coordinate changes -/

variable {X' U' Y' : Type*}
variable [AddCommGroup X'] [Module 𝕜 X']
variable [AddCommGroup U'] [Module 𝕜 U']
variable [AddCommGroup Y'] [Module 𝕜 Y']

/-- A change of state coordinates `x = e x̄`, with `e : X' ≃ₗ[𝕜] X`. The new
state map is `e⁻¹ ∘ A ∘ e`, the new input map is `e⁻¹ ∘ B` and the new output
map is `C ∘ e`; the feedthrough map `D` is unchanged. -/
def changeState (sys : LinearSystem 𝕜 X U Y) (e : X' ≃ₗ[𝕜] X) :
    LinearSystem 𝕜 X' U Y where
  A := e.symm.toLinearMap.comp (sys.A.comp e.toLinearMap)
  B := e.symm.toLinearMap.comp sys.B
  C := sys.C.comp e.toLinearMap
  D := sys.D

@[simp]
theorem changeState_A (sys : LinearSystem 𝕜 X U Y) (e : X' ≃ₗ[𝕜] X) :
    (sys.changeState e).A = e.symm.toLinearMap.comp (sys.A.comp e.toLinearMap) := rfl

@[simp]
theorem changeState_B (sys : LinearSystem 𝕜 X U Y) (e : X' ≃ₗ[𝕜] X) :
    (sys.changeState e).B = e.symm.toLinearMap.comp sys.B := rfl

@[simp]
theorem changeState_C (sys : LinearSystem 𝕜 X U Y) (e : X' ≃ₗ[𝕜] X) :
    (sys.changeState e).C = sys.C.comp e.toLinearMap := rfl

@[simp]
theorem changeState_D (sys : LinearSystem 𝕜 X U Y) (e : X' ≃ₗ[𝕜] X) :
    (sys.changeState e).D = sys.D := rfl

/-- The dynamics in the new state coordinates is the old dynamics at `e x`,
transported back by `e⁻¹`. -/
theorem changeState_dynamics (sys : LinearSystem 𝕜 X U Y) (e : X' ≃ₗ[𝕜] X)
    (x : X') (u : U) :
    (sys.changeState e).dynamics x u = e.symm (sys.dynamics (e x) u) := by
  simp only [dynamics, changeState, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    map_add]

/-- The readout in the new state coordinates is the old readout at `e x`. -/
theorem changeState_readout (sys : LinearSystem 𝕜 X U Y) (e : X' ≃ₗ[𝕜] X)
    (x : X') (u : U) :
    (sys.changeState e).readout x u = sys.readout (e x) u := by
  simp only [readout, changeState, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]

/-- A change of input coordinates `u = e û`. The new input map is `B ∘ e` and
the new feedthrough map is `D ∘ e`; the state and output maps are unchanged. -/
def changeInput (sys : LinearSystem 𝕜 X U Y) (e : U' ≃ₗ[𝕜] U) :
    LinearSystem 𝕜 X U' Y where
  A := sys.A
  B := sys.B.comp e.toLinearMap
  C := sys.C
  D := sys.D.comp e.toLinearMap

@[simp]
theorem changeInput_A (sys : LinearSystem 𝕜 X U Y) (e : U' ≃ₗ[𝕜] U) :
    (sys.changeInput e).A = sys.A := rfl

@[simp]
theorem changeInput_B (sys : LinearSystem 𝕜 X U Y) (e : U' ≃ₗ[𝕜] U) :
    (sys.changeInput e).B = sys.B.comp e.toLinearMap := rfl

@[simp]
theorem changeInput_C (sys : LinearSystem 𝕜 X U Y) (e : U' ≃ₗ[𝕜] U) :
    (sys.changeInput e).C = sys.C := rfl

@[simp]
theorem changeInput_D (sys : LinearSystem 𝕜 X U Y) (e : U' ≃ₗ[𝕜] U) :
    (sys.changeInput e).D = sys.D.comp e.toLinearMap := rfl

/-- The dynamics in the new input coordinates is the old dynamics at the
transported input `e u`. -/
theorem changeInput_dynamics (sys : LinearSystem 𝕜 X U Y) (e : U' ≃ₗ[𝕜] U)
    (x : X) (u : U') :
    (sys.changeInput e).dynamics x u = sys.dynamics x (e u) := by
  simp only [dynamics, changeInput, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]

/-- The readout in the new input coordinates is the old readout at the
transported input `e u`. -/
theorem changeInput_readout (sys : LinearSystem 𝕜 X U Y) (e : U' ≃ₗ[𝕜] U)
    (x : X) (u : U') :
    (sys.changeInput e).readout x u = sys.readout x (e u) := by
  simp only [readout, changeInput, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]

/-- A change of output coordinates `ȳ = e y`. The new output map is
`e ∘ C` and the new feedthrough map is `e ∘ D`; the state and input maps are
unchanged. -/
def changeOutput (sys : LinearSystem 𝕜 X U Y) (e : Y ≃ₗ[𝕜] Y') :
    LinearSystem 𝕜 X U Y' where
  A := sys.A
  B := sys.B
  C := e.toLinearMap.comp sys.C
  D := e.toLinearMap.comp sys.D

@[simp]
theorem changeOutput_A (sys : LinearSystem 𝕜 X U Y) (e : Y ≃ₗ[𝕜] Y') :
    (sys.changeOutput e).A = sys.A := rfl

@[simp]
theorem changeOutput_B (sys : LinearSystem 𝕜 X U Y) (e : Y ≃ₗ[𝕜] Y') :
    (sys.changeOutput e).B = sys.B := rfl

@[simp]
theorem changeOutput_C (sys : LinearSystem 𝕜 X U Y) (e : Y ≃ₗ[𝕜] Y') :
    (sys.changeOutput e).C = e.toLinearMap.comp sys.C := rfl

@[simp]
theorem changeOutput_D (sys : LinearSystem 𝕜 X U Y) (e : Y ≃ₗ[𝕜] Y') :
    (sys.changeOutput e).D = e.toLinearMap.comp sys.D := rfl

/-- The readout in the new output coordinates is the transported old readout. -/
theorem changeOutput_readout (sys : LinearSystem 𝕜 X U Y) (e : Y ≃ₗ[𝕜] Y')
    (x : X) (u : U) :
    (sys.changeOutput e).readout x u = e (sys.readout x u) := by
  simp only [readout, changeOutput, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    map_add]

end LinearSystem
