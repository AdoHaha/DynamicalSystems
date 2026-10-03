/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Kalman
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # First-order local surjectivity via linearization

This file formalises an open-mapping / local-surjectivity corollary of the
implicit-mapping theorem for continuous-time control systems `ẋ = f x u`,
following Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional
Systems*, 2nd ed., 1998, Ch. 3 §3.7 (printed pp. 122–128; Definition 3.7.5,
Remark 3.7.6 and Theorem 7).  This is the linear precursor of the nonlinear
(Lie-theoretic) controllability theory of Chapter 4.

For a control system the **linearization** at the origin is the pair `(A, B)` of
Fréchet derivatives

`A = ∂ₓf(0,0) : X →L[ℝ] X`,   `B = ∂ᵤf(0,0) : U →L[ℝ] X`,

see `linearizationA` and `linearizationB`.  The pair is **controllable** when the
Kalman rank condition `rank [B AB ⋯ A^{n-1}B] = n` holds, equivalently when the
Kalman controllability map `LinearMap.kalmanControllabilityMap A B n` is
surjective (`LinearMap.isControllable_iff_surjective_kalmanControllabilityMap`).

The formalised result is the purely functional-analytic open-mapping step: if the
end-point map `Φ` is strictly differentiable with surjective derivative, then `Φ`
maps a neighbourhood of the base point onto a neighbourhood of its image.  Applied
to a control system this yields *joint local surjectivity*: every target `y`
sufficiently close to `Φ p` is attained as `Φ(z, ν) = y` for some `(z, ν)` close
to `p`.  It is **not** Sontag's local controllability: it neither says that the
same control steers every nearby initial state to `0`, nor that the trajectory
stays within a prescribed neighbourhood (no excursion bound).

The differentiability of the end-point map and the identification of its control
derivative with the Kalman map are the regularity conclusions of Sontag
Theorem 1 (p. 57), which are not formalised here; they enter
`localSurjectivity_of_controllable_linearization` as hypotheses on the end-point
map, exactly as in Sontag's proof.  Sontag's own proof uses the implicit-mapping
theorem to obtain a *uniform* selection `j(z, y)`; that uniform selection is not
formalised here.

## Control constraints

Only the unconstrained first-order problem is treated: controls are parameterised
by finitely many free values `Fin n → U` (the piecewise-constant controls used to
state the Kalman rank condition), so no control constraint set is imposed.  This
is the scope of Sontag §3.7; constrained versions belong to Chapter 4.

## Main definitions

* `linearizationA`, `linearizationB`: the Fréchet derivatives of the vector field
  with respect to state and control at the origin.
* `linearizationControllable`: controllability of the linearized pair.
* `LocallyOnto`: local surjectivity (openness at a point) of a map, stated
  through an end-point map.

## Main results

* `linearizationA_def`, `linearizationB_def`: the derivatives are definitionally
  the ones displayed above.
* `linearizationControllable_iff`: unfolding of the controllability predicate.
* `localSurjectivity_of_controllable_linearization`: a controllable linearization
  implies local surjectivity of the end-point map at the origin; the conclusion is
  joint local surjectivity (every nearby target `y` has some nearby `(z, ν)` with
  `Φ(z, ν) = y`), not uniform control from every nearby initial state.

## References

* E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional
  Systems*, 2nd ed., Springer, 1998, Ch. 3 §3.7, printed pp. 122–128.
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {X U : Type*}

/-! ### The linearization of a control system -/

section LinearizationA

variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup U]

/-- The state linearization `A = ∂ₓf(0,0) : X →L[ℝ] X` of the control system
`ẋ = f x u` at the origin, i.e. the Fréchet derivative of `x ↦ f x 0` at `0`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 3 §3.7, the
linearization appearing in Theorem 7). -/
noncomputable def linearizationA (f : X → U → X) : X →L[ℝ] X :=
  fderiv ℝ (fun x ↦ f x 0) 0

end LinearizationA

section Linearization

variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]

omit [NormedSpace ℝ U] in
/-- Unfolding of the state linearization (definitional). -/
theorem linearizationA_def (f : X → U → X) :
    linearizationA f = fderiv ℝ (fun x ↦ f x 0) 0 := rfl

/-- The input linearization `B = ∂ᵤf(0,0) : U →L[ℝ] X` of the control system
`ẋ = f x u` at the origin, i.e. the Fréchet derivative of `u ↦ f 0 u` at `0`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 3 §3.7, the
linearization appearing in Theorem 7). -/
noncomputable def linearizationB (f : X → U → X) : U →L[ℝ] X :=
  fderiv ℝ (fun u ↦ f 0 u) 0

/-- Unfolding of the input linearization (definitional). -/
theorem linearizationB_def (f : X → U → X) :
    linearizationB f = fderiv ℝ (fun u ↦ f 0 u) 0 := rfl

/-- The linearization of `ẋ = f x u` at the origin is controllable: the Kalman
rank condition `rank [B AB ⋯ A^{n-1}B] = n` holds for
`A = ∂ₓf(0,0)` and `B = ∂ᵤf(0,0)` (Sontag, *Mathematical Control Theory*, 2nd
ed., 1998, Ch. 3 §3.7).  The bridge between this predicate and the displayed
Kalman rank statement is
`LinearMap.isControllable_iff_finrank_range_kalmanControllabilityMap` in
`DynamicalSystems.Linear.Kalman`. -/
def linearizationControllable (f : X → U → X) : Prop :=
  LinearMap.IsControllable (linearizationA f).toLinearMap (linearizationB f).toLinearMap

/-- Unfolding of `linearizationControllable` in terms of the displayed Fréchet
derivatives. -/
theorem linearizationControllable_iff (f : X → U → X) :
    linearizationControllable f ↔
      LinearMap.IsControllable (fderiv ℝ (fun x ↦ f x 0) 0).toLinearMap
        (fderiv ℝ (fun u ↦ f 0 u) 0).toLinearMap :=
  Iff.rfl

end Linearization

/-! ### Local surjectivity -/

section Local

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- **Local surjectivity (openness at a point).**  For a map `Φ : E → F`, this
says that `Φ` maps every neighbourhood of `p` onto a neighbourhood of `Φ p`,
i.e. `map Φ (𝓝 p) = 𝓝 (Φ p)`.

Concretely, when `Φ(x₀, u) = x(T)` is the end-point map of `ẋ = f x u` and
`p = (0,0)`, `Φ p = 0`, the condition asks that every target `y` sufficiently
close to `0` be attained as `Φ(x₀, u) = y` for some `(x₀, u)` close to `(0,0)`.
This is *joint local surjectivity*: it does **not** assert that a single control
steers every nearby initial state to `0`, nor that the trajectory stays within a
prescribed neighbourhood.  Those uniform statements are not formalised here
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 3 §3.7,
Definition 3.7.5 and Remark 3.7.6). -/
def LocallyOnto (Φ : E → F) (p : E) : Prop :=
  map Φ (𝓝 p) = 𝓝 (Φ p)

/-- The continuity half of local surjectivity: `Φ` is continuous at `p`. -/
theorem LocallyOnto.tendsto {Φ : E → F} {p : E}
    (h : LocallyOnto Φ p) : Tendsto Φ (𝓝 p) (𝓝 (Φ p)) :=
  h.le

/-- The local-surjectivity half of `LocallyOnto`: every neighbourhood of `Φ p` is
the image of a neighbourhood of `p`.  In control terms, every sufficiently small
target is reachable by a nearby choice of initial state and control. -/
theorem LocallyOnto.exists_image_subset {Φ : E → F} {p : E}
    (h : LocallyOnto Φ p) {V : Set F} (hV : V ∈ 𝓝 (Φ p)) :
    ∃ W ∈ 𝓝 p, Φ '' W ⊆ V :=
  ⟨Φ ⁻¹' V, Filter.mem_map.mp (h.le hV), image_preimage_subset Φ V⟩

end Local

/-! ### The linearization principle -/

section Principle

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]

/-- **First-order local surjectivity (an open-mapping corollary of the
implicit-mapping theorem).**  Let `ẋ = f x u` be a control system, and let `Φ` be
a candidate end-point map on the finitely many free control values `Fin n → U`
with `n = Module.finrank ℝ X`.  Assume `Φ` is strictly differentiable at `(0,0)`
with derivative `L`, and that the control component of `L` is the Kalman
controllability map of the linearization `(A, B) = (∂ₓf(0,0), ∂ᵤf(0,0))`:
`L (0, u) = kalmanControllabilityMap A B n u` for every `u`.

If the linearization is controllable, then `Φ` is locally onto at the origin:
every target `y` sufficiently close to `Φ (0,0)` is attained as `Φ(z, ν) = y` for
some `(z, ν)` close to `(0,0)`.  The quantifier shape is exactly
`∀ y close to Φ (0,0), ∃ (z, ν) close to (0,0), Φ (z, ν) = y`: this is *joint
local surjectivity*, and it does **not** give uniform control from every nearby
initial state to `0`.

The following are **additional unformalised assumptions**, entering as hypotheses
rather than being proved here:
* the end-point-map regularity (Sontag Theorem 1, p. 57) — that `Φ` is the
  end-point map of `ẋ = f x u` and is strictly differentiable with the stated
  derivative — is not formalised;
* the `Fin n → U` control parametrisation is a finite-dimensional surrogate for
  the piecewise-constant controls used to state the Kalman rank condition;
* there is no time parameter `T`, no excursion/`d∞` bound, and no
  `Φ (0,0) = 0` (equivalently `f 0 0 = 0`) hypothesis in the statement.

The proof is an open-mapping / local-surjectivity corollary of the
implicit-mapping theorem: controllability makes the Kalman map surjective, hence
the derivative `L` — whose range already contains the range of the Kalman map —
is surjective, and `HasStrictFDerivAt.map_nhds_eq_of_surj` converts a surjective
strict derivative into local surjectivity.  Sontag's own proof uses the
implicit-mapping theorem to obtain a *uniform selection* `j(z, y)`, a
continuously differentiable control depending on both endpoints; that uniform
selection is **not** formalised here (Sontag, *Mathematical Control Theory*, 2nd
ed., 1998, Ch. 3 §3.7, Theorem 7). -/
theorem localSurjectivity_of_controllable_linearization
    (f : X → U → X)
    (Φ : X × (Fin (Module.finrank ℝ X) → U) → X)
    (L : (X × (Fin (Module.finrank ℝ X) → U)) →L[ℝ] X)
    (hΦ : HasStrictFDerivAt Φ L (0, 0))
    (hderiv : ∀ u : Fin (Module.finrank ℝ X) → U,
      L (0, u) =
        LinearMap.kalmanControllabilityMap (linearizationA f).toLinearMap
          (linearizationB f).toLinearMap
          (Module.finrank ℝ X) u)
    (hcont : linearizationControllable f) :
    LocallyOnto Φ (0, 0) := by
  rw [LocallyOnto]
  have hsurj : Function.Surjective
      (LinearMap.kalmanControllabilityMap (linearizationA f).toLinearMap
        (linearizationB f).toLinearMap
        (Module.finrank ℝ X)) :=
    (LinearMap.isControllable_iff_surjective_kalmanControllabilityMap _ _).mp hcont
  have hrange : L.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x
    obtain ⟨u, hu⟩ := hsurj x
    exact ⟨(0, u), Eq.trans (hderiv u) hu⟩
  exact hΦ.map_nhds_eq_of_surj hrange

end Principle
